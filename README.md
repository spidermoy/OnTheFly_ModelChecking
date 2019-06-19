Efficient On-the-Fly Model Checking for LTL and CTL★
=======

This repository contains a functional implementation in Haskell of the algorithms included in the article
_Efficient On-the-Fly Model Checking for CTL★_ (Bhat, Girish, Rance Cleaveland, and Orna Grumberg).

It's important to say this method works without Büchi automatons.
In the words of the authors:

> In this paper we present an on-the-fly algorithm for checking finite-state Kripke structures against CTL★ formulas.

> Our routine constructs the state space of the system under consideration in a need-driven fashion and will therefore perform better in practice.

See [Efficient On-the-Fly Model Checking for CTL★](https://www.semanticscholar.org/paper/Eecient-On-the-fly-Model-Checking-for-Ctl-Bhat-Cleaveland/e7dbc6e9ff14c98d61af98247e79a3b2058cbfff) for more details.
