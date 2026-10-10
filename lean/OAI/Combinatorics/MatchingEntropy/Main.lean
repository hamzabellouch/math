import OAI.Combinatorics.MatchingEntropy.ExpansionSequences

/-!
# Sharp analytic bounds for perfect-matching entropy

For a finite loopless labelled multigraph on `2m` vertices, with `m ≥ 1` and a perfect
matching, every point of the matching polytope satisfies
`F - (2 - 2 / m) * B ≤ H ≤ F`. Here `F` and `B` are the coordinate entropy and
complement entropy with natural logarithms, and `H` is the attained supremum of entropy
over all perfect-matching laws with the prescribed mean.

The development includes the odd-cut description of the matching polytope, sharp face
rank bounds, minimal faces, fractional and connected-component reductions, attained
entropy and weighted partition objectives, matching counts, degenerate cases, colored
triangle-expansion families, and concrete coefficient obstructions.
-/
