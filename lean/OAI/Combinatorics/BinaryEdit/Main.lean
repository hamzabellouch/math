import OAI.Combinatorics.BinaryEdit.BinaryLowerBound

/-!
# Binary edit-distance distortion from a finite tree

The finite group of leaf coordinates carries recursively concatenated words.
Tagged subsequence matchings give separation, while cheap translations and
nonnegative Fourier weights bound averaged ℓ₁ displacements. A binary block
code of width `M²` and distortion at most `804` produces equal-length binary
witnesses. Comparing the word-length and distortion scales gives the lower
bound for every sufficiently large cap.

The construction and binary conversion formalize OpenAI's September 27, 2026
manuscript, *Tree Constructions for the ℓ₁ Distortion of Binary Edit Distance*.
-/
