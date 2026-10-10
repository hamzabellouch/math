import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Preliminaries.SummandTails

namespace OAI

/-!
# Published counting bounds for the summands

Christian Elsholtz, *Additive decomposability of multiplicatively defined sets*,
Functiones et Approximatio Commentarii Mathematici 35 (2006), 61–77,
Theorem 1.9, printed p. 63. DOI: 10.7169/facm/1229442617.
https://www.math.tugraz.at/~elsholtz/WWW/papers/papers22wirsing04.pdf

We record just its square-root counting consequence for a hypothetical
asymptotic decomposition, in the nonnegative-integer convention of the target
manuscript (Section 2, Lemma `size`). This is an explicit conditional input;
no instance is postulated globally. The tail truncation is proved separately.
-/

namespace Ostmann

/-- The only counting-function estimates needed from Elsholtz's Theorem 1.9. -/
def PublishedSummandSizeBound : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → EventuallyPrimeSumset A B →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix A N).card ∧
      (summandPrefix A N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 ∧
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix B N).card ∧
      (summandPrefix B N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2

end Ostmann

end OAI
