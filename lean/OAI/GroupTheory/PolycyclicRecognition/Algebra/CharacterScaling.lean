import OAI.GroupTheory.PolycyclicRecognition.Analysis.BadCharacterCompactness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveZeroSums

namespace OAI

/-! # Positive scaling and the finite zero-sum obstruction -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra InnerProductSpace
variable {Q M E : Type} [CommGroup Q] [AddCommGroup M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ρ : Representation ℤ Q M) (e : Q →* Multiplicative E)

theorem inwardCharacterMonoid_smul (v : E) {c : ℝ} (hc : 0 < c) :
    characterNonnegativeMonoid (inwardVectorCharacter e (c • v)) =
      characterNonnegativeMonoid (inwardVectorCharacter e v) := by
  ext q
  change 0 ≤ -⟪c • v, (e q).toAdd⟫_ℝ ↔ 0 ≤ -⟪v, (e q).toAdd⟫_ℝ
  rw [real_inner_smul_left, ← mul_neg, mul_nonneg_iff_of_pos_left hc]

theorem finite_inwardCharacter_smul_iff (v : E) {c : ℝ} (hc : 0 < c) :
    Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e (c • v))]
      (characterMonoidRepresentation ρ (inwardVectorCharacter e (c • v))).asModule ↔
    Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e v)]
      (characterMonoidRepresentation ρ (inwardVectorCharacter e v)).asModule := by
  unfold characterMonoidRepresentation
  rw [inwardCharacterMonoid_smul e v hc]

theorem badUnitCharacters_no_convex_zero_of_no_zero_sum
    [Module.Finite ℤ[Q] ρ.asModule]
    (h : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (z : ι → E),
      (∀ i, ¬Module.Finite ℤ[characterNonnegativeMonoid (inwardVectorCharacter e (z i))]
        (characterMonoidRepresentation ρ (inwardVectorCharacter e (z i))).asModule) →
      (∑ i, z i) ≠ 0) :
    (0 : E) ∉ convexHull ℝ (badUnitCharacters ρ e) := by
  apply zero_not_mem_convexHull_of_no_positive_sum
  intro ι _ z w hz hw hsum hzero
  have hn : Nonempty ι := by
    by_contra hn
    let : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hsum
  let := hn
  apply h ι (fun i => w i • z i) ?_ hzero
  intro i
  exact fun hfin => (hz i).2 ((finite_inwardCharacter_smul_iff ρ e (z i) (hw i)).mp hfin)

end PolycyclicRecognition

end

end OAI
