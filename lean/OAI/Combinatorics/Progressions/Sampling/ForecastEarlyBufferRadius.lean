import OAI.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]

private theorem forecast_cube_factor_one_le (j : Fin m) :
    (1 : ℝ) ≤ (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1) :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (by linarith [Nat.cast_nonneg (Fintype.card α) (α := ℝ)]))

theorem allocatedProductIdealSiteRadius_forecast_monomials (j : Fin m) :
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤
      allocatedProductIdealSiteRadius (G := G) B rowSets := by
  have hr : (1 : ℝ) ≤ (rowSets j).card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_coe_sort.mp inferInstance)
  have hT := allocatedIdealCoverSupport_nonneg (G := G) B rowSets j
  calc
    _ ≤ (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) (forecast_cube_factor_one_le (α := α) j)
    _ ≤ allocatedIdealCoverSupport (G := G) B rowSets j := allocatedIdealCoverSupport_inactive B rowSets j
    _ ≤ (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j :=
      le_mul_of_one_le_left hT hr
    _ ≤ _ := allocatedProductIdealSiteRadius_dominates B rowSets j

theorem allocatedProductIdealSiteRadius_forecast_three (hm : 0 < m) :
    (3 : ℝ) ≤ allocatedProductIdealSiteRadius (G := G) B rowSets := by
  let j : Fin m := ⟨0, hm⟩
  have hr : (1 : ℝ) ≤ (rowSets j).card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_coe_sort.mp inferInstance)
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ m :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [Nat.cast_nonneg (Fintype.card α) (α := ℝ)]))
  have hT : 2 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
    have hi := allocatedIdealCoverSupport_ideal (G := G) B rowSets j
    unfold partitionedIdealRadius at hi
    linarith
  have hsum := Finset.single_le_sum
    (f := fun k : Fin m => (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets k))
    (Finset.mem_univ j)
  have hprod : 2 ≤ (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j :=
    hT.trans (le_mul_of_one_le_left (by linarith) hr)
  change 3 ≤ 1 + ∑ k : Fin m, (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k
  linarith

end Erdos3.VectorPolynomial

end

end OAI
