import OAI.Combinatorics.BalancedRyser.Local.AlignedUnusedLaw
import OAI.Combinatorics.BalancedRyser.Probability.RootChildDependence

namespace OAI

namespace Balanced.Local.AlignedGlobal

open AlignedUnused RootChildPartition

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem card_aligned_mul {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) :
    Fintype.card {M : MergedPairs F // Aligned P a bits p M} *
      Fintype.card F ^ (4 * b) = Fintype.card (MergedPairs F) := by
  have hp := alignment_probability P hκ a ha bits p
  unfold offsetProbability at hp
  rw [← FiniteUniformFibers.probability_eq_sum,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div] at hp
  simp only [ENNReal.toReal_natCast] at hp
  change (Fintype.card {M : MergedPairs F // Aligned P a bits p M} : ℝ) /
    Fintype.card (MergedPairs F) = 1 / (Fintype.card F : ℝ) ^ (4 * b) at hp
  have ht : (Fintype.card (MergedPairs F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hq : (Fintype.card F : ℝ) ^ (4 * b) ≠ 0 := by positivity
  have hm := (div_eq_div_iff ht hq).mp hp
  simp only [one_mul] at hm
  exact_mod_cast hm

omit [Field F] [Fintype F] in

theorem card_usedDirections {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Function.Injective a.2) :
    (usedDirections P a).card = 4 * b - κ := by
  rw [usedDirections, Finset.card_image_of_injective _ ha]
  simp

abbrev FreeCoordinates {b : ℕ} (D : Finset (Fin b × Fin 4)) :=
  {ij : Fin b × Fin 4 // ij ∉ D} → F

omit [Field F] in

theorem coordinate_exponent_identity {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (D : Finset (Fin b × Fin 4)) (hD : D.card = 2 * κ) :
    Fintype.card {ij : Fin b × Fin 4 // ij ∉ D} +
      2 * Fintype.card {d : Direction F // d ∉ usedDirections P a} + 4 * b =
        2 * Fintype.card (Direction F) := by
  have hdle : D.card ≤ 4 * b := by
    simpa [Fintype.card_prod, Nat.mul_comm] using Finset.card_le_univ D
  have hule : (usedDirections P a).card ≤ Fintype.card (Direction F) :=
    Finset.card_le_univ _
  rw [card_usedDirections P a ha.2.1] at hule
  simp only [Fintype.card_subtype_compl, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe]
  rw [hD, card_usedDirections P a ha.2.1]
  omega

theorem card_aligned_eq_free_product {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F)
    (D : Finset (Fin b × Fin 4)) (hD : D.card = 2 * κ) :
    Fintype.card {M : MergedPairs F // Aligned P a bits p M} =
      Fintype.card (FreeCoordinates (F := F) D × UnusedArray P a) := by
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fintype.card_pos (α := F)) (4 * b))
  rw [card_aligned_mul P hκ a ha bits p]
  simp only [Fintype.card_prod, FreeCoordinates, UnusedArray,
    MergedPairs, Fintype.card_fun, Fintype.card_bool, ← pow_mul]
  rw [← pow_add, ← pow_add]
  congr 1
  have he := coordinate_exponent_identity P a ha D hD
  omega

theorem card_aligned_eq_rootChild_product {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (R : Finset (Fin b))
    (hcount : (Finset.univ \ R).card = κ)
    (hchild : ∀ i, i ∉ R → (P.classSet i ∩ R.biUnion P.classSet).card = 1) :
    Fintype.card {M : MergedPairs F // Aligned P a bits p M} =
      Fintype.card (FreeCoordinates (F := F) (dependentOccurrences P R) ×
        UnusedArray P a) := by
  apply card_aligned_eq_free_product P hκ a ha bits p
  rw [card_dependentOccurrences P R hchild, hcount]

end
end Balanced.Local.AlignedGlobal

end OAI
