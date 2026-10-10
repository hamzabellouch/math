import OAI.Geometry.HeilbronnTriangle.AuxiliarySamplingSupport
import OAI.Geometry.HeilbronnTriangle.WeightedZeroPartition
import OAI.Geometry.HeilbronnTriangle.LiftedBadEvent

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySampling.Law

open scoped BigOperators
open LiftingProbability

variable {q h : ℕ} [Fact q.Prime]

theorem density_ratio_le_main_square (L : Law q (h ^ 2)) :
    (q : ℝ) ^ 3 / L.size ≤ 2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12 := by
  have hs : (q : ℝ) ^ 2 ≤ 2000 ^ 3 * ((h : ℝ) ^ 2) ^ 6 * L.size := by
    exact_mod_cast L.size_lower
  have hsize : (0 : ℝ) < L.size := by exact_mod_cast L.size_pos
  apply (div_le_iff₀ hsize).mpr
  calc
    (q : ℝ) ^ 3 = (q : ℝ) * (q : ℝ) ^ 2 := by ring
    _ ≤ (q : ℝ) * (2000 ^ 3 * ((h : ℝ) ^ 2) ^ 6 * L.size) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q)
    _ = _ := by ring

theorem weight_le_two_main_square (L : Law q (h ^ 2))
    (p : Fin 3 → Fin 3 → ZMod q) :
    auxiliaryWeight q L.size L.weight L.sets p ≤
      (2 * 2000 ^ 6) * (q : ℝ) ^ 2 * (h : ℝ) ^ 24 := by
  calc
    _ ≤ 2 * ((q : ℝ) ^ 3 / L.size) ^ 2 := L.weight_le_two p
    _ ≤ 2 * (2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12) ^ 2 := by
      gcongr
      exact L.density_ratio_le_main_square
    _ = _ := by ring

theorem weight_le_four_main_square (L : Law q (h ^ 2))
    (p : Fin 3 → Fin 3 → ZMod q) (hne : ∃ i j, p i ≠ p j) :
    auxiliaryWeight q L.size L.weight L.sets p ≤
      (4 * 2000 ^ 3) * (q : ℝ) * (h : ℝ) ^ 12 := by
  obtain ⟨i, j, hij⟩ := hne
  calc
    _ ≤ 4 * ((q : ℝ) ^ 3 / L.size) := L.weight_le_four p i j hij
    _ ≤ 4 * (2000 ^ 3 * (q : ℝ) * (h : ℝ) ^ 12) :=
      mul_le_mul_of_nonneg_left L.density_ratio_le_main_square (by norm_num)
    _ = _ := by ring

theorem affine_or_equalPair_of_weight_pos {H : ℕ} (L : Law q H)
    (p : Fin 3 → Fin 3 → ZMod q)
    (hpositive : 0 < auxiliaryWeight q L.size L.weight L.sets p) :
    AffineIndependent (ZMod q) p ∨
      ∃ i : Fin 3, WeightedZeroPartition.EqualPair p i := by
  obtain ⟨ω, hω⟩ := L.exists_outcome_of_weight_pos p hpositive
  exact WeightedZeroPartition.affine_or_equalPair_of_cap p (L.sets ω)
    (L.isCap ω) hω

end Problem355.AuxiliarySampling.Law

end

end OAI
