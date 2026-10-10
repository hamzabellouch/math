import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.ADCellHaarPairs

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem latticeRadius_le_depth_multiple (R : ℝ) (hR : 0 < R) (k t I : ℕ) (ht : t ≤ I) :
    latticeRadius R k ≤ (64 : ℝ) ^ I * latticeRadius R (k + t) := by
  calc
    _ = latticeRadius R k * ((64 : ℝ) * (1 / 64)) ^ I := by norm_num
    _ = (64 : ℝ) ^ I * latticeRadius R (k + I) := by rw [latticeRadius_add, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (latticeRadius_antitone R hR.le (Nat.add_le_add_left ht k)) (by positivity)

def haarCellMassRatio (n : ℕ) (C G : ℝ) (I : ℕ) : ℝ :=
  C * G * 3 ^ n * 8 ^ n * (64 : ℝ) ^ (I * n)

theorem haarCellMassRatio_pos (n : ℕ) (C G : ℝ) (I : ℕ) (hC : 0 < C) (hG : 0 < G) :
    0 < haarCellMassRatio n C G I := by
  unfold haarCellMassRatio
  positivity

theorem CellHaarPair.parent_mass_le_inner {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    μ.real (cleanSupportCell μ R hR k z) ≤ haarCellMassRatio n C G I * μ.real P.innerCell := by
  have hp := cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  have hc := lattice_core_admissible_at_later_level μ R hR k
    (k + P.outerOffset + P.innerOffset) (by omega) hcore
  have hi := cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR
    (k + P.outerOffset + P.innerOffset) hc P.innerCenter
  have hr : latticeRadius R k ≤ (64 : ℝ) ^ I *
      latticeRadius R (k + P.outerOffset + P.innerOffset) := by
    simpa only [Nat.add_assoc] using! latticeRadius_le_depth_multiple R hR k
      (P.outerOffset + P.innerOffset) I P.depth_bound
  have hid : (G * 3 ^ n) * ((64 : ℝ) ^ I * latticeRadius R
      (k + P.outerOffset + P.innerOffset)) ^ n = haarCellMassRatio n C G I *
        ((latticeRadius R (k + P.outerOffset + P.innerOffset) / 8) ^ n / C) := by
    simp only [haarCellMassRatio, mul_pow, div_pow, pow_mul]
    field_simp
  calc
    _ ≤ (G * 3 ^ n) * latticeRadius R k ^ n := hp.2
    _ ≤ (G * 3 ^ n) * ((64 : ℝ) ^ I * latticeRadius R
        (k + P.outerOffset + P.innerOffset)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (latticeRadius_pos R hR k).le hr n) (by positivity)
    _ = _ := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hi.1 (haarCellMassRatio_pos n C G I hC hG).le

end

end RieszRectifiability

end OAI
