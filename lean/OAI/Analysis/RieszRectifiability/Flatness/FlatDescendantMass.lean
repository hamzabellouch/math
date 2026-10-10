import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellSeeds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem SupportCellDescendant.top_radius_eq {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) :
    latticeRadius R k = (64 : ℝ) ^ i.depth * i.radius := by
  change _ = (64 : ℝ) ^ i.depth * latticeRadius R (k + i.depth)
  rw [latticeRadius_add]
  have hp : (64 : ℝ) ^ i.depth * (1 / 64 : ℝ) ^ i.depth = 1 := by
    rw [← mul_pow]
    norm_num
  change _ = (64 : ℝ) ^ i.depth * (latticeRadius R k * (1 / 64 : ℝ) ^ i.depth)
  rw [mul_left_comm, hp, mul_one]

theorem SupportCellDescendant.radius_lower_of_depth_le {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (I : ℕ) (hi : i.depth ≤ I) :
    latticeRadius R k ≤ (64 : ℝ) ^ I * i.radius := by
  rw [i.top_radius_eq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) i.radius_pos.le

def flatDescendantMassConstant (n : ℕ) (C G : ℝ) (I : ℕ) : ℝ :=
  C * G * (24 * (64 : ℝ) ^ I) ^ n

theorem flatDescendantMassConstant_pos (n : ℕ) (C G : ℝ) (I : ℕ) (hC : 0 < C) (hG : 0 < G) :
    0 < flatDescendantMassConstant n C G I := by
  unfold flatDescendantMassConstant
  positivity

theorem SupportCellDescendant.parent_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (i : SupportCellDescendant μ R hR k z) (I : ℕ) (hi : i.depth ≤ I) :
    μ.real (cleanSupportCell μ R hR k z) ≤ flatDescendantMassConstant n C G I * μ.real i.cell := by
  have hicore : AdmissibleRadius μ (latticeRadius R (k + i.depth) / 8) := by
    simpa only [one_div_mul_eq_div, SupportCellDescendant.radius] using! i.core_admissible hcore
  have hlow := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR
    (k + i.depth) hicore ⟨i.center, i.mem_net⟩).1
  have htop := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).2
  have hscale := i.radius_lower_of_depth_le I hi
  have hK := flatDescendantMassConstant_pos n C G I hC hG
  have hparent := latticeRadius_pos R hR k
  calc
    _ ≤ G * (3 * latticeRadius R k) ^ n := by simpa only [mul_pow, mul_assoc] using! htop
    _ ≤ G * (3 * ((64 : ℝ) ^ I * i.radius)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) n) hG.le
    _ = flatDescendantMassConstant n C G I * ((i.radius / 8) ^ n / C) := by
      have heq : 3 * ((64 : ℝ) ^ I * i.radius) =
          (24 * (64 : ℝ) ^ I) * (i.radius / 8) := by ring
      rw [heq, mul_pow]
      unfold flatDescendantMassConstant
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hK.le

end

end RieszRectifiability

end OAI
