import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailWeightedL2

namespace OAI

/-! Weighted top energy is preserved by subtracting an outgoing parameter correction. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ

theorem spectralWeighted_square_sub_integrable (u v : ℝ → V) (R : ℝ) (hR : 0≤R)
    (hcU : ContinuousOn u (Ioi R)) (hcV : ContinuousOn v (Ioi R))
    (hu : IntegrableOn (fun r => r^11*‖u r‖^2) (Ioi R))
    (hv : IntegrableOn (fun r => r^11*‖v r‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖u r-v r‖^2) (Ioi R) := by
  have hmajor := (hu.add hv).const_mul (2 : ℝ)
  apply hmajor.mono'
    (((continuousOn_id.pow 11).mul ((hcU.sub hcV).norm.pow 2)).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr₀ : 0≤r := hR.trans hr.le
  have hsq : ‖u r-v r‖^2 ≤ 2*(‖u r‖^2+‖v r‖^2) := by
    have h := norm_sub_le (u r) (v r)
    have hnorm := norm_nonneg (u r-v r)
    nlinarith [sq_nonneg (‖u r‖-‖v r‖)]
  change ‖(r^11*‖u r-v r‖^2 : ℝ)‖ ≤ 2*(r^11*‖u r‖^2+r^11*‖v r‖^2)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg hr₀ 11) (sq_nonneg ‖u r-v r‖))]
  calc
    _ ≤ r^11*(2*(‖u r‖^2+‖v r‖^2)) :=
      mul_le_mul_of_nonneg_left hsq (pow_nonneg hr₀ _)
    _ = _ := by ring

theorem spectralWeighted_square_smul_integrable (u : ℝ → V) (R : ℝ) (c : ℂ)
    (hu : IntegrableOn (fun r => r^11*‖u r‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖c • u r‖^2) (Ioi R) := by
  have hi : IntegrableOn (fun r => ‖c‖^2*(r^11*‖u r‖^2)) (Ioi R) := hu.const_mul _
  apply hi.congr_fun _ measurableSet_Ioi
  intro r _
  dsimp only
  rw [norm_smul,mul_pow]
  ring

theorem spectralWeighted_top_sub_integrable (u v : ℝ → V) (R : ℝ) (hR : 0≤R) (N : ℕ)
    (hcU : ContDiffOn ℝ ∞ u (Ioi R)) (hcV : ContDiffOn ℝ ∞ v (Ioi R))
    (hu : IntegrableOn (fun r => r^11*‖iteratedDeriv N u r‖^2) (Ioi R))
    (hv : IntegrableOn (fun r => r^11*‖iteratedDeriv N v r‖^2) (Ioi R)) :
    IntegrableOn (fun r => r^11*‖iteratedDeriv N (fun s => u s-v s) r‖^2) (Ioi R) := by
  have hi := spectralWeighted_square_sub_integrable (iteratedDeriv N u) (iteratedDeriv N v) R hR
    (homogeneousPair_iteratedDeriv_smooth_tail u R hcU N).continuousOn
    (homogeneousPair_iteratedDeriv_smooth_tail v R hcV N).continuousOn hu hv
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  dsimp only
  rw [iteratedDeriv_fun_sub
    (((hcU r hr).contDiffAt (Ioi_mem_nhds hr)).of_le (by simp))
    (((hcV r hr).contDiffAt (Ioi_mem_nhds hr)).of_le (by simp))]

end DefocusingNLS

end OAI
