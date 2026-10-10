import Mathlib
import OAI.Analysis.CoulombRadii.Screening.ScaledTest
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma countTest_laplacian_scaled (R : ℝ) (x : Position) :
    coordinateLaplacian (Coulomb.countTest 0 R) x=
      R⁻¹^2*coordinateLaplacian Coulomb.cutSeed (R⁻¹ • x) := by
  unfold Coulomb.countTest
  rw [Coulomb.coordinateLaplacian_scaled (Coulomb.cutSeed_smooth.of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [sub_zero]

lemma countTest_laplacian_inner {R : ℝ} {x : Position} (hx : ‖x‖<R) :
    coordinateLaplacian (Coulomb.countTest 0 R) x=0 := by
  have hR := (norm_nonneg x).trans_lt hx
  have he : Coulomb.countTest 0 R=ᶠ[𝓝 x] (fun _ : Position => (1:ℝ)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy
    exact Coulomb.countTest_one 0 hR (by simpa only [sub_zero] using hy.le)
  rw [coordinateLaplacian_congr_nhds he]
  simp [coordinateLaplacian]

lemma countTest_laplacian_abs_integral {R : ℝ} (hR : 0<R) :
    (∫ x,|coordinateLaplacian (Coulomb.countTest 0 R) x|)=
      R*(∫ x,|coordinateLaplacian Coulomb.cutSeed x|) := by
  simp only [countTest_laplacian_scaled,abs_mul,abs_of_nonneg (sq_nonneg R⁻¹),integral_const_mul]
  rw [Measure.integral_comp_inv_smul volume (fun x => |coordinateLaplacian Coulomb.cutSeed x|) R]
  simp only [show Module.finrank ℝ Position=3 by simp [Position],smul_eq_mul,abs_of_pos (pow_pos hR 3)]
  field_simp

lemma countTest_pairing_bound {F : Position → ℝ} {C R : ℝ}
    (hF : Measurable F) (hC : 0≤C) (hR : 0<R)
    (hbound : ∀ x,R≤‖x‖ → |F x|≤C/‖x‖^4) :
    |∫ x,F x*coordinateLaplacian (Coulomb.countTest 0 R) x|≤
      C*(∫ x,|coordinateLaplacian Coulomb.cutSeed x|)/R^3 := by
  let Δ : Position → ℝ := coordinateLaplacian (Coulomb.countTest 0 R)
  have hΔc : Continuous Δ := (contDiff_coordinateLaplacian (Coulomb.countTest_smooth 0 R)).continuous
  have hΔs : HasCompactSupport Δ := hasCompactSupport_coordinateLaplacian (Coulomb.countTest_compact 0 hR)
  have hiΔ : Integrable (fun x => |Δ x|) := (hΔc.integrable_of_hasCompactSupport hΔs).abs
  have hb : ∀ x,|F x*Δ x|≤(C/R^4)*|Δ x| := by
    intro x
    by_cases hx : R≤‖x‖
    · rw [abs_mul]
      apply mul_le_mul_of_nonneg_right ((hbound x hx).trans ?_) (abs_nonneg _)
      exact div_le_div_of_nonneg_left hC (pow_pos hR 4) (pow_le_pow_left₀ hR.le hx 4)
    · rw [show Δ x=0 from countTest_laplacian_inner (lt_of_not_ge hx)]
      simp
  have hi : Integrable (fun x => F x*Δ x) :=
    (hiΔ.const_mul (C/R^4)).mono' (hF.mul hΔc.measurable).aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  calc
    _≤∫ x,|F x*Δ x| := abs_integral_le_integral_abs
    _≤∫ x,(C/R^4)*|Δ x| := integral_mono hi.abs (hiΔ.const_mul _) hb
    _=(C/R^4)*(R*(∫ x,|coordinateLaplacian Coulomb.cutSeed x|)) := by
      rw [integral_const_mul,countTest_laplacian_abs_integral hR]
    _=_ := by field_simp

end NeutralAtom
end

end

end OAI
