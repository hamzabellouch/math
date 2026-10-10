import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! A fixed smooth plane cutoff with quantitative rescaling. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def planeUnitBump : ContDiffBump (0 : ℂ) := ⟨1,2,zero_lt_one,one_lt_two⟩
def planeScaledBump (r : ℝ) (z : ℂ) : ℝ := planeUnitBump (r⁻¹ • z)

lemma planeScaledBump_smooth (r : ℝ) : ContDiff ℝ ∞ (planeScaledBump r) := by
  change ContDiff ℝ ∞ (fun z : ℂ => planeUnitBump (r⁻¹ • z))
  exact planeUnitBump.contDiff.comp
    ((contDiff_const (c := r⁻¹)).smul (contDiff_id : ContDiff ℝ ∞ (fun z : ℂ => z)))

lemma planeScaledBump_unit (r : ℝ) (z : ℂ) : planeScaledBump r z∈Icc 0 1 :=
  ⟨planeUnitBump.nonneg,planeUnitBump.le_one⟩

lemma planeScaledBump_one {r : ℝ} (hr : 0<r) {z : ℂ} (hz : ‖z‖≤r) :
    planeScaledBump r z=1 := by
  apply planeUnitBump.one_of_mem_closedBall
  change r⁻¹ • z∈closedBall (0:ℂ) 1
  apply mem_closedBall_zero_iff.mpr
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hz)

lemma planeScaledBump_zero {r : ℝ} (hr : 0<r) {z : ℂ} (hz : 2*r≤‖z‖) :
    planeScaledBump r z=0 := by
  apply planeUnitBump.zero_of_le_dist
  change 2≤dist (r⁻¹ • z) 0
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  exact (le_inv_mul_iff₀ hr).mpr (by nlinarith)

lemma planeScaledBump_eventually_zero {r : ℝ} (hr : 0<r) {z : ℂ} (hz : 2*r<‖z‖) :
    planeScaledBump r =ᶠ[𝓝 z] 0 := by
  filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hz] with y hy
  exact planeScaledBump_zero hr hy.le

lemma exists_planeUnitBump_derivative_bound : ∃B:ℝ,0≤B ∧ ∀z,‖fderiv ℝ planeUnitBump z‖≤B := by
  obtain ⟨B,hB⟩ := ((planeUnitBump.contDiff : ContDiff ℝ 1 (planeUnitBump : ℂ → ℝ)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (planeUnitBump.hasCompactSupport.fderiv ℝ)
  exact ⟨max 0 B,le_max_left _ _,fun z => (hB z).trans (le_max_right _ _)⟩

lemma planeScaledBump_derivative_bound {B r : ℝ} (hB : ∀z,‖fderiv ℝ planeUnitBump z‖≤B)
    (hr : 0<r) (z : ℂ) : ‖fderiv ℝ (planeScaledBump r) z‖≤B/r := by
  have hd := ((planeUnitBump.contDiff : ContDiff ℝ 1 (planeUnitBump : ℂ → ℝ)).differentiable one_ne_zero (r⁻¹ • z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul r⁻¹)
  change HasFDerivAt (planeScaledBump r) _ z at hd
  rw [hd.fderiv]
  calc
    ‖(fderiv ℝ planeUnitBump (r⁻¹ • z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ ℂ)‖ ≤
        ‖fderiv ℝ planeUnitBump (r⁻¹ • z)‖*‖r⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B*r⁻¹ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),ContinuousLinearMap.norm_id,mul_one]
      exact mul_le_mul_of_nonneg_right (hB _) (inv_nonneg.mpr hr.le)
    _ = B/r := by rw [div_eq_mul_inv]

end CircleDomainRigidity

end

end OAI
