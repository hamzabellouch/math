import OAI.Geometry.SurfaceImmersion.Geometry.TransverseSmallFunction
import OAI.Geometry.SurfaceImmersion.Geometry.AxisFlatBounds

namespace OAI

/-! A fixed one-dimensional bump rescaled only in the transverse coordinate. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def transverseCutoff (r : ℝ) (x : Base) : ℝ := TransverseSmallFunction.cutoff (x 0/r)

lemma transverseCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (transverseCutoff r) :=
  TransverseSmallFunction.cutoff.contDiff.comp ((contDiff_apply ℝ ℝ (0 : Fin 2)).div_const r)

lemma transverseCutoff_le_one (r : ℝ) (x : Base) : |transverseCutoff r x| ≤ 1 := by
  change |TransverseSmallFunction.cutoff (x 0/r)| ≤ 1
  rw [abs_of_nonneg TransverseSmallFunction.cutoff.nonneg]
  exact TransverseSmallFunction.cutoff.le_one

lemma transverseCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (transverseCutoff r) ⊆ {x | |x 0| ≤ r} := by
  apply closure_minimal _ (isClosed_le (by fun_prop) continuous_const)
  intro x hx
  have hb : |x 0/r| < 1 := by
    have h := TransverseSmallFunction.cutoff.support_eq
    have hh : x 0/r ∈ ball (0 : ℝ) 1 := h ▸ hx
    simpa only [mem_ball,Real.dist_eq,sub_zero] using hh
  rw [abs_div,abs_of_pos hr] at hb
  exact ((div_lt_one hr).mp hb).le

lemma transverseCutoff_axis_germ (r t : ℝ) :
    transverseCutoff r =ᶠ[𝓝 (crosscapAxis t)] 1 := by
  have hc : Continuous (fun x : Base => x 0/r) := by fun_prop
  have ht : Tendsto (fun x : Base => x 0/r) (𝓝 (crosscapAxis t)) (𝓝 0) := by
    simpa [crosscapAxis_apply] using hc.continuousAt.tendsto (x := crosscapAxis t)
  exact TransverseSmallFunction.cutoff.eventuallyEq_one.comp_tendsto ht

theorem transverseCutoff_derivative_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ r : ℝ, 0 < r → ∀ x : Base, ‖fderiv ℝ (transverseCutoff r) x‖ ≤ B/r := by
  have hχ : ContDiff ℝ ∞ (TransverseSmallFunction.cutoff : ℝ → ℝ) :=
    TransverseSmallFunction.cutoff.contDiff
  have hcomp : HasCompactSupport (fderiv ℝ (TransverseSmallFunction.cutoff : ℝ → ℝ)) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) TransverseSmallFunction.cutoff.hasCompactSupport
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  let P : Base →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  refine ⟨|C| * ‖P‖,mul_nonneg (abs_nonneg _) (norm_nonneg _),?_⟩
  intro r hr x
  have hscale : HasFDerivAt (fun y : Base => y 0/r) (r⁻¹ • P) x := by
    convert P.hasFDerivAt.const_smul r⁻¹ using 1
    funext y
    change y 0/r = r⁻¹*y 0
    ring
  have hd := (hχ.differentiable (by simp) _).hasFDerivAt.comp x hscale
  change HasFDerivAt (transverseCutoff r) _ x at hd
  rw [hd.fderiv]
  calc
    _ ≤ ‖fderiv ℝ TransverseSmallFunction.cutoff (x 0/r)‖*‖r⁻¹ • P‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ |C| * ‖r⁻¹ • P‖ := mul_le_mul_of_nonneg_right ((hC _).trans (le_abs_self C)) (norm_nonneg _)
    _ = (|C| * ‖P‖)/r := by rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]; ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
