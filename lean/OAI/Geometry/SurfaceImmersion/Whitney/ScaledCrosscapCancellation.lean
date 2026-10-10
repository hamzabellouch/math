import OAI.Geometry.SurfaceImmersion.Whitney.SupportedCrosscapCancellation

namespace OAI

/-! A supported cancellation can be placed in an arbitrarily small ball. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def rescaledSurface (r : ℝ) (F : Base → ProjectionTarget 3) : Base → ProjectionTarget 3 :=
  fun x => r • F (r⁻¹ • x)

lemma rescaledSurface_smooth (r : ℝ) {F : Base → ProjectionTarget 3}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (rescaledSurface r F) :=
  (hF.comp (contDiff_id.const_smul r⁻¹)).const_smul r

lemma rescaledSurface_immersion {r : ℝ} (hr : r ≠ 0)
    {F : Base → ProjectionTarget 3} (hF : ContDiff ℝ ∞ F)
    (hI : ∀ x, Function.Injective (fderiv ℝ F x)) (x : Base) :
    Function.Injective (fderiv ℝ (rescaledSurface r F) x) := by
  have hd := ((hF.differentiable (by simp) (r⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r⁻¹)).const_smul r
  change HasFDerivAt (rescaledSurface r F) _ x at hd
  rw [hd.fderiv]
  exact (smul_right_injective (ProjectionTarget 3) hr).comp
    ((hI _).comp (smul_right_injective Base (inv_ne_zero hr)))

theorem exists_small_supported_crosscap_cancellation {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (F : Base → ProjectionTarget 3), 0 < r ∧
      ContDiff ℝ ∞ F ∧ (∀ x, Function.Injective (fderiv ℝ F x)) ∧
      ∀ x, ε ≤ ‖x‖ → F x = rescaledSurface r (crosscapPair 3) x := by
  obtain ⟨F,K,hF,hI,hK,hEq⟩ := exists_supported_crosscap_cancellation
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : Base → Base)).continuousOn
  let r := ε / (2*(|C|+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hsize : r*|C| < ε := by
    dsimp [r]
    have hd : 0 < 2*(|C|+1) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith [abs_nonneg C]
  refine ⟨r,rescaledSurface r F,hr,rescaledSurface_smooth r hF,
    rescaledSurface_immersion (ne_of_gt hr) hF hI,?_⟩
  intro x hx
  have hout : r⁻¹ • x ∉ K := by
    intro hin
    have hnorm : ‖x‖ = r*‖r⁻¹ • x‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr,mul_inv_cancel_left₀ (ne_of_gt hr)]
    have hb : ‖x‖ ≤ r*|C| := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left ((hC _ hin).trans (le_abs_self C)) hr.le
    exact (not_lt_of_ge hx) (hb.trans_lt hsize)
  exact congrArg (r • ·) (hEq _ hout)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
