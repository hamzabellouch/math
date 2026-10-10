import OAI.Probability.SLE.Geometry.NormalizedLoewnerCharts
import OAI.Probability.SLE.DiskHalfPlane

namespace OAI

/-! The actual marked point in a unit-modulus restarted chart. Its physical
scale is exactly the original conformal radius, including the inverse-map
derivative factor used in the dense experiment. -/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

def unitMarkedState (q : ℂ) : ℂ := q / (‖q‖ : ℂ)

lemma unitMarkedState_norm {q : ℂ} (hq : q ≠ 0) : ‖unitMarkedState q‖ = 1 := by
  rw [unitMarkedState, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_pos_iff.mpr hq).ne']

lemma unitMarkedState_im (q : ℂ) : (unitMarkedState q).im = Real.sin (Complex.arg q) := by
  rw [unitMarkedState, Complex.div_ofReal_im, Complex.sin_arg]

lemma IsCapacityTwoWitness.inverse_derivative_identity
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) :
    deriv (F t) (G t z) * deriv (G t) z = 1 := by
  have hFd := ((hw.2.2.2.2.1 t).differentiableAt
    (isOpen_upperHalfPlane.mem_nhds (hw.2.2.2.2.2.1 t hz))).hasDerivAt
  have hGd := ((hw.2.2.2.1 t).differentiableAt
    ((isOpen_survivingDomain hw.1 t).mem_nhds hz)).hasDerivAt
  have he : (fun w => F t (G t w)) =ᶠ[𝓝 z] (fun w => w) := by
    filter_upwards [(isOpen_survivingDomain hw.1 t).mem_nhds hz] with w hwl
    exact hw.2.2.2.2.2.2.2.1 t w hwl
  exact ((hFd.comp z hGd).congr_of_eventuallyEq he.symm).unique (hasDerivAt_id z)

lemma normalizedInverse_derivative
    (F : ℂ → ℂ) (u a : ℝ) (w : ℂ)
    (hF : DifferentiableAt ℂ F ((u : ℂ) + (a : ℂ) * w)) :
    deriv (normalizedInverse F u a) w = deriv F ((u : ℂ) + (a : ℂ) * w) * (a : ℂ) := by
  have hA := (hasDerivAt_const w (u : ℂ)).add ((hasDerivAt_id w).const_mul (a : ℂ))
  change deriv (fun x => F ((u : ℂ) + (a : ℂ) * x)) w = _
  simpa only [Function.comp_def, Pi.add_apply, Pi.mul_apply, id_eq, zero_add, mul_one] using
    (hF.hasDerivAt.comp w hA).deriv

/-- All hypotheses of the uniform conformal dense experiment are supplied
by the actual live marked state and its normalized inverse chart. -/
theorem IsCapacityTwoWitness.normalized_marked_state
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    let q := G T z - (U T : ℂ)
    let w := unitMarkedState q
    let f := normalizedInverse (F T) (U T) ‖q‖
    ‖w‖ = 1 ∧ 0 < w.im ∧ f w = z ∧
      DifferentiableOn ℂ f upperHalfPlane ∧ InjOn f upperHalfPlane ∧
      deriv f w ≠ 0 ∧ 2 * w.im * ‖deriv f w‖ = fullRadius G T z := by
  dsimp only
  let q := G T z - (U T : ℂ)
  let w := unitMarkedState q
  let f := normalizedInverse (F T) (U T) ‖q‖
  have hq : q ≠ 0 := hw.centered_ne_zero T z hz
  have ha : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hqim : 0 < q.im := by
    simpa only [q, Complex.sub_im, Complex.ofReal_im, sub_zero] using hw.imag_positive T z hz
  have hwim : 0 < w.im := by
    dsimp only [w, unitMarkedState]
    rw [Complex.div_ofReal_im]
    exact div_pos hqim ha
  have heval : (U T : ℂ) + (‖q‖ : ℂ) * w = G T z := by
    dsimp only [w, unitMarkedState]
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
    dsimp only [q]
    ring
  have hcharts := normalized_capacity_charts hw T ‖q‖ ha
  have hFdiff : DifferentiableAt ℂ (F T) ((U T : ℂ) + (‖q‖ : ℂ) * w) := by
    rw [heval]
    exact (hw.2.2.2.2.1 T).differentiableAt
      (isOpen_upperHalfPlane.mem_nhds (hw.imag_positive T z hz))
  have hdf : deriv f w = deriv (F T) (G T z) * (‖q‖ : ℂ) := by
    dsimp only [f]
    rw [normalizedInverse_derivative _ _ _ _ hFdiff, heval]
  have hidentity := hw.inverse_derivative_identity T z hz
  have hFne : deriv (F T) (G T z) ≠ 0 := by
    intro he
    rw [he, zero_mul] at hidentity
    exact zero_ne_one hidentity
  have hnorm : ‖deriv f w‖ = ‖deriv (F T) (G T z)‖ * ‖q‖ := by
    rw [hdf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hnidentity : ‖deriv (F T) (G T z)‖ * ‖deriv (G T) z‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hidentity
  have hGpos := hw.derivative_norm_positive hU T z hz
  refine ⟨unitMarkedState_norm hq, hwim, ?_, hcharts.1, hcharts.2.1,
    by rw [hdf]; exact mul_ne_zero hFne (Complex.ofReal_ne_zero.mpr ha.ne'), ?_⟩
  · change F T ((U T : ℂ) + (‖q‖ : ℂ) * w) = z
    rw [heval, hw.2.2.2.2.2.2.2.1 T z hz]
  · rw [fullRadius, hnorm]
    change 2 * (q / (‖q‖ : ℂ)).im *
      (‖deriv (F T) (G T z)‖ * ‖q‖) = 2 * (G T z).im / ‖deriv (G T) z‖
    rw [Complex.div_ofReal_im]
    have hqi : q.im = (G T z).im := by simp only [q, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [hqi]
    apply (eq_div_iff hGpos.ne').mpr
    field_simp
    nlinarith [hnidentity]

end SLEExactGauge

end

end OAI
