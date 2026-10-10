import OAI.Probability.SLE.Geometry.RestartGreenCovariance
import OAI.Probability.SLE.Gauge.ConformalSausageTransfer

namespace OAI

/-! Change of variables for the conditional Green potential at a restart.
The identity accepts arbitrary nonnegative spatial tests. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

theorem IsCapacityTwoWitness.restart_green_integral
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T+t)-U T) β G' F')
    (κ : ℝ) (t : ℝ≥0) (f : ℂ → ℝ≥0∞) :
    (∫⁻ x in survivingDomain γ T, f x * ENNReal.ofReal (greenDensity κ U γ G (T+t) x)) =
      ∫⁻ z in upperHalfPlane, f (F T (z+(U T:ℂ))) *
        ENNReal.ofReal (‖deriv (F T) (z+(U T:ℂ))‖^(dimension κ)) *
        ENNReal.ofReal (greenDensity κ (fun r => U (T+r)-U T) β G' t z) := by
  let J : ℂ → ℂ := fun z => F T (z+(U T:ℂ))
  have hshift (z : ℂ) (hz : z ∈ upperHalfPlane) : z+(U T:ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero] using hz
  have himage : J '' upperHalfPlane = survivingDomain γ T := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hw.2.2.2.2.2.2.1 T (hshift z hz)
    · intro hy
      refine ⟨G T y-(U T:ℂ),?_,?_⟩
      · simpa only [upperHalfPlane,mem_ofPred_eq,Complex.sub_im,Complex.ofReal_im,sub_zero]
          using hw.2.2.2.2.2.1 T hy
      · change F T ((G T y-(U T:ℂ))+(U T:ℂ)) = y
        rw [sub_add_cancel,hw.2.2.2.2.2.2.2.1 T y hy]
  have hinj : InjOn J upperHalfPlane := by
    intro z hz v hv he
    have h := congrArg (G T) he
    change G T (F T (z+(U T:ℂ))) = G T (F T (v+(U T:ℂ))) at h
    rw [hw.2.2.2.2.2.2.2.2.1 T _ (hshift z hz),
      hw.2.2.2.2.2.2.2.2.1 T _ (hshift v hv)] at h
    exact add_right_cancel h
  have hd (z : ℂ) (hz : z ∈ upperHalfPlane) :
      HasDerivAt J (deriv (F T) (z+(U T:ℂ))) z := by
    have h := ((hw.2.2.2.2.1 T).differentiableAt
      (isOpen_upperHalfPlane.mem_nhds (hshift z hz))).hasDerivAt.comp z
      ((hasDerivAt_id z).add_const (U T:ℂ))
    simpa only [Function.comp_def,id_eq,mul_one,J] using h
  rw [← himage]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume isOpen_upperHalfPlane.measurableSet
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj]
  apply setLIntegral_congr_fun isOpen_upperHalfPlane.measurableSet
  intro z hz
  dsimp only
  rw [complex_derivative_real_det,abs_of_nonneg (sq_nonneg _)]
  have he := congrArg ENNReal.ofReal (hw.restart_green_area_covariance hU T hb κ t z hz)
  rw [ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)] at he
  change ENNReal.ofReal (‖deriv (F T) (z+(U T:ℂ))‖^2) *
    (f (J z) * ENNReal.ofReal (greenDensity κ U γ G (T+t) (J z))) = _
  calc
    _ = f (J z) * (ENNReal.ofReal (‖deriv (F T) (z+(U T:ℂ))‖^2) *
        ENNReal.ofReal (greenDensity κ U γ G (T+t) (J z))) := by ring
    _ = _ := by rw [he]; ac_rfl

end SLEExactGauge

end

end OAI
