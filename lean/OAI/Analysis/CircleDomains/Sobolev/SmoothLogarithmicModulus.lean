import OAI.Analysis.CircleDomains.Sobolev.SmoothCircleOscillation
import OAI.Analysis.CircleDomains.Sobolev.RealPolarAnnulus
import OAI.Analysis.CircleDomains.Sobolev.LogarithmicEnergyBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! A logarithmic modulus for a homeomorphic height, expressed using a
uniformly close smooth approximation and its actual annular energy. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smoothCircleVariation_nonneg {f : ℂ → ℝ} (c : ℂ) (r : ℝ) :
    0 ≤ smoothCircleVariation f c r :=
  intervalIntegral.integral_nonneg (by positivity) (fun _ _ => abs_nonneg _)

 theorem homeomorphic_pair_sq_le_circle_energy (φ : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℂ) {r ε : ℝ} (hr : 0 < r)
    (_hε : 0 ≤ ε) (happrox : ∀ z ∈ sphere c r, |(φ z).im-f z| ≤ ε)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 - 8*ε^2 ≤
      16*Real.pi*r^2*(∫ θ in (0 : ℝ)..(2*Real.pi),
        ‖fderiv ℝ f (circleMap c r θ)‖^2) := by
  have hp := homeomorphic_pair_le_circle_variation φ hf c hr happrox hx hy
  have hv := smoothCircleVariation_nonneg (f := f) c r
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hp 2
  have hder := smoothCircleVariation_sq_le hf c r
  have hg : Continuous (fun θ => ‖fderiv ℝ f (circleMap c r θ)‖^2) :=
    (((hf.continuous_fderiv (by norm_num)).comp (continuous_circleMap c r)).norm.pow 2)
  have hd : Continuous (fun θ => (deriv (f ∘ circleMap c r) θ)^2) :=
    ((hf.comp (contDiff_circleMap c r)).continuous_deriv (by norm_num)).pow 2
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by positivity : (0 : ℝ) ≤ 2*Real.pi)
    (hd.intervalIntegrable _ _) ((continuous_const.mul hg).intervalIntegrable _ _)
    (fun θ _ => smooth_circle_deriv_sq_le hf c r θ)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hder' := hder.trans (mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ 2*Real.pi))
  nlinarith [sq_nonneg (smoothCircleVariation f c r-ε)]

 theorem homeomorphic_pair_logarithmic_smooth_bound (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {r R ε : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hε : 0 ≤ ε)
    (happrox : ∀ z ∈ closedBall c R, |(φ z).im-f z| ≤ ε)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    (|(φ x).im-(φ y).im|^2-8*ε^2)*Real.log (R/r) ≤
      16*Real.pi*(∫ z in {z : ℂ | r < dist z c ∧ dist z c < R}, ‖fderiv ℝ f z‖^2) := by
  let E : ℝ → ℝ := fun t => ∫ θ in (0 : ℝ)..(2*Real.pi),
    ‖fderiv ℝ f (circleMap c t θ)‖^2
  have hc : Continuous (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
    unfold circleMap
    fun_prop
  have hE : Continuous E :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (((hf.continuous_fderiv (by norm_num)).comp hc).norm.pow 2) _ _
  have hcircle : ∀ t ∈ Ioo r R,
      |(φ x).im-(φ y).im|^2-8*ε^2 ≤ 16*Real.pi*t^2*E t := by
    intro t ht
    apply homeomorphic_pair_sq_le_circle_energy φ hf c (hr.trans ht.1) hε
    · intro z hz
      exact happrox z ((closedBall_subset_closedBall ht.2.le) (sphere_subset_closedBall hz))
    · exact closedBall_subset_closedBall ht.1.le hx
    · exact closedBall_subset_closedBall ht.1.le hy
  have h := logarithmic_radial_bound hr hrR hE.continuousOn hcircle
  have heq := integral_polar_annulus_center
    ((hf.continuous_fderiv (by norm_num)).norm.pow 2) c hr.le hrR
  change (∫ z in {z : ℂ | r < dist z c ∧ dist z c < R}, ‖fderiv ℝ f z‖^2) =
    (∫ t in r..R, t*E t) at heq
  rwa [← heq] at h

end CircleDomainRigidity

end

end OAI
