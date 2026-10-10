import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Bessel
import OAI.Geometry.TamingCompatibility.Currents.BoundedDistribution

namespace OAI

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace
namespace TamingCompatibility.EuclideanSobolev
open TemperedDistribution
open scoped ENNReal ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma negative_weight_moment (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    r^n * (1+r^2)^(-(2*(n:ℝ))/2) ≤ 1 := by
  have he : -(2*(n:ℝ))/2 = -(n:ℝ) := by ring
  rw [he, Real.rpow_neg (by positivity), Real.rpow_natCast]
  apply (mul_inv_le_iff₀ (pow_pos (by positivity) _)).mpr
  simp only [one_mul]
  exact pow_le_pow_left₀ hr (by nlinarith [sq_nonneg (r - 1/2)]) n

lemma fourier_moments_of_all_orders {u : 𝓢'(E,F)}
    (hu : ∀ s : ℝ, MemSobolev s 2 u)
    (v : Lp F 1 (volume : Measure E)) (hv : 𝓕 u = (v : 𝓢'(E,F))) (n : ℕ) :
    Integrable (fun ξ : E => ‖ξ‖^n * ‖v ξ‖) := by
  let s : ℝ := Module.finrank ℝ E + 1
  have hs : Module.finrank ℝ E < 2*s := by
    dsimp [s]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  have hn : MemSobolev s 2 (besselPotential E F (2*(n:ℝ)) u) := by
    rw [memSobolev_besselPotential_iff]
    exact hu _
  obtain ⟨w,hw⟩ := hn.fourier_memL1 hs
  let b := RellichWeight.bessel (E := E) (2*(n:ℝ)) (by positivity)
  have hb : (b : E → ℂ).HasTemperateGrowth := by
    change (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(2*(n:ℝ))/2))).HasTemperateGrowth
    fun_prop
  let z : Lp F 1 (volume : Measure E) := ((b.memLp_top (μ := volume)).toLp b) • w
  have hz : (z : 𝓢'(E,F)) = (v : 𝓢'(E,F)) := by
    rw [Lp.toTemperedDistribution_smul_eq hb (b.memLp_top (μ := volume)), ← hw]
    change smulLeftCLM F (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(2*(n:ℝ))/2)))
      (𝓕 (besselPotential E F (2 * (n:ℝ)) u)) = _
    rw [← fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      besselPotential_besselPotential_apply]
    simpa using hv
  have hzv : z = v := (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot) hz
  have hae : ∀ᵐ ξ ∂(volume : Measure E), v ξ = b ξ • w ξ := by
    filter_upwards [Lp.coeFn_lpSMul (r := (1:ℝ≥0∞)) ((b.memLp_top (μ := volume)).toLp b) w,
      (b.memLp_top (μ := volume)).coeFn_toLp] with ξ hz hb'
    change z ξ = _ at hz
    rw [hzv] at hz
    change v ξ = ((b.memLp_top (μ := volume)).toLp b) ξ • w ξ at hz
    rw [hb'] at hz
    exact hz
  apply (memLp_one_iff_integrable.mp (Lp.memLp w)).norm.mono'
    ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards [hae] with ξ hξ
  change ‖‖ξ‖^n * ‖v ξ‖‖ ≤ ‖w ξ‖
  rw [hξ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change ‖ξ‖^n * (‖(((1+‖ξ‖^2)^(-(2*(n:ℝ))/2) : ℝ) : ℂ)‖ * ‖w ξ‖) ≤ ‖w ξ‖
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right (negative_weight_moment n ‖ξ‖ (norm_nonneg ξ))
    (norm_nonneg (w ξ))).trans_eq (one_mul _)

theorem exists_smooth_representative {u : 𝓢'(E,F)}
    (hu : ∀ s : ℝ, MemSobolev s 2 u) :
    ∃ g : E →ᵇ F, ContDiff ℝ ∞ (g : E → F) ∧ u = boundedDistribution g := by
  have hs : Module.finrank ℝ E < 2*((Module.finrank ℝ E : ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  obtain ⟨v,hv⟩ := (hu _).fourier_memL1 hs
  refine ⟨Real.Lp.fourierTransformInv v, ?_, ?_⟩
  · have hc : ContDiff ℝ ∞ (𝓕 (v : E → F)) :=
      Real.contDiff_fourier (fun n _ => fourier_moments_of_all_orders hu v hv n)
    have he : (Real.Lp.fourierTransformInv v : E → F) = 𝓕⁻ (v : E → F) := by
      ext x
      exact Real.Lp.fourierTransformInv_apply v x
    rw [he]
    have he' : 𝓕⁻ (v : E → F) = (𝓕 (v : E → F)) ∘ Neg.neg := by
      ext x
      exact Real.fourierInv_eq_fourier_neg _ x
    rw [he']
    exact hc.comp contDiff_neg
  · rw [← inverseFourier_boundedDistribution, ← hv, fourierInv_fourier_eq]

end TamingCompatibility.EuclideanSobolev

end

end OAI
