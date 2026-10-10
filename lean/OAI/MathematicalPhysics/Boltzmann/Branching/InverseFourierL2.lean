import OAI.MathematicalPhysics.Boltzmann.Collision.FourierL2Identification

namespace OAI

/-! # The inverse Fourier integral agrees with the inverse L2 transform -/
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap Topology
namespace BoltzmannNonuniqueness.Published

theorem inverseFourier_L2_pairing (a : Lp ℂ 2 (volume : Measure FourierSpace))
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * (𝓕⁻ a : Lp ℂ 2 volume) x) = ∫ x, (𝓕⁻ g) x * a x := by
  have h := congrArg (fun T : 𝓢'(FourierSpace, ℂ) => T g)
    (Lp.fourierInv_toTemperedDistribution_eq a)
  simpa only [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] using h.symm

theorem inverseFourier_integral_pairing {f : FourierSpace → ℂ} (hf : Integrable f)
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * 𝓕⁻ f x) = ∫ x, (𝓕⁻ g) x * f x := by
  have he : (-innerₗ FourierSpace).flip = -innerₗ FourierSpace := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact congrArg Neg.neg (real_inner_comm x y)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure FourierSpace))
    (ν := (volume : Measure FourierSpace)) (L := -innerₗ FourierSpace)
    Real.continuous_fourierChar continuous_inner.neg g.integrable hf
  rw [he] at h
  have h' : (∫ x, g x * 𝓕⁻ f x) = ∫ x, 𝓕⁻ (g : FourierSpace → ℂ) x * f x := by
    simpa only [Real.fourierInv_eq,VectorFourier.fourierIntegral,LinearMap.neg_apply,
      neg_neg,smul_eq_mul,innerₗ_apply_apply] using h.symm
  simpa only [← SchwartzMap.fourierInv_coe] using h'

theorem inverseFourier_L2_ae_eq_integral {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    (fun x => (𝓕⁻ (h₂.toLp f) : Lp ℂ 2 volume) x) =ᵐ[volume] 𝓕⁻ f := by
  have hc : Continuous (𝓕⁻ f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner.neg hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕⁻ (h₂.toLp f))).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ : 𝓢(FourierSpace, ℂ) := hs'.toSchwartzMap hg'
  have h₁ := inverseFourier_L2_pairing (h₂.toLp f) ψ
  have h₂' : (∫ x, (𝓕⁻ ψ) x * (h₂.toLp f) x) = ∫ x, (𝓕⁻ ψ) x * f x := by
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    rw [hx]
  have h := (h₁.trans h₂').trans (inverseFourier_integral_pairing hf ψ).symm
  change (∫ x, (g x : ℂ) * (𝓕⁻ (h₂.toLp f) : Lp ℂ 2 volume) x) =
    ∫ x, (g x : ℂ) * 𝓕⁻ f x at h
  simpa only [Complex.real_smul] using h

end BoltzmannNonuniqueness.Published

end

end OAI
