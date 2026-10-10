import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralUnitTest

namespace OAI

/-! A locally integrable flux with zero weak derivative is constant on an interval. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralWeakFlux_constant (a b : ℝ) (hab : a < b) (F : ℝ → ℂ)
    (hF : LocallyIntegrable F)
    (hw : ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ Icc a b → ∫ x, deriv Φ x • F x = 0) :
    ∃ c : ℂ, ∀ᵐ x, x ∈ Ioo a b → F x=c := by
  obtain ⟨β,hβ,hβc,hβs,hβi⟩ := spectralUnitTest a b hab
  let c : ℂ := ∫ x, β x • F x
  refine ⟨c,?_⟩
  have hfc : LocallyIntegrable (fun x => F x-c) := hF.sub (locallyIntegrable_const c)
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hfc.locallyIntegrableOn (Ioo a b))
  have ha : ∀ᵐ x, x ∈ Ioo a b → F x-c=0 := by
    apply hz
    intro φ hφ hφc hφs
    let d : ℝ := ∫ x, φ x
    let ψ := fun x => φ x-d*β x
    have hd : ContDiff ℝ ∞ ψ := hφ.sub (contDiff_const.mul hβ)
    have hψs : Function.support ψ ⊆ Ioo a b := by
      intro x hx
      by_contra h
      have h1 : φ x=0 := Function.notMem_support.mp (fun hx => h (hφs (subset_tsupport _ hx)))
      have h2 : β x=0 := Function.notMem_support.mp (fun hx => h (hβs (subset_tsupport _ hx)))
      exact hx (by simp [ψ,h1,h2])
    have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hβi' : Integrable β := hβ.continuous.integrable_of_hasCompactSupport hβc
    have hψi : ∫ x, ψ x=0 := by
      simp only [ψ]
      rw [integral_sub hφi (hβi'.const_mul d),integral_const_mul,hβi,mul_one]
      exact sub_self d
    obtain ⟨Φ,hΦ,hΦc,hΦs,hΦd⟩ := spectralTestPrimitive a b ψ hd hψs hψi
    have hp : ∫ x, ψ x • F x=0 := by
      simpa only [hΦd] using hw Φ hΦ hΦc hΦs
    have hφF := hF.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hβF := hF.integrable_smul_left_of_hasCompactSupport hβ.continuous hβc
    have hrel : (∫ x, φ x • F x)=d • c := by
      have he : (∫ x, ψ x • F x)=(∫ x, φ x • F x)-d • c := by
        have heq : (fun x => ψ x • F x)=
            (fun x => φ x • F x-d • (β x • F x)) := by
          funext x
          dsimp only [ψ]
          rw [sub_smul,smul_smul]
        rw [heq,integral_sub,integral_smul]
        · exact hφF
        · exact hβF.smul d
      rw [he] at hp
      exact sub_eq_zero.mp hp
    simp only [smul_sub]
    rw [integral_sub hφF (hφi.smul_const c),integral_smul_const,hrel,sub_self]
  filter_upwards [ha] with x hx hxab
  exact sub_eq_zero.mp (hx hxab)

end DefocusingNLS

end OAI
