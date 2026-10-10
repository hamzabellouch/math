import OAI.MathematicalPhysics.Boltzmann.Branching.L2PairingBound
import OAI.MathematicalPhysics.Boltzmann.Branching.SpacetimeFourierCoordinates

namespace OAI

section

/-! # The L2 Fourier transform and the classical integral have the same smooth pairings -/
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace BoltzmannNonuniqueness.Published

theorem fourier_L2_schwartz_pairing {f : FourierSpace → ℂ} (hf : MemLp f 2 volume)
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * (𝓕 (hf.toLp f) : Lp ℂ 2 volume) x) = ∫ x, (𝓕 g) x * f x := by
  let a : Lp ℂ 2 volume := hf.toLp f
  have h := congrArg (fun T : 𝓢'(FourierSpace, ℂ) => T g)
    (Lp.fourier_toTemperedDistribution_eq a)
  simp only [TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply] at h
  calc
    _ = ∫ x, (𝓕 g) x * a x := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

theorem fourier_integral_schwartz_pairing {f : FourierSpace → ℂ} (hf : Integrable f)
    (g : 𝓢(FourierSpace, ℂ)) :
    (∫ x, g x * 𝓕 f x) = ∫ x, (𝓕 g) x * f x := by
  have he : (innerₗ FourierSpace).flip = innerₗ FourierSpace := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm x y
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure FourierSpace))
    (ν := (volume : Measure FourierSpace)) (L := innerₗ FourierSpace)
    Real.continuous_fourierChar continuous_inner g.integrable hf
  rw [he] at h
  exact h.symm

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Classical and Hilbert-space Fourier transforms agree on L1 intersect L2 -/
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap Topology
namespace BoltzmannNonuniqueness.Published

theorem fourier_L2_ae_eq_integral {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    (fun x => (𝓕 (h₂.toLp f) : Lp ℂ 2 volume) x) =ᵐ[volume] 𝓕 f := by
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (h₂.toLp f))).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
  let ψ : 𝓢(FourierSpace, ℂ) := hs'.toSchwartzMap hg'
  have h := (fourier_L2_schwartz_pairing h₂ ψ).trans
    (fourier_integral_schwartz_pairing hf ψ).symm
  change (∫ x, (g x : ℂ) * (𝓕 (h₂.toLp f) : Lp ℂ 2 volume) x) =
    ∫ x, (g x : ℂ) * 𝓕 f x at h
  simpa only [Complex.real_smul] using h

theorem fourier_integral_memLp {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  (Lp.memLp (𝓕 (h₂.toLp f))).ae_eq (fourier_L2_ae_eq_integral hf h₂)

theorem fourier_integral_norm_sq {f : FourierSpace → ℂ}
    (hf : Integrable f) (h₂ : MemLp f 2 volume) :
    (∫ x, ‖𝓕 f x‖^2) = ∫ x, ‖f x‖^2 := by
  calc
    _ = ∫ x, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2 volume) x‖^2 := by
      apply integral_congr_ae
      filter_upwards [fourier_L2_ae_eq_integral hf h₂] with x hx
      rw [hx]
    _ = ‖𝓕 (h₂.toLp f)‖^2 := (L2_norm_sq_integral _).symm
    _ = ‖h₂.toLp f‖^2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖f x‖^2 := by
      rw [L2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]

end BoltzmannNonuniqueness.Published

end

end

end OAI
