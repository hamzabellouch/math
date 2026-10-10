import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
variable {ι κ : Type*} [Fintype κ]

theorem additive_noise_lintegral (μ : Measure (ι → ℝ)) [SFinite μ]
    (φ : (κ → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (L : (ι → ℝ) → (κ → ℝ)) (hL : Measurable L)
    (F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1,L z.1+z.2) ∂μ.prod ((volume : Measure (κ → ℝ)).withDensity φ)) =
      ∫⁻ y, ∫⁻ x, φ (y-L x)*F (x,y) ∂μ ∂volume := by
  rw [lintegral_prod _ (by fun_prop)]
  have he (x : ι → ℝ) :
      (∫⁻ e, F (x,L x+e) ∂(volume : Measure (κ → ℝ)).withDensity φ)=
      ∫⁻ y, φ (y-L x)*F (x,y) ∂volume := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hφ (by fun_prop)]
    have hh := lintegral_add_left_eq_self
      (μ := (volume : Measure (κ → ℝ))) (fun y => φ (y-L x)*F (x,y)) (L x)
    simpa only [Pi.mul_apply,add_sub_cancel_left] using hh
  simp only [he]
  exact lintegral_lintegral_swap (by fun_prop)

theorem residual_density_lintegral (ρ : Measure (ι → ℝ)) [SFinite ρ]
    (p : (κ → ℝ) → ℝ≥0∞) (hp : Measurable p)
    (K : (κ → ℝ) → (ι → ℝ)) (hK : Measurable K)
    (F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1+K z.2,z.2) ∂ρ.prod ((volume : Measure (κ → ℝ)).withDensity p)) =
      ∫⁻ y, p y*(∫⁻ r, F (r+K y,y) ∂ρ) ∂volume := by
  rw [lintegral_prod_symm _ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop)]
  rfl

theorem kernel_test_ae (μ ρ : Measure (ι → ℝ)) [SFinite μ] [SFinite ρ]
    {φ p : (κ → ℝ) → ℝ≥0∞} (hφ : Measurable φ) (hp : Measurable p)
    {L : (ι → ℝ) → (κ → ℝ)} {K : (κ → ℝ) → (ι → ℝ)}
    (hL : Measurable L) (hK : Measurable K)
    (hjoint : (μ.prod ((volume : Measure (κ → ℝ)).withDensity φ)).map
      (fun z => (z.1,L z.1+z.2)) =
      (ρ.prod ((volume : Measure (κ → ℝ)).withDensity p)).map
        (fun z => (z.1+K z.2,z.2)))
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ)=ᵐ[volume]
      (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) := by
  have h1 : Measurable (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ) := by fun_prop
  have h2 : Measurable (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) := by fun_prop
  apply (withDensity_eq_iff_of_sigmaFinite h1.aemeasurable h2.aemeasurable).mp
  ext s hs
  rw [withDensity_apply _ hs,withDensity_apply _ hs]
  let F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞ := fun z => s.indicator (fun _ => f z.1) z.2
  have hF : Measurable F := by
    exact (hf.comp measurable_fst).indicator (hs.preimage measurable_snd)
  have hh := congrArg (fun ν => ∫⁻ z, F z ∂ν) hjoint
  rw [lintegral_map hF (by fun_prop),lintegral_map hF (by fun_prop),
    additive_noise_lintegral μ φ hφ L hL F hF,
    residual_density_lintegral ρ p hp K hK F hF] at hh
  have he1 (y : κ → ℝ) : (∫⁻ x, φ (y-L x)*F (x,y) ∂μ)=
      s.indicator (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ) y := by
    by_cases hy : y ∈ s <;> simp [F,hy]
  have he2 (y : κ → ℝ) : p y*(∫⁻ r, F (r+K y,y) ∂ρ)=
      s.indicator (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) y := by
    by_cases hy : y ∈ s <;> simp [F,hy]
  simp_rw [he1,he2] at hh
  simpa only [lintegral_indicator hs] using hh

end SKGap.GaussianDensity
end
end

end OAI
