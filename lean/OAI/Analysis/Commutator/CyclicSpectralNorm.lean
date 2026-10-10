import Mathlib
import OAI.Analysis.Commutator.CyclicSpectralMeasure

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped ComplexOrder InnerProductSpace CompactlySupported ComplexConjugate

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω] [T2Space Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def normSqFunction (f : C(Ω,ℂ)) : C_c(Ω,ℝ) :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    ⟨fun x => Complex.normSq (f x),Complex.continuous_normSq.comp f.continuous⟩

omit [T2Space Ω] [MeasurableSpace Ω] [BorelSpace Ω] in
lemma complexify_normSq (f : C(Ω,ℂ)) : complexify (normSqFunction f)=star f*f := by
  ext x
  change (Complex.normSq (f x):ℂ)=star (f x)*f x
  simp [Complex.normSq_eq_conj_mul_self]

lemma representation_norm_integral (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : C(Ω,ℂ)) :
    ‖ρ f ξ‖^2=∫ x,Complex.normSq (f x) ∂measure ρ ξ := by
  have hi := integral_real ρ ξ (normSqFunction f)
  rw [complexify_normSq,map_mul,map_star] at hi
  change (∫ x,Complex.normSq (f x) ∂measure ρ ξ)=
    (inner ℂ ξ ((ρ f).adjoint (ρ f ξ))).re at hi
  rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K] at hi
  change (∫ x,Complex.normSq (f x) ∂measure ρ ξ)=
    ((Complex.ofReal ‖ρ f ξ‖)^2).re at hi
  rw [←Complex.ofReal_pow, Complex.ofReal_re] at hi
  exact hi.symm

lemma toLp_norm_eq (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : C(Ω,ℂ)) :
    ‖ContinuousMap.toLp 2 (measure ρ ξ) ℂ f‖=‖ρ f ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),MeasureTheory.ContinuousMap.inner_toLp]
  simp_rw [Complex.mul_conj]
  rw [integral_complex_ofReal]
  simpa using (representation_norm_integral ρ ξ f).symm

end Kadison.CyclicSpectral

end

end
end

end OAI
