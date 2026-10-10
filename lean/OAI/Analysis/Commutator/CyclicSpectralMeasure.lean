import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped ComplexOrder InnerProductSpace CompactlySupported

namespace Kadison.CyclicSpectral

variable {Ω H : Type*} [TopologicalSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def complexify (f : C_c(Ω,ℝ)) : C(Ω,ℂ) :=
  ⟨fun x => (f x:ℂ),Complex.continuous_ofReal.comp f.continuous⟩

lemma complexify_add (f g : C_c(Ω,ℝ)) : complexify (f+g)=complexify f+complexify g := by
  ext x
  simp [complexify]

lemma complexify_smul (r : ℝ) (f : C_c(Ω,ℝ)) : complexify (r•f)=(r:ℂ)•complexify f := by
  ext x
  simp [complexify]

lemma complexify_sub (f g : C_c(Ω,ℝ)) : complexify (f-g)=complexify f-complexify g := by
  ext x
  simp [complexify]

lemma complexify_nonneg {f : C_c(Ω,ℝ)} (hf : 0≤f) : 0≤complexify f := by
  intro x
  exact Complex.zero_le_real.mpr (hf x)

def vectorFunctional (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : C_c(Ω,ℝ) →ₚ[ℝ] ℝ where
  toFun f := (inner ℂ ξ (ρ (complexify f) ξ)).re
  map_add' f g := by simp [complexify_add]
  map_smul' r f := by
    rw [complexify_smul,map_smul]
    simp
  monotone' := by
    intro f g hfg
    have hp : 0≤ρ (complexify (g-f)) := map_nonneg ρ (complexify_nonneg (sub_nonneg.mpr hfg))
    have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).re_inner_nonneg_right ξ
    simpa [complexify_sub,inner_sub_right,sub_nonneg] using hi

variable [T2Space Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

def measure (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : Measure Ω :=
  RealRMK.rieszMeasure (vectorFunctional ρ ξ)

instance measure_regular (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    (measure ρ ξ).Regular := inferInstanceAs (RealRMK.rieszMeasure (vectorFunctional ρ ξ)).Regular

instance measure_finite (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    IsFiniteMeasure (measure ρ ξ) := inferInstance

lemma integral_real (ρ : C(Ω,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (f : C_c(Ω,ℝ)) :
    ∫ x,f x ∂measure ρ ξ=(inner ℂ ξ (ρ (complexify f) ξ)).re :=
  RealRMK.integral_rieszMeasure (vectorFunctional ρ ξ) f

end Kadison.CyclicSpectral

end

end
end

end OAI
