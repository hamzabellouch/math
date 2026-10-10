import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ProductNormalize

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma lintegral_ignore_coordinate (μ ν : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (j : I) (he : ∀i,i≠j→μ i=ν i)
    (F : (∀i,X i)→ℝ≥0∞) (hF : Measurable F)
    (hignore : ∀x y,F (Function.update x j y)=F x) :
    (∫⁻x,F x ∂Measure.pi μ)=∫⁻x,F x ∂Measure.pi ν := by
  let x₀ : ∀i,X i := fun i ↦ Classical.choice (nonempty_of_isProbabilityMeasure (μ i))
  rw [lintegral_eq_lmarginal_univ (μ:=μ) x₀,lintegral_eq_lmarginal_univ (μ:=ν) x₀,
    lmarginal_erase' (μ:=μ) F hF (Finset.mem_univ j),lmarginal_erase' (μ:=ν) F hF (Finset.mem_univ j)]
  simp_rw [hignore,lintegral_const,measure_univ,mul_one]
  unfold lmarginal
  congr 2
  funext i
  exact he i (Finset.mem_erase.mp i.property).1

lemma conditioned_lintegral_ignore (μ ν : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (j : I) (he : ∀i,i≠j→μ i=ν i)
    (A : Set (∀i,X i)) (hA : MeasurableSet A)
    (hAi : ∀x y,Function.update x j y∈A↔x∈A)
    (F : (∀i,X i)→ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀x y,F (Function.update x j y)=F x) :
    (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) A)=
      ∫⁻x,F x ∂conditionedMeasure (Measure.pi ν) A := by
  have hw (x : ∀i,X i) (y : X j) :
      A.indicator (fun _ ↦ (1:ℝ≥0∞)) (Function.update x j y)=A.indicator (fun _ ↦ 1) x := by
    by_cases hx : x∈A
    · rw [indicator_of_mem ((hAi x y).mpr hx),indicator_of_mem hx]
    · rw [indicator_of_notMem ((hAi x y).not.mpr hx),indicator_of_notMem hx]
  have hm : (Measure.pi μ) A=(Measure.pi ν) A := by
    have hh := lintegral_ignore_coordinate μ ν j he _ (measurable_const.indicator hA) hw
    simpa only [lintegral_indicator_const hA,one_mul] using hh
  rw [conditionedMeasure,conditionedMeasure,lintegral_smul_measure,lintegral_smul_measure,hm]
  congr 1
  rw [←lintegral_indicator hA,←lintegral_indicator hA]
  apply lintegral_ignore_coordinate μ ν j he _ (hF.indicator hA)
  intro x y
  by_cases hx : x∈A
  · rw [indicator_of_mem ((hAi x y).mpr hx),indicator_of_mem hx,hFi]
  · rw [indicator_of_notMem ((hAi x y).not.mpr hx),indicator_of_notMem hx]

lemma conditioned_map_ignore {Y : Type*} [MeasurableSpace Y]
    (μ ν : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (j : I) (he : ∀i,i≠j→μ i=ν i)
    (A : Set (∀i,X i)) (hA : MeasurableSet A)
    (hAi : ∀x y,Function.update x j y∈A↔x∈A)
    (f : (∀i,X i)→Y) (hf : Measurable f)
    (hfi : ∀x y,f (Function.update x j y)=f x) :
    (conditionedMeasure (Measure.pi μ) A).map f=
      (conditionedMeasure (Measure.pi ν) A).map f := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf,lintegral_map hF hf]
  apply conditioned_lintegral_ignore μ ν j he A hA hAi _ (hF.comp hf)
  intro x y
  simp only [Function.comp_def,hfi]

end HardSphere.Comparison

end
end

end

end OAI
