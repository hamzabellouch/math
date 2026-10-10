import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! The compact-space representation step for the measure-modulus dual:
a positive linear functional taking the constant one to one is a genuine
probability law. This is the existing Riesz representation theorem. -/
open Set MeasureTheory
open scoped CompactlySupported
noncomputable section
namespace CircleDomainRigidity

lemma exists_probability_of_compact_positive_functional
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (h1 : Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ = 1) :
    ∃ P : ProbabilityMeasure X, ∀ f : C_c(X,ℝ), ∫ x, f x ∂(P : Measure X) = Λ f := by
  let μ := RealRMK.rieszMeasure Λ
  have hm : μ univ = 1 := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    have hi := RealRMK.integral_rieszMeasure Λ
      (⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ : C_c(X,ℝ))
    rw [h1] at hi
    change (∫ _x : X, (1 : ℝ) ∂μ) = 1 at hi
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def] using hi
  let : IsProbabilityMeasure μ := ⟨hm⟩
  exact ⟨⟨μ,inferInstance⟩,RealRMK.integral_rieszMeasure Λ⟩

lemma exists_probability_of_compact_positive_functional_trim
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [m : MeasurableSpace X] (hm : m ≤ borel X)
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (h1 : Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ = 1) :
    ∃ P : ProbabilityMeasure X, ∀ f : C_c(X,ℝ), Measurable f →
      (∫ x, f x ∂(P : Measure X)) = Λ f := by
  have hex : ∃ μ : @Measure X (borel X), μ univ = 1 ∧
      ∀ f : C_c(X,ℝ), (∫ x, f x ∂μ) = Λ f := by
    let : MeasurableSpace X := borel X
    let : BorelSpace X := ⟨rfl⟩
    obtain ⟨P,hP⟩ := exists_probability_of_compact_positive_functional Λ h1
    exact ⟨(P : Measure X),measure_univ,hP⟩
  obtain ⟨μ,hμ,hint⟩ := hex
  let ν : Measure X := μ.trim hm
  have hn : ν univ = 1 := by
    change μ.trim hm univ = 1
    rw [trim_measurableSet_eq hm MeasurableSet.univ]
    exact hμ
  let : IsProbabilityMeasure ν := ⟨hn⟩
  refine ⟨⟨ν,inferInstance⟩,?_⟩
  intro f hf
  change (∫ x, f x ∂μ.trim hm) = Λ f
  rw [← integral_trim hm hf.stronglyMeasurable]
  exact hint f

end CircleDomainRigidity

end

end OAI
