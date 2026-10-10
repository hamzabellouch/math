import OAI.Probability.InvariantIsing.Spectral.CompactTestsInMeasure

namespace OAI

/-! Positive resolvents as a separating family for compact nonnegative spectral laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

def compactResolventTest (R : ℝ) (t : {t : ℝ // 0 < t}) : Icc (0 : ℝ) R →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => positiveResolventTest t x,
      (continuous_positiveResolventTest t.property).comp continuous_subtype_val⟩

lemma compactResolventTests_separate (R : ℝ) (μ ν : ProbabilityMeasure (Icc (0 : ℝ) R))
    (h : ∀ t : {t : ℝ // 0 < t},
      (∫ x, compactResolventTest R t x ∂(μ : Measure _)) =
        ∫ x, compactResolventTest R t x ∂(ν : Measure _)) : μ = ν := by
  have hnonneg (η : ProbabilityMeasure (Icc (0 : ℝ) R)) :
      ∀ᵐ x ∂(η.map (fun x => (x : ℝ)) : Measure ℝ), 0 ≤ x := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Ici).mpr
    exact ae_of_all _ fun x => x.property.1
  have he := positiveResolvent_unique (μ.map (fun x => (x : ℝ)) : Measure ℝ)
    (ν.map (fun x => (x : ℝ)) : Measure ℝ) (hnonneg μ) (hnonneg ν) (fun t ht => ?_)
  · apply ProbabilityMeasure.toMeasure_injective
    apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
    exact he
  · simp only [ProbabilityMeasure.toMeasure_map]
    rw [integral_map measurable_subtype_coe.aemeasurable
      (continuous_positiveResolventTest ht).aestronglyMeasurable,
      integral_map measurable_subtype_coe.aemeasurable
      (continuous_positiveResolventTest ht).aestronglyMeasurable]
    exact h ⟨t,ht⟩

theorem compact_resolvent_tendstoInMeasure (R : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℕ → Ω → ProbabilityMeasure (Icc (0 : ℝ) R)) (ν : ProbabilityMeasure (Icc (0 : ℝ) R))
    (h : ∀ t : {t : ℝ // 0 < t}, TendstoInMeasure P
      (fun n ω => ∫ x, compactResolventTest R t x ∂(Z n ω : Measure _)) Filter.atTop
      (fun _ => ∫ x, compactResolventTest R t x ∂(ν : Measure _))) :
    TendstoInMeasure P
      (fun n ω => LevyProkhorov.ofMeasure ((Z n ω).map (fun x => (x : ℝ)))) Filter.atTop
      (fun _ => LevyProkhorov.ofMeasure (ν.map (fun x => (x : ℝ)))) := by
  let F : {t : ℝ // 0 < t} → ProbabilityMeasure (Icc (0 : ℝ) R) → ℝ :=
    fun t η => ∫ x, compactResolventTest R t x ∂(η : Measure _)
  let G : ProbabilityMeasure (Icc (0 : ℝ) R) → LevyProkhorov (ProbabilityMeasure ℝ) :=
    fun η => LevyProkhorov.ofMeasure (η.map (fun x : Icc (0 : ℝ) R => (x : ℝ)))
  have hF : ∀ t, Continuous (F t) := fun t =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (compactResolventTest R t)
  have hG : Continuous G :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp
      (ProbabilityMeasure.continuous_map (f := fun x : Icc (0 : ℝ) R => (x : ℝ)) continuous_subtype_val)
  exact compact_tests_tendstoInMeasure P F hF (compactResolventTests_separate R) G hG ν Z h

end InvariantIsing

end

end OAI
