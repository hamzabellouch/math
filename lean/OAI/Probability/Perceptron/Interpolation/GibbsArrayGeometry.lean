import Mathlib
import OAI.Probability.Perceptron.Interpolation.CompactArrayMap
import OAI.Probability.Perceptron.Interpolation.GibbsOverlapArray

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
section
variable {A S K : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [CompactSpace K]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))
variable (Q : S → S → K) (hQ : Measurable (Function.uncurry Q))

omit [CompactSpace K] in
lemma gibbsOverlapArray_exchangeable (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=K) e)
      (gibbsOverlapArrayLaw κ P H hH Q hQ : Measure _)
      (gibbsOverlapArrayLaw κ P H hH Q hQ : Measure _) := by
  have hr := annealedInfiniteReplica_reindex κ P H hH e
  have hm : Measurable (fun a : A×(ℕ→S) => overlapArray Q a.2) :=
    (overlapArray_measurable Q hQ).comp measurable_snd
  refine ⟨(compactRelabel_continuous e).measurable,?_⟩
  change Measure.map _ (Measure.map (fun a : A×(ℕ→S) => overlapArray Q a.2) _) = _
  rw [Measure.map_map (compactRelabel_continuous e).measurable hm]
  change Measure.map ((fun a : A×(ℕ→S) => overlapArray Q a.2) ∘
    (fun a : A×(ℕ→S) => (a.1,fun i => a.2 (e i)))) _ = _
  rw [← Measure.map_map hm hr.measurable,hr.map_eq]
  rfl

omit [CompactSpace K] in
lemma gibbsOverlapArray_closed_full {F : Set (CompactArray K)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→S, overlapArray Q x ∈ F) :
    gibbsOverlapArrayLaw κ P H hH Q hQ F=1 := by
  have hp : (fun a : A×(ℕ→S) => overlapArray Q a.2) ⁻¹' F=univ := by
    ext a
    simp only [mem_preimage,mem_univ,iff_true]
    exact hfull a.2
  apply ENNReal.coe_injective
  rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  change (Measure.map (fun a : A×(ℕ→S) => overlapArray Q a.2) _) F=1
  have hm : Measurable (fun a : A×(ℕ→S) => overlapArray Q a.2) :=
    (overlapArray_measurable Q hQ).comp measurable_snd
  rw [Measure.map_apply hm hF.measurableSet,hp]
  exact measure_univ
end

lemma compactMapLaw_exchangeable {K L : Type*} [TopologicalSpace K] [TopologicalSpace L]
    [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
    [SecondCountableTopology K] [SecondCountableTopology L]
    (f : K→L) (hf : Continuous f) (μ : ProbabilityMeasure (CompactArray K))
    (e : Equiv.Perm ℕ)
    (he : MeasurePreserving (compactRelabel (K:=K) e) (μ : Measure _) (μ : Measure _)) :
    MeasurePreserving (compactRelabel (K:=L) e) (compactMapLaw f hf μ : Measure _)
      (compactMapLaw f hf μ : Measure _) := by
  refine ⟨(compactRelabel_continuous e).measurable,?_⟩
  change Measure.map _ (Measure.map (compactMapArray f) _) = _
  rw [Measure.map_map (compactRelabel_continuous e).measurable (compactMapArray_continuous hf).measurable]
  change Measure.map (compactMapArray f ∘ compactRelabel e) _ = _
  rw [← Measure.map_map (compactMapArray_continuous hf).measurable he.measurable,he.map_eq]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
