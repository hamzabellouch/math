import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicDescent

namespace OAI

noncomputable section
open scoped Topology
open Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

 

def adelicTorusHaar (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) : Measure (TorusQuotient K) := by
  let := adelic_torus_quotient_compact d hprime hdegree K hn
  exact Measure.haarMeasure ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩

lemma adelicTorusHaar_probability (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) : IsProbabilityMeasure (adelicTorusHaar d hprime hdegree K hn) := by
  constructor
  exact Measure.haarMeasure_self

lemma adelicTorusHaar_invariant (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) : Measure.IsMulLeftInvariant (adelicTorusHaar d hprime hdegree K hn) := by
  delta adelicTorusHaar
  infer_instance

lemma adelicTorusHaar_isHaar (d : ℕ) (hprime : (d+1).Prime) (hdegree : 5 ≤ d+1)
    (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (hn : finrank ℚ K = d+1) : Measure.IsHaarMeasure (adelicTorusHaar d hprime hdegree K hn) := by
  delta adelicTorusHaar
  infer_instance

end PrimeDegreePackets.Adelic

end

end OAI
