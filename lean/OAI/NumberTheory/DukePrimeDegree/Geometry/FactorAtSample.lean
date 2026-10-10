import OAI.NumberTheory.DukePrimeDegree.Entropy.PrefixPointConditionals
import OAI.NumberTheory.DukePrimeDegree.Geometry.SampledFactorIdentification

namespace OAI

/-! # Recovering an independent factor at its current sampled point -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma factor_of_conjugated_fst (d : ℕ) (q : InitialRootStep (d+1))
    (κ : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ))
    (hp : κ = κ.fst.prod κ.snd)
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (t : ℝ)
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hV : MeasurableSet V)
    (hk : κ.fst.map (q.nextConjugation d t) =
      (anchorNormalize (ν.map (Homeomorph.mulLeft (q.nextConjugation d t w)))
        ((q.nextConjugation d t) '' V)).restrict ((q.nextConjugation d t) '' V)) :
    κ = ((anchorNormalize
      ((ν.map (q.nextConjugation d (-t))).map (Homeomorph.mulLeft w)) V).restrict V).prod κ.snd := by
  let η := (ν.map (q.nextConjugation d (-t))).map (Homeomorph.mulLeft w)
  have hzero : ν.map (q.nextConjugation d (t-t)) = ν := by
    rw [sub_self]
    have he : q.nextConjugation d 0 = id := funext (q.nextConjugation_zero d)
    rw [he,Measure.map_id]
  have ht : η.map (q.nextConjugation d t) =
      ν.map (Homeomorph.mulLeft (q.nextConjugation d t w)) :=
    q.translated_reference_conjugation d ν w t t hzero
  have hm := q.map_normalized_restriction_conjugation_covariant d t η V hV
  rw [ht] at hm
  have hfst := (q.nextConjugationHomeomorph d t).measurableEmbedding.map_injective
    (hk.trans hm.symm)
  exact hp.trans (congrArg (fun θ => θ.prod κ.snd) hfst)

end InitialRootStep
end DukePrimeDegree

end

end OAI
