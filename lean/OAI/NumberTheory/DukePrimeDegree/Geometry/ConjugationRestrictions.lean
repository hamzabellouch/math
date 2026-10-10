import OAI.NumberTheory.DukePrimeDegree.Geometry.RootOrderCoordinates

namespace OAI

/-! # Normalized restrictions under extremal conjugation -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

def nextConjugationHomeomorph (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ
      positiveRootGeneratedGroup (q.remaining.erase q.root) where
  toFun := q.nextConjugation d r
  invFun := q.nextConjugation d (-r)
  left_inv w := by simpa only [neg_neg] using q.nextConjugation_neg_cancel d (-r) w
  right_inv := q.nextConjugation_neg_cancel d r
  continuous_toFun := q.continuous_nextConjugation d r
  continuous_invFun := q.continuous_nextConjugation d (-r)

lemma map_normalized_restriction_conjugation (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (hν : ν.map (q.nextConjugation d r) = ν)
    (B : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hB : MeasurableSet B) :
    ((anchorNormalize ν B).restrict B).map (q.nextConjugation d r) =
      (anchorNormalize ν ((q.nextConjugation d r) '' B)).restrict
        ((q.nextConjugation d r) '' B) := by
  let E := (q.nextConjugationHomeomorph d r).toMeasurableEquiv
  have him : MeasurableSet (E '' B) := E.measurableEmbedding.measurableSet_image.mpr hB
  have hn := anchorNormalize_map_equiv ν E B
  change ν.map E = ν at hν
  rw [hν] at hn
  change ((anchorNormalize ν B).restrict B).map E =
    (anchorNormalize ν (E '' B)).restrict (E '' B)
  rw [hn,Measure.restrict_map E.measurable him,E.injective.preimage_image]

end InitialRootStep
end DukePrimeDegree

end

end OAI
