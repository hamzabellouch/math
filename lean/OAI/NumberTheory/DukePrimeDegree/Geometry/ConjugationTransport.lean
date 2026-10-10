import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationRestrictions

namespace OAI

/-! # Conjugation transports translated and normalized leaf products -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma nextConjugation_mul (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (u v : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    q.nextConjugation d r (u*v) = q.nextConjugation d r u * q.nextConjugation d r v := by
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.transvection q.distinct (-r) * (u.val*v.val) *
      Matrix.SpecialLinearGroup.transvection q.distinct r =
    (Matrix.SpecialLinearGroup.transvection q.distinct (-r) * u.val *
      Matrix.SpecialLinearGroup.transvection q.distinct r) *
    (Matrix.SpecialLinearGroup.transvection q.distinct (-r) * v.val *
      Matrix.SpecialLinearGroup.transvection q.distinct r)
  rw [←Matrix.SpecialLinearGroup.transvection_inv]
  group

lemma map_leftTranslate_conjugation (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    (ν.map (Homeomorph.mulLeft w)).map (q.nextConjugation d r) =
      (ν.map (q.nextConjugation d r)).map (Homeomorph.mulLeft (q.nextConjugation d r w)) := by
  rw [Measure.map_map (q.continuous_nextConjugation d r).measurable
      (Homeomorph.mulLeft w).measurable,
    Measure.map_map (Homeomorph.mulLeft (q.nextConjugation d r w)).measurable
      (q.continuous_nextConjugation d r).measurable]
  congr 1
  funext u
  exact q.nextConjugation_mul d r w u

lemma map_normalized_restriction_conjugation_covariant (d : ℕ)
    (q : InitialRootStep (d+1)) (r : ℝ)
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (B : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hB : MeasurableSet B) :
    ((anchorNormalize ν B).restrict B).map (q.nextConjugation d r) =
      (anchorNormalize (ν.map (q.nextConjugation d r)) ((q.nextConjugation d r) '' B)).restrict
        ((q.nextConjugation d r) '' B) := by
  let E := (q.nextConjugationHomeomorph d r).toMeasurableEquiv
  have him : MeasurableSet (E '' B) := E.measurableEmbedding.measurableSet_image.mpr hB
  have hn := anchorNormalize_map_equiv ν E B
  change ((anchorNormalize ν B).restrict B).map E =
    (anchorNormalize (ν.map E) (E '' B)).restrict (E '' B)
  rw [hn,Measure.restrict_map E.measurable him,E.injective.preimage_image]

end InitialRootStep
end DukePrimeDegree

end

end OAI
