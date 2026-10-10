import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationTransport

namespace OAI

/-! # Moving a sampled reference through the selected root direction -/

noncomputable section
open Matrix MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma nextConjugation_add (d : ℕ) (q : InitialRootStep (d+1)) (r t : ℝ)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    q.nextConjugation d r (q.nextConjugation d t w) = q.nextConjugation d (t+r) w := by
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.transvection q.distinct (-r) *
      (Matrix.SpecialLinearGroup.transvection q.distinct (-t) * w.val *
        Matrix.SpecialLinearGroup.transvection q.distinct t) *
      Matrix.SpecialLinearGroup.transvection q.distinct r = _
  calc
    _ = (Matrix.SpecialLinearGroup.transvection q.distinct (-r) *
          Matrix.SpecialLinearGroup.transvection q.distinct (-t)) * w.val *
        (Matrix.SpecialLinearGroup.transvection q.distinct t *
          Matrix.SpecialLinearGroup.transvection q.distinct r) := by group
    _ = _ := by
      rw [←Matrix.SpecialLinearGroup.transvection_add,←Matrix.SpecialLinearGroup.transvection_add,
        show -r + -t = -(t+r) by ring]
      rfl

lemma map_reference_conjugation (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root))) (t₀ t : ℝ) :
    (ν.map (q.nextConjugation d (-t₀))).map (q.nextConjugation d t) =
      ν.map (q.nextConjugation d (t-t₀)) := by
  rw [Measure.map_map (q.continuous_nextConjugation d t).measurable
    (q.continuous_nextConjugation d (-t₀)).measurable]
  apply congrArg (fun f => ν.map f)
  funext w
  simpa only [Function.comp_apply,show -t₀+t=t-t₀ by ring] using q.nextConjugation_add d t (-t₀) w

theorem translated_reference_conjugation (d : ℕ) (q : InitialRootStep (d+1))
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (t₀ t : ℝ)
    (hν : ν.map (q.nextConjugation d (t-t₀)) = ν) :
    ((ν.map (q.nextConjugation d (-t₀))).map (Homeomorph.mulLeft w)).map
        (q.nextConjugation d t) =
      ν.map (Homeomorph.mulLeft (q.nextConjugation d t w)) := by
  rw [q.map_leftTranslate_conjugation,q.map_reference_conjugation,hν]

end InitialRootStep
end DukePrimeDegree

end

end OAI
