import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationRestrictions
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootOrderConditionals

namespace OAI

/-! # Identifying a product factor from conditionals in the opposite root order -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

theorem identify_remaining_conditional_factor (d : ℕ) (q : InitialRootStep (d+1))
    (ρ : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ))
    [IsProbabilityMeasure ρ] (hprod : ρ = ρ.fst.prod ρ.snd)
    (ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (hinv : ∀ r : ℝ, ν.map (q.nextConjugation d r) = ν)
    (B : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hB : MeasurableSet B)
    (hcond : ∀ᵐ r ∂ρ.snd,
      (ρ.map (q.rootOrderCoordinates d)).condKernel r =
        (anchorNormalize ν ((q.nextConjugation d r) '' B)).restrict
          ((q.nextConjugation d r) '' B)) :
    ρ = ((anchorNormalize ν B).restrict B).prod ρ.snd := by
  obtain ⟨r,hr,hc⟩ := ((q.rootOrderCoordinates_conditional_of_product d ρ hprod).and hcond).exists
  have hm := q.map_normalized_restriction_conjugation d r ν (hinv r) B hB
  have he : ρ.fst.map (q.nextConjugation d r) =
      ((anchorNormalize ν B).restrict B).map (q.nextConjugation d r) :=
    hr.symm.trans (hc.trans hm.symm)
  have hf := (q.nextConjugationHomeomorph d r).measurableEmbedding.map_injective he
  exact hprod.trans (congrArg (fun ξ => ξ.prod ρ.snd) hf)

end InitialRootStep
end DukePrimeDegree

end

end OAI
