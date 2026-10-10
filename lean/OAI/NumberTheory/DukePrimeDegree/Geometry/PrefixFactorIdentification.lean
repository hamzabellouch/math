import OAI.NumberTheory.DukePrimeDegree.Entropy.PrefixRootConditionals
import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationTransport

namespace OAI

/-! # Recovering the remaining factor from extended-prefix conditionals -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

theorem identify_factor_from_extended_prefix (d : ℕ) (q : InitialRootStep (d+1))
    (ρ : Measure (S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)))
    [IsFiniteMeasure ρ]
    (hprod : ∀ᵐ s ∂ρ.fst,
      ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd)
    (ν : S → Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (B : S → Set (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (hB : ∀ s, MeasurableSet (B s))
    (hcond : ∀ᵐ s ∂ρ.fst, ∀ᵐ t ∂(ρ.condKernel s).snd,
      (ρ.map (q.prefixRootExchange d)).condKernel (s,t) =
        (anchorNormalize ((ν s).map (q.nextConjugation d t)) ((q.nextConjugation d t) '' B s)).restrict
          ((q.nextConjugation d t) '' B s)) :
    ∀ᵐ s ∂ρ.fst, ρ.condKernel s =
      ((anchorNormalize (ν s) (B s)).restrict (B s)).prod (ρ.condKernel s).snd := by
  filter_upwards [hprod,hcond,q.ae_prefixRootExchange_conditional d ρ hprod]
    with s hp hc he
  obtain ⟨t,ht,hc⟩ := (he.and hc).exists
  have hm := q.map_normalized_restriction_conjugation_covariant d t (ν s) (B s) (hB s)
  have hf : (ρ.condKernel s).fst.map (q.nextConjugation d t) =
      ((anchorNormalize (ν s) (B s)).restrict (B s)).map (q.nextConjugation d t) :=
    ht.symm.trans (hc.trans hm.symm)
  have hfst := (q.nextConjugationHomeomorph d t).measurableEmbedding.map_injective hf
  exact hp.trans (congrArg (fun η => η.prod (ρ.condKernel s).snd) hfst)

end InitialRootStep
end DukePrimeDegree

end

end OAI
