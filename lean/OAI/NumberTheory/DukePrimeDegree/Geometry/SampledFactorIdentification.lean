import OAI.NumberTheory.DukePrimeDegree.Geometry.RootFiberReferenceCovariance
import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationReference
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixFactorIdentification

namespace OAI

/-! # Identifying a rectangle factor at a common sampled reference -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

theorem exists_translated_nextProduct_factor (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (b : S → X (d+1)) (hb : Measurable b)
    (ρ : Measure (S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)))
    [IsFiniteMeasure ρ] (hρ : ρ.map (q.rootFiberPoint d b) ≪ μ)
    (hprod : ∀ᵐ s ∂ρ.fst,
      ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd)
    (B : S → Set (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (hB : ∀ s, MeasurableSet (B s))
    (Good : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) → Prop)
    (hGood : ∀ᵐ z ∂ρ, Good z)
    (hcond : ∀ᵐ z ∂ρ,
      (ρ.map (q.prefixRootExchange d)).condKernel (z.1,z.2.2) =
        (anchorNormalize
          ((q.nextIntrinsicProduct d μ (q.rootFiberPoint d b z)).map
            (Homeomorph.mulLeft (q.nextConjugation d z.2.2 z.2.1)))
          ((q.nextConjugation d z.2.2) '' B z.1)).restrict
            ((q.nextConjugation d z.2.2) '' B z.1)) :
    ∀ᵐ s ∂ρ.fst, ∃ w : positiveRootGeneratedGroup (q.remaining.erase q.root), ∃ t₀ : ℝ,
      Good (s,(w,t₀)) ∧
      ρ.condKernel s =
        ((anchorNormalize
          (((q.nextIntrinsicProduct d μ (q.rootFiberPoint d b (s,(w,t₀)))).map
            (q.nextConjugation d (-t₀))).map (Homeomorph.mulLeft w))
          (B s)).restrict (B s)).prod (ρ.condKernel s).snd := by
  have H := q.exists_covariant_nextProduct_reference d μ b hb ρ hρ hprod
    (fun z => Good z ∧
      (ρ.map (q.prefixRootExchange d)).condKernel (z.1,z.2.2) =
        (anchorNormalize
          ((q.nextIntrinsicProduct d μ (q.rootFiberPoint d b z)).map
            (Homeomorph.mulLeft (q.nextConjugation d z.2.2 z.2.1)))
          ((q.nextConjugation d z.2.2) '' B z.1)).restrict
            ((q.nextConjugation d z.2.2) '' B z.1)) (hGood.and hcond)
  filter_upwards [H,hprod,q.ae_prefixRootExchange_conditional d ρ hprod] with s hs hp he
  obtain ⟨w,t₀,hw,ht⟩ := hs
  refine ⟨w,t₀,hw.1,?_⟩
  obtain ⟨t,het,hct⟩ := (he.and ht).exists
  let ν := ((q.nextIntrinsicProduct d μ (q.rootFiberPoint d b (s,(w,t₀)))).map
    (q.nextConjugation d (-t₀))).map (Homeomorph.mulLeft w)
  have hc : (ρ.map (q.prefixRootExchange d)).condKernel (s,t) =
      (anchorNormalize (ν.map (q.nextConjugation d t))
        ((q.nextConjugation d t) '' B s)).restrict ((q.nextConjugation d t) '' B s) := by
    rw [q.translated_reference_conjugation d _ w t₀ t hct.2.2]
    simpa only [hct.2.1] using hct.1.2
  have hm := q.map_normalized_restriction_conjugation_covariant d t ν (B s) (hB s)
  have hf : (ρ.condKernel s).fst.map (q.nextConjugation d t) =
      ((anchorNormalize ν (B s)).restrict (B s)).map (q.nextConjugation d t) :=
    het.symm.trans (hc.trans hm.symm)
  have hfst := (q.nextConjugationHomeomorph d t).measurableEmbedding.map_injective hf
  exact hp.trans (congrArg (fun η => η.prod (ρ.condKernel s).snd) hfst)

end InitialRootStep
end DukePrimeDegree

end

end OAI
