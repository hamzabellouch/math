import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalRectangleProducts

namespace OAI

/-! # Including the base of an independent conditional rectangle -/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditional_product_map_base_embedding
    {S T B : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (ρ : Measure (S × (B × ℝ))) [IsFiniteMeasure ρ]
    (e : S → T) (he : MeasurableEmbedding e)
    (hprod : ∀ᵐ s ∂ρ.fst,
      ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) :
    let σ := ρ.map (Prod.map e id)
    ∀ᵐ t ∂σ.fst, σ.condKernel t = (σ.condKernel t).fst.prod (σ.condKernel t).snd := by
  intro σ
  have hfst : σ.fst = ρ.fst.map e :=
    fst_map_fibers_of_measurable ρ e he.measurable Prod.snd measurable_snd
  have hc : ∀ᵐ s ∂ρ.fst, σ.condKernel (e s) = ρ.condKernel s := by
    have H := conditional_map_fibers_embedding ρ e he Prod.snd measurable_snd
    filter_upwards [H] with s hs
    change σ.condKernel (e s) = (ρ.condKernel s).map id at hs
    simpa only [Measure.map_id] using hs
  rw [hfst]
  apply he.ae_map_iff.mpr
  filter_upwards [hc,hprod] with s hs hp
  simpa only [hs] using hp

end DukePrimeDegree

end

end OAI
