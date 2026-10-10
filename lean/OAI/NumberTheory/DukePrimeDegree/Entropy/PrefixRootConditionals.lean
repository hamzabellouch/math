import OAI.NumberTheory.DukePrimeDegree.Entropy.RootOrderConditionals

namespace OAI

/-! # Nested conditionals in exchanged prefix-root coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

lemma ae_nested_remaining_conditionals (d : ℕ) (q : InitialRootStep (d+1))
    (σ : Measure (S × (ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root))))
    [IsFiniteMeasure σ] :
    ∀ᵐ s ∂σ.fst, ∀ᵐ t ∂(σ.condKernel s).fst,
      (σ.map MeasurableEquiv.prodAssoc.symm).condKernel (s,t) =
        (σ.condKernel s).condKernel t := by
  let κ := σ.condKernel
  let ρ := σ.map MeasurableEquiv.prodAssoc.symm
  have hρ : ρ = (σ.fst ⊗ₘ κ.fst) ⊗ₘ κ.condKernel := by
    calc
      ρ = (σ.fst ⊗ₘ (κ.fst ⊗ₖ κ.condKernel)).map MeasurableEquiv.prodAssoc.symm := by
        rw [Kernel.disintegrate,Measure.disintegrate]
      _ = _ := Measure.compProd_assoc
  have hfst : ρ.fst = σ.fst ⊗ₘ κ.fst := by
    rw [hρ,Measure.fst_compProd]
  have heq : κ.condKernel =ᵐ[ρ.fst] ρ.condKernel :=
    eq_condKernel_of_measure_eq_compProd κ.condKernel (by rw [hfst]; exact hρ)
  rw [hfst] at heq
  have h := Measure.ae_ae_of_ae_compProd heq
  filter_upwards [h] with s hs
  have hinner := Kernel.condKernel_apply_eq_condKernel κ s
  filter_upwards [hs,hinner] with t ht htc
  exact ht.symm.trans htc

def prefixRootExchange (d : ℕ) (q : InitialRootStep (d+1))
    (z : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    (S × ℝ) × positiveRootGeneratedGroup (q.remaining.erase q.root) :=
  ((z.1,z.2.2),q.nextConjugation d z.2.2 z.2.1)

lemma measurable_prefixRootExchange (d : ℕ) (q : InitialRootStep (d+1)) :
    Measurable (q.prefixRootExchange d (S := S)) := by
  have hF : Measurable (fun z : S ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) =>
      (z.1,q.rootOrderCoordinates d z.2)) :=
    measurable_fst.prodMk ((q.rootOrderCoordinates d).measurable.comp measurable_snd)
  exact MeasurableEquiv.prodAssoc.symm.measurable.comp hF

theorem ae_prefixRootExchange_conditional (d : ℕ) (q : InitialRootStep (d+1))
    (ρ : Measure (S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)))
    [IsFiniteMeasure ρ]
    (hprod : ∀ᵐ s ∂ρ.fst,
      ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) :
    ∀ᵐ s ∂ρ.fst, ∀ᵐ t ∂(ρ.condKernel s).snd,
      (ρ.map (q.prefixRootExchange d)).condKernel (s,t) =
        ((ρ.condKernel s).fst).map (q.nextConjugation d t) := by
  let F := fun z : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) =>
    q.rootOrderCoordinates d z.2
  have hF : Measurable F := (q.rootOrderCoordinates d).measurable.comp measurable_snd
  let σ := ρ.map (fun z => (z.1,F z))
  have hs : σ.fst = ρ.fst := by
    have H := fst_map_fibers ρ (MeasurableEquiv.refl S) F hF
    change σ.fst = ρ.fst.map id at H
    simpa only [Measure.map_id] using H
  have hc : ∀ᵐ s ∂ρ.fst,
      σ.condKernel s = (ρ.condKernel s).map (q.rootOrderCoordinates d) := by
    exact conditional_map_fibers ρ (MeasurableEquiv.refl S) F hF
  have hn := q.ae_nested_remaining_conditionals d σ
  rw [hs] at hn
  have hm : σ.map MeasurableEquiv.prodAssoc.symm = ρ.map (q.prefixRootExchange d) := by
    dsimp only [σ]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      (measurable_fst.prodMk hF)]
    rfl
  filter_upwards [hprod,hc,hn] with s hp hc hn
  have hb : (σ.condKernel s).fst = (ρ.condKernel s).snd := by
    rw [hc,Measure.fst,Measure.map_map measurable_fst (q.rootOrderCoordinates d).measurable]
    rfl
  rw [hb] at hn
  have ht := q.rootOrderCoordinates_conditional_of_product d (ρ.condKernel s) hp
  filter_upwards [hn,ht] with t hn ht
  have hn' : (ρ.map (q.prefixRootExchange d)).condKernel (s,t) =
      (σ.condKernel s).condKernel t := by simpa only [hm] using hn
  exact hn'.trans (by simpa only [hc] using ht)

end InitialRootStep
end DukePrimeDegree

end

end OAI
