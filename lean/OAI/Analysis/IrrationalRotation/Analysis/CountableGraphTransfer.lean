import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

open MeasureTheory

namespace Invariant233.Fields

variable {X Y Ω ι : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [Countable ι] {μ : Measure X} {ν : Measure Ω}

theorem ae_relation_of_countable_graphs
    (P : X → Y → Prop) (t : ι → X → Y) (x : Ω → X) (y : Ω → Y)
    (hx : AEMeasurable x ν) (hμ : ν.map x ≪ μ)
    (hgraph : ∀ i, ∀ᵐ z ∂μ, P z (t i z))
    (hsupport : ∀ᵐ ω ∂ν, ∃ i, y ω = t i (x ω)) :
    ∀ᵐ ω ∂ν, P (x ω) (y ω) := by
  have hcommon : ∀ᵐ z ∂μ, ∀ i, P z (t i z) := ae_all_iff.mpr hgraph
  have hpull : ∀ᵐ ω ∂ν, ∀ i, P (x ω) (t i (x ω)) :=
    ae_of_ae_map hx (hμ.ae_le hcommon)
  filter_upwards [hpull, hsupport] with ω hω hωsupport
  obtain ⟨i, hi⟩ := hωsupport
  rw [hi]
  exact hω i

theorem ae_pair_relation_of_countable_graphs [MeasurableSpace Y]
    {β : Measure (X × Y)} (P : X → Y → Prop) (t : ι → X → Y)
    (hμ : β.map Prod.fst ≪ μ)
    (hgraph : ∀ i, ∀ᵐ z ∂μ, P z (t i z))
    (hsupport : ∀ᵐ z ∂β, ∃ i, z.2 = t i z.1) :
    ∀ᵐ z ∂β, P z.1 z.2 :=
  ae_relation_of_countable_graphs P t Prod.fst Prod.snd
    measurable_fst.aemeasurable hμ hgraph hsupport

end Invariant233.Fields

end OAI
