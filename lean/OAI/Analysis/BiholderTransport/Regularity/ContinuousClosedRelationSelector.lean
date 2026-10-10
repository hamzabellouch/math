import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace WeakMTWTransport

lemma continuousAt_closed_relation_selector
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    {R : Set (X × Y)} (hR : IsClosed R) {T : X → Y}
    (hT : ∀ x, (x,T x) ∈ R) {x : X}
    (hx : ∀ y, (x,y) ∈ R → y = T x) : ContinuousAt T x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let B : Set (X × Y) := R ∩ {z | ε ≤ dist z.2 (T x)}
  have hB : IsClosed B :=
    hR.inter (isClosed_le continuous_const (continuous_snd.dist continuous_const))
  have hclosed : IsClosed (Prod.fst '' B) := isClosedMap_fst_of_compactSpace B hB
  have hxB : x ∈ (Prod.fst '' B)ᶜ := by
    rintro ⟨⟨a,b⟩, hab, hax⟩
    change a = x at hax
    subst a
    have hb := hx b hab.1
    have hdist := hab.2
    change ε ≤ dist b (T x) at hdist
    rw [hb,dist_self] at hdist
    exact (not_le.mpr hε) hdist
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hxB)
  refine ⟨δ,hδ,?_⟩
  intro a ha
  apply lt_of_not_ge
  intro han
  exact hd ha ⟨(a,T a),⟨hT a,han⟩,rfl⟩

lemma aemeasurable_closed_relation_selector
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {R : Set (X × Y)} (hR : IsClosed R) {T : X → Y}
    (hT : ∀ x, (x,T x) ∈ R)
    (hsingle : ∀ᵐ x ∂μ, ∀ y, (x,y) ∈ R → y = T x) : AEMeasurable T μ := by
  let S : Set X := {x | ∀ y, (x,y) ∈ R → y = T x}
  have hS : ∀ᵐ x ∂μ, x ∈ S := hsingle
  have hSnull : NullMeasurableSet S μ := by
    have he : (univ : Set X) =ᵐ[μ] S := by
      filter_upwards [hS] with x hx
      exact propext ⟨fun _ => hx, fun _ => mem_univ x⟩
    exact nullMeasurableSet_univ.congr he
  have hc : ContinuousOn T S := by
    intro x hx
    exact (continuousAt_closed_relation_selector hR hT hx).continuousWithinAt
  have hm := hc.aemeasurable₀ hSnull
  rwa [Measure.restrict_eq_self_of_ae_mem hS] at hm

end WeakMTWTransport

end

end

end

end OAI
