import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketShear
import OAI.Analysis.LipschitzHilbert.Trees.SourceShortTreeGlobal
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCells
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeSelectorError

namespace OAI

/-! Change of coordinates for actual tree sums and their integrals. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem integrableOn_slopeShear_iff {V : Type*} [NormedAddCommGroup V]
    (t : ℝ) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (f : ℝ×ℝ → V) :
    IntegrableOn (fun z => f (slopeShear t z)) ((slopeShear t) ⁻¹' E) (volume.prod volume) ↔
      IntegrableOn f E (volume.prod volume) := by
  classical
  rw [←integrable_indicator_iff (hE.preimage (slopeShear t).measurable),
    ←integrable_indicator_iff hE]
  have he : ((slopeShear t) ⁻¹' E).indicator (fun z => f (slopeShear t z))=
      (E.indicator f) ∘ (slopeShear t) := by
    funext z
    simp only [Set.indicator_apply,mem_preimage,Function.comp_apply]
  rw [he]
  exact (slopeShear_measurePreserving t).integrable_comp_emb (slopeShear t).measurableEmbedding

theorem integralOn_slopeShear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : ℝ) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (f : ℝ×ℝ → V) :
    (∫ z in (slopeShear t) ⁻¹' E, f (slopeShear t z) ∂volume.prod volume)=
      ∫ z in E, f z ∂volume.prod volume := by
  classical
  rw [←integral_indicator (hE.preimage (slopeShear t).measurable),←integral_indicator hE]
  have he : ((slopeShear t) ⁻¹' E).indicator (fun z => f (slopeShear t z))=
      (E.indicator f) ∘ (slopeShear t) := by
    funext z
    simp only [Set.indicator_apply,mem_preimage,Function.comp_apply]
  rw [he]
  exact (slopeShear_measurePreserving t).integral_comp (slopeShear t).measurableEmbedding _

theorem treeCell_slopeShear (t b W : ℝ) (k j n : ℤ) :
    (slopeShear t) ⁻¹' SourceWhitney.treeCell t b W k j n=
      SourceWhitney.treeCell 0 b W k j n := by
  ext z
  simp only [mem_preimage,SourceWhitney.treeCell,mem_ofPred_eq]
  change (z.1∈DyadicLineGrid.cell 0 k j ∧
    |(z.2+t*z.1-t*z.1)-b-(n:ℝ)*W|≤W/2) ↔ _
  simp only [add_sub_cancel_right,zero_mul,sub_zero]

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem ordinaryPacketValue_slopeShear (t : ℝ)
    (c : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (q : P.PacketIndex) (z : ℝ×ℝ) :
    P.ordinaryPacketValue 0 c (fun j l k s => selector j l k (s+t))
      (fun z => u (slopeShear t z)-t) q z=
      P.ordinaryPacketValue t c selector u q (slopeShear t z) := by
  simp only [ordinaryPacketValue,sub_add_cancel,P.physicalPacket_slopeShear]

theorem shortTreeValue_slopeShear (hne : Nonempty P.PacketIndex) (t CW : ℝ)
    (c : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    P.shortTreeValue hne 0 CW c (fun j l k s => selector j l k (s+t))
      (fun z => u (slopeShear t z)-t) z=
      P.shortTreeValue hne t CW c selector u (slopeShear t z) := by
  classical
  have hf : (slopeShear t z).1=z.1 := rfl
  simp only [shortTreeValue,SourceWhitney.paste,shortLocalValue,hf]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs
  · exact P.ordinaryPacketValue_slopeShear t c selector u q z
  · rfl


theorem physicalTreeSelectorValue_slopeShear (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue 0 c
      (fun j l k => selector j l k ((u (slopeShear t z)-t)+t)) z=
      P.physicalTreeSelectorValue t c (fun j l k => selector j l k (u (slopeShear t z)))
        (slopeShear t z) := by
  ext k
  simp only [physicalTreeSelectorValue,Finset.sum_apply,
    WithLp.ofLp_sum,sub_add_cancel,P.physicalPacket_slopeShear]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
