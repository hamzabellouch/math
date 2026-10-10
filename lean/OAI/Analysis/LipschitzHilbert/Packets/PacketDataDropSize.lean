import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDropPackets
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSizeTest

namespace OAI

/-! Dropping scales preserves every remaining unsigned size test. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem dropPackets_tail (first : Fin N) (Q : Finset P.PacketIndex) :
    P.dropPackets first (Q.filter (fun q => first.val≤q.1.val))=P.dropPackets first Q := by
  ext q
  simp only [mem_dropPackets,Finset.mem_filter]
  have h : first.val≤(P.dropPacket first q).1.val := by
    change first.val≤first.val+q.1.val
    omega
  exact and_iff_left h

theorem dropScales_unsignedSizeTestEnergy (first : Fin N) (Q : Finset P.PacketIndex)
    (w cb : ℝ) (hw : 0<w) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox) :
    (P.dropScales first).unsignedSizeTestEnergy w cb (fun j l => cell (dropIndex first j) l)
      (((first.val:ℤ).negOnePow : ℤ)*grid) (fun j l v => c (dropIndex first j) l v)
      (P.dropPackets first Q) T=
    P.unsignedSizeTestEnergy w cb cell grid c (Q.filter (fun q => first.val≤q.1.val)) T := by
  let f := fun q : P.PacketIndex =>
    if P.length q.1≤T.length ∧
      (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
      T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
      cb*w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0
  have hsum := P.sum_dropPackets first (Q.filter (fun q => first.val≤q.1.val))
    (fun q hq => (Finset.mem_filter.mp hq).2) f
  rw [P.dropPackets_tail] at hsum
  unfold unsignedSizeTestEnergy
  refine Eq.trans ?_ hsum
  apply Finset.sum_congr rfl
  rintro ⟨j,l,v⟩ _
  simp only [dropScales_length,dropScales_actualX,dropScales_actualZ,P.dropScales_angularCell first w hw]
  rfl

theorem dropScales_unsignedSizeTestEnergy_le (first : Fin N) (Q : Finset P.PacketIndex)
    (w cb : ℝ) (hw : 0<w) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox) :
    (P.dropScales first).unsignedSizeTestEnergy w cb (fun j l => cell (dropIndex first j) l)
      (((first.val:ℤ).negOnePow : ℤ)*grid) (fun j l v => c (dropIndex first j) l v)
      (P.dropPackets first Q) T≤P.unsignedSizeTestEnergy w cb cell grid c Q T := by
  rw [P.dropScales_unsignedSizeTestEnergy first Q w cb hw cell grid c T]
  exact P.unsignedSizeTestEnergy_mono w cb cell grid c (Finset.filter_subset _ _) T

theorem dropPackets_nonempty (first : Fin N) (Q : Finset P.PacketIndex)
    (hne : Q.Nonempty) (hQ : ∀ q∈Q, first.val≤q.1.val) :
    (P.dropPackets first Q).Nonempty := by
  obtain ⟨⟨j,l,v⟩,hq⟩ := hne
  obtain ⟨i,hi⟩ := dropIndex_surjective_tail first j (hQ ⟨j,⟨l,v⟩⟩ hq)
  subst j
  exact ⟨⟨i,⟨l,v⟩⟩,P.mem_dropPackets first Q _ |>.mpr hq⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
