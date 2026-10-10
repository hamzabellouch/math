import OAI.Analysis.LipschitzHilbert.Geometry.SourceSizeSelectionOrder
import OAI.Analysis.LipschitzHilbert.Geometry.SourceSizeSelectionEnergy

namespace OAI

/-! Paired tops and their actual recorded test packets. Chronological
nondeletion is a conclusion of the finite stopping run. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def sizeSelectionRecords (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) :
    Finset P.PacketIndex → List SlopeBox → List (SlopeBox × Finset P.PacketIndex)
  | _, [] => []
  | R, T::tops => (T,P.sizeTestPackets negative w cb cell grid R T) ::
      sizeSelectionRecords negative w cb A cell grid
        (R\P.sizeDeletePackets w A cell grid R T) tops

theorem sizeSelectionRecords_packets (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeSelectionRecords negative w cb A cell grid R tops).map Prod.snd =
      P.recordedSizeTests negative w cb A cell grid R tops := by
  induction tops generalizing R with
  | nil => rfl
  | cons T tops ih => simp only [sizeSelectionRecords,List.map_cons,recordedSizeTests,ih]

theorem sizeSelectionRecords_tops (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeSelectionRecords negative w cb A cell grid R tops).map Prod.fst=tops := by
  induction tops generalizing R with
  | nil => rfl
  | cons T tops ih => simp only [sizeSelectionRecords,List.map_cons,ih]

theorem sizeSelectionRecords_subset (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox)
    (p : SlopeBox × Finset P.PacketIndex)
    (hp : p ∈ P.sizeSelectionRecords negative w cb A cell grid R tops) : p.2⊆R := by
  apply P.recordedSizeTests_subset negative w cb A cell grid R tops p.2
  rw [←P.sizeSelectionRecords_packets negative w cb A cell grid R tops]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem records_geometry
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p ∈ P.sizeSelectionRecords negative w cb A cell grid initial tops,
      p.1.width=P.width ∧ p.1.length≤tau ∧
      ∀ q∈p.2, P.length q.1≤p.1.length ∧
        (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox p.1 (1/2) ∧
        p.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
        cb*w/P.length q.1≤sizeDirection negative (p.1.slope-P.rowSlope q.1 q.2.1) := by
  induction h with
  | stop => simp only [sizeSelectionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨hT.1,hT.2.1,?_⟩
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    · exact ih p hp

/-- A later recorded packet lies outside every earlier enlarged deletion
box whenever its scale and angular cell make it eligible for deletion. -/
theorem records_order
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    (P.sizeSelectionRecords negative w cb A cell grid initial tops).Pairwise
      (fun p p' => sizeDirection negative p.1.slope<sizeDirection negative p'.1.slope+epsilon ∧
        ∀ q∈p'.2, ¬(P.length q.1≤p.1.length ∧
          (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox p.1 A ∧
          p.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))) := by
  induction h with
  | stop => exact List.Pairwise.nil
  | step R T tops remaining _ hfirst htail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro p hp
    have hpTop : p.1∈tops := by
      rw [←P.sizeSelectionRecords_tops negative w cb A cell grid
        (R\P.sizeDeletePackets w A cell grid R T) tops]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    refine ⟨hfirst p.1 (P.sizeTestFails_mono negative w cb tau sigma cell grid c
      Finset.sdiff_subset p.1 (htail.selected_failing p.1 hpTop)),?_⟩
    intro q hq heligible
    have hsub := P.sizeSelectionRecords_subset negative w cb A cell grid
      (R\P.sizeDeletePackets w A cell grid R T) tops p hp hq
    exact (Finset.mem_sdiff.mp hsub).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hsub).1,heligible⟩)

end SizeStoppingRun
end LipschitzHilbert.SourceLabeledLattice

end

end OAI
