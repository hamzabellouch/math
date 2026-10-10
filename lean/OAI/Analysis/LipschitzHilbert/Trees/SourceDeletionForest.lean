import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectedPackets

namespace OAI

/-! The full trees removed by the size-selection loop, including the
nonseparated packets deleted with each recorded top. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def sizeDeletionRecords (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) :
    Finset P.PacketIndex → List SlopeBox → List (SlopeBox × Finset P.PacketIndex)
  | _, [] => []
  | R, T::tops => (T,P.sizeDeletePackets w A cell grid R T) ::
      sizeDeletionRecords w A cell grid (R\P.sizeDeletePackets w A cell grid R T) tops

theorem sizeDeletionRecords_tops (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeDeletionRecords w A cell grid R tops).map Prod.fst=tops := by
  induction tops generalizing R with
  | nil => rfl
  | cons T tops ih => simp only [sizeDeletionRecords,List.map_cons,ih]

theorem sizeDeletionRecords_subset (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    ∀ p∈P.sizeDeletionRecords w A cell grid R tops, p.2⊆R := by
  induction tops generalizing R with
  | nil => simp only [sizeDeletionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons T tops ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Finset.filter_subset _ _
    · exact (ih _ p hp).trans Finset.sdiff_subset

theorem sizeDeletionRecords_disjoint (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeDeletionRecords w A cell grid R tops).Pairwise (fun p q => Disjoint p.2 q.2) := by
  induction tops generalizing R with
  | nil => exact List.Pairwise.nil
  | cons T tops ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih _⟩
    intro p hp
    have hsub := P.sizeDeletionRecords_subset w A cell grid
      (R\P.sizeDeletePackets w A cell grid R T) tops p hp
    apply Finset.disjoint_left.mpr
    intro q hq hqp
    exact (Finset.mem_sdiff.mp (hsub hqp)).2 hq

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem deletion_forest_covers
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (q : P.PacketIndex) (hq : q∈initial) :
    q∈remaining ∨ ∃ p∈P.sizeDeletionRecords w A cell grid initial tops, q∈p.2 := by
  induction h with
  | stop => exact Or.inl hq
  | step R T tops remaining _ _ _ ih =>
    by_cases hd : q∈P.sizeDeletePackets w A cell grid R T
    · exact Or.inr ⟨(T,P.sizeDeletePackets w A cell grid R T),List.mem_cons_self,hd⟩
    · rcases ih (Finset.mem_sdiff.mpr ⟨hq,hd⟩) with hr | ⟨p,hp,hqp⟩
      · exact Or.inl hr
      · exact Or.inr ⟨p,List.mem_cons_of_mem _ hp,hqp⟩

theorem deletion_forest_nonempty
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) :
    ∀ p∈P.sizeDeletionRecords w A cell grid initial tops, p.2.Nonempty := by
  induction h with
  | stop => simp only [sizeDeletionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨q,hq⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
      exact ⟨q,P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq⟩
    · exact ih p hp

theorem deletion_forest_geometry
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ p∈P.sizeDeletionRecords w A cell grid initial tops,
      p.1.width=P.width ∧ p.1.length≤tau ∧ ∀ q∈p.2,
        P.length q.1≤p.1.length ∧
        (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox p.1 A ∧
        p.1.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) := by
  induction h with
  | stop => simp only [sizeDeletionRecords,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | step R T tops remaining hT _ _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨hT.1,hT.2.1,?_⟩
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    · exact ih p hp

theorem deletion_forest_sum {E : Type*} [AddCommMonoid E]
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (f : P.PacketIndex → E) :
    (∑ q∈initial, f q)=
      ((P.sizeDeletionRecords w A cell grid initial tops).map (fun p => ∑ q∈p.2, f q)).sum+
        ∑ q∈remaining, f q := by
  induction h with
  | stop => simp only [sizeDeletionRecords,List.map_nil,List.sum_nil,zero_add]
  | step R T tops remaining _ _ _ ih =>
    have hd : P.sizeDeletePackets w A cell grid R T⊆R := Finset.filter_subset _ _
    have he := Finset.sum_sdiff (f := f) hd
    change (∑ q∈R, f q)=(∑ q∈P.sizeDeletePackets w A cell grid R T, f q)+
      ((P.sizeDeletionRecords w A cell grid (R\P.sizeDeletePackets w A cell grid R T) tops).map
        (fun p => ∑ q∈p.2, f q)).sum+(∑ q∈remaining, f q)
    rw [←he,ih]
    ac_rfl

theorem deletion_forest_area :
    ((P.sizeDeletionRecords w A cell grid initial tops).map (fun p => p.1.area)).sum=
      (tops.map SlopeBox.area).sum := by
  calc
    _ = (((P.sizeDeletionRecords w A cell grid initial tops).map Prod.fst).map SlopeBox.area).sum := by
      rw [List.map_map]
      rfl
    _ = _ := by rw [P.sizeDeletionRecords_tops]

end SizeStoppingRun
theorem two_size_deletion_forest_sum {E : Type*} [AddCommMonoid E]
    (w cb tau sigma epsilon A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial middle remaining : Finset P.PacketIndex) (positive negative : List SlopeBox)
    (hp : P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial positive middle)
    (hn : P.SizeStoppingRun true w cb tau sigma epsilon A cell grid c middle negative remaining)
    (f : P.PacketIndex → E) :
    (∑ q∈initial, f q)=
      ((P.sizeDeletionRecords w A cell grid initial positive).map (fun p => ∑ q∈p.2, f q)).sum+
      ((P.sizeDeletionRecords w A cell grid middle negative).map (fun p => ∑ q∈p.2, f q)).sum+
      ∑ q∈remaining, f q := by
  rw [hp.deletion_forest_sum f,hn.deletion_forest_sum f]
  exact (add_assoc _ _ _).symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
