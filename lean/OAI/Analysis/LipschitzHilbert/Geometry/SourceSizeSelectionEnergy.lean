import OAI.Analysis.LipschitzHilbert.Trees.SourceOrdinarySizeStopping

namespace OAI

/-! Disjoint recorded tests and the exact energy bookkeeping for the
finite signed size-selection run. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def recordedSizeTests (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) :
    Finset P.PacketIndex → List SlopeBox → List (Finset P.PacketIndex)
  | _, [] => []
  | R, T::tops => P.sizeTestPackets negative w cb cell grid R T ::
      recordedSizeTests negative w cb A cell grid (R\P.sizeDeletePackets w A cell grid R T) tops

theorem recordedSizeTests_subset (negative : Bool) (w cb A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    ∀ Q∈P.recordedSizeTests negative w cb A cell grid R tops, Q⊆R := by
  induction tops generalizing R with
  | nil => simp only [recordedSizeTests,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons T tops ih =>
    intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact Finset.filter_subset _ _
    · exact (ih _ Q hQ).trans Finset.sdiff_subset

theorem recordedSizeTests_disjoint (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.recordedSizeTests negative w cb A cell grid R tops).Pairwise Disjoint := by
  induction tops generalizing R with
  | nil => exact List.Pairwise.nil
  | cons T tops ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih _⟩
    intro Q hQ
    have hQsub := P.recordedSizeTests_subset negative w cb A cell grid
      (R\P.sizeDeletePackets w A cell grid R T) tops Q hQ
    apply Finset.disjoint_left.mpr
    intro q hq hqQ
    exact (Finset.mem_sdiff.mp (hQsub hqQ)).2
      (P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq)

def packetEnergySum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (R : Finset P.PacketIndex) : ℝ :=
  ∑ q∈R, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width

theorem recordedSizeTests_energy_le (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    ((P.recordedSizeTests negative w cb A cell grid R tops).map (P.packetEnergySum c)).sum≤
      P.packetEnergySum c R := by
  have hnonneg (q : P.PacketIndex) : 0≤‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  induction tops generalizing R with
  | nil => exact Finset.sum_nonneg (fun q _ => hnonneg q)
  | cons T tops ih =>
    let Q := P.sizeTestPackets negative w cb cell grid R T
    let S := R\P.sizeDeletePackets w A cell grid R T
    have hd : Disjoint Q S := by
      apply Finset.disjoint_left.mpr
      intro q hq hqs
      exact (Finset.mem_sdiff.mp hqs).2
        (P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq)
    have hsub : Q∪S⊆R := Finset.union_subset (Finset.filter_subset _ _) Finset.sdiff_subset
    change P.packetEnergySum c Q+
      ((P.recordedSizeTests negative w cb A cell grid S tops).map (P.packetEnergySum c)).sum≤_
    apply (add_le_add le_rfl (ih S)).trans
    change (∑ q∈Q, _)+(∑ q∈S, _)≤∑ q∈R, _
    rw [←Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hnonneg q)

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem top_area_energy
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    sigma^2/2*(tops.map SlopeBox.area).sum≤
      ((P.recordedSizeTests negative w cb A cell grid initial tops).map (P.packetEnergySum c)).sum := by
  induction h with
  | stop => simp only [List.map_nil,List.sum_nil,mul_zero,le_refl,recordedSizeTests]
  | step R T tops remaining hT _ _ ih =>
    change sigma^2/2*(T.area+(tops.map SlopeBox.area).sum)≤
      P.sizeTestEnergy negative w cb cell grid c R T+
        ((P.recordedSizeTests negative w cb A cell grid
          (R\P.sizeDeletePackets w A cell grid R T) tops).map (P.packetEnergySum c)).sum
    have ht : sigma^2/2*T.area≤P.sizeTestEnergy negative w cb cell grid c R T := by
      have hh := hT.2.2.le
      convert hh using 1
      ring
    rw [mul_add]
    exact add_le_add ht ih

/-- Selection charges top area to the actual disjoint coefficient
energy. -/
theorem top_area_le (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c
    initial tops remaining) (hsigma : 0<sigma) (hA : 1/2≤A) :
    (tops.map SlopeBox.area).sum≤2/sigma^2*P.packetEnergySum c initial := by
  have henergy := (h.top_area_energy).trans
    (P.recordedSizeTests_energy_le negative w cb A hA cell grid c initial tops)
  have hs : 0<sigma^2/2 := div_pos (sq_pos_of_pos hsigma) (by norm_num)
  calc
    _ ≤ P.packetEnergySum c initial/(sigma^2/2) :=
      (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using henergy)
    _ = _ := by field_simp

end SizeStoppingRun
end LipschitzHilbert.SourceLabeledLattice

end

end OAI
