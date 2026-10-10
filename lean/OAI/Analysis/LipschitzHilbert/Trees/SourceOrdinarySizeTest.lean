import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityKeepers
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityScaledForest

namespace OAI

/-! The signed size tests used in ordinary tree selection. Failing tests
have a packet witness and admit the manuscript's near-extremal direction. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def sizeDirection (negative : Bool) (s : ℝ) : ℝ := if negative then -s else s

def sizeTestPackets (negative : Bool) (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (remaining : Finset P.PacketIndex) (T : SlopeBox) : Finset P.PacketIndex :=
  remaining.filter fun q => P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
    T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
    cb*w/P.length q.1≤sizeDirection negative (T.slope-P.rowSlope q.1 q.2.1)

def sizeTestEnergy (negative : Bool) (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (remaining : Finset P.PacketIndex) (T : SlopeBox) : ℝ :=
  ∑ q∈P.sizeTestPackets negative w cb cell grid remaining T,
    ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width

def sizeTestFails (negative : Bool) (w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (remaining : Finset P.PacketIndex) (T : SlopeBox) : Prop :=
  T.width=P.width ∧ T.length≤tau ∧
    sigma^2*T.area/2<P.sizeTestEnergy negative w cb cell grid c remaining T

theorem sizeTestEnergy_mono (negative : Bool) (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox) :
    P.sizeTestEnergy negative w cb cell grid c R T≤P.sizeTestEnergy negative w cb cell grid c S T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hRS)
  intro q _ _
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le

theorem sizeTestFails_mono (negative : Bool) (w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox)
    (hfail : P.sizeTestFails negative w cb tau sigma cell grid c R T) :
    P.sizeTestFails negative w cb tau sigma cell grid c S T :=
  ⟨hfail.1,hfail.2.1,hfail.2.2.trans_le (P.sizeTestEnergy_mono negative w cb cell grid c hRS T)⟩

theorem failing_size_test_nonempty (negative : Bool) (w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (T : SlopeBox)
    (hfail : P.sizeTestFails negative w cb tau sigma cell grid c R T) :
    (P.sizeTestPackets negative w cb cell grid R T).Nonempty := by
  by_contra hn
  have he : P.sizeTestPackets negative w cb cell grid R T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have h := hfail.2.2
  simp only [sizeTestEnergy,he,Finset.sum_empty] at h
  have ha : 0≤sigma^2*T.area/2 := div_nonneg (mul_nonneg (sq_nonneg _) T.area_pos.le) (by norm_num)
  linarith

theorem size_test_direction_lower (negative : Bool) (w cb : ℝ) (hw : 0≤w) (hcb : 0≤cb)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (R : Finset P.PacketIndex)
    (T : SlopeBox) (q : P.PacketIndex) (hq : q∈P.sizeTestPackets negative w cb cell grid R T)
    (L : ℝ) (hL : L≤sizeDirection negative (P.rowSlope q.1 q.2.1)) :
    L≤sizeDirection negative T.slope := by
  have hd := (Finset.mem_filter.mp hq).2.2.2.2
  have hn : 0≤cb*w/P.length q.1 :=
    div_nonneg (mul_nonneg hcb hw) (P.length_pos q.1).le
  cases negative <;> simp only [sizeDirection,Bool.false_eq_true,ite_false,ite_true] at * <;> linarith

/-- Near-infimum selection is valid even though test directions vary
continuously. The finite packet family supplies the lower bound. -/
theorem exists_near_first_size_test (negative : Bool) (w cb tau sigma epsilon : ℝ)
    (hw : 0≤w) (hcb : 0≤cb) (hepsilon : 0<epsilon)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex)
    (hex : ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T) :
    ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T ∧
      ∀ U, P.sizeTestFails negative w cb tau sigma cell grid c R U →
        sizeDirection negative T.slope<sizeDirection negative U.slope+epsilon := by
  obtain ⟨T0,hT0⟩ := hex
  obtain ⟨q0,_hq0⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T0 hT0
  have hne : (Finset.univ : Finset P.PacketIndex).Nonempty := ⟨q0,Finset.mem_univ _⟩
  obtain ⟨q,_hq,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset P.PacketIndex)
    (fun q => sizeDirection negative (P.rowSlope q.1 q.2.1)) hne
  let S : Set ℝ := {x | ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T ∧
    sizeDirection negative T.slope=x}
  have hSne : S.Nonempty := ⟨sizeDirection negative T0.slope,T0,hT0,rfl⟩
  have hbelow : BddBelow S := by
    refine ⟨sizeDirection negative (P.rowSlope q.1 q.2.1),?_⟩
    rintro x ⟨T,hT,rfl⟩
    obtain ⟨p,hp⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
    exact P.size_test_direction_lower negative w cb hw hcb cell grid R T p hp _
      (hmin p (Finset.mem_univ _))
  obtain ⟨x,hx,hclose⟩ := exists_lt_of_csInf_lt hSne
    (lt_add_of_pos_right (sInf S) hepsilon)
  obtain ⟨T,hT,rfl⟩ := hx
  refine ⟨T,hT,?_⟩
  intro U hU
  exact hclose.trans_le (add_le_add (csInf_le hbelow ⟨U,hU,rfl⟩) le_rfl)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
