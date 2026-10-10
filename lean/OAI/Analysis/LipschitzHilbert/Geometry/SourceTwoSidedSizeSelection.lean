import OAI.Analysis.LipschitzHilbert.Geometry.SourceSizeSelectionEnergy
import OAI.Analysis.LipschitzHilbert.Geometry.SourceSizeSelectionOrder

namespace OAI

/-! Positive followed by negative selection leaves every separated
size test below its threshold. Both runs retain their original geometry. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def unsignedSizeTestEnergy (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (T : SlopeBox) : ℝ :=
  ∑ q∈R, if P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
    T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
    cb*w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1| then
    ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0

private theorem signed_indicator_bound (common : Prop) (a d e : ℝ) (he : 0≤e) :
    (if common ∧ a≤|d| then e else 0)≤
      (if common ∧ a≤d then e else 0)+(if common ∧ a≤-d then e else 0) := by
  by_cases hc : common
  · simp only [hc,true_and]
    by_cases hd : 0≤d
    · rw [abs_of_nonneg hd]
      split_ifs <;> linarith
    · rw [abs_of_nonpos (le_of_not_ge hd)]
      split_ifs <;> linarith
  · simp only [hc,false_and,ite_false,add_zero,le_refl]

theorem unsignedSizeTestEnergy_le (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex) (T : SlopeBox) :
    P.unsignedSizeTestEnergy w cb cell grid c R T≤
      P.sizeTestEnergy false w cb cell grid c R T+P.sizeTestEnergy true w cb cell grid c R T := by
  simp only [unsignedSizeTestEnergy,sizeTestEnergy,sizeTestPackets,Finset.sum_filter,
    sizeDirection,Bool.false_eq_true,ite_false,ite_true]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  simpa only [and_assoc] using signed_indicator_bound
    (P.length q.1≤T.length ∧
      (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
      T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (cb*w/P.length q.1) (T.slope-P.rowSlope q.1 q.2.1)
    (‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le)

theorem exists_two_sided_size_selection (w cb tau sigma epsilon A : ℝ)
    (hw : 0≤w) (hcb : 0≤cb) (hepsilon : 0<epsilon) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) :
    ∃ positive middle negative remaining,
      P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial positive middle ∧
      P.SizeStoppingRun true w cb tau sigma epsilon A cell grid c middle negative remaining ∧
      remaining⊆initial ∧
      ∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T≤sigma^2*T.area := by
  obtain ⟨positive,middle,hpos⟩ := P.exists_size_stopping_run false w cb tau sigma epsilon A
    hw hcb hepsilon hA cell grid c initial
  obtain ⟨negative,remaining,hneg⟩ := P.exists_size_stopping_run true w cb tau sigma epsilon A
    hw hcb hepsilon hA cell grid c middle
  refine ⟨positive,middle,negative,remaining,hpos,hneg,
    hneg.remaining_subset.trans hpos.remaining_subset,?_⟩
  intro T hwidth hlen
  have hp : P.sizeTestEnergy false w cb cell grid c remaining T≤sigma^2*T.area/2 := by
    apply le_of_not_gt
    intro hbad
    exact hpos.terminal_good T (P.sizeTestFails_mono false w cb tau sigma cell grid c
      hneg.remaining_subset T ⟨hwidth,hlen,hbad⟩)
  have hn : P.sizeTestEnergy true w cb cell grid c remaining T≤sigma^2*T.area/2 := by
    apply le_of_not_gt
    intro hbad
    exact hneg.terminal_good T ⟨hwidth,hlen,hbad⟩
  exact (P.unsignedSizeTestEnergy_le w cb cell grid c remaining T).trans (by linarith)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
