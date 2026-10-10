import OAI.Analysis.LipschitzHilbert.Trees.SourceLongPrefixes

namespace OAI

/-! The hard angular cutoff in the frozen long-tree expression selects
one exact interval of the original scale indices. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def angularStart (w d : ℝ) : ℕ :=
  (Finset.univ.filter (fun j : Fin N => w/P.length j<d)).sup (fun j => j.val+1)

theorem angularStart_le (w d : ℝ) : P.angularStart w d≤N := by
  apply Finset.sup_le
  intro j _
  omega

theorem angularStart_spec (w d : ℝ) (hw : 0≤w) (j : Fin N) :
    j.val<P.angularStart w d ↔ w/P.length j<d := by
  unfold angularStart
  rw [Finset.lt_sup_iff]
  constructor
  · rintro ⟨k,hk,hjk⟩
    have hkj : j≤k := by change j.val≤k.val; omega
    have hdiv : w/P.length j≤w/P.length k :=
      div_le_div_of_nonneg_left hw (P.length_pos k) (P.length_antitone hkj)
    exact hdiv.trans_lt (Finset.mem_filter.mp hk).2
  · intro hj
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,by omega⟩

def frozenLongValue (t r w s : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    EuclideanSpace ℂ κ :=
  ∑ j : Fin N, if 32*r<P.length j ∧ |s-t|≤w/P.length j then
    planarFixedSynthesis (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
      (fun a k => P.physicalPacket t j a.1 a.2 k) z else 0

/-- The frozen selector tail, intersected with the long prefix, is a
literal interval difference, including the empty-interval case. -/
theorem frozenLongValue_eq_interval (t r w s : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    P.frozenLongValue t r w s c z=
      P.physicalLongIntervalSchwartz t r c (P.angularStart w |s-t|) N z := by
  simp only [physicalLongIntervalSchwartz,sub_apply,physicalTreePartialSchwartz_apply,
    physicalTreePartial,packetPartialSum]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hl : j.val<min N (P.longPrefix r) ↔ 32*r<P.length j := by
    rw [lt_min_iff,P.longPrefix_spec]
    exact and_iff_right j.isLt
  have ha : j.val<min (P.angularStart w |s-t|) (P.longPrefix r) ↔
      ¬|s-t|≤w/P.length j ∧ 32*r<P.length j := by
    rw [lt_min_iff,P.angularStart_spec w |s-t| hw,P.longPrefix_spec,not_le]
  by_cases hj : 32*r<P.length j <;> by_cases hs : |s-t|≤w/P.length j <;>
    simp only [hl,ha,hj,hs,and_true,and_false,not_true_eq_false,
      not_false_eq_true,ite_true,ite_false,sub_zero,sub_self]

theorem frozenLongValue_norm (t r w s : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    ‖P.frozenLongValue t r w s c z‖≤P.physicalTreeMaximal t c z := by
  rw [P.frozenLongValue_eq_interval t r w s hw c z]
  exact P.physicalLongIntervalSchwartz_norm t r c _ _ z

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
