import OAI.Combinatorics.Crossing.ChordOrientations
import OAI.Combinatorics.Crossing.FiniteSeparation

namespace OAI

namespace Zarankiewicz

theorem orderSign_shift_of_separated (a b ε : ℝ) (hε : 0 < ε) (hab : a ≠ b)
    (hgap : ε < |a-b|) :
    orderSign a (b+ε) = orderSign a b ∧ orderSign a (b-ε) = orderSign a b := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [abs_of_neg (sub_neg.mpr h)] at hgap
    have hplus : a < b+ε := by linarith
    have hminus : a < b-ε := by linarith
    simp [orderSign,h,hplus,hminus]
  · rw [abs_of_pos (sub_pos.mpr h)] at hgap
    have hplus : b+ε < a := by linarith
    have hminus : b-ε < a := by linarith
    simp [orderSign,not_lt.mpr h.le,h,hplus,hminus,
      not_lt.mpr hplus.le,not_lt.mpr hminus.le]

theorem orderSign_opposite_average (a b ε : ℝ) (hε : 0<ε)
    (hgap : a ≠ b → ε < |a-b|) :
    (orderSign a (b+ε)+orderSign a (b-ε))/2 = orderSign a b := by
  by_cases hab : a = b
  · subst b
    have hplus : a < a+ε := by linarith
    have hminus : a-ε < a := by linarith
    simp [orderSign,hplus,hminus,not_lt.mpr hminus.le]
  · obtain ⟨hp,hm⟩ := orderSign_shift_of_separated a b ε hε hab (hgap hab)
    rw [hp,hm]
    ring

theorem shifted_node_ne {ι : Type*} (node : ι → ℝ) (hn : Function.Injective node)
    (ε : ℝ) (hε : 0<ε) (hgap : ∀ i j, i ≠ j → ε < |node i-node j|) (i j : ι) :
    node i ≠ node j+ε ∧ node i ≠ node j-ε := by
  by_cases heq : node i = node j
  · have hij := hn heq
    subst j
    constructor <;> linarith
  · have hg := hgap i j (fun hij => heq (congrArg node hij))
    constructor
    · intro he
      rw [he] at hg
      simp only [add_sub_cancel_left,abs_of_pos hε] at hg
      exact (lt_irrefl ε) hg
    · intro he
      have hh : |node i-node j| = ε := by rw [he]; rw [sub_sub_cancel_left,abs_neg,abs_of_pos hε]
      rw [hh] at hg
      exact (lt_irrefl ε) hg

end Zarankiewicz

end OAI
