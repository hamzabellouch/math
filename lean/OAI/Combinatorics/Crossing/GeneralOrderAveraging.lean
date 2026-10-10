import OAI.Combinatorics.Crossing.OrderShift

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem orderSign_of_close (a b z ε : ℝ) (hgap : ε < |a-b|) (hz : |z-b| < ε) :
    orderSign a z = orderSign a b := by
  have ha : a ≠ b := by intro h; subst a; simp at hgap; have := abs_nonneg (z-b); linarith
  have hzb := abs_lt.mp hz
  rcases lt_or_gt_of_ne ha with hab | hba
  · have hgz : a < z := by rw [abs_of_neg (sub_neg.mpr hab)] at hgap; linarith
    simp [orderSign,hab,hgz]
  · have hgz : z < a := by rw [abs_of_pos (sub_pos.mpr hba)] at hgap; linarith
    simp [orderSign,not_lt.mpr hba.le,not_lt.mpr hgz.le,hba,hgz]

theorem orderSign_straddling_average (a b p q ε : ℝ)
    (hgap : a ≠ b → ε < |a-b|) (hp : |p-b| < ε) (hq : |q-b| < ε)
    (hstraddle : (p<b ∧ b<q) ∨ (q<b ∧ b<p)) :
    (orderSign a p+orderSign a q)/2 = orderSign a b := by
  by_cases hab : a=b
  · subst a
    rcases hstraddle with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · simp [orderSign,hp,hq,not_lt.mpr hp.le]
    · simp [orderSign,hp,hq,not_lt.mpr hq.le]
  · rw [orderSign_of_close a b p ε (hgap hab) hp,orderSign_of_close a b q ε (hgap hab) hq]
    ring

end Zarankiewicz

end

end OAI
