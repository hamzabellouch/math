import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped BigOperators

def stepAt (root before after t : ℝ) : ℝ := if t < root then before else after

def stepEvent {n : ℕ} (r lo hi : Fin n → ℝ) (i : Fin n) : ℝ :=
  if 0 < r i ∧ r i < 1 then
    (hi i-lo i) * ∏ j, if j=i then 1 else stepAt (r j) (lo j) (hi j) (r i)
  else 0

theorem sum_stepEvent (n : ℕ) (r lo hi : Fin n → ℝ) (hr : StrictMono r)
    (h0 : ∀ i, r i ≠ 0) (h1 : ∀ i, r i ≠ 1) :
    (∑ i, stepEvent r lo hi i) =
      (∏ i, stepAt (r i) (lo i) (hi i) 1) - ∏ i, stepAt (r i) (lo i) (hi i) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    let rt := fun i : Fin n => r i.succ
    let lt := fun i : Fin n => lo i.succ
    let ht := fun i : Fin n => hi i.succ
    have hrt : StrictMono rt := hr.comp (fun _ _ h => Fin.succ_lt_succ_iff.mpr h)
    have hind := ih rt lt ht hrt (fun i => h0 i.succ) (fun i => h1 i.succ)
    have hfirst : ∀ i : Fin n, r 0 < r i.succ := fun i => hr (Fin.succ_pos i)
    have hhead : stepEvent r lo hi 0 =
        if 0 < r 0 ∧ r 0 < 1 then (hi 0-lo 0) * ∏ i : Fin n, lt i else 0 := by
      unfold stepEvent
      rw [Fin.prod_univ_succ]
      simp only [ite_true,one_mul,Fin.succ_ne_zero,ite_false]
      congr 1
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact ite_eq_left (hfirst i)
    have htail : ∀ i : Fin n, stepEvent r lo hi i.succ = hi 0 * stepEvent rt lt ht i := by
      intro i
      unfold stepEvent
      rw [Fin.prod_univ_succ]
      simp only [(Fin.succ_ne_zero i).symm,ite_false,Fin.succ_inj]
      rw [show stepAt (r 0) (lo 0) (hi 0) (r i.succ) = hi 0 from ite_eq_right (not_lt.mpr (hfirst i).le)]
      change (if 0 < rt i ∧ rt i < 1 then (ht i-lt i) *
        (hi 0 * ∏ j, if j=i then 1 else stepAt (rt j) (lt j) (ht j) (rt i)) else 0) = _
      split_ifs <;> ring
    rw [Fin.sum_univ_succ,hhead]
    simp_rw [htail]
    rw [← Finset.mul_sum,hind,Fin.prod_univ_succ,Fin.prod_univ_succ]
    rcases lt_or_gt_of_ne (h0 0) with hrneg | hrpos
    · have hn1 : ¬ 1 < r 0 := by linarith
      have hn0 : ¬ 0 < r 0 := by linarith
      simp only [hn0,false_and,ite_false,stepAt,hn1]
      ring
    · rcases lt_or_gt_of_ne (h1 0) with hrlt | hrgt
      · have hn1 : ¬ 1 < r 0 := by linarith
        have ht0 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 0) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrpos.trans (hfirst i))
        rw [ht0]
        simp only [hrpos,hrlt,and_self,ite_true,stepAt,hn1,ite_false]
        ring
      · have ht0 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 0) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrpos.trans (hfirst i))
        have ht1 : (∏ i : Fin n, stepAt (rt i) (lt i) (ht i) 1) = ∏ i : Fin n, lt i := by
          apply Finset.prod_congr rfl
          intro i hi
          exact ite_eq_left (hrgt.trans (hfirst i))
        rw [ht0,ht1]
        simp [stepAt,hrpos,hrgt,not_lt.mpr hrgt.le]

end Zarankiewicz

end

end OAI
