import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.FiniteProduct
import OAI.Probability.SKBarriers.SpinGlass.FiniteIndicators

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic.FiniteLaw
variable {X Y I J : Type*} [Fintype X] [Fintype Y] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem expect_expect_comm (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X → Y → ℝ) :
    P.expect (fun x => Q.expect (f x))=Q.expect (fun y => P.expect (fun x => f x y)) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem iid_expect_sum (P : FiniteLaw X) (f : (I ⊕ J → X) → ℝ) :
    (P.iid (I ⊕ J)).expect f=(P.iid I).expect (fun z => (P.iid J).expect (fun w => f (Sum.elim z w))) := by
  classical
  unfold expect iid pi
  calc
    _ = ∑ z : (I → X) × (J → X), (∏ i, P.weight (z.1 i))*(∏ j, P.weight (z.2 j))*f (Sum.elim z.1 z.2) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I J X)
      intro z
      simp only [Equiv.sumArrowEquivProdArrow_apply_fst,Equiv.sumArrowEquivProdArrow_apply_snd,Fintype.prod_sum_type]
      congr 1
      congr 1
      funext i
      cases i <;> rfl
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem iid_miss_bound (P : FiniteLaw X) (A : X → Prop) (K : ℕ) {a : ℝ}
    (_ha : 0 ≤ a) (hA : a ≤ P.prob A) :
    (P.iid (Fin K)).prob (fun z => ∀ i, ¬A (z i)) ≤ Real.exp (-a*K) := by
  have H := P.iid_predictable_bound (fun _ _ x => ¬A x) (fun _ => 1-P.prob A)
    (fun _ => sub_nonneg.mpr (P.prob_le_one A)) (fun _ _ => (P.prob_not A).le) K
  have H' : (P.iid (Fin K)).prob (fun z => ∀ i, ¬A (z i)) ≤ (1-P.prob A)^K := by
    simpa using H
  refine H'.trans ?_
  have hbase : 1-P.prob A ≤ Real.exp (-a) := by
    have H := Real.add_one_le_exp (-a)
    linarith only [H,hA]
  calc
    (1-P.prob A)^K ≤ (Real.exp (-a))^K := pow_le_pow_left₀ (sub_nonneg.mpr (P.prob_le_one A)) hbase K
    _ = Real.exp (-a*K) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem iid_cell_miss_bound (P : FiniteLaw X) (S : X → Prop) (R : X → X → Prop)
    (K : ℕ) {a δ : ℝ} (ha : 0 ≤ a)
    (hcov : P.prob (fun x => S x ∧ P.prob (fun y => S y ∧ R x y)<a) ≤ δ) :
    (P.iid (Fin K)).expect (fun z => P.prob (fun x => S x ∧ ∀ i, ¬(S (z i) ∧ R x (z i)))) ≤
      δ+Real.exp (-a*K) := by
  classical
  unfold prob
  rw [expect_expect_comm]
  calc
    _ ≤ P.expect (fun x => (if S x ∧ P.prob (fun y => S y ∧ R x y)<a then 1 else 0)+Real.exp (-a*K)) := by
      apply expect_mono
      intro x
      by_cases hb : S x ∧ P.prob (fun y => S y ∧ R x y)<a
      · rw [ite_eq_left hb]
        exact (prob_le_one _ _).trans (by linarith only [Real.exp_pos (-a*K)])
      · rw [ite_eq_right hb,zero_add]
        by_cases hx : S x
        · have hmass : a ≤ P.prob (fun y => S y ∧ R x y) := le_of_not_gt (fun h => hb ⟨hx,h⟩)
          simp only [hx,true_and]
          rw [expect_indicator_eq_prob]
          exact P.iid_miss_bound (fun y => S y ∧ R x y) K ha hmass
        · simp only [hx,false_and,ite_false,expect_zero,Real.exp_nonneg]
    _ = P.prob (fun x => S x ∧ P.prob (fun y => S y ∧ R x y)<a)+Real.exp (-a*K) := by
      rw [expect_add,expect_const,expect_indicator_eq_prob]
    _ ≤ _ := by linarith only [hcov]

theorem exists_le_expect (P : FiniteLaw X) (f : X → ℝ) : ∃ x, f x ≤ P.expect f := by
  classical
  by_contra! H
  have he : P.expect f < P.expect f := by
    calc
      P.expect f = ∑ x, P.weight x*P.expect f := by simp only [← Finset.sum_mul,P.sum_one,one_mul]
      _ < ∑ x, P.weight x*f x := by
        apply Finset.sum_lt_sum
        · intro x _
          exact mul_le_mul_of_nonneg_left (H x).le (P.nonneg x)
        · have hp : ∃ x, 0 < P.weight x := by
            by_contra! hp
            have hz : ∑ x, P.weight x=0 := Finset.sum_eq_zero (fun x _ => le_antisymm (hp x) (P.nonneg x))
            rw [P.sum_one] at hz
            norm_num at hz
          obtain ⟨x,hx⟩ := hp
          exact ⟨x,Finset.mem_univ x,mul_lt_mul_of_pos_left (H x) hx⟩
      _ = P.expect f := rfl
  exact lt_irrefl _ he

end SK.Analytic.FiniteLaw

end
end

end OAI
