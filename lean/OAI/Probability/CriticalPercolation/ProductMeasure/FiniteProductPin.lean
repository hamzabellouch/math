import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

noncomputable def pin (w : E → A → ℝ) (e : E) (b : A) : E → A → ℝ :=
  Function.update w e (fun a => if a = b then 1 else 0)

omit [Fintype E] [Fintype A] in
lemma pin_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (e : E) (b : A) :
    ∀ j a, 0 ≤ pin w e b j a := by
  intro j a
  by_cases h : j = e
  · subst j; simp [pin]; split_ifs <;> norm_num
  · simpa [pin,h] using hw j a

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

def prefixEvent : List (E × A) → (E → A) → Prop
  | [], _ => True
  | (e,b)::xs, ω => ω e = b ∧ prefixEvent xs ω

noncomputable def prefixWeight (w : E → A → ℝ) : List (E × A) → E → A → ℝ
  | [] => w
  | (e,b)::xs => prefixWeight (pin w e b) xs

noncomputable def prefixFactor (w : E → A → ℝ) : List (E × A) → ℝ
  | [] => 1
  | (e,b)::xs => w e b*prefixFactor (pin w e b) xs

omit [Fintype E] [Fintype A] in
lemma prefixWeight_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (xs : List (E × A)) :
    ∀ e a, 0 ≤ prefixWeight w xs e a := by
  induction xs generalizing w with
  | nil => exact hw
  | cons x xs ih => exact ih _ (pin_nonneg w hw x.1 x.2)

omit [Fintype E] in
lemma prefixWeight_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (xs : List (E × A)) : ∀ e, ∑ a, prefixWeight w xs e a = 1 := by
  induction xs generalizing w with
  | nil => exact hw
  | cons x xs ih => exact ih _ (pin_normalized w hw x.1 x.2)

omit [Fintype E] [Fintype A] in
lemma prefixFactor_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (xs : List (E × A)) :
    0 ≤ prefixFactor w xs := by
  induction xs generalizing w with
  | nil => exact zero_le_one
  | cons x xs ih => exact mul_nonneg (hw _ _) (ih _ (pin_nonneg w hw x.1 x.2))

theorem expect_prefix (w : E → A → ℝ) (xs : List (E × A)) (f : (E → A) → ℝ) :
    expect w (fun ω => if prefixEvent xs ω then f ω else 0) =
      prefixFactor w xs*expect (prefixWeight w xs) f := by
  induction xs generalizing w with
  | nil => simp [prefixEvent,prefixFactor,prefixWeight]
  | cons x xs ih =>
    have he : (fun ω => if prefixEvent (x::xs) ω then f ω else 0) =
        (fun ω => if ω x.1 = x.2 then (if prefixEvent xs ω then f ω else 0) else 0) := by
      funext ω
      by_cases h : ω x.1 = x.2 <;> by_cases hp : prefixEvent xs ω <;> simp [prefixEvent,h,hp]
    rw [he,expect_mask_pin,ih]
    exact (mul_assoc _ _ _).symm

omit [Fintype E] [Fintype A] in
lemma prefixWeight_fresh (w : E → A → ℝ) (xs : List (E × A)) (e : E)
    (he : e ∉ xs.map Prod.fst) : prefixWeight w xs e = w e := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at he
    rw [prefixWeight,ih _ he.2,pin,Function.update_of_ne he.1]
end CriticalPercolation.FiniteProduct

end
end

end OAI
