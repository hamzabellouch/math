import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace OAI

/-! # The harmonic square-root weight of tuples with no singleton -/

namespace Ostmann

open scoped BigOperators Classical

theorem tuple_range_fiber_card_le {A : Type*} [Fintype A] (n : ℕ) (S : Finset A) :
    ((Finset.univ : Finset (Fin n → A)).filter (fun x => Finset.univ.image x = S)).card ≤ n ^ n := by
  let T := (Finset.univ : Finset (Fin n → A)).filter (fun x => Finset.univ.image x = S)
  by_cases ht : T.Nonempty
  · obtain ⟨x, hx⟩ := ht
    have hxS : Finset.univ.image x = S := (Finset.mem_filter.mp hx).2
    have hS : S.card ≤ n := by
      rw [← hxS]
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := x)
    let f : T → (Fin n → S) := fun y i => ⟨y.val i, by
      rw [← (Finset.mem_filter.mp y.property).2]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    have hf : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun h i)
    have hc : T.card ≤ S.card ^ n := by
      simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
        Fintype.card_le_of_injective f hf
    exact hc.trans (Nat.pow_le_pow_left hS n)
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ n ^ n
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem all_multiple_sqrt_weight {A : Type*} [Fintype A] (n : ℕ) (w : A → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1) (x : Fin n → A)
    (hm : ∀ a ∈ Finset.univ.image x,
      2 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card) :
    (∏ i, Real.sqrt (w (x i))) ≤ ∏ a ∈ Finset.univ.image x, w a := by
  have he := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
    (t := Finset.univ.image x) (g := x) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun a => Real.sqrt (w a))
  rw [← he]
  apply Finset.prod_le_prod₀ (fun a _ => by positivity)
  intro a ha
  simp only [Finset.prod_const]
  calc
    Real.sqrt (w a) ^ ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card ≤
        Real.sqrt (w a) ^ 2 :=
      pow_le_pow_of_le_one (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (hw1 a)) (hm a ha)
    _ = w a := Real.sq_sqrt (hw0 a)

noncomputable def allMultipleTuples (A : Type*) [Fintype A] (n : ℕ) : Finset (Fin n → A) :=
  Finset.univ.filter (fun x => ∀ a ∈ Finset.univ.image x,
    2 ≤ ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card)

theorem exists_singleton_of_not_allMultiple {A : Type*} [Fintype A] {n : ℕ}
    (x : Fin n → A) (hx : x ∉ allMultipleTuples A n) :
    ∃ i, ∀ j, x j = x i → j = i := by
  simp only [allMultipleTuples, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
    not_le] at hx
  obtain ⟨a, ha⟩ := hx
  have ha' : a ∈ Finset.univ.image x ∧
      ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card < 2 := by
    obtain ⟨ha, hlt⟩ := ha
    exact ⟨ha, hlt⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha'.1
  have hpos : 0 < ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i => x i = a)).card = 1 := by omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  have hxi : x i = a := by
    have hm : i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => x i = a) := by rw [hi]; simp
    exact (Finset.mem_filter.mp hm).2
  refine ⟨i, fun l hl => ?_⟩
  have hm : l ∈ (Finset.univ : Finset (Fin n)).filter (fun i => x i = a) := by simp [hl, hxi]
  rw [hi] at hm
  exact Finset.mem_singleton.mp hm

/-- Grouping by the distinct value set pays at most n^n for the ordered
assignments, while each distinct prime contributes its full harmonic weight. -/
theorem all_multiple_tuple_weight_le {A : Type*} [Fintype A] (n : ℕ) (w : A → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1) :
    (∑ x ∈ allMultipleTuples A n, ∏ i, Real.sqrt (w (x i))) ≤
      (n : ℝ) ^ n * ∏ a, (1 + w a) := by
  have hmaps (x : Fin n → A) (_hx : x ∈ allMultipleTuples A n) :
      Finset.univ.image x ∈ (Finset.univ : Finset A).powerset := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber (S : Finset A) :
      (∑ x ∈ (allMultipleTuples A n).filter (fun x => Finset.univ.image x = S),
        ∏ i, Real.sqrt (w (x i))) ≤ (n : ℝ) ^ n * ∏ a ∈ S, w a := by
    let T := (allMultipleTuples A n).filter (fun x => Finset.univ.image x = S)
    have hT : T.card ≤ n ^ n := by
      apply (Finset.card_le_card (show T ⊆ (Finset.univ : Finset (Fin n → A)).filter
        (fun x => Finset.univ.image x = S) from ?_)).trans (tuple_range_fiber_card_le n S)
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩
    calc
      _ ≤ ∑ _x ∈ T, ∏ a ∈ S, w a := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hxA, hxS⟩ := Finset.mem_filter.mp hx
        have hm := (Finset.mem_filter.mp hxA).2
        simpa only [hxS] using all_multiple_sqrt_weight n w hw0 hw1 x hm
      _ = (T.card : ℝ) * ∏ a ∈ S, w a := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT)
        (Finset.prod_nonneg (fun a _ => hw0 a))
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset A).powerset, (n : ℝ) ^ n * ∏ a ∈ S, w a :=
      Finset.sum_le_sum (fun S _ => hfiber S)
    _ = (n : ℝ) ^ n * ∏ a, (1 + w a) := by
      rw [← Finset.mul_sum, ← Finset.prod_one_add]

theorem all_multiple_tuple_weight_exp {A : Type*} [Fintype A] (n : ℕ) (w : A → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∀ a, w a ≤ 1) :
    (∑ x ∈ allMultipleTuples A n, ∏ i, Real.sqrt (w (x i))) ≤
      (n : ℝ) ^ n * Real.exp (∑ a, w a) := by
  exact (all_multiple_tuple_weight_le n w hw0 hw1).trans
    (mul_le_mul_of_nonneg_left (Real.prod_one_add_le_exp_sum Finset.univ hw0) (by positivity))

end Ostmann

end OAI
