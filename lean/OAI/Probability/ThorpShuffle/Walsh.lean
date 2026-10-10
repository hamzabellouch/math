import OAI.Probability.ThorpShuffle.PairAveraging

namespace OAI

universe uι uκ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def character {ι : Type uι} [Fintype ι] (a x : ι → Bool) : ℝ :=
  ∏ i, if a i then sign (x i) else 1

theorem character_symm {ι : Type uι} [Fintype ι] (a x : ι → Bool) :
    character a x = character x a := by
  apply Finset.prod_congr rfl
  intro i _
  cases a i <;> cases x i <;> rfl

@[simp] theorem character_false {ι : Type uι} [Fintype ι] (x : ι → Bool) :
    character (fun _ => false) x = 1 := by
  simp [character]

@[simp] theorem character_sq {ι : Type uι} [Fintype ι] (a x : ι → Bool) :
    character a x ^ 2 = 1 := by
  unfold character
  rw [← Finset.prod_pow]
  have h (i : ι) : (if a i then sign (x i) else (1 : ℝ)) ^ 2 = 1 := by
    cases a i <;> simp
  simp only [h, Finset.prod_const_one]

theorem sum_character_pair {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) :
    (∑ x : ι → Bool, character a x * character b x) =
      if a = b then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  have hlocal (u v : Bool) :
      (∑ x : Bool, (if u then sign x else (1 : ℝ)) * (if v then sign x else 1)) =
        if u = v then 2 else 0 := by
    cases u <;> cases v <;> norm_num [sign]
  have hf : (∑ x : ι → Bool, character a x * character b x) =
      ∏ i, (if a i = b i then (2 : ℝ) else 0) := by
    calc
      _ = ∑ x : ι → Bool, ∏ i,
          (if a i then sign (x i) else (1 : ℝ)) * (if b i then sign (x i) else 1) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.prod_mul_distrib).symm
      _ = ∏ i, ∑ x : Bool,
          (if a i then sign x else (1 : ℝ)) * (if b i then sign x else 1) :=
        (Fintype.prod_sum (fun (i : ι) (x : Bool) =>
          (if a i then sign x else (1 : ℝ)) * (if b i then sign x else 1))).symm
      _ = _ := by simp only [hlocal]
  rw [hf]
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, a i = b i := fun he => h (funext he)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sum_character_pair_dual {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) :
    (∑ a : ι → Bool, character a x * character a y) =
      if x = y then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  calc
    _ = ∑ a : ι → Bool, character x a * character y a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [character_symm a x, character_symm a y]
    _ = _ := sum_character_pair x y

def coefficient {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) (a : ι → Bool) : ℝ :=
  ∑ x, w x * character a x

theorem parseval {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) :
    mean (fun a : ι → Bool => coefficient w a ^ 2) = ∑ x, w x ^ 2 := by
  have hs :
      (∑ a : ι → Bool, coefficient w a ^ 2) =
        (Fintype.card (ι → Bool) : ℝ) * ∑ x, w x ^ 2 := by
    calc
      _ = ∑ a : ι → Bool, ∑ x, ∑ y,
          (character a x * character a y) * (w x * w y) := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [coefficient, pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = ∑ x, ∑ y, (∑ a : ι → Bool, character a x * character a y) * (w x * w y) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by
        simp only [sum_character_pair_dual, ite_mul, zero_mul]
        simp [Finset.mul_sum, pow_two]
  unfold mean
  rw [hs]
  have hcard : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ _ hcard

@[simp] theorem coefficient_false {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) :
    coefficient w (fun _ => false) = ∑ x, w x := by
  simp [coefficient]

theorem character_reindex {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a x : κ → Bool) :
    character (a ∘ e) (x ∘ e) = character a x := by
  exact Equiv.prod_comp e (fun i => if a i then sign (x i) else 1)

theorem character_cons (d : ℕ) (h b : Bool) (a x : Position d) :
    character (Fin.cons h a) (Fin.cons b x) =
      (if h then sign b else 1) * character a x := by
  simp [character, Fin.prod_univ_succ]

end Conditional

end Thorp

end

end OAI
