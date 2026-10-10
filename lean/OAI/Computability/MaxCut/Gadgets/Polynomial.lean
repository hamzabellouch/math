import Mathlib
import OAI.Computability.MaxCut.Estimates.Degree

namespace OAI

noncomputable section
namespace OptimalMaxCut.BooleanFourthMoment
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad

 theorem sum_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    ∑ x, F x = ∑ b : Bool, ∑ y : Cube (Fin n), F (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  exact Fintype.sum_prod_type _

 theorem expect_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, F x) = 𝔼 b : Bool, 𝔼 y : Cube (Fin n), F (Fin.cons b y) := by
  calc
    _ = 𝔼 p : Bool × Cube (Fin n), F (Fin.cons p.1 p.2) :=
      (Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) _ F (fun _ => rfl)).symm
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]

 theorem expect_bool (F : Bool → ℝ) : (𝔼 b, F b) = (F false + F true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [add_comm]

noncomputable def polynomial {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (x : Cube I) : ℝ := ∑ s, c s * walsh s x

noncomputable def energy {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) : ℝ :=
  ∑ s, (∏ i, if s i then (3 : ℝ) else 1) * c s ^ 2

 theorem energy_nonneg {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    0 ≤ energy c := by
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg _ (sq_nonneg _)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> norm_num

 theorem walsh_cons {n : ℕ} (s x : Cube (Fin n)) (a b : Bool) :
    walsh (Fin.cons a s) (Fin.cons b x) = (if a then bitSign b else 1) * walsh s x := by
  cases a <;> simp [walsh, Fin.prod_univ_succ, bitSign]

 theorem polynomial_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) (x : Cube (Fin n)) (b : Bool) :
    polynomial c (Fin.cons b x) = polynomial (fun s => c (Fin.cons false s)) x +
      bitSign b * polynomial (fun s => c (Fin.cons true s)) x := by
  unfold polynomial
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [walsh_cons, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

 theorem energy_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    energy c = energy (fun s => c (Fin.cons false s)) +
      3 * energy (fun s => c (Fin.cons true s)) := by
  unfold energy
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
    one_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

 theorem fourth_moment_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) =
      (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 4) +
      6 * (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 2 *
        polynomial (fun s => c (Fin.cons true s)) x ^ 2) +
      (𝔼 x, polynomial (fun s => c (Fin.cons true s)) x ^ 4) := by
  rw [expect_cube_succ, Finset.expect_comm]
  simp_rw [expect_bool]
  simp only [polynomial_cons, bitSign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  simp_rw [show ∀ a b : ℝ, ((a + b) ^ 4 + (a + -b) ^ 4) / 2 = a ^ 4 + 6 * (a ^ 2 * b ^ 2) + b ^ 4 by
    intro a b; ring]
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect]

 theorem fourth_moment_bound (n : ℕ) (c : Cube (Fin n) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) ≤ energy c ^ 2 := by
  induction n with
  | zero => simp [polynomial, energy, walsh]; exact le_of_eq (by ring)
  | succ n ih =>
    let c₀ : Cube (Fin n) → ℝ := fun s => c (Fin.cons false s)
    let c₁ : Cube (Fin n) → ℝ := fun s => c (Fin.cons true s)
    have h₀ := ih c₀
    have h₁ := ih c₁
    have he₀ := energy_nonneg c₀
    have he₁ := energy_nonneg c₁
    have hm₀ : 0 ≤ 𝔼 x, polynomial c₀ x ^ 4 := by positivity
    have hm₁ : 0 ≤ 𝔼 x, polynomial c₁ x ^ 4 := by positivity
    have hc := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => polynomial c₀ x ^ 2) (fun x => polynomial c₁ x ^ 2)
    simp only [← pow_mul, Nat.reduceMul] at hc
    have hc' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ^ 2 ≤
        (energy c₀ * energy c₁) ^ 2 := by
      calc _ ≤ _ := hc
           _ ≤ energy c₀ ^ 2 * energy c₁ ^ 2 := mul_le_mul h₀ h₁ hm₁ (sq_nonneg _)
           _ = _ := by ring
    have hc'' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ≤ energy c₀ * energy c₁ :=
      (sq_le_sq₀ (by positivity) (mul_nonneg he₀ he₁)).mp hc'
    rw [fourth_moment_cons, energy_cons]
    change (𝔼 x, polynomial c₀ x ^ 4) +
      6 * (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) +
      (𝔼 x, polynomial c₁ x ^ 4) ≤ (energy c₀ + 3 * energy c₁) ^ 2
    nlinarith [sq_nonneg (energy c₁)]

 theorem weight_eq_degree {I : Type*} [Fintype I] [DecidableEq I] (s : Cube I) :
    (∏ i, if s i then (3 : ℝ) else 1) = 3 ^ Analytic.degree s := by
  simp [Finset.prod_ite, Analytic.degree]

 theorem energy_truncated {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (c : Cube I → ℝ) (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    energy c ≤ 3 ^ K * ∑ s, c s ^ 2 := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [weight_eq_degree]
  by_cases hs : Analytic.degree s ≤ K
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (sq_nonneg _)
  · rw [hc s (lt_of_not_ge hs)]; simp

 theorem coefficient_polynomial {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (a : Cube I) : coefficient (polynomial c) a = c a := by
  unfold coefficient polynomial
  simp only [Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_expect, walsh_orthogonality]
  simp

 theorem polynomial_second_moment {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    (𝔼 x, polynomial c x ^ 2) = ∑ s, c s ^ 2 := by
  rw [← walsh_parseval]
  simp only [coefficient_polynomial]

 theorem degree_fourth_moment_bound {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    (𝔼 x, polynomial c x ^ 4) ≤ (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 := by
  rw [polynomial_second_moment]
  exact (fourth_moment_bound n c).trans
    ((sq_le_sq₀ (energy_nonneg c) (by positivity)).mpr (energy_truncated K c hc))

 theorem degree_third_moment_bound {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsmall : (𝔼 x, polynomial c x ^ 2) ≤ τ ^ 2) :
    (𝔼 x, |polynomial c x| ^ 3) ≤ 3 ^ K * τ * (𝔼 x, polynomial c x ^ 2) := by
  have hsecond : 0 ≤ 𝔼 x, polynomial c x ^ 2 := by positivity
  have hfourth := degree_fourth_moment_bound c hc
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |polynomial c x|) (fun x => polynomial c x ^ 2)
  have hp (a : ℝ) : |a| * a ^ 2 = |a| ^ 3 := by rw [← sq_abs]; ring
  simp_rw [hp, sq_abs, ← pow_mul, Nat.reduceMul] at hCS
  have hbound : (𝔼 x, |polynomial c x| ^ 3) ^ 2 ≤
      (3 ^ K * τ * (𝔼 x, polynomial c x ^ 2)) ^ 2 := by
    calc
      _ ≤ (𝔼 x, polynomial c x ^ 2) * (𝔼 x, polynomial c x ^ 4) := hCS
      _ ≤ (𝔼 x, polynomial c x ^ 2) * (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourth hsecond
      _ = (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 * (𝔼 x, polynomial c x ^ 2) := by ring
      _ ≤ (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 * τ ^ 2 :=
        mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hbound

 theorem walsh_flip {I : Type*} [Fintype I] [DecidableEq I]
    (s x : Cube I) (i : I) :
    walsh s (Function.update x i (!x i)) = (if s i then -1 else 1) * walsh s x := by
  classical
  have hp (j : I) : bitSign (s j && Function.update x i (!x i) j) =
      (if j = i then (if s i then (-1 : ℝ) else 1) else 1) * bitSign (s j && x j) := by
    by_cases h : j = i
    · subst j; cases s i <;> cases x i <;> simp [bitSign]
    · simp [h]
  simp only [walsh, hp, Finset.prod_mul_distrib]
  simp

noncomputable def discreteDiff {I : Type*} [Fintype I] [DecidableEq I]
    (f : Cube I → ℝ) (i : I) (x : Cube I) : ℝ := (f x - f (Function.update x i (!x i))) / 2

 theorem polynomial_diff {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (i : I) :
    discreteDiff (polynomial c) i = polynomial (fun s => if s i then c s else 0) := by
  funext x
  simp only [discreteDiff, polynomial, walsh_flip, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  cases s i <;> simp

 theorem total_diff_second {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) :
    (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) =
      ∑ s, (Analytic.degree s : ℝ) * c s ^ 2 := by
  simp only [polynomial_diff, polynomial_second_moment]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [ite_pow, zero_pow (by omega : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp [Analytic.degree]

 theorem total_diff_second_truncated {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (c : Cube I → ℝ) (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤
      K * (𝔼 x, polynomial c x ^ 2) := by
  rw [total_diff_second, polynomial_second_moment, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : Analytic.degree s ≤ K
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg _)
  · rw [hc s (lt_of_not_ge hs)]; simp

 theorem total_diff_third_truncated {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsmall : ∀ i, (𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤ τ ^ 2) :
    (∑ i, 𝔼 x, |discreteDiff (polynomial c) i x| ^ 3) ≤
      3 ^ K * τ * K * (𝔼 x, polynomial c x ^ 2) := by
  calc
    _ ≤ ∑ i, 3 ^ K * τ * (𝔼 x, discreteDiff (polynomial c) i x ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hsmall i
      rw [polynomial_diff] at hi ⊢
      exact degree_third_moment_bound _ (fun s hs => by rw [hc s hs]; split_ifs <;> rfl)
        hτ hi
    _ = 3 ^ K * τ * (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 3 ^ K * τ * (K * (𝔼 x, polynomial c x ^ 2)) :=
      mul_le_mul_of_nonneg_left (total_diff_second_truncated K c hc) (by positivity)
    _ = _ := by ring

end OptimalMaxCut.BooleanFourthMoment

end

end OAI
