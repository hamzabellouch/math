import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Spin

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
namespace FiniteLaw
variable {α : Type*} [Fintype α]

def mean (p : α → ℝ) (f : α → ℝ) : ℝ := ∑ x, p x * f x

def variance (p : α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ x, p x * (f x - mean p f) ^ 2

theorem variance_eq (p f : α → ℝ) (hp1 : ∑ x, p x = 1) :
    variance p f = mean p (fun x => f x ^ 2) - mean p f ^ 2 := by
  have h (x : α) : p x * (f x - mean p f) ^ 2 =
      p x * f x ^ 2 - 2 * mean p f * (p x * f x) + mean p f ^ 2 * p x := by ring
  simp only [variance, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hp1, mul_one]
  simp only [mean]
  ring

theorem common_mass (p q : α → ℝ) (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    ∑ x, min (p x) (q x) = 1 - totalVariation p q := by
  have h (x : α) : min (p x) (q x) = (p x + q x - |p x - q x|) / 2 := by
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp only [h, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1,
    totalVariation]
  ring

theorem common_mass_square (p q f : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) :
    (1 - totalVariation p q) * (mean p f - mean q f) ^ 2 ≤
      2 * variance p f + 2 * variance q f := by
  rw [← common_mass p q hp1 hq1, Finset.sum_mul]
  calc
    _ ≤ ∑ x, (2 * (p x * (f x - mean p f) ^ 2) +
        2 * (q x * (f x - mean q f) ^ 2)) := by
      apply Finset.sum_le_sum
      intro x _
      have hpoint : (mean p f - mean q f) ^ 2 ≤
          2 * (f x - mean p f) ^ 2 + 2 * (f x - mean q f) ^ 2 := by nlinarith [sq_nonneg (2 * f x - mean p f - mean q f)]
      have hmul := mul_le_mul_of_nonneg_left hpoint (le_min (hp x) (hq x))
      have hpbound := mul_le_mul_of_nonneg_right (min_le_left (p x) (q x)) (sq_nonneg (f x - mean p f))
      have hqbound := mul_le_mul_of_nonneg_right (min_le_right (p x) (q x)) (sq_nonneg (f x - mean q f))
      nlinarith only [hmul, hpbound, hqbound]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, variance]

theorem totalVariation_square (p q : α → ℝ) :
    4 * totalVariation p q ^ 2 ≤ (Fintype.card α : ℝ) * ∑ x, (p x - q x) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x : α => (1 : ℝ)) (fun x => |p x - q x|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at h
  unfold totalVariation
  nlinarith only [h]

end FiniteLaw
namespace Independent
variable {n : ℕ}

@[simp] theorem spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]

@[simp] theorem spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]

@[simp] theorem coupling_zero (i j : Fin n) : coupling (0 : Disorder n) i j = 0 := by
  simp [coupling]

@[simp] theorem mass_zero (x : Spin n) : mass (0 : Disorder n) 0 x = 1 / (2 : ℝ) ^ n := by
  simp [mass, weight, hamiltonian, partition, Spin]

@[simp] theorem siteKernel_zero (i : Fin n) (x y : Spin n) :
    siteKernel (0 : Disorder n) i x y =
      (if y = x then 1 / 2 else 0) + (if y = flip i x then 1 / 2 else 0) := by
  have h : (1 / (2 : ℝ) ^ n) / (1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ n) = 1 / 2 := by
    field_simp
    norm_num
  simp only [siteKernel, mass_zero, h]

def character (S : Finset (Fin n)) (x : Spin n) : ℝ := ∏ i ∈ S, spinValue (x i)

@[simp] theorem character_empty (x : Spin n) : character ∅ x = 1 := by simp [character]

@[simp] theorem character_sq (S : Finset (Fin n)) (x : Spin n) : character S x ^ 2 = 1 := by
  simp only [character, ← Finset.prod_pow, spinValue_sq, Finset.prod_const_one]

@[simp] theorem character_plus (S : Finset (Fin n)) : character S (fun _ => true) = 1 := by
  simp [character, spinValue]

@[simp] theorem character_flip (S : Finset (Fin n)) (i : Fin n) (x : Spin n) :
    character S (flip i x) = if i ∈ S then -character S x else character S x := by
  by_cases hi : i ∈ S
  · simp only [ite_eq_left hi, character]
    rw [← Finset.mul_prod_erase S _ hi, ← Finset.mul_prod_erase S (fun j => spinValue (x j)) hi]
    simp only [flip_same, spinValue_not, neg_mul]
    congr 2
    apply Finset.prod_congr rfl
    intro j hj
    rw [flip_other i j x (Finset.mem_erase.mp hj).1]
  · simp only [ite_eq_right hi, character]
    apply Finset.prod_congr rfl
    intro j hj
    rw [flip_other i j x (fun h => hi (h ▸ hj))]

theorem character_complete (x y : Spin n) :
    ∑ S : Finset (Fin n), character S x * character S y =
      if x = y then (2 : ℝ) ^ n else 0 := by
  have hxyp : ∑ S : Finset (Fin n), character S x * character S y =
      ∏ i, (spinValue (x i) * spinValue (y i) + 1) := by
    simp only [Fintype.prod_add, Finset.prod_const_one, mul_one, character,
      Finset.prod_mul_distrib]
  rw [hxyp]
  by_cases hxy : x = y
  · subst y
    simp only [← sq, spinValue_sq]
    norm_num
  · simp only [ite_eq_right hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [spinValue]

def eigenvalue (S : Finset (Fin n)) : ℝ := 1 - (S.card : ℝ) / n

theorem siteKernel_character (i : Fin n) (x : Spin n) (S : Finset (Fin n)) :
    ∑ y, siteKernel (0 : Disorder n) i x y * character S y =
      if i ∈ S then 0 else character S x := by
  simp only [siteKernel_zero, add_mul, Finset.sum_add_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, character_flip]
  split_ifs <;> ring

theorem transition_character (hn : 0 < n) (x : Spin n) (S : Finset (Fin n)) :
    ∑ y, transition (0 : Disorder n) x y * character S y = eigenvalue S * character S x := by
  simp only [transition, Nat.ne_of_gt hn, ↓reduceIte, div_mul_eq_mul_div,
    ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [siteKernel_character]
  have hmem : ∑ i : Fin n, (if i ∈ S then 0 else character S x) =
      (n : ℝ) * character S x - (S.card : ℝ) * character S x := by
    have hf (i : Fin n) : (if i ∈ S then 0 else character S x) =
        character S x - (if i ∈ S then character S x else 0) := by split_ifs <;> ring
    simp only [hf, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hmem]
  dsimp [eigenvalue]
  field_simp

theorem power_character (hn : 0 < n) (k : ℕ) (x : Spin n) (S : Finset (Fin n)) :
    ∑ y, (transition (0 : Disorder n) ^ k) x y * character S y =
      eigenvalue S ^ k * character S x := by
  induction k generalizing x with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    have he (z : Spin n) : ∑ y, (transition (0 : Disorder n) ^ k) x z *
        transition 0 z y * character S y =
        (transition (0 : Disorder n) ^ k) x z * (eigenvalue S * character S z) := by
      simp only [mul_assoc, ← Finset.mul_sum, transition_character hn]
    simp only [he]
    rw [show (∑ z, (transition (0 : Disorder n) ^ k) x z *
        (eigenvalue S * character S z)) = eigenvalue S *
        ∑ z, (transition (0 : Disorder n) ^ k) x z * character S z from by
          rw [Finset.mul_sum]; congr 1; funext z; ring]
    rw [ih]
    ring

theorem return_probability (hn : 0 < n) (k : ℕ) (x : Spin n) :
    (2 : ℝ) ^ n * (transition (0 : Disorder n) ^ k) x x =
      ∑ S : Finset (Fin n), eigenvalue S ^ k := by
  have H := congrArg (fun f : Finset (Fin n) → ℝ => ∑ S, f S * character S x)
    (funext (power_character hn k x))
  simp only [Finset.sum_mul] at H
  rw [Finset.sum_comm] at H
  have hinn (y : Spin n) : ∑ S : Finset (Fin n),
      (transition (0 : Disorder n) ^ k) x y * character S y * character S x =
      (transition (0 : Disorder n) ^ k) x y * (if y = x then (2 : ℝ) ^ n else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum, character_complete]
  simp only [hinn, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at H
  have hright (S : Finset (Fin n)) : eigenvalue S ^ k * character S x * character S x =
      eigenvalue S ^ k := by rw [mul_assoc, ← sq, character_sq, mul_one]
  simp only [hright] at H
  simpa only [mul_comm] using H

theorem transition_isSymm : (transition (0 : Disorder n)).IsSymm := by
  have hsite (i : Fin n) (x y : Spin n) : siteKernel 0 i x y = siteKernel 0 i y x := by
    have hb := siteKernel_balance (0 : Disorder n) i x y
    simp only [mass_zero] at hb
    exact mul_left_cancel₀ (one_div_ne_zero (pow_ne_zero n (by norm_num))) hb
  change (transition (0 : Disorder n))ᵀ = transition 0
  by_cases hn : n = 0
  · simp [transition, hn]
  · apply Matrix.ext
    intro x y
    change transition 0 y x = transition 0 x y
    simp only [transition, hn, ↓reduceIte]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hsite i y x)

theorem eigenvalue_nonneg (hn : 0 < n) (S : Finset (Fin n)) : 0 ≤ eigenvalue S := by
  have hc : (S.card : ℝ) ≤ n := by
    exact_mod_cast (show S.card ≤ n from (Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  exact sub_nonneg.mpr ((div_le_one (Nat.cast_pos.mpr hn)).mpr hc)

theorem eigenvalue_exp_bound (hn : 0 < n) (k : ℕ) (S : Finset (Fin n)) :
    eigenvalue S ^ (2 * k) ≤ Real.exp (-2 * k / n) ^ S.card := by
  have h := pow_le_pow_left₀ (eigenvalue_nonneg hn S)
    (Real.one_sub_le_exp_neg ((S.card : ℝ) / n)) (2 * k)
  apply h.trans_eq
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem sum_eigenvalue_bound (hn : 0 < n) (k : ℕ) :
    (∑ S : Finset (Fin n), eigenvalue S ^ (2 * k)) ≤
      Real.exp ((n : ℝ) * Real.exp (-2 * k / n)) := by
  calc
    _ ≤ ∑ S : Finset (Fin n), Real.exp (-2 * k / n) ^ S.card :=
      Finset.sum_le_sum (fun S _ => eigenvalue_exp_bound hn k S)
    _ = (Real.exp (-2 * k / n) + 1) ^ n := by
      have h := Fintype.prod_add (fun _ : Fin n => Real.exp (-2 * k / n)) (fun _ => (1 : ℝ))
      simpa using h.symm
    _ ≤ Real.exp (Real.exp (-2 * k / n)) ^ n :=
      pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) n
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem row_square (hn : 0 < n) (k : ℕ) (x : Spin n) :
    (2 : ℝ) ^ n * ∑ y, ((transition (0 : Disorder n) ^ k) x y) ^ 2 =
      ∑ S : Finset (Fin n), eigenvalue S ^ (2 * k) := by
  have hret := return_probability hn (2 * k) x
  have h : (transition (0 : Disorder n) ^ (2 * k)) x x =
      ∑ y, ((transition (0 : Disorder n) ^ k) x y) ^ 2 := by
    rw [two_mul, pow_add, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro y _
    rw [(transition_isSymm.pow k).apply x y, sq]
  rwa [h] at hret

theorem row_centered_square (hn : 0 < n) (k : ℕ) (x : Spin n) :
    (2 : ℝ) ^ n * ∑ y, ((transition (0 : Disorder n) ^ k) x y - mass 0 0 y) ^ 2 =
      (∑ S : Finset (Fin n), eigenvalue S ^ (2 * k)) - 1 := by
  have hsum := Matrix.sum_row_of_mem_rowStochastic (transition_pow_stochastic (0 : Disorder n) k) x
  have hcard : (Fintype.card (Spin n) : ℝ) = (2 : ℝ) ^ n := by simp [Spin]
  calc
    _ = (2 : ℝ) ^ n * ∑ y, ((transition (0 : Disorder n) ^ k) x y) ^ 2 - 1 := by
      simp only [mass_zero, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcard]
      field_simp
      ring
    _ = _ := by rw [row_square hn k x]

theorem row_tv_square_upper (hn : 0 < n) (k : ℕ) (x : Spin n) :
    4 * totalVariation ((transition (0 : Disorder n) ^ k) x) (mass 0 0) ^ 2 ≤
      Real.exp ((n : ℝ) * Real.exp (-2 * k / n)) - 1 := by
  have hc := FiniteLaw.totalVariation_square ((transition (0 : Disorder n) ^ k) x) (mass 0 0)
  have hcard : (Fintype.card (Spin n) : ℝ) = (2 : ℝ) ^ n := by simp [Spin]
  rw [hcard, row_centered_square hn k x] at hc
  exact hc.trans (sub_le_sub_right (sum_eigenvalue_bound hn k) 1)

theorem distance_upper (hn : 0 < n) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : Real.exp ((n : ℝ) * Real.exp (-2 * k / n)) - 1 ≤ 4 * ε ^ 2) :
    discreteDistance (0 : Disorder n) k ≤ ε := by
  apply Finset.sup'_le
  intro x _
  have htv := row_tv_square_upper hn k x
  nlinarith only [htv, hbound, hε,
    totalVariation_nonneg ((transition (0 : Disorder n) ^ k) x) (mass 0 0)]

def flipEquiv (i : Fin n) : Spin n ≃ Spin n where
  toFun := flip i
  invFun := flip i
  left_inv := flip_flip i
  right_inv := flip_flip i

theorem mean_character (S : Finset (Fin n)) (hS : S.Nonempty) :
    FiniteLaw.mean (mass (0 : Disorder n) 0) (character S) = 0 := by
  obtain ⟨i, hi⟩ := hS
  have hs := Equiv.sum_comp (flipEquiv i) (character S)
  change (∑ x : Spin n, character S (flip i x)) = ∑ x : Spin n, character S x at hs
  simp only [character_flip, ite_eq_left hi, Finset.sum_neg_distrib] at hs
  have hz : (∑ x : Spin n, character S x) = 0 := by linarith
  simp only [FiniteLaw.mean, mass_zero, ← Finset.mul_sum, hz, mul_zero]

@[simp] theorem character_singleton (i : Fin n) (x : Spin n) :
    character {i} x = spinValue (x i) := by simp [character]

theorem character_pair (i j : Fin n) (hij : i ≠ j) (x : Spin n) :
    character {i, j} x = spinValue (x i) * spinValue (x j) := by
  simp [character, hij]

def magnetization (x : Spin n) : ℝ := ∑ i, spinValue (x i)

theorem row_mean_spin (hn : 0 < n) (k : ℕ) (i : Fin n) :
    FiniteLaw.mean ((transition (0 : Disorder n) ^ k) (fun _ => true))
      (fun x => spinValue (x i)) = (1 - 1 / (n : ℝ)) ^ k := by
  simpa [FiniteLaw.mean, eigenvalue] using power_character hn k (fun _ => true) {i}

theorem row_mean_pair (hn : 0 < n) (k : ℕ) (i j : Fin n) (hij : i ≠ j) :
    FiniteLaw.mean ((transition (0 : Disorder n) ^ k) (fun _ => true))
      (fun x => spinValue (x i) * spinValue (x j)) = (1 - 2 / (n : ℝ)) ^ k := by
  simpa [FiniteLaw.mean, character_pair i j hij, eigenvalue, hij, spinValue] using
    power_character hn k (fun _ => true) {i, j}

theorem equilibrium_mean_spin (i : Fin n) :
    FiniteLaw.mean (mass (0 : Disorder n) 0) (fun x => spinValue (x i)) = 0 := by
  simpa only [FiniteLaw.mean, character_singleton] using mean_character {i} (Finset.singleton_nonempty i)

theorem equilibrium_mean_pair (i j : Fin n) (hij : i ≠ j) :
    FiniteLaw.mean (mass (0 : Disorder n) 0)
      (fun x => spinValue (x i) * spinValue (x j)) = 0 := by
  simpa only [FiniteLaw.mean, character_pair i j hij] using mean_character {i, j} (by simp)

theorem row_mean_magnetization (hn : 0 < n) (k : ℕ) :
    FiniteLaw.mean ((transition (0 : Disorder n) ^ k) (fun _ => true)) magnetization =
      (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k := by
  simp only [FiniteLaw.mean, magnetization, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ i : Fin n, FiniteLaw.mean ((transition (0 : Disorder n) ^ k) (fun _ => true))
    (fun x => spinValue (x i))) = _
  simp only [row_mean_spin hn, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

theorem equilibrium_mean_magnetization :
    FiniteLaw.mean (mass (0 : Disorder n) 0) magnetization = 0 := by
  simp only [FiniteLaw.mean, magnetization, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ i : Fin n, FiniteLaw.mean (mass (0 : Disorder n) 0)
    (fun x => spinValue (x i))) = _
  simp only [equilibrium_mean_spin, Finset.sum_const_zero]

theorem eigenvalue_two_le_square (hn : 2 ≤ n) (k : ℕ) :
    (1 - 2 / (n : ℝ)) ^ k ≤ ((1 - 1 / (n : ℝ)) ^ k) ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h0 : 0 ≤ 1 - 2 / (n : ℝ) := by
    exact sub_nonneg.mpr ((div_le_one hnpos).mpr hnR)
  have hb : 1 - 2 / (n : ℝ) ≤ (1 - 1 / (n : ℝ)) ^ 2 := by
    rw [show (2 : ℝ) / n = 2 * (1 / (n : ℝ)) from by ring]
    nlinarith [sq_nonneg (1 / (n : ℝ))]
  simpa only [← pow_mul, mul_comm 2 k] using pow_le_pow_left₀ h0 hb k

theorem row_variance_magnetization (hn : 2 ≤ n) (k : ℕ) :
    FiniteLaw.variance ((transition (0 : Disorder n) ^ k) (fun _ => true)) magnetization ≤ n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  let p := (transition (0 : Disorder n) ^ k) (fun _ => true)
  let r := (1 - 1 / (n : ℝ)) ^ k
  have hp1 : ∑ x, p x = 1 :=
    Matrix.sum_row_of_mem_rowStochastic (transition_pow_stochastic (0 : Disorder n) k) _
  have hpij (i j : Fin n) :
      FiniteLaw.mean p (fun x => spinValue (x i) * spinValue (x j)) ≤
        (if j = i then 1 else 0) + r ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp only [← sq, spinValue_sq, FiniteLaw.mean, mul_one, hp1, ↓reduceIte]
      linarith [sq_nonneg r]
    · rw [ite_eq_right (Ne.symm hij)]
      exact (row_mean_pair hnpos k i j hij).le.trans (by
        simpa only [zero_add] using eigenvalue_two_le_square hn k)
  have hexpand : FiniteLaw.mean p (fun x => magnetization x ^ 2) =
      ∑ i, ∑ j, FiniteLaw.mean p (fun x => spinValue (x i) * spinValue (x j)) := by
    simp only [FiniteLaw.mean, magnetization, sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsecond : FiniteLaw.mean p (fun x => magnetization x ^ 2) ≤ n + n ^ 2 * r ^ 2 := by
    rw [hexpand]
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ((if j = i then (1 : ℝ) else 0) + r ^ 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpij i j))
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
  rw [FiniteLaw.variance_eq p _ hp1, row_mean_magnetization hnpos]
  dsimp only [r] at hsecond
  nlinarith only [hsecond]

theorem equilibrium_variance_magnetization :
    FiniteLaw.variance (mass (0 : Disorder n) 0) magnetization = n := by
  have hpij (i j : Fin n) :
      FiniteLaw.mean (mass (0 : Disorder n) 0)
        (fun x => spinValue (x i) * spinValue (x j)) = if j = i then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [← sq, spinValue_sq, FiniteLaw.mean, mul_one, sum_mass, ↓reduceIte]
    · rw [ite_eq_right (Ne.symm hij)]
      exact equilibrium_mean_pair i j hij
  have hexpand : FiniteLaw.mean (mass (0 : Disorder n) 0) (fun x => magnetization x ^ 2) =
      ∑ i, ∑ j, FiniteLaw.mean (mass (0 : Disorder n) 0)
        (fun x => spinValue (x i) * spinValue (x j)) := by
    simp only [FiniteLaw.mean, magnetization, sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [FiniteLaw.variance_eq _ _ (sum_mass _ _), equilibrium_mean_magnetization, hexpand]
  simp only [hpij, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, zero_pow (by decide : 2 ≠ 0), sub_zero]

end Independent
end SKRatio
end
end
end

end OAI
