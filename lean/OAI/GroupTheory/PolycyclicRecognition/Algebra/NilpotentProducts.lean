import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Polynomial bounds for products with nilpotent increments

The finite-degree product estimate in the nilpotent-coordinate argument is
proved here in a normed associative algebra. The factors need not commute.
Homogeneous terms are sums over ordered sublists, so nilpotence truncates the
expansion before a fixed degree, independently of the number of factors.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Ring

variable {A : Type*} [Ring A]

/-- The degree-`k` part of an ordered product of `1 + x`. -/
def homogeneousProduct (l : List A) (k : ℕ) : A :=
  ((l.sublistsLen k).map List.prod).sum

@[simp] theorem homogeneousProduct_zero (l : List A) : homogeneousProduct l 0 = 1 := by
  simp [homogeneousProduct]

@[simp] theorem homogeneousProduct_nil_succ (k : ℕ) :
    homogeneousProduct ([] : List A) (k + 1) = 0 := by
  simp [homogeneousProduct]

theorem homogeneousProduct_cons_succ (x : A) (l : List A) (k : ℕ) :
    homogeneousProduct (x :: l) (k + 1) =
      homogeneousProduct l (k + 1) + x * homogeneousProduct l k := by
  simp only [homogeneousProduct, List.sublistsLen_succ_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, List.prod_cons]
  rw [List.sum_map_mul_left]

theorem homogeneousProduct_eq_zero_of_length_lt (l : List A) {k : ℕ}
    (hk : l.length < k) : homogeneousProduct l k = 0 := by
  simp [homogeneousProduct, List.sublistsLen_of_length_lt hk]

/-- Exact ordered expansion; no commutativity hypothesis is used. -/
theorem prod_one_add_eq_sum_homogeneous (l : List A) :
    (l.map (fun x => 1 + x)).prod =
      ∑ k ∈ Finset.range (l.length + 1), homogeneousProduct l k := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hz : homogeneousProduct l (l.length + 1) = 0 :=
      homogeneousProduct_eq_zero_of_length_lt l (Nat.lt_succ_self _)
    calc
      ((x :: l).map (fun x => 1 + x)).prod =
          (1 + x) * ∑ k ∈ Finset.range (l.length + 1), homogeneousProduct l k := by
        simp only [List.map_cons, List.prod_cons, ih]
      _ = (∑ k ∈ Finset.range (l.length + 2), homogeneousProduct l k) +
          x * ∑ k ∈ Finset.range (l.length + 1), homogeneousProduct l k := by
        rw [Finset.sum_range_succ (f := homogeneousProduct l) (n := l.length + 1),
          hz, add_zero, add_mul, one_mul]
      _ = ∑ k ∈ Finset.range ((x :: l).length + 1),
          homogeneousProduct (x :: l) k := by
        simp only [List.length_cons]
        rw [Finset.sum_range_succ' (f := homogeneousProduct l) (n := l.length + 1),
          Finset.sum_range_succ' (f := homogeneousProduct (x :: l)) (n := l.length + 1)]
        simp only [homogeneousProduct_zero, homogeneousProduct_cons_succ,
          Finset.sum_add_distrib, Finset.mul_sum]
        abel

/-- Nilpotence kills every homogeneous term of sufficiently high degree. -/
theorem homogeneousProduct_eq_zero_of_nilpotence (S : Set A) (c : ℕ)
    (hnil : ∀ l : List A, (∀ x ∈ l, x ∈ S) → c ≤ l.length → l.prod = 0)
    (l : List A) (hl : ∀ x ∈ l, x ∈ S) {k : ℕ} (hk : c ≤ k) :
    homogeneousProduct l k = 0 := by
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hsl, hlen⟩ := List.mem_sublistsLen.mp hs
  exact hnil s (fun x hx => hl x (hsl.subset hx)) (hlen ▸ hk)

/-- Truncating at the nilpotence degree is exact even for arbitrarily many
factors. -/
theorem prod_one_add_eq_truncated (S : Set A) (c : ℕ)
    (hnil : ∀ l : List A, (∀ x ∈ l, x ∈ S) → c ≤ l.length → l.prod = 0)
    (l : List A) (hl : ∀ x ∈ l, x ∈ S) :
    (l.map (fun x => 1 + x)).prod =
      ∑ k ∈ Finset.range c, homogeneousProduct l k := by
  rw [prod_one_add_eq_sum_homogeneous]
  rcases le_total (l.length + 1) c with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro k _ hk
    exact homogeneousProduct_eq_zero_of_length_lt l (by simpa using hk)
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro k _ hk
    exact homogeneousProduct_eq_zero_of_nilpotence S c hnil l hl (by simpa using hk)

end Ring

section Normed

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Each homogeneous term has the binomial bound expected from its ordered
sublist expansion. -/
theorem norm_homogeneousProduct_le (l : List A) {M : ℝ} (hM : 0 ≤ M)
    (hl : ∀ x ∈ l, ‖x‖ ≤ M) (k : ℕ) :
    ‖homogeneousProduct l k‖ ≤ (l.length.choose k : ℝ) * M ^ k := by
  induction l generalizing k with
  | nil => cases k <;> simp
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hx : ‖x‖ ≤ M := hl x (by simp)
      have htail : ∀ y ∈ l, ‖y‖ ≤ M := fun y hy => hl y (by simp [hy])
      rw [homogeneousProduct_cons_succ]
      calc
        _ ≤ ‖homogeneousProduct l (k + 1)‖ + ‖x * homogeneousProduct l k‖ := norm_add_le _ _
        _ ≤ (l.length.choose (k + 1) : ℝ) * M ^ (k + 1) +
            M * ((l.length.choose k : ℝ) * M ^ k) := by
          apply add_le_add (ih htail (k + 1))
          exact (norm_mul_le _ _).trans
            (mul_le_mul hx (ih htail k) (norm_nonneg _) hM)
        _ = ((x :: l).length.choose (k + 1) : ℝ) * M ^ (k + 1) := by
          simp only [List.length_cons, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
          ring

/-- Fixed nilpotence degree turns the ordered product expansion into a
polynomial bound in the number of factors. -/
theorem norm_prod_one_add_le_polynomial (S : Set A) (c : ℕ)
    (hnil : ∀ l : List A, (∀ x ∈ l, x ∈ S) → c ≤ l.length → l.prod = 0)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x ∈ S, ‖x‖ ≤ M)
    (l : List A) (hl : ∀ x ∈ l, x ∈ S) :
    ‖(l.map (fun x => 1 + x)).prod‖ ≤
      (c : ℝ) * (1 + M) ^ c * (1 + (l.length : ℝ)) ^ c := by
  rw [prod_one_add_eq_truncated S c hnil l hl]
  calc
    _ ≤ ∑ k ∈ Finset.range c, ‖homogeneousProduct l k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range c, (l.length.choose k : ℝ) * M ^ k := by
      apply Finset.sum_le_sum
      intro k _
      exact norm_homogeneousProduct_le l hM (fun x hx => hbound x (hl x hx)) k
    _ ≤ ∑ _k ∈ Finset.range c, ((1 + (l.length : ℝ)) * (1 + M)) ^ c := by
      apply Finset.sum_le_sum
      intro k hk
      have hc : k ≤ c := (Finset.mem_range.mp hk).le
      have hn : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
      have hbase : 1 ≤ (1 + (l.length : ℝ)) * (1 + M) := by
        nlinarith [mul_nonneg hn hM]
      calc
        (l.length.choose k : ℝ) * M ^ k ≤ (l.length : ℝ) ^ k * M ^ k := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM _)
          exact_mod_cast Nat.choose_le_pow l.length k
        _ = ((l.length : ℝ) * M) ^ k := (mul_pow _ _ _).symm
        _ ≤ ((1 + (l.length : ℝ)) * (1 + M)) ^ k := by
          apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hM)
          nlinarith
        _ ≤ ((1 + (l.length : ℝ)) * (1 + M)) ^ c := pow_le_pow_right₀ hbase hc
    _ = (c : ℝ) * (1 + M) ^ c * (1 + (l.length : ℝ)) ^ c := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow]
      ring

/-- The inverse of a nilpotent perturbation of one is a finite geometric sum,
with a bound that is polynomial in the perturbation norm. -/
theorem norm_inv_le_of_nilpotent_sub_one (u : Aˣ) (c : ℕ)
    (hn : (1 - (u : A)) ^ c = 0) :
    ‖(↑u⁻¹ : A)‖ ≤ (c : ℝ) * (1 + ‖1 - (u : A)‖) ^ c := by
  have hsum : (∑ k ∈ Finset.range c, (1 - (u : A)) ^ k) * (u : A) = 1 := by
    simpa only [sub_sub_cancel, hn, sub_zero] using geom_sum_mul_neg (1 - (u : A)) c
  rw [u.inv_eq_of_mul_eq_one_left hsum]
  calc
    _ ≤ ∑ k ∈ Finset.range c, ‖(1 - (u : A)) ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range c, (1 + ‖1 - (u : A)‖) ^ c := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ‖1 - (u : A)‖ ^ k := norm_pow_le _ _
        _ ≤ (1 + ‖1 - (u : A)‖) ^ k := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          linarith [norm_nonneg (1 - (u : A))]
        _ ≤ (1 + ‖1 - (u : A)‖) ^ c :=
          pow_le_pow_right₀ (by linarith [norm_nonneg (1 - (u : A))])
            (Finset.mem_range.mp hk).le
    _ = _ := by simp

end Normed

end PolycyclicRecognition

end OAI
