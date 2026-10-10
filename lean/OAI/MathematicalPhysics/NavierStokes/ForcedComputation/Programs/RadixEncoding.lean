import Mathlib

namespace OAI

/-!
# Infinite tape tails and their radix coordinates

Unlike finite prefix interval arithmetic, these lemmas connect the actual
infinite symbolic tail to a real point of its coding interval.
-/

noncomputable section

namespace ForcedComputation.Radix

variable {A : Type*}

def encode (B : ℝ) (digit : A → ℝ) (u : ℕ → A) : ℝ :=
  ∑' n : ℕ, digit (u n) * B⁻¹ ^ (n + 1)

theorem summable_bound {B : ℝ} (hB : 1 < B) :
    Summable (fun n : ℕ => (B - 1) * B⁻¹ ^ (n + 1)) := by
  have hi : ‖B⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hB
  exact ((summable_geometric_of_norm_lt_one hi).mul_left ((B - 1) * B⁻¹)).congr
    (fun n => by rw [pow_succ]; ring)

theorem summable_digits {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (u : ℕ → A) :
    Summable (fun n : ℕ => digit (u n) * B⁻¹ ^ (n + 1)) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (hd (u n)).1 (by positivity))
    (fun n => mul_le_mul_of_nonneg_right (hd (u n)).2 (by positivity)) (summable_bound hB)

theorem tsum_bound {B : ℝ} (hB : 1 < B) :
    (∑' n : ℕ, (B - 1) * B⁻¹ ^ (n + 1)) = 1 := by
  have hi : ‖B⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hB
  calc
    (∑' n : ℕ, (B - 1) * B⁻¹ ^ (n + 1)) =
        ∑' n : ℕ, ((B - 1) * B⁻¹) * B⁻¹ ^ n := by
      apply tsum_congr
      intro n
      rw [pow_succ]
      ring
    _ = ((B - 1) * B⁻¹) * (1 - B⁻¹)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hi]
    _ = 1 := by
      have hb : B ≠ 0 := by linarith
      have hsub : B - 1 ≠ 0 := by linarith
      field_simp [hb, hsub]

theorem encode_mem_unit {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (u : ℕ → A) :
    encode B digit u ∈ Set.Icc 0 1 := by
  refine ⟨tsum_nonneg (fun n => mul_nonneg (hd (u n)).1 (by positivity)), ?_⟩
  calc
    encode B digit u ≤ ∑' n : ℕ, (B - 1) * B⁻¹ ^ (n + 1) :=
      (summable_digits hB hd u).tsum_le_tsum
        (fun n => mul_le_mul_of_nonneg_right (hd (u n)).2 (by positivity)) (summable_bound hB)
    _ = 1 := tsum_bound hB

theorem encode_shift {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (u : ℕ → A) :
    encode B digit u = (digit (u 0) + encode B digit (fun n => u (n + 1))) / B := by
  unfold encode
  rw [(summable_digits hB hd u).tsum_eq_zero_add]
  have ht : (∑' n : ℕ, digit (u (n + 1)) * B⁻¹ ^ (n + 1 + 1)) =
      B⁻¹ * ∑' n : ℕ, digit (u (n + 1)) * B⁻¹ ^ (n + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_succ]
    ring
  rw [ht]
  simp only [zero_add, pow_one, div_eq_mul_inv]
  ring

def prepend (a : A) (u : ℕ → A) (n : ℕ) : A :=
  Nat.casesOn n a u

theorem encode_prepend {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (a : A) (u : ℕ → A) :
    encode B digit (prepend a u) = (digit a + encode B digit u) / B := by
  exact encode_shift hB hd (prepend a u)

theorem encode_const {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (a : A) :
    encode B digit (fun _ => a) = digit a / (B - 1) := by
  have he := encode_shift hB hd (fun _ => a)
  have hb : B ≠ 0 := by linarith
  have hsub : B - 1 ≠ 0 := by linarith
  apply (eq_div_iff hsub).mpr
  have hh := (eq_div_iff hb).mp he
  nlinarith

def prependWord : List A → (ℕ → A) → ℕ → A
  | [], u => u
  | a :: w, u => prepend a (prependWord w u)

def prefixValue (B : ℝ) (digit : A → ℝ) : List A → ℝ
  | [] => 0
  | a :: w => (digit a + prefixValue B digit w) / B

theorem encode_prependWord {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (w : List A) (u : ℕ → A) :
    encode B digit (prependWord w u) =
      prefixValue B digit w + B⁻¹ ^ w.length * encode B digit u := by
  induction w with
  | nil => simp [prependWord, prefixValue]
  | cons a w ih =>
    rw [prependWord, encode_prepend hB hd, ih, prefixValue, List.length_cons, pow_succ]
    simp only [div_eq_mul_inv]
    ring

/-- A finite input on a blank tail has an explicitly rational radix formula. -/
theorem encode_finite_input {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (w : List A) (blank : A) :
    encode B digit (prependWord w (fun _ => blank)) =
      prefixValue B digit w + B⁻¹ ^ w.length * (digit blank / (B - 1)) := by
  rw [encode_prependWord hB hd, encode_const hB hd]

theorem encode_in_first_cylinder {B : ℝ} {digit : A → ℝ} (hB : 1 < B)
    (hd : ∀ a, 0 ≤ digit a ∧ digit a ≤ B - 1) (u : ℕ → A) :
    encode B digit u ∈ Set.Icc (digit (u 0) / B) ((digit (u 0) + 1) / B) := by
  rw [encode_shift hB hd]
  have ht := encode_mem_unit hB hd (fun n => u (n + 1))
  have hp : 0 < B := by linarith
  constructor
  · exact (div_le_div_iff_of_pos_right hp).mpr (by linarith [ht.1])
  · exact (div_le_div_iff_of_pos_right hp).mpr (by linarith [ht.2])

end ForcedComputation.Radix

end

end OAI
