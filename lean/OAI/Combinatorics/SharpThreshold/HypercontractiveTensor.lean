import Mathlib

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Weighted Cauchy--Schwarz in a form useful for finite product measures. -/
theorem weighted_cauchy_schwarz_sq {α : Type u} (s : Finset α)
    (w u v : α → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) :
    (∑ x ∈ s, w x * u x * v x) ^ 2 ≤
      (∑ x ∈ s, w x * (u x) ^ 2) * (∑ x ∈ s, w x * (v x) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro x hx
    exact mul_nonneg (hw x hx) (sq_nonneg _)
  · intro x hx
    exact mul_nonneg (hw x hx) (sq_nonneg _)
  · intro x hx
    exact le_of_eq (by ring)

/-- The root-free Minkowski step in tensorization of the fourth moment. -/
theorem weighted_fourth_moment_add_sq {α : Type u} (s : Finset α)
    (w A B : α → ℝ) (a b : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : (∑ x ∈ s, w x * (A x) ^ 4) ≤ a ^ 2)
    (hB : (∑ x ∈ s, w x * (B x) ^ 4) ≤ b ^ 2) :
    (∑ x ∈ s, w x * ((A x) ^ 2 + (B x) ^ 2) ^ 2) ≤ (a + b) ^ 2 := by
  have hcs := weighted_cauchy_schwarz_sq s w (fun x => (A x) ^ 2)
    (fun x => (B x) ^ 2) hw
  have hA0 : 0 ≤ ∑ x ∈ s, w x * (A x) ^ 4 :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (by positivity))
  have hB0 : 0 ≤ ∑ x ∈ s, w x * (B x) ^ 4 :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx) (by positivity))
  have hprod := mul_le_mul hA hB hB0 (sq_nonneg a)
  have hpow : ∀ x : ℝ, (x ^ 2) ^ 2 = x ^ 4 := fun x => by ring
  simp_rw [hpow] at hcs
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hcross : (∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) ≤ a * b := by
    nlinarith [sq_nonneg ((∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) - a * b)]
  have hexpand : (∑ x ∈ s, w x * ((A x) ^ 2 + (B x) ^ 2) ^ 2) =
      (∑ x ∈ s, w x * (A x) ^ 4) +
      2 * (∑ x ∈ s, w x * (A x) ^ 2 * (B x) ^ 2) +
      (∑ x ∈ s, w x * (B x) ^ 4) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hexpand]
  nlinarith

/-- A version of the fourth-moment Minkowski step with two nonnegative coefficients. -/
theorem weighted_fourth_moment_combo {α : Type u} (s : Finset α)
    (w A B : α → ℝ) (a b c d : ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : (∑ x ∈ s, w x * (A x) ^ 4) ≤ a ^ 2)
    (hB : (∑ x ∈ s, w x * (B x) ^ 4) ≤ b ^ 2) :
    (∑ x ∈ s, w x * (c * (A x) ^ 2 + d * (B x) ^ 2) ^ 2) ≤
      (c * a + d * b) ^ 2 := by
  have hA' : (∑ x ∈ s, w x * (Real.sqrt c * A x) ^ 4) ≤ (c * a) ^ 2 := by
    calc
      _ = c ^ 2 * (∑ x ∈ s, w x * (A x) ^ 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_pow, show Real.sqrt c ^ 4 = c ^ 2 by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hc]]
        ring
      _ ≤ c ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left hA (sq_nonneg c)
      _ = _ := by ring
  have hB' : (∑ x ∈ s, w x * (Real.sqrt d * B x) ^ 4) ≤ (d * b) ^ 2 := by
    calc
      _ = d ^ 2 * (∑ x ∈ s, w x * (B x) ^ 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [mul_pow, show Real.sqrt d ^ 4 = d ^ 2 by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hd]]
        ring
      _ ≤ d ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_left hB (sq_nonneg d)
      _ = _ := by ring
  have h := weighted_fourth_moment_add_sq s w
    (fun x => Real.sqrt c * A x) (fun x => Real.sqrt d * B x)
    (c * a) (d * b) hw (mul_nonneg hc ha) (mul_nonneg hd hb) hA' hB'
  simpa only [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hd] using h

/-- A fourth-moment contraction tensorizes with a two-point contraction.
No linearity assumptions are needed for this analytic step. -/
theorem fourth_moment_tensor_bool {α : Type u} [Fintype α]
    (w : α → ℝ) (q : Bool → ℝ)
    (T : (α → ℝ) → α → ℝ) (S : (Bool → ℝ) → Bool → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hq : ∀ b, 0 ≤ q b)
    (hT : ∀ g, (∑ x, w x * (T g x) ^ 4) ≤ (∑ x, w x * (g x) ^ 2) ^ 2)
    (hS : ∀ g, (∑ b, q b * (S g b) ^ 4) ≤ (∑ b, q b * (g b) ^ 2) ^ 2)
    (g : Bool → α → ℝ) :
    (∑ x, ∑ b, w x * q b * (S (fun c => T (g c) x) b) ^ 4) ≤
      (∑ b, ∑ x, q b * w x * (g b x) ^ 2) ^ 2 := by
  classical
  have ha : 0 ≤ ∑ x, w x * (g false x) ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  have hb : 0 ≤ ∑ x, w x * (g true x) ^ 2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  calc
    _ = ∑ x, w x * (∑ b, q b * (S (fun c => T (g c) x) b) ^ 4) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ x, w x * (∑ b, q b * (T (g b) x) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hS _) (hw x)
    _ = ∑ x, w x * (q false * (T (g false) x) ^ 2 +
        q true * (T (g true) x) ^ 2) ^ 2 := by
      simp only [Fintype.sum_bool, add_comm]
    _ ≤ (q false * (∑ x, w x * (g false x) ^ 2) +
        q true * (∑ x, w x * (g true x) ^ 2)) ^ 2 :=
      weighted_fourth_moment_combo Finset.univ w (T (g false)) (T (g true))
        _ _ (q false) (q true) (fun x _ => hw x) ha hb (hq false) (hq true)
        (hT _) (hT _)
    _ = _ := by
      simp only [Fintype.sum_bool, Finset.mul_sum]
      congr 1
      ring_nf

end Problem313

end

end OAI
