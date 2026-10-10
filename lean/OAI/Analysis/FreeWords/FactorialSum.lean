import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

noncomputable section

open scoped BigOperators

theorem choose_mono_small {m a b : ℕ} (hab : a ≤ b) (hb : b ≤ m / 2) :
    m.choose a ≤ m.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem choose_two_le {m p : ℕ} (hp : 2 ≤ p) (hpm : p + 2 ≤ m) :
    m.choose 2 ≤ m.choose p := by
  by_cases h : p ≤ m / 2
  · exact choose_mono_small hp h
  · rw [← Nat.choose_symm (show p ≤ m by omega)]
    exact choose_mono_small (by omega) (by omega)

theorem factorial_product_middle {m p : ℕ} (hp : 2 ≤ p) (hpm : p + 2 ≤ m) :
    p.factorial * (m-p).factorial ≤ 2 * (m-2).factorial := by
  have hc := choose_two_le hp hpm
  have hp' := Nat.choose_mul_factorial_mul_factorial (show p ≤ m by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show 2 ≤ m by omega)
  have hpos := Nat.choose_pos (show 2 ≤ m by omega)
  norm_num only [Nat.factorial_two] at h2
  nlinarith [Nat.mul_le_mul_right (p.factorial * (m-p).factorial) hc]

def factorialRoot (m p : ℕ) : ℝ := Real.sqrt ((p.factorial : ℝ) * (m-p).factorial)

theorem factorialRoot_middle {m p : ℕ} (hp : 2 ≤ p) (hpm : p + 2 ≤ m) :
    factorialRoot m p ≤ Real.sqrt (2 * ((m-2).factorial : ℝ)) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast factorial_product_middle hp hpm

theorem factorialRoot_sum_small (m : ℕ) (hm : m ≤ 3) :
    (∑ p ∈ Finset.range (m+1), factorialRoot m p) ≤ 5 * Real.sqrt (m.factorial : ℝ) := by
  interval_cases m <;>
    norm_num [factorialRoot, Finset.sum_range_succ, Real.sqrt_mul] <;>
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg 6, Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)]

theorem sum_range_four_ends {R : Type*} [AddCommMonoid R] (f : ℕ → R) (k : ℕ) :
    (∑ p ∈ Finset.range (k+5), f p) =
      f 0 + f 1 + (∑ i ∈ Finset.range (k+1), f (i+2)) + f (k+3) + f (k+4) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show k+3 = 2+(k+1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.add_comm 2]

theorem factorialRoot_sum (m : ℕ) :
    (∑ p ∈ Finset.range (m+1), factorialRoot m p) ≤ 5 * Real.sqrt (m.factorial : ℝ) := by
  by_cases hm : m ≤ 3
  · exact factorialRoot_sum_small m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k+4 := ⟨m-4, by omega⟩
  let A : ℝ := Real.sqrt ((k+4).factorial : ℝ)
  let B : ℝ := Real.sqrt ((k+3).factorial : ℝ)
  let C : ℝ := Real.sqrt (2 * ((k+2).factorial : ℝ))
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hAsq : A^2 = ((k+4).factorial : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hBsq : B^2 = ((k+3).factorial : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hCsq : C^2 = 2 * ((k+2).factorial : ℝ) := Real.sq_sqrt (by positivity)
  have hfac : ((k+4).factorial : ℝ) = (k+4) * ((k+3).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ (k+3)
  have hfac' : ((k+3).factorial : ℝ) = (k+3) * ((k+2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ (k+2)
  have hBA : 2 * B ≤ A := by
    apply (sq_le_sq₀ (by positivity) hA).mp
    nlinarith [Nat.cast_nonneg (α := ℝ) k, sq_nonneg B]
  have hCA : (k+1 : ℝ) * C ≤ 2 * A := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, hAsq, hCsq, hfac, hfac']
    nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) (k+2).factorial,
      mul_nonneg (sq_nonneg (k:ℝ)) (Nat.cast_nonneg (α := ℝ) (k+2).factorial),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) (k+2).factorial)]
  have hmid : (∑ i ∈ Finset.range (k+1), factorialRoot (k+4) (i+2)) ≤ (k+1:ℝ) * C := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k+1), C := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := factorialRoot_middle (m := k+4) (p := i+2) (by omega)
          (by have := Finset.mem_range.mp hi; omega)
        simpa only [show k+4-2=k+2 by omega] using hh
      _ = _ := by simp
  rw [sum_range_four_ends]
  have hends : factorialRoot (k+4) 0 = A ∧ factorialRoot (k+4) 1 = B ∧
      factorialRoot (k+4) (k+3) = B ∧ factorialRoot (k+4) (k+4) = A := by
    simp [factorialRoot, A, B, show k+4-1=k+3 by omega,
      show k+4-(k+3)=1 by omega]
  rw [hends.1, hends.2.1, hends.2.2.1, hends.2.2.2]
  change A + B + _ + B + A ≤ 5*A
  linarith

end

end KKFreeWords
end

end OAI
