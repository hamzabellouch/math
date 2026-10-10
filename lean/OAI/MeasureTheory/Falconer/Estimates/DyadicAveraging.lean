import OAI.MeasureTheory.Falconer.Estimates.DyadicSlopeVariance

namespace OAI

/-! Finite dyadic averaging and the energy increment identity. -/
namespace Falconer

noncomputable def dyadicAverage (g : ℝ → ℝ → ℝ) (a h : ℝ) : ℕ → ℝ
  | 0 => g a h
  | n+1 => (dyadicAverage g a (h/2) n+dyadicAverage g (a+h/2) (h/2) n)/2

theorem dyadicAverage_nonneg {g : ℝ → ℝ → ℝ} (hg : ∀ a h, 0 ≤ g a h)
    (a h : ℝ) (n : ℕ) : 0 ≤ dyadicAverage g a h n := by
  induction n generalizing a h with
  | zero => exact hg a h
  | succ n ih => exact div_nonneg (add_nonneg (ih _ _) (ih _ _)) (by norm_num)

theorem dyadicAverage_mono {g k : ℝ → ℝ → ℝ} (hg : ∀ a h, g a h ≤ k a h)
    (a h : ℝ) (n : ℕ) : dyadicAverage g a h n ≤ dyadicAverage k a h n := by
  induction n generalizing a h with
  | zero => exact hg a h
  | succ n ih => exact div_le_div_of_nonneg_right (add_le_add (ih _ _) (ih _ _)) (by norm_num)

@[simp] theorem dyadicAverage_const (c a h : ℝ) (n : ℕ) :
    dyadicAverage (fun _ _ => c) a h n = c := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicAverage,ih]; ring

theorem dyadicAverage_add (g k : ℝ → ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    dyadicAverage (fun a h => g a h+k a h) a h n =
      dyadicAverage g a h n+dyadicAverage k a h n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicAverage,ih]; ring

theorem dyadicAverage_sub (g k : ℝ → ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    dyadicAverage (fun a h => g a h-k a h) a h n =
      dyadicAverage g a h n-dyadicAverage k a h n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicAverage,ih]; ring

theorem dyadicAverage_mul (c : ℝ) (g : ℝ → ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    dyadicAverage (fun a h => c*g a h) a h n = c*dyadicAverage g a h n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicAverage,ih]; ring

theorem dyadicAverage_comp (g : ℝ → ℝ → ℝ) (a h : ℝ) (n m : ℕ) :
    dyadicAverage (fun a h => dyadicAverage g a h m) a h n =
      dyadicAverage g a h (n+m) := by
  induction n generalizing a h with
  | zero => simp only [dyadicAverage,Nat.zero_add]
  | succ n ih => simp only [dyadicAverage,ih,Nat.succ_add]

theorem dyadicSlopeEnergy_eq_average (f : ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    dyadicSlopeEnergy f a h n =
      dyadicAverage (fun a h => (intervalSecantSlope f a h)^2) a h n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicSlopeEnergy,dyadicAverage,ih]

theorem dyadicSlopeVariance_eq_average (f : ℝ → ℝ) (a h c : ℝ) (n : ℕ) :
    dyadicSlopeVariance f a h c n =
      dyadicAverage (fun a h => (intervalSecantSlope f a h-c)^2) a h n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicSlopeVariance,dyadicAverage,ih]

theorem dyadicAverage_centered_variance (f : ℝ → ℝ) (a : ℝ) {h : ℝ}
    (hh : 0 < h) (n m : ℕ) :
    dyadicAverage (fun a h => dyadicSlopeVariance f a h (intervalSecantSlope f a h) m) a h n =
      dyadicSlopeEnergy f a h (n+m)-dyadicSlopeEnergy f a h n := by
  induction n generalizing a h with
  | zero => simpa only [dyadicAverage,Nat.zero_add] using dyadicSlopeVariance_centered f a hh m
  | succ n ih =>
    rw [dyadicAverage,ih a (half_pos hh),ih (a+h/2) (half_pos hh),Nat.succ_add]
    simp only [dyadicSlopeEnergy]
    ring

theorem dyadicAverage_markov {g : ℝ → ℝ → ℝ} (hg : ∀ a h, 0 ≤ g a h)
    (a h θ : ℝ) (n : ℕ) :
    θ*dyadicAverage (fun a h => if θ < g a h then 1 else 0) a h n ≤
      dyadicAverage g a h n := by
  classical
  rw [← dyadicAverage_mul]
  apply dyadicAverage_mono
  intro a h
  split_ifs with ht
  · simpa only [mul_one] using ht.le
  · simpa only [mul_zero] using hg a h

end Falconer

end OAI
