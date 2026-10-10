import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.W34

def theta {K : Type*} [Ring K] (a b : K) (n : Fin 4 → ℕ) : K :=
  (n 0 : K) + (n 1 : K) * a + (n 2 : K) * b + (n 3 : K) * (a * b)

theorem norm_root_int_le_sqrt (a : ℂ) (d : ℤ) (q : ℝ)
    (ha : a ^ 2 = (d : ℂ)) (hq : 0 ≤ q) (hd : |(d : ℝ)| ≤ q) :
    ‖a‖ ≤ Real.sqrt q := by
  have hs : ‖a‖ ^ 2 ≤ q := by
    calc
      ‖a‖ ^ 2 = ‖a ^ 2‖ := (Complex.norm_pow a 2).symm
      _ = |(d : ℝ)| := by rw [ha, Complex.norm_intCast]
      _ ≤ q := hd
  have hr := Real.sq_sqrt hq
  have hp := Real.sqrt_nonneg q
  nlinarith [norm_nonneg a]

theorem norm_root_two_le_two (b : ℂ) (hb : b ^ 2 = 2) : ‖b‖ ≤ 2 := by
  have hs : ‖b‖ ^ 2 = 2 := by
    calc
      ‖b‖ ^ 2 = ‖b ^ 2‖ := (Complex.norm_pow b 2).symm
      _ = 2 := by rw [hb]; norm_num
  nlinarith [norm_nonneg b]

theorem theta_norm_bound (a b : ℂ) (n : Fin 4 → ℕ) (N : ℕ) (s : ℝ)
    (hn : ∀ i, n i ≤ N) (hs : 1 ≤ s) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ 2) :
    ‖theta a b n‖ ≤ 8 * (N : ℝ) * s := by
  have hn' (i : Fin 4) : (n i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn i
  have hab : ‖a * b‖ ≤ 2 * s := by
    rw [Complex.norm_mul]
    calc
      ‖a‖ * ‖b‖ ≤ s * 2 := mul_le_mul ha hb (norm_nonneg b) (by linarith)
      _ = 2 * s := by ring
  have ht : ‖theta a b n‖ ≤
      (n 0 : ℝ) + (n 1 : ℝ) * ‖a‖ + (n 2 : ℝ) * ‖b‖ +
        (n 3 : ℝ) * ‖a * b‖ := by
    unfold theta
    calc
      _ ≤ ‖(n 0 : ℂ) + (n 1 : ℂ) * a + (n 2 : ℂ) * b‖ +
          ‖(n 3 : ℂ) * (a * b)‖ := norm_add_le _ _
      _ ≤ (‖(n 0 : ℂ) + (n 1 : ℂ) * a‖ + ‖(n 2 : ℂ) * b‖) +
          ‖(n 3 : ℂ) * (a * b)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖(n 0 : ℂ)‖ + ‖(n 1 : ℂ) * a‖) + ‖(n 2 : ℂ) * b‖) +
          ‖(n 3 : ℂ) * (a * b)‖ :=
        add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
      _ = _ := by simp only [Complex.norm_mul, Complex.norm_natCast]
  calc
    ‖theta a b n‖ ≤ (n 0 : ℝ) + (n 1 : ℝ) * ‖a‖ +
        (n 2 : ℝ) * ‖b‖ + (n 3 : ℝ) * ‖a * b‖ := ht
    _ ≤ (N : ℝ) + (N : ℝ) * s + (N : ℝ) * 2 + (N : ℝ) * (2 * s) := by
      exact add_le_add
        (add_le_add
          (add_le_add (hn' 0) (mul_le_mul (hn' 1) ha (norm_nonneg a) (Nat.cast_nonneg N)))
          (mul_le_mul (hn' 2) hb (norm_nonneg b) (Nat.cast_nonneg N)))
        (mul_le_mul (hn' 3) hab (norm_nonneg (a * b)) (Nat.cast_nonneg N))
    _ ≤ 8 * (N : ℝ) * s := by
      have hp := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sub_nonneg.mpr hs)
      nlinarith

theorem embedding_theta_bound {K : Type*} [Ring K] (ν : K →+* ℂ)
    (a b : K) (d : ℤ) (q N : ℕ) (n : Fin 4 → ℕ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hq : 1 ≤ q) (hd : |(d : ℝ)| ≤ (q : ℝ)) (hn : ∀ i, n i ≤ N) :
    ‖ν (theta a b n)‖ ≤ 8 * (N : ℝ) * Real.sqrt (q : ℝ) := by
  have ha' : ν a ^ 2 = (d : ℂ) := by rw [← map_pow, ha, map_intCast]
  have hb' : ν b ^ 2 = 2 := by rw [← map_pow, hb, map_ofNat]
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : 1 ≤ Real.sqrt (q : ℝ) := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    have hnonneg := Real.sqrt_nonneg (q : ℝ)
    nlinarith
  have h := theta_norm_bound (ν a) (ν b) n N (Real.sqrt (q : ℝ)) hn hs
    (norm_root_int_le_sqrt (ν a) d (q : ℝ) ha' (Nat.cast_nonneg q) hd)
    (norm_root_two_le_two (ν b) hb')
  simpa only [theta, map_add, map_mul, map_natCast] using h

end WeightedTorusJets.W34


end SiegelZeros

end OAI
