import Mathlib

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem367
namespace CriticalBranching

def step (b : ℕ) (p q : ℝ) : ℝ := 1 - (1 - p * q) ^ b

def survival (b : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => step b p (survival b p n)

theorem one_sub_pow_quadratic (n : ℕ) {y : ℝ} (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - (1 - y) ^ (n + 1) ≤ (n + 1 : ℕ) * y - (n : ℝ) * y ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnon : 0 ≤ 1 - y := sub_nonneg.mpr hy1
    calc
      1 - (1 - y) ^ (n + 1 + 1) =
          y + (1 - y) * (1 - (1 - y) ^ (n + 1)) := by rw [pow_succ]; ring
      _ ≤ y + (1 - y) * ((n + 1 : ℕ) * y - (n : ℝ) * y ^ 2) := by
        gcongr
      _ ≤ (n + 1 + 1 : ℕ) * y - (n + 1 : ℕ) * y ^ 2 := by
        push_cast
        have h := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          (mul_nonneg (sq_nonneg y) hnon)
        nlinarith

theorem step_mem_Icc (b : ℕ) {p q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : step b p q ∈ Set.Icc (0 : ℝ) 1 := by
  have hy1 : p * q ≤ 1 :=
    (mul_le_mul_of_nonneg_right hp.2 hq.1).trans (by simpa using hq.2)
  have hz0 : 0 ≤ 1 - p * q := sub_nonneg.mpr hy1
  have hz1 : 1 - p * q ≤ 1 := by nlinarith [mul_nonneg hp.1 hq.1]
  constructor
  · exact sub_nonneg.mpr (pow_le_one₀ hz0 hz1)
  · exact sub_le_self _ (pow_nonneg hz0 b)

theorem survival_mem_Icc (b : ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) : survival b p n ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simp [survival]
  | succ n ih => exact step_mem_Icc b hp ih

theorem step_le_quadratic {b : ℕ} (hb : 1 ≤ b) {p q : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hcritical : (b : ℝ) * p ≤ 1) :
    step b p q ≤ q - ((b : ℝ) - 1) * p ^ 2 * q ^ 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have hy0 : 0 ≤ p * q := mul_nonneg hp.1 hq.1
  have hy1 : p * q ≤ 1 :=
    (mul_le_mul_of_nonneg_right hp.2 hq.1).trans (by simpa using hq.2)
  have h := one_sub_pow_quadratic n hy0 hy1
  have hmul := mul_le_mul_of_nonneg_right hcritical hq.1
  unfold step
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hmul ⊢
  calc
    1 - (1 - p * q) ^ (n + 1) ≤ (n + 1 : ℕ) * (p * q) - (n : ℝ) * (p * q) ^ 2 := h
    _ = ((n : ℝ) + 1) * p * q - ((n : ℝ) + 1 - 1) * p ^ 2 * q ^ 2 := by push_cast; ring
    _ ≤ q - ((n : ℝ) + 1 - 1) * p ^ 2 * q ^ 2 := sub_le_sub_right (by simpa using hmul) _

theorem le_reciprocal_of_quadratic_drift {q : ℕ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hq : ∀ n, 0 ≤ q n) (hzero : q 0 ≤ 1)
    (hstep : ∀ n, q (n + 1) ≤ q n - c * (q n) ^ 2) :
    ∀ n, q n ≤ 1 / (1 + c * n) := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    have hqn := hq n
    have hd : 0 < 1 + c * q n := by positivity
    have hn : 0 < 1 + c * n := by positivity
    have hn' : 0 < 1 + c * (n + 1 : ℕ) := by positivity
    have hi := (le_div_iff₀ hn).mp ih
    calc
      q (n + 1) ≤ q n / (1 + c * q n) := by
        apply (le_div_iff₀ hd).mpr
        have hs := mul_le_mul_of_nonneg_right (hstep n) hd.le
        have hnon : 0 ≤ c ^ 2 * (q n) ^ 3 := by positivity
        nlinarith
      _ ≤ 1 / (1 + c * (n + 1 : ℕ)) := by
        apply (div_le_div_iff₀ hd hn').mpr
        push_cast
        nlinarith

theorem tendsto_zero_of_quadratic_drift {q : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hq : ∀ n, 0 ≤ q n) (hzero : q 0 ≤ 1)
    (hstep : ∀ n, q (n + 1) ≤ q n - c * (q n) ^ 2) :
    Tendsto q atTop (𝓝 0) := by
  have hb := le_reciprocal_of_quadratic_drift hc.le hq hzero hstep
  have hinf : Tendsto (fun n : ℕ => 1 + c * (n : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have hz : Tendsto (fun n : ℕ => 1 / (1 + c * n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hinf
  exact squeeze_zero hq hb hz

theorem survival_le_reciprocal {b : ℕ} (hb : 1 ≤ b) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hcritical : (b : ℝ) * p ≤ 1) (n : ℕ) :
    survival b p n ≤ 1 / (1 + (((b : ℝ) - 1) * p ^ 2) * n) := by
  apply le_reciprocal_of_quadratic_drift
  · have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
    positivity
  · exact fun k => (survival_mem_Icc b hp k).1
  · simp [survival]
  · intro k
    exact step_le_quadratic hb hp (survival_mem_Icc b hp k) hcritical

theorem survival_tendsto_zero {b : ℕ} (hb : 2 ≤ b) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hcritical : (b : ℝ) * p ≤ 1) :
    Tendsto (survival b p) atTop (𝓝 0) := by
  by_cases hpzero : p = 0
  · subst p
    apply tendsto_congr' (Filter.eventually_atTop.mpr ⟨1, ?_⟩) |>.mpr tendsto_const_nhds
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [survival, step]
  · have hp0 : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hpzero)
    apply tendsto_zero_of_quadratic_drift (c := ((b : ℝ) - 1) * p ^ 2)
    · have hb' : (1 : ℝ) < b := by exact_mod_cast hb
      positivity
    · exact fun n => (survival_mem_Icc b hp n).1
    · simp [survival]
    · intro n
      exact step_le_quadratic (by omega) hp (survival_mem_Icc b hp n) hcritical

end CriticalBranching
end Problem367

end

end OAI
