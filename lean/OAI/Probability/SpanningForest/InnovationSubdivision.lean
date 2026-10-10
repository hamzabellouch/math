import Mathlib

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.InnovationSubdivision

theorem norm_sub_geometric_le {A : Type*} [NormedRing A]
    (a : A) (μ : ℕ → A) (ε : ℝ) (ha : ‖a‖ ≤ 1) :
    ∀ n, (∀ k < n, ‖μ (k + 1) - a * μ k‖ ≤ ε) →
      ‖μ n - a ^ n * μ 0‖ ≤ (n : ℝ) * ε := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hstep
    have ih' := ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    have hid : μ (n + 1) - a ^ (n + 1) * μ 0 =
        (μ (n + 1) - a * μ n) + a * (μ n - a ^ n * μ 0) := by
      rw [pow_succ']
      noncomm_ring
    rw [hid]
    calc
      ‖(μ (n + 1) - a * μ n) + a * (μ n - a ^ n * μ 0)‖
          ≤ ‖μ (n + 1) - a * μ n‖ + ‖a * (μ n - a ^ n * μ 0)‖ :=
        norm_add_le _ _
      _ ≤ ε + ‖a‖ * ‖μ n - a ^ n * μ 0‖ :=
        add_le_add (hstep n (Nat.lt_succ_self n)) (norm_mul_le _ _)
      _ ≤ ε + 1 * ((n : ℝ) * ε) := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem tendsto_subdivision_error (C T : ℝ) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * C *
      (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have hquot : Tendsto (fun n : ℕ => T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hquot
  have hlim : Tendsto (fun n : ℕ => C * T *
      Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C * T)).mul hroot
  convert hlim using 1
  funext n
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem eq_of_subdivision_bounds {A : Type*} [NormedAddCommGroup A]
    (z w : A) (C T : ℝ)
    (h : ∀ n : ℕ, ‖z - w‖ ≤ ((n + 1 : ℕ) : ℝ) * C *
      (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) :
    z = w := by
  have hzero : ‖z - w‖ ≤ 0 := ge_of_tendsto' (tendsto_subdivision_error C T) h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))

theorem eq_of_subdivision_recurrences {A : Type*} [NormedRing A]
    (z w : A) (a : ℕ → A) (μ : ℕ → ℕ → A) (C T : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hfinal : ∀ n, μ n (n + 1) = z)
    (hfree : ∀ n, a n ^ (n + 1) * μ n 0 = w)
    (hstep : ∀ n k, k < n + 1 →
      ‖μ n (k + 1) - a n * μ n k‖ ≤
        C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) :
    z = w := by
  apply eq_of_subdivision_bounds z w C T
  intro n
  have hbound := norm_sub_geometric_le (a n) (μ n)
    (C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))
    (ha n) (n + 1) (hstep n)
  rw [hfinal n, hfree n] at hbound
  simpa only [mul_assoc] using hbound

theorem eq_of_eventual_subdivision_recurrences {A : Type*} [NormedRing A]
    (z w : A) (a : ℕ → A) (μ : ℕ → ℕ → A) (C T : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (hfinal : ∀ n, μ n (n + 1) = z)
    (hfree : ∀ n, a n ^ (n + 1) * μ n 0 = w)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1,
      ‖μ n (k + 1) - a n * μ n k‖ ≤
        C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) :
    z = w := by
  have hb : ∀ᶠ n : ℕ in atTop, ‖z - w‖ ≤ ((n + 1 : ℕ) : ℝ) * C *
      (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hstep] with n hn
    have hbound := norm_sub_geometric_le (a n) (μ n)
      (C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ)))
      (ha n) (n + 1) hn
    rw [hfinal n, hfree n] at hbound
    simpa only [mul_assoc] using hbound
  have hz : ‖z - w‖ ≤ 0 := ge_of_tendsto (tendsto_subdivision_error C T) hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

theorem gaussian_identity_of_subdivision_recurrences
    (z m : ℂ) (μ : ℕ → ℕ → ℂ) (C T v : ℝ) (hT : 0 ≤ T) (hv : 0 ≤ v)
    (hinit : ∀ n, μ n 0 = m) (hfinal : ∀ n, μ n (n + 1) = z)
    (hstep : ∀ᶠ n : ℕ in atTop, ∀ k < n + 1,
      ‖μ n (k + 1) - (Real.exp (-(T / ((n + 1 : ℕ) : ℝ)) * v) : ℂ) * μ n k‖ ≤
        C * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) :
    z = (Real.exp (-T * v) : ℂ) * m := by
  apply eq_of_eventual_subdivision_recurrences z ((Real.exp (-T * v) : ℂ) * m)
    (fun n => (Real.exp (-(T / ((n + 1 : ℕ) : ℝ)) * v) : ℂ)) μ C T
    ?_ hfinal ?_ hstep
  · intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hT (by positivity))) hv
  · intro n
    rw [hinit n]
    congr 1
    have he : Real.exp (-(T / ((n + 1 : ℕ) : ℝ)) * v) ^ (n + 1) =
        Real.exp (-T * v) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp
    exact_mod_cast he

end Problem336.InnovationSubdivision

end

end OAI
