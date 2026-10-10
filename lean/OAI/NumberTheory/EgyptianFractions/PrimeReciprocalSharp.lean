import Mathlib

namespace OAI
noncomputable section
open Filter Finset Set MeasureTheory
open scoped Topology BigOperators

namespace Problem337

/-- The elementary integral estimate for the real zeta series. -/
theorem nat_rpow_series_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ 1 + 1 / (s - 1) := by
  have hsneg : -s < -1 := by linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr hsneg
  have hsumshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s)) :=
    (summable_nat_add_iff 1).mpr hsum
  have htail : (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-s)) ≤ 1 / (s - 1) := by
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici (1 : ℝ)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by have hx1 : 1 ≤ x := hx; linarith) hxy (by linarith)
    have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-s)) 1
      (by simpa using hanti)
      (integrableOn_Ioi_rpow_of_lt hsneg (by norm_num))
      (by
        intro x hx
        apply Real.rpow_nonneg
        have hx1 : (1 : ℝ) < x := by simpa using hx
        linarith)
    rw [integral_Ioi_rpow_of_lt hsneg (by norm_num)] at h
    convert h using 1
    norm_num
    rw [show -s + 1 = -(s - 1) by ring, div_neg]
    ring
  rw [hsum.tsum_eq_zero_add, hsumshift.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Nat.cast_one, Real.zero_rpow (by linarith : -s ≠ 0),
    Real.one_rpow, zero_add]
  exact add_le_add_right htail 1

/-- A finite-prime Euler-product estimate, without any prime-distribution input. -/
theorem prime_rpow_sum_le_log_zeta_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {s : ℝ} (hs : 1 < s) :
    (∑ p ∈ P, (p : ℝ) ^ (-s)) ≤ Real.log (1 + 1 / (s - 1)) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-s)
      map_one' := by simp
      map_mul' := by
        intro m n
        simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hsum : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hprod : (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) ≤ 1 + 1 / (s - 1) := by
    calc
      (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) =
          ∑' n : Nat.factoredNumbers P, (n.val : ℝ) ^ (-s) := by
        simpa [f, Finset.filter_true_of_mem hP] using
          (EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum P)
      _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) :=
        Summable.tsum_subtype_le _ _ (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsum
      _ ≤ 1 + 1 / (s - 1) := nat_rpow_series_le hs
  have hfactor : ∀ p ∈ P, 0 < 1 - (p : ℝ) ^ (-s) := by
    intro p hp
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
  calc
    (∑ p ∈ P, (p : ℝ) ^ (-s)) ≤ ∑ p ∈ P, Real.log ((1 - (p : ℝ) ^ (-s))⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Real.log_inv]
      have := Real.log_le_sub_one_of_pos (hfactor p hp)
      linarith
    _ = Real.log (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) := by
      apply (Real.log_prod _).symm
      intro p hp
      exact inv_ne_zero (ne_of_gt (hfactor p hp))
    _ ≤ Real.log (1 + 1 / (s - 1)) :=
      Real.log_le_log (Finset.prod_pos (fun p hp => inv_pos.mpr (hfactor p hp))) hprod

/-- The elementary logarithmic bound for reciprocals of primes in a finite interval. -/
theorem prime_reciprocal_sum_le (P : Finset ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hP : ∀ p ∈ P, p.Prime) (hcap : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ Real.exp 1 * Real.log (1 + Real.log T) := by
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  let s : ℝ := 1 + 1 / Real.log T
  have hs : 1 < s := by
    dsimp [s]
    have : 0 < 1 / Real.log T := one_div_pos.mpr hlogT
    linarith
  have hterm : ∀ p ∈ P, 1 / (p : ℝ) ≤ Real.exp 1 * (p : ℝ) ^ (-s) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hpdelta : (p : ℝ) ^ (1 / Real.log T) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hp0]
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_le_log hp0 (hcap p hp)
      have := (div_le_one hlogT).2 hlog
      simpa only [div_eq_mul_inv, one_mul] using this
    have hpow : (p : ℝ) ^ s ≤ Real.exp 1 * (p : ℝ) := by
      dsimp [s]
      rw [Real.rpow_add hp0, Real.rpow_one]
      nlinarith
    rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
    exact (div_le_div_iff₀ hp0 (Real.rpow_pos_of_pos hp0 s)).2 (by simpa using hpow)
  calc
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ ∑ p ∈ P, Real.exp 1 * (p : ℝ) ^ (-s) :=
      Finset.sum_le_sum hterm
    _ = Real.exp 1 * ∑ p ∈ P, (p : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * Real.log (1 + 1 / (s - 1)) :=
      mul_le_mul_of_nonneg_left (prime_rpow_sum_le_log_zeta_bound P hP hs) (Real.exp_pos 1).le
    _ = Real.exp 1 * Real.log (1 + Real.log T) := by
      simp [s]

/-- The weighted variant used in the smooth-prefix divisor estimate. -/
theorem prime_weighted_reciprocal_sum_le (P : Finset ℕ) (T δ : ℝ)
    (hT : 2 ≤ T) (hδ : 0 ≤ δ) (hP : ∀ p ∈ P, p.Prime)
    (hcap : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, (p : ℝ) ^ (-1 + δ)) ≤
      T ^ δ * Real.exp 1 * Real.log (1 + Real.log T) := by
  have hterm : ∀ p ∈ P, (p : ℝ) ^ (-1 + δ) ≤ T ^ δ * (1 / (p : ℝ)) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    rw [Real.rpow_add hp0, Real.rpow_neg_one]
    have hpow := Real.rpow_le_rpow hp0.le (hcap p hp) hδ
    simpa only [one_div, mul_comm] using mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hp0.le)
  calc
    (∑ p ∈ P, (p : ℝ) ^ (-1 + δ)) ≤ ∑ p ∈ P, T ^ δ * (1 / (p : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = T ^ δ * (∑ p ∈ P, 1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ T ^ δ * (Real.exp 1 * Real.log (1 + Real.log T)) :=
      mul_le_mul_of_nonneg_left (prime_reciprocal_sum_le P T hT hP hcap)
        (Real.rpow_nonneg (by linarith) _)
    _ = T ^ δ * Real.exp 1 * Real.log (1 + Real.log T) := by ring

end Problem337

end

end OAI
