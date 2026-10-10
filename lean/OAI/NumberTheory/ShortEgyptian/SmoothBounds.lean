import OAI.NumberTheory.ShortEgyptian.DivisorCover

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def primeRecipBound (T : ℝ) : ℝ :=
  8+4*Real.log (1+Real.log T/Real.log 2)

theorem prime_reciprocals_real (T : ℝ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (1:ℝ)/p ≤ primeRecipBound T := by
  have h2 : 2 ≤ ⌊T⌋₊ := Nat.le_floor hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (prime_reciprocals_bound ⌊T⌋₊ h2).trans
  have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊T⌋₊))
    (Nat.floor_le (by linarith : 0 ≤ T))
  have hh : 0 ≤ Real.log (⌊T⌋₊:ℝ) := Real.log_natCast_nonneg _
  have harg : 0 < 1+Real.log (⌊T⌋₊:ℝ)/Real.log 2 := by positivity
  have hlog' := Real.log_le_log harg (show 1+Real.log (⌊T⌋₊:ℝ)/Real.log 2 ≤ 1+Real.log T/Real.log 2 by gcongr)
  unfold primeRecipBound
  linarith

theorem shifted_prime_sum (T lam : ℝ) (hT : 2 ≤ T) (hlam : 0 ≤ lam) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p:ℝ)^(-(1-lam)) ≤
      T^lam * primeRecipBound T := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊T⌋₊, T^lam * ((1:ℝ)/p) := by
      apply sum_le_sum
      intro p hp
      have hh := Nat.mem_primesLE.mp hp
      have hp0 : 0 < (p:ℝ) := by exact_mod_cast hh.2.pos
      have hpT : (p:ℝ) ≤ T := le_trans (by exact_mod_cast hh.1) (Nat.floor_le (by linarith))
      calc
        _ = (p:ℝ)^lam * ((1:ℝ)/p) := by
          rw [one_div, ← Real.rpow_neg_one,← Real.rpow_add hp0]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le hpT hlam) (by positivity)
    _ = T^lam * ∑ p ∈ Nat.primesLE ⌊T⌋₊, (1:ℝ)/p := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_reciprocals_real T hT) (Real.rpow_nonneg (by linarith) _)

noncomputable def smallSmoothConst : ℝ := ∑' n : ℕ, (n:ℝ)^(-41/40:ℝ)

theorem smallSmoothConst_nonneg : 0 ≤ smallSmoothConst := by
  exact tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem small_prime_sum (T : ℝ) (hT : 0 ≤ T) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p:ℝ)^(-(1-(1/10:ℝ))) ≤ T^(1/8:ℝ)*smallSmoothConst := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-41/40:ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊T⌋₊, T^(1/8:ℝ)*(p:ℝ)^(-41/40:ℝ) := by
      apply sum_le_sum
      intro p hp
      have hh := Nat.mem_primesLE.mp hp
      have hp0 : 0 < (p:ℝ) := by exact_mod_cast hh.2.pos
      have hpT : (p:ℝ) ≤ T := le_trans (by exact_mod_cast hh.1) (Nat.floor_le hT)
      calc
        _ = (p:ℝ)^(1/8:ℝ)*(p:ℝ)^(-41/40:ℝ) := by rw [← Real.rpow_add hp0]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le hpT (by norm_num)) (Real.rpow_nonneg hp0.le _)
    _ = T^(1/8:ℝ) * ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p:ℝ)^(-41/40:ℝ) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (Real.rpow_nonneg hT _)

theorem factored_primesLE {n : ℕ} (hn : n ≠ 0) {T : ℝ}
    (hs : ∀ p ∈ n.primeFactorsList, (p:ℝ) ≤ T) :
    n ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) := by
  refine ⟨hn, ?_⟩
  intro p hp
  exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hs p hp), Nat.prime_of_mem_primeFactorsList hp⟩

theorem divisor_harmonic_bound (r : ℕ) (T : ℝ) (hT : 2 ≤ T) :
    ∑ d ∈ Icc 1 ⌊T⌋₊, (d.divisors.card:ℝ)^r/d ≤
      Real.exp (momentSeriesConst r * primeRecipBound T) := by
  have hf : ∀ d ∈ Icc 1 ⌊T⌋₊, d ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) := by
    intro d hd
    have hd' := mem_Icc.mp hd
    apply factored_primesLE (by omega)
    intro p hp
    apply le_trans _ (Nat.floor_le (by linarith : 0 ≤ T))
    exact_mod_cast (Nat.le_of_dvd (by omega : 0 < d) (Nat.dvd_of_mem_primeFactorsList hp)).trans hd'.2
  have hh := smooth_divisor_weight r (by norm_num : 1/2 ≤ (1:ℝ)) (Icc 1 ⌊T⌋₊) (Nat.primesLE ⌊T⌋₊) hf
  have hfilter : (Nat.primesLE ⌊T⌋₊).filter Nat.Prime = Nat.primesLE ⌊T⌋₊ := filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [divisorWeight, Real.rpow_neg_one, ← div_eq_mul_inv, hfilter] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  simpa only [one_div] using mul_le_mul_of_nonneg_left (prime_reciprocals_real T hT) (momentSeriesConst_nonneg r)

theorem rough_exponential_bound {n : ℕ} (hn : n ≠ 0) (v W z : ℝ)
    (hv : 0 < v) (hvW : v < W) (hz : 1 < z) (hW : Real.log n ≤ W)
    (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (truncatedDivisorCount (Real.exp v) n:ℝ) ≤
      Real.exp ((1+Real.log (W/v))*v/Real.log z) := by
  have hW0 : 0 < W := hv.trans hvW
  have hq : 0 < v/W := div_pos hv hW0
  have hq1 : v/W < 1 := (div_lt_one hW0).mpr hvW
  have hb := rough_truncated_bound hn (Real.exp v) W z (v/W) hz hq hq1 hW hrough
  rw [Real.log_exp, Real.log_div hv.ne' hW0.ne'] at hb
  rw [Real.log_div hW0.ne' hv.ne']
  convert hb using 1
  congr 1
  field_simp
  ring

theorem prefix_weight_bound {n d e p : ℕ} (hde : n = d*e)
    (hd : d ≠ 0) (he : e ≠ 0) (hp : p.Prime) (r : ℕ) (v W : ℝ)
    (hv : 0 < v) (hvW : v < W) (hnW : Real.log n ≤ W)
    (hr : ∀ q ∈ e.primeFactorsList, p ≤ q) :
    (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ (d.divisors.card:ℝ)^r *
      Real.exp ((r:ℝ)*(1+Real.log (W/v))*v/Real.log p) := by
  have hele : (e:ℝ) ≤ n := by
    exact_mod_cast (Nat.le_of_dvd (by rw [hde]; exact Nat.mul_pos (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero he))
      (hde ▸ dvd_mul_left e d))
  have hrough := rough_exponential_bound he v W p hv hvW (by exact_mod_cast hp.one_lt)
    ((Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero he) hele).trans hnW)
    (fun q hq => by exact_mod_cast hr q hq)
  have hmul : (truncatedDivisorCount (Real.exp v) n:ℝ) ≤
      (d.divisors.card:ℝ)*truncatedDivisorCount (Real.exp v) e := by
    rw [hde]
    exact_mod_cast truncatedDivisors_mul (Real.exp v) hd he
  calc
    _ ≤ ((d.divisors.card:ℝ)*truncatedDivisorCount (Real.exp v) e)^r := pow_le_pow_left₀ (Nat.cast_nonneg _) hmul r
    _ ≤ ((d.divisors.card:ℝ)*Real.exp ((1+Real.log (W/v))*v/Real.log p))^r := by gcongr
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring

theorem smooth_prefix_sum (r : ℕ) (v T lam : ℝ) (hT : 2 ≤ T)
    (hlam : 0 ≤ lam) (hlam' : lam ≤ 1/2) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) ∧ Real.exp (v/5) ≤ d) :
    ∑ d ∈ s, (d.divisors.card:ℝ)^r/d ≤
      Real.exp (-lam*v/5 + momentSeriesConst r * (T^lam * primeRecipBound T)) := by
  have hh := rankin_divisor_weight r (Real.exp (v/5)) lam (Real.exp_pos _) hlam hlam' s (Nat.primesLE ⌊T⌋₊) hs
  have hfilter : (Nat.primesLE ⌊T⌋₊).filter Nat.Prime = Nat.primesLE ⌊T⌋₊ := filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  rw [Real.log_exp, hfilter] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hsum := mul_le_mul_of_nonneg_left (shifted_prime_sum T lam hT hlam) (momentSeriesConst_nonneg r)
  linarith

theorem small_smooth_prefix_sum (v T : ℝ) (hT : 0 ≤ T) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers (Nat.primesLE ⌊T⌋₊) ∧ Real.exp (v/5) ≤ d) :
    ∑ d ∈ s, (1:ℝ)/d ≤
      Real.exp (-v/50 + momentSeriesConst 0 * (T^(1/8:ℝ) * smallSmoothConst)) := by
  have hh := rankin_divisor_weight 0 (Real.exp (v/5)) (1/10) (Real.exp_pos _) (by norm_num) (by norm_num)
    s (Nat.primesLE ⌊T⌋₊) hs
  have hfilter : (Nat.primesLE ⌊T⌋₊).filter Nat.Prime = Nat.primesLE ⌊T⌋₊ := filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [pow_zero, Real.log_exp, hfilter] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hsum := mul_le_mul_of_nonneg_left (small_prime_sum T hT) (momentSeriesConst_nonneg 0)
  linarith

end ShortEgyptian

end OAI
