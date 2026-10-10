import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace Ostmann.Conclusion

def bulkScale (k : ℕ) : ℝ := (k : ℝ)^4

def bulkSize (k : ℕ) (L : ℝ) : ℕ := 2 * ⌊bulkScale k * L / 2⌋₊

def initialGap (Bs : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  (Bs + 8 * Real.log (bulkScale k)) * bulkSize k L

def stepGap (BD Bz : ℝ) (k : ℕ) (L : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ)^j * (BD + Bz * Real.log (bulkScale k) +
    (2/5 : ℝ) * Real.log ((2 : ℝ)^j)) * bulkSize k L

def frequencyBudget (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) : ℝ :=
  initialGap Bs k L + ∑ j ∈ Finset.range l, stepGap BD Bz k L j +
    (2 : ℝ)^l * Real.sqrt (bulkSize k L)

def frequencyBound (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) : ℕ :=
  ⌊Real.exp (frequencyBudget Bs BD Bz k L l)⌋₊

theorem bulkSize_even (k : ℕ) (L : ℝ) : Even (bulkSize k L) := by
  exact even_two_mul _

theorem bulkSize_bounds (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    bulkScale k * L - 2 < (bulkSize k L : ℝ) ∧
      (bulkSize k L : ℝ) ≤ bulkScale k * L := by
  have h := Nat.lt_floor_add_one (bulkScale k * L / 2)
  have h' := Nat.floor_le (show 0 ≤ bulkScale k * L / 2 by
    unfold bulkScale
    positivity)
  simp only [bulkSize, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> linarith

theorem bulkSize_tendsto_atTop {k : ℕ} (hk : 0 < k) :
    Tendsto (fun L : ℝ => (bulkSize k L : ℝ)) atTop atTop := by
  have hz : 0 < bulkScale k := by unfold bulkScale; positivity
  have h : Tendsto (fun L : ℝ => bulkScale k * L - 2) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      (tendsto_id.const_mul_atTop hz).atTop_add (tendsto_const_nhds (x := -(2 : ℝ)))
  apply tendsto_atTop_mono' atTop _ h
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  exact (bulkSize_bounds k hL).1.le

theorem sum_dyadic (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 : ℝ)^j = (2 : ℝ)^k - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem sum_dyadic_log (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 : ℝ)^j * Real.log ((2 : ℝ)^j) =
      (2 : ℝ)^k * Real.log ((2 : ℝ)^k) -
        2 * (2 : ℝ)^k * Real.log 2 + 2 * Real.log 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Real.log_pow]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem frequencyBudget_eq (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) :
    frequencyBudget Bs BD Bz k L l =
      (Bs + 8 * Real.log (bulkScale k)) * bulkSize k L +
      (BD + Bz * Real.log (bulkScale k)) * bulkSize k L * ((2 : ℝ)^l - 1) +
      (2/5 : ℝ) * bulkSize k L * ((2 : ℝ)^l * Real.log ((2 : ℝ)^l) -
        2*(2 : ℝ)^l*Real.log 2+2*Real.log 2) +
      (2 : ℝ)^l * Real.sqrt (bulkSize k L) := by
  unfold frequencyBudget initialGap stepGap
  simp_rw [show ∀ j : ℕ,
    (2 : ℝ)^j * (BD+Bz*Real.log (bulkScale k)+(2/5 : ℝ)*Real.log ((2 : ℝ)^j)) *
      bulkSize k L =
      ((BD+Bz*Real.log (bulkScale k))*bulkSize k L)*(2 : ℝ)^j +
      ((2/5 : ℝ)*bulkSize k L)*((2 : ℝ)^j*Real.log ((2 : ℝ)^j)) from fun j => by ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_dyadic, sum_dyadic_log]
  ring

def finalRate (BD Bs Bz C : ℝ) (k : ℕ) : ℝ :=
  -(7/20 : ℝ) * Real.log ((2 : ℝ)^k) + BD + 2*Bs +
    (Bz+16)*Real.log (bulkScale k)+C

theorem finalRate_div_tendsto (BD Bs Bz C : ℝ) :
    Tendsto (fun k : ℕ => finalRate BD Bs Bz C k / (k : ℝ)) atTop
      (𝓝 (-(7/20 : ℝ)*Real.log 2)) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun k : ℕ => (BD+2*Bs+C)/(k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (hconst.add (hlog.const_mul (4*(Bz+16)))).const_add
    (-(7/20 : ℝ)*Real.log 2)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [finalRate, bulkScale, Real.log_pow]
  field_simp
  ring

theorem finalRate_tendsto_atBot (BD Bs Bz C : ℝ) :
    Tendsto (finalRate BD Bs Bz C) atTop atBot := by
  have hneg : -(7/20 : ℝ)*Real.log 2 < 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have h := (finalRate_div_tendsto BD Bs Bz C).neg_mul_atTop hneg
      tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  exact div_mul_cancel₀ _ hk0

theorem exists_depth_for_final_rate (BD Bs Bz C B : ℝ) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ finalRate BD Bs Bz C k < -2*B-4 := by
  have h := (finalRate_tendsto_atBot BD Bs Bz C).eventually
    (eventually_lt_atBot (-2*B-4))
  exact ((eventually_ge_atTop k₀).and h).exists

end Ostmann.Conclusion

end

end OAI
