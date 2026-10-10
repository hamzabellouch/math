import OAI.NumberTheory.JointDickman.Arithmetic.TotientLogBound
import Mathlib.NumberTheory.Harmonic.Bounds

namespace OAI

/-! # A sufficient subpower bound for the kernel denominator sum

Mertens' product theorem and the harmonic sum bound suffice here. A
polylogarithmic bound is enough to absorb either of the manuscript's
positive power savings, so no additional mean-value theorem is assumed.
-/

namespace JointDickman
open Filter Finset
open scoped Topology

noncomputable def kernelDenominatorSum (j Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 Q, (1/(q.totient : ℝ))*((j*q : ℕ)/(Nat.totient (j*q) : ℝ))

theorem kernelDenominatorSum_log_bound
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ j Q : ℕ,
      0 < j → 0 < Q → j*Q ≤ B^15 →
      kernelDenominatorSum j Q ≤ K^2*(Real.log B)^2*(1+15*Real.log B) := by
  obtain ⟨K,hK,hbound⟩ := totient_log_bound hMP
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with B hboundB hB
  intro j Q hj hQ hscale
  have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hQscale : Q ≤ B^15 := (Nat.le_mul_of_pos_left Q hj).trans hscale
  have hterm (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (1/(q.totient : ℝ))*((j*q : ℕ)/(Nat.totient (j*q) : ℝ)) ≤
        (K^2*(Real.log B)^2)*(1/(q : ℝ)) := by
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    have hjq : 0 < j*q := Nat.mul_pos hj hq0
    have hqB : q ≤ B^15 := (mem_Icc.mp hq).2.trans hQscale
    have hjqB : j*q ≤ B^15 := (Nat.mul_le_mul_left j (mem_Icc.mp hq).2).trans hscale
    have hqφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr hq0)
    have hjqφ : (0 : ℝ) < (j*q).totient := by exact_mod_cast (Nat.totient_pos.mpr hjq)
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq0
    have hfirst : 1/(q.totient : ℝ) ≤ K*Real.log B/q := by
      apply (div_le_div_iff₀ hqφ hqreal).mpr
      simpa only [one_mul] using hboundB q hq0 hqB
    have hsecond : ((j*q : ℕ) : ℝ)/(Nat.totient (j*q) : ℝ) ≤ K*Real.log B :=
      (div_le_iff₀ hjqφ).mpr (hboundB (j*q) hjq hjqB)
    exact (mul_le_mul hfirst hsecond (by positivity) (div_nonneg (mul_nonneg hK.le hlog) (Nat.cast_nonneg q))).trans_eq (by ring)
  have hsum : (∑ q ∈ Icc 1 Q, 1/(q : ℝ)) ≤ 1+Real.log Q := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using
      harmonic_le_one_add_log Q
  have hlogQ : Real.log (Q : ℝ) ≤ 15*Real.log B := by
    have hh := Real.log_le_log (by exact_mod_cast hQ : (0 : ℝ) < Q)
      (show (Q : ℝ) ≤ (B : ℝ)^15 by exact_mod_cast hQscale)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, (K^2*(Real.log B)^2)*(1/(q : ℝ)) := sum_le_sum hterm
    _ = (K^2*(Real.log B)^2)*(∑ q ∈ Icc 1 Q, 1/(q : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.trans (by linarith)) (by positivity)

theorem kernelDenominatorSum_subpower
    (hMP : PublishedInputs.PrimeProductMertensInput) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ j Q : ℕ, 0 < j → 0 < Q → j*Q ≤ B^15 →
      kernelDenominatorSum j Q ≤ (B : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := kernelDenominatorSum_log_bound hMP
  have hlim := (((log_power_div_power_tendsto_zero 2 hε).add
    ((log_power_div_power_tendsto_zero 3 hε).const_mul 15)).const_mul (K^2)).comp
      tendsto_natCast_atTop_atTop
  simp only [mul_zero,add_zero] at hlim
  filter_upwards [hbound,hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with B hboundB hsmall hB
  intro j Q hj hQ hscale
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  refine (hboundB j Q hj hQ hscale).trans ?_
  apply (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp
  convert hsmall using 1
  simp only [Function.comp_def,Real.rpow_ofNat]
  ring

end JointDickman

end OAI
