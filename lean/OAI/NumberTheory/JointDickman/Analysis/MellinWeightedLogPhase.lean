import OAI.NumberTheory.JointDickman.Amplification.IncreasingPartialSummation
import OAI.NumberTheory.JointDickman.Analysis.MellinSieveRegularity
import OAI.NumberTheory.JointDickman.Analysis.CharacterLogPhase

namespace OAI

/-! # Logarithmic cancellation with the two Mellin profile weights -/
namespace JointDickman
open Finset Filter Complex Problem337
open scoped Topology

lemma mellinSieveFunction_dilate {N d x : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hx : 0 < x) (t : ℝ) :
    mellinSieveFunction N t (d*x) =
      Complex.exp (((-Real.log d*t : ℝ) : ℂ)*I)*mellinSieveFunction (N/d) t x := by
  have hw : mellinSieveWeight N (d*x) = mellinSieveWeight (N/d) x := by
    unfold mellinSieveWeight
    rw [Real.log_mul hd.ne' hx.ne', Real.log_div hN.ne' hd.ne']
    rw [show Real.log d+Real.log x-Real.log N =
      Real.log x-(Real.log N-Real.log d) by ring]
    congr 1
    field_simp
  unfold mellinSieveFunction
  rw [hw, Real.log_mul hd.ne' hx.ne', mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma linear_log_phase_sum_bound (t : ℝ) (L R : ℤ) (hL : 0 < L) (hLR : L ≤ R)
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ V, L ≤ V → V ≤ R →
      ‖∑ n ∈ Icc L V, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, (n:ℂ)*(n:ℂ)^(-((t:ℂ)*I))‖ ≤ 2*D*((R:ℝ)+1) := by
  have hh := increasing_weighted_sum_Icc_bound
    (fun n => (n:ℂ)^(-((t:ℂ)*I))) (fun n => (n:ℝ)) L R hLR hD
    (fun n hn => by exact_mod_cast (hL.le.trans hn))
    (fun i _ j _ hij => by change (i:ℝ) ≤ (j:ℝ); exact_mod_cast hij) hpartial
  simpa only [Complex.real_smul, Complex.ofReal_intCast, Int.cast_add, Int.cast_one] using hh

lemma mellinSieveFunction_left_sum {N : ℝ} (hN : 0 < N) (t : ℝ)
    (L R : ℤ) (hL : 0 < L) (hLR : L ≤ R) (hRN : (R:ℝ) ≤ N)
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ V, L ≤ V → V ≤ R →
      ‖∑ n ∈ Icc L V, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ 2*D*((R:ℝ)+1)/N := by
  have he : (∑ n ∈ Icc L R, mellinSieveFunction N t n) =
      (1/(N:ℂ))*(∑ n ∈ Icc L R, (n:ℂ)*(n:ℂ)^(-((t:ℂ)*I))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hL.trans_le (mem_Icc.mp hn).1
    rw [mellinSieveFunction_left hN hn0 (le_trans (by exact_mod_cast (mem_Icc.mp hn).2) hRN),
      show (1:ℂ)-(t:ℂ)*I = 1+(-((t:ℂ)*I)) by ring,
      cpow_add _ _ (by exact_mod_cast hn0.ne'), cpow_one]
    push_cast
    ring
  rw [he, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  have hh := linear_log_phase_sum_bound t L R hL hLR hD hpartial
  have := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1/N by positivity)
  simpa only [one_div_mul_eq_div] using this

lemma mellinSieveFunction_right_sum {N : ℝ} (hN : 0 < N) (t : ℝ)
    (L R : ℤ) (hL : 0 < L) (hNL : N ≤ (L:ℝ))
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ V, L ≤ V → V ≤ R →
      ‖∑ n ∈ Icc L V, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ N^3*D*(L:ℝ)^(-3:ℝ) := by
  have he : (∑ n ∈ Icc L R, mellinSieveFunction N t n) =
      (N:ℂ)^3*(∑ n ∈ Icc L R, (((n:ℝ)^(-3:ℝ):ℝ):ℂ)*(n:ℂ)^(-((t:ℂ)*I))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hL.trans_le (mem_Icc.mp hn).1
    have hNn : N ≤ (n:ℝ) := hNL.trans (by exact_mod_cast (mem_Icc.mp hn).1)
    rw [mellinSieveFunction_right hN hNn,
      show (-3:ℂ)-(t:ℂ)*I = ((-3:ℝ):ℂ)+(-((t:ℂ)*I)) by push_cast; ring,
      cpow_add _ _ (by exact_mod_cast hn0.ne')]
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp, ← ofReal_cpow hn0.le]
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  have hh := rpow_weighted_sum_Icc_bound
    (fun n => (n:ℂ)^(-((t:ℂ)*I))) L R (σ := 3) hL hD (by norm_num) hpartial
  have := mul_le_mul_of_nonneg_left hh (show 0 ≤ N^3 by positivity)
  simpa only [mul_assoc] using this

/-- Logarithmic phase cancellation in the angular convention. -/
theorem angular_log_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (t : ℝ) (L R : ℤ),
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ A*U^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hbound⟩ := logarithmic_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [hbound, eventually_gt_atTop (0:ℝ)] with U hbound hU
  intro t L R hlo hhi hL hR
  have he : (∑ n ∈ Icc L R, (n:ℂ)^(-((t:ℂ)*I))) =
      ∑ n ∈ Icc L R, differencingPhase (0*n+(-t/(2*Real.pi))*Real.log (n:ℝ)) := by
    apply sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := hU.trans_le (hL.trans (by exact_mod_cast (mem_Icc.mp hn).1))
    simpa only [zero_mul, zero_add] using imaginary_power_as_log_phase t (by exact_mod_cast hn0)
  rw [he]
  exact hbound 0 (-t/(2*Real.pi)) L R
    (by simpa only [neg_div, abs_neg] using hlo)
    (by simpa only [neg_div, abs_neg] using hhi) hL hR

end JointDickman

end OAI
