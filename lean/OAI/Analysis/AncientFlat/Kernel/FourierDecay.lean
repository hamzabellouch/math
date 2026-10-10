import Mathlib

namespace OAI
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace PeriodicResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def freq (n : ℤ) : ℂ := (2*Real.pi*(n:ℝ) : ℝ)*Complex.I
def osc (n : ℤ) (t : ℝ) : ℂ := Complex.exp (freq n*(t:ℂ))
lemma osc_continuous (n : ℤ) : Continuous (osc n) := by
  unfold osc
  fun_prop
lemma osc_deriv (n : ℤ) (t : ℝ) : HasDerivAt (osc n) (freq n*osc n t) t := by
  have h0 : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h := (h0.const_mul (freq n)).cexp
  change HasDerivAt (fun t : ℝ => Complex.exp (freq n*(t:ℂ))) (freq n*osc n t) t
  simpa only [osc, mul_one, one_mul, mul_comm] using h
lemma osc_norm (n : ℤ) (t : ℝ) : ‖osc n t‖=1 := by
  simp [osc, Complex.norm_exp, freq]
lemma osc_zero (n : ℤ) : osc n 0=1 := by simp [osc]
lemma osc_one (n : ℤ) : osc n 1=1 := by
  simp only [osc, Complex.ofReal_one, mul_one]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  congr 1
  simp only [freq, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
  ring
lemma osc_add (n m : ℤ) (t : ℝ) : osc (n+m) t=osc n t*osc m t := by
  rw [osc, osc, osc, ← Complex.exp_add]
  congr 1
  simp only [freq, Int.cast_add, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

def coeff (f : ℝ → E) (n : ℤ) : E := ∫ t in (0:ℝ)..1, osc n t • f t
lemma coeff_derivative (f g : ℝ → E) (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ t, HasDerivAt f (g t) t) (hper : f 1=f 0) (n : ℤ) :
    coeff g n= -freq n • coeff f n := by
  have h := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (osc_continuous n).continuousOn hf.continuousOn
    (fun t _ => osc_deriv n t) (fun t _ => hd t)
    ((continuous_const.mul (osc_continuous n)).intervalIntegrable 0 1)
    (hg.intervalIntegrable 0 1)
  simp only [osc_one, osc_zero, one_smul, hper, sub_self, zero_sub] at h
  rw [coeff, h]
  simp only [mul_smul, intervalIntegral.integral_smul, coeff, neg_smul]
omit [CompleteSpace E] in
lemma periodic_deriv (f : ℝ → E) (h : Function.Periodic f 1) :
    Function.Periodic (deriv f) 1 := by
  intro t
  rw [← deriv_comp_add_const f 1 t]
  congr 1
  exact funext h

omit [CompleteSpace E] in
lemma coeff_norm_le (f : ℝ → E) {M : ℝ}
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖≤M) (n : ℤ) : ‖coeff f n‖≤M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun t => osc n t • f t) (C := M) (by
      intro t ht
      rw [norm_smul, osc_norm, one_mul]
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at ht
      exact hM t ⟨ht.1.le, ht.2⟩)
  simpa [coeff] using h

lemma freq_sq_ge (n : ℤ) : (n:ℝ)^2≤‖freq n‖^2 := by
  have hp : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
  have he : ‖freq n‖=2*Real.pi*|(n:ℝ)| := by
    simp [freq, Complex.norm_real, Real.norm_eq_abs]
  rw [he]
  nlinarith [sq_nonneg (n:ℝ), sq_abs (n:ℝ), mul_le_mul_of_nonneg_right hp (abs_nonneg (n:ℝ))]

theorem summable_coeff_norm (f : ℝ → E) (hf : ContDiff ℝ 2 f)
    (hp : Function.Periodic f 1) : Summable (fun n : ℤ => ‖coeff f n‖) := by
  have hg : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hh : Continuous (deriv (deriv f)) := (hg.deriv' (n := 0)).continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hh.continuousOn
  have hMb : 0≤M := (norm_nonneg _).trans (hM 0 (by simp))
  have hbound (n : ℤ) (hn : n≠0) : ‖coeff f n‖≤M*(1/(n:ℝ)^2) := by
    have h1 := coeff_derivative f (deriv f) hf.continuous hg.continuous
      (fun t => (hf.differentiable (by norm_num) t).hasDerivAt) (by simpa using hp 0) n
    have h2 := coeff_derivative (deriv f) (deriv (deriv f)) hg.continuous hh
      (fun t => (hg.differentiable (by norm_num) t).hasDerivAt)
      (by simpa using periodic_deriv f hp 0) n
    have he : coeff (deriv (deriv f)) n=(freq n)^2 • coeff f n := by
      rw [h2, h1, smul_smul]
      congr 1
      ring
    have hnorm := coeff_norm_le (deriv (deriv f)) hM n
    rw [he, norm_smul, norm_pow] at hnorm
    have hn2 : 0<(n:ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
    rw [mul_one_div, le_div_iff₀ hn2]
    calc
      ‖coeff f n‖*(n:ℝ)^2 ≤ ‖coeff f n‖*‖freq n‖^2 :=
        mul_le_mul_of_nonneg_left (freq_sq_ge n) (norm_nonneg _)
      _ ≤ M := by simpa [mul_comm] using hnorm
  classical
  have hs : Summable (fun n : ℤ => (if n=0 then ‖coeff f 0‖ else 0)+M*(1/(n:ℝ)^2)) :=
    (hasSum_ite_eq 0 ‖coeff f 0‖).summable.add ((Real.summable_one_div_int_pow.mpr (by norm_num : 1<2)).mul_left M)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  by_cases hn : n=0
  · subst n
    simp
  · simpa [hn] using hbound n hn
end PeriodicResolvent

end

end OAI
