import Mathlib
import OAI.Analysis.Conductivity.Variational.CrossingProfiles

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma cutoff_exp_hasDerivAt {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (a z : ℝ) :
    HasDerivAt (fun z => χ z * exp (-a*z))
      ((deriv χ z-a*χ z)*exp (-a*z)) z := by
  have hd := (hχ.differentiable (by simp) z).hasDerivAt
  have he := ((hasDerivAt_id z).const_mul (-a)).exp
  exact (hd.mul he).congr_deriv
    (g' := (deriv χ z-a*χ z)*exp (-a*z)) (by simp only [id_eq,mul_one]; ring)

lemma cutoff_exp_residual {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (a z : ℝ) :
    deriv (deriv (fun z => χ z * exp (-a*z))) z - a^2*(χ z * exp (-a*z)) =
      (deriv (deriv χ) z-2*a*deriv χ z)*exp (-a*z) := by
  have he : deriv (fun z => χ z * exp (-a*z)) =
      fun z => (deriv χ z-a*χ z)*exp (-a*z) :=
    funext fun z => (cutoff_exp_hasDerivAt hχ a z).deriv
  rw [he]
  have hd := ((smooth_deriv_infty hχ).differentiable (by simp) z).hasDerivAt
  have hd₁ := (hχ.differentiable (by simp) z).hasDerivAt
  have hd₂ := ((hd.sub (hd₁.const_mul a)).mul (((hasDerivAt_id z).const_mul (-a)).exp))
  simp only [Pi.mul_def,Pi.sub_def,id_eq,mul_one] at hd₂
  rw [hd₂.deriv]
  ring

lemma crossing_cutoff_derivative_bounds {M L : ℝ} (hM0 : 1 ≤ M) (hL : 1 ≤ L)
    (hM : ∀ x : ℝ, |deriv smoothTransition x| ≤ M ∧
      |deriv (deriv smoothTransition) x| ≤ M) (z : ℝ) :
    |deriv (crossingOn L) z| ≤ 4*M ∧
    |deriv (deriv (crossingOn L)) z| ≤ 16*M ∧
    |deriv (crossingOff L) z| ≤ 4*M ∧
    |deriv (deriv (crossingOff L)) z| ≤ 16*M := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hq : |4/L| ≤ 4 := by
    rw [abs_of_pos (div_pos (by norm_num) hLp)]
    exact (div_le_iff₀ hLp).mpr (by linarith)
  have hq₂ : |(4/L)^2| ≤ 16 := by
    rw [abs_pow]
    nlinarith [abs_nonneg (4/L)]
  rw [crossingOn_second,crossingOff_second,deriv_crossingOn,deriv_crossingOff]
  simp only [abs_mul,abs_neg]
  constructor
  · rw [mul_comm, mul_comm 4 M]
    exact mul_le_mul (hM _).1 hq (abs_nonneg _) (zero_le_one.trans hM0)
  · exact ⟨mul_le_mul hq₂ (hM _).2 (abs_nonneg _) (by norm_num),
      mul_le_mul hq (hM _).1 (abs_nonneg _) (by norm_num),
      mul_le_mul hq₂ (hM _).2 (abs_nonneg _) (by norm_num)⟩

def crossingResidualFirst (L z : ℝ) : ℝ :=
  deriv (deriv (crossingFirst L)) z - 9*crossingFirst L z

def crossingResidualSecond (L z : ℝ) : ℝ :=
  deriv (deriv (crossingSecond L)) z - crossingSecond L z

lemma crossingResidualFirst_formula (L z : ℝ) :
    crossingResidualFirst L z =
      (deriv (deriv (crossingOff L)) z-6*deriv (crossingOff L) z)*exp (-3*z) := by
  unfold crossingResidualFirst crossingFirst
  simpa only [show (3:ℝ)^2=9 by norm_num,show (2:ℝ)*3=6 by norm_num] using
    cutoff_exp_residual (crossingOff_smooth L) 3 z
lemma crossingResidualSecond_formula (L z : ℝ) :
    crossingResidualSecond L z =
      (deriv (deriv (crossingOn L)) z-2*deriv (crossingOn L) z)*exp (-z) := by
  unfold crossingResidualSecond crossingSecond
  simpa only [one_pow,one_mul,mul_one,neg_one_mul] using
    cutoff_exp_residual (crossingOn_smooth L) 1 z

lemma crossingResidualFirst_normalized (L z : ℝ) :
    crossingResidualFirst L z / exp (-z) =
      (deriv (deriv (crossingOff L)) z-6*deriv (crossingOff L) z)*exp (-2*z) := by
  rw [crossingResidualFirst_formula,mul_div_assoc,←exp_sub]
  congr 2
  ring
lemma crossingResidualSecond_normalized (L z : ℝ) :
    crossingResidualSecond L z / exp (-3*z) =
      (deriv (deriv (crossingOn L)) z-2*deriv (crossingOn L) z)*exp (2*z) := by
  rw [crossingResidualSecond_formula,mul_div_assoc,←exp_sub]
  congr 2
  ring

lemma crossingResidualFirst_zero {L z : ℝ} (hL : 0 < L) (hz : z < L/2) :
    crossingResidualFirst L z = 0 := by
  have hu : 4*z/L-2 < 0 := by
    have : 4*z/L < 2 := (div_lt_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualFirst_formula,crossingOff_second]
  simp only [deriv_crossingOff,
    (smoothTransition_flat_left hu).1,(smoothTransition_flat_left hu).2]
  ring
lemma crossingResidualSecond_zero {L z : ℝ} (hL : 0 < L) (hz : -L/2 < z) :
    crossingResidualSecond L z = 0 := by
  have hu : 1 < 4*z/L+3 := by
    have : -2 < 4*z/L := (lt_div_iff₀ hL).mpr (by linarith)
    linarith
  rw [crossingResidualSecond_formula,crossingOn_second]
  simp only [deriv_crossingOn,
    (smoothTransition_flat_right hu).1,(smoothTransition_flat_right hu).2]
  ring

lemma crossing_residual_bounds {M L : ℝ} (hM0 : 1 ≤ M) (hL : 1 ≤ L)
    (hM : ∀ x : ℝ, |deriv smoothTransition x| ≤ M ∧
      |deriv (deriv smoothTransition) x| ≤ M) (z : ℝ) :
    |crossingResidualFirst L z / exp (-z)| ≤ 40*M*exp (-L) ∧
    |crossingResidualSecond L z / exp (-3*z)| ≤ 40*M*exp (-L) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hMp : 0 ≤ M := le_trans (by norm_num) hM0
  obtain ⟨hon₁,hon₂,hoff₁,hoff₂⟩ := crossing_cutoff_derivative_bounds hM0 hL hM z
  constructor
  · by_cases hz : z < L/2
    · rw [crossingResidualFirst_zero hLp hz,zero_div,abs_zero]
      positivity
    · rw [crossingResidualFirst_normalized,abs_mul,abs_of_pos (exp_pos _)]
      have he : exp (-2*z) ≤ exp (-L) := exp_le_exp.mpr (by linarith)
      have hr : |deriv (deriv (crossingOff L)) z-6*deriv (crossingOff L) z| ≤ 40*M := by
        have := abs_sub (deriv (deriv (crossingOff L)) z) (6*deriv (crossingOff L) z)
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<6)] at this
        linarith
      exact mul_le_mul hr he (exp_pos _).le (by positivity)
  · by_cases hz : -L/2 < z
    · rw [crossingResidualSecond_zero hLp hz,zero_div,abs_zero]
      positivity
    · rw [crossingResidualSecond_normalized,abs_mul,abs_of_pos (exp_pos _)]
      have he : exp (2*z) ≤ exp (-L) := exp_le_exp.mpr (by linarith)
      have hr : |deriv (deriv (crossingOn L)) z-2*deriv (crossingOn L) z| ≤ 40*M := by
        have := abs_sub (deriv (deriv (crossingOn L)) z) (2*deriv (crossingOn L) z)
        rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at this
        linarith
      exact mul_le_mul hr he (exp_pos _).le (by positivity)

lemma crossing_mode_ratios {L z : ℝ} :
    (z ≤ 0 → |crossingSecond L z / exp (-3*z)| ≤ 1) ∧
    (0 ≤ z → |crossingFirst L z / exp (-z)| ≤ 1) := by
  constructor
  · intro hz
    rw [crossingSecond,mul_div_assoc,←exp_sub,abs_mul,
      abs_of_nonneg (crossingOn_bounds L z).1,abs_of_pos (exp_pos _)]
    have he : exp (-z- -3*z) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left he (crossingOn_bounds L z).1).trans
      (by simpa using (crossingOn_bounds L z).2)
  · intro hz
    rw [crossingFirst,mul_div_assoc,←exp_sub,abs_mul,
      abs_of_nonneg (crossingOff_bounds L z).1,abs_of_pos (exp_pos _)]
    have he : exp (-3*z- -z) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left he (crossingOff_bounds L z).1).trans
      (by simpa using (crossingOff_bounds L z).2)

lemma exists_small_crossing_scale {M : ℝ} (hM : 1 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ 40*M*exp (-L) ≤ 1/56 := by
  refine ⟨2240*M+1,by linarith,?_⟩
  rw [exp_neg,←div_eq_mul_inv,div_le_iff₀ (exp_pos _)]
  have := add_one_le_exp (2240*M+1)
  linarith

end ScalarConductivity

end

end OAI
