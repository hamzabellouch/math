import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences
import OAI.Analysis.IrrationalRotation.Analysis.ConvolutionContradiction
import Mathlib.Analysis.PSeries

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace Invariant233.ParameterAttenuation

def central (r : ℝ) (n : ℤ) : ℂ := if n = 0 then (r : ℂ) else 0

lemma central_support (r : ℝ) (K : ℕ) :
    Function.support (central r) ⊆ Set.Icc (-(K : ℤ)) (K : ℤ) := by
  intro n hn
  have hn0 : n = 0 := by
    by_contra h
    exact hn (by simp [central, h])
  subst n
  constructor <;> omega

lemma norm_central_le {r : ℝ} (hr : 0 ≤ r) (n : ℤ) :
    ‖central r n‖ ≤ r := by
  by_cases hn : n = 0
  · simp [central, hn, Complex.norm_real, abs_of_nonneg hr]
  · simp [central, hn, hr]

lemma circle_convolution_central (K : ℕ) (r : ℝ) (n : ℤ) :
    CircleParameterData.convolutionCoefficient K (central r) (central r) n =
      if n = 0 then (r : ℂ) * r else 0 := by
  unfold CircleParameterData.convolutionCoefficient
  rw [Finset.sum_eq_single 0]
  · simp [central]
  · intro i hi hi0
    simp [central, hi0]
  · intro h
    exact False.elim (h (by simp))

lemma product_convolution_central (K : ℕ) (r : ℝ) (n : ℕ) :
    FiniteWindow.convolution K (central r) (central r) n =
      if n = 0 then (r : ℂ) * r else 0 := by
  unfold FiniteWindow.convolution
  rw [Finset.sum_eq_single 0]
  · simp [central]
  · intro i hi hi0
    simp [central, hi0]
  · intro h
    by_cases hn : n = 0
    · subst n
      exact False.elim (h (by simp))
    · simp [central, hn]

lemma norm_circle_convolution_central_le (K : ℕ) (r : ℝ) (n : ℤ) :
    ‖CircleParameterData.convolutionCoefficient K (central r) (central r) n‖ ≤ r ^ 2 := by
  rw [circle_convolution_central]
  split_ifs
  · simp [Complex.norm_real, pow_two]
  · simpa using sq_nonneg r

lemma norm_product_convolution_central_le (K : ℕ) (r : ℝ) (n : ℕ) :
    ‖FiniteWindow.convolution K (central r) (central r) n‖ ≤ r ^ 2 := by
  rw [product_convolution_central]
  split_ifs
  · simp [Complex.norm_real, pow_two]
  · simpa using sq_nonneg r

lemma attenuation_le_reciprocal_cube (K : ℕ) (L ε j : ℝ) (hj : 0 < j)
    (hε : ε ≤ (1 / j) ^ 2)
    (hchoice : (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) ≤ ε / j) :
    Real.exp (-L / 10000) ≤ (1 / j) ^ 3 := by
  calc
    Real.exp (-L / 10000) ≤
        (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) := by
      nlinarith [Real.exp_pos (-L / 10000), Nat.cast_nonneg (α := ℝ) K]
    _ ≤ ε / j := hchoice
    _ ≤ (1 / j) ^ 2 / j := div_le_div_of_nonneg_right hε hj.le
    _ = (1 / j) ^ 3 := by ring

lemma log_le_attenuation {L j : ℝ} (hj : 0 < j)
    (h : Real.exp (-L / 10000) ≤ (1 / j) ^ 3) :
    30000 * Real.log j ≤ L := by
  have hlog := Real.log_le_log (Real.exp_pos (-L / 10000)) h
  rw [Real.log_exp, Real.log_pow, Real.log_div one_ne_zero hj.ne', Real.log_one] at hlog
  linarith

lemma summable_shifted_reciprocal_power (k : ℕ) (hk : 1 < k) :
    Summable (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) ^ k) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ k)⁻¹) :=
    Real.summable_nat_pow_inv.mpr hk
  simpa only [one_div, inv_pow] using (summable_nat_add_iff 1).mpr h

end ParameterAttenuation

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coefficientBound_ge_one (j : ℕ) : 1 ≤ p.coefficientBound j := by
  unfold CircleParameterData.coefficientBound
  apply Real.one_le_exp_iff.mpr
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (hp.C_pos s (Finset.mem_Icc.mp hs).1).le (Nat.cast_nonneg _)

theorem epsilon_le_reciprocal_sq (j : ℕ) (hj : 1 ≤ j) :
    p.ε j ≤ (1 / (j : ℝ)) ^ 2 := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hr : 0 ≤ 1 / (j : ℝ) := by positivity
  have hr1 : 1 / (j : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hjR
  have hb (n : ℤ) : ‖ParameterAttenuation.central (1 / (j : ℝ)) n‖ ≤
      p.coefficientBound j :=
    (ParameterAttenuation.norm_central_le hr n).trans (hr1.trans (hp.coefficientBound_ge_one j))
  have hcenter : 1 / (j : ℝ) ≤ ‖ParameterAttenuation.central (1 / (j : ℝ)) 0‖ := by
    change _ ≤ ‖((1 / (j : ℝ) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  obtain ⟨n, hn, hε⟩ := hp.polynomial_lower j hj _ _
    (ParameterAttenuation.central_support _ _) (ParameterAttenuation.central_support _ _)
    hb hb hcenter hcenter
  exact hε.trans (ParameterAttenuation.norm_circle_convolution_central_le _ _ _)

theorem summable_epsilon : Summable (fun n : ℕ => p.ε (n + 1)) := by
  apply Summable.of_nonneg_of_le (fun n => (hp.epsilon_pos (n + 1) (by omega)).le)
    (fun n => hp.epsilon_le_reciprocal_sq (n + 1) (by omega))
  exact ParameterAttenuation.summable_shifted_reciprocal_power 2 (by norm_num)

theorem attenuation_le_reciprocal_cube (j : ℕ) (hj : 1 ≤ j) :
    Real.exp (-p.L j / 10000) ≤ (1 / (j : ℝ)) ^ 3 := by
  apply ParameterAttenuation.attenuation_le_reciprocal_cube (p.K j) (p.L j) (p.ε j)
    (j : ℝ) (by exact_mod_cast (show 0 < j by omega))
    (hp.epsilon_le_reciprocal_sq j hj)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    hp.polynomial_attenuation j hj

theorem log_le_attenuation (j : ℕ) (hj : 1 ≤ j) :
    30000 * Real.log (j : ℝ) ≤ p.L j :=
  ParameterAttenuation.log_le_attenuation
    (by exact_mod_cast (show 0 < j by omega)) (hp.attenuation_le_reciprocal_cube j hj)

theorem summable_attenuation :
    Summable (fun n : ℕ => Real.exp (-p.L (n + 1) / 10000)) := by
  apply Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le)
    (fun n => hp.attenuation_le_reciprocal_cube (n + 1) (by omega))
  exact ParameterAttenuation.summable_shifted_reciprocal_power 3 (by norm_num)

theorem tendsto_L_atTop : Tendsto p.L atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (eventually_atTop.2 ⟨1, fun j hj => hp.log_le_attenuation j hj⟩)
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
    (by norm_num : (0 : ℝ) < 30000)

theorem conditional_tail_le (j : ℕ) (hj : 1 ≤ j) :
    (2 * (p.K j : ℝ) + 1) *
      (Real.exp (-p.L j) + 2 * Real.sqrt (Real.exp (-p.L j / 400))) ≤ p.ε j / j := by
  apply ConvolutionContradiction.coefficient_tail_le _ _ _ _ (hp.L_pos j hj).le
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    hp.polynomial_attenuation j hj

theorem not_eventually_conditional_obstruction (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ j : ℕ in atTop, c * p.ε j ≤ (2 * (p.K j : ℝ) + 1) *
      (Real.exp (-p.L j) + 2 * Real.sqrt (Real.exp (-p.L j / 400))) := by
  intro h
  apply ConvolutionContradiction.not_eventually_small_error c p.ε hc
    (eventually_atTop.2 ⟨1, fun j hj => hp.epsilon_pos j hj⟩)
  filter_upwards [h, eventually_ge_atTop 1] with j hj hj1
  exact hj.trans (hp.conditional_tail_le j hj1)

end CircleParameterLaws

namespace ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem epsilon_le_reciprocal_sq (n : ℕ) :
    p.ε n ≤ (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
  have hnR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hr : 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity
  have hr1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hnR
  have hb (i : ℤ) (_hi : |i| ≤ (p.K n : ℤ)) :
      ‖ParameterAttenuation.central (1 / ((n + 1 : ℕ) : ℝ)) i‖ ≤ p.coefficientBound n :=
    (ParameterAttenuation.norm_central_le hr i).trans (hr1.trans (hp.coefficientBound_ge_one n))
  have hcenter : 1 / ((n + 1 : ℕ) : ℝ) ≤
      ‖ParameterAttenuation.central (1 / ((n + 1 : ℕ) : ℝ)) 0‖ := by
    change _ ≤ ‖((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  obtain ⟨i, hi, hε⟩ := hp.polynomial_lower n _ _ hb hb hcenter hcenter
  exact hε.trans (ParameterAttenuation.norm_product_convolution_central_le _ _ _)

theorem summable_epsilon : Summable p.ε := by
  apply Summable.of_nonneg_of_le (fun n => (hp.epsilon_pos n).le)
    hp.epsilon_le_reciprocal_sq
  exact ParameterAttenuation.summable_shifted_reciprocal_power 2 (by norm_num)

theorem attenuation_le_reciprocal_cube (n : ℕ) :
    Real.exp (-p.L n / 10000) ≤ (1 / ((n + 1 : ℕ) : ℝ)) ^ 3 := by
  apply ParameterAttenuation.attenuation_le_reciprocal_cube (p.K n) (p.L n) (p.ε n)
    ((n + 1 : ℕ) : ℝ) (by positivity) (hp.epsilon_le_reciprocal_sq n)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    hp.polynomial_attenuation n

theorem log_le_attenuation (n : ℕ) :
    30000 * Real.log ((n + 1 : ℕ) : ℝ) ≤ p.L n :=
  ParameterAttenuation.log_le_attenuation (by positivity) (hp.attenuation_le_reciprocal_cube n)

theorem summable_attenuation :
    Summable (fun n : ℕ => Real.exp (-p.L n / 10000)) := by
  apply Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le)
    hp.attenuation_le_reciprocal_cube
  exact ParameterAttenuation.summable_shifted_reciprocal_power 3 (by norm_num)

theorem tendsto_L_atTop : Tendsto p.L atTop atTop := by
  apply tendsto_atTop_mono hp.log_le_attenuation
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.cast_le.mpr (Nat.le_succ n))
      tendsto_natCast_atTop_atTop
  exact (Real.tendsto_log_atTop.comp hn).const_mul_atTop
    (by norm_num : (0 : ℝ) < 30000)

theorem conditional_tail_le (n : ℕ) :
    (2 * (p.K n : ℝ) + 1) *
      (Real.exp (-p.L n) + 2 * Real.sqrt (Real.exp (-p.L n / 400))) ≤
      p.ε n / ((n + 1 : ℕ) : ℝ) := by
  apply ConvolutionContradiction.coefficient_tail_le _ _ _ _
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hp.L_ge_one n))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    hp.polynomial_attenuation n

theorem not_eventually_conditional_obstruction (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n : ℕ in atTop, c * p.ε n ≤ (2 * (p.K n : ℝ) + 1) *
      (Real.exp (-p.L n) + 2 * Real.sqrt (Real.exp (-p.L n / 400))) := by
  intro h
  have hstage : ∀ᶠ n : ℕ in atTop, 1 / ((n + 1 : ℕ) : ℝ) < c := by
    have ht : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    exact ht.eventually (gt_mem_nhds hc)
  obtain ⟨n, hn, hnc⟩ := (h.and hstage).exists
  exact ConvolutionContradiction.fixed_stage_contradiction c (p.ε n)
    ((n + 1 : ℕ) : ℝ) (hp.epsilon_pos n) hnc (hn.trans (hp.conditional_tail_le n))

end ProductScaleLaws
end Invariant233

end

end OAI
