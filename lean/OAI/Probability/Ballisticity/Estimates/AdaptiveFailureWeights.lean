import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def successes {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, if ω ∈ B k then (1:ℝ) else 0
noncomputable def failureWeight {Ω : Type*} (B : ℕ → Set Ω) (s : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (s/4*(n:ℝ)-successes B n ω)

lemma successes_nonneg {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) : 0 ≤ successes B n ω := by
  apply Finset.sum_nonneg
  intro k hk
  split_ifs <;> norm_num
lemma successes_succ {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    successes B (n+1) ω = successes B n ω+(if ω ∈ B n then 1 else 0) := by
  simp only [successes,Finset.sum_range_succ]
lemma measurable_successes {Ω : Type*} [MeasurableSpace Ω] (B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n)) (n : ℕ) : Measurable (successes B n) := by
  apply Finset.measurable_fun_sum
  intro k hk
  exact Measurable.ite (hB k) measurable_const measurable_const
lemma measurable_failureWeight {Ω : Type*} [MeasurableSpace Ω] (B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n)) (s : ℝ) (n : ℕ) : Measurable (failureWeight B s n) :=
  (measurable_const.sub (measurable_successes B hB n)).exp
lemma failureWeight_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n)) (s : ℝ) (n : ℕ) :
    Integrable (failureWeight B s n) μ := by
  refine (integrable_const (Real.exp (s/4*n))).mono' (measurable_failureWeight B hB s n).aestronglyMeasurable ?_
  filter_upwards [] with ω
  dsimp only [failureWeight]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (successes_nonneg B n ω)

lemma failureWeight_step {Ω : Type*} (B : ℕ → Set Ω) (s : ℝ) (n : ℕ) (ω : Ω) :
    failureWeight B s (n+1) ω = Real.exp (s/4)*
      (failureWeight B s n ω-(1-Real.exp (-1))*
        (if ω ∈ B n then failureWeight B s n ω else 0)) := by
  rw [failureWeight,successes_succ,Nat.cast_add,Nat.cast_one]
  split_ifs with h
  · have he : s/4*((n:ℝ)+1)-(successes B n ω+1) = s/4+(s/4*n-successes B n ω)+(-1) := by ring
    rw [he,Real.exp_add,Real.exp_add]
    dsimp [failureWeight]
    ring
  · have he : s/4*((n:ℝ)+1)-(successes B n ω+0) = s/4+(s/4*n-successes B n ω) := by ring
    rw [he,Real.exp_add]
    simp only [mul_zero,sub_zero,failureWeight]

lemma failureWeight_contraction {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (s/4)*(1-s*(1-Real.exp (-1))) ≤ Real.exp (-s/4) := by
  have he : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg]
    have h₂ : (2:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h₂
  have h₁ : 1-s*(1-Real.exp (-1)) ≤ 1-s/2 := by nlinarith
  have h₂ : 1-s/2 ≤ Real.exp (-s/2) := by
    have := Real.add_one_le_exp (-s/2)
    linarith
  calc
    Real.exp (s/4)*(1-s*(1-Real.exp (-1))) ≤ Real.exp (s/4)*Real.exp (-s/2) :=
      mul_le_mul_of_nonneg_left (h₁.trans h₂) (Real.exp_pos _).le
    _ = Real.exp (-s/4) := by rw [←Real.exp_add]; congr 1; ring

lemma adaptive_failureWeight_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n))
    {s : ℝ} (hs : 0 ≤ s)
    (hstep : ∀ n, s*(∫ ω, failureWeight B s n ω ∂μ) ≤
      ∫ ω in B n, failureWeight B s n ω ∂μ) (n : ℕ) :
    (∫ ω, failureWeight B s n ω ∂μ) ≤ (Real.exp (-s/4))^n := by
  induction n with
  | zero => simp [failureWeight,successes]
  | succ n ih =>
    have hi := failureWeight_integrable μ B hB s n
    have his := hi.indicator (hB n)
    have hid : (fun ω => if ω ∈ B n then failureWeight B s n ω else 0) =
        (B n).indicator (failureWeight B s n) := by rfl
    have hi' : Integrable (fun ω => if ω ∈ B n then failureWeight B s n ω else 0) μ := by
      rw [hid]
      exact his
    have hEq : (∫ ω, failureWeight B s (n+1) ω ∂μ) = Real.exp (s/4)*
        ((∫ ω, failureWeight B s n ω ∂μ)-(1-Real.exp (-1))*
          ∫ ω in B n, failureWeight B s n ω ∂μ) := by
      simp_rw [failureWeight_step]
      rw [integral_const_mul,integral_sub hi (hi'.const_mul _),integral_const_mul]
      rw [hid,integral_indicator (hB n)]
    have h0 : 0 ≤ 1-Real.exp (-1) := by
      have := Real.exp_le_one_iff.mpr (show (-1:ℝ) ≤ 0 by norm_num)
      linarith
    have hw0 : 0 ≤ ∫ ω, failureWeight B s n ω ∂μ := integral_nonneg fun _ => (Real.exp_pos _).le
    rw [hEq]
    calc
      Real.exp (s/4)*((∫ ω, failureWeight B s n ω ∂μ)-(1-Real.exp (-1))*
          ∫ ω in B n, failureWeight B s n ω ∂μ)
        ≤ Real.exp (s/4)*(1-s*(1-Real.exp (-1)))*(∫ ω, failureWeight B s n ω ∂μ) := by
          have hh := mul_le_mul_of_nonneg_left (hstep n) h0
          nlinarith [Real.exp_pos (s/4)]
      _ ≤ Real.exp (-s/4)*(∫ ω, failureWeight B s n ω ∂μ) :=
        mul_le_mul_of_nonneg_right (failureWeight_contraction hs) hw0
      _ ≤ Real.exp (-s/4)*(Real.exp (-s/4))^n := mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = (Real.exp (-s/4))^(n+1) := by rw [pow_succ]; ring
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def failureSeries {Ω : Type*} (B : ℕ → Set Ω) (s : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (failureWeight B s n ω)

lemma measurable_failureSeries {Ω : Type*} [MeasurableSpace Ω] (B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet (B n)) (s : ℝ) : Measurable (failureSeries B s) :=
  Measurable.tsum fun index => (measurable_failureWeight B hB s index).ennreal_ofReal

lemma failureSeries_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n))
    {s : ℝ} (hs : 0 < s)
    (hstep : ∀ n, s*(∫ ω, failureWeight B s n ω ∂μ) ≤
      ∫ ω in B n, failureWeight B s n ω ∂μ) :
    (∫⁻ ω, failureSeries B s ω ∂μ) ≤ ENNReal.ofReal ((1-Real.exp (-s/4))⁻¹) := by
  have hexp0 := (Real.exp_pos (-s/4)).le
  have hexp1 : Real.exp (-s/4) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum := summable_geometric_of_lt_one hexp0 hexp1
  unfold failureSeries
  rw [lintegral_tsum (fun n => (measurable_failureWeight B hB s n).ennreal_ofReal.aemeasurable)]
  calc
    ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal (failureWeight B s n ω) ∂μ
      ≤ ∑' n : ℕ, ENNReal.ofReal ((Real.exp (-s/4))^n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [←ofReal_integral_eq_lintegral_ofReal (failureWeight_integrable μ B hB s n)
          (ae_of_all _ fun _ => (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal (adaptive_failureWeight_mean μ B hB hs.le hstep n)
    _ = ENNReal.ofReal ((1-Real.exp (-s/4))⁻¹) := by
      rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hexp0 n) hsum,
        tsum_geometric_of_lt_one hexp0 hexp1]

theorem adaptive_failure_excess {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) (hB : ∀ n, MeasurableSet (B n))
    {s : ℝ} (hs : 0 < s)
    (hstep : ∀ n, s*(∫ ω, failureWeight B s n ω ∂μ) ≤
      ∫ ω in B n, failureWeight B s n ω ∂μ) :
    ∃ W : Ω → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
      Integrable (fun ω => Real.exp (W ω)) μ ∧
      (∀ᵐ ω ∂μ, ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W ω) ∧
      (∫ ω, Real.exp (W ω) ∂μ) ≤ 1+(1-Real.exp (-s/4))⁻¹ := by
  let F := failureSeries B s
  have hF : Measurable F := measurable_failureSeries B hB s
  have hmean := failureSeries_mean μ B hB hs hstep
  have hfinite : (∫⁻ ω, F ω ∂μ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmean
  have hae : ∀ᵐ ω ∂μ, F ω ≠ ⊤ := (ae_lt_top hF hfinite).mono fun _ h => h.ne
  have hi : Integrable (fun ω => (F ω).toReal) μ := (integrable_toReal_iff hF.aemeasurable hae).mpr hfinite
  let W := fun ω => Real.log (1+(F ω).toReal)
  have hpos (ω) : 0 < 1+(F ω).toReal := by positivity
  have heq : (fun ω => Real.exp (W ω)) = fun ω => 1+(F ω).toReal := by
    funext ω
    exact Real.exp_log (hpos ω)
  refine ⟨W,(measurable_const.add hF.ennreal_toReal).log,?_,?_,?_,?_⟩
  · intro ω
    exact Real.log_nonneg (by have := ENNReal.toReal_nonneg (a := F ω); linarith)
  · rw [heq]
    exact (integrable_const _).add hi
  · filter_upwards [hae] with ω hω
    intro n
    have hh : failureWeight B s n ω ≤ (F ω).toReal := by
      have := ENNReal.toReal_mono hω (ENNReal.le_tsum (f := fun k => ENNReal.ofReal (failureWeight B s k ω)) n)
      have hn : 0 ≤ failureWeight B s n ω := (Real.exp_pos _).le
      simpa only [ENNReal.toReal_ofReal hn] using this
    have hl := Real.log_le_log (Real.exp_pos (s/4*(n:ℝ)-successes B n ω))
      (hh.trans (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)))
    simpa only [Real.log_exp] using hl
  · rw [heq,integral_add (integrable_const _) hi,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    apply add_le_add le_rfl
    rw [integral_toReal hF.aemeasurable (hae.mono fun _ h => lt_top_iff_ne_top.mpr h)]
    have hp : 0 ≤ (1-Real.exp (-s/4))⁻¹ := by
      apply inv_nonneg.mpr
      have := Real.exp_le_one_iff.mpr (show -s/4 ≤ 0 by linarith)
      linarith
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmean
    simpa only [ENNReal.toReal_ofReal hp] using this
end DirectionalTransience

end

end

end OAI
