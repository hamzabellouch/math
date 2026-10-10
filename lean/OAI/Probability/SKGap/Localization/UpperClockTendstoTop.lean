import Mathlib
import OAI.Probability.SKGap.Localization.PoissonBinomialProbability

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKGapCutoff

lemma upperClock_tendsto_atTop {rate ε : ℝ} (hrate : 0 < rate) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ⌈(1+ε)*(n:ℝ)*cutoffTime rate n⌉₊) atTop atTop := by
  apply tendsto_nat_ceil_atTop.comp
  exact (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith : 0 < 1+ε)).atTop_mul_atTop₀
    (cutoffTime_tendsto_atTop hrate)

lemma upperClock_shifted_time {rate ε q : ℝ} (hrate : 0 < rate) (hε : 0 < ε)
    (hq : 0 < q) (y : ℝ) :
    ∀ᶠ n : ℕ in atTop, (1+ε/2)*cutoffTime rate n ≤
      (q*(⌈(1+ε)*(n:ℝ)*cutoffTime rate n⌉₊:ℝ)+
        y*Real.sqrt (⌈(1+ε)*(n:ℝ)*cutoffTime rate n⌉₊:ℝ))/(q*n) := by
  let M : ℕ → ℕ := fun n => ⌈(1+ε)*(n:ℝ)*cutoffTime rate n⌉₊
  let c := q*ε/(2*(1+ε))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcq : c < q := by
    dsimp [c]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(1+ε))).mpr
    nlinarith
  have hs : Tendsto (fun n => c*Real.sqrt (M n : ℝ)) atTop atTop := by
    exact (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp
      (upperClock_tendsto_atTop hrate hε))).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop 1, hs.eventually_ge_atTop |y|] with n hn hy
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hM : (1+ε)*(n:ℝ)*cutoffTime rate n ≤ (M n:ℝ) := Nat.le_ceil _
  have hsq : Real.sqrt (M n:ℝ)^2 = (M n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have herr : -c*(M n:ℝ) ≤ y*Real.sqrt (M n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hy (Real.sqrt_nonneg (M n:ℝ))
    have hy' := mul_le_mul_of_nonneg_right (neg_abs_le y) (Real.sqrt_nonneg (M n:ℝ))
    nlinarith
  apply (le_div_iff₀ (mul_pos hq hn')).mpr
  have hmain := mul_le_mul_of_nonneg_left hM (sub_pos.mpr hcq).le
  have hid : (q-c)*(1+ε) = q*(1+ε/2) := by
    dsimp [c]
    field_simp
    ring
  change _ ≤ q*(M n:ℝ)+y*Real.sqrt (M n:ℝ)
  calc
    _ = (q-c)*((1+ε)*(n:ℝ)*cutoffTime rate n) := by
      calc
        _ = ((q-c)*(1+ε))*(n:ℝ)*cutoffTime rate n := by rw [hid]; ring
        _ = _ := by ring
    _ ≤ (q-c)*(M n:ℝ) := hmain
    _ ≤ _ := by nlinarith

end SKGapCutoff

namespace SKGapCutoff

abbrev BoundedTVTest (n : ℕ) := Spin n × {f : Observables n // ∀ x, |f x| ≤ 1}

theorem discrete_upper_of_holding {β rate ε q : ℝ} (hrate : 0 < rate)
    (hε : 0 < ε) (hq : 0 < q) (hq1 : q < 1)
    (good : (n : ℕ) → GaussianCoordinates n → Prop)
    (hgood : Tendsto (fun n => disorderLaw β n {g | ¬good n g}) atTop (𝓝 0))
    (hhold : ∀ n, 0 < n → ∀ g, good n g → ∀ x,
      1-q ≤ discreteKernel (sampledInteraction g) 1 x x)
    (hcont : DisorderLimit β
      (fun n J => worstContinuous J ((1+ε/2)*cutoffTime rate n)) 0) :
    DisorderLimit β (fun n J => worstDiscrete J
      ⌈(1+ε)*(n:ℝ)*cutoffTime rate n⌉₊) 0 := by
  let M : ℕ → ℕ := fun n => ⌈(1+ε)*(n:ℝ)*cutoffTime rate n⌉₊
  let a : (n : ℕ) → GaussianCoordinates n → BoundedTVTest n → ℕ → ℝ :=
    fun n g i j => (residualAttempt (sampledInteraction g) q ^ j) i.2.val i.1 -
      gibbsExpectation (sampledInteraction g) i.2.val
  let good' : (n : ℕ) → GaussianCoordinates n → Prop := fun n g => 0 < n ∧ good n g
  have hgood' : Tendsto (fun n => disorderLaw β n {g | ¬good' n g}) atTop (𝓝 0) := by
    apply hgood.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    congr 1
    ext g
    simp only [good',show 0 < n by omega,true_and]
  have hab : ∀ n g, good' n g → ∀ i j, |a n g i j| ≤ 2 := by
    intro n g hg i j
    exact residual_test_bound (sampledInteraction g) hq (hhold n hg.1 g hg.2)
      i.2.val i.2.property i.1 j
  have hp : ∀ y δ : ℝ, 0 < δ → Tendsto (fun n => disorderLaw β n
      {g | good' n g ∧ ∃ i, δ < |∑' j,
        Clock.poissonMass (q*M n+y*Real.sqrt (M n)) j*a n g i j|}) atTop (𝓝 0) := by
    intro y δ hδ
    apply tendsto_const_nhds.squeeze' (hcont (δ/2) (by positivity))
      (Eventually.of_forall (fun _ => zero_le))
    filter_upwards [upperClock_shifted_time hrate hε hq y,eventually_ge_atTop 1] with n hs hn
    have hn' : 0 < n := by omega
    apply measure_mono
    rintro g ⟨_hg,i,hi⟩
    have he := residual_poisson_test hn' (sampledInteraction g) hq.ne'
      (q*(M n:ℝ)+y*Real.sqrt (M n:ℝ)) i.2.val i.1
    change _ < |∑' j, Clock.poissonMass (q*M n+y*Real.sqrt (M n)) j*
      ((residualAttempt (sampledInteraction g) q ^ j) i.2.val i.1-
        gibbsExpectation (sampledInteraction g) i.2.val)| at hi
    rw [he] at hi
    have hb := (continuous_test_bound (sampledInteraction g) _ i.2.val i.2.property i.1).trans
      (mul_le_mul_of_nonneg_left (worstContinuous_mono_time (sampledInteraction g) hs) (by norm_num : (0:ℝ)≤2))
    change δ/2 < |worstContinuous (sampledInteraction g) ((1+ε/2)*cutoffTime rate n)-0|
    rw [sub_zero,abs_of_nonneg (worstContinuous_nonneg _ _)]
    linarith
  have hbin := Clock.poisson_to_binomial_in_probability hq hq1 (by norm_num : (0:ℝ)<2)
    (disorderLaw β) good' hgood' (fun n _ => M n)
    (fun K => ((upperClock_tendsto_atTop hrate hε).eventually_ge_atTop K).mono (fun n hn _ _ => hn)) a hab hp
  intro δ hδ
  apply tendsto_const_nhds.squeeze' (hbin δ hδ) (Eventually.of_forall (fun _ => zero_le))
  apply Eventually.of_forall
  intro n
  apply measure_mono
  intro g hg
  obtain ⟨x,f,hf,he⟩ := worstDiscrete_has_test (sampledInteraction g) (M n)
  refine ⟨(x,⟨f,hf⟩),?_⟩
  change δ < |∑' j, Clock.binomialMass q (M n) j*
    ((residualAttempt (sampledInteraction g) q ^ j) f x-
      gibbsExpectation (sampledInteraction g) f)|
  rw [residual_binomial_test (sampledInteraction g) hq.ne' (M n) f x,he]
  change δ < |worstDiscrete (sampledInteraction g) (M n)-0| at hg
  rw [sub_zero] at hg
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith [abs_nonneg (worstDiscrete (sampledInteraction g) (M n))]

end SKGapCutoff

end

end OAI
