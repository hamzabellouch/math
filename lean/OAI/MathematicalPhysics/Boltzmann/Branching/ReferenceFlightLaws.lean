import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceMinorization
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceAngularCharts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Poisson.Basic

namespace OAI

section

/-! # A finite collision-chart measure with a volume lower bound -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem minorizationChart_measurable : Measurable minorizationChart := by
  unfold minorizationChart incomingChart normalChart NormedSpace.normalize child
  fun_prop

theorem minorizationChart_measure_lower :
    ∃ (U : Set V) (r : ℝ) (K : ℝ≥0), IsOpen U ∧ (0 : V) ∈ U ∧
      U ⊆ ball (0 : V) 1 ∧ 0 < r ∧ 0 < K ∧
      IsFiniteMeasure (volume.restrict U) ∧
      volume.restrict (ball (0 : V) r) ≤
        ((K : ℝ≥0∞)^3) • (volume.restrict U).map minorizationChart := by
  obtain ⟨U,r,K,hU,hU0,hUb,hr,hK,hbound⟩ := minorizationChart_volume_lower
  have hf : IsFiniteMeasure (volume.restrict U) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono hUb) measure_ball_lt_top
  refine ⟨U,r,K,hU,hU0,hUb,hr,hK,hf,?_⟩
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.restrict_apply hs,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply minorizationChart_measurable hs,
    Measure.restrict_apply (minorizationChart_measurable hs)]
  refine (hbound (s ∩ ball 0 r) inter_subset_right).trans ?_
  gcongr 1
  apply measure_mono
  intro x hx
  exact ⟨hx.2.1,hx.1⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Geometric decay of odd observables for the actual velocity chain -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniformized_odd_decay : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧
    ∀ (f : RetainedState → V), Measurable f → (∀ v, f (stateNeg v) = -f v) →
      ∀ M : ℝ, (∀ v, ‖f v‖ ≤ M) → ∀ (n : ℕ) (v : RetainedState),
        ‖chainAverage n f v‖ ≤ (1-ε)^(n/3)*M := by
  obtain ⟨ε,hε,hεsmall,hcontract⟩ := uniformized_three_odd_contraction
  refine ⟨ε,hε,hεsmall,?_⟩
  intro f hf ho M hM
  have hblocks : ∀ (k : ℕ) (v : RetainedState),
      ‖chainAverage (3*k) f v‖ ≤ (1-ε)^k*M := by
    intro k
    induction k with
    | zero => intro v; simpa only [Nat.mul_zero,chainAverage_zero,pow_zero,one_mul] using hM v
    | succ k ih =>
      intro v
      have hh := hcontract (chainAverage (3*k) f) (chainAverage_measurable _ hf)
        (chainAverage_odd _ ho) ((1-ε)^k*M) ih v
      calc
        ‖chainAverage (3*(k+1)) f v‖ = ‖chainAverage 3 (chainAverage (3*k) f) v‖ := by
          rw [show 3*(k+1) = 3*k+3 by omega,chainAverage_add _ _ hf hM]
        _ ≤ (1-ε)*((1-ε)^k*M) := hh
        _ = (1-ε)^(k+1)*M := by rw [pow_succ]; ring
  intro n v
  have hn : 3*(n/3)+n%3 = n := by omega
  calc
    ‖chainAverage n f v‖ = ‖chainAverage (n%3) (chainAverage (3*(n/3)) f) v‖ := by
      nth_rw 1 [← hn]
      rw [chainAverage_add _ _ hf hM]
    _ ≤ (1-ε)^(n/3)*M := chainAverage_bound _ (hblocks (n/3)) v

theorem uniformized_velocity_mean_decay : ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∀ (n : ℕ) (v : RetainedState),
      ‖∫ u : RetainedState, (u : V) ∂(uniformizedKernel^n) v‖ ≤ 5*q^(n/3) := by
  obtain ⟨ε,hε,hεsmall,hdecay⟩ := uniformized_odd_decay
  refine ⟨1-ε,by linarith,by linarith,?_⟩
  intro n v
  have hh := hdecay (Subtype.val : RetainedState → V) measurable_subtype_coe
    (fun _ => rfl) 5 retainedState_norm n v
  simpa only [chainAverage,mul_comm] using hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A geometric bound at every jump count -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniformized_geometric_mean : ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧
    ∀ (n : ℕ) (v : RetainedState),
      ‖∫ u : RetainedState, (u : V) ∂(uniformizedKernel^n) v‖ ≤ C*r^n := by
  obtain ⟨q,hq,hq1,hbound⟩ := uniformized_velocity_mean_decay
  let r := (q+2)/3
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hqr : q ≤ r^3 := by
    have hh := mul_nonneg (sq_nonneg (q-1)) (show 0 ≤ q+8 by linarith)
    dsimp [r]
    nlinarith
  refine ⟨5/r^2,r,by positivity,hr,hr1,?_⟩
  intro n v
  have hp := pow_le_pow_left₀ hq.le hqr (n/3)
  have hrem : r^2 ≤ r^(n%3) := by
    have hh : n%3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases he : n%3
    · simp only [pow_zero]; nlinarith [sq_nonneg r]
    · simp only [pow_one]; nlinarith
    · exact le_rfl
  have hpow : q^(n/3)*r^2 ≤ r^n := by
    calc
      q^(n/3)*r^2 ≤ (r^3)^(n/3)*r^(n%3) :=
        mul_le_mul hp hrem (sq_nonneg _) (pow_nonneg (by positivity) _)
      _ = r^n := by rw [← pow_mul,← pow_add]; congr 1; omega
  have hh : 5*q^(n/3) ≤ (5/r^2)*r^n := by
    rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity : 0 < r^2)]
    nlinarith
  exact (hbound n v).trans hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The constant-rate reference transition law as an actual Poisson mixture -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def countKernel (v : RetainedState) : Kernel ℕ RetainedState where
  toFun n := (uniformizedKernel^n) v
  measurable' := .of_discrete

instance countKernel_isMarkov (v : RetainedState) : IsMarkovKernel (countKernel v) := by
  constructor
  intro n
  change IsProbabilityMeasure ((uniformizedKernel^n) v)
  infer_instance

def poissonKernel (r : ℝ≥0) : Kernel RetainedState RetainedState :=
  Kernel.sum (fun n => Kernel.withDensity (uniformizedKernel^n)
    (fun _ _ => (poissonMeasure r) {n}))

theorem poissonKernel_apply (r : ℝ≥0) (v : RetainedState) :
    poissonKernel r v = (poissonMeasure r).bind (fun n => (uniformizedKernel^n) v) := by
  rw [poissonKernel,Kernel.sum_apply,poissonMeasure,Measure.bind_sum _ _ (.of_discrete)]
  apply congrArg Measure.sum
  funext n
  rw [Kernel.withDensity_apply _ measurable_const,withDensity_const,
    Measure.bind_smul _ _ (.of_discrete),Measure.dirac_bind (.of_discrete),Measure.sum_smul_dirac_singleton]

instance poissonKernel_isMarkov (r : ℝ≥0) : IsMarkovKernel (poissonKernel r) := by
  constructor
  intro v
  constructor
  rw [poissonKernel_apply,Measure.bind_apply MeasurableSet.univ (.of_discrete)]
  simp only [measure_univ,lintegral_const,one_mul]

theorem poissonKernel_average (r : ℝ≥0) (v : RetainedState) {f : RetainedState → V}
    (hf : Measurable f) {M : ℝ} (hM : ∀ u, ‖f u‖ ≤ M) :
    (∫ u, f u ∂poissonKernel r v) = ∫ n, chainAverage n f v ∂poissonMeasure r := by
  have hi : Integrable f (poissonKernel r v) :=
    (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ hM)
  have heq : poissonKernel r v =
      (countKernel v ∘ₖ Kernel.const Unit (poissonMeasure r)) () := by
    rw [poissonKernel_apply,Kernel.comp_apply,Kernel.const_apply]
    rfl
  rw [heq] at hi ⊢
  rw [Kernel.integral_comp hi]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exponential mean-velocity decay for the actual Poisson transition law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ProbabilityTheory Nat

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem poisson_power_integral (r : ℝ≥0) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ n : ℕ, q^n ∂poissonMeasure r) = Real.exp ((r : ℝ)*(q-1)) := by
  have hi : Integrable (fun n : ℕ => q^n) (poissonMeasure r) := by
    apply (integrable_const (1 : ℝ)).mono' (.of_discrete)
    exact ae_of_all _ (fun n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq _)]
      exact pow_le_one₀ hq hq1)
  rw [integral_poissonMeasure' hi]
  simp only [smul_eq_mul]
  have he (n : ℕ) : (Real.exp (-(r : ℝ))*(r : ℝ)^n/(n.factorial : ℝ))*q^n =
      Real.exp (-(r : ℝ))*(((r : ℝ)*q)^n/(n.factorial : ℝ)) := by rw [mul_pow]; ring
  simp_rw [he]
  rw [tsum_mul_left]
  have hs : (∑' n : ℕ, ((r : ℝ)*q)^n/(n.factorial : ℝ)) = Real.exp ((r : ℝ)*q) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ)*q)).tsum_eq
  rw [hs,← Real.exp_add]
  congr 1
  ring

theorem poisson_velocity_mean_decay : ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
    ∀ (r : ℝ≥0) (v : RetainedState),
      ‖∫ u : RetainedState, (u : V) ∂poissonKernel r v‖ ≤ C*Real.exp (-a*(r : ℝ)) := by
  obtain ⟨C,q,hC,hq,hq1,hbound⟩ := uniformized_geometric_mean
  refine ⟨C,1-q,hC,by linarith,?_⟩
  intro r v
  rw [poissonKernel_average r v measurable_subtype_coe retainedState_norm]
  have hi : Integrable (fun n : ℕ => q^n) (poissonMeasure r) := by
    apply (integrable_const (1 : ℝ)).mono' (.of_discrete)
    exact ae_of_all _ (fun n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq.le _)]
      exact pow_le_one₀ hq.le hq1.le)
  calc
    ‖∫ n, chainAverage n (Subtype.val : RetainedState → V) v ∂poissonMeasure r‖ ≤
        ∫ n, C*q^n ∂poissonMeasure r :=
      norm_integral_le_of_norm_le (hi.const_mul C) (ae_of_all _ (fun n => hbound n v))
    _ = C*Real.exp (-(1-q)*(r : ℝ)) := by
      rw [integral_const_mul,poisson_power_integral r hq.le hq1.le]
      congr 2
      ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniformly bounded sums of the expected velocities of the discrete chain -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.ReferenceGeometry

def velocitySum (n : ℕ) (v : RetainedState) : V :=
  ∑ k ∈ Finset.range (n+1), chainAverage k (fun u => (u : V)) v

theorem velocitySum_measurable (n : ℕ) : Measurable (velocitySum n) := by
  unfold velocitySum
  exact Finset.measurable_sum _ fun k _ => chainAverage_measurable k measurable_subtype_coe

theorem velocitySum_bound (n : ℕ) (v : RetainedState) : ‖velocitySum n v‖ ≤ (n+1 : ℕ)*5 := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖chainAverage k (fun u => (u : V)) v‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n+1), (5 : ℝ) :=
      Finset.sum_le_sum fun k _ => chainAverage_bound k retainedState_norm v
    _ = _ := by simp

theorem velocitySum_succ (n : ℕ) (v : RetainedState) :
    velocitySum (n+1) v = (v : V) + ∫ u, velocitySum n u ∂uniformizedKernel v := by
  have hi (k : ℕ) : Integrable (chainAverage k (fun u => (u : V))) (uniformizedKernel v) :=
    (integrable_const (5 : ℝ)).mono' (chainAverage_measurable k measurable_subtype_coe).aestronglyMeasurable
      (ae_of_all _ (chainAverage_bound k retainedState_norm))
  unfold velocitySum
  rw [integral_finsetSum _ (fun k _ => hi k),Finset.sum_range_succ']
  simp only [chainAverage_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [chainAverage,pow_one] using
    chainAverage_add k 1 measurable_subtype_coe retainedState_norm v

theorem velocitySum_uniform_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (n : ℕ) (v : RetainedState), ‖velocitySum n v‖ ≤ B := by
  obtain ⟨C,r,hC,hr,hr1,hmean⟩ := uniformized_geometric_mean
  refine ⟨C/(1-r),by positivity,?_⟩
  intro n v
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖chainAverage k (fun u => (u : V)) v‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n+1), C*r^k := Finset.sum_le_sum fun k _ => hmean k v
    _ = C * ∑ k ∈ Finset.range (n+1), r^k := (Finset.mul_sum _ _ _).symm
    _ ≤ C/(1-r) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ hC.le
      have hs := hasSum_geometric_of_lt_one hr.le hr1
      exact (Summable.sum_le_tsum (Finset.range (n+1)) (fun i _ => pow_nonneg hr.le i) hs.summable).trans_eq hs.tsum_eq

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Chapman–Kolmogorov for the actual Poisson reference transition law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem poissonKernel_lintegral (r : ℝ≥0) (v : RetainedState) {f : RetainedState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ u, f u ∂poissonKernel r v) =
      ∫⁻ n, ∫⁻ u, f u ∂(uniformizedKernel^n) v ∂poissonMeasure r := by
  rw [poissonKernel_apply,Measure.lintegral_bind (.of_discrete) hf.aemeasurable]

theorem poissonKernel_apply_set (r : ℝ≥0) (v : RetainedState) {A : Set RetainedState}
    (hA : MeasurableSet A) : poissonKernel r v A =
      ∫⁻ n, (uniformizedKernel^n) v A ∂poissonMeasure r := by
  rw [poissonKernel_apply,Measure.bind_apply hA (.of_discrete)]

theorem poissonKernel_add (r s : ℝ≥0) : poissonKernel (r+s) = poissonKernel r ∘ₖ poissonKernel s := by
  ext v A hA
  have hf : Measurable (fun p : RetainedState × ℕ => (uniformizedKernel^p.2) p.1 A) :=
    measurable_from_prod_countable_left (fun n => (uniformizedKernel^n).measurable_coe hA)
  calc
    poissonKernel (r+s) v A = ∫⁻ k, (uniformizedKernel^k) v A ∂poissonMeasure (r+s) :=
      poissonKernel_apply_set _ _ hA
    _ = ∫⁻ m, ∫⁻ n, (uniformizedKernel^(m+n)) v A ∂poissonMeasure r ∂poissonMeasure s := by
      rw [show r+s = s+r by exact add_comm _ _,← poissonMeasure_conv_poissonMeasure,
        Measure.lintegral_conv (.of_discrete)]
    _ = ∫⁻ m, ∫⁻ n, ∫⁻ u, (uniformizedKernel^n) u A ∂(uniformizedKernel^m) v
        ∂poissonMeasure r ∂poissonMeasure s := by
      apply lintegral_congr
      intro m
      apply lintegral_congr
      intro n
      exact Kernel.pow_add_apply_eq_lintegral _ _ _ _ hA
    _ = ∫⁻ m, ∫⁻ u, ∫⁻ n, (uniformizedKernel^n) u A ∂poissonMeasure r
        ∂(uniformizedKernel^m) v ∂poissonMeasure s := by
      apply lintegral_congr
      intro m
      exact (lintegral_lintegral_swap hf.aemeasurable).symm
    _ = ∫⁻ m, ∫⁻ u, poissonKernel r u A ∂(uniformizedKernel^m) v ∂poissonMeasure s := by
      simp_rw [poissonKernel_apply_set r _ hA]
    _ = ∫⁻ u, poissonKernel r u A ∂poissonKernel s v :=
      (poissonKernel_lintegral s v ((poissonKernel r).measurable_coe hA)).symm
    _ = (poissonKernel r ∘ₖ poissonKernel s) v A := (Kernel.comp_apply' _ _ _ hA).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Correlations of two actual reference velocities at separated times -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ProbabilityTheory RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def poissonJoint (r s : ℝ≥0) (v : RetainedState) : Measure (RetainedState × RetainedState) :=
  (poissonKernel r v) ⊗ₘ poissonKernel s

instance poissonJoint_isProbability (r s : ℝ≥0) (v : RetainedState) :
    IsProbabilityMeasure (poissonJoint r s v) := by
  constructor
  rw [poissonJoint,Measure.compProd_apply MeasurableSet.univ]
  simp

theorem state_inner_bound (u w : RetainedState) : |inner ℝ (u : V) (w : V)| ≤ 25 := by
  calc
    _ ≤ ‖(u : V)‖*‖(w : V)‖ := abs_real_inner_le_norm _ _
    _ ≤ 5*5 := mul_le_mul (retainedState_norm u) (retainedState_norm w)
      (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem poissonJoint_inner (r s : ℝ≥0) (v : RetainedState) :
    (∫ z : RetainedState × RetainedState, inner ℝ (z.1 : V) (z.2 : V) ∂poissonJoint r s v) =
      ∫ u : RetainedState, inner ℝ (u : V)
        (∫ w : RetainedState, (w : V) ∂poissonKernel s u) ∂poissonKernel r v := by
  have hi : Integrable (fun z : RetainedState × RetainedState => inner ℝ (z.1 : V) (z.2 : V))
      (poissonJoint r s v) := by
    apply (integrable_const (25 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using state_inner_bound z.1 z.2)
  rw [poissonJoint,Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [] with u
  have hw : Integrable (fun w : RetainedState => (w : V)) (poissonKernel s u) :=
    (integrable_const (5 : ℝ)).mono' measurable_subtype_coe.aestronglyMeasurable
      (ae_of_all _ retainedState_norm)
  exact (innerSL ℝ (u : V)).integral_comp_comm hw

theorem poisson_velocity_correlation_decay : ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
    ∀ (r s : ℝ≥0) (v : RetainedState),
      |∫ z : RetainedState × RetainedState, inner ℝ (z.1 : V) (z.2 : V) ∂poissonJoint r s v| ≤
        C*Real.exp (-a*(s : ℝ)) := by
  obtain ⟨C,a,hC,ha,hmean⟩ := poisson_velocity_mean_decay
  refine ⟨5*C,a,by positivity,ha,?_⟩
  intro r s v
  rw [poissonJoint_inner]
  have hb (u : RetainedState) :
      ‖inner ℝ (u : V) (∫ w : RetainedState, (w : V) ∂poissonKernel s u)‖ ≤
        (5*C)*Real.exp (-a*(s : ℝ)) := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖(u : V)‖*‖∫ w : RetainedState, (w : V) ∂poissonKernel s u‖ := abs_real_inner_le_norm _ _
      _ ≤ 5*(C*Real.exp (-a*(s : ℝ))) :=
        mul_le_mul (retainedState_norm u) (hmean s u) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le_const (μ := poissonKernel r v) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Position-preserving jumps and deterministic flights of the reference process -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev FlightState := V × RetainedState

def freeFlight (t : ℝ) (z : FlightState) : FlightState := (z.1+t • (z.2 : V),z.2)

theorem freeFlight_measurable : Measurable (fun p : ℝ × FlightState => freeFlight p.1 p.2) := by
  unfold freeFlight
  fun_prop

def freeFlightKernel (t : ℝ) : Kernel FlightState FlightState :=
  Kernel.deterministic (freeFlight t) (freeFlight_measurable.comp (measurable_const.prodMk measurable_id))

instance freeFlightKernel_isMarkov (t : ℝ) : IsMarkovKernel (freeFlightKernel t) := inferInstanceAs
  (IsMarkovKernel (Kernel.deterministic (freeFlight t) _))

def flightJump : Kernel FlightState FlightState :=
  (Kernel.id ×ₖ (uniformizedKernel.comap Prod.snd measurable_snd)).map
    (fun p : FlightState × RetainedState => (p.1.1,p.2))

instance flightJump_isMarkov : IsMarkovKernel flightJump := by
  unfold flightJump
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem flightJump_apply (z : FlightState) :
    flightJump z = (uniformizedKernel z.2).map (fun v => (z.1,v)) := by
  ext A hA
  have hf : Measurable (fun p : FlightState × RetainedState => (p.1.1,p.2)) := by fun_prop
  rw [flightJump,Kernel.map_apply' _ hf z hA,Kernel.id_prod_apply' _ z (hf hA),
    Kernel.comap_apply,Measure.map_apply (by fun_prop) hA]
  rfl

theorem freeFlightKernel_add (s t : ℝ) :
    freeFlightKernel (s+t) = freeFlightKernel s ∘ₖ freeFlightKernel t := by
  unfold freeFlightKernel
  rw [Kernel.deterministic_comp_deterministic]
  congr 1
  funext z
  ext1
  · simp only [freeFlight,Function.comp_apply,add_smul]
    module
  · rfl

theorem freeFlightKernel_zero : freeFlightKernel 0 = Kernel.id := by
  ext z A hA
  simp only [freeFlightKernel,Kernel.deterministic_apply,Kernel.id_apply]
  congr 1
  simp [freeFlight]

theorem flightJump_velocity : flightJump.map Prod.snd =
    uniformizedKernel.comap (Prod.snd : FlightState → RetainedState) measurable_snd := by
  ext1 z
  rw [Kernel.map_apply _ measurable_snd,flightJump_apply,
    Measure.map_map measurable_snd (by fun_prop),Kernel.comap_apply]
  change (uniformizedKernel z.2).map id = _
  rw [Measure.map_id]

theorem freeFlight_velocity (t : ℝ) : (freeFlightKernel t).map Prod.snd =
    Kernel.deterministic (Prod.snd : FlightState → RetainedState) measurable_snd := by
  ext z A hA
  rw [Kernel.map_apply' _ measurable_snd _ hA,freeFlightKernel,Kernel.deterministic_apply,
    Kernel.deterministic_apply,Measure.dirac_apply' _ (measurable_snd hA),Measure.dirac_apply' _ hA]
  rfl

theorem freeFlight_displacement (t : ℝ) (z : FlightState) :
    ‖(freeFlight t z).1-z.1‖ ≤ 5*|t| := by
  simp only [freeFlight,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left (retainedState_norm z.2) (abs_nonneg t)
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lebesgue waiting-time choices for finite collision histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev TimeFlightState := ℝ × FlightState

def waitingDensity (p : TimeFlightState) (s : ℝ) : ℝ≥0∞ := (Ioc 0 p.1).indicator 1 s

theorem waitingDensity_measurable : Measurable (Function.uncurry waitingDensity) := by
  let D : Set (TimeFlightState × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ q.1.1}
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst.fst)
  exact (measurable_const.indicator hD : Measurable (D.indicator (fun _ => (1 : ℝ≥0∞))))

def waitingTime : Kernel TimeFlightState ℝ :=
  Kernel.withDensity (Kernel.const TimeFlightState (volume : Measure ℝ)) waitingDensity

instance waitingTime_isSFinite : IsSFiniteKernel waitingTime := by
  apply Kernel.IsSFiniteKernel.withDensity
  intro p s
  by_cases h : s ∈ Ioc 0 p.1 <;> simp [waitingDensity,h]

theorem waitingTime_apply (p : TimeFlightState) : waitingTime p = volume.restrict (Ioc 0 p.1) := by
  rw [waitingTime,Kernel.withDensity_apply _ waitingDensity_measurable,Kernel.const_apply]
  exact withDensity_indicator_one measurableSet_Ioc

theorem waitingTime_mass (p : TimeFlightState) : waitingTime p univ = ENNReal.ofReal p.1 := by
  rw [waitingTime_apply,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]

def advanceState (p : TimeFlightState) (s : ℝ) (u : RetainedState) : TimeFlightState :=
  (p.1-s,((freeFlight s p.2).1,u))

theorem advanceState_measurable :
    Measurable (fun q : (TimeFlightState × ℝ) × RetainedState => advanceState q.1.1 q.1.2 q.2) := by
  unfold advanceState freeFlight
  fun_prop

def jumpAfterWait : Kernel (TimeFlightState × ℝ) TimeFlightState :=
  (Kernel.id ×ₖ uniformizedKernel.comap (fun q : TimeFlightState × ℝ => q.1.2.2)
    (by fun_prop)).map (fun q => advanceState q.1.1 q.1.2 q.2)

instance jumpAfterWait_isMarkov : IsMarkovKernel jumpAfterWait :=
  Kernel.IsMarkovKernel.map _ advanceState_measurable

def historyStep : Kernel TimeFlightState TimeFlightState :=
  jumpAfterWait ∘ₖ (Kernel.id ×ₖ waitingTime)

instance historyStep_isSFinite : IsSFiniteKernel historyStep := by unfold historyStep; infer_instance

theorem jumpAfterWait_lintegral (q : TimeFlightState × ℝ) {f : TimeFlightState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ p, f p ∂jumpAfterWait q) =
      ∫⁻ u, f (advanceState q.1 q.2 u) ∂uniformizedKernel q.1.2.2 := by
  rw [jumpAfterWait,Kernel.lintegral_map _ advanceState_measurable q hf]
  simpa only [Function.comp_def,Kernel.comap_apply] using!
    Kernel.lintegral_id_prod (hf.comp advanceState_measurable)
      (uniformizedKernel.comap (fun q : TimeFlightState × ℝ => q.1.2.2) (by fun_prop)) q

theorem historyStep_lintegral (p : TimeFlightState) {f : TimeFlightState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ q, f q ∂historyStep p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u, f (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  rw [historyStep,Kernel.lintegral_comp _ _ _ hf,
    Kernel.lintegral_id_prod (hf.lintegral_kernel (κ := jumpAfterWait))]
  simp_rw [jumpAfterWait_lintegral _ hf]
  rw [waitingTime_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual finite free-flight and collision-history kernels -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def finishFlight (p : TimeFlightState) : FlightState := freeFlight p.1 p.2

theorem finishFlight_measurable : Measurable finishFlight := freeFlight_measurable

instance historyStep_pow_isSFinite (n : ℕ) : IsSFiniteKernel (historyStep^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    have heq : historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep := by
      simpa only [pow_one] using Kernel.pow_add historyStep n 1
    rw [heq]
    let _ := ih
    infer_instance

def historyKernel (n : ℕ) : Kernel TimeFlightState FlightState :=
  (historyStep^n).map finishFlight

instance historyKernel_isSFinite (n : ℕ) : IsSFiniteKernel (historyKernel n) := by
  unfold historyKernel
  infer_instance

theorem historyKernel_zero : historyKernel 0 = Kernel.deterministic finishFlight finishFlight_measurable := by
  unfold historyKernel
  change Kernel.id.map finishFlight = _
  exact Kernel.id_map finishFlight_measurable

theorem historyKernel_succ_lintegral (n : ℕ) (p : TimeFlightState) {f : FlightState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ z, f z ∂historyKernel (n+1) p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u, ∫⁻ z, f z ∂historyKernel n (advanceState p s u)
        ∂uniformizedKernel p.2.2 := by
  have hs : historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep := by
    simpa only [pow_one] using Kernel.pow_add historyStep n 1
  have hg : Measurable (fun q : TimeFlightState => ∫⁻ w, f (finishFlight w) ∂(historyStep^n) q) :=
    (hf.comp finishFlight_measurable).lintegral_kernel
  calc
    (∫⁻ z, f z ∂historyKernel (n+1) p) =
        ∫⁻ q, ∫⁻ w, f (finishFlight w) ∂(historyStep^n) q ∂historyStep p := by
      rw [historyKernel,hs,Kernel.lintegral_map _ finishFlight_measurable _ hf]
      exact Kernel.lintegral_comp _ _ _ (hf.comp finishFlight_measurable)
    _ = ∫⁻ s in Ioc 0 p.1, ∫⁻ u, ∫⁻ w, f (finishFlight w)
        ∂(historyStep^n) (advanceState p s u) ∂uniformizedKernel p.2.2 := historyStep_lintegral p hg
    _ = _ := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro u
      exact (Kernel.lintegral_map _ finishFlight_measurable _ hf).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exact time-simplex factor for a fixed number of collisions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def simplexTime (n : ℕ) (T : ℝ) : ℝ≥0∞ := ENNReal.ofReal (T^n/(n.factorial : ℝ))

theorem simplexTime_ne_top (n : ℕ) (T : ℝ) : simplexTime n T ≠ ⊤ := ENNReal.ofReal_ne_top

theorem simplexTime_zero (T : ℝ) : simplexTime 0 T = 1 := by simp [simplexTime]

theorem simplexTime_integral (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ s in Ioc 0 T, simplexTime n (T-s)) = simplexTime (n+1) T := by
  let f : ℝ → ℝ := fun s => (T-s)^n/(n.factorial : ℝ)
  have hi : IntegrableOn f (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      ((show Continuous f by dsimp [f]; fun_prop).intervalIntegrable 0 T)
  change (∫⁻ s in Ioc 0 T, ENNReal.ofReal (f s)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← intervalIntegral.integral_of_le hT]
    change ENNReal.ofReal (∫ s in (0 : ℝ)..T, (T-s)^n/(n.factorial : ℝ)) = _
    rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n),
      integral_pow]
    simp only [sub_self,sub_zero,zero_pow (Nat.succ_ne_zero n),simplexTime,
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    congr 1
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hs.2) _) (Nat.cast_nonneg _)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The first two time moments on a collision simplex -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def simplexVolume (n : ℕ) (T : ℝ) : ℝ := T^n/(n.factorial : ℝ)

theorem simplexVolume_nonneg (n : ℕ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ simplexVolume n T := by
  unfold simplexVolume
  positivity

theorem simplexTime_toReal (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (simplexTime n T).toReal = simplexVolume n T :=
  ENNReal.toReal_ofReal (simplexVolume_nonneg n hT)

theorem simplexVolume_continuous (n : ℕ) : Continuous (simplexVolume n) := by
  unfold simplexVolume
  fun_prop

theorem simplexVolume_step (n : ℕ) (T : ℝ) :
    (n+1 : ℝ)*simplexVolume (n+1) T = T*simplexVolume n T := by
  simp only [simplexVolume,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp

theorem integral_simplexVolume (n : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, simplexVolume n (T-s)) = simplexVolume (n+1) T := by
  simp only [simplexVolume,intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n),integral_pow]
  simp only [sub_self,sub_zero,zero_pow (Nat.succ_ne_zero n),Nat.factorial_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

theorem integral_time_simplexVolume (n : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, s*simplexVolume n (T-s)) = simplexVolume (n+2) T := by
  have hp (s : ℝ) : s*simplexVolume n (T-s) =
      T*simplexVolume n (T-s)-(n+1 : ℝ)*simplexVolume (n+1) (T-s) := by
    rw [simplexVolume_step]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_simplexVolume,integral_simplexVolume]
  · have h := simplexVolume_step (n+1) T
    push_cast at h
    nlinarith
  · exact ((simplexVolume_continuous n).comp (by fun_prop)).const_mul T |>.intervalIntegrable _ _
  · exact ((simplexVolume_continuous (n+1)).comp (by fun_prop)).const_mul (n+1 : ℝ) |>.intervalIntegrable _ _

theorem integral_time_sq_simplexVolume (n : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, s^2*simplexVolume n (T-s)) = 2*simplexVolume (n+3) T := by
  have hp (s : ℝ) : s^2*simplexVolume n (T-s) =
      T*(s*simplexVolume n (T-s))-(n+1 : ℝ)*(s*simplexVolume (n+1) (T-s)) := by
    rw [mul_left_comm (n+1 : ℝ) s, simplexVolume_step]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_time_simplexVolume,integral_time_simplexVolume]
  · have h := simplexVolume_step (n+2) T
    push_cast at h
    nlinarith
  · exact (show Continuous (fun s : ℝ => T*(s*simplexVolume n (T-s))) by
      unfold simplexVolume; fun_prop).intervalIntegrable _ _
  · exact (show Continuous (fun s : ℝ => (n+1 : ℝ)*(s*simplexVolume (n+1) (T-s))) by
      unfold simplexVolume; fun_prop).intervalIntegrable _ _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Velocity marginal and total mass of each actual flight history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyKernel_velocity_lintegral (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1)
    {f : RetainedState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z.2 ∂historyKernel n p) =
      simplexTime n p.1 * ∫⁻ u, f u ∂(uniformizedKernel^n) p.2.2 := by
  induction n generalizing p with
  | zero =>
    rw [historyKernel_zero,Kernel.deterministic_apply,lintegral_dirac' (finishFlight p) (show Measurable (fun z : FlightState => f z.2) from hf.comp measurable_snd)]
    simp only [simplexTime_zero,one_mul,finishFlight,freeFlight,pow_zero]
    change f p.2.2 = ∫⁻ u, f u ∂Kernel.id p.2.2
    rw [Kernel.id_apply,lintegral_dirac' _ hf]
  | succ n ih =>
    rw [historyKernel_succ_lintegral n p (f := fun z => f z.2) (hf.comp measurable_snd)]
    have hpow : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    calc
      (∫⁻ s in Ioc 0 p.1, ∫⁻ u, ∫⁻ z, f z.2 ∂historyKernel n (advanceState p s u)
          ∂uniformizedKernel p.2.2) =
        ∫⁻ s in Ioc 0 p.1, simplexTime n (p.1-s) *
          ∫⁻ u, ∫⁻ w, f w ∂(uniformizedKernel^n) u ∂uniformizedKernel p.2.2 := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        simp_rw [ih _ (show 0 ≤ (advanceState p s _).1 from sub_nonneg.mpr hs.2)]
        exact lintegral_const_mul' _ _ (simplexTime_ne_top _ _)
      _ = (∫⁻ s in Ioc 0 p.1, simplexTime n (p.1-s)) *
          ∫⁻ u, f u ∂(uniformizedKernel^(n+1)) p.2.2 := by
        rw [hpow,Kernel.lintegral_comp _ _ _ hf]
        exact lintegral_mul_const _ (by unfold simplexTime; fun_prop)
      _ = _ := by rw [simplexTime_integral n hT]

theorem historyKernel_velocity_map (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    (historyKernel n p).map Prod.snd = simplexTime n p.1 • (uniformizedKernel^n) p.2.2 := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA,Measure.smul_apply,smul_eq_mul]
  have h := historyKernel_velocity_lintegral n p hT (f := A.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hA)
  change (∫⁻ z, (Prod.snd ⁻¹' A).indicator 1 z ∂historyKernel n p) =
    simplexTime n p.1 * ∫⁻ u, A.indicator 1 u ∂(uniformizedKernel^n) p.2.2 at h
  rw [lintegral_indicator_one (measurable_snd hA),lintegral_indicator_one hA] at h
  exact h

theorem historyKernel_mass (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    historyKernel n p univ = simplexTime n p.1 := by
  have h := historyKernel_velocity_lintegral n p hT (measurable_const (a := (1 : ℝ≥0∞)))
  simpa only [lintegral_const,one_mul,measure_univ,mul_one] using h

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual free-flight law with a fixed Poisson collision rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def flightWeight (rate T : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rate : ℝ)*T) * (rate : ℝ)^n)

theorem flightWeight_simplexTime (rate T : ℝ≥0) (n : ℕ) :
    flightWeight rate T n * simplexTime n T = poissonMeasure (rate*T) {n} := by
  rw [flightWeight,simplexTime,← ENNReal.ofReal_mul (by positivity),poissonMeasure_singleton]
  congr 1
  simp only [NNReal.coe_mul,neg_mul,mul_pow]
  ring

def flightKernel (rate T : ℝ≥0) : Kernel FlightState FlightState :=
  Kernel.sum (fun n => Kernel.withDensity
    ((historyKernel n).comap (fun z => ((T : ℝ),z)) (by fun_prop))
    (fun _ _ => flightWeight rate T n))

instance flightKernel_isSFinite (rate T : ℝ≥0) : IsSFiniteKernel (flightKernel rate T) := by
  unfold flightKernel
  have hi (n : ℕ) : IsSFiniteKernel (Kernel.withDensity
      ((historyKernel n).comap (fun z => ((T : ℝ),z)) (by fun_prop))
      (fun _ _ => flightWeight rate T n)) :=
    by
      apply Kernel.IsSFiniteKernel.withDensity
      intro p q
      exact ENNReal.ofReal_ne_top
  infer_instance

theorem flightKernel_apply (rate T : ℝ≥0) (z : FlightState) :
    flightKernel rate T z =
      Measure.sum (fun n => flightWeight rate T n • historyKernel n ((T : ℝ),z)) := by
  rw [flightKernel,Kernel.sum_apply]
  congr 1
  funext n
  rw [Kernel.withDensity_apply _ measurable_const,withDensity_const,Kernel.comap_apply]

theorem flightKernel_velocity_lintegral (rate T : ℝ≥0) (z : FlightState)
    {f : RetainedState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, f w.2 ∂flightKernel rate T z) = ∫⁻ u, f u ∂poissonKernel (rate*T) z.2 := by
  rw [flightKernel_apply,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure,smul_eq_mul]
  simp_rw [historyKernel_velocity_lintegral _ ((T : ℝ),z) T.coe_nonneg hf]
  simp_rw [← mul_assoc,flightWeight_simplexTime]
  rw [poissonKernel_lintegral _ _ hf,poissonMeasure,lintegral_sum_measure]
  congr 1
  funext n
  rw [lintegral_smul_measure,lintegral_dirac,Measure.sum_smul_dirac_singleton,smul_eq_mul]

instance flightKernel_isMarkov (rate T : ℝ≥0) : IsMarkovKernel (flightKernel rate T) := by
  constructor
  intro z
  constructor
  have h := flightKernel_velocity_lintegral rate T z (measurable_const (a := (1 : ℝ≥0∞)))
  simpa only [lintegral_const,one_mul,measure_univ] using h

theorem flightKernel_velocity_map (rate T : ℝ≥0) (z : FlightState) :
    (flightKernel rate T z).map Prod.snd = poissonKernel (rate*T) z.2 := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA]
  have h := flightKernel_velocity_lintegral rate T z
    (f := A.indicator 1) (measurable_const.indicator hA)
  change (∫⁻ w, (Prod.snd ⁻¹' A).indicator 1 w ∂flightKernel rate T z) =
    ∫⁻ u, A.indicator 1 u ∂poissonKernel (rate*T) z.2 at h
  rw [lintegral_indicator_one (measurable_snd hA),lintegral_indicator_one hA] at h
  exact h

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Jointly measurable flight laws with remaining time as a kernel input -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def realFlightWeight (rate : ℝ≥0) (n : ℕ) (T : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(rate : ℝ)*T)*(rate : ℝ)^n)

def flightFamily (rate : ℝ≥0) : Kernel TimeFlightState FlightState :=
  Kernel.sum (fun n => Kernel.withDensity (historyKernel n)
    (fun p _ => realFlightWeight rate n p.1))

instance flightFamily_isSFinite (rate : ℝ≥0) : IsSFiniteKernel (flightFamily rate) := by
  unfold flightFamily
  have hi (n : ℕ) : IsSFiniteKernel (Kernel.withDensity (historyKernel n)
      (fun p _ => realFlightWeight rate n p.1)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p z
    exact ENNReal.ofReal_ne_top
  infer_instance

theorem realFlightWeight_measurable (rate : ℝ≥0) (n : ℕ) :
    Measurable (Function.uncurry (fun (p : TimeFlightState) (_ : FlightState) => realFlightWeight rate n p.1)) := by
  unfold realFlightWeight
  fun_prop

theorem flightFamily_apply (rate : ℝ≥0) (p : TimeFlightState) :
    flightFamily rate p = Measure.sum (fun n => realFlightWeight rate n p.1 • historyKernel n p) := by
  rw [flightFamily,Kernel.sum_apply]
  congr 1
  funext n
  rw [Kernel.withDensity_apply _ (realFlightWeight_measurable rate n),withDensity_const]

theorem flightFamily_eq (rate T : ℝ≥0) (z : FlightState) :
    flightFamily rate ((T : ℝ),z) = flightKernel rate T z := by
  rw [flightFamily_apply,flightKernel_apply]
  rfl

theorem flightFamily_lintegral (rate : ℝ≥0) (p : TimeFlightState) (f : FlightState → ℝ≥0∞) :
    (∫⁻ z, f z ∂flightFamily rate p) =
      ∑' n, realFlightWeight rate n p.1 * ∫⁻ z, f z ∂historyKernel n p := by
  rw [flightFamily_apply,lintegral_sum_measure]
  simp only [lintegral_smul_measure,smul_eq_mul]

theorem realFlightWeight_succ (rate : ℝ≥0) (n : ℕ) (T s : ℝ) :
    realFlightWeight rate (n+1) T = ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) *
      realFlightWeight rate n (T-s) := by
  unfold realFlightWeight
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : Real.exp (-(rate : ℝ)*s)*Real.exp (-(rate : ℝ)*(T-s)) =
      Real.exp (-(rate : ℝ)*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [pow_succ]
  calc
    _ = (rate : ℝ)*((Real.exp (-(rate : ℝ)*s)*Real.exp (-(rate : ℝ)*(T-s)))*(rate : ℝ)^n) := by
      rw [he]
      ring
    _ = _ := by ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The first-event renewal identity for the actual reference flight law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weighted_history_succ_lintegral (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    realFlightWeight rate (n+1) p.1 * (∫⁻ z, f z ∂historyKernel (n+1) p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u,
        ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) *
          (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))
        ∂uniformizedKernel p.2.2 := by
  have hw : realFlightWeight rate (n+1) p.1 ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [historyKernel_succ_lintegral n p hf,← lintegral_const_mul' _ _ hw]
  apply lintegral_congr
  intro s
  rw [← lintegral_const_mul' _ _ hw]
  apply lintegral_congr
  intro u
  rw [realFlightWeight_succ,mul_assoc]

theorem flightFamily_first_event (rate : ℝ≥0) (p : TimeFlightState)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂flightFamily rate p) =
      ENNReal.ofReal (Real.exp (-(rate : ℝ)*p.1))*f (finishFlight p) +
      ∫⁻ s in Ioc 0 p.1, ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) *
        ∫⁻ u, ∫⁻ z, f z ∂flightFamily rate (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  let a : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s))
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hadv : Measurable (fun q : ℝ × RetainedState => advanceState p q.1 q.2) := by
    unfold advanceState freeFlight
    fun_prop
  have hb (n : ℕ) : Measurable (fun q : ℝ × RetainedState => a q.1 *
      (realFlightWeight rate n (p.1-q.1) * ∫⁻ z, f z ∂historyKernel n (advanceState p q.1 q.2))) := by
    apply (ha.comp measurable_fst).mul
    apply Measurable.mul
    · unfold realFlightWeight
      fun_prop
    · exact (hf.lintegral_kernel (κ := historyKernel n)).comp hadv
  rw [flightFamily_lintegral,tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · rw [historyKernel_zero,Kernel.deterministic_apply,lintegral_dirac' _ hf]
    simp [realFlightWeight]
  · simp_rw [weighted_history_succ_lintegral rate _ p hf]
    change (∑' n, ∫⁻ s in Ioc 0 p.1, ∫⁻ u, a s *
      (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))
      ∂uniformizedKernel p.2.2) = _
    rw [← lintegral_tsum (fun n => (hb n).lintegral_prod_right'.aemeasurable)]
    apply lintegral_congr
    intro s
    have hs (n : ℕ) : Measurable (fun u : RetainedState => a s *
        (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))) :=
      (hb n).comp (measurable_const.prodMk measurable_id)
    change (∑' n, ∫⁻ u, a s *
      (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))
      ∂uniformizedKernel p.2.2) = _
    rw [← lintegral_tsum (fun n => (hs n).aemeasurable)]
    simp_rw [ENNReal.tsum_mul_left]
    have hi (u : RetainedState) :
        (∑' n, realFlightWeight rate n (p.1-s) *
          ∫⁻ z, f z ∂historyKernel n (advanceState p s u)) =
          ∫⁻ z, f z ∂flightFamily rate (advanceState p s u) :=
      (flightFamily_lintegral rate (advanceState p s u) f).symm
    simp_rw [hi]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exponential first-event kernel on remaining-time flight states -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def renewalDensity (rate : ℝ≥0) (p q : TimeFlightState) : ℝ≥0∞ :=
  ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*(p.1-q.1)))

theorem renewalDensity_measurable (rate : ℝ≥0) : Measurable (Function.uncurry (renewalDensity rate)) := by
  unfold renewalDensity
  fun_prop

def renewalStep (rate : ℝ≥0) : Kernel TimeFlightState TimeFlightState :=
  Kernel.withDensity historyStep (renewalDensity rate)

instance renewalStep_isSFinite (rate : ℝ≥0) : IsSFiniteKernel (renewalStep rate) := by
  unfold renewalStep
  apply Kernel.IsSFiniteKernel.withDensity
  intro p q
  exact ENNReal.ofReal_ne_top

theorem renewalStep_lintegral (rate : ℝ≥0) (p : TimeFlightState)
    {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂renewalStep rate p) =
      ∫⁻ s in Ioc 0 p.1, ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s))*
        ∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  rw [renewalStep,Kernel.lintegral_withDensity _ (renewalDensity_measurable rate) _ hF,
    historyStep_lintegral p]
  · apply lintegral_congr
    intro s
    have he (u : RetainedState) : renewalDensity rate p (advanceState p s u) =
        ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) := by
      simp only [renewalDensity,advanceState,sub_sub_cancel]
    simp_rw [he]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · exact ((renewalDensity_measurable rate).comp (measurable_const.prodMk measurable_id)).mul hF

theorem renewalStep_le (rate : ℝ≥0) (p : TimeFlightState) :
    renewalStep rate p ≤ ENNReal.ofReal (rate : ℝ) • historyStep p := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [← lintegral_indicator_one hA,renewalStep_lintegral rate p (F := A.indicator 1) (measurable_const.indicator hA),
    Measure.smul_apply,smul_eq_mul,← lintegral_indicator_one hA,
    historyStep_lintegral p (f := A.indicator 1) (measurable_const.indicator hA),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_right rate.coe_nonneg
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr rate.coe_nonneg) hs.1.le))

theorem flightFamily_renewal (rate : ℝ≥0) (p : TimeFlightState)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂flightFamily rate p) =
      ENNReal.ofReal (Real.exp (-(rate : ℝ)*p.1))*f (finishFlight p) +
        ∫⁻ q, ∫⁻ z, f z ∂flightFamily rate q ∂renewalStep rate p := by
  rw [renewalStep_lintegral rate p (hf.lintegral_kernel)]
  exact flightFamily_first_event rate p hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Factorial remainder bounds for the actual first-event kernel -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance renewalStep_pow_isSFinite (rate : ℝ≥0) (n : ℕ) : IsSFiniteKernel (((renewalStep rate)^n)) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate by
      simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1]
    let _ := ih
    infer_instance

theorem renewalStep_power_le (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState) :
    ((renewalStep rate)^n) p ≤ (ENNReal.ofReal (rate : ℝ))^n • (historyStep^n) p := by
  induction n generalizing p with
  | zero => simp only [pow_zero,one_smul]; exact le_rfl
  | succ n ih =>
    have hh : ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate := by
      simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1
    have hg : historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep := by
      simpa only [pow_one] using Kernel.pow_add historyStep n 1
    apply Measure.le_iff.mpr
    intro A hA
    rw [hh,hg,Kernel.comp_apply' _ _ _ hA,Measure.smul_apply,smul_eq_mul,
      Kernel.comp_apply' _ _ _ hA]
    calc
      _ ≤ ∫⁻ q, (ENNReal.ofReal (rate : ℝ))^n * (historyStep^n) q A
          ∂(ENNReal.ofReal (rate : ℝ) • historyStep p) := by
        apply lintegral_mono' (renewalStep_le rate p)
        intro q
        exact ih q A
      _ = _ := by
        rw [lintegral_smul_measure,lintegral_const_mul' _ _
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),pow_succ]
        simp only [smul_eq_mul]
        ac_rfl

theorem historyStep_power_mass (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    (historyStep^n) p univ = simplexTime n p.1 := by
  have hh := historyKernel_mass n p hT
  rw [historyKernel,Kernel.map_apply' _ finishFlight_measurable _ MeasurableSet.univ,preimage_univ] at hh
  exact hh

theorem renewalStep_power_mass_bound (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ((renewalStep rate)^n) p univ ≤ ENNReal.ofReal (((rate : ℝ)*p.1)^n/(n.factorial : ℝ)) := by
  have hh := renewalStep_power_le rate n p univ
  rw [Measure.smul_apply,smul_eq_mul,historyStep_power_mass n p hT,simplexTime,
    ← ENNReal.ofReal_pow rate.coe_nonneg,← ENNReal.ofReal_mul (by positivity)] at hh
  convert hh using 1
  rw [mul_pow]
  congr 1
  ring

theorem renewalStep_remainder_tendsto (rate : ℝ≥0) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    Tendsto (fun n : ℕ => ((renewalStep rate)^n) p univ) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => ENNReal.ofReal (((rate : ℝ)*p.1)^n/(n.factorial : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (FloorSemiring.tendsto_pow_div_factorial_atTop ((rate : ℝ)*p.1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => zero_le) (fun n => renewalStep_power_mass_bound rate n p hT)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # First-event iterations stay inside the initial time interval -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyStep_time_support (p : TimeFlightState) (_hT : 0 ≤ p.1) :
    ∀ᵐ q ∂historyStep p, q.1 ∈ Icc 0 p.1 := by
  let A : Set TimeFlightState := {q | q.1 ∉ Icc 0 p.1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  change historyStep p A = 0
  rw [← lintegral_indicator_one hA,historyStep_lintegral p (f := A.indicator 1)
    (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply lintegral_eq_zero_of_ae_eq_zero
  apply ae_of_all
  intro u
  have hq : (advanceState p s u).1 ∈ Icc 0 p.1 :=
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1.le⟩
  exact indicator_of_notMem (show advanceState p s u ∉ A from not_not.mpr hq) 1

theorem renewalStep_time_support (rate : ℝ≥0) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ∀ᵐ q ∂renewalStep rate p, q.1 ∈ Icc 0 p.1 :=
  (Measure.absolutelyContinuous_of_le_smul (renewalStep_le rate p)).ae_le (historyStep_time_support p hT)

theorem renewalStep_power_time_support (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ∀ᵐ q ∂((renewalStep rate)^n) p, q.1 ∈ Icc 0 p.1 := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,ae_dirac_iff (by measurability)]
    exact ⟨hT,le_rfl⟩
  | succ n ih =>
    rw [show ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate by
      simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1]
    apply Kernel.ae_comp_of_ae_ae (by measurability)
    filter_upwards [renewalStep_time_support rate p hT] with q hq
    filter_upwards [ih q hq.1] with w hw
    exact ⟨hw.1,hw.2.trans hq.2⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
