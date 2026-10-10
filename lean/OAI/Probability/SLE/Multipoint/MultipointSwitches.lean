import OAI.Probability.SLE.Stochastic.BrownianOptionalIntervals
import OAI.Probability.SLE.Multipoint.MultipointAngular

namespace OAI

/-! Finite switching for the regularized multipoint product. Smooth
pieces may change at bounded stopping times, provided the jumps are
downward. A completed factor can therefore remain constant on all later
pieces without any condition on its subsequent lifetime. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators

namespace SLEExactGauge

/-- At a switching time the active/completed pattern has only finitely
many possibilities. Apply the conditional interval estimate on each
past-measurable branch and sum. The branch formula also covers several
simultaneous switches. -/
theorem brownian_finite_branch_optional_interval_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet[hσ.measurableSpace] (A i))
    (K : ι → ℝ≥0) (F a : ι → ℝ≥0 → Ω → ℝ → ℝ)
    (hF : ∀ i ∈ s, SmoothTimeBrownianField B hm (K i) (F i) (a i))
    (hdrift : ∀ i ∈ s, ∀ ω ∈ A i, ∀ u,
      (σ ω : ℝ) ≤ u → u < (τ ω : ℝ) → brownianFieldDrift B (F i) (a i) u ω ≤ 0) :
    (∫ ω, ∑ i ∈ s, (A i).indicator
      (fun ω => F i (τ ω) ω (B (τ ω) ω)) ω ∂P) ≤
    ∫ ω, ∑ i ∈ s, (A i).indicator
      (fun ω => F i (σ ω) ω (B (σ ω) ω)) ω ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hAi (i : ι) (hi : i ∈ s) : MeasurableSet (A i) :=
    hσ.measurableSpace_le _ (hA i hi)
  have hleft (i : ι) (hi : i ∈ s) : Integrable ((A i).indicator
      (fun ω => F i (τ ω) ω (B (τ ω) ω))) P :=
    ((hF i hi).eval_stopped_integrable hBm (stopping_time_measurable_nnreal hτ)).indicator
      (hAi i hi)
  have hright (i : ι) (hi : i ∈ s) : Integrable ((A i).indicator
      (fun ω => F i (σ ω) ω (B (σ ω) ω))) P :=
    ((hF i hi).eval_stopped_integrable hBm (stopping_time_measurable_nnreal hσ)).indicator
      (hAi i hi)
  rw [integral_finsetSum _ hleft, integral_finsetSum _ hright]
  apply Finset.sum_le_sum
  intro i hi
  rw [integral_indicator (hAi i hi), integral_indicator (hAi i hi)]
  exact brownian_time_field_optional_interval_le hB hm hBm hBc (hF i hi)
    σ τ hσ hτ hστ T hb (hA i hi) (hdrift i hi)

/-- Patching finitely many bounded stopping intervals preserves the
conditional expectation bound. Each field is required to have
nonpositive drift only on its own interval. -/
theorem brownian_finite_switch_optional_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (N : ℕ) (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, n ≤ N → IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (hmono : ∀ n, n < N → ∀ ω, τ n ω ≤ τ (n+1) ω)
    (T : ℝ≥0) (hbound : ∀ n, n ≤ N → ∀ ω, τ n ω ≤ T)
    (K : ℕ → ℝ≥0) (F a : ℕ → ℝ≥0 → Ω → ℝ → ℝ)
    (hF : ∀ n, n ≤ N → SmoothTimeBrownianField B hm (K n) (F n) (a n))
    {A : Set Ω} (hA : MeasurableSet[(hτ 0 (Nat.zero_le N)).measurableSpace] A)
    (hdrift : ∀ n, n < N → ∀ ω ∈ A, ∀ u,
      (τ n ω : ℝ) ≤ u → u < (τ (n+1) ω : ℝ) →
        brownianFieldDrift B (F n) (a n) u ω ≤ 0)
    (hjump : ∀ n, n < N → ∀ ω ∈ A,
      F (n+1) (τ (n+1) ω) ω (B (τ (n+1) ω) ω) ≤
        F n (τ (n+1) ω) ω (B (τ (n+1) ω) ω)) :
    (∫ ω in A, F N (τ N ω) ω (B (τ N ω) ω) ∂P) ≤
      ∫ ω in A, F 0 (τ 0 ω) ω (B (τ 0 ω) ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hstart : ∀ n, n ≤ N → ∀ ω, τ 0 ω ≤ τ n ω := by
    intro n
    induction n with
    | zero => intro _ _; exact le_rfl
    | succ n ih =>
      intro hn ω
      exact (ih (Nat.le_trans (Nat.le_succ n) hn) ω).trans
        (hmono n (Nat.lt_of_succ_le hn) ω)
  have hAm (n : ℕ) (hn : n ≤ N) :
      MeasurableSet[(hτ n hn).measurableSpace] A := by
    apply IsStoppingTime.measurableSpace_mono (hτ 0 (Nat.zero_le N)) (hτ n hn)
      (fun ω => WithTop.coe_le_coe.mpr (hstart n hn ω))
    exact hA
  have hind : ∀ n, n ≤ N →
      (∫ ω in A, F n (τ n ω) ω (B (τ n ω) ω) ∂P) ≤
        ∫ ω in A, F 0 (τ 0 ω) ω (B (τ 0 ω) ω) ∂P := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih =>
      intro hn
      have hn' := Nat.le_trans (Nat.le_succ n) hn
      have hnN := Nat.lt_of_succ_le hn
      have hflow := brownian_time_field_optional_interval_le hB hm hBm hBc
        (hF n hn') (τ n) (τ (n+1)) (hτ n hn') (hτ (n+1) hn)
        (hmono n hnN) T (hbound (n+1) hn) (hAm n hn') (hdrift n hnN)
      have hright := (hF n hn').eval_stopped_integrable hBm
        (stopping_time_measurable_nnreal (hτ (n+1) hn)) (P := P.restrict A)
      have hleft := (hF (n+1) hn).eval_stopped_integrable hBm
        (stopping_time_measurable_nnreal (hτ (n+1) hn)) (P := P.restrict A)
      have hswitch : (∫ ω in A, F (n+1) (τ (n+1) ω) ω (B (τ (n+1) ω) ω) ∂P) ≤
          ∫ ω in A, F n (τ (n+1) ω) ω (B (τ (n+1) ω) ω) ∂P := by
        apply integral_mono_ae hleft hright
        filter_upwards [ae_restrict_mem ((hτ 0 (Nat.zero_le N)).measurableSpace_le _ hA)]
          with ω hω
        exact hjump n hnN ω hω
      exact hswitch.trans (hflow.trans (ih hn'))
  exact hind N le_rfl

namespace Multipoint

def activeFactor (p β U u θ : ℝ) : ℝ :=
  Real.exp (p / 2 * u) / 3 * angularFactor p (regulator β U u) θ

lemma activeFactor_activation_le {p β U θ : ℝ}
    (hp : 0 < p) (hU : 0 ≤ U) (hθ : 0 ≤ Real.sin θ) :
    activeFactor p β U 0 θ ≤ 1 := by
  unfold activeFactor
  rw [regulator_zero β U hU]
  have h := (angularFactor_endpoint_bounds hp hθ).2
  simp only [mul_zero, Real.exp_zero]
  linarith

/-- Completion freezes the factor at its angle-independent lower bound. -/
lemma activeFactor_completion_jump {p β U θ : ℝ}
    (hp : 0 < p) (hU : 0 ≤ U) (hθ : 0 ≤ Real.sin θ) :
    Real.exp (p / 2 * U) / 3 ≤ activeFactor p β U U θ := by
  unfold activeFactor
  rw [regulator_end β U hU]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (angularFactor_endpoint_bounds hp hθ).1 (by positivity : 0 ≤ Real.exp (p / 2 * U) / 3)

lemma activeFactor_nonneg {p β U u θ : ℝ} (hθ : 0 ≤ Real.sin θ) :
    0 ≤ activeFactor p β U u θ := by
  unfold activeFactor
  exact mul_nonneg (by positivity)
    ((regulator_pos β U u).le.trans (angularFactor_ge_delta (regulator_pos β U u).le hθ))

/-- Simultaneous activation or completion of any subset still gives a
downward jump for the finite product. Unchanged completed factors need
only be nonnegative constants. -/
lemma finite_factor_switch_le {ι : Type*} (s : Finset ι) (before after : ι → ℝ)
    (hafter : ∀ i ∈ s, 0 ≤ after i) (hle : ∀ i ∈ s, after i ≤ before i) :
    (∏ i ∈ s, after i) ≤ ∏ i ∈ s, before i :=
  Finset.prod_le_prod₀ hafter hle

end Multipoint
end SLEExactGauge

end

end OAI
