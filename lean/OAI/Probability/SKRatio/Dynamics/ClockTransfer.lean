import Mathlib
import OAI.Probability.SKRatio.Dynamics.Median
import OAI.Probability.SKRatio.Dynamics.PoissonBinomial
import OAI.Probability.SKRatio.Dynamics.ClockBridge

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter ProbabilityTheory SKRatioClock
namespace SKRatio.Calculus

lemma median_attempts_diverge_of_log_lower
    (G : ∀ n : ℕ, Set (Disorder n)) {c : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, c*Real.log n ≤ medianTime g) :
    ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)*(c*Real.log n)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ (hlog.const_mul_atTop hc)
  intro R
  filter_upwards [hscale,hlim.eventually_ge_atTop R] with n hn hR
  intro g hg
  exact hR.trans (mul_le_mul_of_nonneg_left (hn g hg) (Nat.cast_nonneg n))

lemma upper_median_clock_diverges
    (G : ∀ n : ℕ, Set (Disorder n)) {b : ℝ} (hb : 0 < b)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g) :
    ∀ K : ℕ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      K ≤ ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ := by
  intro K
  have hp : 0 < 1+b := by linarith
  filter_upwards [hdiv ((K:ℝ)/(1+b))] with n hn
  intro g hg
  have hx := (div_le_iff₀ hp).mp (hn g hg)
  have hy : (K:ℝ) ≤ (⌈(1+b)*(n:ℝ)*medianTime g⌉₊:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    nlinarith only [hx]
  exact_mod_cast hy

lemma upper_clock_shifted_time {n : ℕ} (hn : 0 < n) (t : ℝ)
    {b q y : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hy : |y| ≤ (q*b/(2*(1+b)))*Real.sqrt (⌈(1+b)*(n:ℝ)*t⌉₊:ℝ)) :
    (1+b/2)*t ≤
      (q*(⌈(1+b)*(n:ℝ)*t⌉₊:ℝ)+y*Real.sqrt (⌈(1+b)*(n:ℝ)*t⌉₊:ℝ))/(q*n) := by
  let M : ℕ := ⌈(1+b)*(n:ℝ)*t⌉₊
  let c := q*b/(2*(1+b))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcq : c < q := by
    dsimp [c]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(1+b))).mpr
    nlinarith
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hM : (1+b)*(n:ℝ)*t ≤ (M:ℝ) := Nat.le_ceil _
  have hsq : Real.sqrt (M:ℝ)^2 = (M:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have herr : -c*(M:ℝ) ≤ y*Real.sqrt (M:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hy (Real.sqrt_nonneg (M:ℝ))
    have hy' := mul_le_mul_of_nonneg_right (neg_abs_le y) (Real.sqrt_nonneg (M:ℝ))
    change |y| * Real.sqrt (M:ℝ) ≤ c*Real.sqrt (M:ℝ)*Real.sqrt (M:ℝ) at hh
    nlinarith
  apply (le_div_iff₀ (mul_pos hq hn')).mpr
  have hmain := mul_le_mul_of_nonneg_left hM (sub_pos.mpr hcq).le
  have hid : (q-c)*(1+b) = q*(1+b/2) := by
    dsimp [c]
    field_simp
    ring
  change _ ≤ q*(M:ℝ)+y*Real.sqrt (M:ℝ)
  calc
    _ = (q-c)*((1+b)*(n:ℝ)*t) := by
      calc
        _ = ((q-c)*(1+b))*(n:ℝ)*t := by rw [hid]; ring
        _ = _ := by ring
    _ ≤ (q-c)*(M:ℝ) := hmain
    _ ≤ _ := by nlinarith

lemma uniform_upper_clock_shift
    (G : ∀ n : ℕ, Set (Disorder n)) {b q : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g)
    (y : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      (1+b/2)*medianTime g ≤
        (q*(⌈(1+b)*(n:ℝ)*medianTime g⌉₊:ℝ)+
          y*Real.sqrt (⌈(1+b)*(n:ℝ)*medianTime g⌉₊:ℝ))/(q*n) := by
  have hc : 0 < q*b/(2*(1+b)) := by positivity
  have hs := (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)).const_mul_atTop hc
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.eventually_ge_atTop |y|)
  filter_upwards [upper_median_clock_diverges G hb hdiv N,eventually_gt_atTop 0] with n hn hn0
  intro g hg
  exact upper_clock_shifted_time hn0 (medianTime g) hb hq (hN _ (hn g hg))

theorem uniform_discrete_upper_of_holding
    (G : ∀ n : ℕ, Set (Disorder n)) {b q : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hq1 : q < 1)
    (hdiv : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, R ≤ (n:ℝ)*medianTime g)
    (hhold : ∀ n, 0 < n → ∀ g ∈ G n, ∀ x, 1-q ≤ transition g x x)
    (hcont : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      continuousDistance g ((1+b/2)*medianTime g) ≤ δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      discreteDistance g ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ ≤ δ := by
  classical
  let ι : ℕ → Type := fun n => Option
    ({g : Disorder n // g ∈ G n ∧ 0 < n} × Spin n ×
      {f : Observables n // ∀ x, |f x| ≤ 1})
  let M : (n : ℕ) → ι n → ℕ := fun n i => match i with
    | none => n+1
    | some j => ⌈(1+b)*(n:ℝ)*medianTime j.1.val⌉₊
  let a : (n : ℕ) → ι n → ℕ → ℝ := fun _ i k => match i with
    | none => 0
    | some j => (residualAttempt (coupling j.1.val) q ^ k) j.2.2.val j.2.1-
        FiniteLaw.mean (mass j.1.val 0) j.2.2.val
  have hM : ∀ K : ℕ, ∀ᶠ n in atTop, ∀ i : ι n, K ≤ M n i := by
    intro K
    filter_upwards [upper_median_clock_diverges G hb hdiv K,eventually_ge_atTop K] with n hn hnK
    intro i
    cases i with
    | none => exact hnK.trans (Nat.le_succ n)
    | some j => exact hn j.1.val j.1.property.1
  have hab : ∀ n (i : ι n) k, |a n i k| ≤ 2 := by
    intro n i k
    cases i with
    | none => norm_num [a]
    | some j =>
      exact residual_test_bound j.1.val hq
        (hhold n j.1.property.2 j.1.val j.1.property.1) j.2.2.val j.2.2.property j.2.1 k
  have hp : ∀ y ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i : ι n,
      |∑' j, Clock.poissonMass (q*M n i+y*Real.sqrt (M n i)) j*a n i j| < ε := by
    intro y ε hε
    filter_upwards [uniform_upper_clock_shift G hb hq hdiv y,hcont (ε/4) (by positivity)] with n hn hcn
    intro i
    cases i with
    | none => simpa only [a,mul_zero,tsum_zero,abs_zero] using hε
    | some j =>
      change |∑' k, Clock.poissonMass
        (q*(⌈(1+b)*(n:ℝ)*medianTime j.1.val⌉₊:ℝ)+
          y*Real.sqrt (⌈(1+b)*(n:ℝ)*medianTime j.1.val⌉₊:ℝ)) k*
          ((residualAttempt (coupling j.1.val) q ^ k) j.2.2.val j.2.1-
            FiniteLaw.mean (mass j.1.val 0) j.2.2.val)| < ε
      rw [residual_poisson_test j.1.property.2 j.1.val hq.ne']
      have htime := hn j.1.val j.1.property.1
      have ht : 0 ≤ (1+b/2)*medianTime j.1.val :=
        mul_nonneg (by linarith) (medianTime_mem j.1.val).1
      have hbd := (continuous_test_bound j.1.val _ j.2.2.val j.2.2.property j.2.1).trans
        (mul_le_mul_of_nonneg_left (continuousDistance_antitone j.1.val ht htime) (by norm_num))
      have hc := hcn j.1.val j.1.property.1
      linarith
  have hbin := Clock.poisson_to_binomial_uniform_clocks hq hq1 M hM a hab hp
  intro δ hδ
  filter_upwards [hbin δ hδ,eventually_gt_atTop 0] with n hn hn0
  intro g hg
  apply Finset.sup'_le
  intro x _
  apply FiniteLaw.totalVariation_le_of_tests
  intro f hf
  let i : ι n := some (⟨g,hg,hn0⟩,x,⟨f,hf⟩)
  have hbd := hn i
  change |∑' k, Clock.binomialMass q ⌈(1+b)*(n:ℝ)*medianTime g⌉₊ k*
    ((residualAttempt (coupling g) q ^ k) f x-FiniteLaw.mean (mass g 0) f)| < δ at hbd
  rw [residual_binomial_test g hq.ne'] at hbd
  change |((transition g ^ ⌈(1+b)*(n:ℝ)*medianTime g⌉₊) *ᵥ f) x-
    FiniteLaw.mean (mass g 0) f| ≤ 2*δ
  linarith

end SKRatio.Calculus

end
end

end OAI
