import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import OAI.NumberTheory.Jacobsthal.Estimates.InverseWeightGrowth

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.RegenerationTails

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open BuchstabBridge DerivativeWeights WeightFutureIntegrals WeightTailBounds
open TransitionKernels FinitePathMeasures

theorem tailDensity_setIntegral {left right mass : ℝ} {B : ℝ → ℝ} (h : left ≤ right) :
    (∫ t in Ici right, tailDensity left mass B t) = (∫ t in Ici right, B t) / mass := by
  calc
    _ = ∫ t in Ici right, B t / mass := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro t ht
      exact indicator_of_mem (show t ∈ Ici left from le_trans h ht) _
    _ = _ := integral_div mass B

theorem evenKernel_tail (s : EvenState) {h : ℝ} (hh : 0 ≤ h) :
    evenKernel s (Ici (s.1 - 1 + h)) = ENNReal.ofReal (phiEven (s.1 + h) / phiEven s.1) := by
  rw [evenKernel_apply, ← ofReal_integral_eq_lintegral_ofReal
    (evenDensity_integrable s).integrableOn (Eventually.of_forall (evenDensity_nonneg s))]
  congr 1
  change (∫ t in Ici (s.1 - 1 + h), tailDensity (s.1 - 1) (phiEven s.1) (fun t => W t * phiOdd t) t) = _
  rw [tailDensity_setIntegral (by linarith), integral_Ici_eq_integral_Ioi]
  have hf := (phiEven_future_integral (s := s.1 + h) (by linarith [s.2])).2
  rw [show s.1 + h - 1 = s.1 - 1 + h by ring] at hf
  rw [← hf]

theorem oddKernel_tail (s : OddState) (hs : 3 ≤ s.1) {h : ℝ} (hh : 0 ≤ h) :
    oddKernel s (Ici (s.1 - 1 + h)) = ENNReal.ofReal (phiOdd (s.1 + h) / phiOdd s.1) := by
  rw [oddKernel_apply, ← ofReal_integral_eq_lintegral_ofReal
    (oddDensity_integrable s).integrableOn (Eventually.of_forall (oddDensity_nonneg s))]
  congr 1
  change (∫ t in Ici (s.1 - 1 + h), tailDensity (max 2 (s.1 - 1)) (phiOdd s.1)
    (fun t => W t * phiEven t) t) = _
  rw [tailDensity_setIntegral (by apply max_le <;> linarith), integral_Ici_eq_integral_Ioi]
  have hf := (phiOdd_future_integral (s.1 + h)).2
  rw [max_eq_right (show 2 ≤ s.1 + h - 1 by linarith),
    show s.1 + h - 1 = s.1 - 1 + h by ring] at hf
  rw [← hf]

theorem exponential_comparison {P : ℝ → ℝ} {U rate a b : ℝ}
    (hp : ∀ t, U ≤ t → 0 < P t)
    (hd : ∀ t, U ≤ t → DifferentiableAt ℝ P t)
    (hl : ∀ t, U ≤ t → rate ≤ -deriv P t / P t)
    (ha : U ≤ a) (hab : a ≤ b) : P b ≤ P a * Real.exp (-rate * (b - a)) := by
  let H : ℝ → ℝ := fun t => Real.exp (rate * t) * P t
  have hder : ∀ t, U ≤ t → HasDerivAt H
      (Real.exp (rate * t) * (deriv P t + rate * P t)) t := by
    intro t ht
    have h := (((hasDerivAt_id t).const_mul rate).exp).mul (hd t ht).hasDerivAt
    convert! h using 1
    simp only [id_eq, mul_one]
    ring
  have hm : AntitoneOn H (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro t ht
      exact (hder t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htU : U ≤ t := by linarith [ht.1]
      rw [(hder t htU).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have h := (le_div_iff₀ (hp t htU)).mp (hl t htU)
      linarith
  have h := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hq : P b ≤ Real.exp (rate * a) * P a / Real.exp (rate * b) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [H, mul_comm] using h
  calc
    P b ≤ Real.exp (rate * a) * P a / Real.exp (rate * b) := hq
    _ = P a * (Real.exp (rate * a) / Real.exp (rate * b)) := by ring
    _ = _ := by rw [← Real.exp_sub]; congr 1; congr 1; ring

theorem kernel_exponential_tails (rate : ℝ) : ∃ U : ℝ, 4 ≤ U ∧
    (∀ s : EvenState, U ≤ s.1 → ∀ h : ℝ, 0 ≤ h →
      evenKernel s (Ici (s.1 - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-rate * h))) ∧
    (∀ s : OddState, U ≤ s.1 → ∀ h : ℝ, 0 ≤ h →
      oddKernel s (Ici (s.1 - 1 + h)) ≤ ENNReal.ofReal (Real.exp (-rate * h))) := by
  obtain ⟨U, hU, hb⟩ := weights_logDeriv_growth rate
  refine ⟨U, hU, ?_, ?_⟩
  · intro s hs h hh
    rw [evenKernel_tail s hh]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiEven_pos (by linarith))).mpr
    have he := exponential_comparison (P := phiEven)
      (fun t ht => phiEven_pos (by linarith))
      (fun t ht => (phiEven_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).1) hs (show s.1 ≤ s.1 + h by linarith)
    simpa only [add_sub_cancel_left, mul_comm] using he
  · intro s hs h hh
    rw [oddKernel_tail s (by linarith) hh]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (phiOdd_pos s.1)).mpr
    have ho := exponential_comparison (P := phiOdd) (fun t _ => phiOdd_pos t)
      (fun t ht => (phiOdd_hasDerivAt (by linarith)).differentiableAt)
      (fun t ht => (hb t ht).2) hs (show s.1 ≤ s.1 + h by linarith)
    simpa only [add_sub_cancel_left, mul_comm] using ho

def regenerationState : OddState := ⟨1, by norm_num⟩

theorem oddKernel_regeneration (s : OddState) (hs : s.1 ≤ 3) :
    oddKernel s = oddKernel regenerationState := by
  ext B hB
  rw [oddKernel_apply, oddKernel_apply]
  congr 1
  ext t
  congr 1
  unfold oddDensity
  rw [max_eq_left (show s.1 - 1 ≤ 2 by linarith), phiOdd_initial hs]
  norm_num [regenerationState, phiOdd, tailDensity]

theorem stateKernel_regeneration (s : OddState) (hs : s.1 ≤ 3) :
    stateKernel (.inr s) = stateKernel (.inr regenerationState) := by
  change oddBranch s = oddBranch regenerationState
  rw [oddBranch, Kernel.map_apply _ measurable_inl, Kernel.map_apply _ measurable_inl,
    oddToEven, Kernel.comapRight_apply, Kernel.comapRight_apply, oddKernel_regeneration s hs]

theorem costKernel_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    costKernel (.inr s, T) = costKernel (.inr regenerationState, T) := by
  ext B hB
  rw [costKernel_apply _ hB, costKernel_apply _ hB]
  exact congrArg (fun μ : Measure State => μ {t | (t, T + FinitePathGeometry.cost (stateRatio t)) ∈ B})
    (stateKernel_regeneration s hs)

end NumberTheoryLean.RegenerationTails

end

section

namespace NumberTheoryLean.RegenerationDrift

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open TransitionKernels RegenerationTails

theorem exponential_moment_of_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hsupport : ∀ᵐ x ∂μ, m ≤ x)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) ≤ ENNReal.ofReal (2 * Real.exp m) := by
  have hnn : 0 ≤ᵐ[μ] (fun x : ℝ => x - m) := by
    filter_upwards [hsupport] with x hx
    exact sub_nonneg.mpr hx
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul (f := fun x : ℝ => x - m)
    (g := Real.exp) μ hnn (measurable_id.sub measurable_const).aemeasurable
    (fun t _ => Real.continuous_exp.intervalIntegrable 0 t)
    (Eventually.of_forall (fun t => (Real.exp_pos t).le))
  simp only [integral_exp, Real.exp_zero] at hlc
  have hsmall : (∫⁻ x, ENNReal.ofReal (Real.exp (x - m) - 1) ∂μ) ≤ 1 := by
    rw [hlc]
    calc
      _ ≤ ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-h)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
        have hset : {x : ℝ | h ≤ x - m} = Ici (m + h) := by ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro hx <;> linarith
        rw [hset]
        calc
          _ ≤ ENNReal.ofReal (Real.exp (-2 * h)) * ENNReal.ofReal (Real.exp h) :=
            mul_le_mul (htail h hh.le) le_rfl zero_le zero_le
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            congr 2
            ring
      _ = 1 := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
          (Eventually.of_forall (fun h => (Real.exp_pos (-h)).le)), integral_exp_neg_Ioi_zero]
        norm_num
  have hshiftMeas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (x - m) - 1)) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (measurable_id.sub measurable_const)).sub measurable_const)
  have heq : (fun x : ℝ => ENNReal.ofReal (Real.exp (x - m))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (Real.exp (x - m) - 1) + 1) := by
    filter_upwards [hsupport] with x hx
    have he : 1 ≤ Real.exp (x - m) := Real.one_le_exp_iff.mpr (sub_nonneg.mpr hx)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (sub_nonneg.mpr he) zero_le_one]
    congr 1
    ring
  have hshift : (∫⁻ x, ENNReal.ofReal (Real.exp (x - m)) ∂μ) ≤ 2 := by
    rw [lintegral_congr_ae heq, lintegral_add_left hshiftMeas]
    simp only [lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ 1 + 1 := add_le_add hsmall le_rfl
      _ = 2 := by norm_num
  have hscale : ∀ x : ℝ, ENNReal.ofReal (Real.exp x) =
      ENNReal.ofReal (Real.exp m) * ENNReal.ofReal (Real.exp (x - m)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [lintegral_congr hscale, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (Real.exp m) * 2 := mul_le_mul le_rfl hshift zero_le zero_le
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num; ring

theorem exponential_integrable_of_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hsupport : ∀ᵐ x ∂μ, m ≤ x)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    Integrable Real.exp μ := by
  refine ⟨Real.continuous_exp.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => (Real.exp_pos x).le))).mpr
  exact lt_of_le_of_lt (exponential_moment_of_tail μ m hsupport htail) ENNReal.ofReal_lt_top

noncomputable def driftFactor : ℝ := 2 / Real.exp 1

theorem driftFactor_pos : 0 < driftFactor := by unfold driftFactor; positivity
theorem driftFactor_lt_one : driftFactor < 1 := by
  unfold driftFactor
  exact (div_lt_one (Real.exp_pos 1)).mpr Real.exp_one_gt_two

theorem drift_scale (s : ℝ) : 2 * Real.exp (s - 1) = driftFactor * Real.exp s := by
  unfold driftFactor
  rw [Real.exp_sub]
  ring

theorem kernel_exponential_drift : ∃ U : ℝ, 4 ≤ U ∧
    (∀ s : EvenState, U ≤ s.1 → Integrable Real.exp (evenKernel s) ∧
      (∫⁻ t, ENNReal.ofReal (Real.exp t) ∂evenKernel s) ≤ ENNReal.ofReal (driftFactor * Real.exp s.1)) ∧
    (∀ s : OddState, U ≤ s.1 → Integrable Real.exp (oddKernel s) ∧
      (∫⁻ t, ENNReal.ofReal (Real.exp t) ∂oddKernel s) ≤ ENNReal.ofReal (driftFactor * Real.exp s.1)) := by
  obtain ⟨U, hU, he, ho⟩ := kernel_exponential_tails 2
  refine ⟨U, hU, ?_, ?_⟩
  · intro s hs
    refine ⟨exponential_integrable_of_tail _ (s.1 - 1) (evenKernel_ae_support s) (he s hs), ?_⟩
    simpa only [drift_scale] using exponential_moment_of_tail _ (s.1 - 1) (evenKernel_ae_support s) (he s hs)
  · intro s hs
    have hsupport : ∀ᵐ t ∂oddKernel s, s.1 - 1 ≤ t := by
      filter_upwards [oddKernel_ae_support s] with t ht
      exact le_trans (le_max_right _ _) ht
    refine ⟨exponential_integrable_of_tail _ (s.1 - 1) hsupport (ho s hs), ?_⟩
    simpa only [drift_scale] using exponential_moment_of_tail _ (s.1 - 1) hsupport (ho s hs)

theorem kernel_drift_expectation : ∃ U : ℝ, 4 ≤ U ∧
    (∀ s : EvenState, U ≤ s.1 → Integrable Real.exp (evenKernel s) ∧
      (∫ t, Real.exp t ∂evenKernel s) ≤ driftFactor * Real.exp s.1) ∧
    (∀ s : OddState, U ≤ s.1 → Integrable Real.exp (oddKernel s) ∧
      (∫ t, Real.exp t ∂oddKernel s) ≤ driftFactor * Real.exp s.1) := by
  obtain ⟨U, hU, he, ho⟩ := kernel_exponential_drift
  refine ⟨U, hU, ?_, ?_⟩
  · intro s hs
    obtain ⟨hi, hb⟩ := he s hs
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff (mul_pos driftFactor_pos (Real.exp_pos _)).le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact hb
  · intro s hs
    obtain ⟨hi, hb⟩ := ho s hs
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff (mul_pos driftFactor_pos (Real.exp_pos _)).le).mp ?_⟩
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun t => (Real.exp_pos t).le))]
    exact hb

end NumberTheoryLean.RegenerationDrift

end

end Erdos970

end OAI
