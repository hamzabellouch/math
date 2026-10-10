import OAI.NumberTheory.Jacobsthal.Paths.AdmittedHarmonicPaths

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LowStateHorizon

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

 theorem cost_ge_inv_add_one {t : ℝ} (ht : 0 < t) : 1 / (t + 1) ≤ cost t := by
  have hx : 0 < 1 + 1 / t := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have heq : 1 - (1 + 1 / t)⁻¹ = 1 / (t + 1) := by
    field_simp [ht.ne', hx.ne', show t + 1 ≠ 0 by linarith]
    ring
  rw [heq] at h
  exact h

theorem stateRatio_ge_nineteen_twentieths (s : State) : (19 / 20 : ℝ) ≤ stateRatio s := by
  cases s with
  | inl s => change (19 / 20 : ℝ) ≤ s.1; linarith [s.2]
  | inr s => change (19 / 20 : ℝ) ≤ s.1; linarith [s.2]

theorem costKernel_time_update (z : CostState) :
    ∀ᵐ y ∂costKernel z, y.2 = z.2 + cost (stateRatio y.1) := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hp : MeasurableSet {y : CostState | y.2 = z.2 + cost (stateRatio y.1)} :=
    measurableSet_eq_fun measurable_snd
      (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst)))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable hp).mpr
  exact Eventually.of_forall fun _ => rfl

theorem harmonicKernel_time_update (z : CostState) :
    ∀ᵐ y ∂harmonicKernel z, y.2 = z.2 + cost (stateRatio y.1) :=
  (harmonicKernel_absolutelyContinuous z).ae_le (costKernel_time_update z)

def lowDomain (v ell S : ℝ) : Set CostState := arrivalSet v ell ∩ {z | stateRatio z.1 ≤ S}

theorem lowDomain_measurable (v ell S : ℝ) : MeasurableSet (lowDomain v ell S) :=
  (arrivalSet_measurable v ell).inter (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const)

noncomputable def lowKernel (K : Kernel CostState CostState) (v ell S : ℝ) : Kernel CostState CostState :=
  K.restrict (lowDomain_measurable v ell S)

theorem low_step_clock (K : Kernel CostState CostState) (v ell S : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1)) (z : CostState) :
    ∀ᵐ y ∂lowKernel K v ell S z, z.2 + 1 / (S + 1) ≤ y.2 := by
  rw [lowKernel, Kernel.restrict_apply]
  filter_upwards [ae_restrict_of_ae (hTime z), ae_restrict_mem (lowDomain_measurable v ell S)] with y hy hD
  have hs : stateRatio y.1 ≤ S := hD.2
  have ht := stateRatio_pos y.1
  have hc : 1 / (S + 1) ≤ cost (stateRatio y.1) :=
    le_trans (one_div_le_one_div_of_le (by linarith : 0 < stateRatio y.1 + 1) (by linarith))
      (cost_ge_inv_add_one ht)
  linarith

theorem low_pow_clock (K : Kernel CostState CostState) (v ell S : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1)) (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂((lowKernel K v ell S) ^ n) z, z.2 + (n : ℝ) / (S + 1) ≤ y.2 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    change ∀ᵐ y ∂Measure.dirac z, z.2 + (0 : ℝ) / (S + 1) ≤ y.2
    exact (ae_dirac_iff (p := fun y : CostState => z.2 + (0 : ℝ) / (S + 1) ≤ y.2)
      (measurableSet_le measurable_const measurable_snd)).mpr (by simp)
  | succ n ih =>
    have hp : (lowKernel K v ell S) ^ (n + 1) = (lowKernel K v ell S) ∘ₖ ((lowKernel K v ell S) ^ n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
    filter_upwards [ih] with y hy
    filter_upwards [low_step_clock K v ell S hTime y] with t ht
    calc
      z.2 + ((n + 1 : ℕ) : ℝ) / (S + 1) = (z.2 + (n : ℝ) / (S + 1)) + 1 / (S + 1) := by push_cast; ring
      _ ≤ y.2 + 1 / (S + 1) := add_le_add hy le_rfl
      _ ≤ t.2 := ht

theorem low_pow_terminal (K : Kernel CostState CostState) (v ell S : ℝ) (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂((lowKernel K v ell S) ^ (n + 1)) z, y ∈ lowDomain v ell S := by
  have hp : (lowKernel K v ell S) ^ (n + 1) = (lowKernel K v ell S) ∘ₖ ((lowKernel K v ell S) ^ n) := pow_succ' _ _
  rw [hp]
  apply Kernel.ae_comp_of_ae_ae (lowDomain_measurable v ell S)
  apply Eventually.of_forall
  intro y
  rw [lowKernel, Kernel.restrict_apply]
  exact ae_restrict_mem (lowDomain_measurable v ell S)

theorem low_pow_zero_of_clock (K : Kernel CostState CostState) (v ell S : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1))
    (hell : 0 < ell) (n : ℕ) (hn : 0 < n) (z : CostState)
    (hclock : v - z.2 - Real.log ((19 / 20 : ℝ) * ell) ≤ (n : ℝ) / (S + 1)) :
    ((lowKernel K v ell S) ^ n) z = 0 := by
  have hD : ∀ᵐ y ∂((lowKernel K v ell S) ^ n) z, y ∈ lowDomain v ell S := by
    cases n with
    | zero => omega
    | succ n => exact low_pow_terminal K v ell S n z
  have hfalse : ∀ᵐ y ∂((lowKernel K v ell S) ^ n) z, False := by
    filter_upwards [low_pow_clock K v ell S hTime n z, hD] with y hy hdom
    have ha : ell < gapValue v y / stateRatio y.1 := hdom.1
    have hmul := (lt_div_iff₀ (stateRatio_pos y.1)).mp ha
    have hgap : (19 / 20 : ℝ) * ell < gapValue v y := by
      have hlow := mul_le_mul_of_nonneg_left (stateRatio_ge_nineteen_twentieths y.1) hell.le
      nlinarith
    have hlog := Real.log_lt_log (mul_pos (by norm_num : (0 : ℝ) < 19 / 20) hell) hgap
    rw [gapValue, Real.log_exp] at hlog
    linarith
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hfalse

noncomputable def sourceHorizon (S B : ℝ) : ℕ := ⌈(S + 1) * (Real.log B + 2)⌉₊ + 1

theorem source_low_horizon (K : Kernel CostState CostState) (v ell S B : ℝ)
    (hTime : ∀ z, ∀ᵐ y ∂K z, y.2 = z.2 + cost (stateRatio y.1))
    (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B) (z : CostState)
    (hgap : gapValue v z ≤ (23 / 10 : ℝ) * B) (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    ((lowKernel K v ell S) ^ n) z = 0 := by
  have hell0 : 0 < ell := by linarith
  have hn0 : 0 < n := by unfold sourceHorizon at hn; omega
  apply low_pow_zero_of_clock K v ell S hTime hell0 n hn0 z
  have hlogR := Real.log_le_log (Real.exp_pos (v - z.2)) hgap
  rw [Real.log_exp, Real.log_mul (by norm_num : (23 / 10 : ℝ) ≠ 0) hB.ne'] at hlogR
  have hlog23 : Real.log (23 / 10 : ℝ) ≤ 13 / 10 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 23 / 10)
    norm_num at h
    exact h
  have hlog19 : (-1 / 19 : ℝ) ≤ Real.log (19 / 20 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19 / 20)
    norm_num at h
    linarith
  have hlogell : Real.log (19 / 20 : ℝ) ≤ Real.log ((19 / 20 : ℝ) * ell) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hspan : v - z.2 - Real.log ((19 / 20 : ℝ) * ell) ≤ Real.log B + 2 := by linarith
  have hceil := Nat.le_ceil ((S + 1) * (Real.log B + 2))
  have hN : ((⌈(S + 1) * (Real.log B + 2)⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
    have hN' : ⌈(S + 1) * (Real.log B + 2)⌉₊ ≤ n := by unfold sourceHorizon at hn; omega
    exact_mod_cast hN'
  apply le_trans hspan
  apply (le_div_iff₀ (by linarith : 0 < S + 1)).mpr
  nlinarith

theorem source_horizon_log_cube {B : ℝ} (hB : 2 ≤ Real.log B) :
    ((sourceHorizon ((Real.log B) ^ 2) B : ℕ) : ℝ) ≤ 5 * (Real.log B) ^ 3 := by
  let x := Real.log B
  have hx : 2 ≤ x := hB
  have hpos : 0 ≤ (x ^ 2 + 1) * (x + 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hpos).le
  change ((⌈(x ^ 2 + 1) * (x + 2)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * x ^ 3
  push_cast
  have h2 : 0 ≤ (x - 2) * x := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (x - 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  nlinarith

theorem tilted_source_horizon (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (z : CostState) (hgap : gapValue v z ≤ (23 / 10 : ℝ) * B) (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    ((lowKernel costKernel v ell S) ^ n) z = 0 :=
  source_low_horizon costKernel v ell S B costKernel_time_update hell hS hB z hgap n hn

theorem harmonic_source_horizon (v ell S B : ℝ) (hell : 1 ≤ ell) (hS : 0 < S) (hB : 0 < B)
    (z : CostState) (hgap : gapValue v z ≤ (23 / 10 : ℝ) * B) (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    ((lowKernel harmonicKernel v ell S) ^ n) z = 0 :=
  source_low_horizon harmonicKernel v ell S B harmonicKernel_time_update hell hS hB z hgap n hn

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
