import Mathlib
import OAI.Probability.SLE.DiskHalfPlane

namespace OAI

/-! Angular Power Dynkin for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma powerLogGenerator_lyapunov (κ b : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    powerLogGenerator κ (codimension κ) (greenExponent κ - b) q x =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) q x *
        logClockRate κ q x * (κ * b / 8) *
          (1 - (greenExponent κ - b) * ((logAngleSq κ q x)⁻¹ - 1)) := by
  unfold powerLogGenerator
  rw [← power_physical_generator κ _ _ hκ.le]
  exact green_weighted_power_generator κ b hκ q x

lemma powerLogDensity_div_angle (κ p α : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    powerLogDensity κ p α q x / logAngleSq κ q x =
      powerLogDensity κ p (α - 2) q x := by
  rw [powerLogDensity_radius_angle κ p α 0, powerLogDensity_radius_angle κ p (α - 2) 0,
    mul_div_assoc]
  congr 1
  rw [show (α - 2) / 2 = α / 2 - 1 by ring,
    Real.rpow_sub (logAngleSq_pos κ q x), Real.rpow_one]

lemma powerLogGenerator_two_powers (κ b : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    powerLogGenerator κ (codimension κ) (greenExponent κ - b) q x =
      logClockRate κ q x * (κ * b / 8) *
        ((1 + (greenExponent κ - b)) *
            powerLogDensity κ (codimension κ) (greenExponent κ - b) q x -
          (greenExponent κ - b) *
            powerLogDensity κ (codimension κ) (greenExponent κ - b - 2) q x) := by
  rw [powerLogGenerator_lyapunov κ b hκ,
    ← powerLogDensity_div_angle κ (codimension κ) (greenExponent κ - b)]
  ring

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

 

theorem mean_power
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 ≤ κ) (p α : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ α) :
    Integrable (fun ω => powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) P ∧
    Integrable (fun ω => ∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      powerLogGenerator κ p α (a.solution.Q t ω) (B t.toNNReal ω)) P ∧
      (∫ ω, powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) =
        powerLogDensity κ p α (initialLogCoordinates z) 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(a.τ ω : ℝ),
          powerLogGenerator κ p α (a.solution.Q t ω) (B t.toNNReal ω)) ∂P := by
  let K := Real.exp (p * (u - Real.log 2 - Real.log z.im))
  let C := K * (|(-4 * α + κ * α * (α + 1) / 2)| + |(4 * p - κ * α / 2)|) /
    Real.exp (2 * a.lo)
  apply a.solution.stopped_power_dynkin_bounded hB hBm hBc hB0 hκ p α a.τ a.stopping
    a.T a.bounded (fun ω t ht => (a.inside ω t ht).2.2) K C (by dsimp [C, K]; positivity)
  · intro ω t ht
    rw [abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
    exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp ha _ _ (a.inside ω t ht).1
  · intro ω t ht
    exact powerLogGenerator_le_radius_height κ p α (Real.log z.im) u a.lo hp ha _ _
      (a.inside ω t ht).1 (a.inside ω t ht).2.2.1

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε δ : ℝ}

 

lemma synchronize (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (ω : Ω)
    (t : ℝ≥0) (ha : t ≤ a.τ ω) (hb : t ≤ b.τ ω) :
    a.solution.Q t ω = b.solution.Q t ω := by
  let lo := min a.lo b.lo
  let hi := max a.hi b.hi
  have hle : lo ≤ hi := (min_le_left _ _).trans (a.le.trans (le_max_left _ _))
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (s : ℝ) := clippedLogLoewnerField lo hi hle (Real.sqrt κ * B s.toNNReal ω)
  have hd (c : AngularLocalization B hm κ z u ε) (hc : t ≤ c.τ ω)
      (hlo : lo ≤ c.lo) (hhi : c.hi ≤ hi) (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      HasDerivWithinAt (fun s => c.solution.Q s ω) (V s (c.solution.Q s ω)) (Icc 0 (t : ℝ)) s := by
    have hsc : s.toNNReal ≤ c.τ ω := (Real.toNNReal_le_iff_le_coe.mpr hs.2).trans hc
    have hcbar := (c.inside ω s.toNNReal hsc).2.2
    rw [Real.coe_toNNReal _ hs.1] at hcbar
    have hder := (c.solution.derivative ω s hs.1).mono
      (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
    rwa [clippedLogLoewnerField_eq_physical _ _ _ _ _ hcbar,
      ← clippedLogLoewnerField_eq_physical lo hi hle _ _ ⟨hlo.trans hcbar.1, hcbar.2.trans hhi⟩] at hder
  have hda := hd a ha (min_le_left _ _) (le_max_left _ _)
  have hdb (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      HasDerivWithinAt (fun s => b.solution.Q s ω) (V s (b.solution.Q s ω)) (Icc 0 (t : ℝ)) s := by
    have hsb : s.toNNReal ≤ b.τ ω := (Real.toNNReal_le_iff_le_coe.mpr hs.2).trans hb
    have hcbar := (b.inside ω s.toNNReal hsb).2.2
    rw [Real.coe_toNNReal _ hs.1] at hcbar
    have hder := (b.solution.derivative ω s hs.1).mono
      (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
    rwa [clippedLogLoewnerField_eq_physical _ _ _ _ _ hcbar,
      ← clippedLogLoewnerField_eq_physical lo hi hle _ _
        ⟨(min_le_right _ _).trans hcbar.1, hcbar.2.trans (le_max_right _ _)⟩] at hder
  have he : EqOn (fun s => a.solution.Q s ω) (fun s => b.solution.Q s ω) (Icc 0 (t : ℝ)) := by
    apply ODE_solution_unique (fun s => hlip (Real.sqrt κ * B s.toNNReal ω))
      (fun s hs => (hda s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hda s ⟨hs.1, hs.2.le⟩))
      (fun s hs => (hdb s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hdb s ⟨hs.1, hs.2.le⟩))
    exact (a.solution.initial ω).trans (b.solution.initial ω).symm
  exact he ⟨t.coe_nonneg, le_rfl⟩

lemma stopping_le (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (huv : u ≤ v) (hδε : δ ≤ ε)
    (ω : Ω) : a.τ ω ≤ b.τ ω := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have he := a.synchronize b ω (b.τ ω) hlt.le le_rfl
  have hh := a.before ω _ hlt
  rw [he] at hh
  rcases b.boundary ω with hc | hθ
  · linarith [hh.1]
  · linarith [hh.2]

lemma hit_time_unique (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z u δ) (ω : Ω)
    (ha : logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω) = u)
    (hb : logRadiusClock (Real.log z.im) (b.solution.Q (b.τ ω) ω) = u) :
    a.τ ω = b.τ ω := by
  apply le_antisymm
  · by_contra hn
    have hlt := lt_of_not_ge hn
    have he := a.synchronize b ω (b.τ ω) hlt.le le_rfl
    have hh := (a.before ω _ hlt).1
    rw [he, hb] at hh
    exact lt_irrefl _ hh
  · by_contra hn
    have hlt := lt_of_not_ge hn
    have he := b.synchronize a ω (a.τ ω) hlt.le le_rfl
    have hh := (b.before ω _ hlt).1
    rw [he, ha] at hh
    exact lt_irrefl _ hh

lemma hit_finer (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z u δ) (hδε : δ ≤ ε) (ω : Ω)
    (ha : logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω) = u) :
    b.τ ω = a.τ ω ∧ logRadiusClock (Real.log z.im) (b.solution.Q (b.τ ω) ω) = u := by
  have hab := a.stopping_le b le_rfl hδε ω
  have he : b.τ ω = a.τ ω := by
    apply le_antisymm _ hab
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hq := a.synchronize b ω (a.τ ω) le_rfl hlt.le
    have hh := (b.before ω _ hlt).1
    rw [← hq, ha] at hh
    exact lt_irrefl _ hh
  refine ⟨he, ?_⟩
  rw [he, ← a.synchronize b ω (a.τ ω) le_rfl hab]
  exact ha

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma continuous_logClockRate (κ : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => logClockRate κ p.1 p.2) := by
  have hN : Continuous (fun p : (ℂ × ℝ) × ℝ => greenLogNormSq κ p.1 p.2) := by
    unfold greenLogNormSq
    fun_prop
  unfold logClockRate
  exact (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).div (hN.pow 2)
    (fun p => pow_ne_zero 2 (greenLogNormSq_pos κ p.1 p.2).ne')

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma radius_clock_derivative (ω : Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ)) :
    HasDerivWithinAt (fun t => logRadiusClock (Real.log z.im) (a.solution.Q t ω))
      (logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)) (Icc (0 : ℝ) (a.τ ω : ℝ)) t := by
  have hd := (a.solution.derivative ω t ht.1).mono
    (show Icc (0 : ℝ) (a.τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hb := (a.inside ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)).2.2
  rw [Real.coe_toNNReal t ht.1] at hb
  rw [clippedLogLoewnerField_eq_physical _ _ _ _ _ hb] at hd
  exact log_ode_clock_derivative (Real.log z.im) hd

noncomputable def clock : FiniteIncreasingClock Ω where
  S t ω := logRadiusClock (Real.log z.im) (a.solution.Q t ω)
  T := a.τ
  zero ω := by rw [a.solution.initial]; simp [logRadiusClock, initialLogCoordinates]
  continuous ω := (continuous_logRadiusClock _).comp (a.solution.lipschitz ω).continuous
  strict ω := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) (a.τ ω : ℝ))
      ((continuous_logRadiusClock _).comp (a.solution.lipschitz ω).continuous).continuousOn
    · intro t ht
      exact (a.radius_clock_derivative ω t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact logClockRate_pos κ (a.solution.Q t ω) (B t.toNNReal ω)

lemma clock_measurable : Measurable (Function.uncurry a.clock.S) :=
  (continuous_logRadiusClock _).measurable.comp a.solution.measurable

lemma inverse_measurable : Measurable (Function.uncurry a.clock.inverse) :=
  a.clock.measurable_inverse a.clock_measurable (stopping_time_measurable_nnreal a.stopping)

lemma clock_upper (ω : Ω) : a.clock.S (a.τ ω) ω ≤ u := (a.inside ω _ le_rfl).1

noncomputable def radiusValue (p α s : ℝ) (ω : Ω) : ℝ :=
  powerLogDensity κ p α (a.solution.Q (a.clock.inverse s ω) ω)
    (B (a.clock.inverse s ω).toNNReal ω)

lemma radiusValue_continuous
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) (ω : Ω) :
    Continuous (fun s => a.radiusValue p α s ω) := by
  exact (powerLogDensity_contDiff κ p α).continuous.comp
    (((a.solution.lipschitz ω).continuous.comp (a.clock.continuous_inverse ω)).prodMk
      ((hBc ω).comp (continuous_real_toNNReal.comp (a.clock.continuous_inverse ω))))

lemma radiusValue_measurable
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (p α : ℝ) :
    Measurable (Function.uncurry (a.radiusValue p α)) := by
  exact (powerLogDensity_contDiff κ p α).continuous.measurable.comp
    ((a.solution.measurable.comp (a.inverse_measurable.prodMk measurable_snd)).prodMk
      (hBm.comp ((continuous_real_toNNReal.measurable.comp a.inverse_measurable).prodMk measurable_snd)))

lemma radiusValue_at_clock (p α : ℝ) (ω : Ω) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ)) :
    a.radiusValue p α (a.clock.S t ω) ω =
      powerLogDensity κ p α (a.solution.Q t ω) (B t.toNNReal ω) := by
  unfold radiusValue
  rw [a.clock.inverse_clock ω t ht]

lemma radius_integral_substitution
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) (ω : Ω) :
    (∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      powerLogDensity κ p α (a.solution.Q t ω) (B t.toNNReal ω) *
        logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)) =
      ∫ s in (0 : ℝ)..(a.clock.S (a.τ ω) ω), a.radiusValue p α s ω := by
  have hh := intervalIntegral.integral_comp_mul_deriv''
    (a.clock.continuous ω).continuousOn
    (f' := fun t => logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω))
    (a := (0 : ℝ)) (b := (a.τ ω : ℝ)) (g := fun s => a.radiusValue p α s ω)
    (fun t ht => by
      have ht' : t ∈ Ioo (0 : ℝ) (a.τ ω : ℝ) := by
        simpa only [min_eq_left (a.τ ω).coe_nonneg, max_eq_right (a.τ ω).coe_nonneg] using ht
      exact ((a.radius_clock_derivative ω t ⟨ht'.1.le, ht'.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)).hasDerivWithinAt)
    ((continuous_logClockRate κ).comp
      ((a.solution.lipschitz ω).continuous.prodMk ((hBc ω).comp continuous_real_toNNReal))).continuousOn
    (a.radiusValue_continuous hBc p α ω).continuousOn
  rw [a.clock.zero ω] at hh
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ) := by
    simpa only [uIcc_of_le (a.τ ω).coe_nonneg] using ht
  dsimp only [Function.comp_def]
  rw [a.radiusValue_at_clock p α ω t ht']

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma powerLogDensity_le_radius_angle
    (κ p α η₀ u ε : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (q : ℂ × ℝ) (x : ℝ)
    (hs : logRadiusClock η₀ q ≤ u) (ha : ε ≤ logAngleSq κ q x) :
    powerLogDensity κ p α q x ≤
      Real.exp (p * (u - Real.log 2 - η₀)) * max 1 (ε ^ (α / 2)) := by
  rw [powerLogDensity_radius_angle κ p α η₀ q x]
  have hpow : (logAngleSq κ q x) ^ (α / 2) ≤ max 1 (ε ^ (α / 2)) := by
    by_cases hp' : 0 ≤ α / 2
    · have hh : (logAngleSq κ q x) ^ (α / 2) ≤ 1 := by
        simpa only [Real.one_rpow] using
          (Real.rpow_le_rpow (logAngleSq_pos κ q x).le (logAngleSq_le_one κ q x) hp')
      exact hh.trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hε ha (le_of_not_ge hp')).trans (le_max_right _ _)
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hp))
    hpow (Real.rpow_nonneg (logAngleSq_pos κ q x).le _) (Real.exp_pos _).le

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε v δ : ℝ}
  (a : AngularLocalization B hm κ z u ε)

noncomputable def radiusKernel (p α s : ℝ) (ω : Ω) : ℝ :=
  if s ≤ a.clock.S (a.τ ω) ω then a.radiusValue p α s ω else 0

lemma radiusKernel_nonneg (p α s : ℝ) (ω : Ω) : 0 ≤ a.radiusKernel p α s ω := by
  unfold radiusKernel
  split_ifs
  · exact (powerLogDensity_pos _ _ _ _ _).le
  · rfl

lemma radiusKernel_le (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (s : ℝ) (ω : Ω) :
    a.radiusKernel p α s ω ≤
      Real.exp (p * (u - Real.log 2 - Real.log z.im)) * max 1 (ε ^ (α / 2)) := by
  have ht := a.clock.inverse_mem s ω
  have htn := Real.toNNReal_le_iff_le_coe.mpr ht.2
  have hh := a.inside ω (a.clock.inverse s ω).toNNReal htn
  rw [Real.coe_toNNReal _ ht.1] at hh
  unfold radiusKernel
  split_ifs
  · exact powerLogDensity_le_radius_angle κ p α (Real.log z.im) u ε hp hε _ _ hh.1 hh.2.1
  · exact mul_nonneg (Real.exp_pos _).le ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))

lemma radiusKernel_measurable
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (p α : ℝ) :
    Measurable (Function.uncurry (a.radiusKernel p α)) := by
  have ht : Measurable (fun q : ℝ × Ω => a.clock.S (a.τ q.2) q.2) :=
    a.clock_measurable.comp (((measurable_coe_nnreal_real.comp
      (stopping_time_measurable_nnreal a.stopping)).comp measurable_snd).prodMk measurable_snd)
  exact Measurable.ite (measurableSet_le measurable_fst ht) (a.radiusValue_measurable hBm p α) measurable_const

lemma radiusKernel_integral (p α : ℝ) (ω : Ω) :
    (∫ s in (0 : ℝ)..u, a.radiusKernel p α s ω) =
      ∫ s in (0 : ℝ)..(a.clock.S (a.τ ω) ω), a.radiusValue p α s ω := by
  change (∫ s in (0 : ℝ)..u,
    Set.indicator {s | s ≤ a.clock.S (a.τ ω) ω} (fun s => a.radiusValue p α s ω) s) = _
  exact intervalIntegral.integral_indicator ⟨a.clock.terminal_nonneg ω, a.clock_upper ω⟩

lemma synchronize_real (b : AngularLocalization B hm κ z v δ)
    (ω : Ω) (t : ℝ) (h0 : 0 ≤ t) (ha : t ≤ (a.τ ω : ℝ)) (hb : t ≤ (b.τ ω : ℝ)) :
    a.solution.Q t ω = b.solution.Q t ω := by
  simpa only [Real.coe_toNNReal t h0] using a.synchronize b ω t.toNNReal
    (Real.toNNReal_le_iff_le_coe.mpr ha) (Real.toNNReal_le_iff_le_coe.mpr hb)

lemma terminal_clock_le (b : AngularLocalization B hm κ z v δ)
    (huv : u ≤ v) (hδε : δ ≤ ε) (ω : Ω) :
    a.clock.S (a.τ ω) ω ≤ b.clock.S (b.τ ω) ω := by
  have ht := a.stopping_le b huv hδε ω
  have he := a.synchronize b ω (a.τ ω) le_rfl ht
  change logRadiusClock _ _ ≤ logRadiusClock _ _
  rw [he]
  exact (b.clock.strict ω).monotoneOn ⟨(a.τ ω).coe_nonneg, by exact_mod_cast ht⟩
    ⟨(b.τ ω).coe_nonneg, le_rfl⟩ (by exact_mod_cast ht)

lemma inverse_synchronize (b : AngularLocalization B hm κ z v δ)
    (huv : u ≤ v) (hδε : δ ≤ ε) (ω : Ω) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ a.clock.S (a.τ ω) ω) :
    a.clock.inverse s ω = b.clock.inverse s ω := by
  let t := a.clock.inverse s ω
  have htm := a.clock.inverse_mem s ω
  have hab : (a.τ ω : ℝ) ≤ (b.τ ω : ℝ) := by exact_mod_cast a.stopping_le b huv hδε ω
  have he : b.clock.S t ω = s := by
    change logRadiusClock _ (b.solution.Q t ω) = s
    rw [← a.synchronize_real b ω t htm.1 htm.2 (htm.2.trans hab)]
    change a.clock.S (a.clock.inverse s ω) ω = s
    rw [a.clock.clock_inverse, max_eq_left hs0]
    exact min_eq_left hs
  exact (b.clock.inverse_clock ω t ⟨htm.1, htm.2.trans hab⟩).symm.trans (by rw [he])

lemma radiusKernel_mono (b : AngularLocalization B hm κ z v δ)
    (huv : u ≤ v) (hδε : δ ≤ ε) (p α s : ℝ) (hs0 : 0 ≤ s) (ω : Ω) :
    a.radiusKernel p α s ω ≤ b.radiusKernel p α s ω := by
  by_cases hs : s ≤ a.clock.S (a.τ ω) ω
  · have hsb := hs.trans (a.terminal_clock_le b huv hδε ω)
    rw [radiusKernel, ite_eq_left hs, radiusKernel, ite_eq_left hsb]
    have he := a.inverse_synchronize b huv hδε ω s hs0 hs
    have htm := a.clock.inverse_mem s ω
    have hab : (a.τ ω : ℝ) ≤ (b.τ ω : ℝ) := by exact_mod_cast a.stopping_le b huv hδε ω
    unfold radiusValue
    rw [← he, a.synchronize_real b ω _ htm.1 htm.2 (htm.2.trans hab)]
  · rw [radiusKernel, ite_eq_right hs]
    exact b.radiusKernel_nonneg p α s ω

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma physical_power_continuous
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) (ω : Ω) :
    Continuous (fun t : ℝ =>
      powerLogDensity κ p α (a.solution.Q t ω) (B t.toNNReal ω) *
        logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)) := by
  have hq := (a.solution.lipschitz ω).continuous.prodMk ((hBc ω).comp continuous_real_toNNReal)
  exact ((powerLogDensity_contDiff κ p α).continuous.comp hq).mul
    ((continuous_logClockRate κ).comp hq)

lemma generator_radial_integral
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (b : ℝ) (ω : Ω) :
    (∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      powerLogGenerator κ (codimension κ) (greenExponent κ - b)
        (a.solution.Q t ω) (B t.toNNReal ω)) =
      (κ * b / 8) * ((1 + (greenExponent κ - b)) *
          (∫ s in (0 : ℝ)..u, a.radiusKernel (codimension κ) (greenExponent κ - b) s ω) -
        (greenExponent κ - b) *
          (∫ s in (0 : ℝ)..u, a.radiusKernel (codimension κ) (greenExponent κ - b - 2) s ω)) := by
  let f (α : ℝ) (t : ℝ) :=
    powerLogDensity κ (codimension κ) α (a.solution.Q t ω) (B t.toNNReal ω) *
      logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)
  have hfi (α : ℝ) : IntervalIntegrable (f α) volume (0 : ℝ) (a.τ ω : ℝ) :=
    (a.physical_power_continuous hBc (codimension κ) α ω).intervalIntegrable _ _
  have he (t : ℝ) : powerLogGenerator κ (codimension κ) (greenExponent κ - b)
      (a.solution.Q t ω) (B t.toNNReal ω) =
        (κ * b / 8) * ((1 + (greenExponent κ - b)) * f (greenExponent κ - b) t -
          (greenExponent κ - b) * f (greenExponent κ - b - 2) t) := by
    rw [powerLogGenerator_two_powers κ b hκ]
    dsimp only [f]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((hfi _).const_mul _) ((hfi _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [a.radiusKernel_integral, a.radiusKernel_integral,
    ← a.radius_integral_substitution hBc, ← a.radius_integral_substitution hBc]

lemma radiusKernel_cumulative_integrable
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (hu : 0 ≤ u) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..u, a.radiusKernel p α s ω) P := by
  let C := Real.exp (p * (u - Real.log 2 - Real.log z.im)) * max 1 (ε ^ (α / 2))
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))
  have hh := bounded_stopped_cumulative_integrable (P := P) (a.radiusKernel p α)
    (a.radiusKernel_measurable hBm p α) (fun _ => u.toNNReal) (fun _ => u.toNNReal)
    measurable_const (fun _ => le_rfl) u.toNNReal (fun _ => le_rfl) C hC
    (fun ω s _ _ => by
      rw [abs_of_nonneg (a.radiusKernel_nonneg p α s ω)]
      exact a.radiusKernel_le p α hp hε s ω)
  simpa only [Real.coe_toNNReal u hu] using hh.1

lemma radiusKernel_fubini
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (hu : 0 ≤ u) :
    (∫ ω, (∫ s in (0 : ℝ)..u, a.radiusKernel p α s ω) ∂P) =
      ∫ s in (0 : ℝ)..u, ∫ ω, a.radiusKernel p α s ω ∂P := by
  have hi : Integrable (Function.uncurry (a.radiusKernel p α)) ((volume.restrict (Ioc 0 u)).prod P) :=
    Integrable.of_bound (a.radiusKernel_measurable hBm p α).aestronglyMeasurable
      (Real.exp (p * (u - Real.log 2 - Real.log z.im)) * max 1 (ε ^ (α / 2)))
      (Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        change |a.radiusKernel p α q.1 q.2| ≤ _
        rw [abs_of_nonneg (a.radiusKernel_nonneg p α q.1 q.2)]
        exact a.radiusKernel_le p α hp hε q.1 q.2)
  simp_rw [intervalIntegral.integral_of_le hu]
  exact (integral_integral_swap hi).symm

 

theorem power_balance
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb : b ≤ greenExponent κ) (hε : 0 < ε) (hu : 0 ≤ u) :
    (∫ ω, powerLogDensity κ (codimension κ) (greenExponent κ - b)
      (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
      (κ * b / 8) * (greenExponent κ - b) *
        (∫ ω, (∫ s in (0 : ℝ)..u,
          a.radiusKernel (codimension κ) (greenExponent κ - b - 2) s ω) ∂P) =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 +
        (κ * b / 8) * (1 + (greenExponent κ - b)) *
          (∫ ω, (∫ s in (0 : ℝ)..u,
            a.radiusKernel (codimension κ) (greenExponent κ - b) s ω) ∂P) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨_, _, he⟩ := a.mean_power hB hBm hBc hB0 hκ.le (codimension κ)
    (greenExponent κ - b) (codimension_pos κ hκ8).le (sub_nonneg.mpr hb)
  simp_rw [a.generator_radial_integral hBc hκ b] at he
  rw [integral_const_mul,
    integral_sub ((a.radiusKernel_cumulative_integrable hBm _ _ (codimension_pos κ hκ8).le hε hu).const_mul _)
      ((a.radiusKernel_cumulative_integrable hBm _ _ (codimension_pos κ hκ8).le hε hu).const_mul _),
    integral_const_mul, integral_const_mul] at he
  linarith

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε δ : ℝ}

lemma radiusKernel_eq_of_live (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (huv : u ≤ v) (hδε : δ ≤ ε)
    (p α s : ℝ) (hs0 : 0 ≤ s) (ω : Ω) (hs : s ≤ a.clock.S (a.τ ω) ω) :
    a.radiusKernel p α s ω = b.radiusKernel p α s ω := by
  have hsb := hs.trans (a.terminal_clock_le b huv hδε ω)
  rw [radiusKernel, ite_eq_left hs, radiusKernel, ite_eq_left hsb]
  have he := a.inverse_synchronize b huv hδε ω s hs0 hs
  have htm := a.clock.inverse_mem s ω
  have hab : (a.τ ω : ℝ) ≤ (b.τ ω : ℝ) := by exact_mod_cast a.stopping_le b huv hδε ω
  unfold radiusValue
  rw [← he, a.synchronize_real b ω _ htm.1 htm.2 (htm.2.trans hab)]

lemma terminal_clock_min (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v ε) (huv : u ≤ v) (ω : Ω) :
    a.clock.S (a.τ ω) ω = min u (b.clock.S (b.τ ω) ω) := by
  have ht := a.stopping_le b huv le_rfl ω
  apply le_antisymm
  · exact le_min (a.clock_upper ω) (a.terminal_clock_le b huv le_rfl ω)
  · rcases a.boundary ω with hc | ha
    · exact (min_le_left _ _).trans_eq hc.symm
    · have he : a.τ ω = b.τ ω := by
        apply le_antisymm ht
        by_contra hn
        have hh := (b.before ω _ (lt_of_not_ge hn)).2
        rw [← a.synchronize b ω (a.τ ω) le_rfl ht, ha] at hh
        exact lt_irrefl _ hh
      have hq := a.synchronize b ω (a.τ ω) le_rfl ht
      change min u (logRadiusClock _ _) ≤ logRadiusClock _ _
      rw [hq, he]
      exact min_le_right _ _

lemma radiusKernel_eq_below (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v ε) (huv : u ≤ v)
    (p α s : ℝ) (hs0 : 0 ≤ s) (hsu : s ≤ u) (ω : Ω) :
    a.radiusKernel p α s ω = b.radiusKernel p α s ω := by
  by_cases hs : s ≤ a.clock.S (a.τ ω) ω
  · exact a.radiusKernel_eq_of_live b huv le_rfl p α s hs0 ω hs
  · have hsb : ¬ s ≤ b.clock.S (b.τ ω) ω := by
      intro h
      exact hs (by rw [a.terminal_clock_min b huv ω]; exact le_min hsu h)
    rw [radiusKernel, ite_eq_right hs, radiusKernel, ite_eq_right hsb]

lemma radiusKernel_uniform_bound (a : AngularLocalization B hm κ z u ε)
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (s : ℝ) (ω : Ω) :
    a.radiusKernel p α s ω ≤ Real.exp (p * (u - Real.log 2 - Real.log z.im)) := by
  unfold radiusKernel
  split_ifs
  · have ht := a.clock.inverse_mem s ω
    have hh := a.inside ω (a.clock.inverse s ω).toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)
    rw [Real.coe_toNNReal _ ht.1] at hh
    exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp hα _ _ hh.1
  · exact (Real.exp_pos _).le

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

 

noncomputable def limitRadiusKernel (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (p α s : ℝ) (ω : Ω) : ℝ :=
  if h : ∃ n, max s 0 ≤ (a n).clock.S ((a n).τ ω) ω then
    (a (Nat.find h)).radiusKernel p α (max s 0) ω else 0

lemma radiusKernel_eventually_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α s : ℝ) (ω : Ω) :
    ∀ᶠ n in atTop, (a n).radiusKernel p α (max s 0) ω = limitRadiusKernel a p α s ω := by
  unfold limitRadiusKernel
  split_ifs with hh
  · filter_upwards [eventually_ge_atTop (Nat.find hh)] with n hn
    exact ((a (Nat.find hh)).radiusKernel_eq_of_live (a n) le_rfl (hε hn)
      p α _ (le_max_right _ _) ω (Nat.find_spec hh)).symm
  · apply Eventually.of_forall
    intro n
    have hn : ¬ max s 0 ≤ (a n).clock.S ((a n).τ ω) ω := fun h => hh ⟨n, h⟩
    rw [AngularLocalization.radiusKernel, ite_eq_right hn]

lemma limitRadiusKernel_nonneg
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (p α s : ℝ) (ω : Ω) :
    0 ≤ limitRadiusKernel a p α s ω := by
  unfold limitRadiusKernel
  split_ifs
  · exact AngularLocalization.radiusKernel_nonneg _ _ _ _ _
  · rfl

lemma limitRadiusKernel_measurable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (p α : ℝ) :
    Measurable (Function.uncurry (limitRadiusKernel a p α)) := by
  apply measurable_of_tendsto_metrizable
    (fun n => ((a n).radiusKernel_measurable hBm p α).comp
      ((measurable_fst.max measurable_const).prodMk measurable_snd))
  apply tendsto_pi_nhds.mpr
  intro q
  apply tendsto_const_nhds.congr'
  filter_upwards [radiusKernel_eventually_limit a hε p α q.1 q.2] with n hn
  exact hn.symm

lemma limitRadiusKernel_uniform_bound
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (s : ℝ) (ω : Ω) :
    limitRadiusKernel a p α s ω ≤ Real.exp (p * (u - Real.log 2 - Real.log z.im)) := by
  unfold limitRadiusKernel
  split_ifs
  · exact AngularLocalization.radiusKernel_uniform_bound _ _ _ hp hα _ _
  · exact (Real.exp_pos _).le

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

def hit (a : AngularLocalization B hm κ z u ε) : Set Ω :=
  {ω | logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω) = u}

lemma measurable_hit (a : AngularLocalization B hm κ z u ε) :
    MeasurableSet[a.stopping.measurableSpace] a.hit :=
  measurableSet_eq_fun a.clock_stopped_measurable measurable_const

noncomputable def hitTime (a : AngularLocalization B hm κ z u ε) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ a.hit then (a.τ ω : WithTop ℝ≥0) else ⊤

lemma hitTime_stopping (a : AngularLocalization B hm κ z u ε) :
    IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) a.hitTime := by
  intro t
  have he : {ω | a.hitTime ω ≤ (t : WithTop ℝ≥0)} = a.hit ∩ {ω | (a.τ ω : WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [hitTime, mem_ofPred_eq, mem_inter_iff]
    split_ifs with h
    · simp only [h, true_and]
    · simp only [h, false_and, iff_false]
      exact WithTop.not_top_le_coe t
  rw [he]
  exact a.measurable_hit.2 t

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

 

noncomputable def localizedRadiusStop
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ n, (a n).hitTime ω

lemma localizedRadiusStop_eq_hit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) (n : ℕ)
    (hn : ω ∈ (a n).hit) : localizedRadiusStop a ω = ((a n).τ ω : WithTop ℝ≥0) := by
  apply le_antisymm
  · exact (iInf_le _ n).trans_eq (by rw [AngularLocalization.hitTime, ite_eq_left hn])
  · apply le_iInf
    intro m
    by_cases h : ω ∈ (a m).hit
    · have he := (a m).hit_time_unique (a n) ω h hn
      rw [AngularLocalization.hitTime, ite_eq_left h, he]
    · rw [AngularLocalization.hitTime, ite_eq_right h]
      exact le_top

lemma localizedRadiusStop_eq_top
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω)
    (hn : ∀ n, ω ∉ (a n).hit) : localizedRadiusStop a ω = ⊤ := by
  simp [localizedRadiusStop, AngularLocalization.hitTime, hn]

lemma localizedRadiusStop_le_iff
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) (t : ℝ≥0) :
    localizedRadiusStop a ω ≤ (t : WithTop ℝ≥0) ↔ ∃ n, ω ∈ (a n).hit ∧ (a n).τ ω ≤ t := by
  constructor
  · intro h
    by_cases he : ∃ n, ω ∈ (a n).hit
    · obtain ⟨n, hn⟩ := he
      rw [localizedRadiusStop_eq_hit a ω n hn, WithTop.coe_le_coe] at h
      exact ⟨n, hn, h⟩
    · rw [localizedRadiusStop_eq_top a ω (not_exists.mp he)] at h
      exact False.elim (WithTop.coe_ne_top (a := t) (top_le_iff.mp h))
  · rintro ⟨n, hn, ht⟩
    rw [localizedRadiusStop_eq_hit a ω n hn, WithTop.coe_le_coe]
    exact ht

lemma localizedRadiusStop_stopping
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) :
    IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (localizedRadiusStop a) := by
  intro t
  have he : {ω | localizedRadiusStop a ω ≤ (t : WithTop ℝ≥0)} =
      ⋃ n, ((a n).hit ∩ {ω | ((a n).τ ω : WithTop ℝ≥0) ≤ t}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, WithTop.coe_le_coe]
    exact localizedRadiusStop_le_iff a ω t
  rw [he]
  exact MeasurableSet.iUnion fun n => (a n).measurable_hit.2 t

lemma localizedRadiusStop_history_hit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[(localizedRadiusStop_stopping a).measurableSpace] A) :
    MeasurableSet[(a n).stopping.measurableSpace] (A ∩ (a n).hit) := by
  refine ⟨hA.1.inter (a n).measurable_hit.1, ?_⟩
  intro t
  have he : (A ∩ (a n).hit) ∩ {ω | ((a n).τ ω : WithTop ℝ≥0) ≤ t} =
      (A ∩ {ω | localizedRadiusStop a ω ≤ (t : WithTop ℝ≥0)}) ∩
        ((a n).hit ∩ {ω | ((a n).τ ω : WithTop ℝ≥0) ≤ t}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hωA, hωn⟩, hωt⟩
      exact ⟨⟨hωA, (localizedRadiusStop_eq_hit a ω n hωn) ▸ hωt⟩, hωn, hωt⟩
    · rintro ⟨⟨hωA, _⟩, hωn, hωt⟩
      exact ⟨⟨hωA, hωn⟩, hωt⟩
  rw [he]
  exact (hA.2 t).inter ((a n).measurable_hit.2 t)

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

 

lemma integrable_monotone_limit_of_integral_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) P)
    (hF : AEStronglyMeasurable F P)
    (hn : ∀ n ω, 0 ≤ f n ω) (hFn : ∀ ω, 0 ≤ F ω)
    (hmono : ∀ ω, Monotone (fun n => f n ω))
    (hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)))
    (C : ℝ) (hbound : ∀ n, (∫ ω, f n ω ∂P) ≤ C) :
    Integrable F P ∧
      Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, F ω ∂P)) := by
  have hl : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (F ω) ∂P)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hf n).aemeasurable.ennreal_ofReal)
    · exact Eventually.of_forall fun ω n m hnm => ENNReal.ofReal_le_ofReal (hmono ω hnm)
    · exact Eventually.of_forall fun ω => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim ω)
  have hle : (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) ≤ ENNReal.ofReal C := by
    apply le_of_tendsto hl
    apply Eventually.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Eventually.of_forall (hn n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hFi : Integrable F P := by
    refine ⟨hF, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have he : (fun ω => ‖F ω‖ₑ) = fun ω => ENNReal.ofReal (F ω) := by
      funext ω
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hFn ω)]
    rw [he]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  exact ⟨hFi, integral_tendsto_of_tendsto_of_monotone hf hFi
    (Eventually.of_forall hmono) (Eventually.of_forall hlim)⟩
end SLEExactGauge
end

 
end

end OAI
