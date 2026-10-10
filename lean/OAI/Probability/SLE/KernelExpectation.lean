import Mathlib
import OAI.Probability.SLE.AngularPowerDynkin

namespace OAI

/-! Kernel Expectation for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε : ℝ}

lemma stopped_power_eq_kernel_of_hit (a : AngularLocalization B hm κ z u ε)
    (p α : ℝ) (ω : Ω) (hh : ω ∈ a.hit) :
    powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) =
      a.radiusKernel p α u ω := by
  have hc : a.clock.S (a.τ ω) ω = u := hh
  rw [radiusKernel, ite_eq_left hc.ge]
  simpa only [hc, Real.toNNReal_coe] using
    (a.radiusValue_at_clock p α ω _ ⟨(a.τ ω).coe_nonneg, le_rfl⟩).symm

lemma stopped_power_kernel_gap (a : AngularLocalization B hm κ z u ε)
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 ≤ ε) (ω : Ω) :
    0 ≤ powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) -
      a.radiusKernel p α u ω ∧
    powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) -
      a.radiusKernel p α u ω ≤
        Real.exp (p * (u - Real.log 2 - Real.log z.im)) * ε ^ (α / 2) := by
  by_cases hh : ω ∈ a.hit
  · rw [a.stopped_power_eq_kernel_of_hit p α ω hh, sub_self]
    exact ⟨le_rfl, mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hε _)⟩
  · have hc : ¬ u ≤ a.clock.S (a.τ ω) ω := by
      intro h
      exact hh (le_antisymm (a.clock_upper ω) h)
    rw [radiusKernel, ite_eq_right hc, sub_zero]
    refine ⟨(powerLogDensity_pos _ _ _ _ _).le, ?_⟩
    have ha := (a.boundary ω).resolve_left hh
    rw [powerLogDensity_radius_angle κ p α (Real.log z.im), ha]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by
      rw [← ha]; exact (logAngleSq_pos _ _ _).le) _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [(a.inside ω _ le_rfl).1]) hp

lemma radiusKernel_region_integrable
    (a : AngularLocalization B hm κ z u ε) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (v : ℝ) :
    Integrable (fun q : ℝ × Ω => a.radiusKernel p α (max q.1 0) q.2)
      ((volume.restrict (Ioc 0 v)).prod P) := by
  apply Integrable.of_bound
    (((a.radiusKernel_measurable hBm p α).comp
      ((measurable_fst.max measurable_const).prodMk measurable_snd)).aestronglyMeasurable)
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)) * max 1 (ε ^ (α / 2)))
  exact Eventually.of_forall fun q => by
    change ‖a.radiusKernel p α (max q.1 0) q.2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (a.radiusKernel_nonneg p α _ _)]
    exact a.radiusKernel_le p α hp hε _ _

lemma radiusKernel_region_integral
    (a : AngularLocalization B hm κ z u ε) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (v : ℝ) (hv : 0 ≤ v) :
    (∫ q : ℝ × Ω, a.radiusKernel p α (max q.1 0) q.2
      ∂((volume.restrict (Ioc 0 v)).prod P)) =
      ∫ ω, (∫ s in (0 : ℝ)..v, a.radiusKernel p α s ω) ∂P := by
  rw [integral_prod_symm _ (a.radiusKernel_region_integrable hBm p α hp hε v)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    dsimp only
    rw [intervalIntegral.integral_of_le hv]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [max_eq_left hs.1.le]

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (s : ℝ) :
    Integrable (limitRadiusKernel a p α s) P := by
  apply Integrable.of_bound
    (((limitRadiusKernel_measurable a hε hBm p α).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
  exact Eventually.of_forall fun ω => by
    change ‖limitRadiusKernel a p α s ω‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (limitRadiusKernel_nonneg a p α s ω)]
    exact limitRadiusKernel_uniform_bound a p α hp hα s ω

lemma limitRadiusKernel_region_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (v : ℝ) :
    Integrable (Function.uncurry (limitRadiusKernel a p α))
      ((volume.restrict (Ioc 0 v)).prod P) := by
  apply Integrable.of_bound (limitRadiusKernel_measurable a hε hBm p α).aestronglyMeasurable
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
  exact Eventually.of_forall fun q => by
    change ‖limitRadiusKernel a p α q.1 q.2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (limitRadiusKernel_nonneg a p α q.1 q.2)]
    exact limitRadiusKernel_uniform_bound a p α hp hα q.1 q.2

lemma radiusKernel_region_integral_tendsto
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (v : ℝ) :
    Tendsto (fun n => ∫ q : ℝ × Ω, (a n).radiusKernel p α (max q.1 0) q.2
        ∂((volume.restrict (Ioc 0 v)).prod P)) atTop
      (𝓝 (∫ q : ℝ × Ω, limitRadiusKernel a p α q.1 q.2
        ∂((volume.restrict (Ioc 0 v)).prod P))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (p * (u - Real.log 2 - Real.log z.im)))
    (fun n => (((a n).radiusKernel_measurable hBm p α).comp
      ((measurable_fst.max measurable_const).prodMk measurable_snd)).aestronglyMeasurable)
    (integrable_const _)
  · intro n
    exact Eventually.of_forall fun q => by
      change ‖(a n).radiusKernel p α (max q.1 0) q.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg ((a n).radiusKernel_nonneg p α _ _)]
      exact (a n).radiusKernel_uniform_bound p α hp hα _ _
  · apply Eventually.of_forall
    intro q
    apply tendsto_const_nhds.congr'
    filter_upwards [radiusKernel_eventually_limit a hε p α q.1 q.2] with n hn
    exact hn.symm

lemma stopped_power_tendsto_limitRadiusKernel
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    (hu : 0 ≤ u) (huv : u ≤ v) (p α : ℝ) (hp : 0 ≤ p) (hα : 0 < α) (ω : Ω) :
    Tendsto (fun n => powerLogDensity κ p α ((a n).solution.Q ((a n).τ ω) ω)
      (B ((a n).τ ω) ω)) atTop (𝓝 (limitRadiusKernel b p α u ω)) := by
  have hk : Tendsto (fun n => (a n).radiusKernel p α u ω) atTop
      (𝓝 (limitRadiusKernel b p α u ω)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [radiusKernel_eventually_limit b hε p α u ω] with n hn
    rw [max_eq_left hu] at hn
    exact (hn.symm.trans ((a n).radiusKernel_eq_below (b n) huv p α u hu le_rfl ω).symm)
  have ht : Tendsto (fun n => Real.exp (p * (u - Real.log 2 - Real.log z.im)) *
      ε n ^ (α / 2)) atTop (𝓝 0) := by
    have hh := ((Real.continuousAt_rpow_const 0 (α / 2) (Or.inr (by positivity))).tendsto.comp hεlim).const_mul
      (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
    simpa only [Real.zero_rpow (by positivity : α / 2 ≠ 0), mul_zero, Function.comp_def] using hh
  have hg := squeeze_zero (fun n => ((a n).stopped_power_kernel_gap p α hp (hε0 n) ω).1)
    (fun n => ((a n).stopped_power_kernel_gap p α hp (hε0 n) ω).2) ht
  have hh := hg.add hk
  simpa only [sub_add_cancel, zero_add] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε : ℝ}

lemma stopped_power_uniform_integrable
    (a : AngularLocalization B hm κ z u ε) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) :
    Integrable (fun ω => powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) P := by
  apply a.solution.stopped_power_integrable hBm p α a.τ
    (stopping_time_measurable_nnreal a.stopping)
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
  intro ω
  rw [abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
  exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp hα _ _ (a.inside ω _ le_rfl).1

lemma radiusKernel_region_integral_eq_below
    (a : AngularLocalization B hm κ z u ε) (b : AngularLocalization B hm κ z v ε)
    (huv : u ≤ v) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (hu : 0 ≤ u) :
    (∫ q : ℝ × Ω, b.radiusKernel p α (max q.1 0) q.2
        ∂((volume.restrict (Ioc 0 u)).prod P)) =
      ∫ ω, (∫ s in (0 : ℝ)..u, a.radiusKernel p α s ω) ∂P := by
  rw [b.radiusKernel_region_integral hBm p α hp hε u hu]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 u := by simpa only [uIcc_of_le hu] using hs
  exact (a.radiusKernel_eq_below b huv p α s hs'.1 hs'.2 ω).symm

lemma power_balance_below
    (a : AngularLocalization B hm κ z u ε) (c : AngularLocalization B hm κ z v ε)
    (huv : u ≤ v) {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb : b ≤ greenExponent κ)
    (hε : 0 < ε) (hu : 0 ≤ u) :
    (∫ ω, powerLogDensity κ (codimension κ) (greenExponent κ - b)
        (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
      (κ * b / 8) * (greenExponent κ - b) *
        (∫ q : ℝ × Ω, c.radiusKernel (codimension κ) (greenExponent κ - b - 2) (max q.1 0) q.2
          ∂((volume.restrict (Ioc 0 u)).prod P)) =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 +
        (κ * b / 8) * (1 + (greenExponent κ - b)) *
          (∫ q : ℝ × Ω, c.radiusKernel (codimension κ) (greenExponent κ - b) (max q.1 0) q.2
            ∂((volume.restrict (Ioc 0 u)).prod P)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [a.radiusKernel_region_integral_eq_below c huv hBm _ _ (codimension_pos κ hκ8).le hε hu,
    a.radiusKernel_region_integral_eq_below c huv hBm _ _ (codimension_pos κ hκ8).le hε hu]
  exact a.power_balance hB hBm hBc hB0 hκ hκ8 b hb hε hu

end AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma stopped_power_integral_tendsto_limitRadiusKernel
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hu : 0 ≤ u) (huv : u ≤ v) (p α : ℝ) (hp : 0 ≤ p) (hα : 0 < α) :
    Tendsto (fun n => ∫ ω, powerLogDensity κ p α ((a n).solution.Q ((a n).τ ω) ω)
      (B ((a n).τ ω) ω) ∂P) atTop (𝓝 (∫ ω, limitRadiusKernel b p α u ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (p * (u - Real.log 2 - Real.log z.im)))
    (fun n => ((a n).stopped_power_uniform_integrable hBm p α hp hα.le).aestronglyMeasurable)
    (integrable_const _)
  · intro n
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
      exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp hα.le _ _ ((a n).inside ω _ le_rfl).1
  · exact Eventually.of_forall fun ω => stopped_power_tendsto_limitRadiusKernel a b hε hεlim hε0
      hu huv p α hp hα ω

 

theorem limit_power_balance
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (c : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Integrable (Function.uncurry (limitRadiusKernel c (codimension κ) (greenExponent κ - b - 2)))
        ((volume.restrict (Ioc 0 u)).prod P) ∧
    (∫ ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) u ω ∂P) +
      (κ * b / 8) * (greenExponent κ - b) *
        (∫ q : ℝ × Ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b - 2) q.1 q.2
          ∂((volume.restrict (Ioc 0 u)).prod P)) =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 +
        (κ * b / 8) * (1 + (greenExponent κ - b)) *
          (∫ q : ℝ × Ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) q.1 q.2
            ∂((volume.restrict (Ioc 0 u)).prod P)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let p := codimension κ
  let α := greenExponent κ - b
  let lam := κ * b / 8
  have hp : 0 ≤ p := (codimension_pos κ hκ8).le
  have hα : 0 < α := sub_pos.mpr hb
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hla : 0 < lam * α := mul_pos hlam hα
  have he (n : ℕ) := (a n).power_balance_below (c n) huv hB hBm hBc hB0 hκ hκ8 b hb.le (hε0 n) hu
  have hl := radiusKernel_region_integral_tendsto (P := P) c hε hBm p α hp hα.le u
  obtain ⟨C, hC⟩ := hl.bddAbove_range
  let D := (powerLogDensity κ p α (initialLogCoordinates z) 0 + lam * (1 + α) * C) / (lam * α)
  have hbound (n : ℕ) : (∫ q : ℝ × Ω, (c n).radiusKernel p (α - 2) (max q.1 0) q.2
      ∂((volume.restrict (Ioc 0 u)).prod P)) ≤ D := by
    apply (le_div_iff₀ hla).mpr
    have hnon : 0 ≤ (∫ ω, powerLogDensity κ p α
        ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) ∂P) :=
      integral_nonneg fun ω => (powerLogDensity_pos κ p α
        ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω)).le
    have hlow := mul_le_mul_of_nonneg_left (hC (mem_range_self n)) (mul_nonneg hlam.le (by linarith : 0 ≤ 1 + α))
    dsimp only [p, α, lam] at hnon hlow ⊢
    nlinarith [he n]
  obtain ⟨hhigh, hhighlim⟩ := integrable_monotone_limit_of_integral_le
    (fun n => (c n).radiusKernel_region_integrable hBm p (α - 2) hp (hε0 n) u)
    (limitRadiusKernel_measurable c hε hBm p (α - 2)).aestronglyMeasurable
    (fun n q => (c n).radiusKernel_nonneg p (α - 2) _ _)
    (fun q => limitRadiusKernel_nonneg c p (α - 2) q.1 q.2)
    (fun q n m hnm => (c n).radiusKernel_mono (c m) le_rfl (hε hnm) p (α - 2) _ (le_max_right _ _) _)
    (fun q => by
      apply tendsto_const_nhds.congr'
      filter_upwards [radiusKernel_eventually_limit c hε p (α - 2) q.1 q.2] with n hn
      exact hn.symm) D hbound
  refine ⟨hhigh, ?_⟩
  have hs := stopped_power_integral_tendsto_limitRadiusKernel (P := P) a c hε hεlim (fun n => (hε0 n).le)
    hBm hu huv p α hp hα
  have hleft := hs.add (hhighlim.const_mul (lam * α))
  have hright := (hl.const_mul (lam * (1 + α))).const_add (powerLogDensity κ p α (initialLogCoordinates z) 0)
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n => (he n).symm))

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
  (a : AngularLocalization B hm κ z u ε)

lemma radiusValue_factor (p α s : ℝ) (hs : 0 ≤ s) (ω : Ω)
    (hl : s ≤ a.clock.S (a.τ ω) ω) :
    a.radiusValue p α s ω =
      Real.exp (p * (s - Real.log 2 - Real.log z.im)) *
        (a.radiusValue 0 2 s ω) ^ (α / 2) := by
  have hc : a.clock.S (a.clock.inverse s ω) ω = s := by
    rw [a.clock.clock_inverse, max_eq_left hs]
    exact min_eq_left hl
  have he : a.radiusValue 0 2 s ω =
      logAngleSq κ (a.solution.Q (a.clock.inverse s ω) ω) (B (a.clock.inverse s ω).toNNReal ω) := by
    rw [radiusValue, powerLogDensity_radius_angle κ 0 2 (Real.log z.im)]
    norm_num
  rw [he, radiusValue, powerLogDensity_radius_angle κ p α (Real.log z.im)]
  change Real.exp (p * (a.clock.S (a.clock.inverse s ω) ω - _ - _)) * _ = _
  rw [hc]

lemma radiusKernel_zero (p s : ℝ) (hs : 0 ≤ s) (ω : Ω) :
    a.radiusKernel p 0 s ω = if s ≤ a.clock.S (a.τ ω) ω then
      Real.exp (p * (s - Real.log 2 - Real.log z.im)) else 0 := by
  unfold radiusKernel
  split_ifs with h
  · rw [a.radiusValue_factor p 0 s hs ω h, zero_div, Real.rpow_zero, mul_one]
  · rfl

lemma radiusKernel_power_factor (p α β s : ℝ) (hs : 0 ≤ s) (ω : Ω) :
    a.radiusKernel p (α + β) s ω = a.radiusKernel p α s ω *
      (a.radiusKernel 0 2 s ω) ^ (β / 2) := by
  unfold radiusKernel
  split_ifs with hl
  · rw [a.radiusValue_factor p (α + β) s hs ω hl,
      a.radiusValue_factor p α s hs ω hl]
    have hpos : 0 < a.radiusValue 0 2 s ω := powerLogDensity_pos _ _ _ _ _
    rw [add_div, Real.rpow_add hpos]
    ring
  · simp

end AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_zero
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (p s : ℝ) (ω : Ω) :
    limitRadiusKernel a p 0 s ω =
      if ∃ n, max s 0 ≤ (a n).clock.S ((a n).τ ω) ω then
        Real.exp (p * (max s 0 - Real.log 2 - Real.log z.im)) else 0 := by
  unfold limitRadiusKernel
  split_ifs with hh
  · rw [(a (Nat.find hh)).radiusKernel_zero p (max s 0) (le_max_right _ _) ω,
      ite_eq_left (Nat.find_spec hh)]
  · rfl

lemma limitRadiusKernel_zero_growth
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (p s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    limitRadiusKernel a p 0 t ω ≤ Real.exp (p * (t - s)) * limitRadiusKernel a p 0 s ω := by
  by_cases hh : ∃ n, t ≤ (a n).clock.S ((a n).τ ω) ω
  · have hh' : ∃ n, s ≤ (a n).clock.S ((a n).τ ω) ω := by
      obtain ⟨n, hn⟩ := hh
      exact ⟨n, hst.trans hn⟩
    rw [limitRadiusKernel_zero, max_eq_left (hs.trans hst), ite_eq_left hh,
      limitRadiusKernel_zero, max_eq_left hs, ite_eq_left hh', ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring
  · rw [limitRadiusKernel_zero a p t ω, max_eq_left (hs.trans hst), ite_eq_right hh]
    exact mul_nonneg (Real.exp_pos _).le (limitRadiusKernel_nonneg a p 0 s ω)

lemma limitRadiusKernel_power_factor
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α β s : ℝ) (ω : Ω) :
    limitRadiusKernel a p (α + β) s ω = limitRadiusKernel a p α s ω *
      (limitRadiusKernel a 0 2 s ω) ^ (β / 2) := by
  obtain ⟨n, h1, h2, h3⟩ := ((radiusKernel_eventually_limit a hε p (α + β) s ω).and
    ((radiusKernel_eventually_limit a hε p α s ω).and
      (radiusKernel_eventually_limit a hε 0 2 s ω))).exists
  rw [← h1, ← h2, ← h3]
  exact (a n).radiusKernel_power_factor p α β _ (le_max_right _ _) ω

lemma limitRadiusKernel_angle_le_one
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (s : ℝ) (ω : Ω) :
    limitRadiusKernel a 0 2 s ω ≤ 1 := by
  simpa only [zero_mul, Real.exp_zero] using
    limitRadiusKernel_uniform_bound a 0 2 le_rfl (by norm_num) s ω

lemma integral_limitRadiusKernel_zero_growth
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p s t : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ ω, limitRadiusKernel a p 0 t ω ∂P) ≤
      Real.exp (p * (t - s)) * (∫ ω, limitRadiusKernel a p 0 s ω ∂P) := by
  rw [← integral_const_mul]
  exact integral_mono (limitRadiusKernel_integrable a hε hBm p 0 hp le_rfl t)
    ((limitRadiusKernel_integrable a hε hBm p 0 hp le_rfl s).const_mul _)
    (fun ω => limitRadiusKernel_zero_growth a p s t hs hst ω)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

 

lemma weighted_rpow_jensen {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {w f : Ω → ℝ} {I q : ℝ} (hI : 0 < I)
    (hw : Integrable w P) (hw0 : ∀ ω, 0 ≤ w ω) (hmean : (∫ ω, w ω ∂P) = I)
    (hf0 : ∀ ω, 0 ≤ f ω) (hq : 1 ≤ q)
    (hfi : Integrable (fun ω => w ω * f ω) P)
    (hfqi : Integrable (fun ω => w ω * (f ω) ^ q) P) :
    ((∫ ω, w ω * f ω ∂P) / I) ^ q ≤ (∫ ω, w ω * (f ω) ^ q ∂P) / I := by
  let d (ω : Ω) : ℝ≥0∞ := ENNReal.ofReal (w ω / I)
  have hd : AEMeasurable d P := (hw.div_const I).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hd0 (ω : Ω) : (d ω).toReal = w ω / I := ENNReal.toReal_ofReal (div_nonneg (hw0 ω) hI.le)
  let Q := P.withDensity d
  have hprob : IsProbabilityMeasure Q := by
    constructor
    rw [show Q = P.withDensity d from rfl, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    change (∫⁻ ω, ENNReal.ofReal (w ω / I) ∂P) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (hw.div_const I)
      (Eventually.of_forall fun ω => div_nonneg (hw0 ω) hI.le), integral_div,
      hmean, div_self hI.ne', ENNReal.ofReal_one]
  let := hprob
  have he (g : Ω → ℝ) : (fun ω => (d ω).toReal • g ω) = (fun ω => (w ω * g ω) / I) := by
    funext ω
    rw [hd0, smul_eq_mul]
    ring
  have hi : Integrable f Q := by
    apply (integrable_withDensity_iff_integrable_smul₀' hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    rw [he]
    exact hfi.div_const I
  have hqi : Integrable (fun ω => (f ω) ^ q) Q := by
    apply (integrable_withDensity_iff_integrable_smul₀' hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    rw [he]
    exact hfqi.div_const I
  have hj := (convexOn_rpow hq).map_integral_le
    (Real.continuous_rpow_const (by positivity : 0 ≤ q)).continuousOn isClosed_Ici
    (Eventually.of_forall hf0) hi hqi
  have hint (g : Ω → ℝ) : (∫ ω, g ω ∂Q) = (∫ ω, w ω * g ω ∂P) / I := by
    rw [show Q = P.withDensity d from rfl, integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), he, integral_div]
  simpa only [hint] using hj

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_green_mean
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (c : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    (∫ ω, limitRadiusKernel c (codimension κ) (greenExponent κ) u ω ∂P) = initialGreen κ z := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ht := stopped_power_integral_tendsto_limitRadiusKernel (P := P) a c hε hεlim hε0 hBm hu huv
    (codimension κ) (greenExponent κ) (codimension_pos κ hκ8).le (greenExponent_pos κ hκ hκ8)
  have he (n : ℕ) : (∫ ω, powerLogDensity κ (codimension κ) (greenExponent κ)
      ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) ∂P) = initialGreen κ z :=
    ((a n).mean_green hB hBm hBc hB0 hκ hκ8 hz).2
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (he n).symm))

lemma limitRadiusKernel_inverse_factor
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    (p a b s : ℝ) (ω : Ω) :
    limitRadiusKernel c p (a - b) s ω = limitRadiusKernel c p a s ω *
      (limitRadiusKernel c 0 2 s ω) ^ (-b / 2) := by
  simpa only [sub_eq_add_neg] using limitRadiusKernel_power_factor c hε p a (-b) s ω

lemma limitRadiusKernel_inverse_moment_jensen
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p a b s I : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (hab : b ≤ a)
    (hI : 0 < I) (hmean : (∫ ω, limitRadiusKernel c p a s ω ∂P) = I)
    (hi : Integrable (limitRadiusKernel c p (a - b - 2) s) P) :
    ((∫ ω, limitRadiusKernel c p (a - b) s ω ∂P) / I) ^ (1 + 2 / b) ≤
      (∫ ω, limitRadiusKernel c p (a - b - 2) s ω ∂P) / I := by
  let w := limitRadiusKernel c p a s
  let f (ω : Ω) := (limitRadiusKernel c 0 2 s ω) ^ (-b / 2)
  have he (ω : Ω) : w ω * f ω = limitRadiusKernel c p (a - b) s ω :=
    (limitRadiusKernel_inverse_factor c hε p a b s ω).symm
  have heq (ω : Ω) : w ω * (f ω) ^ (1 + 2 / b) = limitRadiusKernel c p (a - b - 2) s ω := by
    dsimp only [f, w]
    rw [← Real.rpow_mul (limitRadiusKernel_nonneg c 0 2 s ω)]
    have hexp : -b / 2 * (1 + 2 / b) = -(b + 2) / 2 := by field_simp
    rw [hexp, ← limitRadiusKernel_inverse_factor c hε p a (b + 2) s ω]
    rw [show a - (b + 2) = a - b - 2 by ring]
  have hfi : Integrable (fun ω => w ω * f ω) P := by
    simpa only [he] using limitRadiusKernel_integrable c hε hBm p (a - b) hp (sub_nonneg.mpr hab) s
  have hfqi : Integrable (fun ω => w ω * (f ω) ^ (1 + 2 / b)) P := by simpa only [heq] using hi
  have hj := weighted_rpow_jensen (w := w) (f := f) hI (limitRadiusKernel_integrable c hε hBm p a hp ha s)
    (limitRadiusKernel_nonneg c p a s) hmean
    (fun ω => Real.rpow_nonneg (limitRadiusKernel_nonneg c 0 2 s ω) _)
    (le_add_of_nonneg_right (div_nonneg (by norm_num) hb.le) : 1 ≤ 1 + 2 / b) hfi hfqi
  simpa only [he, heq] using hj

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

noncomputable def weight (a : AngularLocalization B hm κ z u ε) (ω : Ω) : ℝ :=
  greenLogDensity κ (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)

lemma weight_bound (a : AngularLocalization B hm κ z u ε)
    (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) :
    0 ≤ a.weight ω ∧ a.weight ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) :=
  ⟨greenLogDensity_nonneg _ _ _, greenLogDensity_le_radius κ _ u hκ hκ8 _ _ (a.inside ω _ le_rfl).1⟩

lemma radius_at_hit (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hh : ω ∈ a.hit) :
    z ∈ survivingDomain γ (a.τ ω) ∧ fullRadius G (a.τ ω) z = (2 * z.im) * Real.exp (-u) := by
  have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
  have hl := (a.chart_identification hBc hz ω γ G F hw).1
  refine ⟨hl, (fullRadius_level_iff_logClock hU hw z _ hl u).mpr ?_⟩
  rw [logRadiusClock_logCoordinates hU hw z _ hl, ← a.clock_eq_chart hBc hz ω γ G F hw _ le_rfl]
  exact hh

lemma weight_eq_source (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    a.weight ω = greenDensity κ (fun t => Real.sqrt κ * B t ω) γ G (a.τ ω) z := by
  obtain ⟨hl, he⟩ := a.chart_identification hBc hz ω γ G F hw
  rw [weight, he _ le_rfl]
  exact greenLogDensity_logCoordinates ((hBc ω).const_mul _) hw κ _ z _ hl rfl

lemma weight_eq_stoppedGreen_of_hit (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hh : ω ∈ a.hit) :
    a.weight ω = stoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G z u := by
  obtain ⟨hl, hR⟩ := a.radius_at_hit hBc hz ω γ G F hw hh
  rw [stoppedGreen_eq_of_live_level ((hBc ω).const_mul _) hw κ z u _ hl hR]
  exact a.weight_eq_source hBc hz ω γ G F hw

lemma weight_small_of_not_hit (a : AngularLocalization B hm κ z u ε)
    (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) (hn : ω ∉ a.hit) :
    a.weight ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) *
      ε ^ (greenExponent κ / 2) := by
  exact greenLogDensity_le_at_angular_exit κ _ u ε hκ hκ8 _ _ (a.inside ω _ le_rfl).1
    ((a.boundary ω).resolve_left hn).le

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma eventually_hit_of_live_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (T : ℝ≥0) (hT : z ∈ survivingDomain γ T)
    (hR : fullRadius G T z = (2 * z.im) * Real.exp (-u)) :
    ∀ᶠ n in atTop, ω ∈ (a n).hit ∧ (a n).τ ω = T := by
  have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
  obtain ⟨δ, hδ, hδb⟩ := live_angleSq_lower_bound hU hw z T hT
  have hTc : Real.log ((2 * z.im) / fullRadius G T z) = u := by
    rw [← logRadiusClock_logCoordinates hU hw z T hT]
    exact (fullRadius_level_iff_logClock hU hw z T hT u).mp hR
  filter_upwards [(tendsto_order.mp hε).2 δ hδ] with n hn
  obtain ⟨hl, he⟩ := (a n).chart_identification hBc hz ω γ G F hw
  have hr := (a n).clock_eq_chart hBc hz ω γ G F hw ((a n).τ ω) le_rfl
  have htT : (a n).τ ω ≤ T := live_clock_le_time hU hw z _ T hl hT (by
    rw [hTc, ← hr]; exact ((a n).inside ω _ le_rfl).1)
  have ha : ε n < logAngleSq κ ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) := by
    rw [he _ le_rfl, logAngleSq_logCoordinates κ _ G z _ (hw.imag_positive _ z hl)]
    exact hn.trans_le (hδb _ htT)
  have hh : ω ∈ (a n).hit := ((a n).boundary ω).resolve_right (ne_of_gt ha)
  refine ⟨hh, ?_⟩
  exact live_radius_unique hU hw z _ T hl hT (((a n).radius_at_hit hBc hz ω γ G F hw hh).2.trans hR.symm)

lemma localizedRadiusStop_eq_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    localizedRadiusStop a ω = radiusLevelTime γ G z u := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    obtain ⟨n, hn, he⟩ := (eventually_hit_of_live_level a hε hBc hz ω γ G F hw T hT hR).exists
    rw [localizedRadiusStop_eq_hit a ω n hn, he,
      radiusLevelTime_eq_of_live_level ((hBc ω).const_mul _) hw z u T hT hR]
    rfl
  · rw [localizedRadiusStop_eq_top a ω (fun n hn => hh
      ⟨(a n).τ ω, (a n).radius_at_hit hBc hz ω γ G F hw hn⟩)]
    have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
        fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro s ⟨_, hsl, hsR⟩
      exact hh ⟨s.toNNReal, hsl, hsR⟩
    rw [radiusLevelTime, he, sInf_empty]
    rfl

lemma localization_weight_tendsto
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    Tendsto (fun n => (a n).weight ω) atTop
      (𝓝 (stoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G z u)) := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_hit_of_live_level a hε hBc hz ω γ G F hw T hT hR] with n hn
    exact ((a n).weight_eq_stoppedGreen_of_hit hBc hz ω γ G F hw hn.1).symm
  · rw [stoppedGreen_eq_zero_of_no_level κ _ _ _ z u hh]
    have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
    have ht : Tendsto (fun n => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) *
        ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
      have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hε).const_mul
        (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
    apply squeeze_zero (fun n => ((a n).weight_bound hκ hκ8 ω).1) _ ht
    intro n
    exact (a n).weight_small_of_not_hit hκ hκ8 ω
      (fun hn => hh ⟨(a n).τ ω, (a n).radius_at_hit hBc hz ω γ G F hw hn⟩)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def stoppedAngleSq (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) : ℝ :=
  if radiusLevelTime γ G z u < ∞ then
    (Real.sin (Complex.arg (G (radiusLevelTime γ G z u).toNNReal z -
      ((Real.sqrt κ * B (radiusLevelTime γ G z u).toNNReal : ℝ) : ℂ)))) ^ 2
  else 0

lemma stoppedAngleSq_nonneg (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) : 0 ≤ stoppedAngleSq κ B γ G z u := by
  unfold stoppedAngleSq
  split_ifs
  · exact sq_nonneg _
  · rfl

lemma radiusLevelTime_eq_top_of_no_level (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) (hn : ¬ ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
      fullRadius G t z = (2 * z.im) * Real.exp (-u)) : radiusLevelTime γ G z u = ∞ := by
  have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
      fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = ∅ := by
    exact Set.eq_empty_iff_forall_notMem.mpr fun s hs => hn ⟨s.toNNReal, hs.2⟩
  rw [radiusLevelTime, he, sInf_empty]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_eq_zero_of_no_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (p α : ℝ) (hn : ¬ ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧
      fullRadius G T z = (2 * z.im) * Real.exp (-u)) :
    limitRadiusKernel a p α u ω = 0 := by
  unfold limitRadiusKernel
  apply dite_eq_right
  rintro ⟨n, hn'⟩
  have hh : ω ∈ (a n).hit := le_antisymm ((a n).clock_upper ω) ((le_max_left u 0).trans hn')
  exact hn ⟨(a n).τ ω, (a n).radius_at_hit hBc hz ω γ G F hw hh⟩

lemma limitRadiusKernel_eq_stopped_of_live_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (T : ℝ≥0) (hT : z ∈ survivingDomain γ T)
    (hR : fullRadius G T z = (2 * z.im) * Real.exp (-u)) (p α : ℝ) :
    limitRadiusKernel a p α u ω = powerLogDensity κ p α (logLoewnerCoordinates G z T) (B T ω) := by
  obtain ⟨n, hn, hhit, htime⟩ := ((radiusKernel_eventually_limit a hε p α u ω).and
    (eventually_hit_of_live_level a hεlim hBc hz ω γ G F hw T hT hR)).exists
  rw [max_eq_left hu] at hn
  rw [← hn, ← (a n).stopped_power_eq_kernel_of_hit p α ω hhit]
  obtain ⟨_, he⟩ := (a n).chart_identification hBc hz ω γ G F hw
  rw [he _ le_rfl, htime]

lemma limitRadiusKernel_eq_stoppedGreen
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    limitRadiusKernel a (codimension κ) (greenExponent κ) u ω =
      stoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G z u := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    rw [limitRadiusKernel_eq_stopped_of_live_level a hε hεlim hBc hz hu ω γ G F hw T hT hR]
    rw [stoppedGreen_eq_of_live_level ((hBc ω).const_mul _) hw κ z u T hT hR]
    exact greenLogDensity_logCoordinates ((hBc ω).const_mul _) hw κ _ z T hT rfl
  · rw [limitRadiusKernel_eq_zero_of_no_level a hBc hz ω γ G F hw _ _ hh,
      stoppedGreen_eq_zero_of_no_level κ _ γ G z u hh]

lemma limitRadiusKernel_eq_stoppedAngleSq
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    limitRadiusKernel a 0 2 u ω = stoppedAngleSq κ (fun t => B t ω) γ G z u := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    rw [limitRadiusKernel_eq_stopped_of_live_level a hε hεlim hBc hz hu ω γ G F hw T hT hR]
    rw [stoppedAngleSq, radiusLevelTime_eq_of_live_level ((hBc ω).const_mul _) hw z u T hT hR]
    simp only [ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]
    rw [powerLogDensity_radius_angle κ 0 2 (Real.log z.im)]
    norm_num only [zero_mul, Real.exp_zero, one_mul, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
    exact logAngleSq_logCoordinates κ _ G z T (hw.imag_positive T z hT)
  · rw [limitRadiusKernel_eq_zero_of_no_level a hBc hz ω γ G F hw _ _ hh,
      stoppedAngleSq, radiusLevelTime_eq_top_of_no_level γ G z u hh]
    simp
end SLEExactGauge
end

 
end

end OAI
