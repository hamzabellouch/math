import Mathlib
import OAI.Probability.SLE.KernelConsistency

namespace OAI

/-! Angular Moments for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}
noncomputable def physicalGreenLimit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => (a n).physicalWeight t ω)

lemma physicalWeight_exists_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    ∃ l : ℝ, Tendsto (fun n => (a n).physicalWeight t ω) atTop (𝓝 l) := by
  by_cases ht : ∃ n, t ≤ (a n).τ ω
  · obtain ⟨n, hn⟩ := ht
    refine ⟨(a n).physicalWeight t ω, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop n] with m hnm
    have hm' := hn.trans ((a n).stopping_le (a m) le_rfl (hε hnm) ω)
    simp only [AngularLocalization.physicalWeight, ← NNReal.coe_min, min_eq_left hn, min_eq_left hm']
    rw [(a n).synchronize (a m) ω t hn hm']
  · by_cases hh : ∃ n, ω ∈ (a n).hit
    · obtain ⟨n, hn⟩ := hh
      refine ⟨(a n).physicalWeight t ω, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [eventually_ge_atTop n] with m hnm
      have heτ : (a n).τ ω = (a m).τ ω := le_antisymm
        ((a n).stopping_le (a m) le_rfl (hε hnm) ω)
        ((a m).stopping_le_of_hit (a n) le_rfl ω hn)
      have hnt : (a n).τ ω ≤ t := (lt_of_not_ge (fun h => ht ⟨n, h⟩)).le
      have hmt : (a m).τ ω ≤ t := heτ ▸ hnt
      simp only [AngularLocalization.physicalWeight, ← NNReal.coe_min, min_eq_right hnt, min_eq_right hmt]
      rw [(a n).synchronize (a m) ω ((a n).τ ω) le_rfl heτ.le, heτ]
    · refine ⟨0, ?_⟩
      have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
      let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
      have hpow : Tendsto (fun n => K * ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
        have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
        simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
      apply squeeze_zero (fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).1) _ hpow
      intro n
      have hnt : (a n).τ ω ≤ t := (lt_of_not_ge (fun h => ht ⟨n, h⟩)).le
      change greenLogDensity κ _ _ ≤ _
      rw [← NNReal.coe_min, min_eq_right hnt]
      exact (a n).weight_small_of_not_hit hκ hκ8 ω (fun hn => hh ⟨n, hn⟩)

lemma physicalWeight_tendsto_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => (a n).physicalWeight t ω) atTop (𝓝 (physicalGreenLimit a t ω)) := by
  obtain ⟨l, hl⟩ := physicalWeight_exists_limit a hε hεlim hκ hκ8 t ω
  simpa only [physicalGreenLimit, hl.limUnder_eq] using hl

lemma physicalGreenLimit_bound
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    0 ≤ physicalGreenLimit a t ω ∧ physicalGreenLimit a t ω ≤
      Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) := by
  have ht := physicalWeight_tendsto_limit a hε hεlim hκ hκ8 t ω
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).1),
    le_of_tendsto ht (Eventually.of_forall fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).2)⟩

lemma physicalGreenLimit_adapted
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) (physicalGreenLimit a) := by
  intro t
  have hs (n : ℕ) := (a n).physicalWeight_adapted hBc t
  let : MeasurableSpace Ω := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t
  exact StronglyMeasurable.limUnder hs

lemma physicalGreenLimit_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P] (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) : Integrable (physicalGreenLimit a t) P := by
  apply Integrable.of_bound ((physicalGreenLimit_adapted a hBc t).mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le t)).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (physicalGreenLimit_bound a hε hεlim hκ hκ8 t ω).1]
  exact (physicalGreenLimit_bound a hε hεlim hκ hκ8 t ω).2

 

theorem physicalGreenLimit_martingale
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    Martingale (physicalGreenLimit a) (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) P := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have had := physicalGreenLimit_adapted a hBc
  have hi := physicalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  have hmar (n : ℕ) := (a n).physicalWeight_martingale hB hBm hBc hB0 hκ hκ8
  refine ⟨had, fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (f.le s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) _ (had s).aestronglyMeasurable
  intro A hA _
  have hlim (v : ℝ≥0) : Tendsto (fun n => ∫ ω in A, (a n).physicalWeight v ω ∂P) atTop
      (𝓝 (∫ ω in A, physicalGreenLimit a v ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => ((a n).physicalWeight_integrable (P := P) hBc hκ hκ8 v).integrableOn.aestronglyMeasurable)
      (integrable_const _) _ (Eventually.of_forall (physicalWeight_tendsto_limit a hε hεlim hκ hκ8 v))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).physicalWeight_bound hκ hκ8 v ω).1]
    exact ((a n).physicalWeight_bound hκ hκ8 v ω).2
  apply tendsto_nhds_unique (hlim s)
  convert hlim t using 1
  ext n
  exact (hmar n).setIntegral_eq hst hA

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def physicalStoppedGreen (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) (t : ℝ≥0) : ℝ :=
  if radiusLevelTime γ G z u ≤ (t : ℝ≥0∞) then stoppedGreen κ U γ G z u
    else greenDensity κ U γ G t z

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma physicalWeight_tendsto_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) γ G F) (t : ℝ≥0) :
    Tendsto (fun n => (a n).physicalWeight t ω) atTop
      (𝓝 (physicalStoppedGreen κ (fun s => Real.sqrt κ * B s ω) γ G z u t)) := by
  have hU := (hBc ω).const_mul (Real.sqrt κ)
  have hρ := localizedRadiusStop_eq_source a hεlim hBc hz ω γ G F hw
  by_cases hrt : radiusLevelTime γ G z u ≤ (t : ℝ≥0∞)
  · rw [physicalStoppedGreen, ite_eq_left hrt]
    have hρt : localizedRadiusStop a ω ≤ (t : WithTop ℝ≥0) := by
      rw [hρ]
      exact hrt
    obtain ⟨n, hn, hnt⟩ := (localizedRadiusStop_le_iff a ω t).mp hρt
    obtain ⟨hl, hR⟩ := (a n).radius_at_hit hBc hz ω γ G F hw hn
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_hit_of_live_level a hεlim hBc hz ω γ G F hw ((a n).τ ω) hl hR]
      with m hm'
    have ht' : (a m).τ ω ≤ t := hm'.2.le.trans hnt
    simpa only [AngularLocalization.physicalWeight, ← NNReal.coe_min, min_eq_right ht', AngularLocalization.weight]
      using ((a m).weight_eq_stoppedGreen_of_hit hBc hz ω γ G F hw hm'.1).symm
  · rw [physicalStoppedGreen, ite_eq_right hrt]
    have hno (n : ℕ) (hnt : (a n).τ ω ≤ t) : ω ∉ (a n).hit := by
      intro hn
      apply hrt
      have hcan := (localizedRadiusStop_le_iff a ω t).mpr ⟨n, hn, hnt⟩
      rw [hρ] at hcan
      exact hcan
    by_cases hl : z ∈ survivingDomain γ t
    · obtain ⟨δ, hδ, hδb⟩ := live_angleSq_lower_bound hU hw z t hl
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_order.mp hεlim).2 δ hδ] with n hn
      have hbefore : t ≤ (a n).τ ω := by
        by_contra hnt
        have hnt' := lt_of_not_ge hnt
        have hexit := ((a n).boundary ω).resolve_left (hno n hnt'.le)
        obtain ⟨hla, heq⟩ := (a n).chart_identification hBc hz ω γ G F hw
        have ha : logAngleSq κ ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) =
          (Real.sin (Complex.arg (G ((a n).τ ω) z - ((Real.sqrt κ * B ((a n).τ ω) ω : ℝ) : ℂ)))) ^ 2 := by
          rw [heq _ le_rfl]
          exact logAngleSq_logCoordinates κ _ G z _ (hw.imag_positive _ z hla)
        have hb := hδb ((a n).τ ω) hnt'.le
        rw [← ha, hexit] at hb
        exact (not_lt_of_ge hb) hn
      dsimp only [AngularLocalization.physicalWeight]
      rw [← NNReal.coe_min, min_eq_left hbefore, ((a n).chart_identification hBc hz ω γ G F hw).2 t hbefore]
      exact (greenLogDensity_logCoordinates hU hw κ _ z t hl rfl).symm
    · have hnt (n : ℕ) : (a n).τ ω < t := by
        apply lt_of_not_ge
        intro hn
        exact hl (survivingDomain_antitone γ hn ((a n).chart_identification hBc hz ω γ G F hw).1)
      rw [greenDensity, ite_eq_right hl]
      have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
      let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
      have hpow : Tendsto (fun n => K * ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
        have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
        simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
      apply squeeze_zero (fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).1) _ hpow
      intro n
      change greenLogDensity κ _ _ ≤ _
      rw [← NNReal.coe_min, min_eq_right (hnt n).le]
      exact (a n).weight_small_of_not_hit hκ hκ8 ω (hno n (hnt n).le)

lemma physicalGreenLimit_eq_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) γ G F) (t : ℝ≥0) :
    physicalGreenLimit a t ω = physicalStoppedGreen κ (fun s => Real.sqrt κ * B s ω) γ G z u t :=
  (physicalWeight_tendsto_source a hεlim hBc hκ hκ8 hz ω γ G F hw t).limUnder_eq

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

noncomputable def terminalGreenLimit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => (a n).weight ω)

lemma localization_weight_tendsto_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) :
    Tendsto (fun n => (a n).weight ω) atTop (𝓝 (terminalGreenLimit a ω)) := by
  suffices ∃ l : ℝ, Tendsto (fun n => (a n).weight ω) atTop (𝓝 l) by
    obtain ⟨l, hl⟩ := this
    simpa only [terminalGreenLimit, hl.limUnder_eq] using hl
  by_cases hh : ∃ n, ω ∈ (a n).hit
  · obtain ⟨n, hn⟩ := hh
    refine ⟨(a n).weight ω, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop n] with m hnm
    have ht : (a n).τ ω = (a m).τ ω := le_antisymm
      ((a n).stopping_le (a m) le_rfl (hε hnm) ω)
      ((a m).stopping_le_of_hit (a n) le_rfl ω hn)
    have he := (a n).synchronize (a m) ω ((a n).τ ω) le_rfl ht.le
    simp only [AngularLocalization.weight]
    rw [he, ht]
  · refine ⟨0, ?_⟩
    have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
    let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
    have ht : Tendsto (fun n => K * ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
      have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
      simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
    apply squeeze_zero (fun n => ((a n).weight_bound hκ hκ8 ω).1) _ ht
    intro n
    exact (a n).weight_small_of_not_hit hκ hκ8 ω (fun hn => hh ⟨n, hn⟩)

lemma terminalGreenLimit_bound
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) :
    0 ≤ terminalGreenLimit a ω ∧ terminalGreenLimit a ω ≤
      Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) := by
  have ht := localization_weight_tendsto_limit a hε hεlim hκ hκ8 ω
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n => ((a n).weight_bound hκ hκ8 ω).1),
    le_of_tendsto ht (Eventually.of_forall fun n => ((a n).weight_bound hκ hκ8 ω).2)⟩

lemma terminalGreenLimit_stronglyMeasurable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) : StronglyMeasurable (terminalGreenLimit a) := by
  have hs (n : ℕ) := ((a n).physicalWeight_adapted hBc (a n).T).mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le (a n).T)
  have hs' (n : ℕ) : StronglyMeasurable ((a n).weight) := by
    convert hs n using 1
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right ((a n).bounded ω)]
  exact StronglyMeasurable.limUnder hs'

lemma terminalGreenLimit_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P] (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) : Integrable (terminalGreenLimit a) P := by
  apply Integrable.of_bound (terminalGreenLimit_stronglyMeasurable a hBc).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (terminalGreenLimit_bound a hε hεlim hκ hκ8 ω).1]
  exact (terminalGreenLimit_bound a hε hεlim hκ hκ8 ω).2

 

theorem physicalGreenLimit_condExp_terminal
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ωω, Continuous (fun t => B t ωω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) :
    physicalGreenLimit a t =ᵐ[P]
      P[terminalGreenLimit a | (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t] := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hi := terminalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  apply ae_eq_condExp_of_forall_setIntegral_eq (f.le t) hi
    (fun _ _ _ => (physicalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8 t).integrableOn)
    _ (physicalGreenLimit_adapted a hBc t).aestronglyMeasurable
  intro A hA _
  have hlim₁ : Tendsto (fun n => ∫ ω in A, (a n).physicalWeight t ω ∂P) atTop
      (𝓝 (∫ ω in A, physicalGreenLimit a t ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => ((a n).physicalWeight_integrable (P := P) hBc hκ hκ8 t).integrableOn.aestronglyMeasurable)
      (integrable_const _) _ (Eventually.of_forall (physicalWeight_tendsto_limit a hε hεlim hκ hκ8 t))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).physicalWeight_bound hκ hκ8 t ω).1]
    exact ((a n).physicalWeight_bound hκ hκ8 t ω).2
  have hw (n : ℕ) : (a n).physicalWeight (max t (a n).T) = (a n).weight := by
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right (((a n).bounded ω).trans (le_max_right _ _))]
  have hwi (n : ℕ) : Integrable ((a n).weight) P := by
    rw [← hw n]
    exact (a n).physicalWeight_integrable (P := P) hBc hκ hκ8 _
  have hlim₂ : Tendsto (fun n => ∫ ω in A, (a n).weight ω ∂P) atTop
      (𝓝 (∫ ω in A, terminalGreenLimit a ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => (hwi n).integrableOn.aestronglyMeasurable) (integrable_const _) _
      (Eventually.of_forall (localization_weight_tendsto_limit a hε hεlim hκ hκ8))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).weight_bound hκ hκ8 ω).1]
    exact ((a n).weight_bound hκ hκ8 ω).2
  apply tendsto_nhds_unique hlim₁
  convert hlim₂ using 1
  ext n
  rw [← hw n]
  exact ((a n).physicalWeight_martingale hB hBm hBc hB0 hκ hκ8).setIntegral_eq (le_max_left _ _) hA

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

def naturalNatFiltration (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) : Filtration ℕ mΩ where
  seq n := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) n
  mono' := fun n m h => (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono (by exact_mod_cast h)
  le' n := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le n

lemma terminalGreenLimit_measurable_at_infinity
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    StronglyMeasurable[⨆ n, naturalNatFiltration B hm n] (terminalGreenLimit a) := by
  have hs (n : ℕ) : StronglyMeasurable[⨆ n, naturalNatFiltration B hm n] ((a n).weight) := by
    obtain ⟨m, hm'⟩ := exists_nat_ge (a n).T
    have hme := ((a n).physicalWeight_adapted hBc (a n).T).mono
      (((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hm').trans
        (show naturalNatFiltration B hm m ≤ ⨆ n, naturalNatFiltration B hm n from le_iSup _ m))
    convert hme using 1
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right ((a n).bounded ω)]
  let : MeasurableSpace Ω := ⨆ n, naturalNatFiltration B hm n
  exact StronglyMeasurable.limUnder hs

theorem physicalGreenLimit_tendsto_at_infinity
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => physicalGreenLimit a n ω) atTop (𝓝 (terminalGreenLimit a ω)) := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  have hi := terminalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  have ht := hi.tendsto_ae_condExp (ℱ := naturalNatFiltration B hm)
    (terminalGreenLimit_measurable_at_infinity a hBc)
  have he : ∀ᵐ ω ∂P, ∀ n : ℕ, physicalGreenLimit a n ω =
      P[terminalGreenLimit a | naturalNatFiltration B hm n] ω := by
    rw [ae_all_iff]
    intro n
    exact physicalGreenLimit_condExp_terminal a hε hεlim hB hBm hBc hB0 hκ hκ8 n
  filter_upwards [ht, he] with ω hω heω
  simpa only [heω] using hω

lemma terminalGreenLimit_eq_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) γ G F) :
    terminalGreenLimit a ω = stoppedGreen κ (fun s => Real.sqrt κ * B s ω) γ G z u :=
  (localization_weight_tendsto a hεlim hBc hκ hκ8 hz ω γ G F hw).limUnder_eq

 

theorem killedGreen_tendsto_zero_of_no_radius
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω)) :
    ∀ᵐ ω ∂P, radiusLevelTime (γ ω) (G ω) z u = ∞ →
      Tendsto (fun n : ℕ => greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) n z)
        atTop (𝓝 0) := by
  filter_upwards [hw, physicalGreenLimit_tendsto_at_infinity a hε hεlim hB hBm hBc hB0 hκ hκ8]
    with ω hω ht
  intro hn
  have ht' : terminalGreenLimit a ω = 0 := by
    rw [terminalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω]
    simp only [stoppedGreen, hn, lt_irrefl, ite_false]
  rw [ht'] at ht
  convert ht using 1
  ext n
  rw [physicalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω n,
    physicalStoppedGreen, hn, ite_eq_right (by exact not_le.mpr (ENNReal.coe_lt_top (r := (n : ℝ≥0))))]

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem exists_physical_green_martingale_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
    ∃ (M : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Martingale M (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) P ∧
      Integrable Z P ∧
      (∀ t ω, 0 ≤ M t ω ∧ M t ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
      (∀ ω, 0 ≤ Z ω ∧ Z ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
      (∀ t, M t =ᵐ[P] P[Z | (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t]) ∧
      (∀ᵐ ω ∂P, (∀ t, M t ω = physicalStoppedGreen κ (fun s => Real.sqrt κ * B s ω)
          (γ ω) (G ω) z u t) ∧
        Z ω = stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u) ∧
      (∀ᵐ ω ∂P, radiusLevelTime (γ ω) (G ω) z u = ∞ →
        Tendsto (fun n : ℕ => greenDensity κ (fun s => Real.sqrt κ * B s ω)
          (γ ω) (G ω) n z) atTop (𝓝 0)) := by
  dsimp only
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A₀ := div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (n : ℕ) : AngularLocalization B hm κ z u (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z u (ε n)
      hu (hε0 n) (hεA n))
  refine ⟨physicalGreenLimit a, terminalGreenLimit a,
    physicalGreenLimit_martingale a hεanti hεlim hB hBm hBc hB0 hκ hκ8,
    terminalGreenLimit_integrable a hεanti hεlim hBc hκ hκ8,
    physicalGreenLimit_bound a hεanti hεlim hκ hκ8,
    terminalGreenLimit_bound a hεanti hεlim hκ hκ8,
    physicalGreenLimit_condExp_terminal a hεanti hεlim hB hBm hBc hB0 hκ hκ8, ?_,
    killedGreen_tendsto_zero_of_no_radius a hεanti hεlim hB hBm hBc hB0 hκ hκ8 hz γ G F hw⟩
  filter_upwards [hw] with ω hω
  exact ⟨fun t => physicalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω t,
    terminalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω⟩

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

lemma physicalWeight_continuous (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t => a.physicalWeight t ω) := by
  have hc : Continuous (fun t : ℝ≥0 => min t (a.τ ω)) := continuous_id.min continuous_const
  exact (greenLogDensity_contDiff κ).continuous.comp
    ((((a.solution.lipschitz ω).continuous.comp NNReal.continuous_coe).comp hc).prodMk
      ((hBc ω).comp hc))

lemma physicalWeight_stopping_measurable (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Measurable[hσ.measurableSpace] (fun ω => a.physicalWeight (σ ω) ω) := by
  have hp := (a.physicalWeight_adapted hBc).isStronglyProgressive_of_continuous
    (a.physicalWeight_continuous hBc)
  exact measurable_stoppedValue hp hσ

lemma physicalWeight_stopping_integrable (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => a.physicalWeight (σ ω) ω) P := by
  apply Integrable.of_bound
    ((a.physicalWeight_stopping_measurable hBc σ hσ).mono hσ.measurableSpace_le le_rfl).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (a.physicalWeight_bound hκ hκ8 (σ ω) ω).1]
  exact (a.physicalWeight_bound hκ hκ8 (σ ω) ω).2

 

lemma integral_physicalWeight_stopping (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    (∫ ω, a.physicalWeight (σ ω) ω ∂P) = greenLogDensity κ (initialLogCoordinates z) 0 := by
  let ρ (ω : Ω) : ℝ≥0 := min (σ ω) (a.τ ω)
  have hρ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (ρ ω : WithTop ℝ≥0)) := by
    simpa only [ρ, WithTop.coe_min] using hσ.min a.stopping
  have hin (ω : Ω) (v : ℝ≥0) (hv : v ≤ ρ ω) :
      logRadiusClock (Real.log z.im) (a.solution.Q v ω) ≤ u ∧
        a.lo ≤ (a.solution.Q v ω).1.im ∧ (a.solution.Q v ω).1.im ≤ a.hi := by
    have hh := a.inside ω v (hv.trans (min_le_right _ _))
    exact ⟨hh.1, hh.2.2⟩
  have hh := (a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u ρ hρ a.T (fun ω => (min_le_right _ _).trans (a.bounded ω)) hin).2
  simpa only [ρ, physicalWeight, NNReal.coe_min] using hh

lemma physicalWeight_setIntegral_stopping (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    (∫ ω in A, a.physicalWeight (σ ω) ω ∂P) =
      ∫ ω in A, a.physicalWeight (τ ω) ω ∂P := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let ρ (ω : Ω) : ℝ≥0 := if ω ∈ A then τ ω else σ ω
  have hρ : IsStoppingTime f (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    stopping_paste_after f hσ hτ hστ hA
  have hiσ := a.physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 σ hσ
  have hiρ := a.physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 ρ hρ
  have hiτ := a.physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 τ hτ
  have he (ω : Ω) : a.physicalWeight (ρ ω) ω - a.physicalWeight (σ ω) ω =
      A.indicator (fun ω => a.physicalWeight (τ ω) ω - a.physicalWeight (σ ω) ω) ω := by
    by_cases hω : ω ∈ A <;> simp [ρ, hω]
  have heI : (∫ ω, A.indicator (fun ω => a.physicalWeight (τ ω) ω -
      a.physicalWeight (σ ω) ω) ω ∂P) = 0 := by
    simp_rw [← he]
    rw [integral_sub hiρ hiσ,
      a.integral_physicalWeight_stopping hB hBm hBc hB0 hκ hκ8 ρ hρ,
      a.integral_physicalWeight_stopping hB hBm hBc hB0 hκ hκ8 σ hσ, sub_self]
  rw [integral_indicator (hσ.measurableSpace_le _ hA),
    integral_sub hiτ.integrableOn hiσ.integrableOn] at heI
  exact (sub_eq_zero.mp heI).symm

end AngularLocalization
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma physicalGreenLimit_stopping_measurable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    StronglyMeasurable[hσ.measurableSpace] (fun ω => physicalGreenLimit a (σ ω) ω) := by
  have hs (n : ℕ) : StronglyMeasurable[hσ.measurableSpace]
      (fun ω => (a n).physicalWeight (σ ω) ω) :=
    ((a n).physicalWeight_stopping_measurable hBc σ hσ).stronglyMeasurable
  let : MeasurableSpace Ω := hσ.measurableSpace
  exact StronglyMeasurable.limUnder hs

lemma physicalGreenLimit_stopping_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => physicalGreenLimit a (σ ω) ω) P := by
  apply Integrable.of_bound
    ((physicalGreenLimit_stopping_measurable a hBc σ hσ).mono hσ.measurableSpace_le).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (physicalGreenLimit_bound a hε hεlim hκ hκ8 (σ ω) ω).1]
  exact (physicalGreenLimit_bound a hε hεlim hκ hκ8 (σ ω) ω).2

 

end SLEExactGauge
end
end
end

end OAI
