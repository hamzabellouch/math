import Mathlib
import OAI.Probability.SLE.AngularMoments

namespace OAI

/-! Inverse Moments for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}
theorem physicalGreenLimit_stopping_condExp_terminal
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    (fun ω => physicalGreenLimit a (σ ω) ω) =ᵐ[P]
      P[terminalGreenLimit a | hσ.measurableSpace] := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hi := terminalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  apply ae_eq_condExp_of_forall_setIntegral_eq hσ.measurableSpace_le hi
    (fun _ _ _ => (physicalGreenLimit_stopping_integrable a hε hεlim (P := P) hBc hκ hκ8 σ hσ).integrableOn)
    _ (physicalGreenLimit_stopping_measurable a hBc σ hσ).aestronglyMeasurable
  intro A hA _
  have hlim₁ : Tendsto (fun n => ∫ ω in A, (a n).physicalWeight (σ ω) ω ∂P) atTop
      (𝓝 (∫ ω in A, physicalGreenLimit a (σ ω) ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => ((a n).physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 σ hσ).integrableOn.aestronglyMeasurable)
      (integrable_const _) _
      (Eventually.of_forall fun ω => physicalWeight_tendsto_limit a hε hεlim hκ hκ8 (σ ω) ω)
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).physicalWeight_bound hκ hκ8 (σ ω) ω).1]
    exact ((a n).physicalWeight_bound hκ hκ8 (σ ω) ω).2
  have hwi (n : ℕ) : Integrable ((a n).weight) P := by
    have hh := (a n).physicalWeight_integrable (P := P) hBc hκ hκ8 (a n).T
    convert hh using 1
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right ((a n).bounded ω)]
  have hlim₂ : Tendsto (fun n => ∫ ω in A, (a n).weight ω ∂P) atTop
      (𝓝 (∫ ω in A, terminalGreenLimit a ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => (hwi n).integrableOn.aestronglyMeasurable)
      (integrable_const _) _
      (Eventually.of_forall (localization_weight_tendsto_limit a hε hεlim hκ hκ8))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).weight_bound hκ hκ8 ω).1]
    exact ((a n).weight_bound hκ hκ8 ω).2
  have he (n : ℕ) : (∫ ω in A, (a n).physicalWeight (σ ω) ω ∂P) =
      ∫ ω in A, (a n).weight ω ∂P := by
    let τ (ω : Ω) : ℝ≥0 := max (σ ω) (a n).T
    have hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)) := by
      simpa only [τ, WithTop.coe_max] using hσ.max
        (isStoppingTime_const (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) (a n).T)
    have hx := (a n).physicalWeight_setIntegral_stopping hB hBm hBc hB0 hκ hκ8 σ τ hσ hτ
      (fun ω => le_max_left _ _) hA
    convert hx using 1
    congr 1
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min, τ,
      min_eq_right (((a n).bounded ω).trans (le_max_right _ _))]
  apply tendsto_nhds_unique hlim₁
  simpa only [he] using hlim₂

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem exists_physical_green_stopping_regular
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
      (∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime
          (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
          (fun ω => (σ ω : WithTop ℝ≥0))),
        (fun ω => M (σ ω) ω) =ᵐ[P] P[Z | hσ.measurableSpace]) ∧
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
    physicalGreenLimit_condExp_terminal a hεanti hεlim hB hBm hBc hB0 hκ hκ8,
    (fun σ hσ => physicalGreenLimit_stopping_condExp_terminal a hεanti hεlim hB hBm hBc hB0 hκ hκ8 σ hσ), ?_,
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

 

theorem exists_physical_green_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    ∃ C : ℝ≥0 → Ω → ℝ,
    ∃ hCm : Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2),
      IsBrownianReal C P ∧ (∀ ω, Continuous (fun t => C t ω)) ∧ (∀ ω, C 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) ∧
      let hm (t : ℝ≥0) : Measurable (C t) := hCm.comp (measurable_const.prodMk measurable_id)
      ∃ (M : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
        Martingale M (Filtration.natural C (fun t => (hm t).stronglyMeasurable)) P ∧
        Integrable Z P ∧
        (∀ t ω, 0 ≤ M t ω ∧ M t ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
        (∀ ω, 0 ≤ Z ω ∧ Z ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
        (∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime
            (Filtration.natural C (fun t => (hm t).stronglyMeasurable))
            (fun ω => (σ ω : WithTop ℝ≥0))),
          (fun ω => M (σ ω) ω) =ᵐ[P] P[Z | hσ.measurableSpace]) ∧
        (∀ᵐ ω ∂P, (∀ t, M t ω = physicalStoppedGreen κ (fun s => Real.sqrt κ * B s ω)
            (γ ω) (G ω) z u t) ∧
          Z ω = stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u) ∧
        (∀ᵐ ω ∂P, radiusLevelTime (γ ω) (G ω) z u = ∞ →
          Tendsto (fun n : ℕ => greenDensity κ (fun s => Real.sqrt κ * B s ω)
            (γ ω) (G ω) n z) atTop (𝓝 0)) := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω hω'
    simpa only [hω'] using hω
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz u hu
  refine ⟨C, hCm, hC, hCc, hC0, hCB, M, Z, hM, hZ, hMb, hZb, hStop, ?_, ?_⟩
  · filter_upwards [heq, hCB] with ω hω hω'
    simpa only [hω'] using hω
  · filter_upwards [hNoHit, hCB] with ω hω hω'
    simpa only [hω'] using hω

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def spatialHitTime (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) : WithTop ℝ≥0 :=
  hittingAfter (fun t (_ : Unit) => dist (γ t) z - r) {0} 0 ()

lemma spatialHitTime_le_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    spatialHitTime γ z r ≤ (T : WithTop ℝ≥0) ↔
      ∃ t ∈ Icc 0 T, dist (γ t) z = r := by
  simpa only [spatialHitTime, sub_eq_zero] using
    hittingAfter_zero_le_iff (fun t (_ : Unit) => dist (γ t) z - r)
      (fun _ => (hc.dist continuous_const).sub continuous_const) 0 T ()

lemma spatialHitTime_lt_of_dist_lt {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hstart : r ≤ dist (γ 0) z)
    (t : ℝ≥0) (ht : dist (γ t) z < r) : spatialHitTime γ z r < t := by
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t from bot_le)
    (hc.dist continuous_const).continuousOn ⟨ht.le, hstart⟩
  have hst : s < t := lt_of_le_of_ne hs.2 (by intro h; subst s; exact ht.ne he)
  exact ((spatialHitTime_le_iff hc z r s).mpr ⟨s, ⟨bot_le, le_rfl⟩, he⟩).trans_lt
    (WithTop.coe_lt_coe.mpr hst)

lemma IsCapacityTwoWitness.radius_hit_forces_spatial_before
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r) (t : ℝ≥0)
    (hτ : radiusLevelTime γ G z u ≤ (t : ℝ≥0∞)) : spatialHitTime γ z r < t := by
  have hex : ∃ a : ℝ≥0, z ∈ survivingDomain γ a ∧
      fullRadius G a z = (2 * z.im) * Real.exp (-u) := by
    by_contra hn
    rw [radiusLevelTime_eq_top_of_no_level γ G z u hn] at hτ
    exact ENNReal.not_top_le_coe hτ
  obtain ⟨a, ha, hR⟩ := hex
  have hat : a ≤ t := by
    rw [radiusLevelTime_eq_of_live_level hU h z u a ha hR] at hτ
    exact ENNReal.coe_le_coe.mp hτ
  obtain ⟨s, hs, hd⟩ := h.trace_approach_of_radius_lt hU a z ha r hr hy (hR ▸ hlevel)
  have hstart : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  exact (spatialHitTime_lt_of_dist_lt h.1 z r hstart s hd).trans_le
    (WithTop.coe_le_coe.mpr (hs.2.trans hat))

lemma IsCapacityTwoWitness.physicalGreen_eq_before_spatial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    physicalStoppedGreen κ U γ G z u t = greenDensity κ U γ G t z := by
  apply ite_eq_right
  intro hτ
  exact (not_lt_of_ge ht) (h.radius_hit_forces_spatial_before hU z r hr hy u hlevel t hτ)

lemma IsCapacityTwoWitness.radius_no_hit_of_spatial_no_hit
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r)
    (ht : spatialHitTime γ z r = ⊤) : radiusLevelTime γ G z u = ∞ := by
  apply radiusLevelTime_eq_top_of_no_level
  rintro ⟨t, hl, hR⟩
  have hh := h.radius_hit_forces_spatial_before hU z r hr hy u hlevel t
    (le_of_eq (radiusLevelTime_eq_of_live_level hU h z u t hl hR))
  rw [ht] at hh
  exact not_top_lt hh

noncomputable def spatialGreenWeight (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (r : ℝ) : ℝ :=
  if spatialHitTime γ z r = ⊤ then 0 else
    greenDensity κ U γ G ((spatialHitTime γ z r).untopD 0) z

noncomputable def boundedSpatialHit (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ)
    (T : ℝ≥0) : ℝ≥0 := (min (spatialHitTime γ z r) T).untopD 0

lemma boundedSpatialHit_coe (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    (boundedSpatialHit γ z r T : WithTop ℝ≥0) = min (spatialHitTime γ z r) T := by
  have hn : min (spatialHitTime γ z r) (T : WithTop ℝ≥0) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
  change (((min (spatialHitTime γ z r) (T : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = _
  rw [← hv, WithTop.untopD_coe]

lemma boundedSpatialHit_le (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    (boundedSpatialHit γ z r T : WithTop ℝ≥0) ≤ spatialHitTime γ z r := by
  rw [boundedSpatialHit_coe]
  exact min_le_left _ _

 

lemma IsCapacityTwoWitness.spatialGreen_limit
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r)
    (hno : radiusLevelTime γ G z u = ∞ →
      Tendsto (fun n : ℕ => greenDensity κ U γ G n z) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => physicalStoppedGreen κ U γ G z u
      (boundedSpatialHit γ z r n)) atTop (𝓝 (spatialGreenWeight κ U γ G z r)) := by
  by_cases ht : spatialHitTime γ z r = ⊤
  · have hn := hno (h.radius_no_hit_of_spatial_no_hit hU z r hr hy u hlevel ht)
    have he (n : ℕ) : boundedSpatialHit γ z r n = n := by
      simp only [boundedSpatialHit, ht, min_eq_right (le_top), WithTop.untopD_coe]
    simpa only [he, h.physicalGreen_eq_before_spatial hU κ z r hr hy u hlevel _
      (by rw [ht]; exact le_top), spatialGreenWeight, ite_eq_left ht] using hn
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ht
    have he : (spatialHitTime γ z r).untopD 0 = v := by rw [← hv, WithTop.untopD_coe]
    rw [spatialGreenWeight, ite_eq_right ht, he]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Nat.ceil (v : ℝ))] with n hn
    have hvn : v ≤ (n : ℝ≥0) := by
      change (v : ℝ) ≤ (n : ℝ)
      exact (Nat.le_ceil (v : ℝ)).trans (Nat.cast_le.mpr hn)
    have hbn : boundedSpatialHit γ z r n = v := by
      simp only [boundedSpatialHit, ← hv, min_eq_left (WithTop.coe_le_coe.mpr hvn), WithTop.untopD_coe]
    rw [hbn]
    exact (h.physicalGreen_eq_before_spatial hU κ z r hr hy u hlevel v hv.le).symm

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.live_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    z ∈ survivingDomain γ 0 := by
  have hl := h.2.2.2.2.2.2.1 0 hz
  have he := h.2.2.2.2.2.2.2.2.1 0 z hz
  rw [h.initial_value _ hl.1.1] at he
  exact he ▸ hl

lemma IsCapacityTwoWitness.green_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (hU0 : U 0 = 0)
    (κ : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    greenDensity κ U γ G 0 z = initialGreen κ z := by
  have he := greenLogDensity_logCoordinates hU h κ 0 z 0 (h.live_initial hz)
    (by rw [hU0, mul_zero])
  simp only [NNReal.coe_zero] at he
  rw [logLoewnerCoordinates_initial hU h z (h.live_initial hz)] at he
  rw [← he]
  exact greenLogDensity_initial κ z hz

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma boundedSpatialHit_stopping (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    IsStoppingTime a.filtration
      (fun ω : a.samples => (boundedSpatialHit (γ ω) z r T : WithTop ℝ≥0)) := by
  exact a.boundedDiskHit_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r T

 

theorem spatialGreen_expectation_of_level [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (hz : z ∈ upperHalfPlane) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hu : 0 ≤ u) (hlevel : (2 * z.im) * Real.exp (-u) < r) :
    Integrable (fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) (P.comap Subtype.val) ∧
    (∫ ω : a.samples, spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z r ∂(P.comap Subtype.val)) = initialGreen κ z := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness) z hz u hu
  let σ (n : ℕ) (ω : a.samples) : ℝ≥0 := boundedSpatialHit (γ ω) z r n
  have hσ (n : ℕ) : IsStoppingTime a.filtration (fun ω => (σ n ω : WithTop ℝ≥0)) :=
    a.boundedSpatialHit_stopping z r n
  dsimp only [filtration] at hσ
  let W (ω : a.samples) := spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
    (γ ω) (a.G ω) z r
  let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
  have hMi (n : ℕ) : Integrable (fun ω => M (σ n ω) ω) μ :=
    integrable_condExp.congr (hStop (σ n) (hσ n)).symm
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (σ n ω) ω) atTop (𝓝 (W ω)) := by
    filter_upwards [heq, hNoHit] with ω he hn
    simpa only [he.1, σ, W, Function.comp_apply] using
      (a.witness ω).spatialGreen_limit ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel hn
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖M (σ n ω) ω‖ ≤ K := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hMb _ ω).1]
    exact (hMb _ ω).2
  have hWi : Integrable W μ := by
    apply Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hMi n).aestronglyMeasurable) hlim) K
    filter_upwards [hlim] with ω hω
    exact le_of_tendsto hω.norm (Eventually.of_forall fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hMb _ ω).1]
      exact (hMb _ ω).2)
  have hI : Tendsto (fun n : ℕ => ∫ ω, M (σ n ω) ω ∂μ) atTop (𝓝 (∫ ω, W ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hMi n).aestronglyMeasurable) (integrable_const _) hbound hlim
  have hInt (n : ℕ) : (∫ ω, M (σ n ω) ω ∂μ) = ∫ ω, Z ω ∂μ := by
    rw [integral_congr_ae (hStop (σ n) (hσ n))]
    have : IsFiniteMeasure (μ.trim (hσ n).measurableSpace_le) :=
      isFiniteMeasure_trim (hσ n).measurableSpace_le
    exact integral_condExp (μ := μ) (f := Z) (hσ n).measurableSpace_le
  have h0 : M 0 =ᵐ[μ] fun _ => initialGreen κ z := by
    filter_upwards [heq] with ω he
    rw [he.1 0]
    dsimp only [Function.comp_apply]
    rw [(a.witness ω).physicalGreen_eq_before_spatial
      ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel 0 bot_le]
    exact (a.witness ω).green_initial ((a.continuous_B ω).const_mul _)
      (by rw [a.zero_B ω, mul_zero]) κ hz
  have hZInt : (∫ ω, Z ω ∂μ) = initialGreen κ z := by
    calc
      _ = ∫ ω, M 0 ω ∂μ := by
        rw [integral_congr_ae (hClosed 0)]
        exact (integral_condExp (μ := μ) (f := Z) (a.filtration.le 0)).symm
      _ = _ := by rw [integral_congr_ae h0, integral_const]; simp
  refine ⟨hWi, ?_⟩
  have he : (∫ ω, W ω ∂μ) = ∫ ω, Z ω ∂μ :=
    tendsto_nhds_unique hI (by simpa only [hInt] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω, Z ω ∂μ) atTop (𝓝 (∫ ω, Z ω ∂μ))))
  exact he.trans hZInt

 

theorem spatialGreen_expectation [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im) :
    Integrable (fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) (P.comap Subtype.val) ∧
    (∫ ω : a.samples, spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z r ∂(P.comap Subtype.val)) = initialGreen κ z := by
  have hz : z ∈ upperHalfPlane := hr.trans_le hy
  let u := Real.log (4 * z.im / r)
  have hratio : 0 < 4 * z.im / r := div_pos (mul_pos (by norm_num) hz) hr
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hr).mpr (by linarith))
  have hlev : (2 * z.im) * Real.exp (-u) = r / 2 := by
    dsimp only [u]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp [(show 0 < z.im from hz).ne']
    ring
  exact a.spatialGreen_expectation_of_level hκ hκ8 z hz r hr hy u hu
    (by rw [hlev]; linarith)

end RegularSLEPresentation
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

structure SpatialClippedFamily {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ) where
  Q : ℕ → ℝ → ℂ × Ω → ℂ × ℝ
  measurable : ∀ n, Measurable (fun p : ℝ × (ℂ × Ω) => Q n p.1 p.2)
  initial : ∀ n z ω, Q n 0 (z, ω) = initialLogCoordinates z
  derivative : ∀ n z ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q n s (z, ω))
    (clippedLogLoewnerField (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (U t.toNNReal ω) (Q n t (z, ω))) (Ici 0) t

noncomputable def spatialClippedFamily
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω)) : SpatialClippedFamily U where
  Q n := (exists_spatial_clipped_flow U hUm hUc n).choose
  measurable n := (exists_spatial_clipped_flow U hUm hUc n).choose_spec.1
  initial n := (exists_spatial_clipped_flow U hUm hUc n).choose_spec.2.1
  derivative n := (exists_spatial_clipped_flow U hUm hUc n).choose_spec.2.2

namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

def valid (n : ℕ) (t : ℝ≥0) (z : ℂ) (ω : Ω) : Prop :=
  0 < z.im ∧ Real.log z.im ≤ (n : ℝ) ∧ -(n : ℝ) ≤ (c.Q n t (z, ω)).1.im

lemma valid_measurable (n : ℕ) :
    MeasurableSet {p : ℝ≥0 × (ℂ × Ω) | c.valid n p.1 p.2.1 p.2.2} := by
  have hz : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => p.2.1.im) :=
    Complex.measurable_im.comp (measurable_fst.comp measurable_snd)
  have hQ : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => (c.Q n p.1 p.2).1.im) :=
    Complex.measurable_im.comp ((c.measurable n).comp
      ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)).fst
  exact (measurableSet_lt measurable_const hz).inter
    ((measurableSet_le (Real.measurable_log.comp hz) measurable_const).inter
      (measurableSet_le measurable_const hQ))

lemma derivative_compact (n : ℕ) (z : ℂ) (ω : Ω) (T : ℝ≥0) (t : ℝ)
    (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt (fun s => c.Q n s (z, ω))
      (clippedLogLoewnerField (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
        (U t.toNNReal ω) (c.Q n t (z, ω))) (Icc 0 (T : ℝ)) t :=
  (c.derivative n z ω t ht.1).mono Icc_subset_Ici_self

lemma live_of_valid {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (n : ℕ) (t : ℝ≥0) (z : ℂ) (hv : c.valid n t z ω) :
    z ∈ survivingDomain γ t := by
  exact (clipped_log_identification_of_endpoint hUc h t z hv.1 _ _ _
    (fun s => c.Q n s (z, ω)) (c.initial n z ω)
    (c.derivative_compact n z ω t) hv.2.2 hv.2.1).1

lemma agrees_of_live {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (n : ℕ) (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (hlo : -(n : ℝ) ≤ Real.log (G t z).im) (hhi : Real.log z.im ≤ (n : ℝ)) :
    c.Q n t (z, ω) = logLoewnerCoordinates G z t := by
  exact clipped_log_loewner_agrees hUc h t z hz _ _ _ hlo hhi
    (fun s => c.Q n s (z, ω)) (c.initial n z ω)
    (c.derivative_compact n z ω t) ⟨t.coe_nonneg, le_rfl⟩

lemma eventually_valid_agrees {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    ∀ᶠ n : ℕ in atTop, c.valid n t z ω ∧
      c.Q n t (z, ω) = logLoewnerCoordinates G z t := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (-Real.log (G t z).im) (Real.log z.im))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlo : -(n : ℝ) ≤ Real.log (G t z).im := by
    have ha := (le_max_left (-Real.log (G t z).im) (Real.log z.im)).trans (hN.trans hNn)
    linarith
  have hhi : Real.log z.im ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
  have he := c.agrees_of_live ω hUc h n t z hz hlo hhi
  refine ⟨⟨hz.1.1, hhi, ?_⟩, he⟩
  rw [he, logCoordinates_im]
  exact hlo

end SpatialClippedFamily
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

noncomputable def greenApprox (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (p : ℝ≥0 × (ℂ × Ω)) : ℝ := by
  classical
  exact if c.valid n p.1 p.2.1 p.2.2 then greenLogDensity κ (c.Q n p.1 p.2) (B p.1 p.2.2) else 0

lemma greenApprox_measurable (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (n : ℕ) :
    Measurable (c.greenApprox κ B n) := by
  have hQ := (c.measurable n).comp
    ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hB : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => B p.1 p.2.2) :=
    hBm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply Measurable.ite (c.valid_measurable n) _ measurable_const
  exact (greenLogDensity_contDiff κ).continuous.measurable.comp (hQ.prodMk hB)

noncomputable def jointGreen (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (p : ℝ≥0 × (ℂ × Ω)) : ℝ := limUnder atTop (fun n => c.greenApprox κ B n p)

lemma jointGreen_measurable (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    Measurable (c.jointGreen κ B) :=
  (StronglyMeasurable.limUnder (fun n => (c.greenApprox_measurable κ B hBm n).stronglyMeasurable)).measurable

lemma jointGreen_eq (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hUc : Continuous (fun t => U t ω))
    (hU : ∀ t, U t ω = Real.sqrt κ * B t ω)
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) :
    c.jointGreen κ B (t, z, ω) = greenDensity κ (fun s => U s ω) γ G t z := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  by_cases hz : z ∈ survivingDomain γ t
  · filter_upwards [c.eventually_valid_agrees ω hUc hw t z hz] with n hn
    rw [greenApprox, ite_eq_left hn.1, hn.2]
    exact greenLogDensity_logCoordinates hUc hw κ (B t ω) z t hz (hU t)
  · filter_upwards [] with n
    have hn : ¬ c.valid n t z ω := fun hv => hz (c.live_of_valid ω hUc hw n t z hv)
    simp only [greenApprox, ite_eq_right hn, greenDensity, ite_eq_right hz]

end SpatialClippedFamily

 

theorem exists_joint_green_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) :
    ∃ M : ℝ≥0 × (ℂ × Ω) → ℝ, Measurable M ∧
      ∀ᵐ ω ∂P, ∀ t z, M (t, z, ω) =
        greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z := by
  obtain ⟨C, hCm, hCc, _, _, hCB⟩ := exists_regular_brownian_version hB
  let U (t : ℝ≥0) (ω : Ω) := Real.sqrt κ * C t ω
  let c := spatialClippedFamily U (hCm.const_mul _) (fun ω => (hCc ω).const_mul _)
  refine ⟨c.jointGreen κ C, c.jointGreen_measurable κ C hCm, ?_⟩
  filter_upwards [hw, hCB] with ω hω hCBω
  have hwC : IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω) := by
    simpa only [U, hCBω] using hω
  intro t z
  have hh := c.jointGreen_eq κ C ω ((hCc ω).const_mul _) (fun _ => rfl) hwC t z
  simpa only [U, hCBω] using hh

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

noncomputable def chartApprox (n : ℕ) (p : ℝ≥0 × (ℂ × Ω)) : ℂ := by
  classical
  exact if c.valid n p.1 p.2.1 p.2.2 then
    ((c.Q n p.1 p.2).1.re : ℂ) + (Real.exp (c.Q n p.1 p.2).1.im : ℂ) * Complex.I
  else 0

lemma chartApprox_measurable (n : ℕ) : Measurable (c.chartApprox n) := by
  have hQ := (c.measurable n).comp
    ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hre := Complex.measurable_ofReal.comp (Complex.measurable_re.comp hQ.fst)
  have him := Complex.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp (Complex.measurable_im.comp hQ.fst))
  exact Measurable.ite (c.valid_measurable n) (hre.add (him.mul_const _)) measurable_const

end SpatialClippedFamily
end SLEExactGauge
end
end
end

end OAI
