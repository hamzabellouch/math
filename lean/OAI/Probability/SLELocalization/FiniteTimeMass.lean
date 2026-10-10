import Mathlib
import OAI.Probability.SLELocalization.FiniteClock
import OAI.Probability.SLELocalization.PhysicalPast
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Finite Time Mass estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteTilt GreenPhysical

theorem physicalDistanceStoppedDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (ε : ℝ) (hε : 0 < ε) (hsmall : ε < z.im) :
    (∫⁻ sample, physicalStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z ε ∂P) =
        ENNReal.ofReal ((2*z.im)^(-codimension κ) * (z.im/‖z‖)^(8/κ-1)) := by
  obtain ⟨u,hu,hρ⟩ : ∃ u : ℝ, 0 < u ∧ (2*z.im)*Real.exp (-u) < ε/4 := by
    have hl : Tendsto (fun u : ℝ => (2*z.im)*Real.exp (-u)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
    exact ((eventually_gt_atTop 0).and (hl.eventually (gt_mem_nhds (by linarith : 0 < ε/4)))).exists
  let C := cutoffs hz u hu.le
  let F := fun n sample => ENNReal.ofReal ((C n).physicalValue κ B γ ε sample)
  have hexp (n : ℕ) := (C n).physical_expectation hB κ hκ γ g f hmaps hz hu ε
  have hFm (n : ℕ) : AEMeasurable (F n) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hexp n).1.aemeasurable
  have hFb (n : ℕ) : ∀ᵐ sample ∂P, F n sample ≤ ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb
    exact ENNReal.ofReal_le_ofReal ((C n).physicalValue_bound κ hκ B γ ε sample hz hu hc hb)
  have hFl : ∀ᵐ sample ∂P, Tendsto (fun n => F n sample) atTop
      (𝓝 (physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z ε)) := by
    filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb
    exact tendsto_physicalValue_killed κ B γ g f sample hm hz hu hc hb hε hsmall hρ hκ
  have hfin : (∫⁻ _ : Ω, ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) ∂P) ≠ (⊤ : ℝ≥0∞) := by
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  have hdct := tendsto_lintegral_of_dominated_convergence'
    (fun _ : Ω => ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8)))) hFm hFb hfin hFl
  have hint (n : ℕ) : (∫⁻ sample, F n sample ∂P) = ENNReal.ofReal (green (1-κ/8) (8/κ-1) z.re z.im 0) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hexp n).1
      (Filter.Eventually.of_forall (fun sample => (C n).physicalValue_nonneg κ B γ ε sample)), (hexp n).2]
  simp only [hint] at hdct
  have he := tendsto_nhds_unique hdct tendsto_const_nhds
  rw [green_initial κ hz] at he
  exact he

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.FiniteTilt

lemma physicalValue_aemeasurable_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
    {e : ℝ} (he : 0 < e) (hes : e < z.im) (hr : (2*z.im)*Real.exp (-u) < e/4) :
    (∀ n : ℕ, AEMeasurable (fun sample => ENNReal.ofReal
      ((cutoffs hz u hu.le n).physicalValue κ B γ e sample)) P) ∧
    ∀ᵐ sample ∂P, Tendsto (fun n => ENNReal.ofReal
      ((cutoffs hz u hu.le n).physicalValue κ B γ e sample)) atTop
      (𝓝 (physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e)) := by
  constructor
  · intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((cutoffs hz u hu.le n).physical_expectation hB κ hκ γ g f hmaps hz hu e).1.aemeasurable
  · filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb
    exact tendsto_physicalValue_killed κ B γ g f sample hm hz hu hc hb he hes hr hκ

lemma tendsto_setLIntegral_physicalValue {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
    {e : ℝ} (he : 0 < e) (hes : e < z.im) (hr : (2*z.im)*Real.exp (-u) < e/4) (E : Set Ω) :
    Tendsto (fun n => ∫⁻ sample in E, ENNReal.ofReal
      ((cutoffs hz u hu.le n).physicalValue κ B γ e sample) ∂P) atTop
      (𝓝 (∫⁻ sample in E, physicalStoppedDensity κ (fun t => B t sample)
        (γ sample) (g sample) z e ∂P)) := by
  let C := cutoffs hz u hu.le
  let F := fun n sample => ENNReal.ofReal ((C n).physicalValue κ B γ e sample)
  obtain ⟨hFm,hFl⟩ := physicalValue_aemeasurable_tendsto hB κ hκ γ g f hmaps hz hu he hes hr
  have hFb (n : ℕ) : ∀ᵐ sample ∂P.restrict E,
      F n sample ≤ ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) := by
    apply ae_restrict_of_ae
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb
    exact ENNReal.ofReal_le_ofReal ((C n).physicalValue_bound κ hκ B γ e sample hz hu hc hb)
  have hfin : (∫⁻ _ : Ω in E, ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) ∂P) ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  exact tendsto_lintegral_of_dominated_convergence' _
    (fun n => (hFm n).mono_measure Measure.restrict_le_self) hFb hfin (ae_restrict_of_ae hFl)

end SLEExactGauge.FiniteTilt

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteTilt

lemma physical_radial_avoidance_identity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 < u)
    (e : ℝ) (he : 0 < e) (hes : e < z.im) (hr : (2*z.im)*Real.exp (-u) < e/4) (S : ℝ≥0) :
    (∫⁻ sample in PhysicalPast.avoids κ B z e S,
      physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e ∂P) =
    ∫⁻ sample in PhysicalPast.avoids κ B z e S,
      finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∂P := by
  let C := cutoffs hz u hu.le
  let E := PhysicalPast.avoids κ B z e S
  have hp := tendsto_setLIntegral_physicalValue hB κ hκ γ g f hmaps hz hu he hes hr E
  have hr := tendsto_setLIntegral_value hB κ hκ γ g f hmaps hz hu.le C
    (shrinkingAngle_tendsto z) E
  have hh (n : ℕ) : (∫⁻ sample in E, ENNReal.ofReal ((C n).physicalValue κ B γ e sample) ∂P) =
      ∫⁻ sample in E, ENNReal.ofReal ((C n).value κ B sample) ∂P := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((C n).physical_expectation hB κ hκ γ g f hmaps hz hu e).1.integrableOn
      (Filter.Eventually.of_forall (fun sample => (C n).physicalValue_nonneg κ B γ e sample)),
      ← ofReal_integral_eq_lintegral_ofReal ((C n).expectation hB κ hκ hz hu.le).1.integrableOn
      (Filter.Eventually.of_forall (fun sample => (C n).value_nonneg κ B sample))]
    exact congrArg ENNReal.ofReal ((C n).physical_avoidance_setIntegral hB κ hκ hz hu γ g f hmaps e S).symm
  exact tendsto_nhds_unique (hp.congr' (Filter.Eventually.of_forall hh)) hr

lemma physicalStoppedDensity_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (e : ℝ) (he : 0 < e) (hes : e < z.im) :
    AEMeasurable (fun sample => physicalStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z e) P := by
  obtain ⟨u,hu,hr⟩ : ∃ u : ℝ, 0 < u ∧ (2*z.im)*Real.exp (-u) < e/4 := by
    have hl : Tendsto (fun u : ℝ => (2*z.im)*Real.exp (-u)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
    exact ((eventually_gt_atTop 0).and (hl.eventually (gt_mem_nhds (by linarith : 0 < e/4)))).exists
  obtain ⟨hFm,hFl⟩ := physicalValue_aemeasurable_tendsto hB κ hκ γ g f hmaps hz hu he hes hr
  exact aemeasurable_of_tendsto_metrizable_ae' hFm hFl

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma physicalStoppedDensity_pos_iff {κ : ℝ} {B : ℝ≥0 → ℝ}
    {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal) γ g f)
    (z : ℂ) (e : ℝ) :
    0 < physicalStoppedDensity κ B γ g z e ↔ firstLiveDistanceStop γ z e ≠ (⊤ : ℝ≥0∞) := by
  by_cases hh : firstLiveDistanceStop γ z e = (⊤ : ℝ≥0∞)
  · simp only [physicalStoppedDensity,hh,ite_true,lt_self_iff_false,ne_eq,not_true_eq_false]
  · rw [physicalStoppedDensity,ite_eq_right hh]
    constructor
    · exact fun _ => hh
    · intro _
      obtain ⟨t,ht,hlive,_,_⟩ := PhysicalStop.finite_spec hm.1 hh
      rw [ht,ENNReal.coe_toReal]
      apply ENNReal.ofReal_pos.2
      have hs : 0 < loewnerAngleSine κ B g t z := by
        apply div_pos (hm.im_pos t.coe_nonneg hlive)
        apply norm_pos_iff.2
        simpa only [Complex.ofReal_mul] using (hm.centered_ne_zero t.coe_nonneg hlive)
      exact mul_pos (Real.rpow_pos_of_pos (hm.radius_pos t.coe_nonneg hlive) _)
        (Real.rpow_pos_of_pos hs _)

lemma physical_avoidance_at_finite_hit {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
    (hc : Continuous (fun t => B t sample))
    (z : ℂ) (e : ℝ) (S : ℝ≥0) (hh : firstLiveDistanceStop γ z e ≠ (⊤ : ℝ≥0∞)) :
    sample ∈ PhysicalPast.avoids κ B z e S ↔ (S:ℝ≥0∞) < firstLiveDistanceStop γ z e := by
  rw [PhysicalPast.avoids_eq_source κ B sample hm hc z e S]
  obtain ⟨t,ht,hlive,hd,hmin⟩ := PhysicalStop.finite_spec hm.1 hh
  rw [ht,ENNReal.coe_lt_coe]
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge hd) (h t (not_lt.1 hn))
  · intro h s hs
    exact hmin s (hs.trans_lt h)

lemma physical_before_deep_radius {U : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing U γ g f) (hU : ContinuousOn U (Ici 0))
    {z : ℂ} {e u : ℝ} (he : 0 < e) (hes : e < z.im)
    (hr : (2*z.im)*Real.exp (-u) < e/4)
    (hh : firstLiveRadiusStop γ g z u ≠ (⊤ : ℝ≥0∞)) :
    firstLiveDistanceStop γ z e < firstLiveRadiusStop γ g z u := by
  obtain ⟨t,ht,hlive,hradius⟩ := RadiusPast.live_radius_witness hm hU hh
  rw [ht]
  by_contra hn
  have hb := hm.radius_ge_before_distance_stop he hes (not_lt.1 hn) hlive
  rw [hradius] at hb
  exact (not_lt_of_ge hb) hr

lemma physical_early_nullMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (e : ℝ) (he : 0 < e) (hes : e < z.im) (S : ℝ≥0) :
    NullMeasurableSet {sample | firstLiveDistanceStop (γ sample) z e ≤ (S:ℝ≥0∞)} P := by
  have hd := physicalStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz e he hes
  have hA := (nullMeasurableSet_lt (aemeasurable_const (b := (0 : ℝ≥0∞))) hd).inter
    (PhysicalPast.avoids_nullMeasurable κ hB z e S).compl
  apply hA.congr
  filter_upwards [hmaps,hB.cont] with sample hm hc
  change (0 < physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e ∧
    sample ∉ PhysicalPast.avoids κ B z e S) = (firstLiveDistanceStop (γ sample) z e ≤ (S:ℝ≥0∞))
  apply propext
  rw [physicalStoppedDensity_pos_iff (κ := κ) (B := fun t => B t sample) hm]
  constructor
  · rintro ⟨hh,hno⟩
    exact not_lt.1 (hno ∘ (physical_avoidance_at_finite_hit κ B sample hm hc z e S hh).2)
  · intro hle
    have hh := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    exact ⟨hh,fun hs => not_lt_of_ge hle ((physical_avoidance_at_finite_hit κ B sample hm hc z e S hh).1 hs)⟩

theorem finiteTimePhysicalDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) :
    ∃ T : ℝ, 0 < T ∧ ∀ e : ℝ, 0 < e → e < z.im →
      ENNReal.ofReal (((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))/2) ≤
        ∫⁻ sample in {sample | firstLiveDistanceStop (γ sample) z e ≤ ENNReal.ofReal T},
          physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e ∂P := by
  classical
  let m := (2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)
  let M := ENNReal.ofReal m
  have hm : 0 < m := localizationInitialGreen_pos κ hz
  have hM0 : M ≠ 0 := (ENNReal.ofReal_pos.2 hm).ne'
  have hMtop : M ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨T,hT,hclock⟩ := finiteCenteredPhysicalTime_tight κ hκ B hB γ g f hγ hmaps z hz
    (1/2) (by norm_num)
  refine ⟨T,hT,?_⟩
  intro e he hes
  let S : ℝ≥0 := ⟨T,hT.le⟩
  have hS : (S : ℝ≥0∞) = ENNReal.ofReal T := by
    change (S : ℝ≥0∞) = ENNReal.ofReal (S : ℝ)
    exact ENNReal.ofReal_coe_nnreal.symm
  let E := PhysicalPast.avoids κ B z e S
  let A := {sample | firstLiveDistanceStop (γ sample) z e ≤ (S:ℝ≥0∞)}
  let D := fun sample => physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e
  have hE : NullMeasurableSet E P := PhysicalPast.avoids_nullMeasurable κ hB z e S
  have hA : NullMeasurableSet A P := physical_early_nullMeasurable κ hκ B hB γ g f hmaps z hz e he hes S
  have hD : AEMeasurable D P := physicalStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz e he hes
  obtain ⟨u,hu,hr⟩ : ∃ u : ℝ, 1 < u ∧ (2*z.im)*Real.exp (-u) < e/4 := by
    have hl : Tendsto (fun u : ℝ => (2*z.im)*Real.exp (-u)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
    exact ((eventually_gt_atTop 1).and (hl.eventually (gt_mem_nhds (by linarith : 0 < e/4)))).exists
  have hu0 : 0 < u := by linarith
  let Q := finiteCenteredMeasure κ P B γ g z u
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hhit : ∀ᵐ sample ∂Q, firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞) := by
    change ∀ᵐ sample ∂P.withDensity _,_
    rw [ae_withDensity_iff' ((finiteStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz u hu0).div_const _)]
    exact Filter.Eventually.of_forall (fun sample hn ht => hn (by simp only [finiteStoppedDensity,ht,ite_true,ENNReal.zero_div]))
  have hsub : E ≤ᵐ[Q] {sample | (S:ℝ≥0∞) < firstLiveRadiusStop (γ sample) (g sample) z u} := by
    filter_upwards [hQP.ae_le hmaps,hQP.ae_le hB.cont,hhit] with sample hmaps hc hhit hmem
    have hpr := physical_before_deep_radius hmaps
      ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) he hes hr hhit
    have hfp : firstLiveDistanceStop (γ sample) z e ≠ (⊤ : ℝ≥0∞) := ne_top_of_lt hpr
    exact ((physical_avoidance_at_finite_hit κ B sample hmaps hc z e S hfp).1 hmem).trans hpr
  have hQE : Q E ≤ ENNReal.ofReal (1/2) := by
    apply (measure_mono_ae hsub).trans
    simpa only [hS] using (hclock u hu.le).le
  have hid : (∫⁻ sample in E, D sample ∂P) = M*Q E := by
    rw [physical_radial_avoidance_identity κ hκ B hB γ g f hmaps z hz u hu0 e he hes hr S]
    rw [show Q E = ∫⁻ sample in E, finiteStoppedDensity κ (fun t => B t sample)
        (γ sample) (g sample) z u / M ∂P from withDensity_apply₀ _ hE]
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hM0),← mul_assoc,ENNReal.mul_inv_cancel hM0 hMtop,one_mul]
  have hhalf : M*ENNReal.ofReal (1/2) = ENNReal.ofReal (m/2) := by
    rw [← ENNReal.ofReal_mul hm.le]
    congr 1
    ring
  have htail : (∫⁻ sample in E, D sample ∂P) ≤ ENNReal.ofReal (m/2) := by
    rw [hid,← hhalf]
    exact mul_le_mul' le_rfl hQE
  have hi : Eᶜ.indicator D =ᵐ[P] A.indicator D := by
    filter_upwards [hmaps,hB.cont] with sample hm hc
    by_cases hh : firstLiveDistanceStop (γ sample) z e = (⊤ : ℝ≥0∞)
    · have hd : D sample = 0 := by simp only [D,physicalStoppedDensity,hh,ite_true]
      simp only [Set.indicator_apply,hd,ite_self]
    · have hv := physical_avoidance_at_finite_hit κ B sample hm hc z e S hh
      have hae : sample ∈ Eᶜ ↔ sample ∈ A := by
        simpa only [E,A,mem_compl_iff,mem_ofPred_eq,not_lt] using hv.not
      simp only [Set.indicator_apply,hae]
  have hall : (∫⁻ sample in E, D sample ∂P)+(∫⁻ sample in A, D sample ∂P) = M := by
    rw [← lintegral_indicator₀ hA,← lintegral_congr_ae hi,← lintegral_indicator₀ hE,
      ← lintegral_add_left' (hD.indicator₀ hE)]
    have hp : (fun sample => E.indicator D sample+Eᶜ.indicator D sample) = D := by
      funext sample
      by_cases hs : sample∈E <;> simp [hs]
    rw [hp]
    exact physicalDistanceStoppedDensity κ hκ B hB γ g f hγ hmaps z hz e he hes
  have hdouble : M = ENNReal.ofReal (m/2)+ENNReal.ofReal (m/2) := by
    change ENNReal.ofReal m = _
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ m/2) (by positivity : 0 ≤ m/2)]
    congr 1
    ring
  have hlow : ENNReal.ofReal (m/2) ≤ ∫⁻ sample in A, D sample ∂P := by
    apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
    rw [← hdouble,← hall]
    exact add_le_add htail le_rfl
  simpa only [A,D,m,hS] using hlow

end SLEExactGauge

end

end

end OAI
