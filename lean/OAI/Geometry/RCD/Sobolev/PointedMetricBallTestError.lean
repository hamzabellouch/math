import OAI.Geometry.RCD.Metric.MeasuredBallSetIntegrals
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance
import OAI.Geometry.RCD.Sobolev.BoundedSetTestError

namespace OAI

/-! # Physical inner balls and their image tests differ only on an annulus -/

open Set Metric MeasureTheory
open scoped BoundedContinuousFunction symmDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem pointed_metric_ball_test_error {n : ℕ} (μ : Measure X) {p : X} {r S ρ δ ε : ℝ}
    (hr : 0<r) (hS : 0≤S) (hρS : ρ≤S) (hsmall : 2*ε<δ)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v) (hvm : Measurable v)
    (hfin : μ (ball p (S*r))≠⊤) (hpos : 0<μ.real (ball p (S*r)))
    (φ : Euclidean n →ᵇ ℝ) :
    |(μ.real (ball p (S*r)))⁻¹*(∫ x in ball p (ρ*r), φ (v x) ∂μ)-
      (∫ z in ball 0 ρ, φ z ∂(normalizedBallPushforward μ p r S v hfin : Measure (Euclidean n)))|≤
      ‖φ‖*(normalizedBallPushforward μ p r S v hfin : Measure (Euclidean n)).real
        (closedBall 0 (ρ+δ) \ ball 0 (ρ-δ)) := by
  let : Nonempty X := ⟨p⟩
  let U := ball p (S*r)
  let : IsFiniteMeasure (μ.restrict U) :=
    ⟨by simpa only [U,Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  let κ := normalizedProbabilityLaw (μ.restrict U)
  have hn : μ.restrict U≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp [U,Measure.real] at hh
    exact (ne_of_gt hpos) hh
  have hκU : ∀ᵐ x ∂(κ : Measure X), x∈U := by
    apply ae_iff.mpr
    change (κ : Measure X) Uᶜ=0
    apply (measureReal_eq_zero_iff).mp
    rw [normalizedProbabilityLaw_real _ hn measurableSet_ball.compl]
    have hz : (μ.restrict U) Uᶜ=0 := by
      rw [Measure.restrict_apply measurableSet_ball.compl,compl_inter_self,measure_empty]
    change ((μ.restrict U).real univ)⁻¹*(μ.restrict U).real Uᶜ=0
    simp only [Measure.real,hz,ENNReal.toReal_zero,mul_zero]
  let f := fun x => φ (v x)
  have hfm : Measurable f := φ.continuous.measurable.comp hvm
  have hf : Integrable f (κ : Measure X) :=
    (integrable_const ‖φ‖).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => φ.norm_coe_le_norm (v x))
  have hb : ∀ᵐ x ∂(κ : Measure X), |f x|≤‖φ‖ :=
    Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using φ.norm_coe_le_norm (v x)
  have he := bounded_set_test_error (s := ball p (ρ*r)) (t := v ⁻¹' ball 0 ρ)
    (κ : Measure X) measurableSet_ball
    (hvm measurableSet_ball) hf hb
  let A := closedBall (0:Euclidean n) (ρ+δ) \ ball 0 (ρ-δ)
  have hA : MeasurableSet A := measurableSet_closedBall.diff measurableSet_ball
  have hinc : ball p (ρ*r) ∆ (v ⁻¹' ball 0 ρ) ≤ᵐ[(κ : Measure X)] v ⁻¹' A := by
    filter_upwards [hκU] with x hx
    intro hd
    apply pointed_ball_discrepancy_in_shell hr hS hsmall hv hx
    rcases mem_symmDiff.mp hd with hd | hd
    · exact Or.inl hd
    · exact Or.inr ⟨hd.2,hd.1⟩
  have hmeas : (κ : Measure X).real (ball p (ρ*r) ∆ (v ⁻¹' ball 0 ρ))≤
      (κ : Measure X).real (v ⁻¹' A) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinc)
  have hbound := he.trans (mul_le_mul_of_nonneg_left hmeas (norm_nonneg φ))
  have hs : (∫ x in ball p (ρ*r), f x ∂(κ : Measure X))=
      (μ.real U)⁻¹*(∫ x in ball p (ρ*r), f x ∂μ) := by
    have hh := normalizedProbabilityLaw_integral (μ.restrict U) hn
      ((ball p (ρ*r)).indicator f)
    rw [integral_indicator measurableSet_ball,integral_indicator measurableSet_ball,
      Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball (mul_le_mul_of_nonneg_right hρS hr.le))] at hh
    simpa only [Measure.real,Measure.restrict_apply_univ] using hh
  have ht : (∫ z in ball 0 ρ, φ z ∂(normalizedBallPushforward μ p r S v hfin : Measure (Euclidean n)))=
      ∫ x in v ⁻¹' ball 0 ρ, f x ∂(κ : Measure X) := by
    rw [← integral_indicator measurableSet_ball]
    change (∫ z, (ball 0 ρ).indicator (fun z => φ z) z ∂((κ.map v) : Measure (Euclidean n)))=_
    rw [ProbabilityMeasure.toMeasure_map,integral_map hvm.aemeasurable
      (φ.continuous.measurable.indicator measurableSet_ball).aestronglyMeasurable]
    have hi : (fun x => (ball 0 ρ).indicator (fun z => φ z) (v x))=
        (v ⁻¹' ball 0 ρ).indicator f := by
      funext x
      by_cases hx : v x∈ball 0 ρ <;> simp [hx,f]
    rw [hi,integral_indicator (hvm measurableSet_ball)]
  have hm : (normalizedBallPushforward μ p r S v hfin : Measure (Euclidean n)).real A=
      (κ : Measure X).real (v ⁻¹' A) := by
    change ((κ.map v) : Measure (Euclidean n)).real A=_
    simp only [Measure.real,ProbabilityMeasure.toMeasure_map,Measure.map_apply hvm hA]
  rw [hs,← ht,← hm] at hbound
  exact hbound

end RegularPointCoordinates

end

end OAI
