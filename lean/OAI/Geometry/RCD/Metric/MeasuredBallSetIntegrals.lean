import OAI.Geometry.RCD.Metric.MeasuredBallLaw

namespace OAI

/-! # Set integrals under the exact normalized approximation laws -/

open Set Metric Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem normalizedBallPushforward_measurable_integral {n : ℕ} (μ : Measure X)
    (p : X) (r S : ℝ) (v : X → Euclidean n) (hfin : μ (ball p (S*r))≠⊤)
    (hpos : 0<μ.real (ball p (S*r))) (hv : Measurable v)
    {φ : Euclidean n → ℝ} (hφ : Measurable φ) :
    (∫ z, φ z ∂(normalizedBallPushforward μ p r S v hfin : Measure (Euclidean n)))=
      (μ.real (ball p (S*r)))⁻¹*(∫ x in ball p (S*r), φ (v x) ∂μ) := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hn : μ.restrict (ball p (S*r))≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp [Measure.real] at hh
    exact (ne_of_gt hpos) hh
  change (∫ z, φ z ∂((normalizedProbabilityLaw (μ.restrict (ball p (S*r)))).map v :
    Measure (Euclidean n)))=_
  rw [ProbabilityMeasure.toMeasure_map,integral_map hv.aemeasurable hφ.aestronglyMeasurable,
    normalizedProbabilityLaw_integral _ hn]
  simp only [Measure.real,Measure.restrict_apply_univ]

theorem normalizedBallPushforward_setIntegral {n : ℕ} (μ : Measure X)
    (p : X) (r S : ℝ) (v : X → Euclidean n) (hfin : μ (ball p (S*r))≠⊤)
    (hpos : 0<μ.real (ball p (S*r))) (hv : Measurable v)
    {s : Set (Euclidean n)} (hs : MeasurableSet s)
    {φ : Euclidean n → ℝ} (hφ : Measurable φ) :
    (∫ z in s, φ z ∂(normalizedBallPushforward μ p r S v hfin : Measure (Euclidean n)))=
      (μ.real (ball p (S*r)))⁻¹*
        (∫ x in v ⁻¹' s ∩ ball p (S*r), φ (v x) ∂μ) := by
  have h := normalizedBallPushforward_measurable_integral μ p r S v hfin hpos hv
    (hφ.indicator hs)
  rw [integral_indicator hs] at h
  have he : (fun x => s.indicator φ (v x))=(v ⁻¹' s).indicator (fun x => φ (v x)) := by
    funext x
    by_cases hx : v x∈s <;> simp [hx]
  rw [he,integral_indicator (hv hs),Measure.restrict_restrict (hv hs)] at h
  exact h

theorem euclideanBallProbability_setIntegral {n : ℕ} {S : ℝ} (hS : 0<S)
    {s : Set (Euclidean n)} (hs : MeasurableSet s) (φ : Euclidean n → ℝ) :
    (∫ z in s, φ z ∂(euclideanBallProbability n S : Measure (Euclidean n)))=
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z in s ∩ ball 0 S, φ z) := by
  have h := euclideanBallProbability_integral hS (s.indicator φ)
  rw [integral_indicator hs,integral_indicator hs,Measure.restrict_restrict hs] at h
  exact h

end RegularPointCoordinates

end

end OAI
