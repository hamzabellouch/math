import OAI.Geometry.RCD.Metric.MetricBallLaw

namespace OAI

/-! # Exact set masses of the normalized laws on a metric limit -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace Y]

theorem metricBallLaw_real (μ : Measure X) (p : X) (r S : ℝ)
    (V : X → Y) (hfin : μ (ball p (S*r))≠⊤)
    (hpos : 0<μ.real (ball p (S*r))) (hVm : Measurable V)
    {A : Set Y} (hA : MeasurableSet A) :
    (metricBallLaw μ p r S V hfin : Measure Y).real A=
      (μ.real (ball p (S*r)))⁻¹*μ.real (V ⁻¹' A∩ball p (S*r)) := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hn : μ.restrict (ball p (S*r))≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp [Measure.real] at hh
    exact hpos.ne' hh
  change (((normalizedProbabilityLaw (μ.restrict (ball p (S*r)))).map V :
    Measure Y).real A)=_
  simp only [Measure.real,ProbabilityMeasure.toMeasure_map,Measure.map_apply hVm hA]
  rw [normalizedProbabilityLaw_measure _ hn,Measure.smul_apply,
    Measure.restrict_apply (hVm hA),Measure.restrict_apply_univ]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]

theorem metricBallLaw_mass_lower (μ : Measure X) (p : X) (r S : ℝ)
    (V : X → Y) (hfin : μ (ball p (S*r))≠⊤)
    (hpos : 0<μ.real (ball p (S*r))) (hVm : Measurable V)
    {A : Set Y} (hA : MeasurableSet A) {B : Set X}
    (hsub : B⊆V ⁻¹' A∩ball p (S*r)) {D : ℝ} (hD : 0<D)
    (hvol : μ.real (ball p (S*r))≤D*μ.real B) :
    D⁻¹≤(metricBallLaw μ p r S V hfin : Measure Y).real A := by
  rw [metricBallLaw_real μ p r S V hfin hpos hVm hA]
  have hbound : μ.real B≤μ.real (V ⁻¹' A∩ball p (S*r)) :=
    measureReal_mono hsub (ne_of_lt ((measure_mono inter_subset_right).trans_lt
      (lt_top_iff_ne_top.mpr hfin)))
  have hv : D⁻¹*μ.real (ball p (S*r))≤μ.real B := by
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hvol)
  calc
    D⁻¹=(μ.real (ball p (S*r)))⁻¹*(D⁻¹*μ.real (ball p (S*r))) := by
      field_simp [hpos.ne']
    _≤(μ.real (ball p (S*r)))⁻¹*μ.real B :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hpos.le)
    _≤_ := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)

variable [MetricSpace Y]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem pointed_metric_source_ball_image {p q : X} {o z : Y} {r S ε t : ℝ}
    (hr : 0<r) {V : X → Y} (hV : IsPointedApproximation p o r S ε V)
    (hq : dist q p≤S*r) (hsub : ball q (t*r)⊆ball p (S*r))
    (hz : dist (V q) z≤ε) :
    ball q (t*r)⊆V ⁻¹' closedBall z (t+2*ε)∩ball p (S*r) := by
  intro x hx
  refine ⟨?_,hsub hx⟩
  have hd := (abs_le.mp (hV.2.1 x q (hsub hx).le hq)).2
  have ht : dist x q/r<t := (div_lt_iff₀ hr).mpr hx
  have hh := dist_triangle (V x) (V q) z
  change dist (V x) z≤t+2*ε
  linarith

end RegularPointCoordinates

end

end OAI
