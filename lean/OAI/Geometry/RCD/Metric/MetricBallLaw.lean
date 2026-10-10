import OAI.Geometry.RCD.Coordinates.NormalizedLawCompression
import OAI.Geometry.RCD.Coordinates.NormalizedProbabilityLaw
import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-! # Exact normalized ball laws on a general pointed metric target -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y]

def metricBallLaw (μ : Measure X) (p : X) (r S : ℝ)
    (v : X → Y) (hfin : μ (ball p (S*r))≠⊤) : ProbabilityMeasure Y := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  exact (normalizedProbabilityLaw (μ.restrict (ball p (S*r)))).map v

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem pointed_metric_radial_distance {p : X} {q : Y} {r S ε : ℝ}
    (hr : 0<r) (hS : 0≤S) {v : X → Y}
    (hv : IsPointedApproximation p q r S ε v) {x : X} (hx : dist x p≤S*r) :
    |dist (v x) q-dist x p/r|≤2*ε := by
  have hd := abs_le.mp (hv.2.1 x p hx (by simp; positivity))
  have ht₁ := dist_triangle (v x) (v p) q
  have ht₂ := dist_triangle (v x) q (v p)
  rw [dist_comm q (v p)] at ht₂
  exact abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.1]⟩

variable [BorelSpace Y]

theorem metricBallLaw_integral (μ : Measure X) (p : X) (r S : ℝ)
    (v : X → Y) (hfin : μ (ball p (S*r))≠⊤)
    (hpos : 0<μ.real (ball p (S*r))) (hv : Measurable v)
    {φ : Y → ℝ} (hφ : Continuous φ) :
    (∫ z, φ z ∂(metricBallLaw μ p r S v hfin : Measure Y))=
      (μ.real (ball p (S*r)))⁻¹*(∫ x in ball p (S*r), φ (v x) ∂μ) := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hn : μ.restrict (ball p (S*r))≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp [Measure.real] at hh
    exact hpos.ne' hh
  simpa only [metricBallLaw,Measure.real,Measure.restrict_apply_univ] using
    normalizedProbabilityLaw_map_integral (μ.restrict (ball p (S*r))) hn hv hφ

variable [BorelSpace X]

theorem metricBallLaw_supported (μ : Measure X) (p : X) {q : Y} {r S ε : ℝ}
    (hr : 0<r) (hS : 0≤S) (V : X → Y) (hVm : Measurable V)
    (hV : IsPointedApproximation p q r S ε V)
    (hfin : μ (ball p (S*r))≠⊤) (hpos : 0<μ.real (ball p (S*r))) :
    ∀ᵐ z ∂(metricBallLaw μ p r S V hfin : Measure Y), z∈closedBall q (S+2*ε) := by
  let : Nonempty X := ⟨p⟩
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hn : μ.restrict (ball p (S*r))≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp [Measure.real] at hh
    exact hpos.ne' hh
  change ∀ᵐ z ∂((normalizedProbabilityLaw (μ.restrict (ball p (S*r)))).map V : Measure Y), _
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hVm.aemeasurable measurableSet_closedBall).mpr
  filter_upwards [normalized_restriction_ae_mem μ measurableSet_ball hn] with x hx
  have hrad := (abs_le.mp (pointed_metric_radial_distance hr hS hV hx.le)).2
  have hd : dist x p/r<S := (div_lt_iff₀ hr).mpr hx
  change dist (V x) q≤S+2*ε
  linarith

end RegularPointCoordinates

end

end OAI
