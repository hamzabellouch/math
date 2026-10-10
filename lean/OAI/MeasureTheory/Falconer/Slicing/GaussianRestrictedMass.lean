import OAI.MeasureTheory.Falconer.Slicing.GaussianBallMeasurable

namespace OAI

/-! # Jointly measurable restrictions of the actual Gaussian slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem parameter_restricted_mass_measurable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (B G : Set (P × X)) (hB : MeasurableSet B) (hG : MeasurableSet G) :
    Measurable (fun p : P => (μ.restrict {x | (p,x) ∈ B}) {x | (p,x) ∈ G}) := by
  convert (measurable_measure_prodMk_left (ν := μ) (hG.inter hB)) using 1
  ext p
  rw [Measure.restrict_apply (show MeasurableSet {x | (p,x) ∈ G} from
    hG.preimage measurable_prodMk_left)]
  rfl

theorem gaussian_direction_restriction_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ)
    (G : Set ((Fin h → Space d) × Sphere d)) (hG : MeasurableSet G) :
    Measurable (fun A : Fin h → Space d =>
      gaussianDirectionSliceMeasure ν A r {w | (A,w) ∈ G}) := by
  simp only [gaussianDirectionSliceMeasure,Measure.smul_apply,smul_eq_mul]
  apply Measurable.const_mul
  let B : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hB : MeasurableSet B := by
    simp only [B,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact parameter_restricted_mass_measurable ν B G hB hG

theorem gaussian_point_restriction_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (r : ℝ)
    (G : Set (((Fin h → Space d) × Space h) × Space d)) (hG : MeasurableSet G) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      gaussianPointSliceMeasure μ p.1 p.2 r {x | (p,x) ∈ G}) := by
  simp only [gaussianPointSliceMeasure,Measure.smul_apply,smul_eq_mul]
  apply Measurable.const_mul
  let B : Set (((Fin h → Space d) × Space h) × Space d) :=
    {p | ∀ i, |inner ℝ p.2 (p.1.1 i)-p.1.2 i| ≤ r}
  have hB : MeasurableSet B := by
    simp only [B,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact parameter_restricted_mass_measurable μ B G hB hG

theorem gaussian_direction_bad_ball_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) (T : ℝ≥0∞) :
    Measurable (fun A : Fin h → Space d =>
      gaussianDirectionSliceMeasure ν A r
        {w | T < gaussianDirectionSliceMeasure ν A r (Metric.ball w ρ)}) :=
  gaussian_direction_restriction_mass_measurable ν r _
    (measurableSet_lt measurable_const (gaussian_direction_ball_mass_measurable ν r ρ))

theorem gaussian_point_bad_ball_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (r ρ : ℝ) (T : ℝ≥0∞) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      gaussianPointSliceMeasure μ p.1 p.2 r
        {x | T < gaussianPointSliceMeasure μ p.1 p.2 r (Metric.ball x ρ)}) :=
  gaussian_point_restriction_mass_measurable μ r _
    (measurableSet_lt measurable_const (gaussian_point_ball_mass_measurable μ r ρ))

end Falconer

end OAI
