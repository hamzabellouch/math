import OAI.MeasureTheory.Falconer.Slicing.GaussianPairRestrictions
import OAI.MeasureTheory.Falconer.Slicing.GaussianFinitePruning
import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMass

namespace OAI

/-! # The actual measurable restrictions used in Gaussian slice selection -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

def gaussianPointGood (μ : Measure (Space d)) (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) : Set (Space d) :=
  finiteBallGood (gaussianPointSliceMeasure μ p.1 p.2 δ) r T

def gaussianDirectionGood (ν : Measure (Sphere d)) (δ : ℝ) (r : ι → ℝ)
    (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) : Set (Sphere d) :=
  {w | gaussianDirectionMass ν δ A ≤ M ∧ w ∈ finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T}

theorem gaussianPointGood_measurable_joint (μ : Measure (Space d)) [SFinite μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
      p.2 ∈ gaussianPointGood μ δ r T p.1} := by
  change MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
    ∀ i, gaussianPointSliceMeasure μ p.1.1 p.1.2 δ (ball p.2 (2*r i)) ≤ T i}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    (gaussian_point_ball_mass_measurable μ δ (2*r i)) measurable_const)

theorem gaussianDirectionGood_measurable_joint (ν : Measure (Sphere d)) [SFinite ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) :
    MeasurableSet {p : (Fin h → Space d) × Sphere d | p.2 ∈ gaussianDirectionGood ν δ r T M p.1} := by
  change MeasurableSet {p : (Fin h → Space d) × Sphere d |
    gaussianDirectionMass ν δ p.1 ≤ M ∧
    ∀ i, gaussianDirectionSliceMeasure ν p.1 δ (ball p.2 (2*r i)) ≤ T i}
  simp only [ofPred_and,ofPred_forall]
  apply MeasurableSet.inter
  · exact measurableSet_le ((gaussianDirectionMass_measurable ν δ).comp measurable_fst) measurable_const
  · exact MeasurableSet.iInter (fun i => measurableSet_le
      (gaussian_direction_ball_mass_measurable ν δ (2*r i)) measurable_const)

omit [Fintype ι] in
theorem gaussianPointGood_ball (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (p : (Fin h → Space d) × Space h) (i : ι) (a : Space d) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p))
      (ball a (r i)) ≤ T i := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_ball (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (A : Fin h → Space d) (i : ι) (a : Sphere d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A))
      (ball a (r i)) ≤ T i := by
  calc
    _ ≤ ((gaussianDirectionSliceMeasure ν A δ).restrict
        (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)) (ball a (r i)) :=
      Measure.restrict_mono_set _ (s := gaussianDirectionGood ν δ r T M A)
        (t := finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T) (fun _ hw => hw.2) _
    _ ≤ _ := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_mass (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A)) univ ≤ M := by
  by_cases hm : gaussianDirectionMass ν δ A ≤ M
  · calc
      _ ≤ gaussianDirectionSliceMeasure ν A δ univ := Measure.restrict_le_self _
      _ = gaussianDirectionMass ν δ A := by
        simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
      _ ≤ _ := hm
  · have he : gaussianDirectionGood ν δ r T M A = ∅ := by ext w; simp [gaussianDirectionGood,hm]
    simp only [he,Measure.restrict_empty,Measure.coe_zero,Pi.zero_apply]
    exact zero_le

end Falconer

end OAI
