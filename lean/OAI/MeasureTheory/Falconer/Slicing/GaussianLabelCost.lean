import OAI.MeasureTheory.Falconer.Slicing.GaussianIncidenceTail
import OAI.MeasureTheory.Falconer.Slicing.GaussianPruningSets

namespace OAI

/-! # Integrating direction-label deletion costs against the point slices -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_point_weighted_label_integral
    (μ : Measure (Space d)) [SFinite μ] {δ : ℝ} (hδ : 0 < δ)
    (f : (Fin h → Space d) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointMass μ δ p*f p.1
      ∂(gaussianRows d h).prod volume) =
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*∫⁻ A, f A ∂gaussianRows d h := by
  rw [lintegral_prod (fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*f p.1)
    (show AEMeasurable (fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*f p.1)
      ((gaussianRows d h).prod volume) from
        ((gaussianPointMass_measurable μ δ).mul (hf.comp measurable_fst)).aemeasurable)]
  have hi (A : Fin h → Space d) :
      (∫⁻ z : Space h, gaussianPointMass μ δ (A,z)*f A) =
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*f A := by
    rw [lintegral_mul_const (f A) (show Measurable (fun z : Space h => gaussianPointMass μ δ (A,z)) from
      (gaussianPointMass_measurable μ δ).comp
        (show Measurable (fun z : Space h => (A,z)) from by fun_prop)),gaussianPointMass_integrated μ A hδ]
  simp_rw [hi]
  exact lintegral_const_mul _ hf

theorem gaussian_direction_good_compl_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    Measurable (fun A : Fin h → Space d => gaussianDirectionSliceMeasure ν A δ
      (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)ᶜ) := by
  have hg : MeasurableSet {p : (Fin h → Space d) × Sphere d |
      p.2 ∈ finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r T} := by
    change MeasurableSet {p : (Fin h → Space d) × Sphere d |
      ∀ i, gaussianDirectionSliceMeasure ν p.1 δ (Metric.ball p.2 (2*r i)) ≤ T i}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (gaussian_direction_ball_mass_measurable ν δ (2*r i)) measurable_const)
  exact gaussian_direction_restriction_mass_measurable ν δ _ hg.compl

theorem gaussian_point_good_compl_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    Measurable (fun p : (Fin h → Space d) × Space h => gaussianPointSliceMeasure μ p.1 p.2 δ
      (gaussianPointGood μ δ r T p)ᶜ) :=
  gaussian_point_restriction_mass_measurable μ δ _
    (gaussianPointGood_measurable_joint μ δ r T).compl

end Falconer

end OAI
