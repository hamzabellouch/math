import OAI.MeasureTheory.Falconer.Slicing.GaussianLabelCost

namespace OAI

/-! # All three marginal-pruning costs under the original joint slice law -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_point_pruning_incidence_cost
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i) (M : ℝ≥0∞)
    (hp : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r T p)ᶜ*M
        ∂(gaussianRows d h).prod volume) ≤ (∑ i, (T i)⁻¹*C i)*M := by
  rw [lintegral_mul_const _ (gaussian_point_good_compl_mass_measurable μ δ r T)]
  exact mul_le_mul_left (gaussian_point_finite_ball_deletion μ δ r T C hT hp) M

theorem gaussian_direction_pruning_incidence_cost
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointMass μ δ p*
      gaussianDirectionSliceMeasure ν p.1 δ
        (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r T)ᶜ
        ∂(gaussianRows d h).prod volume) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (T i)⁻¹*C i) := by
  rw [gaussian_point_weighted_label_integral μ hδ _
    (gaussian_direction_good_compl_mass_measurable ν δ r T)]
  exact mul_le_mul_right (gaussian_direction_finite_ball_deletion ν δ r T C hT hp) _

theorem gaussian_mass_pruning_incidence_cost
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) {M B : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hp : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν δ A)^2 ∂gaussianRows d h) ≤ B) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointMass μ δ p*(if M < gaussianDirectionMass ν δ p.1 then
        gaussianDirectionMass ν δ p.1 else 0) ∂(gaussianRows d h).prod volume) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
  let S : Set (Fin h → Space d) := {A | M < gaussianDirectionMass ν δ A}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (gaussianDirectionMass_measurable ν δ)
  have hf : Measurable (S.indicator (gaussianDirectionMass ν δ)) :=
    (gaussianDirectionMass_measurable ν δ).indicator hS
  have he (A : Fin h → Space d) :
      (if M < gaussianDirectionMass ν δ A then gaussianDirectionMass ν δ A else 0) =
        S.indicator (gaussianDirectionMass ν δ) A := by
    simp only [Set.indicator_apply,S,mem_ofPred_eq]
  simp_rw [he]
  rw [gaussian_point_weighted_label_integral μ hδ _ hf,lintegral_indicator hS]
  exact mul_le_mul_right (gaussian_direction_mass_tail ν hM hMtop hp) _

end Falconer

end OAI
