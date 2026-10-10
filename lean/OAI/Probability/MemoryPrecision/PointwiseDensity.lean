import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.JointL1

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def PointwiseDensity {d : ℕ} (μ : Measure (Space d)) (m : ℕ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) : ℝ := by
  classical
  exact if h : ∃ l : ℝ, Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x)
      atTop (𝓝 l) then Classical.choose h else 0

lemma measurable_GaussianRegularization {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (m : ℕ) (δ : ℝ) : Measurable (GaussianRegularization μ m δ) := by
  have he : GaussianRegularization μ m δ = fun x =>
      (projectionSmoothing μ (gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩) m x).toReal :=
    funext (GaussianRegularization_eq_toReal μ m δ)
  rw [he]
  exact (measurable_projectionSmoothing μ _ (measurable_gaussianPDF _ _) m).ennreal_toReal

lemma PointwiseDensity_eq_of_tendsto {d m : ℕ} (μ : Measure (Space d))
    (x : (Fin m → Space d) × (Fin m → ℝ)) {l : ℝ}
    (h : Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x) atTop (𝓝 l)) :
    PointwiseDensity μ m x = l := by
  classical
  unfold PointwiseDensity
  rw [dite_eq_left ⟨l,h⟩]
  exact tendsto_nhds_unique (Classical.choose_spec (show ∃ l : ℝ,
    Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x) atTop (𝓝 l) from ⟨l,h⟩)) h

lemma measurable_PointwiseDensity {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (m : ℕ) : Measurable (PointwiseDensity μ m) := by
  classical
  let S := {x : (Fin m → Space d) × (Fin m → ℝ) | ∃ l : ℝ,
    Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x) atTop (𝓝 l)}
  have hS : MeasurableSet S :=
    measurableSet_exists_tendsto (fun i => measurable_GaussianRegularization μ m _)
  apply measurable_of_tendsto_metrizable
    (f := fun i => S.indicator (GaussianRegularization μ m (1/(i:ℝ))))
    (fun i => (measurable_GaussianRegularization μ m _).indicator hS)
  apply tendsto_pi_nhds.mpr
  intro x
  by_cases hx : x ∈ S
  · rcases hx with ⟨l,hl⟩
    rw [PointwiseDensity_eq_of_tendsto μ x hl]
    simpa only [Set.indicator_of_mem (show x ∈ S from ⟨l,hl⟩)] using hl
  · have he : PointwiseDensity μ m x = 0 := by
      unfold PointwiseDensity
      exact dite_eq_right hx
    rw [he]
    simpa only [Set.indicator_of_notMem hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

lemma GaussianRegularization_nonneg {d : ℕ} (μ : Measure (Space d)) (m : ℕ) (δ : ℝ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) : 0 ≤ GaussianRegularization μ m δ x :=
  integral_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _))

lemma PointwiseDensity_nonneg {d : ℕ} (μ : Measure (Space d)) (m : ℕ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) : 0 ≤ PointwiseDensity μ m x := by
  classical
  unfold PointwiseDensity
  split_ifs with h
  · exact ge_of_tendsto (Classical.choose_spec h)
      (Eventually.of_forall (fun i => GaussianRegularization_nonneg μ m _ x))
  · exact le_rfl
end MemoryPrecision


end

end OAI
