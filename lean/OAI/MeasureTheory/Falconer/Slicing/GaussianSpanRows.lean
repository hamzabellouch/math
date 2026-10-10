import OAI.MeasureTheory.Falconer.Slicing.GaussianFullRank
import OAI.MeasureTheory.Falconer.Slicing.GaussianMultiband
import OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates

namespace OAI

/-! # Gaussian rows projected onto a fixed finite-dimensional span -/
namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d m : ℕ}

noncomputable def projectedGaussianRows (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) (A : Fin m → Space d) : Fin m → Space m :=
  fun i => b (V.orthogonalProjectionOnto (A i))

theorem projectedGaussianRows_measurable (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) : Measurable (projectedGaussianRows V b) := by
  apply measurable_pi_iff.mpr
  intro i
  exact b.continuous.measurable.comp
    (V.orthogonalProjectionOnto.continuous.measurable.comp (measurable_pi_apply i))

theorem projectedGaussianRows_law (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) :
    (gaussianRows d m).map (projectedGaussianRows V b) = gaussianRows m m := by
  let f : Space d → Space m := fun x => b (V.orthogonalProjectionOnto x)
  have hf : Measurable f := b.continuous.measurable.comp V.orthogonalProjectionOnto.continuous.measurable
  change (Measure.pi (fun _ : Fin m => stdGaussian (Space d))).map (fun A i => f (A i)) = _
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  exact congrArg Measure.pi (funext (fun _ => gaussian_projected_coordinates V b))

theorem inner_projectedGaussianRows (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space m) (A : Fin m → Space d) (z : V) (i : Fin m) :
    inner ℝ (b z) (projectedGaussianRows V b A i) = inner ℝ (z : Space d) (A i) := by
  rw [projectedGaussianRows,b.inner_map_map]
  exact V.inner_orthogonalProjectionOnto_eq_of_mem_left z (A i)

theorem eq_zero_of_orthogonal_columns (v : Fin m → Space m)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (z : Space m)
    (hz : ∀ i, inner ℝ z (v i) = 0) : z = 0 := by
  obtain ⟨a,ha⟩ := (euclideanColumnEquiv v hv).surjective z
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ z z = inner ℝ z (∑ i, a i • v i) := by
      rw [← ha]
      rfl
    _ = 0 := by simp [inner_sum,inner_smul_right,hz]

end Falconer

end OAI
