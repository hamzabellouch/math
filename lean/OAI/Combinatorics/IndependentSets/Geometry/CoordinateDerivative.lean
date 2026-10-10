import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.SumCoordinateNorm

namespace OAI

namespace LargeIndependentSets.CubeGradient
open MeasureTheory Set
open scoped BigOperators NNReal Classical

noncomputable def coordinateDerivative {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ := deriv (f ∘ Function.update x i) (x i)

lemma coordinateDerivative_eq {n : ℕ} {f : (Fin n → ℝ) → ℝ} (i : Fin n)
    {x : Fin n → ℝ} (hx : DifferentiableAt ℝ f x) :
    coordinateDerivative f i x = fderiv ℝ f x (Pi.single i 1) := by
  unfold coordinateDerivative
  rw [fderiv_comp_deriv _ (by simpa using hx) (hasDerivAt_update x i (x i)).differentiableAt]
  simp [deriv_update]

lemma fderiv_coordinate_integrable {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (i : Fin n) (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun x => |fderiv ℝ f x (Pi.single i 1)|) μ := by
  apply (integrable_const (L:ℝ)).mono'
    ((measurable_fderiv_apply_const ℝ f (Pi.single i 1)).abs.stronglyMeasurable.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_abs]
  exact (Finset.single_le_sum (fun j _ => abs_nonneg (fderiv ℝ f x (Pi.single j 1)))
    (Finset.mem_univ i)).trans (lipschitz_sum_partials hf x)

theorem integral_total_coordinate_variation {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure (Fin n → ℝ))) :
    (∀ i, Integrable (fun x => |coordinateDerivative f i x|) μ) ∧
    (∑ i, ∫ x, |coordinateDerivative f i x| ∂μ) ≤ L := by
  have he (i : Fin n) : (fun x => |coordinateDerivative f i x|) =ᵐ[μ]
      (fun x => |fderiv ℝ f x (Pi.single i 1)|) := by
    filter_upwards [hμ.ae_le hf.ae_differentiableAt] with x hx
    rw [coordinateDerivative_eq i hx]
  have hi (i : Fin n) : Integrable (fun x => |coordinateDerivative f i x|) μ :=
    (fderiv_coordinate_integrable hf i μ).congr (he i).symm
  refine ⟨hi, ?_⟩
  simp_rw [integral_congr_ae (he _)]
  rw [← integral_finsetSum _ (fun i _ => fderiv_coordinate_integrable hf i μ)]
  have hs : Integrable (fun x => ∑ i, |fderiv ℝ f x (Pi.single i 1)|) μ :=
    integrable_finsetSum _ (fun i _ => fderiv_coordinate_integrable hf i μ)
  have h := integral_mono_ae hs (integrable_const (L:ℝ))
    (Filter.Eventually.of_forall (fun x => lipschitz_sum_partials hf x))
  simpa using h

end LargeIndependentSets.CubeGradient

end OAI
