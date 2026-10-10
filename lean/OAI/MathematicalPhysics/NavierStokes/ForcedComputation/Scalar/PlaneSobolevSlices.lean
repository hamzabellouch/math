import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneGradientTail
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarRegularity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMassContinuity

namespace OAI

/-! For a smooth scalar, its classical derivatives through order two
are square integrable. These are the spatial H² conditions on each slice. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian MeasureTheory Set
open scoped ContDiff

def PlaneSquareIntegrableJet2 (f : Plane → ℝ) : Prop :=
  Integrable (fun x => f x ^ 2) ∧
    (∀ j, Integrable (fun x => spatialD j f x ^ 2)) ∧
    (∀ j k, Integrable (fun x => spatialD j (spatialD k f) x ^ 2))

theorem scalar_square_integrable_jet2 {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ x, |f x| ≤ B * planeTailProfile x)
    (hfM2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M)
    (hfM3 : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ M) :
    PlaneSquareIntegrableJet2 f := by
  have hfi : Integrable f := (planeTailProfile_integrable.const_mul B).mono'
    hf.continuous.aestronglyMeasurable (Filter.Eventually.of_forall
      (fun x => by simpa only [Real.norm_eq_abs] using hfB x))
  have hfb : ∀ x, ‖f x‖ ≤ B := by
    intro x
    rw [Real.norm_eq_abs]
    exact (hfB x).trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (planeTailProfile_le_one x) hB)
  have hi2 : Integrable (fun x => f x * f x) := hfi.mul_bdd
    hf.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  refine ⟨by simpa only [pow_two] using hi2, ?_, ?_⟩
  · exact scalar_gradient_square_integrable hf hB hM hfB hfM2
  · exact scalar_hessian_square_integrable hf hB hM hfB hfM3

theorem PlaneScalarSolution.square_integrable_jet2 (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x)
    {t : ℝ} (ht : t ∈ Icc 0 T) : PlaneSquareIntegrableJet2 (w t) := by
  obtain ⟨B, hB, htail⟩ := hw.uniform_tail_bound hT hν.le ha hh hc hpos
  obtain ⟨M, hM⟩ := hw.spatial_bounds hE hT hν ha hh hc
  exact scalar_square_integrable_jet2 (hw.slice_smooth ht) hB (le_max_left 0 M)
    (htail t ht) (fun x => (hM t ht 2 (by omega) x).trans (le_max_right 0 M))
    (fun x => (hM t ht 3 le_rfl x).trans (le_max_right 0 M))

end ForcedComputation.VelocityDetector

end

end OAI
