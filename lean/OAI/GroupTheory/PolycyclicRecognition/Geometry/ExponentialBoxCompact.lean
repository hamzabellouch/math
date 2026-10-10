import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCoordinates
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OAI

/-! # Compactness of exponential coordinate boxes -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L V G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [T2Space V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace G]

theorem isCompact_exponentialCoordinateBox {n : ℕ}
    (e : L ≃ₗ[ℝ] V) (Exp : V → G) (chart : V ≃ₜ G)
    (hchart : ∀ x, chart x = Exp x) (b : Basis (Fin n) ℝ L)
    (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (exponentialCoordinateBox (Exp ∘ e) b R) := by
  rw [exponentialCoordinateBox_eq_cube_image _ _ R hR]
  have hf : ((Exp ∘ e) ∘ b.equivFun.symm) =
      chart ∘ (b.map e).equivFun.symm := by
    funext t
    simp only [Function.comp_apply, hchart, Basis.map_equivFun]
    rfl
  rw [hf]
  exact isCompact_Icc.image
    (chart.continuous.comp (b.map e).equivFun.symm.toContinuousLinearEquiv.continuous)

end PolycyclicRecognition

end

end OAI
