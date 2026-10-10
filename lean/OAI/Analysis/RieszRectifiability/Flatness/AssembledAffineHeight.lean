import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.AmbientAffineHeight

namespace OAI

/-!
# Assembling affine height coordinates

Coordinatewise continuous linear maps assemble into a Euclidean-valued map. Their affine
extensions give an ambient vector-valued affine map, whose Lipschitz constant is bounded by the
operator norm of its linear part.
-/

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

def assembleCoordinateLinear {n q : ℕ} (M : Fin q → Ambient n →L[ℝ] ℝ) :
    Ambient n →L[ℝ] Ambient q :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi M)

theorem assembleCoordinateLinear_apply {n q : ℕ} (M : Fin q → Ambient n →L[ℝ] ℝ)
    (x : Ambient n) (i : Fin q) : assembleCoordinateLinear M x i = M i x := rfl

theorem exists_ambient_vector_affine {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : Fin q → ℝ) (M : Fin q → Ambient n →L[ℝ] ℝ) :
    ∃ b : Ambient q, ∃ B : Ambient d →L[ℝ] Ambient q, ∀ x i,
      (b + B x) i = ambientAffineHeight a L (c i) (M i) x := by
  refine ⟨toLp 2 c - assembleCoordinateLinear M (L.toContinuousLinearMap.adjoint a),
    (assembleCoordinateLinear M).comp L.toContinuousLinearMap.adjoint, ?_⟩
  intro x i
  change c i - M i (L.toContinuousLinearMap.adjoint a) +
    M i (L.toContinuousLinearMap.adjoint x) =
      c i + M i (L.toContinuousLinearMap.adjoint (x - a))
  rw [map_sub, map_sub]
  ring

theorem vectorAffine_lipschitz {d q : ℕ} (b : Ambient q) (B : Ambient d →L[ℝ] Ambient q) :
    LipschitzWith ‖B‖₊ (fun x => b + B x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_add_left, coe_nnnorm] using! B.lipschitzWith.dist_le_mul x y

end

end RieszRectifiability

end OAI
