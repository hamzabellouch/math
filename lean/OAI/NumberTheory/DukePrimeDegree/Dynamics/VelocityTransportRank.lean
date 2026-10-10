import OAI.NumberTheory.DukePrimeDegree.Dynamics.KernelVelocityFrames
import OAI.NumberTheory.DukePrimeDegree.Dynamics.MeasureStabilizerCovariance
import OAI.NumberTheory.DukePrimeDegree.Dynamics.OrbitRationality

namespace OAI

/-!
# Rank transport for actual stabilizer frames

Right translation conjugates the actual velocity space by a linear
equivalence. Thus the cardinality of the constructed measurable frame
is preserved under component-kernel covariance. This supplies the
invariant rank events used by the finite-frame recurrence theorem.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

def slMatrixConjugationEquiv {n : ℕ} (a : G n) :
    Matrix (Fin n) (Fin n) ℝ ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  { slMatrixConjugationLinear a with
    invFun := slMatrixConjugationLinear a⁻¹
    left_inv := fun V => by
      change slMatrixConjugation a⁻¹ (slMatrixConjugation a V) = V
      simpa only [inv_inv] using slMatrixConjugation_inverse a⁻¹ V
    right_inv := fun V => slMatrixConjugation_inverse a V }

theorem map_matrixVelocitySpace_rightAction {n : ℕ}
    (μ : Measure (X n)) (a : G n) :
    (matrixVelocitySpace (invariantRightSubgroup μ)).map
        (slMatrixConjugationEquiv a).toLinearMap =
      matrixVelocitySpace (invariantRightSubgroup (μ.map (fun x => rightAction x a))) := by
  ext V
  constructor
  · rintro ⟨W, hW, rfl⟩
    exact matrixVelocitySpace_map_rightAction μ a hW
  · intro hV
    let W := slMatrixConjugation a⁻¹ V
    have hW : W ∈ matrixVelocitySpace (invariantRightSubgroup μ) := by
      apply (matrixVelocitySpace_map_rightAction_iff μ a W).mp
      change slMatrixConjugation a (slMatrixConjugation a⁻¹ V) ∈ _
      simpa only [slMatrixConjugation_inverse] using hV
    exact ⟨W, hW, slMatrixConjugation_inverse a V⟩

theorem velocityFrameCard_map_rightAction {n : ℕ}
    (μ : Measure (X n)) (a : G n) :
    velocityFrameCard (μ.map (fun x => rightAction x a)) = velocityFrameCard μ := by
  rw [velocityFrameCard_eq_finrank, velocityFrameCard_eq_finrank,
    ← map_matrixVelocitySpace_rightAction μ a]
  exact (slMatrixConjugationEquiv a).finrank_map_eq _

end DukePrimeDegree

end

end OAI
