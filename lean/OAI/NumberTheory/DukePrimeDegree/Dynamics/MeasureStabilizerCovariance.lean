import OAI.NumberTheory.DukePrimeDegree.Geometry.MeasureConjugation
import OAI.NumberTheory.DukePrimeDegree.Dynamics.MatrixVelocitySpace

namespace OAI

/-!
# Actual stabilizers of transported component measures

Right translation conjugates the measure stabilizer in the opposite
direction. Combining this identity with component-kernel covariance
gives the exact covariance of their spaces of matrix velocities.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrixVelocitySpace_map_rightAction {n : ℕ}
    (μ : Measure (X n)) (a : G n)
    {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ matrixVelocitySpace (invariantRightSubgroup μ)) :
    a⁻¹.val * V * a.val ∈
      matrixVelocitySpace (invariantRightSubgroup (μ.map (fun x => rightAction x a))) := by
  have hc : ∀ g ∈ invariantRightSubgroup μ,
      a⁻¹ * g * (a⁻¹)⁻¹ ∈
        invariantRightSubgroup (μ.map (fun x => rightAction x a)) := by
    intro g hg
    apply (mem_invariantRightSubgroup_map_iff μ a (a⁻¹ * g * (a⁻¹)⁻¹)).mpr
    convert hg using 1
    group
  simpa only [inv_inv] using conjugate_mem_matrixVelocitySpace (invariantRightSubgroup μ)
    (invariantRightSubgroup (μ.map (fun x => rightAction x a))) a⁻¹ hc hV

/-- The tangent transport is an equivalence, not just an inclusion.
This is the exact relation needed for a change of frame. -/
lemma matrixVelocitySpace_map_rightAction_iff {n : ℕ}
    (μ : Measure (X n)) (a : G n)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    a⁻¹.val * V * a.val ∈
        matrixVelocitySpace (invariantRightSubgroup
          (μ.map (fun x => rightAction x a))) ↔
      V ∈ matrixVelocitySpace (invariantRightSubgroup μ) := by
  constructor
  · intro hV
    have h := matrixVelocitySpace_map_rightAction
      (μ.map (fun x => rightAction x a)) a⁻¹ hV
    have hmap : (μ.map (fun x => rightAction x a)).map
        (fun x => rightAction x a⁻¹) = μ := by
      simp only [map_rightAction_mul, mul_inv_cancel, rightAction_one, Measure.map_id']
    have ha : a.val * a⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hcancel : a.val * (a⁻¹.val * V * a.val) * a⁻¹.val = V := by
      calc
        _ = (a.val * a⁻¹.val) * V * (a.val * a⁻¹.val) := by simp only [Matrix.mul_assoc]
        _ = V := by rw [ha, Matrix.one_mul, Matrix.mul_one]
    simpa only [inv_inv, hmap, hcancel] using h
  · exact matrixVelocitySpace_map_rightAction μ a

/-- Normalizer covariance of the genuine conditional measures gives
covariance of their genuine curve-velocity subspaces. -/
theorem ae_component_velocity_covariance {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun x => rightAction x a) = μ) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
      ∀ V ∈ matrixVelocitySpace
        (invariantRightSubgroup (condExpKernel μ (actionInvariantSigma H (X n)) z)),
      a⁻¹.val * V * a.val ∈ matrixVelocitySpace
        (invariantRightSubgroup (condExpKernel μ (actionInvariantSigma H (X n))
          (rightAction z a))) := by
  filter_upwards [lattice_normalizer_component_covariance H a ha μ hμ] with z hz
  intro V hV
  rw [← hz]
  exact matrixVelocitySpace_map_rightAction _ a hV

theorem ae_component_velocity_covariance_iff {n : ℕ}
    (H : Subgroup (G n)) (a : G n)
    (ha : a ∈ Subgroup.normalizer (H : Set (G n)))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun x => rightAction x a) = μ) :
    ∀ᵐ z ∂μ.trim (actionInvariantSigma_le H (X n)),
      ∀ V : Matrix (Fin n) (Fin n) ℝ,
      a⁻¹.val * V * a.val ∈ matrixVelocitySpace
          (invariantRightSubgroup (condExpKernel μ (actionInvariantSigma H (X n))
            (rightAction z a))) ↔
        V ∈ matrixVelocitySpace
          (invariantRightSubgroup (condExpKernel μ (actionInvariantSigma H (X n)) z)) := by
  filter_upwards [lattice_normalizer_component_covariance H a ha μ hμ] with z hz
  intro V
  rw [← hz]
  exact matrixVelocitySpace_map_rightAction_iff _ a V

end DukePrimeDegree

end

end OAI
