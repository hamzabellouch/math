import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # Finite height groups and bounds under a change of normed coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ W]

def heightConjugation (e : V ≃ₗ[ℝ] W) : (V ≃ₗ[ℝ] V) →* (W ≃ₗ[ℝ] W) where
  toFun A := e.symm.trans (A.trans e)
  map_one' := by ext w; simp
  map_mul' A B := by ext w; simp

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem finite_heightConjugation (e : V ≃ₗ[ℝ] W) (D : Subgroup (V ≃ₗ[ℝ] V))
    [Finite D] : Set.Finite (D.map (heightConjugation e) : Set (W ≃ₗ[ℝ] W)) := by
  apply (Set.finite_range (fun A : D => heightConjugation e A.val)).subset
  rintro A ⟨B, hB, rfl⟩
  exact ⟨⟨B, hB⟩, rfl⟩

omit [FiniteDimensional ℝ W] in
theorem norm_height_difference_le (e : V ≃ₗ[ℝ] W)
    (x y z : V) (A : V ≃ₗ[ℝ] V) {B : ℝ}
    (h : ‖x - (y + A z)‖ ≤ B) :
    ‖e x - (e y + heightConjugation e A (e z))‖ ≤
      ‖e.toContinuousLinearEquiv.toContinuousLinearMap‖ * B := by
  have heq : e x - (e y + heightConjugation e A (e z)) = e (x - (y + A z)) := by
    simp [heightConjugation]
  rw [heq]
  exact (e.toContinuousLinearEquiv.toContinuousLinearMap.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left h (norm_nonneg _))

end PolycyclicRecognition

end

end OAI
