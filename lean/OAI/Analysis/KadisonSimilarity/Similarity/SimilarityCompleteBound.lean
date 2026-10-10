import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBounded

namespace OAI

/-! Actual matrix bounds for a similarity, used to identify the minimum
condition number with the complete norm. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def similarityRepresentation (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ) :
    BoundedUnitalHom A H := by
  refine ⟨{
    toFun := fun a => (S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H)
    map_one' := by simp
    map_mul' := by intro a b; simp [mul_assoc]
    map_zero' := by simp
    map_add' := by intro a b; simp [mul_add, add_mul]
    commutes' := ?_ }, ?_⟩
  · intro c
    simp [Algebra.algebraMap_eq_smul_one]
  · exact (continuous_const.mul π.2).mul continuous_const

@[simp] theorem similarityRepresentation_apply
    (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ) (a : A) :
    (similarityRepresentation π S).1 a =
      (S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H) := rfl

def similarityStarRepresentation (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ)
    (hS : ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))) :
    A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  { (similarityRepresentation π S).1 with map_star' := hS }

variable [PartialOrder A] [StarOrderedRing A]

theorem completeBound_conjugate_star (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (V W : H →L[ℂ] H) :
    CompleteBound (fun a => V * σ a * W) (‖V‖ * ‖W‖) := by
  intro n X
  have he : matrixOperator (X.map (fun a => V * σ a * W)) =
      amplify V n * matrixOperator (X.map σ) * amplify W n := by
    ext ξ i
    simp only [matrixOperator_apply, Matrix.map_apply, mul_apply_eq_comp, amplify_apply,
      map_sum]
  rw [he]
  calc
    _ ≤ (‖amplify V n‖ * ‖matrixOperator (X.map σ)‖) * ‖amplify W n‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖V‖ * (1 * ‖CStarMatrix.ofMatrix X‖)) * ‖W‖ := by
      gcongr
      · exact norm_amplify_le V n
      · exact completeBound_starHom σ n X
      · exact norm_amplify_le W n
    _ = _ := by ring

theorem completeBound_of_similarity (π : BoundedUnitalHom A H) (S : (H →L[ℂ] H)ˣ)
    (hS : ∀ a, (S : H →L[ℂ] H) * π.1 (star a) * (↑S⁻¹ : H →L[ℂ] H) =
      star ((S : H →L[ℂ] H) * π.1 a * (↑S⁻¹ : H →L[ℂ] H))) :
    CompleteBound π.1 (‖(S : H →L[ℂ] H)‖ * ‖(↑S⁻¹ : H →L[ℂ] H)‖) := by
  have h := completeBound_conjugate_star (similarityStarRepresentation π S hS)
    (↑S⁻¹ : H →L[ℂ] H) (S : H →L[ℂ] H)
  simpa only [similarityStarRepresentation, similarityRepresentation, AlgHom.coe_mk,
    StarAlgHom.coe_mk, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul,
    mul_one, mul_comm ‖(↑S⁻¹ : H →L[ℂ] H)‖] using h

end KadisonSimilarity

end

end OAI
