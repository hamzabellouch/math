import OAI.Analysis.KadisonSimilarity.Representation.ConcretePredual
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

/-! Isometric duality between the concrete vector predual and the original
von Neumann algebra. The conjugate-linear convention agrees with the
predual interface used by the finite normal trace construction. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

def predualEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ (ConcretePredual M) :=
  LinearMap.mkContinuous
    { toFun := fun φ => (φ : StrongDual ℂ M.toStarSubalgebra) a
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    ‖a‖ (fun φ => by
      exact (φ : StrongDual ℂ M.toStarSubalgebra).le_opNorm a |>.trans_eq (mul_comm _ _))

@[simp] theorem predualEvaluation_apply (a : M.toStarSubalgebra) (φ : ConcretePredual M) :
    predualEvaluation M a φ = (φ : StrongDual ℂ M.toStarSubalgebra) a := rfl

theorem predualEvaluation_norm (a : M.toStarSubalgebra) :
    ‖predualEvaluation M a‖ = ‖a‖ := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  · change ‖(a : H →L[ℂ] H)‖ ≤ ‖predualEvaluation M a‖
    apply norm_le_of_matrix_coefficients _ (norm_nonneg _)
    intro x y
    calc
      ‖inner ℂ y ((a : H →L[ℂ] H) x)‖ =
          ‖predualEvaluation M a (predualCoefficient M x y)‖ := rfl
      _ ≤ ‖predualEvaluation M a‖ * ‖predualCoefficient M x y‖ :=
        (predualEvaluation M a).le_opNorm _
      _ ≤ ‖predualEvaluation M a‖ * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (predualCoefficient_norm_le M x y) (norm_nonneg _)
      _ = _ := by ring

/-- Vector coefficients determine every continuous functional on the predual. -/
theorem predual_ext (F G : StrongDual ℂ (ConcretePredual M))
    (h : ∀ x y, F (predualCoefficient M x y) = G (predualCoefficient M x y)) : F = G := by
  obtain ⟨f, hf, _⟩ := exists_extension_norm_eq (normalFunctionalSpace M).toSubmodule F
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (normalFunctionalSpace M).toSubmodule G
  have hspan : Submodule.span ℂ (Set.range fun xy : H × H => normalCoefficient M xy.1 xy.2) ≤
      (f - g).ker := by
    apply Submodule.span_le.mpr
    rintro φ ⟨⟨x, y⟩, rfl⟩
    change f (normalCoefficient M x y) - g (normalCoefficient M x y) = 0
    exact sub_eq_zero.mpr ((hf (predualCoefficient M x y)).trans
      ((h x y).trans (hg (predualCoefficient M x y)).symm))
  have hc := closure_minimal hspan (f - g).isClosed_ker
  apply ContinuousLinearMap.ext
  intro φ
  have hz := hc φ.property
  change f (φ : StrongDual ℂ M.toStarSubalgebra) -
    g (φ : StrongDual ℂ M.toStarSubalgebra) = 0 at hz
  exact (hf φ).symm.trans ((sub_eq_zero.mp hz).trans (hg φ))

theorem predualEvaluation_surjective : Function.Surjective (predualEvaluation M) := by
  intro F
  refine ⟨⟨operatorOfPredual M F, operatorOfPredual_mem M F⟩, ?_⟩
  apply predual_ext M
  intro x y
  exact operatorOfPredual_coefficient M F x y

def predualEvaluationIsometry : M.toStarSubalgebra →ₗᵢ[ℂ] StrongDual ℂ (ConcretePredual M) where
  toFun := predualEvaluation M
  map_add' := by
    intro a b
    ext φ
    exact (φ : StrongDual ℂ M.toStarSubalgebra).map_add a b
  map_smul' := by
    intro c a
    ext φ
    exact (φ : StrongDual ℂ M.toStarSubalgebra).map_smul c a
  norm_map' := predualEvaluation_norm M

def concretePredualLinearEquiv : StrongDual ℂ (ConcretePredual M) ≃ₗᵢ[ℂ] M.toStarSubalgebra :=
  (LinearIsometryEquiv.ofSurjective (predualEvaluationIsometry M)
    (predualEvaluation_surjective M)).symm

/-- The given concrete algebra is the conjugate dual of an actual Banach space. -/
def concretePredualEquiv : StrongDual ℂ (ConcretePredual M) ≃ₗᵢ⋆[ℂ] M.toStarSubalgebra :=
  (concretePredualLinearEquiv M).trans (starₗᵢ ℂ)

@[simp] theorem concretePredualEquiv_symm_apply (a : M.toStarSubalgebra)
    (φ : ConcretePredual M) :
    (concretePredualEquiv M).symm a φ = (φ : StrongDual ℂ M.toStarSubalgebra) (star a) := rfl

end KadisonSimilarity

end

end OAI
