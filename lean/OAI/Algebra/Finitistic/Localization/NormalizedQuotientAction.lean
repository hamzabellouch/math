import OAI.Algebra.Finitistic.Localization.QuotientRelations

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

lemma quotient_arrow12 (h : Fin d) :
    arrowQ12 P h.succ = inv (arrowQ01 P 0) ≫ arrowQ01 P h.succ ≫ arrowQ12 P 0 := by
  have h := congrArg (fun f => inv (arrowQ01 P 0) ≫ f) (quotient_commutation P h)
  simpa using h

/-- Divide each homogenized path by s's on the target side. -/
def normalizePath : (vertexQ P 0 ⟶ vertexQ P 2) →ₗ[k] End (vertexQ P 0) where
  toFun f := f ≫ inv (arrowQ12 P 0) ≫ inv (arrowQ01 P 0)
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' c f := by simp [Linear.smul_comp]

lemma normalizePath_quadratic (h l : Fin d) :
    normalizePath P (arrowQ01 P l.succ ≫ arrowQ12 P h.succ) =
      normalizedGenerator P h * normalizedGenerator P l := by
  change (arrowQ01 P l.succ ≫ arrowQ12 P h.succ) ≫ inv (arrowQ12 P 0) ≫ inv (arrowQ01 P 0) =
    (arrowQ01 P l.succ ≫ inv (arrowQ01 P 0)) ≫ (arrowQ01 P h.succ ≫ inv (arrowQ01 P 0))
  rw [quotient_arrow12]
  simp [Category.assoc]

lemma normalizePath_linear (h : Fin d) :
    normalizePath P (arrowQ01 P h.succ ≫ arrowQ12 P 0) = normalizedGenerator P h := by
  change (arrowQ01 P h.succ ≫ arrowQ12 P 0) ≫ inv (arrowQ12 P 0) ≫ inv (arrowQ01 P 0) = _
  simp [Category.assoc,normalizedGenerator]

lemma normalizePath_constant :
    normalizePath P (arrowQ01 P 0 ≫ arrowQ12 P 0) = (1 : End (vertexQ P 0)) := by
  change (arrowQ01 P 0 ≫ arrowQ12 P 0) ≫ inv (arrowQ12 P 0) ≫ inv (arrowQ01 P 0) = 𝟙 _
  simp [Category.assoc]

/-- The original, inhomogeneous relations hold on L in the actual quotient. -/
theorem normalizedGenerator_satisfies : P.Satisfies (normalizedGenerator P) := by
  intro j
  have h := congrArg (normalizePath P) (quotient_homogenized P j)
  simpa only [map_add,map_sum,map_smul,map_zero,normalizePath_quadratic,
    normalizePath_linear,normalizePath_constant] using h
end LittleFinitistic.QuadraticEncoding

end

end OAI
