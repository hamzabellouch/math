import OAI.Analysis.BoundedHochschild.NormalMultiplication
import OAI.Analysis.BoundedHochschild.PrimitiveAverages

namespace OAI

/-!
# Weak-star limits and the Hochschild differential

Separate weak-star continuity of multiplication, obtained from the predual,
lets the bounded Hochschild differential pass through pointwise weak-star
limits. No additional normality assumption on the cochains is required.
-/

noncomputable section

namespace BoundedHochschild

variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

/-- The differential preserves pointwise convergence against the predual. -/
theorem predual_tendsto_differential_of_predual
    {n : ℕ} {F : I → Cochain M n} {G : Cochain M n} {l : Filter I}
    (h : ∀ x, PredualTendsto e (fun i => F i x) l (G x))
    (x : Fin (n + 1) → M) :
    PredualTendsto e (fun i => differentialValue (F i) x) l (differentialValue G x) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact predual_tendsto_differential e (HochschildSakai.mul_hasPreadjoint e)
    (HochschildSakai.mul_right_hasPreadjoint e) h x

end BoundedHochschild

end

end OAI
