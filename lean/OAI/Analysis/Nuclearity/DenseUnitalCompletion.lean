import OAI.Analysis.Nuclearity.BoundedStarCompletion

namespace OAI

/-! The image of the algebraic unit is the unit in a dense C*-completion. -/
noncomputable section
namespace WeakPureInfiniteness

variable {R E : Type*} [Ring R] [StarAddMonoid R] [Algebra ℂ R]
  [NonUnitalCStarAlgebra E]

lemma dense_unit_mul (f : R →⋆ₙₐ[ℂ] E) (hf : DenseRange f) (x : E) :
    f 1 * x = x := by
  refine hf.induction_on x (isClosed_eq (continuous_const.mul continuous_id) continuous_id) ?_
  intro r
  rw [← map_mul, one_mul]

lemma dense_mul_unit (f : R →⋆ₙₐ[ℂ] E) (hf : DenseRange f) (x : E) :
    x * f 1 = x := by
  refine hf.induction_on x (isClosed_eq (continuous_id.mul continuous_const) continuous_id) ?_
  intro r
  rw [← map_mul, mul_one]

abbrev denseUnitalCStarAlgebra (f : R →⋆ₙₐ[ℂ] E) (hf : DenseRange f) : CStarAlgebra E := by
  let _ : IsUnital E := ⟨⟨f 1, fun x => ⟨dense_unit_mul f hf x, dense_mul_unit f hf x⟩⟩⟩
  exact IsUnital.toCStarAlgebra

lemma denseUnitalCStarAlgebra_one (f : R →⋆ₙₐ[ℂ] E) (hf : DenseRange f) :
    letI := denseUnitalCStarAlgebra f hf
    f 1 = (1 : E) := by
  let := denseUnitalCStarAlgebra f hf
  simpa only [mul_one] using dense_unit_mul f hf (1 : E)

def denseUnitalHom (f : R →⋆ₙₐ[ℂ] E) (hf : DenseRange f) :
    letI := denseUnitalCStarAlgebra f hf
    R →⋆ₐ[ℂ] E := by
  letI := denseUnitalCStarAlgebra f hf
  exact { f with
    map_one' := denseUnitalCStarAlgebra_one f hf
    commutes' := fun c => by
      change f (algebraMap ℂ R c) = algebraMap ℂ E c
      rw [Algebra.algebraMap_eq_smul_one, map_smul, denseUnitalCStarAlgebra_one f hf,
        Algebra.algebraMap_eq_smul_one] }

end WeakPureInfiniteness

end

end OAI
