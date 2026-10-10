import OAI.Analysis.OperatorAlgebra.HilbertTensorExtension
import OAI.Analysis.OperatorAlgebra.TracialSpatialMultiplication

namespace OAI

/-! Restricting an ambient operator tensor bound to a closed star subalgebra. -/
noncomputable section
namespace WeakPureInfiniteness
lemma minimalSum_map_bound {A B C D : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (φ : A →⋆ₙₐ[ℂ] C) (ψ : B →⋆ₙₐ[ℂ] D)
    {I : Type*} [Fintype I] (a : I → A) (b : I → B)
    (c : I → C) (d : I → D)
    (hc : ∀ i, φ (a i) = c i) (hd : ∀ i, ψ (b i) = d i) :
    ‖∑ i, minimalElementary (c i) (d i)‖ ≤
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  have h := minimalSum_map_norm_le φ ψ a b
  simpa only [hc, hd] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def subalgebraInclusionNonUnital (M : VonNeumannAlgebra H) :
    M.toStarSubalgebra →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun a := a.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def subalgebraOppositeInclusionNonUnital (M : VonNeumannAlgebra H) :
    M.toStarSubalgebraᵐᵒᵖ →⋆ₙₐ[ℂ] (H →L[ℂ] H)ᵐᵒᵖ where
  toFun b := MulOpposite.op b.unop.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma subalgebra_minimalSum_norm_le (M : VonNeumannAlgebra H)
    {I : Type*} [Fintype I] (a : I → M.toStarSubalgebra)
    (b : I → M.toStarSubalgebraᵐᵒᵖ) :
    ‖∑ i, minimalElementary (a i).val (MulOpposite.op (b i).unop.val)‖ ≤
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  exact minimalSum_map_bound (subalgebraInclusionNonUnital M)
    (subalgebraOppositeInclusionNonUnital M) a b
    (fun i => (a i).val) (fun i => MulOpposite.op (b i).unop.val)
    (fun _ => rfl) (fun _ => rfl)

end WeakPureInfiniteness

end

end OAI
