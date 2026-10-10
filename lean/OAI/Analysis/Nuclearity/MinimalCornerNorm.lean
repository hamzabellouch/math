import OAI.Analysis.WeakInfiniteness.TensorSubalgebras
import OAI.Analysis.WeakInfiniteness.TensorFlipEquivalence
import OAI.Analysis.OperatorAlgebra.IsometricCornerNorm

namespace OAI

/-! Faithful corner inclusions preserve the minimal norm. Cutting both tensor
factors is a compression by one contractive elementary projection. -/
noncomputable section
open scoped TensorProduct
namespace WeakPureInfiniteness
universe u

section Inclusions
variable {A B C D : Type u}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma norm_minimalSum_flip {I : Type*} [Fintype I] (a : I → A) (b : I → B) :
    ‖∑ i, minimalElementary (a i) (b i)‖ =
      ‖∑ i, minimalElementary (b i) (a i)‖ := by
  change ‖(minimalTensorSubalgebra A B).subtype (∑ i, minimalElementary (a i) (b i))‖ =
    ‖(minimalTensorSubalgebra B A).subtype (∑ i, minimalElementary (b i) (a i))‖
  simp only [map_sum]
  exact norm_spatialSum_flip Finset.univ a b

lemma norm_minimalSum_mapLeft {I : Type*} [Fintype I]
    (φ : A →⋆ₙₐ[ℂ] C) (hφ : Function.Injective φ) (a : I → A) (b : I → B) :
    ‖∑ i, minimalElementary (φ (a i)) (b i)‖ =
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  have h := NonUnitalStarAlgHom.norm_map (minimalMapLeft (C := B) φ)
    (minimalMapLeft_injective φ hφ) (∑ i, minimalElementary (a i) (b i))
  simpa only [map_sum, minimalMapLeft_elementary] using h

lemma norm_minimalSum_mapBoth {I : Type*} [Fintype I]
    (φ : A →⋆ₙₐ[ℂ] C) (ψ : B →⋆ₙₐ[ℂ] D)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (a : I → A) (b : I → B) :
    ‖∑ i, minimalElementary (φ (a i)) (ψ (b i))‖ =
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  rw [norm_minimalSum_mapLeft φ hφ, norm_minimalSum_flip,
    norm_minimalSum_mapLeft ψ hψ, norm_minimalSum_flip]

end Inclusions

section Corners
variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def isometricCornerOppositeLift (V : K →ₗᵢ[ℂ] H) :
    (K →L[ℂ] K)ᵐᵒᵖ →⋆ₙₐ[ℂ] (H →L[ℂ] H)ᵐᵒᵖ where
  toFun a := MulOpposite.op (isometricCornerLift V a.unop)
  map_zero' := by
    change MulOpposite.op (isometricCornerLiftHom V 0) = 0
    rw [map_zero, MulOpposite.op_zero]
  map_add' a b := by
    change MulOpposite.op (isometricCornerLiftHom V (a.unop + b.unop)) = _
    rw [map_add, MulOpposite.op_add]
    rfl
  map_mul' a b := by
    change MulOpposite.op (isometricCornerLift V (b.unop * a.unop)) = _
    rw [isometricCornerLift_mul, MulOpposite.op_mul]
  map_smul' c a := by
    change MulOpposite.op (isometricCornerLiftHom V (c • a.unop)) = _
    rw [map_smul, MulOpposite.op_smul]
    rfl
  map_star' a := by
    change MulOpposite.op (isometricCornerLift V (star a.unop)) = _
    rw [isometricCornerLift_star]
    rfl

lemma isometricCornerOppositeLift_injective (V : K →ₗᵢ[ℂ] H) :
    Function.Injective (isometricCornerOppositeLift V) := by
  intro a b h
  apply MulOpposite.unop_injective
  apply isometricCornerLift_injective V
  exact congrArg MulOpposite.unop h

lemma norm_minimalSum_cornerLift (V : K →ₗᵢ[ℂ] H) {I : Type*} [Fintype I]
    (a b : I → K →L[ℂ] K) :
    ‖∑ i, minimalElementary (isometricCornerLift V (a i))
      (MulOpposite.op (isometricCornerLift V (b i)))‖ =
    ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ :=
  norm_minimalSum_mapBoth (isometricCornerLiftHom V) (isometricCornerOppositeLift V)
    (isometricCornerLift_injective V) (isometricCornerOppositeLift_injective V)
    a (fun i => MulOpposite.op (b i))

lemma norm_minimalSum_projection_cut {I : Type*} [Fintype I]
    (p : H →L[ℂ] H) (hp : ‖p‖ ≤ 1) (a b : I → H →L[ℂ] H) :
    ‖∑ i, minimalElementary (p * a i * p) (MulOpposite.op (p * b i * p))‖ ≤
      ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ := by
  let P := minimalElementary p (MulOpposite.op p)
  have hP : ‖P‖ ≤ 1 := by
    exact (norm_spatialElementary_le p (MulOpposite.op p)).trans
      (by simpa only [MulOpposite.norm_op, mul_one] using
        mul_le_mul hp hp (norm_nonneg _) zero_le_one)
  have he : (∑ i, minimalElementary (p * a i * p)
      (MulOpposite.op (p * b i * p))) =
      P * (∑ i, minimalElementary (a i) (MulOpposite.op (b i))) * P := by
    simp only [P, Finset.mul_sum, Finset.sum_mul, ← minimalElementary_mul,
      ← MulOpposite.op_mul, mul_assoc]
  rw [he]
  calc
    ‖P * (∑ i, minimalElementary (a i) (MulOpposite.op (b i))) * P‖ ≤
        ‖P‖ * ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ * ‖P‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ * 1 := by
      gcongr
    _ = _ := by rw [one_mul, mul_one]


end Corners
end WeakPureInfiniteness

end

end OAI
