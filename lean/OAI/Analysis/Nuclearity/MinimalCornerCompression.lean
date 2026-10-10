import OAI.Analysis.Nuclearity.MinimalCornerNorm
import OAI.Analysis.OperatorAlgebra.TracialSpatialMultiplication

namespace OAI

/-! Minimal tensor norms contract under simultaneous corner compression. -/
noncomputable section
open scoped TensorProduct
namespace WeakPureInfiniteness
open BoundedRecovery
universe u
variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_minimalSum_corner_compression (M : VonNeumannAlgebra K)
    (V : K →ₗᵢ[ℂ] H) (p : H →L[ℂ] H) (hp : ‖p‖ ≤ 1)
    {I : Type*} [Fintype I] (a b : I → H →L[ℂ] H)
    (ac bc : I → M.toStarSubalgebra)
    (ha : ∀ i, isometricCornerLift V (ac i).val = p * a i * p)
    (hb : ∀ i, isometricCornerLift V (bc i).val = p * b i * p) :
    ‖∑ i, minimalElementary (ac i) (MulOpposite.op (bc i))‖ ≤
      ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ := by
  have hinj : Function.Injective (subalgebraOppositeHom M.toStarSubalgebra) := by
    intro x y h
    apply MulOpposite.unop_injective
    apply Subtype.ext
    exact congrArg MulOpposite.unop h
  have he := norm_minimalSum_mapBoth
    M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom
    (subalgebraOppositeHom M.toStarSubalgebra).toNonUnitalStarAlgHom
    Subtype.val_injective hinj ac (fun i => MulOpposite.op (bc i))
  rw [← he]
  change ‖∑ i, minimalElementary (ac i).val (MulOpposite.op (bc i).val)‖ ≤ _
  rw [← norm_minimalSum_cornerLift V]
  simp only [ha, hb]
  exact norm_minimalSum_projection_cut p hp a b

end WeakPureInfiniteness

end

end OAI
