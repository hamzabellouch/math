import Mathlib
import OAI.Probability.LogConcave.Sampling.SkewCenteringField
import OAI.Probability.LogConcave.Sampling.AdjointCoordinateProductLeft

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace
open TensorEnergy

lemma inner_basis_coordinate {d : ℕ} (y : Point d) (i : Fin d) :
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) y=y i := by
  simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]

theorem jointSkew_field {d : ℕ} {H : Point d → ℝ}
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hH : Differentiable ℝ H)
    (hK : ∀i j,Differentiable ℝ (fun y => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K y (EuclideanSpace.basisFun (Fin d) ℝ j))))
    (hstein : ∀u : Point d,tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (K y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (m y))
    (s : ℝ) (y : Point (d+d)) :
    productPointEquiv d d (skewLieField (productPotential H (fun z : Point d => ‖z‖^2/2))
      (jointSkew K s) y)=skewCenteringField K m s (productPointEquiv d d y) := by
  let L := coordinateProjection (leftCoordinates d d)
  have hf (i j : Fin d) : Differentiable ℝ (fun z => inner ℝ
      (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K (productPointEquiv d d z).1 (EuclideanSpace.basisFun (Fin d) ℝ j))) :=
    (hK i j).comp L.differentiable
  have hG := (gaussianPotential_polySmooth d).smooth.differentiable (by simp)
  apply Prod.ext
  · ext z
    change skewLieField _ _ y (z.castAdd d)=(-s⁻¹ • (K (productPointEquiv d d y).1).adjoint
      (productPointEquiv d d y).2) z
    rw [skewLieField_coordinate,Fin.sum_univ_add]
    simp only [jointSkew,Sum.elim_inl,Sum.elim_inr,jointSkewEntry_LL,jointSkewEntry_RL,
      adjointCoordinate_zero,Finset.sum_const_zero,zero_add]
    simp_rw [adjointCoordinate_const_mul (hf _ _)]
    simp_rw [adjointCoordinate_product_right hH hG (hK _ _),directional_gaussianPotential]
    rw [←Finset.mul_sum]
    change (-s⁻¹)*(∑i : Fin d,inner ℝ (productPointEquiv d d y).2
      (EuclideanSpace.basisFun (Fin d) ℝ i)*inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (K (productPointEquiv d d y).1 (EuclideanSpace.basisFun (Fin d) ℝ z)))=
      (-s⁻¹)*((K (productPointEquiv d d y).1).adjoint (productPointEquiv d d y).2) z
    congr 1
    rw [←inner_basis_coordinate,ContinuousLinearMap.adjoint_inner_right]
    simp_rw [real_inner_comm (productPointEquiv d d y).2,inner_basis_coordinate]
    rw [real_inner_comm,PiLp.inner_apply]
    simp only [RCLike.inner_apply,conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm,inner_basis_coordinate]
  · ext z
    change skewLieField _ _ y (z.natAdd d)=(s⁻¹ • m (productPointEquiv d d y).1) z
    rw [skewLieField_coordinate,Fin.sum_univ_add]
    simp only [jointSkew,Sum.elim_inl,Sum.elim_inr,jointSkewEntry_RR,jointSkewEntry_LR,
      adjointCoordinate_zero,Finset.sum_const_zero,add_zero]
    simp_rw [adjointCoordinate_const_mul (hf _ _)]
    simp_rw [adjointCoordinate_product_left hH hG (hK _ _)]
    rw [←Finset.mul_sum]
    change s⁻¹*tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i w => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ z)
        (K w (EuclideanSpace.basisFun (Fin d) ℝ i))) (productPointEquiv d d y).1=_
    rw [hstein]
    dsimp only
    rw [inner_basis_coordinate]
    rfl
end LogConcaveSampling

end

end

end

end OAI
