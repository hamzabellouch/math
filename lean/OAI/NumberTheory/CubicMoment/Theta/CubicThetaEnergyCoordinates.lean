import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionDifferential

namespace OAI

/-! The intrinsic tangent energy equals the literal three-coordinate
Euclidean gradient. This connects the global form to the local density. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaTangentEnergy_coordinates (L : (ℂ × ℝ) →L[ℝ] ℂ) :
    cubicThetaTangentEnergy (L.comp cubicThetaTangentCoordinates.toContinuousLinearMap)=
      ‖L (1,0)‖^2+‖L (Complex.I,0)‖^2+‖L (0,1)‖^2 := by
  let bR : OrthonormalBasis Unit ℝ ℝ :=
    FiniteDimensional.orthonormalBasisSingleton Unit ℝ (Module.finrank_self ℝ) 1 (by simp)
  let b := Complex.orthonormalBasisOneI.prod bR
  rw [cubicThetaTangentEnergy,cubicThetaTangentEnergy_basis,
    ← cubicThetaTangentEnergy_basis b]
  simp only [b,OrthonormalBasis.prod_apply,Fintype.sum_sum_type,Function.comp_apply,
    Sum.elim_inl,Sum.elim_inr,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,cubicThetaTangentCoordinates,
    LinearMap.inl_apply,LinearMap.inr_apply]
  simp only [Fintype.sum_unique,bR,FiniteDimensional.orthonormalBasisSingleton_apply,
    Fin.sum_univ_succ,Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
  rfl

lemma cubicThetaSectionEnergy_coordinates (F : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy F p=p.val.2^2*
      (‖fderiv ℝ (cubicThetaSectionFunction F) p.val (1,0)‖^2+
       ‖fderiv ℝ (cubicThetaSectionFunction F) p.val (Complex.I,0)‖^2+
       ‖fderiv ℝ (cubicThetaSectionFunction F) p.val (0,1)‖^2) := by
  unfold cubicThetaSectionEnergy cubicThetaSectionDifferential
  rw [cubicThetaTangentEnergy_coordinates]

end CubicFirstMoment

end

end OAI
