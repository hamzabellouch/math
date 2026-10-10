import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNineCusp
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSelectedGaussSum

namespace OAI

/-! A concrete rational-cusp lift on every residue. Nonunit residues get
an arbitrary determinant-one lift, and their cubic character weight is zero. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaProjectedCoefficient_congr {g h : SL(2,Eisenstein)} (he : g=h)
    (hg : primary (g 1 0)) (hh : primary (h 1 0)) :
    cubicThetaProjectedCoefficient g hg = cubicThetaProjectedCoefficient h hh := by
  subst h
  rfl

def cubicThetaResidueCuspMatrix (r : Eisenstein) (hr : primary r) (u : Eisenstein) :
    SL(2,Eisenstein) :=
  if hu : IsCoprime r u then cubicThetaNineGaussMatrix r hr u hu
  else cubicThetaPrimitiveMatrix r 1 isCoprime_one_right

lemma cubicThetaResidueCuspMatrix_of_coprime (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaResidueCuspMatrix r hr u = cubicThetaNineGaussMatrix r hr u hu := by
  exact dite_eq_left hu

lemma cubicThetaResidueCuspMatrix_bottom (r : Eisenstein) (hr : primary r) (u : Eisenstein) :
    cubicThetaResidueCuspMatrix r hr u 1 0=r := by
  unfold cubicThetaResidueCuspMatrix
  split_ifs with hu
  · exact (cubicThetaNineGaussMatrix_entries r hr u hu).2.1
  · rfl

theorem cubicThetaResidueCuspPrimary (r : Eisenstein) (hr : primary r) (u : Eisenstein) :
    primary (cubicThetaResidueCuspMatrix r hr u 1 0) := by
  rw [cubicThetaResidueCuspMatrix_bottom]
  exact hr

lemma cubicThetaResidueCuspMatrix_cusp (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) :
    cubicThetaPrimaryCuspCenter (cubicThetaResidueCuspMatrix r hr u)=
      (traceLambda^3*(u:ℂ))/(r:ℂ) := by
  rw [cubicThetaResidueCuspMatrix,dite_eq_left hu]
  unfold cubicThetaPrimaryCuspCenter
  rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1,
    (cubicThetaNineGaussMatrix_entries r hr u hu).2.1,
    Subalgebra.coe_mul,Subalgebra.coe_pow,lambdaE_coe]

lemma cubicThetaResidueCuspMatrix_weighted (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (rev : Bool) (k : ℕ) (W : ℝ→ℂ) (Z : ℝ) :
    cubicSymbol r u*cubicThetaSelectedAdditiveSum (cubicThetaResidueCuspMatrix r hr u) rev k W Z=
      cubicSymbol r u*cubicThetaSelectedSmoothSum (cubicThetaCircleOrder (!rev) k)
        ((traceLambda^3*(u:ℂ))/(r:ℂ)) W Z := by
  by_cases hu : IsCoprime r u
  · rw [cubicThetaSelectedAdditiveSum_eq,cubicThetaResidueCuspMatrix_cusp r hr u hu]
  · rw [cubicSymbol_eq_zero_of_not_isCoprime hr hu,zero_mul,zero_mul]

end CubicFirstMoment

end

end OAI
