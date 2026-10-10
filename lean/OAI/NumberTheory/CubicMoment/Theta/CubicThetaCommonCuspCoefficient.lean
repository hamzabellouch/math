import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspPeriodicity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNineCusp

namespace OAI

/-! The dual three-cusp coefficient before local cube cancellation.
All dependence on a coprime additive numerator is in its cubic character. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

def cubicThetaCommonCuspCoefficient (n : Eisenstein) : ℂ :=
  (∑ j : Fin 3,omega^j.val*star (cubicThetaActualCuspCoefficient (j.val:ℤ) (-n)))/3

theorem cubicThetaProjectedCoefficient_factor (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0)
    (hd : (3:Eisenstein)∣g 1 1) (n : Eisenstein) :
    cubicThetaProjectedCoefficient g hc n=
      star (cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc))*
        cubicThetaCommonCuspCoefficient n := by
  have ht (j : Fin 3) : cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j)=
      cubicThetaActualCuspCoefficient (j.val:ℤ) :=
    cubicThetaActualCuspCoefficient_periodic (cubicThetaProjectedCuspType_congr g hc ha j)
  unfold cubicThetaProjectedCoefficient cubicThetaCommonCuspCoefficient
  simp_rw [cubicThetaProjectedCuspMultiplier_constant g hc hd,ht]
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cubicThetaNineGaussMatrix_coefficient (r : Eisenstein) (hr : primary r)
    (u : Eisenstein) (hu : IsCoprime r u) (n : Eisenstein) :
    cubicThetaProjectedCoefficient (cubicThetaNineGaussMatrix r hr u hu)
      (cubicThetaNineGaussMatrix_primary r hr u hu) n=
      star (cubicSymbol r u)*cubicThetaCommonCuspCoefficient n := by
  let g := cubicThetaNineGaussMatrix r hr u hu
  have hc := cubicThetaNineGaussMatrix_primary r hr u hu
  have hd : (3:Eisenstein)∣g 1 1 :=
    dvd_trans (show (3:Eisenstein)∣9 from ⟨3,by norm_num⟩) (cubicThetaNineGaussMatrix_nine r hr u hu)
  have ha : (3:Eisenstein)∣g 0 0 := by
    rw [(cubicThetaNineGaussMatrix_entries r hr u hu).1]
    refine ⟨-lambdaE*u,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  rw [cubicThetaProjectedCoefficient_factor g hc ha hd]
  have he := cubicThetaProjectedCuspMultiplier_constant g hc hd (0:Fin 3)
  rw [cubicThetaNineGaussMatrix_multiplier] at he
  rw [←he]

lemma cubicThetaCommonCuspCoefficient_bound (n : Eisenstein) :
    ‖cubicThetaCommonCuspCoefficient n‖≤243 := by
  have he := cubicThetaProjectedCoefficient_factor cubicThetaFullInversion primary_one
    (dvd_zero 3) (dvd_zero 3) n
  have hv : cubicThetaKubotaValue
      (cubicThetaPrimaryBottomPrincipal cubicThetaFullInversion primary_one)=1 := by
    rw [cubicThetaPrimaryBottom_multiplier_adapted cubicThetaFullInversion primary_one
      (dvd_zero 3) (dvd_zero 3)]
    exact cubicSymbol_one_lower _
  rw [hv,star_one,one_mul] at he
  rw [←he]
  exact cubicThetaProjectedCoefficient_bound _ _ _

end CubicFirstMoment

end

end OAI
