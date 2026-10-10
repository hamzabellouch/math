import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCoefficientScaling

namespace OAI

/-! Removal of a ramified cube preserves arithmetic support. This
extends the coordinate scaling to the literal zero-extended coefficient. -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.ramified_emultiplicity {n : Eisenstein} (R : CubicThetaCoordinates n) :
    emultiplicity lambdaE n=R.order := by
  have hp : primary (R.cubePart^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary)
  have he := congrArg (emultiplicity lambdaE) R.numerator_eq
  simpa only [emultiplicity_mul lambdaE_prime,emultiplicity_pow_self_of_prime lambdaE_prime,
    unit_lambda_emultiplicity,primary_lambda_emultiplicity R.squarefree_primary,
    primary_lambda_emultiplicity hp,zero_add,add_zero] using he

lemma CubicThetaCoordinates.order_pos {n : Eisenstein} (R : CubicThetaCoordinates n)
    (hn : lambdaE∣n) : 0<R.order := by
  have hp := dvd_iff_emultiplicity_pos.mpr hn
  rw [R.ramified_emultiplicity] at hp
  exact_mod_cast hp

lemma CubicThetaCoordinates.cube_order {n : Eisenstein} (R : CubicThetaCoordinates (lambdaE^3*n)) :
    3≤R.order := by
  have hm : (3:ℕ∞)≤emultiplicity lambdaE (lambdaE^3*n) :=
    pow_dvd_iff_le_emultiplicity.mp ⟨n,rfl⟩
  rw [R.ramified_emultiplicity] at hm
  exact_mod_cast hm

def CubicThetaCoordinates.removeLambdaCube {n : Eisenstein}
    (R : CubicThetaCoordinates (lambdaE^3*n)) : CubicThetaCoordinates n where
  unit := R.unit
  order := R.order-3
  squarefreePart := R.squarefreePart
  cubePart := R.cubePart
  squarefree_primary := R.squarefree_primary
  cube_primary := R.cube_primary
  squarefree := R.squarefree
  numerator_eq := by
    apply mul_left_cancel₀ (pow_ne_zero 3 lambdaE_prime.ne_zero)
    have hp : lambdaE^R.order=lambdaE^3*lambdaE^(R.order-3) := by
      rw [←pow_add,Nat.add_sub_of_le R.cube_order]
    calc
      _ = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hp]; ring

theorem cubicThetaCoordinates_lambdaCube_iff (n : Eisenstein) :
    Nonempty (CubicThetaCoordinates (lambdaE^3*n)) ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.removeLambdaCube⟩
  · rintro ⟨R⟩
    exact ⟨R.mulLambdaCube⟩

theorem cubicThetaArithmeticCoefficient_lambdaCube {n : Eisenstein} (hn : lambdaE∣n) :
    cubicThetaArithmeticCoefficient (lambdaE^3*n)=(1/3:ℂ)*cubicThetaArithmeticCoefficient n := by
  classical
  by_cases hR : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice hR
    rw [cubicThetaArithmeticCoefficient_formula R.mulLambdaCube,
      cubicThetaArithmeticCoefficient_formula R,R.coefficient_mulLambdaCube (R.order_pos hn)]
  · have hC := mt (cubicThetaCoordinates_lambdaCube_iff n).mp hR
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hR,dite_eq_right hC,mul_zero]

theorem cubicThetaCoefficientAgreement_lambdaCube_iff {h : Eisenstein} (hh : h≠0) :
    (cubicThetaNormalizedObservedCoefficient (lambdaE^3*h)=
      cubicThetaArithmeticCoefficient (-lambdaE*(lambdaE^3*h))) ↔
    cubicThetaNormalizedObservedCoefficient h=cubicThetaArithmeticCoefficient (-lambdaE*h) := by
  rw [cubicThetaNormalizedObservedCoefficient_lambda_cube hh,
    show -lambdaE*(lambdaE^3*h)=lambdaE^3*(-lambdaE*h) by ring,
    cubicThetaArithmeticCoefficient_lambdaCube (show lambdaE∣-lambdaE*h from ⟨-h,by ring⟩)]
  exact mul_right_inj' (by norm_num : (1/3:ℂ)≠0)

end CubicFirstMoment

end

end OAI
