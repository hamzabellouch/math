import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ComplementScaleBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSobolev

namespace OAI

/-! Explicit polynomial bounds for the actual kinetic budget and the
coercive complement allowance in the manufactured Hubbard comparison. -/

noncomputable section
namespace ContinuumCoulomb

def manufacturedKineticBudgetConstant (freq rho : ℝ) : ℝ :=
  2*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2)+2

theorem manufacturedKineticBudgetConstant_positive {freq rho : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) : 0 < manufacturedKineticBudgetConstant freq rho := by
  have hW := PlanarSobolev.wellBound_nonnegative
  have hA : 0 ≤ (-1/2:ℝ)+freq/2 := by linarith
  unfold manufacturedKineticBudgetConstant
  positivity

theorem manufactured_kinetic_complement_budgets {freq rho γ M η ε : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (hγ : 0 < γ) (hγ1 : γ ≤ 1/4)
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hε : ε ≤ 1) :
    M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+2*M*ε ≤
      manufacturedKineticBudgetConstant freq rho*M^2 ∧
    (γ/(16*manufacturedKineticBudgetConstant freq rho))/M^2 ≤
      (γ/8)/(2*(M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+γ/8+1)) := by
  let A := 6*Real.pi*rho+((-1/2:ℝ)+freq/2)
  let C := manufacturedKineticBudgetConstant freq rho
  have hW := PlanarSobolev.wellBound_nonnegative
  have hA : 0 ≤ A := by
    have hE : 0 ≤ (-1/2:ℝ)+freq/2 := by linarith
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hrho) hE
  have hC : 0 < C := manufacturedKineticBudgetConstant_positive hf hrho
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hT : M*((M+η)*PlanarSobolev.wellBound+A) ≤ (2*PlanarSobolev.wellBound+A)*M^2 := by
    have hsum : M+η ≤ 2*M := by linarith
    have hterm := add_le_add (mul_le_mul_of_nonneg_right hsum hW)
      (le_mul_of_one_le_right hA hM)
    have h := mul_le_mul_of_nonneg_left hterm hM0.le
    convert h using 1
    ring
  have hK : 2*M*ε ≤ 2*M^2 := by
    have h := mul_le_mul_of_nonneg_left hε (show 0 ≤ 2*M by positivity)
    nlinarith [sq_nonneg (M-1)]
  have hγb : γ/8+1 ≤ 2*M^2 := by nlinarith [sq_nonneg (M-1)]
  have hden : 2*(M*((M+η)*PlanarSobolev.wellBound+A)+γ/8+1) ≤ 2*C*M^2 := by
    dsimp only [C,manufacturedKineticBudgetConstant,A] at *
    nlinarith only [hT,hγb]
  have hden0 : 0 < 2*(M*((M+η)*PlanarSobolev.wellBound+A)+γ/8+1) := by positivity
  constructor
  · dsimp only [manufacturedKineticBudgetConstant]
    dsimp only [A] at hT
    nlinarith only [hT,hK]
  · have hfinal : (γ/(16*C))/M^2 ≤ (γ/8)/(2*(M*((M+η)*PlanarSobolev.wellBound+A)+γ/8+1)) := by
      calc
        _ = (γ/8)/(2*C*M^2) := by field_simp; norm_num
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden0 hden
    convert hfinal using 1
    dsimp [A,C]
    ring

end ContinuumCoulomb

end

end OAI
