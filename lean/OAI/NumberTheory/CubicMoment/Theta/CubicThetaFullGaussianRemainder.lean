import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullGaussianLimit
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussianPowerBound

namespace OAI

/-! A bounded remainder after subtracting the exact leading heat term. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaFullGaussian_bounded_remainder {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℝ, 0<t → t≤1 →
      |cubicThetaFullGaussian p t-(4*Real.pi^2/243)/t^2|≤M := by
  let C := 4*Real.pi^2/243
  let a := 4*Real.pi^2*p.2/27
  let b := 4*Real.pi^2/(27*p.2)
  let A := cubicThetaGaussianPowerConstant/a^2
  let B := cubicThetaGaussianPowerConstant/b^2
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hA : 0≤A := div_nonneg cubicThetaGaussianPowerConstant_nonneg (sq_nonneg _)
  have hB : 0≤B := div_nonneg cubicThetaGaussianPowerConstant_nonneg (sq_nonneg _)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C*(A*(1+B)+B),by positivity,?_⟩
  intro t ht ht1
  have hT : cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t/p.2)))≤A*t^2 := by
    have h := cubicThetaLatticeGaussianTail_div_bound ha ht
    convert h using 1
    dsimp [a]
    congr 1
    field_simp
  have hU : cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*(t*p.2)))≤B*t^2 := by
    have h := cubicThetaLatticeGaussianTail_div_bound hb ht
    convert h using 1
    dsimp [b]
    congr 1
    ring
  have he := cubicThetaFullGaussian_error hp ht
  rw [cubicThetaScalarGaussian_lead_product hp ht] at he
  calc
    _ ≤ C/t^2*(A*t^2*(1+B*t^2)+B*t^2) := he.trans (by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hC (sq_nonneg t))
      exact add_le_add (mul_le_mul hT (add_le_add le_rfl hU)
        (by linarith [cubicThetaLatticeGaussianTail_nonneg (4*Real.pi^2/(27*(t*p.2)))]) (mul_nonneg hA (sq_nonneg t))) hU)
    _ = C*(A*(1+B*t^2)+B) := by field_simp [ht.ne']
    _ ≤ C*(A*(1+B)+B) := by
      have ht2 : t^2≤1 := by nlinarith
      have hbt : B*t^2≤B := by nlinarith [mul_nonneg hB (sub_nonneg.mpr ht2)]
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hbt) hA) le_rfl) hC

end CubicFirstMoment

end

end OAI
