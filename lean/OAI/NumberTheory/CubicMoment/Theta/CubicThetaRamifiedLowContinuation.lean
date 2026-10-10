import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedDirichletCube
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFreeContinuation

namespace OAI

/-! Continue the literal three low ramified rows by the cubic
identity. Their value at the pole is kept as a residue difference. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedCubeFactor (s : ℂ) : ℂ := 27*(27:ℂ)^(-s)

lemma cubicThetaRamifiedCubeFactor_analytic (s : ℂ) :
    AnalyticAt ℂ cubicThetaRamifiedCubeFactor s := by
  let _ : NeZero (27:ℂ) := ⟨by norm_num⟩
  exact analyticAt_const.mul
    (((differentiable_const_cpow_of_neZero (27:ℂ)).analyticAt _).comp
      (f:=fun z : ℂ => -z) (x:=s) analyticAt_id.neg)

lemma cubicThetaRamifiedCubeFactor_pole :
    cubicThetaRamifiedCubeFactor (4/3)=(1/3:ℂ) := by
  unfold cubicThetaRamifiedCubeFactor
  have hp : (27:ℂ)^(-(4/3:ℂ))=(3:ℂ)^(-(4:ℂ)) := by
    rw [show (27:ℂ)=((3:ℕ):ℂ)^(3:ℕ) by norm_num,
      ← Complex.natCast_cpow_natCast_mul]
    congr 1
    norm_num
  rw [hp,Complex.cpow_neg,show (4:ℂ)=((4:ℕ):ℂ) by rfl,Complex.cpow_natCast]
  norm_num

def cubicThetaRegularizedRamifiedLow (h : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaRegularizedFrequency (lambdaE^3*h) s-
    cubicThetaRamifiedCubeFactor s*cubicThetaRegularizedFrequency h s

theorem cubicThetaRegularizedRamifiedLow_analytic {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedRamifiedLow h) {s : ℂ | 1<s.re} := by
  intro s hs
  exact (cubicThetaRegularizedFrequency_analytic
    (mul_ne_zero (pow_ne_zero 3 lambdaE_prime.ne_zero) hh) s hs).sub
      ((cubicThetaRamifiedCubeFactor_analytic s).mul
        (cubicThetaRegularizedFrequency_analytic hh s hs))

theorem cubicThetaRegularizedRamifiedLow_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedRamifiedLow h s=(s-4/3)*cubicThetaRamifiedLowDirichlet s h := by
  unfold cubicThetaRegularizedRamifiedLow cubicThetaRamifiedCubeFactor
  rw [cubicThetaRegularizedFrequency_right
    (mul_ne_zero (pow_ne_zero 3 lambdaE_prime.ne_zero) hh) hs,
    cubicThetaRegularizedFrequency_right hh hs,
    cubicThetaFrequencyDirichlet_ramified_cube (by linarith)]
  ring

theorem cubicThetaRegularizedRamifiedLow_pole {h : Eisenstein} (hh : h≠0) :
    cubicThetaRegularizedRamifiedLow h (4/3)=
      cubicThetaArithmeticFourierResidue (lambdaE^3*h) (4/3)-
        (1/3:ℂ)*cubicThetaArithmeticFourierResidue h (4/3) := by
  rw [cubicThetaRegularizedRamifiedLow,cubicThetaRegularizedFrequency_residue
    (mul_ne_zero (pow_ne_zero 3 lambdaE_prime.ne_zero) hh),
    cubicThetaRegularizedFrequency_residue hh,cubicThetaRamifiedCubeFactor_pole]

end CubicFirstMoment

end

end OAI
