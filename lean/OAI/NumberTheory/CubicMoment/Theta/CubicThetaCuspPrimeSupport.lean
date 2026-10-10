import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticCubeScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticPrimeSupport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCoefficients

namespace OAI

/-! The same unramified support and cube scaling hold for the two
auxiliary arithmetic families in DR (5.13)--(5.14). -/
noncomputable section
namespace CubicFirstMoment

lemma CubicThetaCoordinates.cuspCoefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) (j : Fin 3) :
    (R.mulPrimaryCube e he).cuspCoefficient j=(norm e:ℂ)⁻¹*R.cuspCoefficient j := by
  unfold cuspCoefficient
  rw [R.coefficient_mulPrimaryCube,R.amplitude_mulPrimaryCube]
  dsimp only [mulPrimaryCube]
  push_cast
  split_ifs <;> ring

theorem cubicThetaCuspCoefficient_mulPrimaryCube {n : Eisenstein}
    (R : CubicThetaCoordinates n) (e : Eisenstein) (he : primary e) (j : Fin 3) :
    cubicThetaCuspCoefficient j (n*e^3)=(norm e:ℂ)⁻¹*cubicThetaCuspCoefficient j n := by
  rw [cubicThetaCuspCoefficient_formula (R.mulPrimaryCube e he),
    cubicThetaCuspCoefficient_formula R,R.cuspCoefficient_mulPrimaryCube]

theorem cubicThetaCuspCoefficient_prime_square {p n : Eisenstein}
    (hp : primaryPrime p) (hn : ¬p ∣ n) (j : Fin 3) :
    cubicThetaCuspCoefficient j (p^2*n)=0 := by
  rw [cubicThetaCuspCoefficient,dite_eq_right (cubicThetaCoordinates_not_square hp hn)]

end CubicFirstMoment

end

end OAI
