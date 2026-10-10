import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelFactorization
import OAI.NumberTheory.Ostmann.QuadraticCenter.MomentWeight

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def signedJacobiAverage (P : Finset ℕ) (ε : ℕ → ℤ) (u : ℤ) : ℝ :=
  (∑ p ∈ P,((ε p*jacobiSym u p:ℤ):ℝ))/P.card

theorem signedJacobiAverage_eq_oriented (P : Finset ℕ) (ε : ℕ → ℤ) (u : ℤ) :
    signedJacobiAverage P ε u = orientedQuadraticAverage P ε (fun _ => 0) u := by
  simp only [signedJacobiAverage,orientedQuadraticAverage,sub_zero]

theorem abs_signedJacobiAverage_le_one (P : Finset ℕ) (hP : 0 < P.card)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P,ε p = -1 ∨ ε p = 1) (u : ℤ) :
    |signedJacobiAverage P ε u| ≤ 1 := by
  rw [signedJacobiAverage_eq_oriented]
  exact abs_orientedQuadraticAverage_le_one P hP ε _ hε u

theorem kernelFactorization_jacobi_eq {z : ℤ} (F : KernelFactorization z)
    {p : ℕ} (hp : Nat.Prime p) (hpt : ¬p ∣ F.squareFactor) :
    jacobiSym z p = jacobiSym F.kernel p := by
  have hc : F.squareFactor.Coprime p := ((hp.coprime_iff_not_dvd).mpr hpt).symm
  have hg : Int.gcd (F.squareFactor:ℤ) p = 1 := by simpa using hc
  calc
    jacobiSym z p = jacobiSym (F.kernel*(F.squareFactor:ℤ)^2) p :=
      congrArg (fun u => jacobiSym u p) F.factorization
    _ = _ := by rw [jacobiSym.mul_left,jacobiSym.sq_one' hg,mul_one]

end Ostmann.QuadraticCenter

end

end OAI
