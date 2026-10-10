import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E] [NormedSpace ℝ E]
    [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- Real or imaginary projection of a complex first derivative. -/
def projectD (p : ℂ →L[ℝ] ℝ) : (E →L[ℂ] ℂ) →L[ℝ] (E →L[ℝ] ℝ) :=
  (compL ℝ E ℂ ℝ p).comp (restrictScalarsL ℂ E ℂ ℝ ℝ)

/-- Explicit restriction in both arguments of a nested complex derivative. -/
def projectD2 (p : ℂ →L[ℝ] ℝ) (B : E →L[ℂ] (E →L[ℂ] ℂ)) :
    E →L[ℝ] (E →L[ℝ] ℝ) := (projectD p).comp (B.restrictScalars ℝ)

lemma hasFDerivAt_project {f : E → ℂ} {A : E →L[ℂ] ℂ} {x : E}
    (hf : HasFDerivAt f A x) (p : ℂ →L[ℝ] ℝ) :
    HasFDerivAt (fun y => p (f y)) (projectD p A) x :=
  p.hasFDerivAt.comp x (hf.restrictScalars ℝ)

lemma hasFDerivAt_projectD {a : E → (E →L[ℂ] ℂ)}
    {B : E →L[ℂ] (E →L[ℂ] ℂ)} {x : E}
    (ha : HasFDerivAt a B x) (p : ℂ →L[ℝ] ℝ) :
    HasFDerivAt (fun y => projectD p (a y)) (projectD2 p B) x :=
  (projectD p).hasFDerivAt.comp x (ha.restrictScalars ℝ)

/-- The square and its first two derivatives, with the second derivative
as an iterated continuous real linear map. -/
def squareD (v : ℝ) (A : E →L[ℝ] ℝ) := (2*v) • A

def squareD2 (v : ℝ) (A : E →L[ℝ] ℝ) (B : E →L[ℝ] (E →L[ℝ] ℝ)) :=
  (2*v) • B + ((2 : ℝ) • A).smulRight A

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma hasFDerivAt_square [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℝ} {a : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f a x) : HasFDerivAt (fun y => (f y)^2) (squareD (f x) a) x := by
  simpa only [squareD, pow_two, two_mul, add_smul, Pi.mul_apply] using hf.fun_mul hf

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma hasFDerivAt_squareD [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℝ} {a : E → (E →L[ℝ] ℝ)}
    {b : E →L[ℝ] (E →L[ℝ] ℝ)} {x : E}
    (hf : HasFDerivAt f (a x) x) (ha : HasFDerivAt a b x) :
    HasFDerivAt (fun y => squareD (f y) (a y)) (squareD2 (f x) (a x) b) x := by
  simpa only [squareD, squareD2, Pi.smul_apply] using (hf.const_mul 2).fun_smul ha

end
end SymmetricMahler

end OAI
