import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLinearFlow
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CanonicalNilpotentLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateLieBrackets
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieWordDerivative
import Mathlib.Algebra.Lie.Derivation.Basic

namespace OAI

/-! # The logarithm of a unipotent Lie automorphism is a derivation

Integer iterates preserve the bracket. Polynomiality extends that identity to
the real flow; its derivative at zero is the derivation identity.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance unipotentLogRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

theorem nilpotentLinearFlow_preserves_lie
    (A : L ≃ₗ⁅ℝ⁆ L) (D : Module.End ℝ L) (hD : IsNilpotent D)
    (hExp : IsNilpotent.exp D = A.toLinearMap) (t : ℝ) (x y : L) :
    nilpotentLinearFlow D t ⁅x, y⁆ = ⁅nilpotentLinearFlow D t x, nilpotentLinearFlow D t y⁆ := by
  let b := Module.finBasis ℝ L
  have hB (u v : L) : basisBracketLinear b (b.equivFun u) (b.equivFun v) =
      b.equivFun ⁅u, v⁆ := by
    change b.equivFun ⁅b.equivFun.symm (b.equivFun u), b.equivFun.symm (b.equivFun v)⁆ = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hl := coordinatePolynomial_nilpotentLinearFlow b D hD ⁅x, y⁆
  have hr := IsCoordinatePolynomial.bilinear (basisBracketLinear b)
    (coordinatePolynomial_nilpotentLinearFlow b D hD x)
    (coordinatePolynomial_nilpotentLinearFlow b D hD y)
  have hp (n : ℕ) (u v : L) :
      (A.toLinearMap ^ n) ⁅u, v⁆ = ⁅(A.toLinearMap ^ n) u, (A.toLinearMap ^ n) v⁆ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change A ⁅(A.toLinearMap ^ n) u, (A.toLinearMap ^ n) v⁆ =
        ⁅A ((A.toLinearMap ^ n) u), A ((A.toLinearMap ^ n) v)⁆
      exact A.map_lie _ _
  have he := hl.ext_nat_grid hr (by
    intro z
    change b.equivFun (nilpotentLinearFlow D (z 0 : ℝ) ⁅x, y⁆) =
      basisBracketLinear b (b.equivFun (nilpotentLinearFlow D (z 0 : ℝ) x))
        (b.equivFun (nilpotentLinearFlow D (z 0 : ℝ) y))
    rw [hB]
    simp only [nilpotentLinearFlow_nat D hD, hExp]
    exact congrArg b.equivFun (hp (z 0) x y))
  have ht := congrFun he (fun _ : Fin 1 => t)
  apply b.equivFun.injective
  change b.equivFun (nilpotentLinearFlow D t ⁅x, y⁆) =
    basisBracketLinear b (b.equivFun (nilpotentLinearFlow D t x))
      (b.equivFun (nilpotentLinearFlow D t y)) at ht
  rwa [hB] at ht

def unipotentLieLogarithm (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1)) :
    LieDerivation ℝ L L := by
  let D := nilpotentLog (A.toLinearMap - 1)
  have hD : IsNilpotent D := nilpotentLog_nilpotent _ hA
  have hExp : IsNilpotent.exp D = A.toLinearMap := by
    rw [exp_nilpotentLog _ hA]
    abel
  refine { D with leibniz' := ?_ }
  intro x y
  have hxy := hasDerivAt_nilpotentLinearFlow_zero D hD ⁅x, y⁆
  have hx := hasDerivAt_nilpotentLinearFlow_zero D hD x
  have hy := hasDerivAt_nilpotentLinearFlow_zero D hD y
  have hb := (normedLieBracket (L := L)).hasDerivAt_of_bilinear (fun _ => hx) (fun _ => hy)
  have heq : (fun t : ℝ => nilpotentLinearFlow D t ⁅x, y⁆) =
      (fun t : ℝ => ⁅nilpotentLinearFlow D t x, nilpotentLinearFlow D t y⁆) :=
    funext (fun t => nilpotentLinearFlow_preserves_lie A D hD hExp t x y)
  rw [heq] at hxy
  have hd := hxy.unique hb
  change D ⁅x, y⁆ = ⁅nilpotentLinearFlow D 0 x, D y⁆ + ⁅D x, nilpotentLinearFlow D 0 y⁆ at hd
  simp only [nilpotentLinearFlow, zero_smul, IsNilpotent.exp_zero, Module.End.one_apply] at hd
  rw [hd, sub_eq_add_neg, lie_skew (D x) y]

end PolycyclicRecognition

end

end OAI
