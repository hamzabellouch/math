import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateOperations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialCoordinateSmooth

namespace OAI

/-! # Polynomial maps in specified finite-dimensional bases -/

noncomputable section
namespace PolycyclicRecognition
open Module
variable {V W U : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {d e k : ℕ}

def IsPolynomialInBasis (b : Basis (Fin d) ℝ V) (c : Basis (Fin e) ℝ W)
    (f : V → W) : Prop :=
  IsCoordinatePolynomial (fun x => c.equivFun (f (b.equivFun.symm x)))

namespace IsPolynomialInBasis
variable {b : Basis (Fin d) ℝ V} {c : Basis (Fin e) ℝ W}
  {a : Basis (Fin k) ℝ U}

theorem linear (f : V →ₗ[ℝ] W) : IsPolynomialInBasis b c f :=
  IsCoordinatePolynomial.linear (c.equivFun.toLinearMap.comp
    (f.comp b.equivFun.symm.toLinearMap))

theorem comp {f : V → W} {g : W → U}
    (hg : IsPolynomialInBasis c a g) (hf : IsPolynomialInBasis b c f) :
    IsPolynomialInBasis b a (g ∘ f) := by
  have h := IsCoordinatePolynomial.comp hg hf
  simpa only [IsPolynomialInBasis, Function.comp_def, LinearEquiv.symm_apply_apply] using h

theorem contDiff {f : V → W} (hf : IsPolynomialInBasis b c f) : ContDiff ℝ ⊤ f := by
  let : FiniteDimensional ℝ V := Module.Finite.of_basis b
  let : FiniteDimensional ℝ W := Module.Finite.of_basis c
  have h := c.equivFun.toContinuousLinearEquiv.symm.contDiff.comp
    ((IsCoordinatePolynomial.contDiff hf).comp b.equivFun.toContinuousLinearEquiv.contDiff)
  change ContDiff ℝ ⊤ (fun x => c.equivFun.symm
    (c.equivFun (f (b.equivFun.symm (b.equivFun x))))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem ext_integer_grid {f g : V → W}
    (hf : IsPolynomialInBasis b c f) (hg : IsPolynomialInBasis b c g)
    (h : ∀ z : Fin d → ℤ,
      f (b.equivFun.symm (fun i => (z i : ℝ))) =
        g (b.equivFun.symm (fun i => (z i : ℝ)))) : f = g := by
  have he := IsCoordinatePolynomial.ext_integer_grid hf hg (fun z => congrArg c.equivFun (h z))
  funext x
  apply c.equivFun.injective
  simpa only [LinearEquiv.symm_apply_apply] using congrFun he (b.equivFun x)

theorem iterate {f : V → V} (hf : IsPolynomialInBasis b b f) (n : ℕ) :
    IsPolynomialInBasis b b (f^[n]) := by
  induction n with
  | zero => exact linear (LinearMap.id : V →ₗ[ℝ] V)
  | succ n ih =>
    have he : f^[n + 1] = f ∘ f^[n] := funext (Function.iterate_succ_apply' f n)
    rw [he]
    exact hf.comp ih

theorem iterate_zero_of_integer_grid {f : V → V}
    (hf : IsPolynomialInBasis b b f) (n : ℕ)
    (hn : ∀ z : Fin d → ℤ, f^[n] (b.equivFun.symm (fun i => (z i : ℝ))) = 0) :
    ∀ x, f^[n] x = 0 := by
  have hz : IsPolynomialInBasis b b (fun _ : V => (0 : V)) := by
    simpa only [IsPolynomialInBasis, map_zero] using
      (IsCoordinatePolynomial.const (I := Fin d) (0 : Fin d → ℝ))
  exact congrFun ((hf.iterate n).ext_integer_grid hz hn)

end IsPolynomialInBasis
end PolycyclicRecognition

end

end OAI
