import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieWordDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealNormedLieAlgebra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace OAI

/-! # Actual derivatives of finite Lie polynomials

The finite-dimensional bracket is continuous in the given norm. The resulting
differential is the algebraic word differential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

/-- Continuous realization of the bracket in the given finite-dimensional norm. -/
def normedLieBracket : L →L[ℝ] L →L[ℝ] L :=
  (show L →ₗ[ℝ] L →L[ℝ] L from
    { toFun := fun x => Module.End.toContinuousLinearMap (𝕜 := ℝ) L (LieModule.toEnd ℝ L L x)
      map_add' := by intro x y; ext z; exact add_lie x y z
      map_smul' := by intro c x; ext z; exact smul_lie c x z }).toContinuousLinearMap

theorem hasFDerivAt_evalBracketWord {I : Type*}
    (X : L → I → L) (dX : I → L →ₗ[ℝ] L) (z : L)
    (hX : ∀ i, HasFDerivAt (fun y => X y i) (dX i).toContinuousLinearMap z)
    (w : FreeMagma I) :
    HasFDerivAt (fun y => evalBracketWord (X y) w)
      (bracketWordDifferential (X z) dX w).toContinuousLinearMap z := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv =>
    have hh := (normedLieBracket (L := L)).hasFDerivAt_of_bilinear hu hv
    apply hh.congr_fderiv
    ext a
    change ⁅evalBracketWord (X z) u, bracketWordDifferential (X z) dX v a⁆ +
        ⁅bracketWordDifferential (X z) dX u a, evalBracketWord (X z) v⁆ =
      ⁅bracketWordDifferential (X z) dX u a, evalBracketWord (X z) v⁆ +
        ⁅evalBracketWord (X z) u, bracketWordDifferential (X z) dX v a⁆
    exact add_comm _ _

theorem hasFDerivAt_finiteDynkinPolynomial {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X : L → Fin n → L)
    (dX : Fin n → L →ₗ[ℝ] L) (z : L)
    (hX : ∀ i, HasFDerivAt (fun y => X y i) (dX i).toContinuousLinearMap z) :
    HasFDerivAt (fun y => finiteDynkinPolynomial coeff (X y))
      (finiteDynkinDifferential coeff (X z) dX).toContinuousLinearMap z := by
  have hh := HasFDerivAt.sum fun d (_ : d ∈ Finset.univ) =>
    HasFDerivAt.sum fun w (_ : w ∈ Finset.univ) =>
      (hasFDerivAt_evalBracketWord X dX z hX (rightNestedWord d.val w)).const_smul (coeff d w)
  have hfun : (∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
      coeff d w • fun y => evalBracketWord (X y) (rightNestedWord d.val w)) =
      fun y => finiteDynkinPolynomial coeff (X y) := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, finiteDynkinPolynomial]
  rw [hfun] at hh
  apply hh.congr_fderiv
  ext a
  simp only [sum_apply, smul_apply,
    LinearMap.coe_toContinuousLinearMap', finiteDynkinDifferential,
    LinearMap.sum_apply, LinearMap.smul_apply]

end PolycyclicRecognition

end

end OAI
