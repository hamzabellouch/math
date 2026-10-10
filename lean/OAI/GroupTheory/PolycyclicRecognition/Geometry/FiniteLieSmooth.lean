import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Smoothness of finite Lie polynomials

A finite-dimensional Lie bracket is a continuous bilinear map in basis
coordinates. Consequently the actual finite Dynkin expressions are smooth;
no smoothness of a chosen logarithm chart is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance finiteLieSmoothNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ L).equivFun.toLinearMap
    (finBasis ℝ L).equivFun.injective
local instance finiteLieSmoothNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ L).equivFun.toLinearMap

/-- Continuous bilinear realization of the given finite-dimensional bracket. -/
def finiteLieBracket : L →L[ℝ] L →L[ℝ] L :=
  (show L →ₗ[ℝ] L →L[ℝ] L from
    { toFun := fun x => Module.End.toContinuousLinearMap (𝕜 := ℝ) L (LieModule.toEnd ℝ L L x)
      map_add' := by intro x y; ext z; exact add_lie x y z
      map_smul' := by intro c x; ext z; exact smul_lie c x z }).toContinuousLinearMap

@[simp] theorem finiteLieBracket_apply (x y : L) : finiteLieBracket x y = ⁅x, y⁆ := rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I : Type*} {n : ℕ∞}

/-- Any fixed evaluated bracket word in smooth input functions is smooth. -/
theorem contDiff_evalBracketWord (X : V → I → L)
    (hX : ∀ i, ContDiff ℝ n (fun v => X v i)) (w : FreeMagma I) :
    ContDiff ℝ n (fun v => evalBracketWord (X v) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul a b ha hb =>
    exact (finiteLieBracket.contDiff.comp ha).clm_apply hb

/-- The finite published Dynkin expression is smooth in all its logarithms. -/
theorem contDiff_finiteDynkinPolynomial {c k : ℕ} (coeff : DynkinCoefficients c k)
    (X : V → Fin k → L) (hX : ∀ i, ContDiff ℝ n (fun v => X v i)) :
    ContDiff ℝ n (fun v => finiteDynkinPolynomial coeff (X v)) := by
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro w _
  exact (contDiff_evalBracketWord X hX (rightNestedWord d.val w)).const_smul _

end PolycyclicRecognition

end

end OAI
