import OAI.Analysis.BoundedHochschild.StinespringRepresentation

namespace OAI

/-! The adjoint and scalar identities of the positive-kernel representation. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    stinespringOperator φ (star b) = star (stinespringOperator φ b) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [stinespringOperator_coe, stinespringOperator_coe, Completion.inner_coe, Completion.inner_coe]
    change kernelForm (stinespringKernel φ) (Finsupp.mapDomain (stinespringLeftLabel (star b)) x) y =
      kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y)
    have hl := kernelForm_mapDomain_left (stinespringKernel φ) (stinespringLeftLabel (star b))
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    have hr := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    refine hl.trans ((congrArg (fun K : Matrix (M × H) (M × H) ℂ => kernelForm K x y) ?_).trans hr.symm)
    funext p q
    simp only [stinespringKernel, stinespringLeftLabel, star_mul, star_star, mul_assoc]

lemma stinespringOperator_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (b : M) :
    stinespringOperator φ (z • b) = z • stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [smul_apply, inner_smul_right, stinespringOperator_inner_coe, stinespringOperator_inner_coe]
  simp only [kernelForm, mul_smul_comm, smul_mul_assoc, map_smul,
    smul_apply, inner_smul_right, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The genuine unital star representation on the positive-kernel Hilbert
space associated to a completely positive map. -/
def stinespringRepresentation (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    M →⋆ₐ[ℂ] (StinespringSpace φ →L[ℂ] StinespringSpace φ) where
  toFun := stinespringOperator φ
  map_zero' := stinespringOperator_zero φ
  map_one' := stinespringOperator_one φ
  map_add' := stinespringOperator_add φ
  map_mul' := stinespringOperator_mul φ
  map_star' := stinespringOperator_star φ
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, stinespringOperator_smul, stinespringOperator_one]
    rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
