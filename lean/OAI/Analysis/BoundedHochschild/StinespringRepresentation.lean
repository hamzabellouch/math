import OAI.Analysis.BoundedHochschild.StinespringLeftAction

namespace OAI

/-! The star representation obtained from the positive-kernel Hilbert space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_ext (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (A B : StinespringSpace φ →L[ℂ] StinespringSpace φ)
    (h : ∀ x y : StinespringPreSpace φ,
      inner ℂ (x : StinespringSpace φ) (A y) = inner ℂ (x : StinespringSpace φ) (B y)) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y => exact h x y

lemma stinespringOperator_inner_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x y : StinespringPreSpace φ) :
    inner ℂ (x : StinespringSpace φ) (stinespringOperator φ b y) =
      kernelForm (fun p q : M × H => inner ℂ p.2 (φ (star p.1 * b * q.1) q.2)) x y := by
  rw [stinespringOperator_coe, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y) = _
  have he := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
    (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
  refine he.trans ?_
  congr 1
  funext p q
  simp only [stinespringKernel, stinespringLeftLabel, mul_assoc]

lemma stinespringOperator_zero (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 0 = 0 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, Finsupp.sum]

lemma stinespringOperator_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a + b) = stinespringOperator φ a + stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  simp only [add_apply, inner_add_right, stinespringOperator_inner_coe, kernelForm,
    mul_add, add_mul, map_add, Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringOperator_one (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 1 = 1 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_coe]
  rw [stinespringShift_one]
  rfl

lemma stinespringOperator_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a * b) = stinespringOperator φ a * stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [mul_apply_eq_comp, stinespringOperator_coe, stinespringOperator_coe,
    stinespringOperator_coe, stinespringShift_mul]

end BoundedHochschild.KadisonRingrose

end

end OAI
