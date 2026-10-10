import OAI.Analysis.BoundedHochschild.StinespringBounds
import OAI.Analysis.BoundedHochschild.PositiveKernelActions

namespace OAI

/-! Left multiplication on the auxiliary positive-kernel Hilbert space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev StinespringPreSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelPreSpace (stinespringKernel φ) (stinespringKernel_positive φ)

def stinespringLeftLabel (b : M) (p : M × H) : M × H := (b * p.1, p.2)

def stinespringShift (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : StinespringPreSpace φ) : StinespringPreSpace φ :=
  Finsupp.mapDomain (stinespringLeftLabel b) x

lemma stinespringShift_one (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) : stinespringShift φ 1 x = x := by
  have he : stinespringLeftLabel (H := H) (1 : M) = id := by
    funext p
    simp only [stinespringLeftLabel, one_mul, id_eq]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [he, Finsupp.mapDomain_id]

lemma stinespringShift_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a b : M) (x : StinespringPreSpace φ) :
    stinespringShift φ a (stinespringShift φ b x) = stinespringShift φ (a * b) x := by
  have he : stinespringLeftLabel (H := H) a ∘ stinespringLeftLabel b =
      stinespringLeftLabel (a * b) := by
    funext p
    simp only [Function.comp_apply, stinespringLeftLabel, mul_assoc]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [← Finsupp.mapDomain_comp, he]

lemma stinespringLeft_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : (M × H) →₀ ℂ) :
    (kernelForm (fun p q => stinespringKernel φ (stinespringLeftLabel b p)
      (stinespringLeftLabel b q)) x x).re ≤ ‖b‖ ^ 2 * (kernelForm (stinespringKernel φ) x x).re := by
  classical
  change (kernelForm (fun p q : M × H => inner ℂ p.2
    (φ (star (b * p.1) * (b * q.1)) q.2)) x x).re ≤
      ‖b‖ ^ 2 * (kernelForm (fun p q : M × H => inner ℂ p.2
        (φ (star p.1 * q.1) q.2)) x x).re
  rw [kernelForm_coefficients, kernelForm_coefficients]
  exact completelyPositive_kernel_left_bound φ (fun p : x.support => p.val.1)
    (fun p : x.support => x p • p.val.2) b

/-- The bounded left action before completing the kernel space. -/
def stinespringPreOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringPreSpace φ →L[ℂ] StinespringPreSpace φ :=
  kernelPreMap (stinespringKernel φ) (stinespringKernel_positive φ)
    (stinespringLeftLabel b) ‖b‖ (norm_nonneg _) (stinespringLeft_bound φ b)

/-- The induced action on the separated Hilbert completion. -/
def stinespringOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringSpace φ →L[ℂ] StinespringSpace φ :=
  (stinespringPreOperator φ b).completion

@[simp] lemma stinespringOperator_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x : StinespringPreSpace φ) :
    stinespringOperator φ b x =
      (UniformSpace.Completion.coe' (stinespringShift φ b x)) := by
  exact ContinuousLinearMap.completion_apply_coe (stinespringPreOperator φ b) x

end BoundedHochschild.KadisonRingrose

end

end OAI
