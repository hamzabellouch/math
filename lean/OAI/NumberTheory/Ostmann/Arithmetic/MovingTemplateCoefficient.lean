import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeCoefficientNode
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplatePair

namespace OAI

/-! # The original coefficient on the complete regular-slot template -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateCoefficient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (y : MovingRegularSlot n r m → σ) (XL XR : ℕ) : ℂ :=
  movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
    (treeLeafMap (List.map y) n (movingTemplateSmall n r m))
    (treeLeafMap (List.map y) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) XL XR

theorem movingTemplateCompensationEquiv_restore {σ : Type*} (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → σ) n) :
    (treeLeafTupleEquiv (Fin 4 → σ) n).symm
      (fun j i => movingTemplateCompensationEquiv σ n a (j, i)) = a := by
  change (treeLeafTupleEquiv (Fin 4 → σ) n).symm
    (treeLeafTupleEquiv (Fin 4 → σ) n a) = a
  exact Equiv.symm_apply_apply _ _

theorem movingTemplateCoefficient_restored {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (a : TreeLeafTuple (Fin 4 → σ) n) (y : MovingRegularSlot n r m → σ) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m s
      (movingRestoreSample n r m (movingTemplateCompensationEquiv σ n a) y) XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (appendMovingSlotLeaves n (movingCompensationSlots n a)
        (treeLeafMap (List.map y) n (movingTemplateSmall n r m)))
      (treeLeafMap (List.map y) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) XL XR := by
  unfold movingTemplateCoefficient
  rw [movingRestoreSample_small_leaves, movingRestoreSample_bulk_leaves,
    movingTemplateCompensationEquiv_restore]

/-- Pair the surviving templates and restore each sampled compensation vector
in both children. This is the actual product recursion on the prescribed roles. -/
theorem movingTemplateCoefficient_prime_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (left right : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s
      (movingTemplatePairSample n r m left right) XL XR =
    ∑ a : TreeLeafTuple (Fin 4 → σ) n, (movingCompensationPrior (μ n) n a : ℂ) *
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        let CL := flattenMovingSlots n (treeLeafMap (List.map left) n (movingTemplateSmall n r m)) ++
          flattenMovingSlots n (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m)))
        let CR := flattenMovingSlots n (treeLeafMap (List.map right) n (movingTemplateSmall n r m)) ++
          flattenMovingSlots n (treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m)))
        let u := flattenMovingSlots n (movingCompensationSlots n a)
        let p := movingTopPivot value CL CR u XL XR s v.val w.val
        movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR u XL XR s v.val w.val *
          movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
            (movingRestoreSample n r m (movingTemplateCompensationEquiv σ n a) left) p XL *
          star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
            (movingRestoreSample n r m (movingTemplateCompensationEquiv σ n a) right) p XR) := by
  rw [movingTemplateCoefficient, movingTemplatePairSample_small, movingTemplatePairSample_bulk]
  rw [movingFrequencyCoefficient_prime_node value outside μ childBound pivotBound V hV F hF
    φ G n s hs hsV _ _ XL XR hXL hXR hVL hVR]
  simp only [movingTemplateCoefficient_restored]

end Ostmann

end OAI
