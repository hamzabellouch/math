import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeOffDiagonalCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateCoefficient

namespace OAI

/-! # The integer node on the original independent template law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateMapped_product {σ : Type*} (value : σ → ℕ) (n r m : ℕ)
    (y : MovingRegularSlot n r m → σ) :
    MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n (treeLeafMap (List.map y) n (movingTemplateSmall n r m)) ++
        flattenMovingSlots n (treeLeafMap (List.map y) n
          (bulkSlotLeaves n m (movingTemplateBulk n r m)))) = ∏ i, value (y i) := by
  simpa only [flattenMovingSlots_map, MovingSlotReversal.naturalProduct,
    List.map_append, List.map_map, Function.comp_def] using movingTemplate_product value n r m y

theorem movingTemplateCompensationEquiv_product {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n a)) =
      ∏ i, value (movingTemplateCompensationEquiv σ n a i) := by
  rw [movingCompensationProduct_indexed, Fintype.prod_prod_type]
  rfl

/-- This is the full next coefficient under the original independent
compensation law, with its exact integer pivot and complete child coefficients. -/
theorem movingTemplateCoefficient_integer_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hsV : s.natAbs ≤ V (n + 1))
    (left right : MovingRegularSlot n r m → σ) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : 2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s
      (movingTemplatePairSample n r m left right) XL XR =
    ∑ u : TreeLeafIndex n × Fin 4 → σ,
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
      ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
        let LH := XL * ∏ i, value (left i)
        let RH := XR * ∏ i, value (right i)
        let p := reconstructedPivot (v.val * RH - w.val * LH) (s * ∏ i, value (u i))
        if validTransferredPivot I (v.val * RH - w.val * LH) (s * ∏ i, value (u i)) then
          (φ (Real.log p - G (n + 1)) : ℂ) *
            movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
              (movingRestoreSample n r m u left) p XL *
            star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
              (movingRestoreSample n r m u right) p XR)
        else 0 := by
  by_cases hs : s = 0
  · subst s
    change movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      (n + 1) 0 _ _ XL XR = _
    rw [movingFrequencyCoefficient_zero value outside μ childBound pivotBound V F hF φ G]
    simp only [zero_mul, validTransferredPivot, ne_eq, not_true_eq_false, false_and,
      ite_false, Finset.sum_const_zero, mul_zero]
  ·
    let K := fun u : TreeLeafIndex n × Fin 4 → σ =>
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
        ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
          let LH := XL * ∏ i, value (left i)
          let RH := XR * ∏ i, value (right i)
          let p := reconstructedPivot (v.val * RH - w.val * LH) (s * ∏ i, value (u i))
          if validTransferredPivot I (v.val * RH - w.val * LH) (s * ∏ i, value (u i)) then
            (φ (Real.log p - G (n + 1)) : ℂ) *
              movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m v.val
                (movingRestoreSample n r m u left) p XL *
              star (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w.val
                (movingRestoreSample n r m u right) p XR)
          else 0
    change _ = ∑ u, K u
    rw [← (movingTemplateCompensationEquiv σ n).sum_comp K]
    rw [movingTemplateCoefficient_prime_node value outside μ childBound pivotBound V hV F hF
      φ G n r m s hs hsV left right XL XR hXL hXR hVL hVR]
    apply Finset.sum_congr rfl
    intro a _
    have hpμ := movingTemplateCompensationEquiv_prior (μ n) n a
    have hU := movingTemplateCompensationEquiv_product value n a
    by_cases ha : movingCompensationPrior (μ n) n a = 0
    · simp only [K, hpμ, ha, Complex.ofReal_zero, zero_mul]
    · have hc := hcomp (movingTemplateCompensationEquiv σ n a) (hpμ ▸ ha)
      dsimp only [K]
      rw [hpμ, Complex.ofReal_mul, mul_assoc]
      apply congrArg (fun z : ℂ => (movingCompensationPrior (μ n) n a : ℂ) * z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      let small := (treeLeafMap (List.map left) n (movingTemplateSmall n r m),
        treeLeafMap (List.map right) n (movingTemplateSmall n r m))
      let bulk := (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m)),
        treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m)))
      have ht := movingPrimeNodeFactor_substitution value outside μ childBound pivotBound V F hF
        φ G n (movingCompensationSlots n a) small bulk XL XR s v.val w.val I hI hφ hsV
        (((mem_transferFrequencyRange _ _).mp v.property).trans hchild)
        (((mem_transferFrequencyRange _ _).mp w.property).trans hchild)
      dsimp only [small, bulk] at ht
      have hCL := movingTemplateMapped_product value n r m left
      have hCR := movingTemplateMapped_product value n r m right
      simp only [hU, hCL, hCR] at ht
      specialize ht hc.1 hgap hRH hc.2
      simp only [movingTemplateCoefficient_restored]
      dsimp only [movingTopPivot] at ht ⊢
      simp only [hU, hCL, hCR, Complex.ofReal_mul, Nat.cast_prod] at ht ⊢
      split_ifs at ht ⊢ <;> simpa only [mul_assoc, mul_zero] using ht

end Ostmann

end OAI
