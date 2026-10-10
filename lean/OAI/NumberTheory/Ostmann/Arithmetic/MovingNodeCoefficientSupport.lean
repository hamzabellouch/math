import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude

namespace OAI

/-! # Integer substitution on the nonzero original coefficient support -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingPrimeNodeFactor_substitution_on_right {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (u : TreeLeafTuple (List σ) n) (small bulk : TreeLeafTuple (List σ) (n + 1))
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hsV : s.natAbs ≤ V (n + 1))
    (hv : v.natAbs ≤ childBound (n + 1)) (hw : w.natAbs ≤ childBound (n + 1)) :
    let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let LH := XL * MovingSlotReversal.naturalProduct value CL
    let RH := XR * MovingSlotReversal.naturalProduct value CR
    let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v w
    let A := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let B := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (∀ p ∈ I, p * U ≤ pivotBound (n + 1)) →
    (B ≠ 0 → 2 * pivotBound (n + 1) * childBound (n + 1) < RH) →
    (∀ q, q.Prime → q ∣ RH → V (n + 1) < q) →
    (∀ q, q.Prime → q ∣ U → childBound (n + 1) < q) →
    movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w * A * star B =
      if validTransferredPivot I (v * RH - w * LH) (s * U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * A * star B else 0  := by
  intro U CL CR LH RH p A B hbound hgap hRH hU
  by_cases hB : B = 0
  · simp only [hB, star_zero, mul_zero, ite_self]
  · exact movingPrimeNodeFactor_substitution value outside μ childBound pivotBound V F hF
      φ G n u small bulk XL XR s v w I hI hφ hsV hv hw hbound (hgap hB) hRH hU

theorem movingTemplateCoefficient_integer_node_on_coefficients {σ : Type} [Fintype σ]
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
    (hgap : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
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
      have ht := movingPrimeNodeFactor_substitution_on_right value outside μ childBound pivotBound V F hF
        φ G n (movingCompensationSlots n a) small bulk XL XR s v.val w.val I hI hφ hsV
        (((mem_transferFrequencyRange _ _).mp v.property).trans hchild)
        (((mem_transferFrequencyRange _ _).mp w.property).trans hchild)
      dsimp only [small, bulk] at ht
      have hCL := movingTemplateMapped_product value n r m left
      have hCR := movingTemplateMapped_product value n r m right
      simp only [hU, hCL, hCR] at ht
      specialize ht hc.1 (fun hB => hgap (movingTemplateCompensationEquiv σ n a)
        (hpμ ▸ ha) _ _ (by simpa only [movingTemplateCoefficient_restored] using hB)) hRH hc.2
      simp only [movingTemplateCoefficient_restored]
      dsimp only [movingTopPivot] at ht ⊢
      simp only [hU, hCL, hCR, Complex.ofReal_mul, Nat.cast_prod] at ht ⊢
      split_ifs at ht ⊢ <;> simpa only [mul_assoc, mul_zero] using ht

theorem movingTemplateCoefficient_transformed_integer_node_on_coefficients {σ : Type} [Fintype σ]
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
    (hgap : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (hleft : ∀ i, value (left i) ≠ 0) (hright : ∀ i, value (right i) ≠ 0)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s
      (movingTemplatePairSample n r m left right) XL XR *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then XL else XR)
          (value ∘ movingTemplatePairSample n r m left right))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s =
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
              (movingRestoreSample n r m u right) p XR) *
            movingTaggedTransform
              (Sum.elim (movingOneGiantModuli XL (value ∘ left))
                (movingOneGiantModuli XR (value ∘ right)))
              (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
                (Sum.elim (fun _ : Unit => true) (fun _ => false)))
              greg ggiant favorable outside.prod s
        else 0 := by
  have hn := movingTemplateCoefficient_integer_node_on_coefficients value outside μ childBound pivotBound V hV
    F hF φ G n r m s hsV left right XL XR hXL hXR hVL hVR I hI hφ hchild hgap hRH hcomp
  have ht := movingTaggedTransform_paired value n r m left right XL XR
    hXL.ne_zero hXR.ne_zero hleft hright greg ggiant favorable outside.prod s
  rw [hn, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_assoc, Finset.sum_mul]
  apply congrArg (fun z : ℂ =>
    (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) * z)
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  dsimp only
  split_ifs
  · congr 1
    exact ht.symm
  · exact zero_mul _

theorem movingTemplateCoefficient_averaged_integer_node_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (s : ℤ)
    (hsV : s.natAbs ≤ V (n + 1))
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ)
    (XL XR : ℕ) (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < XR * ∏ i, value (right i))
    (hRH : ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ q, q.Prime → q ∣ XR * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    (∑ y : MovingRegularSlot (n + 1) r m → σ, ((∏ i, ν i (y i) : ℝ) : ℂ) *
      (movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s y XL XR *
        movingTaggedTransform
          (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s)) =
    ∑ u : TreeLeafIndex n × Fin 4 → σ,
      (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
      ∑ left : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν true left : ℂ) *
        ∑ right : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν false right : ℂ) *
          ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
            movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G n r m I
              XL XR s left right greg ggiant favorable u v.val w.val := by
  let A := fun y : MovingRegularSlot (n + 1) r m → σ =>
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G (n + 1) r m s y XL XR *
      movingTaggedTransform
        (Sum.elim (fun b : Bool => if b then XL else XR) (value ∘ y))
        (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s
  let M := fun u : TreeLeafIndex n × Fin 4 → σ =>
    (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ)
  let B := fun left right u =>
    ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
      movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G n r m I
        XL XR s left right greg ggiant favorable u v.val w.val
  have hn left right (hr : movingTemplateSidePrior n r m ν false right ≠ 0) :
      A (movingTemplatePairSample n r m left right) = ∑ u, M u * B left right u := by
    exact movingTemplateCoefficient_transformed_integer_node_on_coefficients value outside μ childBound pivotBound V hV
      F hF φ G n r m s hsV left right XL XR hXL hXR hVL hVR I hI hφ hchild
      (hgap right hr) (hRH right hr) hcomp (fun i => (hvalue _).ne_zero)
      (fun i => (hvalue _).ne_zero) greg ggiant favorable
  change (∑ y, ((∏ i, ν i (y i) : ℝ) : ℂ) * A y) = _
  rw [movingTemplatePair_average]
  change (∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
    ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
      A (movingTemplatePairSample n r m left right)) = _
  have he : (∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
      ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
        A (movingTemplatePairSample n r m left right)) =
      ∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
        ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) *
          ∑ u, M u * B left right u := by
    apply Finset.sum_congr rfl
    intro left _
    congr 1
    apply Finset.sum_congr rfl
    intro right _
    by_cases hr : movingTemplateSidePrior n r m ν false right = 0
    · simp only [hr, Complex.ofReal_zero, zero_mul]
    · rw [hn left right hr]
  rw [he]
  change _ = ∑ u, M u * ∑ left, (movingTemplateSidePrior n r m ν true left : ℂ) *
    ∑ right, (movingTemplateSidePrior n r m ν false right : ℂ) * B left right u
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext left
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

theorem movingTemplatePrimeAmplitude_next_on_coefficients {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ q ∈ Pg, q.Prime) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot (n + 1) r m → σ → ℝ)
    (hlarge : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ) (w : ℤ),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G n (4 + r) m w
        (movingRestoreSample n r m u right) p XR ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hRH : ∀ XR : Pg, ∀ right, movingTemplateSidePrior n r m ν false right ≠ 0 →
      ∀ q, q.Prime → q ∣ (XR : ℕ) * (∏ i, value (right i)) → V (n + 1) < q)
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
      Pg ρ ν greg ggiant favorable =
    ∑ XL : Pg, (ρ XL : ℂ) * ∑ XR : Pg, (ρ XR : ℂ) *
      ∑ s : transferFrequencyRange (V (n + 1)),
        ∑ u : TreeLeafIndex n × Fin 4 → σ,
          (((∏ i, μ n (u i)) * ((∏ i, value (u i)) : ℝ) : ℝ) : ℂ) *
            ∑ left : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν true left : ℂ) *
              ∑ right : MovingRegularSlot n r m → σ, (movingTemplateSidePrior n r m ν false right : ℂ) *
                ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
                  movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G
                    n r m I XL XR s.val left right greg ggiant favorable u v.val w.val := by
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  congr 1
  apply Finset.sum_congr rfl
  intro XR _
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact movingTemplateCoefficient_averaged_integer_node_on_coefficients value hvalue outside μ
    childBound pivotBound V hV F hF φ G n r m s.val
    ((mem_transferFrequencyRange _ _).mp s.property) ν XL XR
    (hPg _ XL.property) (hPg _ XR.property) (hlarge XL) (hlarge XR)
    I hI hφ hchild (hgap XR) (hRH XR) hcomp greg ggiant favorable

end Ostmann

end OAI
