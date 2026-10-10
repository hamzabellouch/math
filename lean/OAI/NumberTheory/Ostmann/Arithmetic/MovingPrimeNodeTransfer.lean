import OAI.NumberTheory.Ostmann.Arithmetic.MovingChildListSupport

namespace OAI

/-! # The arithmetic guard is automatic in the genuine off-diagonal -/

namespace Ostmann
open scoped Classical BigOperators

/-- On a retained integer substitution, the supported child coefficients
supply the pairwise and frequency-unit tests of the new node. Its remaining
bounds are exactly the range inequalities used by the full transfer theorem. -/
theorem movingPrimeNodeFactor_transfer_product {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (u : TreeLeafTuple (List σ) n) (small bulk : TreeLeafTuple (List σ) (n + 1))
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p ∈ I, 0 < p)
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
    validTransferredPivot I (v * RH - w * LH) (s * U) →
    (∀ p ∈ I, p * U ≤ pivotBound (n + 1)) →
    2 * pivotBound (n + 1) * childBound (n + 1) < RH →
    (∀ q, q.Prime → q ∣ RH → V (n + 1) < q) →
    (∀ q, q.Prime → q ∣ U → childBound (n + 1) < q) →
    movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w * A * star B =
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * A * star B := by
  intro U CL CR LH RH p A B htrans hbound hgap hRH hU
  by_cases hA : A = 0
  · simp only [hA, mul_zero, zero_mul]
  by_cases hB : B = 0
  · simp only [hB, star_zero, mul_zero]
  have hs : s ≠ 0 := left_ne_zero_of_mul htrans.1
  have hUpos : 0 < U := Nat.pos_of_ne_zero (fun hz => htrans.1 (by simp [hz]))
  have hpI : p ∈ I := htrans.2.2.2
  have hrel : v * (RH : ℤ) - w * (LH : ℤ) = s * (p * U : ℕ) := by
    have he := validTransferredPivot_equation I (v * RH - w * LH) (s * U) htrans
    change v * (RH : ℤ) - w * (LH : ℤ) = (s * U) * p at he
    calc
      _ = (s * U) * p := he
      _ = _ := by rw [Nat.cast_mul]; ring
  have hleft := movingFrequencyCoefficient_child_products value outside μ childBound pivotBound V
    F φ G n v u small.1 bulk.1 p XL hA
  have hright := movingFrequencyCoefficient_child_products value outside μ childBound pivotBound V
    F φ G n w u small.2 bulk.2 p XR hB
  have hLunit : LH.Coprime (p * U) := hleft.2
  have hcop : LH.Coprime RH := transferred_products_coprime LH RH v w s (p * U) hs hrel
    (fun q hq _ hd => hsV.trans_lt (hRH q hq hd))
    (common_prime_pivot_unit (p * U) LH RH hLunit)
  have hmerged := pairwise_coprime_merge_shared (XL :: CL.map value) (XR :: CR.map value)
    outside hleft.1 hright.1 (by simpa only [LH, RH, List.prod_cons, MovingSlotReversal.naturalProduct] using hcop)
  have hperm : ((XL :: CL.map value) ++ (XR :: CR.map value) ++ outside).Perm
      (XL :: XR :: ((CL ++ CR).map value ++ outside)) := by
    apply List.perm_iff_count.mpr
    intro a
    simp only [List.count_cons, List.count_append, List.map_append]
    omega
  have hpair := (hperm.pairwise_iff (fun h => h.symm)).mp hmerged
  have hw0 : w ≠ 0 := by
    intro hz
    apply hB
    subst w
    exact movingFrequencyCoefficient_zero value outside μ childBound pivotBound V F hF φ G
      n (appendMovingSlotLeaves n u small.2) bulk.2 p XR
  have hpw := (movingFrequencyCoefficient_nonzero_support value outside μ childBound pivotBound V
    F φ G n w (appendMovingSlotLeaves n u small.2) bulk.2 p XR hB).2.1
  have hpw' : p.Coprime w.natAbs := by
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using hpw
  have hUw : U.Coprime w.natAbs := large_prime_factors_coprime_frequency U w hw0
    (fun q hq hd => hw.trans_lt (hU q hq hd))
  have hroot : IsCoprime s (RH : ℤ) := by
    have h := large_prime_factors_coprime_frequency RH s hs
      (fun q hq hd => hsV.trans_lt (hRH q hq hd))
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using h.symm
  have hguard : movingNodeArithmeticGuard (childBound (n + 1)) (pivotBound (n + 1))
      LH RH s v w (p * U) :=
    ⟨hs, hroot, hrel, Nat.mul_pos (hI p hpI) hUpos, hbound p hpI, hv, hw, hgap,
      hpw'.mul_left hUw⟩
  have hfactor : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w =
      (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) := by
    unfold movingPrimeNodeFactor
    exact ite_eq_left ⟨hpair, hguard, hUpos⟩
  rw [hfactor]

end Ostmann

end OAI
