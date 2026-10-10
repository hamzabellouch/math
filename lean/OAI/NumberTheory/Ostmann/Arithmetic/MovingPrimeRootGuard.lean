import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTransferSupport
import OAI.NumberTheory.Ostmann.ZeroDensity.MovingZeroFrequency

namespace OAI

/-! # The top frequency guards at actual prime giants -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.Follows.frequencies {σ : Type*} {n : ℕ}
    {T : MovingSlotData σ n} {t : FrequencyTree ℤ n} (hT : T.Follows t)
    (P : ℤ → Prop) (h : ∀ s ∈ allFrequencyList n t, P s) : T.Frequencies P := by
  induction T with
  | leaf s regular => exact h s (by simpa only [allFrequencyList, hT, List.mem_singleton])
  | node s CL CR U left right ihL ihR =>
    refine ⟨h s (by simp only [allFrequencyList, List.mem_cons, hT.1, true_or]), ?_, ?_⟩
    · exact ihL hT.2.1 (fun a ha => h a (List.mem_cons_of_mem _ (List.mem_append_left _ ha)))
    · exact ihR hT.2.2 (fun a ha => h a (List.mem_cons_of_mem _ (List.mem_append_right _ ha)))

theorem movingFrequencySkeleton_follows (σ : Type*) (n : ℕ) (t : FrequencyTree ℤ n) :
    (movingFrequencySkeleton σ n t).Follows t := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨rfl, ih t.2.1, ih t.2.2⟩

theorem movingRootState_prime_support_iff {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (CL CR U : List σ) (XL XR V : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime) (hVL : V < XL) (hVR : V < XR)
    (hf : ∀ s ∈ allFrequencyList (n + 1) t, s ≠ 0 ∧ s.natAbs ≤ V) :
    movingLocalSupport value outside (movingRootState n t CL CR U XL XR) ↔
      (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime := by
  constructor
  · exact fun h => h.1
  · intro hp
    apply moving_local_support_prime_giants value outside
      (movingRootState n t CL CR U XL XR).data XL XR V hXL hXR hVL hVR hp
    apply MovingSlotData.Follows.frequencies
      (T := (movingRootState n t CL CR U XL XR).data) (t := t) _ _ hf
    exact ⟨rfl, movingFrequencySkeleton_follows σ n t.2.1,
      movingFrequencySkeleton_follows σ n t.2.2⟩

/-- Nonzero child coefficients remove the zero-history cases. Thus the
remaining top guard depends only on the actual prime lists and the two root
frequencies, as required before the child sums are multiplied. -/
theorem movingRootState_prime_guard_product {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (l r : ScheduledFrequencyIndex V n)
    (small bulk : TreeLeafTuple (List σ) (n + 1))
    (a : TreeLeafTuple (Fin 4 → σ) n) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) (C : ℂ) (guard : Prop) :
    let u := movingCompensationSlots n a
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let t := (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r)
    let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
    let p := reconstructedPivot
      (frequencyRoot n t.2.1 * (x.rightProduct value : ℤ) -
        frequencyRoot n t.2.2 * (x.leftProduct value : ℤ)) (s * x.compensation value)
    let L := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.1
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let R := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.2
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (if movingLocalSupport value outside x ∧ guard then C * L * star R else 0) =
      (if (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime ∧ guard
        then C * L * star R else 0) := by
  dsimp only
  by_cases hl : ∀ z ∈ allFrequencyList n (scheduledFrequencyHistory V n l), z ≠ 0
  · by_cases hr : ∀ z ∈ allFrequencyList n (scheduledFrequencyHistory V n r), z ≠ 0
    · have hf : ∀ z ∈ allFrequencyList (n + 1)
          (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r),
          z ≠ 0 ∧ z.natAbs ≤ V (n + 1) := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨hs, hsV⟩
        · rcases List.mem_append.mp hz with hz | hz
          · exact ⟨hl z hz, (scheduledFrequencyHistory_all_bound V hV n l z hz).trans
              (hV (Nat.le_succ n))⟩
          · exact ⟨hr z hz, (scheduledFrequencyHistory_all_bound V hV n r z hz).trans
              (hV (Nat.le_succ n))⟩
      rw [movingRootState_prime_support_iff value outside n _ _ _ _ XL XR (V (n + 1))
        hXL hXR hVL hVR hf]
      split_ifs <;> rfl
    · simp only [movingSupportedSampledWeight_zero_frequency value outside μ childBound
        pivotBound F _ hF n _ _ _ _ _ hr, star_zero, mul_zero, ite_self]
  · simp only [movingSupportedSampledWeight_zero_frequency value outside μ childBound
      pivotBound F _ hF n _ _ _ _ _ hl, mul_zero, zero_mul, ite_self]

end Ostmann

end OAI
