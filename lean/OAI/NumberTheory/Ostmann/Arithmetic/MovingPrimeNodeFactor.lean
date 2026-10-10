import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeRootGuard

namespace OAI

/-! # The actual top node factor before summing descendant histories -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original nine arithmetic tests at a node, in terms of its products. -/
def movingNodeArithmeticGuard (N B LH RH : ℕ) (s v w : ℤ) (P : ℕ) : Prop :=
  s ≠ 0 ∧ IsCoprime s (RH : ℤ) ∧ v * RH - w * LH = s * P ∧
    0 < P ∧ P ≤ B ∧ v.natAbs ≤ N ∧ w.natAbs ≤ N ∧
    2 * B * N < RH ∧ P.Coprime w.natAbs

theorem movingRootState_arithmetic_guard {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1)) (CL CR u : List σ)
    (XL XR P : ℕ) (s v w : ℤ) :
    ValidTransferNode (movingSlotSystem value childBound pivotBound)
      (movingRootState n t CL CR u XL XR) s v w P ↔
    movingNodeArithmeticGuard (childBound (n + 1)) (pivotBound (n + 1))
      (XL * MovingSlotReversal.naturalProduct value CL)
      (XR * MovingSlotReversal.naturalProduct value CR) s v w P := by
  constructor
  · intro h
    exact ⟨h.root_ne_zero, h.root_unit, h.relation, h.pivot_pos, h.pivot_bound,
      h.left_bound, h.right_bound, h.range_gap, h.pivot_unit⟩
  · rintro ⟨hs, hu, he, hp, hB, hv, hw, hgap, hunit⟩
    exact ⟨hs, hu, he, hp, hB, hv, hw, hgap, hunit⟩

noncomputable def movingTopPivot {σ : Type*} (value : σ → ℕ)
    (CL CR u : List σ) (XL XR : ℕ) (s v w : ℤ) : ℕ :=
  reconstructedPivot
    (v * (XR * MovingSlotReversal.naturalProduct value CR : ℕ) -
      w * (XL * MovingSlotReversal.naturalProduct value CL : ℕ))
    (s * MovingSlotReversal.naturalProduct value u)

/-- This factor uses only the current lists and three root frequencies.
Descendant support is retained in the two child coefficients. -/
noncomputable def movingPrimeNodeFactor {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (CL CR u : List σ) (XL XR : ℕ) (s v w : ℤ) : ℂ :=
  let U := MovingSlotReversal.naturalProduct value u
  let p := movingTopPivot value CL CR u XL XR s v w
  if (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime ∧
      (movingNodeArithmeticGuard (childBound (n + 1)) (pivotBound (n + 1))
        (XL * MovingSlotReversal.naturalProduct value CL)
        (XR * MovingSlotReversal.naturalProduct value CR) s v w (p * U) ∧ 0 < U)
    then ((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) else 0

/-- The original guarded summand is exactly a root-only factor times the
original two supported child coefficients. This is used only at actual prime
outer giants, where the extra cross-branch frequency tests follow from size. -/
theorem movingPrimeNodeFactor_term {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (l r : ScheduledFrequencyIndex V n)
    (small bulk : TreeLeafTuple (List σ) (n + 1))
    (a : TreeLeafTuple (Fin 4 → σ) n) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) :
    let u := movingCompensationSlots n a
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let t := (s, scheduledFrequencyHistory V n l, scheduledFrequencyHistory V n r)
    let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
    let U := x.compensation value
    let v := frequencyRoot n t.2.1
    let w := frequencyRoot n t.2.2
    let p := reconstructedPivot
      (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (s * U)
    let L := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.1
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let R := movingSupportedSampledWeight value outside μ childBound pivotBound F
      (movingOriginalNode value childBound pivotBound φ G) n t.2.2
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (if movingLocalSupport value outside x ∧
        (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧
          0 < U) then (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * L * star R else 0) =
      movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
        (flattenMovingSlots n u) XL XR s v w * L * star R := by
  intro u CL CR t x U v w p L R
  have h := movingRootState_prime_guard_product value outside μ childBound pivotBound V hV F hF
    φ G n s hs hsV l r small bulk a XL XR hXL hXR hVL hVR
    ((((U : ℝ) * φ (Real.log p - G (n + 1))) : ℝ) : ℂ)
    (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧ 0 < U)
  calc
    _ = (if (XL :: XR :: ((CL ++ CR).map value ++ outside)).Pairwise Nat.Coprime ∧
        (ValidTransferNode (movingSlotSystem value childBound pivotBound) x s v w (p * U) ∧
          0 < U) then ((((U : ℝ) * φ (Real.log p - G (n + 1))) : ℝ) : ℂ) * L * star R
        else 0) := by
      convert h using 1 <;> split_ifs <;> rfl
    _ = _ := by
      simp only [x, movingRootState_arithmetic_guard]
      unfold movingPrimeNodeFactor movingTopPivot
      dsimp only [x, U, p, v, w, t, movingRootState, MovingSlotState.compensation,
        MovingSlotState.leftProduct, MovingSlotState.rightProduct]
      simp only [ite_mul, zero_mul]

end Ostmann

end OAI
