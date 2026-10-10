import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSpectator

namespace OAI

/-! # The spectator zero convention eliminates inserted nonunits -/

namespace Ostmann
open scoped Classical

/-- A giant which is zero at an outside prime survives along one child path
until a leaf. Its zero contribution is thus forced by the original transform. -/
theorem movingSlotSpectator_zero {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (hg : g 0 = 0) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hzero : (XL : ZMod q) = 0 ∨ (XR : ZMod q) = 0) :
    movingSlotSpectator value g D T XL XR = 0 := by
  induction T generalizing XL XR with
  | leaf s regular =>
    rcases hzero with h | h <;>
      simp only [movingSlotSpectator, Nat.cast_mul, h, zero_mul, mul_zero, div_zero, hg]
  | node s CL CR U left right ihL ihR =>
    simp only [movingSlotSpectator]
    split_ifs
    · rfl
    · rcases hzero with h | h
      · rw [ihL _ _ (Or.inr h), zero_mul]
      · rw [ihR _ _ (Or.inr h), star_zero, mul_zero]

/-- For the actual transforms (which vanish at zero), no extra hypothesis
that the composite pivot is a unit is needed for spectator factorization. -/
theorem movingSlotWeight_spectator_of_zero {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (g : ZMod q → ℂ) (hg : g 0 = 0) (D : (ZMod q)ˣ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
        (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t *
      movingSlotSpectator value g D T XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    have hs : s = t := hT
    simp only [recursiveTransferWeight, spectatorHistoryLeaf, movingSlotModulus,
      movingSlotSpectator, hs]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    by_cases hw : recursiveTransferWeight sys F cutoff (n + 1) x t = 0
    · rw [recursiveTransferWeight_mul_leaf]
      change recursiveTransferWeight sys F cutoff (n + 1) x t * _ =
        recursiveTransferWeight sys F cutoff (n + 1) x t * _
      rw [hw, zero_mul, zero_mul]
    · obtain ⟨P, hvalid, _, _⟩ := recursiveTransferWeight_nonzero_valid sys F cutoff _ x t hw
      have hnode := recursiveTransferWeight_node sys F cutoff n x t P hvalid
      have hcut : cutoff x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ≠ 0 := by
        intro hz
        apply hw
        rw [hnode, hz, Complex.ofReal_zero, zero_mul, zero_mul]
      have hdiv : 0 < MovingSlotReversal.naturalProduct value u ∧
          MovingSlotReversal.naturalProduct value u ∣ P := by
        by_contra hd
        apply hcut
        change (if 0 < MovingSlotReversal.naturalProduct value u ∧
          MovingSlotReversal.naturalProduct value u ∣ historyPivot sys x t.1 _ _ then _ else 0) = 0
        rw [hvalid.historyPivot_eq]
        exact ite_eq_right hd
      let p := P / MovingSlotReversal.naturalProduct value u
      have hP : P = MovingSlotReversal.naturalProduct value u * p :=
        (Nat.mul_div_cancel' hdiv.2).symm
      have hrel : left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
          right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
          s * ((MovingSlotReversal.naturalProduct value u * p : ℕ) : ℤ) := by
        simpa only [sys, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct,
          x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root, hP, Int.cast_natCast] using hvalid.relation
      have hnat : (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR = p := by
        unfold MovingSlotReversal.naturalPivot movingGiantPivot
        simp only [MovingSlotData.step, Nat.mul_one]
        rw [reconstructedPivot_of_eq _ _ (by simpa only [← hT.1] using hvalid.root_ne_zero)
          (MovingSlotReversal.naturalProduct value u * p) hrel]
        exact Nat.mul_div_cancel_left p hdiv.1
      rw [recursiveTransferWeight_node _ _ _ _ _ _ P hvalid, hnode]
      change (cutoff x t.1 _ _ : ℂ) *
          recursiveTransferWeight sys (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
            cutoff n ⟨n, left, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
            cutoff n ⟨n, right, p, XR⟩ t.2.2) =
        ((cutoff x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cutoff n ⟨n, left, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys F cutoff n ⟨n, right, p, XR⟩ t.2.2)) * _
      rw [ihL t.2.1 hT.2.1 p XL, ihR t.2.2 hT.2.2 p XR]
      rw [movingSlotSpectator, hnat]
      by_cases hp : (p : ZMod q) = 0
      · rw [ite_eq_left hp, mul_zero, movingSlotSpectator_zero value g hg D left p XL (Or.inl hp), mul_zero, mul_zero]
        simp only [zero_mul]
      · rw [ite_eq_right hp, star_mul]
        ring

end Ostmann

end OAI
