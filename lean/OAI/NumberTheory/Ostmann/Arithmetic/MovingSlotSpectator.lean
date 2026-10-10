import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSystem
import OAI.NumberTheory.Ostmann.Construction.SpectatorWeightFactorization

namespace OAI

/-! # Spectator factorization for the source moving-giant coefficient -/

namespace Ostmann
open scoped Classical

def movingSlotModulus {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ regular, XL, XR⟩ => XL * XR * MovingSlotReversal.naturalProduct value regular
  | ⟨_ + 1, .node _ CL CR _ _ _, XL, XR⟩ =>
      XL * XR * MovingSlotReversal.naturalProduct value (CL ++ CR)

noncomputable def movingSlotSpectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf s regular, XL, XR =>
      g ((s : ZMod q) / ((D : ZMod q) *
        ((XL * XR * MovingSlotReversal.naturalProduct value regular : ℕ) : ZMod q)))
  | _, .node s CL CR u left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      if (p : ZMod q) = 0 then 0 else
        movingSlotSpectator value g D left p XL * star (movingSlotSpectator value g D right p XR)

/-- The full smooth/guarded coefficient factors by the actual spectator
history. All original cutoffs stay in the first factor. -/
theorem movingSlotWeight_spectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (hextra : ∀ x s v w, extra x s v w ≠ 0 →
      (historyPivot (movingSlotSystem value childBound pivotBound) x s v w : ZMod q) ≠ 0)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ)
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
      have hinfo : (0 < MovingSlotReversal.naturalProduct value u ∧
          MovingSlotReversal.naturalProduct value u ∣ P) ∧
          extra x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ≠ 0 := by
        change (if 0 < MovingSlotReversal.naturalProduct value u ∧
          MovingSlotReversal.naturalProduct value u ∣ historyPivot sys x t.1
            (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
          then extra x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) else 0) ≠ 0 at hcut
        rw [hvalid.historyPivot_eq] at hcut
        split_ifs at hcut with hd
        · exact ⟨hd, hcut⟩
        · exact False.elim (hcut rfl)
      let p := P / MovingSlotReversal.naturalProduct value u
      have hP : P = MovingSlotReversal.naturalProduct value u * p :=
        (Nat.mul_div_cancel' hinfo.1.2).symm
      have hPq : (P : ZMod q) ≠ 0 := by
        have h := hextra x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hinfo.2
        rwa [hvalid.historyPivot_eq] at h
      have hpq : (p : ZMod q) ≠ 0 := by
        intro hp
        apply hPq
        rw [hP, Nat.cast_mul, hp, mul_zero]
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
        exact Nat.mul_div_cancel_left p hinfo.1.1
      rw [recursiveTransferWeight_node _ _ _ _ _ _ P hvalid, hnode]
      change (cutoff x t.1 _ _ : ℂ) *
          recursiveTransferWeight sys (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
            cutoff n ⟨n, left, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys (fun x s => F x s * spectatorHistoryLeaf (movingSlotModulus value) g D x s)
            cutoff n ⟨n, right, p, XR⟩ t.2.2) =
        ((cutoff x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cutoff n ⟨n, left, p, XL⟩ t.2.1 *
          star (recursiveTransferWeight sys F cutoff n ⟨n, right, p, XR⟩ t.2.2)) * _
      rw [ihL t.2.1 hT.2.1 p XL, ihR t.2.2 hT.2.2 p XR]
      rw [movingSlotSpectator, hnat, ite_eq_right hpq]
      simp only [star_mul]
      ring

end Ostmann

end OAI
