import OAI.NumberTheory.Ostmann.Construction.FinalReassignmentInteraction

namespace OAI

/-! # The anchor coefficients through their actual creation and later copies -/

namespace Ostmann

/-- The incoming anchor edge before normalization by the bulk parity. -/
def anchorIncoming {n : ℕ} (α : Fin n → ℤ) (t : Fin n → Bool)
    (j : Fin n) (b : Bool) : ℤ :=
  finalCopyParity t * anchorCodeEntry α t j b

theorem copyPathParity_snoc_prefix {n : ℕ} (t : Fin n → Bool) (b : Bool)
    (j : ℕ) (hj : j ≤ n) :
    copyPathParity (finiteCopyPath (Fin.snoc t b)) j = copyPathParity (finiteCopyPath t) j := by
  apply copyPathParity_congr_prefix
  intro h hh
  have hhn : h < n := lt_of_lt_of_le hh hj
  simp only [finiteCopyPath, hhn, Nat.lt_succ_of_lt hhn, dite_true]
  exact @Fin.snoc_castSucc n (fun _ => Bool) b t ⟨h, hhn⟩

theorem anchorCodeEntry_snoc {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) (j : Fin n) :
    anchorCodeEntry α (Fin.snoc t u) j.castSucc b =
      anchorCodeEntry (fun j => α j.castSucc) t j b := by
  have hp := copyPathParity_snoc_prefix t u j (Nat.le_of_lt j.isLt)
  simp only [anchorCodeEntry, finiteAnchorCode, Fin.val_castSucc, hp,
    @Fin.snoc_castSucc n (fun _ => Bool) u t j]

/-- This is exactly the outside-anchor row of `transferredGraph`: every
later copy multiplies its incoming coefficient by that copy's sign. -/
theorem anchorIncoming_snoc_old {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) (j : Fin n) :
    anchorIncoming α (Fin.snoc t u) j.castSucc b =
      transferCopySign u * anchorIncoming (fun j => α j.castSucc) t j b := by
  unfold anchorIncoming
  rw [finalCopyParity_snoc, anchorCodeEntry_snoc, mul_assoc]

theorem anchorIncoming_snoc_new {n : ℕ} (α : Fin (n + 1) → ℤ)
    (t : Fin n → Bool) (u b : Bool) :
    anchorIncoming α (Fin.snoc t u) (Fin.last n) b =
      (transferCopySign u * finalCopyParity t) *
        (if b then (anchorSignPair (α (Fin.last n)) (finalCopyParity t) u).1
         else (anchorSignPair (α (Fin.last n)) (finalCopyParity t) u).2) := by
  have hp := copyPathParity_snoc_prefix t u n le_rfl
  unfold anchorIncoming
  rw [finalCopyParity_snoc]
  congr 1
  simp only [anchorCodeEntry, finiteAnchorCode, Fin.val_last, hp,
    @Fin.snoc_last n (fun _ => Bool) u t]
  rfl

/-- At its reserved step the unnormalized coefficient is precisely the
edge created by the graph transfer, for either clone of the fresh anchor. -/
theorem anchorIncoming_created_by_transfer {H Y : Type*}
    (graph : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (a i : H)
    {n : ℕ} (α : Fin (n + 1) → ℤ) (t : Fin n → Bool) (u b : Bool)
    (hincoming : graph (some (.inl a)) (some (.inl i)) = finalCopyParity t)
    (hpivot : graph (some (.inl a)) none = α (Fin.last n)) :
    anchorIncoming α (Fin.snoc t u) (Fin.last n) b =
      transferredGraph graph (.inl (b, a)) (.inl (u, i)) := by
  have hs := copyPathParity_sign (finiteCopyPath t) n
  change finalCopyParity t = 1 ∨ finalCopyParity t = -1 at hs
  have hpair := transferred_anchor_pair graph a i (α (Fin.last n)) (finalCopyParity t)
    hs hincoming hpivot u
  rw [anchorIncoming_snoc_new]
  have hsq : (transferCopySign u * finalCopyParity t) ^ 2 = 1 := by
    rw [mul_pow, transferCopySign_sq]
    rcases hs with hs | hs <;> simp only [hs] <;> norm_num
  cases b
  · have he := congrArg Prod.snd hpair
    dsimp only at he
    simp only [Bool.false_eq_true, ite_false]
    rw [← he]
    rw [← mul_assoc, ← pow_two, hsq, one_mul]
  · have he := congrArg Prod.fst hpair
    dsimp only at he
    simp only [ite_true]
    rw [← he]
    rw [← mul_assoc, ← pow_two, hsq, one_mul]

end Ostmann

end OAI
