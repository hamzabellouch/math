import OAI.Computability.PerfectCompleteness.Foundations.TerminalCalls
import OAI.Computability.PerfectCompleteness.Sampling.BucketSampler

namespace OAI


namespace PerfectCompleteness.WholeCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

def Index (rows repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | m, _, .refl _ => Fin (rows m)
  | n + 1, _, .step i p =>
      (BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
        Index rows repeats p

instance indexFintype (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (Index rows repeats p) := by
  induction p with
  | refl m => exact inferInstanceAs (Fintype (Fin (rows m)))
  | @step n m i p ih =>
      letI : Fintype (Index rows repeats p) := ih
      exact inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
          Index rows repeats p))

def directRow (rows repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    Fin (rows m) → Index rows repeats p
  | _, _, .refl _, q => q
  | _, _, .step _ p, q => Sum.inr (directRow rows repeats p q)

theorem directRow_injective (rows repeats : Nat → Nat) (p : Path branch n m) :
    Function.Injective (directRow rows repeats p) := by
  induction p with
  | refl m => exact fun _ _ h => h
  | step i p ih =>
      intro a b h
      exact ih (Sum.inr.inj h)

theorem root_ne_lower (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (root : BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p))
    (lower : Index rows repeats p) :
    (Sum.inl root : Index rows repeats (.step i p)) ≠ Sum.inr lower := by
  intro h
  cases h

theorem direction_card (ℓ : Nat) :
    Fintype.card (BucketSampler.Direction ℓ) = 2 ^ ℓ - 1 := by
  have h : 2 ^ ℓ = 1 + Fintype.card (BucketSampler.Direction ℓ) := by
    simpa [BucketSampler.Direction, BucketSampler.F2] using
      Fintype.sum_eq_add_sum_subtype_ne (fun _ : Fin ℓ → BucketSampler.F2 => (1 : Nat)) 0
  omega

@[simp] theorem card_refl (rows repeats : Nat → Nat) :
    Fintype.card (Index (branch := branch) rows repeats (.refl m)) = rows m := by
  exact Fintype.card_fin (rows m)

theorem card_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) :
    Fintype.card (Index rows repeats (.step i p)) =
      (2 ^ rows (n + 1) - 1) * Fintype.card (TerminalIndex repeats (.step i p)) +
        Fintype.card (Index rows repeats p) := by
  change Fintype.card
    ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
      Index rows repeats p) = _
  rw [Fintype.card_sum, Fintype.card_prod, direction_card]

theorem card_eq_formula (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (Index rows repeats p) = rows m +
      ∑ h ∈ Finset.Ioc m n, (2 ^ rows h - 1) *
        ∏ k ∈ Finset.Ioc m h, 2 * repeats k := by
  induction p with
  | refl m => simp only [card_refl, Finset.Ioc_self, Finset.sum_empty, Nat.add_zero]
  | @step n m i p ih =>
      rw [card_step, TerminalCalls.card_eq_prod, ih,
        Finset.sum_Ioc_succ_top p.height_le]
      omega

end
end PerfectCompleteness.WholeCutCalls



namespace PerfectCompleteness.OriginalCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

def Index (rows repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | m, _, .refl _ => BucketSampler.Direction (rows m)
  | n + 1, _, .step i p =>
      (BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
        Index rows repeats p

instance indexFintype (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (Index rows repeats p) := by
  induction p with
  | refl m => exact inferInstanceAs (Fintype (BucketSampler.Direction (rows m)))
  | @step n m i p ih =>
      letI : Fintype (Index rows repeats p) := ih
      exact inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
          Index rows repeats p))

def ownBucket (rows repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    BucketSampler.Direction (rows m) → Index rows repeats p
  | _, _, .refl _, v => v
  | _, _, .step _ p, v => Sum.inr (ownBucket rows repeats p v)

theorem ownBucket_injective (rows repeats : Nat → Nat) (p : Path branch n m) :
    Function.Injective (ownBucket rows repeats p) := by
  induction p with
  | refl m => exact fun _ _ h => h
  | step i p ih =>
      intro a b h
      exact ih (Sum.inr.inj h)

def rootCall (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (origin : BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) :
    Index rows repeats (.step i p) := Sum.inl origin

def lowerCall (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n m)
    (origin : Index rows repeats p) : Index rows repeats (.step i p) := Sum.inr origin

theorem rootCall_injective (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) : Function.Injective (rootCall rows repeats i p) := by
  intro a b h
  exact Sum.inl.inj h

theorem lowerCall_injective (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) : Function.Injective (lowerCall rows repeats i p) := by
  intro a b h
  exact Sum.inr.inj h

theorem root_ne_lower (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (root : BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p))
    (lower : Index rows repeats p) :
    rootCall rows repeats i p root ≠ lowerCall rows repeats i p lower := by
  intro h
  cases h

theorem root_ne_ownBucket (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (root : BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p))
    (own : BucketSampler.Direction (rows m)) :
    rootCall rows repeats i p root ≠ ownBucket rows repeats (.step i p) own :=
  root_ne_lower rows repeats i p root (ownBucket rows repeats p own)

theorem rootCall_mk_eq_iff (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (v w : BucketSampler.Direction (rows (n + 1)))
    (a b : TerminalIndex repeats (.step i p)) :
    rootCall rows repeats i p (v, a) = rootCall rows repeats i p (w, b) ↔
      v = w ∧ a = b := by
  constructor
  · intro h
    have hp := rootCall_injective rows repeats i p h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem card_refl (rows repeats : Nat → Nat) :
    Fintype.card (Index (branch := branch) rows repeats (.refl m)) = 2 ^ rows m - 1 :=
  WholeCutCalls.direction_card (rows m)

theorem card_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) :
    Fintype.card (Index rows repeats (.step i p)) =
      (2 ^ rows (n + 1) - 1) * Fintype.card (TerminalIndex repeats (.step i p)) +
        Fintype.card (Index rows repeats p) := by
  change Fintype.card
    ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
      Index rows repeats p) = _
  rw [Fintype.card_sum, Fintype.card_prod, WholeCutCalls.direction_card]

theorem card_eq_formula (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (Index rows repeats p) = (2 ^ rows m - 1) +
      ∑ h ∈ Finset.Ioc m n, (2 ^ rows h - 1) *
        ∏ k ∈ Finset.Ioc m h, 2 * repeats k := by
  induction p with
  | refl m => simp only [card_refl, Finset.Ioc_self, Finset.sum_empty, Nat.add_zero]
  | @step n m i p ih =>
      rw [card_step, TerminalCalls.card_eq_prod, ih,
        Finset.sum_Ioc_succ_top p.height_le]
      omega

def count (rows repeats : Nat → Nat) (root cutoff : Nat) : Nat :=
  (2 ^ rows cutoff - 1) +
    ∑ h ∈ Finset.Ioc cutoff root, (2 ^ rows h - 1) *
      ∏ k ∈ Finset.Ioc cutoff h, 2 * repeats k

theorem card_eq_count (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (Index rows repeats p) = count rows repeats n m :=
  card_eq_formula rows repeats p

theorem card_branch_independent {branch' : Nat → Nat}
    (rows repeats : Nat → Nat) (p : Path branch n m) (q : Path branch' n m) :
    Fintype.card (Index rows repeats p) = Fintype.card (Index rows repeats q) := by
  rw [card_eq_count, card_eq_count]

end
end PerfectCompleteness.OriginalCutCalls

end OAI
