import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ParentPrefixSearch
import OAI.Combinatorics.LowSpaceSubsetSum.Search.Watchdog

namespace OAI

/-! # Explicit pending-sibling stack for prefix recomputation

A collector result is inspected and discarded in one task action. A frame
contains only the next restriction and remaining index order. In particular,
no overflowing dictionary or reader state is retained in a frame. Task
execution inside this action is accounted for separately by the join ledger.
-/

namespace LowSpaceSubsetSum.PrefixMachine

variable {n : ℕ}

structure Job (n : ℕ) where
  order : List (Fin n)
  restriction : MaskRestriction n

inductive Control (n : ℕ)
  | eval : Job n → List (Job n) → Control n
  | ret : Bool → List (Job n) → Control n

namespace Control

def stack : Control n → List (Job n)
  | .eval _ pending => pending
  | .ret _ pending => pending

/-- Masks and an order pointer can use fewer cells. Counting every mask bit
and every remaining order element still gives this conservative bound. -/
def cells (s : Control n) : ℕ := (4 * n + 16) * (s.stack.length + 1)

end Control

def step (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) : Control n → Watchdog.Transition (Control n)
  | .eval job pending =>
    let out := ({ D with maskRestriction := job.restriction }.collect B).state.user
    if out.keys.overflow then
      match job.order with
      | [] => .next (.ret false pending)
      | i :: rest => .next (.eval ⟨rest, job.restriction.force i false⟩
          (⟨rest, job.restriction.force i true⟩ :: pending))
    else .next (.ret (check out.records) pending)
  | .ret true _ => .halt true
  | .ret false [] => .halt false
  | .ret false (job :: pending) => .next (.eval job pending)

def GoodStack (N : ℕ) (pending : List (Job n)) : Prop :=
  pending.Pairwise (fun a b => a.order.length < b.order.length) ∧
    ∀ job ∈ pending, job.order.length ≤ N

def Invariant (N : ℕ) : Control n → Prop
  | .eval job pending => GoodStack N pending ∧ job.order.length ≤ N ∧
      ∀ next ∈ pending, job.order.length ≤ next.order.length
  | .ret _ pending => GoodStack N pending

theorem goodStack_length {N : ℕ} {pending : List (Job n)} (h : GoodStack N pending) :
    pending.length ≤ N + 1 := by
  have hpair : (pending.map (fun j => j.order.length)).Pairwise (· < ·) :=
    List.pairwise_map.mpr h.1
  have hnd : (pending.map (fun j => j.order.length)).Nodup :=
    hpair.imp (fun hlt => Nat.ne_of_lt hlt)
  have hsub : (pending.map (fun j => j.order.length)).toFinset ⊆ Finset.range (N + 1) := by
    intro r hr
    obtain ⟨job, hj, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h.2 job hj))
  have hc := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_range] using hc

theorem invariant_next (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) (N : ℕ) (s t : Control n)
    (hs : Invariant N s) (ht : step D B check s = .next t) : Invariant N t := by
  cases s with
  | eval job pending =>
    obtain ⟨hstack, hjob, hhead⟩ := hs
    simp only [step] at ht
    split at ht
    · cases ho : job.order with
      | nil =>
        simp only [ho] at ht
        cases ht
        exact hstack
      | cons i rest =>
        simp only [ho] at ht
        cases ht
        have hlen : rest.length + 1 = job.order.length := by simp [ho]
        refine ⟨⟨List.pairwise_cons.mpr ⟨?_, hstack.1⟩, ?_⟩, ?_, ?_⟩
        · intro next hn
          exact lt_of_lt_of_le (by omega : rest.length < job.order.length) (hhead next hn)
        · intro next hn
          rcases List.mem_cons.mp hn with rfl | hn
          · dsimp only; omega
          · exact hstack.2 next hn
        · dsimp only; omega
        · intro next hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact le_rfl
          · exact (show rest.length ≤ job.order.length by omega).trans (hhead next hn)
    · cases ht
      exact hstack
  | ret b pending =>
    cases b with
    | true => simp [step] at ht
    | false =>
      cases pending with
      | nil => simp [step] at ht
      | cons job pending =>
        simp only [step] at ht
        cases ht
        obtain ⟨hpair, hbound⟩ := hs
        obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
        refine ⟨⟨htail, fun j hj => hbound j (List.mem_cons_of_mem _ hj)⟩,
          hbound job (List.mem_cons_self), ?_⟩
        exact fun j hj => (hhead j hj).le

theorem cells_le (N : ℕ) (s : Control n) (hs : Invariant N s) :
    s.cells ≤ (4 * n + 16) * (N + 2) := by
  have hg : GoodStack N s.stack := by
    cases s with
    | eval job pending => exact hs.1
    | ret b pending => exact hs
  have hl := goodStack_length hg
  exact Nat.mul_le_mul_left _ (by omega)

def jobValue (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) (job : Job n) : Bool :=
  D.searchRight B check job.order job.restriction

def meaning (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) : Control n → Bool
  | .eval job pending => jobValue D B check job || pending.any (jobValue D B check)
  | .ret b pending => b || pending.any (jobValue D B check)

theorem step_meaning (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) (s : Control n) :
    match step D B check s with
    | .halt b => meaning D B check s = b
    | .next t => meaning D B check s = meaning D B check t := by
  cases s with
  | eval job pending =>
    cases job with
    | mk order P =>
      by_cases ho : ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = true
      · cases order with
        | nil => simp [step, ho, meaning, jobValue, RepresentationParentData.searchRight]
        | cons i rest =>
          simp only [step, ho, ↓reduceIte, meaning, List.any_cons, jobValue]
          rw [RepresentationParentData.searchRight]
          simp only [ho, ↓reduceIte]
          by_cases hv : D.searchRight B check rest (P.force i false) = true
          · simp only [hv, ↓reduceIte, Bool.true_or]
          · have hf : D.searchRight B check rest (P.force i false) = false := Bool.eq_false_iff.mpr hv
            simp [hf]
      · have hf : ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = false :=
          Bool.eq_false_iff.mpr ho
        rw [step]
        simp only [hf, Bool.false_eq_true, ↓reduceIte, meaning, jobValue]
        rw [RepresentationParentData.searchRight.eq_def]
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
  | ret b pending =>
    cases b <;> cases pending <;> simp [step, meaning]

theorem watchdog_sound (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) (Q : Prop)
    (hcheck : ∀ P, check ({ D with maskRestriction := P }.entries B) = true → Q)
    (job : Job n) (budget : ℕ)
    (hyes : Watchdog.accepted (Watchdog.run (step D B check) Control.cells
      budget (.eval job [])) = true) : Q := by
  apply Watchdog.sound (step D B check) Control.cells
    (fun s => meaning D B check s = true → Q) Q ?_ ?_ budget (.eval job []) ?_ hyes
  · intro s t hs ht h
    have hm := step_meaning D B check s
    rw [ht] at hm
    exact hs (hm.trans h)
  · intro s hs ht
    have hm := step_meaning D B check s
    rw [ht] at hm
    exact hs hm
  · intro h
    have hj : jobValue D B check job = true := by simpa only [meaning, List.any_nil, Bool.or_false] using h
    exact D.searchRight_sound B check Q hcheck job.order job.restriction hj

theorem watchdog_stack_peak (D : RepresentationParentData n) (B : ℕ)
    (check : Array (Entry (Fin n)) → Bool) (job : Job n) (budget : ℕ) :
    (Watchdog.run (step D B check) Control.cells budget (.eval job [])).peak ≤
      (4 * n + 16) * (job.order.length + 2) := by
  apply Watchdog.peak_le _ _ (Invariant job.order.length) _
    (invariant_next D B check job.order.length) (cells_le job.order.length)
  simp [Invariant, GoodStack]

end LowSpaceSubsetSum.PrefixMachine

end OAI
