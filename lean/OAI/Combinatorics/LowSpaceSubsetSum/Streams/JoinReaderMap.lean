import OAI.Combinatorics.LowSpaceSubsetSum.Streams.JoinUserMap

namespace OAI

/-! # Stored-record erasure through buffered joins

The erasure maps both emitted records and reader cursors. Counters and stop
flags are preserved, so the work ledger can be transferred to the source
parent task without changing the order of equal-weight occurrences.
-/

namespace LowSpaceSubsetSum

universe u v s t w z
variable {α : Type u} {β : Type v} {σ : Type s} {σ' : Type t}
  {τ : Type w} {τ' : Type z}

namespace TieBuffer

def mapAll (f : α → β) (g : σ → σ') (r : Result α σ) : Result β σ' :=
  ⟨r.buffer.map f, g r.cursor, r.queries⟩

theorem fillAcc_map (f : α → β) (g : σ → σ')
    (read : σ → Option (α × σ)) (read' : σ' → Option (β × σ'))
    (hr : ∀ s, read' (g s) = (read s).map (Prod.map f g)) (key : β → ℤ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q : ℕ) :
    mapAll f g (fillAcc read (fun x => key (f x)) K fuel s buf q) =
      fillAcc read' key K fuel (g s) (buf.map f) q := by
  induction fuel generalizing s buf q with
  | zero => rfl
  | succ fuel ih =>
    cases h : read s with
    | none => simp only [fillAcc, hr, h, Option.map_none, mapAll]
    | some p =>
      rcases p with ⟨x, s'⟩
      simp only [fillAcc, hr, h, Option.map_some, Prod.map]
      split
      · simpa only [Array.map_push] using ih s' (buf.push x) (q + 1)
      · rfl

theorem fill_map (f : α → β) (g : σ → σ')
    (read : σ → Option (α × σ)) (read' : σ' → Option (β × σ'))
    (hr : ∀ s, read' (g s) = (read s).map (Prod.map f g)) (key : β → ℤ) (K : ℤ)
    (B : ℕ) (s : σ) :
    mapAll f g (fill read (fun x => key (f x)) K B s) = fill read' key K B (g s) :=
  by simpa only [fill, Array.map_empty] using fillAcc_map f g read read' hr key K B s #[] 0

theorem hasKey_map (f : α → β) (g : σ → σ')
    (read : σ → Option (α × σ)) (read' : σ' → Option (β × σ'))
    (hr : ∀ s, read' (g s) = (read s).map (Prod.map f g)) (key : β → ℤ)
    (K : ℤ) (s : σ) :
    hasKey read' key K (g s) = hasKey read (fun x => key (f x)) K s := by
  cases h : read s <;> simp only [hasKey, hr, h, Option.map_none, Option.map_some, Prod.map]

end TieBuffer

namespace TieReplay

def mapAll (g : σ → σ') (h : τ → τ') (r : Result σ τ) : Result σ' τ' :=
  ⟨g r.cursor, h r.state, r.queries, r.reports, r.complete, r.halted⟩

theorem runAcc_map (f : α → β) (g : σ → σ') (h : τ → τ')
    (read : σ → Option (α × σ)) (read' : σ' → Option (β × σ'))
    (hr : ∀ s, read' (g s) = (read s).map (Prod.map f g)) (key : β → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (report' : β → τ' → τ' × Bool)
    (hp : ∀ x a, report' (f x) (h a) = (h (report x a).1, (report x a).2))
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    mapAll g h (runAcc read (fun x => key (f x)) K report fuel s a q r) =
      runAcc read' key K report' fuel (g s) (h a) q r := by
  induction fuel generalizing s a q r with
  | zero => rfl
  | succ fuel ih =>
    cases hs : read s with
    | none => simp only [runAcc, hr, hs, Option.map_none, mapAll]
    | some p =>
      rcases p with ⟨x, s'⟩
      simp only [runAcc, hr, hs, Option.map_some, Prod.map]
      split
      · rw [hp]
        split
        · rfl
        · exact ih _ _ _ _
      · rfl

theorem run_map (f : α → β) (g : σ → σ') (h : τ → τ')
    (read : σ → Option (α × σ)) (read' : σ' → Option (β × σ'))
    (hr : ∀ s, read' (g s) = (read s).map (Prod.map f g)) (key : β → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (report' : β → τ' → τ' × Bool)
    (hp : ∀ x a, report' (f x) (h a) = (h (report x a).1, (report x a).2))
    (fuel : ℕ) (s : σ) (a : τ) :
    mapAll g h (run read (fun x => key (f x)) K report fuel s a) =
      run read' key K report' fuel (g s) (h a) :=
  runAcc_map f g h read read' hr key K report report' hp fuel s a 0 0

end TieReplay

namespace BufferReplay

theorem read_map (f : α → β) (xs : Array α) (i : ℕ) :
    read (xs.map f) i = (read xs i).map (Prod.map f id) := by
  simp only [read, Array.size_map]
  split <;> simp only [Option.map_some, Option.map_none, Array.getElem_map, Prod.map, id_eq]

theorem run_map (f : α → β) (key : β → ℤ) (K : ℤ)
    (report : β → τ → τ × Bool) (xs : Array α) (a : τ) :
    run (fun x => key (f x)) K (fun x => report (f x)) xs a =
      run key K report (xs.map f) a := by
  have h := TieReplay.run_map f id id (read xs) (read (xs.map f))
    (read_map f xs) key K (fun x => report (f x)) report (fun _ _ => rfl) xs.size 0 a
  cases he : TieReplay.run (read xs) (fun x => key (f x)) K
      (fun x => report (f x)) xs.size 0 a
  simpa only [run, he, TieReplay.mapAll, id_eq, Array.size_map] using h

end BufferReplay

namespace JoinOne

theorem run_map (f : α → β) (g : σ → σ')
    (read : σ → Option (α × σ)) (read' : σ' → Option (β × σ'))
    (hr : ∀ s, read' (g s) = (read s).map (Prod.map f g)) (key : β → ℤ) (K : ℤ)
    (report : β → τ → τ × Bool) (buffer : Array α) (saved : σ)
    (long : Bool) (fuel : ℕ) (a : τ) :
    TieReplay.mapAll g id
      (run read (fun x => key (f x)) K (fun x => report (f x)) buffer saved long fuel a) =
      run read' key K report (buffer.map f) (g saved) long fuel a := by
  simp only [run, BufferReplay.run_map f key K report]
  split
  · rfl
  · split
    · have h := TieReplay.run_map f g id read read' hr key K
        (fun x => report (f x)) report (fun _ _ => rfl) fuel saved
        (BufferReplay.run key K report (buffer.map f) a).state
      cases he : TieReplay.run read (fun x => key (f x)) K
          (fun x => report (f x)) fuel saved
          (BufferReplay.run key K report (buffer.map f) a).state
      simp only [he, TieReplay.mapAll, id_eq] at h
      rw [← h]
      rfl
    · rfl

end JoinOne

namespace TieGroup

variable {α' β' σ₁' σ₂' : Type*}

def mapReaders (g : σ → σ') (a : State σ τ) : State σ' τ :=
  ⟨g a.last, a.user, a.queries, a.reports, a.restores⟩

def mapReadersResult (g₁ : σ → σ₁') (g₂ : σ' → σ₂')
    (r : Result σ σ' τ) : Result σ₁' σ₂' τ :=
  ⟨TieReplay.mapAll g₁ (mapReaders g₂) r.outer,
    r.fillQueries, r.bufferSize, r.snapshot⟩

theorem step_mapReaders (f₁ : α → α') (f₂ : β → β') (g : σ → σ')
    (read : σ → Option (β × σ)) (read' : σ' → Option (β' × σ'))
    (hr : ∀ s, read' (g s) = (read s).map (Prod.map f₂ g)) (key : β' → ℤ) (K : ℤ)
    (report : α' → β' → τ → τ × Bool) (buffer : Array β) (saved : σ)
    (long : Bool) (fuel : ℕ) (x : α) (a : State σ τ) :
    (mapReaders g (step read (fun y => key (f₂ y)) K
        (fun x y => report (f₁ x) (f₂ y)) buffer saved long fuel x a).1,
      (step read (fun y => key (f₂ y)) K
        (fun x y => report (f₁ x) (f₂ y)) buffer saved long fuel x a).2) =
      step read' key K report (buffer.map f₂) (g saved) long fuel (f₁ x) (mapReaders g a) := by
  simp only [step, ← JoinOne.run_map f₂ g read read' hr key K (report (f₁ x))]
  rfl

theorem run_mapReaders (f₁ : α → α') (f₂ : β → β') (g₁ : σ → σ₁') (g₂ : σ' → σ₂')
    (read₁ : σ → Option (α × σ)) (read₁' : σ₁' → Option (α' × σ₁'))
    (read₂ : σ' → Option (β × σ')) (read₂' : σ₂' → Option (β' × σ₂'))
    (hr₁ : ∀ s, read₁' (g₁ s) = (read₁ s).map (Prod.map f₁ g₁))
    (hr₂ : ∀ s, read₂' (g₂ s) = (read₂ s).map (Prod.map f₂ g₂))
    (key₁ : α' → ℤ) (key₂ : β' → ℤ) (K : ℤ)
    (report : α' → β' → τ → τ × Bool) (B fuel₁ fuel₂ : ℕ)
    (s₁ : σ) (s₂ : σ') (a : τ) :
    mapReadersResult g₁ g₂
      (run read₁ (fun x => key₁ (f₁ x)) read₂ (fun y => key₂ (f₂ y)) K
        (fun x y => report (f₁ x) (f₂ y)) B fuel₁ fuel₂ s₁ s₂ a) =
      run read₁' key₁ read₂' key₂ K report B fuel₁ fuel₂ (g₁ s₁) (g₂ s₂) a := by
  let filled := TieBuffer.fill read₂ (fun y => key₂ (f₂ y)) K B s₂
  let long := TieBuffer.hasKey read₂ (fun y => key₂ (f₂ y)) K filled.cursor
  have hp := fun x st => (step_mapReaders f₁ f₂ g₂ read₂ read₂' hr₂ key₂ K
    report filled.buffer filled.cursor long fuel₂ x st).symm
  have hm := TieReplay.run_map f₁ g₁ (mapReaders g₂) read₁ read₁' hr₁ key₁ K
    (step read₂ (fun y => key₂ (f₂ y)) K (fun x y => report (f₁ x) (f₂ y))
      filled.buffer filled.cursor long fuel₂)
    (step read₂' key₂ K report (filled.buffer.map f₂) (g₂ filled.cursor) long fuel₂)
    hp fuel₁ s₁ ⟨filled.cursor, a, 0, 0, 0⟩
  simp only [run, mapReadersResult,
    ← TieBuffer.fill_map f₂ g₂ read₂ read₂' hr₂ key₂ K B s₂,
    TieBuffer.mapAll, Array.size_map,
    TieBuffer.hasKey_map f₂ g₂ read₂ read₂' hr₂ key₂ K,
    TieBuffer.hasKey_map f₁ g₁ read₁ read₁' hr₁ key₁ K]
  rw [hm]
  rfl

end TieGroup

namespace StreamJoin

variable {α' β' σ₁' σ₂' : Type*}

def mapReaders (g₁ : σ → σ₁') (g₂ : σ' → σ₂') (a : State σ σ' τ) : State σ₁' σ₂' τ :=
  ⟨g₁ a.left, g₂ a.right, a.user, a.queries, a.reports, a.copies, a.done⟩

def mapReadersStopped (g₁ : σ → σ₁') (g₂ : σ' → σ₂')
    (a : StoppedResult σ σ' τ) : StoppedResult σ₁' σ₂' τ :=
  ⟨mapReaders g₁ g₂ a.state, a.steps⟩

theorem step_mapReaders (f₁ : α → α') (f₂ : β → β') (g₁ : σ → σ₁') (g₂ : σ' → σ₂')
    (read₁ : σ → Option (α × σ)) (read₁' : σ₁' → Option (α' × σ₁'))
    (read₂ : σ' → Option (β × σ')) (read₂' : σ₂' → Option (β' × σ₂'))
    (hr₁ : ∀ s, read₁' (g₁ s) = (read₁ s).map (Prod.map f₁ g₁))
    (hr₂ : ∀ s, read₂' (g₂ s) = (read₂ s).map (Prod.map f₂ g₂))
    (key₁ : α' → ℤ) (key₂ : β' → ℤ) (report : α' → β' → τ → τ × Bool)
    (B fuel₁ fuel₂ : ℕ) (a : State σ σ' τ) :
    mapReaders g₁ g₂ (step read₁ (fun x => key₁ (f₁ x)) read₂ (fun y => key₂ (f₂ y))
      (fun x y => report (f₁ x) (f₂ y)) B fuel₁ fuel₂ a) =
      step read₁' key₁ read₂' key₂ report B fuel₁ fuel₂ (mapReaders g₁ g₂ a) := by
  by_cases hd : a.done = true
  · simp only [step, mapReaders, hd, ↓reduceIte]
  · cases h₁ : read₁ a.left with
    | none => simp only [step, mapReaders, hd, Bool.false_eq_true, ↓reduceIte,
        hr₁, h₁, Option.map_none]
    | some p₁ =>
      rcases p₁ with ⟨x, l⟩
      cases h₂ : read₂ a.right with
      | none => simp only [step, mapReaders, hd, Bool.false_eq_true, ↓reduceIte,
          hr₁, hr₂, h₁, h₂, Option.map_none, Option.map_some, Prod.map]
      | some p₂ =>
        rcases p₂ with ⟨y, r⟩
        simp only [step, mapReaders, hd, Bool.false_eq_true, ↓reduceIte,
          hr₁, hr₂, h₁, h₂, Option.map_some, Prod.map,
          ← TieGroup.run_mapReaders f₁ f₂ g₁ g₂ read₁ read₁' read₂ read₂' hr₁ hr₂
            key₁ key₂ (key₁ (f₁ x)) report B fuel₁ fuel₂,
          TieGroup.mapReadersResult, TieReplay.mapAll, TieGroup.mapReaders]
        split
        · rfl
        · split <;> rfl

theorem stoppedAcc_mapReaders (f₁ : α → α') (f₂ : β → β')
    (g₁ : σ → σ₁') (g₂ : σ' → σ₂')
    (read₁ : σ → Option (α × σ)) (read₁' : σ₁' → Option (α' × σ₁'))
    (read₂ : σ' → Option (β × σ')) (read₂' : σ₂' → Option (β' × σ₂'))
    (hr₁ : ∀ s, read₁' (g₁ s) = (read₁ s).map (Prod.map f₁ g₁))
    (hr₂ : ∀ s, read₂' (g₂ s) = (read₂ s).map (Prod.map f₂ g₂))
    (key₁ : α' → ℤ) (key₂ : β' → ℤ) (report : α' → β' → τ → τ × Bool)
    (B fuel₁ fuel₂ fuel : ℕ) (a : State σ σ' τ) :
    mapReadersStopped g₁ g₂ (stoppedAcc read₁ (fun x => key₁ (f₁ x))
      read₂ (fun y => key₂ (f₂ y)) (fun x y => report (f₁ x) (f₂ y)) B fuel₁ fuel₂ fuel a) =
      stoppedAcc read₁' key₁ read₂' key₂ report B fuel₁ fuel₂ fuel (mapReaders g₁ g₂ a) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    by_cases hd : a.done = true
    · simp only [stoppedAcc, mapReadersStopped, mapReaders, hd, ↓reduceIte]
    · have hdone : (mapReaders g₁ g₂ a).done = a.done := rfl
      have hm := ih (step read₁ (fun x => key₁ (f₁ x)) read₂ (fun y => key₂ (f₂ y))
        (fun x y => report (f₁ x) (f₂ y)) B fuel₁ fuel₂ a)
      simp only [stoppedAcc, hdone, hd, Bool.false_eq_true, ↓reduceIte]
      rw [← step_mapReaders f₁ f₂ g₁ g₂ read₁ read₁' read₂ read₂' hr₁ hr₂
        key₁ key₂ report B fuel₁ fuel₂, ← hm]
      rfl

end StreamJoin

end LowSpaceSubsetSum

end OAI
