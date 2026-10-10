import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasured

namespace OAI

/-! # Dependent generation with access to the preceding stored seed

This variant permits the next stage to run the already counted layout or
parameter preparation on the actual preceding seed. Its charge is part of
that stage's Execution, rather than an implicit evaluation of ideal data.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

variable {w N M : ℕ} {α : Type} [Fintype α]

def firstAccepted {S : SamplerCoupling α} (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (a : Accepted (S.bind B T)) : Accepted S where
  seed := ⟨a.seed.val.1,by
    rcases S.agrees a.seed.val.1 with hn | hs
    · have h := WordSeedRealization.successful_agrees a.seed
      simp only [SamplerCoupling.bind,hn,↓reduceIte] at h
      contradiction
    · exact ⟨_,hs⟩⟩
  value := a.value.1
  correct := congrArg Sigma.fst a.correct

def bindSeedRun {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) (F : ∀ a : Accepted S, Execution (Y a.value))
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) : Result (S.bind B T) :=
  let r := E.run stream cursor
  match r.accepted with
  | none => ⟨none,r.cursor,r.work+1,r.cells,r.retained⟩
  | some a =>
      let t := (F a).run stream r.cursor
      ⟨t.accepted.map (pairAccepted B T a),t.cursor,r.work+t.work+2,
        max r.cells (r.retained+t.cells+8),r.retained+t.retained+8⟩

def bindSeed {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) (F : ∀ a : Accepted S, Execution (Y a.value)) :
    Execution (WordSeedRealization.bind X B T Y) where
  run := bindSeedRun E B T Y F
  value stream cursor := by
    have hr := E.value stream cursor
    rw [WordSeedRealization.bind,WordSeedRejectionExecution.program_run_bind,←hr]
    cases ha : (E.run stream cursor).accepted with
    | none => simp only [bindSeedRun,ha,Option.map_none,continuation,WordProgram.run]
    | some a =>
      rcases a with ⟨s,a,ha'⟩
      subst a
      have ht := (F ⟨s,S.ideal s.val,rfl⟩).value stream (E.run stream cursor).cursor
      simp only [bindSeedRun,ha,Option.map_some,continuation,
        WordSeedRejectionExecution.program_run_map,←ht]
      cases hb : ((F ⟨s,S.ideal s.val,rfl⟩).run stream
          (E.run stream cursor).cursor).accepted <;>
        simp only [Option.map_none,Option.map_some,pairAccepted]

theorem bindSeed_bounded {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) (F : ∀ a : Accepted S, Execution (Y a.value))
    (W C R V D Q : ℕ) (hE : E.Bounded W C R)
    (hF : ∀ a, (F a).Bounded V D Q) :
    (bindSeed E B T Y F).Bounded (W+V+2) (max C (R+D+8)) (R+Q+8) := by
  intro stream cursor
  have he := hE stream cursor
  cases ha : (E.run stream cursor).accepted with
  | none =>
    simp only [bindSeed,bindSeedRun,ha]
    exact ⟨by omega,he.2.1.trans (le_max_left _ _),by omega⟩
  | some a =>
    have hf := hF a stream (E.run stream cursor).cursor
    simp only [bindSeed,bindSeedRun,ha]
    exact ⟨by omega,max_le_max he.2.1 (by omega),by omega⟩

def prepareThen {P : Type} {S : SamplerCoupling α} {X : Realization w N S}
    (prepare : Unit → (P × ℕ) × ℕ) (next : P → Execution X) : Execution X where
  run stream cursor :=
    let prepared := prepare ()
    let out := (next prepared.1.1).run stream cursor
    ⟨out.accepted,out.cursor,prepared.1.2+out.work+2,
      max prepared.2 (prepared.2+out.cells+8),prepared.2+out.retained+8⟩
  value stream cursor := (next (prepare ()).1.1).value stream cursor

theorem prepareThen_bounded {P : Type} {S : SamplerCoupling α} {X : Realization w N S}
    (prepare : Unit → (P × ℕ) × ℕ) (next : P → Execution X)
    (W C V D Q : ℕ) (hW : (prepare ()).1.2 ≤ W) (hC : (prepare ()).2 ≤ C)
    (hNext : ∀ p, (next p).Bounded V D Q) :
    (prepareThen prepare next).Bounded (W+V+2) (C+D+8) (C+Q+8) := by
  intro stream cursor
  have h := hNext (prepare ()).1.1 stream cursor
  change _+_+2 ≤ _ ∧ max _ (_+_+8) ≤ _ ∧ _+_+8 ≤ _
  exact ⟨by omega,max_le (by omega) (by omega),by omega⟩

/-- The concrete cached value is the successful sampler output. -/
theorem accepted_source {S : SamplerCoupling α} (a : Accepted S) :
    S.bounded a.seed.val = some a.value :=
  (WordSeedRealization.successful_agrees a.seed).trans (congrArg some a.correct.symm)

def mapStoredRun {β : Type} [Fintype β] {S : SamplerCoupling α}
    {X : Realization w N S} (E : Execution X) (f : α → β)
    (compute : Accepted S → (β × ℕ) × ℕ)
    (hc : ∀ a, (compute a).1.1 = f a.value)
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) : Result (S.map f) :=
  let r := E.run stream cursor
  match r.accepted with
  | none => ⟨none,r.cursor,r.work+1,r.cells,r.retained⟩
  | some a =>
      let b := compute a
      ⟨some (mapAccepted f a b.1.1 (hc a)),r.cursor,
        r.work+b.1.2+2,max r.cells (r.retained+b.2+8),r.retained+b.2+8⟩

def mapStored {β : Type} [Fintype β] {S : SamplerCoupling α}
    {X : Realization w N S} (E : Execution X) (f : α → β)
    (compute : Accepted S → (β × ℕ) × ℕ)
    (hc : ∀ a, (compute a).1.1 = f a.value) :
    Execution (WordSeedRealization.map X f) where
  run := mapStoredRun E f compute hc
  value stream cursor := by
    have h := E.value stream cursor
    rw [WordSeedRealization.map,WordSeedRejectionExecution.program_run_map,←h]
    cases ha : (E.run stream cursor).accepted <;>
      simp only [mapStoredRun,ha,Option.map_none,Option.map_some,mapAccepted]

theorem mapStored_bounded {β : Type} [Fintype β] {S : SamplerCoupling α}
    {X : Realization w N S} (E : Execution X) (f : α → β)
    (compute : Accepted S → (β × ℕ) × ℕ) (hc : ∀ a, (compute a).1.1 = f a.value)
    (W C R F H : ℕ) (hE : E.Bounded W C R)
    (hF : ∀ a, (compute a).1.2 ≤ F) (hH : ∀ a, (compute a).2 ≤ H) :
    (mapStored E f compute hc).Bounded (W+F+2) (max C (R+H+8)) (R+H+8) := by
  intro stream cursor
  have hr := hE stream cursor
  dsimp only [mapStored,mapStoredRun]
  split
  · dsimp only
    exact ⟨by omega,hr.2.1.trans (le_max_left _ _),by omega⟩
  next a ha =>
    dsimp only
    have hf := hF a
    have hh := hH a
    exact ⟨by omega,max_le_max hr.2.1 (by omega),by omega⟩

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
