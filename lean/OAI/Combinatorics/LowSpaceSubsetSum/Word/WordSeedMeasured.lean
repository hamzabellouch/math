import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedRejectionExecution

namespace OAI

/-! # Measured seed generation with cached accepted outputs

Dependent continuations use the stored output of the preceding call.
The equality with its ideal value is used only for type transport. A map
must provide an actual measured evaluator; its work is added explicitly.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

variable {w N M : ℕ} {α β : Type} [Fintype α] [Fintype β]

structure Accepted (S : SamplerCoupling α) where
  seed : SuccessfulSeed S
  value : α
  correct : value = S.ideal seed.val

structure Result (S : SamplerCoupling α) where
  accepted : Option (Accepted S)
  cursor : ℕ
  work : ℕ
  cells : ℕ
  retained : ℕ

structure Execution {S : SamplerCoupling α} (X : Realization w N S) where
  run : (ℕ → Fin (2^w)) → ℕ → Result S
  value : ∀ stream cursor,
    ((run stream cursor).accepted.map Accepted.seed,(run stream cursor).cursor) =
      WordProgram.run stream X.program cursor

def Execution.Bounded {S : SamplerCoupling α} {X : Realization w N S}
    (E : Execution X) (W C R : ℕ) : Prop :=
  ∀ stream cursor, (E.run stream cursor).work ≤ W ∧
    (E.run stream cursor).cells ≤ C ∧ (E.run stream cursor).retained ≤ R

def pure (a : α) : Execution (WordSeedRealization.pure (w := w) a) where
  run _ cursor := ⟨some ⟨⟨(),a,rfl⟩,a,rfl⟩,cursor,1,4,4⟩
  value _ _ := rfl

theorem pure_bounded (a : α) : (pure (w := w) a).Bounded 1 4 4 :=
  fun _ _ => ⟨le_rfl,le_rfl,le_rfl⟩

def mapAccepted {S : SamplerCoupling α} (f : α → β) (a : Accepted S)
    (b : β) (hb : b = f a.value) : Accepted (S.map f) where
  seed := mapSeed f a.seed
  value := b
  correct := hb.trans (congrArg f a.correct)

def mapRun {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (f : α → β) (compute : α → (β × ℕ) × ℕ) (hc : ∀ a, (compute a).1.1 = f a)
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) : Result (S.map f) :=
  let r := E.run stream cursor
  match r.accepted with
  | none => ⟨none,r.cursor,r.work+1,r.cells,r.retained⟩
  | some a =>
      let b := compute a.value
      ⟨some (mapAccepted f a b.1.1 (hc a.value)),r.cursor,
        r.work+b.1.2+2,max r.cells (r.retained+b.2+8),r.retained+b.2+8⟩

def map {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (f : α → β) (compute : α → (β × ℕ) × ℕ) (hc : ∀ a, (compute a).1.1 = f a) :
    Execution (WordSeedRealization.map X f) where
  run := mapRun E f compute hc
  value stream cursor := by
    have h := E.value stream cursor
    rw [WordSeedRealization.map,WordSeedRejectionExecution.program_run_map,←h]
    cases ha : (E.run stream cursor).accepted <;>
      simp only [mapRun,ha,Option.map_none,Option.map_some,mapAccepted]

theorem map_bounded {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (f : α → β) (compute : α → (β × ℕ) × ℕ) (hc : ∀ a, (compute a).1.1 = f a)
    (W C R F H : ℕ) (hE : E.Bounded W C R)
    (hF : ∀ a, (compute a).1.2 ≤ F) (hH : ∀ a, (compute a).2 ≤ H) :
    (map E f compute hc).Bounded (W+F+2) (max C (R+H+8)) (R+H+8) := by
  intro stream cursor
  have hr := hE stream cursor
  dsimp only [map,mapRun]
  split
  · dsimp only
    exact ⟨by omega,hr.2.1.trans (le_max_left _ _),by omega⟩
  next a ha =>
    dsimp only
    have hf := hF a.value
    have hh := hH a.value
    exact ⟨by omega,max_le_max hr.2.1 (by omega),by omega⟩

def pairAccepted {S : SamplerCoupling α} (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (a : Accepted S) (b : Accepted (T a.value)) :
    Accepted (S.bind B T) where
  seed := pairSeed B T a.seed (a.correct ▸ b.seed)
  value := ⟨a.value,b.value⟩
  correct := by
    rcases a with ⟨s,a,ha⟩
    dsimp only at *
    subst a
    exact congrArg (Sigma.mk (S.ideal s.val)) b.correct

def bindRun {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) (F : ∀ a, Execution (Y a))
    (stream : ℕ → Fin (2^w)) (cursor : ℕ) : Result (S.bind B T) :=
  let r := E.run stream cursor
  match r.accepted with
  | none => ⟨none,r.cursor,r.work+1,r.cells,r.retained⟩
  | some a =>
      let t := (F a.value).run stream r.cursor
      ⟨t.accepted.map (pairAccepted B T a),t.cursor,r.work+t.work+2,
        max r.cells (r.retained+t.cells+8),r.retained+t.retained+8⟩

def bind {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) (F : ∀ a, Execution (Y a)) :
    Execution (WordSeedRealization.bind X B T Y) where
  run := bindRun E B T Y F
  value stream cursor := by
    have hr := E.value stream cursor
    rw [WordSeedRealization.bind,WordSeedRejectionExecution.program_run_bind,←hr]
    cases ha : (E.run stream cursor).accepted with
    | none => simp only [bindRun,ha,Option.map_none,continuation,WordProgram.run]
    | some a =>
      rcases a with ⟨s,a,ha'⟩
      subst a
      have ht := (F (S.ideal s.val)).value stream (E.run stream cursor).cursor
      simp only [bindRun,ha,Option.map_some,continuation,
        WordSeedRejectionExecution.program_run_map,←ht]
      cases hb : ((F (S.ideal s.val)).run stream (E.run stream cursor).cursor).accepted <;>
        simp only [Option.map_none,Option.map_some,pairAccepted]

theorem bind_bounded {S : SamplerCoupling α} {X : Realization w N S} (E : Execution X)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) (F : ∀ a, Execution (Y a))
    (W C R V D Q : ℕ) (hE : E.Bounded W C R) (hF : ∀ a, (F a).Bounded V D Q) :
    (bind E B T Y F).Bounded (W+V+2) (max C (R+D+8)) (R+Q+8) := by
  intro stream cursor
  have hr := hE stream cursor
  dsimp only [bind,bindRun]
  split
  · dsimp only
    exact ⟨by omega,hr.2.1.trans (le_max_left _ _),by omega⟩
  next a ha =>
    have ht := hF a.value stream (E.run stream cursor).cursor
    dsimp only
    exact ⟨by omega,max_le_max hr.2.1 (by omega),by omega⟩

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
