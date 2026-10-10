import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRealization

namespace OAI

/-! # Fair-word programs returning successful bounded sampler seeds

Failure returns no seed. Success retains the actual candidate tuples, so
the prepared algorithm can consume the bounded sampler seed type. Only the law
of the observed bounded output is asserted; unused backup coordinates
need not have their ideal distribution.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedRealization

open WordProgram
attribute [local instance] Classical.propDecidable

variable {w N M : ℕ} {α β : Type} [Fintype α] [Fintype β]

def SuccessfulSeed (S : SamplerCoupling α) :=
  {s : S.Seed // ∃ a, S.bounded s = some a}

def observe (S : SamplerCoupling α) (s : Option (SuccessfulSeed S)) : Option α :=
  s.bind (fun t => S.bounded t.val)

theorem successful_agrees {S : SamplerCoupling α} (s : SuccessfulSeed S) :
    S.bounded s.val = some (S.ideal s.val) := by
  rcases S.agrees s.val with hf | hs
  · obtain ⟨a,ha⟩ := s.property
    rw [ha] at hf
    contradiction
  · exact hs

theorem observe_some {S : SamplerCoupling α} (s : SuccessfulSeed S) :
    observe S (some s) = some (S.ideal s.val) := successful_agrees s

structure Realization (w N : ℕ) {α : Type} [Fintype α] (S : SamplerCoupling α) where
  program : Program w (Option (SuccessfulSeed S))
  faithful : ∀ P, WordProgram.probability (WordProgram.map (observe S) program) P =
    S.boundedLaw.probability P
  bounded : WordProgram.Bounded program N

theorem bind_assoc {A B C : Type} (p : Program w A)
    (f : A → Program w B) (g : B → Program w C) :
    WordProgram.bind (WordProgram.bind p f) g =
      WordProgram.bind p (fun a => WordProgram.bind (f a) g) := by
  induction p with
  | pure a => rfl
  | draw next ih => simp only [WordProgram.bind,ih]

theorem map_bind {A B C : Type} (f : B → C) (p : Program w A)
    (next : A → Program w B) :
    WordProgram.map f (WordProgram.bind p next) =
      WordProgram.bind p (fun a => WordProgram.map f (next a)) := by
  exact bind_assoc p next (fun b => .pure (f b))

theorem bind_map {A B C : Type} (f : A → B) (p : Program w A)
    (next : B → Program w C) :
    WordProgram.bind (WordProgram.map f p) next =
      WordProgram.bind p (fun a => next (f a)) := by
  rw [WordProgram.map,bind_assoc]
  rfl

theorem map_map {A B C : Type} (g : B → C) (f : A → B) (p : Program w A) :
    WordProgram.map g (WordProgram.map f p) = WordProgram.map (fun a => g (f a)) p := by
  exact bind_map f p (fun b => .pure (g b))

def toRealization {S : SamplerCoupling α} (X : Realization w N S) :
    WordRealization.Realization w N S where
  program := WordProgram.map (observe S) X.program
  faithful := X.faithful
  bounded := by
    simpa only [WordProgram.map,Nat.add_zero] using
      WordProgram.bind_bound X.program N X.bounded
        (fun s => .pure (observe S s)) 0 (fun _ => Bounded.pure _ 0)

def pure (a : α) : Realization w 0 (SamplerCoupling.pure a) where
  program := .pure (some ⟨(),a,rfl⟩)
  faithful P := (WordRealization.pure (w := w) a).faithful P
  bounded := Bounded.pure _ 0

def mapSeed {S : SamplerCoupling α} (f : α → β) (s : SuccessfulSeed S) :
    SuccessfulSeed (S.map f) := by
  refine ⟨s.val,?_⟩
  obtain ⟨a,ha⟩ := s.property
  refine ⟨f a,?_⟩
  change (S.bounded s.val).map f = some (f a)
  rw [ha]
  rfl

theorem observe_map {S : SamplerCoupling α} (f : α → β) (s : Option (SuccessfulSeed S)) :
    observe (S.map f) (s.map (mapSeed f)) = (observe S s).map f := by
  cases s <;> rfl

def map {S : SamplerCoupling α} (X : Realization w N S) (f : α → β) :
    Realization w N (S.map f) where
  program := WordProgram.map (Option.map (mapSeed f)) X.program
  faithful P := by
    have he : WordProgram.map (observe (S.map f))
        (WordProgram.map (Option.map (mapSeed f)) X.program) =
      WordProgram.map (Option.map f) (toRealization X).program := by
      rw [map_map]
      change _ = WordProgram.map (Option.map f) (WordProgram.map (observe S) X.program)
      rw [map_map]
      congr 1
      funext s
      exact observe_map f s
    rw [he]
    exact (WordRealization.map (toRealization X) f).faithful P
  bounded := by
    simpa only [WordProgram.map,Nat.add_zero] using
      WordProgram.bind_bound X.program N X.bounded
        (fun s => .pure (s.map (mapSeed f))) 0 (fun _ => Bounded.pure _ 0)

def pairSeed {S : SamplerCoupling α} (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (s : SuccessfulSeed S)
    (t : SuccessfulSeed (T (S.ideal s.val))) : SuccessfulSeed (S.bind B T) := by
  refine ⟨⟨s.val,t.val⟩,?_⟩
  obtain ⟨b,hb⟩ := t.property
  refine ⟨⟨S.ideal s.val,b⟩,?_⟩
  simp only [SamplerCoupling.bind,successful_agrees s,Option.some_ne_none,↓reduceIte,hb,
    Option.map_some]

theorem observe_pair {S : SamplerCoupling α} (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (s : SuccessfulSeed S)
    (t : Option (SuccessfulSeed (T (S.ideal s.val)))) :
    observe (S.bind B T) (t.map (pairSeed B T s)) =
      (observe (T (S.ideal s.val)) t).map (fun b => (⟨S.ideal s.val,b⟩ : Sigma B)) := by
  cases t with
  | none => rfl
  | some t =>
    change (S.bind B T).bounded ⟨s.val,t.val⟩ =
      ((T (S.ideal s.val)).bounded t.val).map _
    simp only [SamplerCoupling.bind,successful_agrees s,Option.some_ne_none,↓reduceIte]

def continuation {S : SamplerCoupling α} (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (Y : ∀ a, Realization w M (T a)) :
    Option (SuccessfulSeed S) → Program w (Option (SuccessfulSeed (S.bind B T)))
  | none => .pure none
  | some s => WordProgram.map (Option.map (pairSeed B T s)) (Y (S.ideal s.val)).program

theorem continuation_observed {S : SamplerCoupling α}
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) (s : Option (SuccessfulSeed S)) :
    WordProgram.map (observe (S.bind B T)) (continuation B T Y s) =
      WordRealization.continuation B T (fun a => toRealization (Y a)) (observe S s) := by
  cases s with
  | none => rfl
  | some s =>
    rw [observe_some]
    simp only [continuation,WordRealization.continuation,toRealization,map_map]
    congr 1
    funext t
    exact observe_pair B T s t

def bind {S : SamplerCoupling α} (X : Realization w N S)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) : Realization w (N+M) (S.bind B T) where
  program := WordProgram.bind X.program (continuation B T Y)
  faithful P := by
    have he : WordProgram.map (observe (S.bind B T))
        (WordProgram.bind X.program (continuation B T Y)) =
      WordProgram.bind (toRealization X).program
        (WordRealization.continuation B T (fun a => toRealization (Y a))) := by
      rw [map_bind]
      change _ = WordProgram.bind (WordProgram.map (observe S) X.program) _
      rw [bind_map]
      congr 1
      funext s
      exact continuation_observed B T Y s
    rw [he]
    exact (WordRealization.bind (toRealization X) B T (fun a => toRealization (Y a))).faithful P
  bounded := by
    apply WordProgram.bind_bound X.program N X.bounded _ M
    intro s
    cases s with
    | none => exact Bounded.pure none M
    | some s =>
      simpa only [continuation,WordProgram.map,Nat.add_zero] using
        WordProgram.bind_bound (Y (S.ideal s.val)).program M (Y (S.ideal s.val)).bounded
          (fun t => .pure (t.map (pairSeed B T s))) 0 (fun _ => Bounded.pure _ 0)

end LowSpaceSubsetSum.WordSeedRealization

end

end OAI
