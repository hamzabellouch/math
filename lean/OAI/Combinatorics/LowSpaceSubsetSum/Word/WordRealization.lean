import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRejection
import OAI.Combinatorics.LowSpaceSubsetSum.Search.StoppedSamplerLaw

namespace OAI

/-! # Exact fair-word refinements of the stopped sampler constructors -/

noncomputable section
namespace LowSpaceSubsetSum.WordRealization

open WordProgram
attribute [local instance] Classical.propDecidable

structure Realization (w N : ℕ) {α : Type} [Fintype α] (S : SamplerCoupling α) where
  program : Program w (Option α)
  faithful : ∀ P, WordProgram.probability program P = S.boundedLaw.probability P
  bounded : WordProgram.Bounded program N

variable {w N M : ℕ} {α β : Type} [Fintype α] [Fintype β]

def pure (a : α) : Realization w 0 (SamplerCoupling.pure a) where
  program := .pure (some a)
  faithful P := by
    change (if P (some a) then (1 : ℝ) else 0) =
      ((FiniteLaw.uniform (Ω := Unit)).map (fun _ => some a)).probability P
    rw [FiniteLaw.map_probability]
    by_cases h : P (some a)
    · simp only [h, ↓reduceIte, FiniteLaw.probability_true]
    · simp only [h, ↓reduceIte, FiniteLaw.probability, Finset.sum_const_zero]
  bounded := Bounded.pure _ 0

def map {S : SamplerCoupling α} (X : Realization w N S) (f : α → β) :
    Realization w N (S.map f) where
  program := WordProgram.map (Option.map f) X.program
  faithful P := by
    rw [WordProgram.probability_map, X.faithful]
    dsimp only [SamplerCoupling.boundedLaw, SamplerCoupling.map]
    rw [FiniteLaw.map_probability, FiniteLaw.map_probability]

  bounded := by
    simpa only [WordProgram.map, Nat.add_zero] using
      WordProgram.bind_bound X.program N X.bounded (fun a => .pure (a.map f)) 0
        (fun _ => Bounded.pure _ 0)

def continuation (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (Y : ∀ a, Realization w M (T a)) :
    Option α → Program w (Option (Sigma B))
  | none => .pure none
  | some a => WordProgram.map (Option.map (fun b => ⟨a,b⟩)) (Y a).program

omit [Fintype α] in
theorem continuation_probability (B : α → Type) [∀ a, Fintype (B a)]
    (T : ∀ a, SamplerCoupling (B a)) (Y : ∀ a, Realization w M (T a))
    (P : Option (Sigma B) → Prop) (a : Option α) :
    WordProgram.probability (continuation B T Y a) P =
      StoppedSamplerLaw.nextProbability B T P a := by
  cases a with
  | none => rfl
  | some a =>
    exact (WordProgram.probability_map _ (Y a).program P).trans ((Y a).faithful _)

def bind {S : SamplerCoupling α} (X : Realization w N S)
    (B : α → Type) [∀ a, Fintype (B a)] (T : ∀ a, SamplerCoupling (B a))
    (Y : ∀ a, Realization w M (T a)) : Realization w (N+M) (S.bind B T) where
  program := WordProgram.bind X.program (continuation B T Y)
  faithful P := by
    change WordProgram.expectation (WordProgram.bind X.program (continuation B T Y))
      (fun x => if P x then 1 else 0) = _
    rw [WordProgram.expectation_bind]
    change WordProgram.expectation X.program
      (fun a => WordProgram.probability (continuation B T Y a) P) = _
    simp only [continuation_probability]
    rw [WordProgram.expectation_of_probability X.program S.boundedLaw X.faithful]
    exact (StoppedSamplerLaw.bind_probability S B T P).symm
  bounded := by
    apply WordProgram.bind_bound X.program N X.bounded _ M
    intro a
    cases a with
    | none => exact Bounded.pure none M
    | some a =>
      simpa only [continuation, WordProgram.map, Nat.add_zero] using
        WordProgram.bind_bound (Y a).program M (Y a).bounded
          (fun x => .pure (x.map (fun b => (⟨a,b⟩ : Sigma B)))) 0 (fun _ => Bounded.pure _ 0)

def rejection (w k : ℕ) (hk : k ≤ w) (N : ℕ)
    (A : Fin (2^k) → Prop) [DecidablePred A] [Nonempty {a : Fin (2^k) // A a}] :
    Realization w N (firstAcceptCoupling A N) where
  program := WordRejection.sample w k N A
  faithful := WordRejection.sample_probability w k hk N A
  bounded := WordRejection.sample_bounded w k N A

end LowSpaceSubsetSum.WordRealization

end

end OAI
