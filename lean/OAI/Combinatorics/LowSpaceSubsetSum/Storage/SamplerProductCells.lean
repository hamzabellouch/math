import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerFinCells

namespace OAI

/-! # Sequential scalar-sampler products with retained seed storage

A failed first draw reserves the unread second seed without executing it.
A successful draw keeps its scalar result while running the second draw.
The reserve and component annotations are supplied by the concrete scalar
samplers; this lemma only accounts for product control and the two records.
-/

noncomputable section
namespace LowSpaceSubsetSum.SamplerProductCells

variable {α β : Type} [Fintype α] [Fintype β]
variable {S : SamplerCoupling α} {T : SamplerCoupling β}

def run (left : S.Seed → SamplerExecution.Trace α × ℕ)
    (right : T.Seed → SamplerExecution.Trace β × ℕ) (rightReserve : ℕ)
    (s : (S.prod T).Seed) : SamplerExecution.Trace (α × β) × ℕ :=
  let first := left s.1
  match first.1.value with
  | none => (⟨none, first.1.reads, first.1.tests⟩, first.2+rightReserve+16)
  | some a =>
    let second := right s.2
    (⟨second.1.value.map (fun b => (a,b)), first.1.reads+second.1.reads,
      first.1.tests+second.1.tests⟩, first.2+second.2+16)

theorem value (left : S.Seed → SamplerExecution.Trace α × ℕ)
    (right : T.Seed → SamplerExecution.Trace β × ℕ) (rightReserve : ℕ)
    (X : SamplerExecution.Execution S) (Y : SamplerExecution.Execution T)
    (hl : ∀ s, (left s).1 = X.run s) (hr : ∀ s, (right s).1 = Y.run s)
    (s : (S.prod T).Seed) :
    (run left right rightReserve s).1 = (SamplerExecution.prod X Y).run s := by
  cases h : (X.run s.1).value with
  | none => simp only [run, hl, h, SamplerExecution.prod, SamplerExecution.map,
      SamplerExecution.bind, ↓reduceIte, Option.map_none]
  | some a =>
    have hi := X.ideal_eq_of_some s.1 a h
    simp only [run, hl, hr, h, SamplerExecution.prod, SamplerExecution.map,
      SamplerExecution.bind, reduceCtorEq, ↓reduceIte, hi, Option.map_map]
    congr 2

theorem cells (left : S.Seed → SamplerExecution.Trace α × ℕ)
    (right : T.Seed → SamplerExecution.Trace β × ℕ) (L R : ℕ)
    (hl : ∀ s, (left s).2 ≤ L) (hr : ∀ s, (right s).2 ≤ R)
    (s : (S.prod T).Seed) : (run left right R s).2 ≤ L+R+16 := by
  have h₁ := hl s.1
  have h₂ := hr s.2
  simp only [run]
  split <;> dsimp only <;> omega

end LowSpaceSubsetSum.SamplerProductCells

end

end OAI
