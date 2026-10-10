import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedRealization
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRangeRealization

namespace OAI

/-! # Successful seed constructors for products and bounded rejection

The rejection constructor draws and retains the full candidate tuple.
Its backup coordinate is the accepted value, so no backup word is read.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedRealization

open WordProgram
attribute [local instance] Classical.propDecidable

def enlarge {w N M : ℕ} {α : Type} [Fintype α] {S : SamplerCoupling α}
    (X : Realization w N S) (h : N ≤ M) : Realization w M S where
  program := X.program
  faithful := X.faithful
  bounded := by
    have hb := WordProgram.bound_add X.program N X.bounded (M-N)
    simpa only [Nat.sub_add_cancel h] using hb

def prod {w N M : ℕ} {α β : Type} [Fintype α] [Fintype β]
    {S : SamplerCoupling α} {T : SamplerCoupling β}
    (X : Realization w N S) (Y : Realization w M T) : Realization w (N+M) (S.prod T) :=
  map (bind X (fun _ => β) (fun _ => T) (fun _ => Y)) (Equiv.sigmaEquivProd α β)

def pi (w N : ℕ) : (k : ℕ) → (A : Fin k → Type) → [∀ i, Fintype (A i)] →
    (S : ∀ i, SamplerCoupling (A i)) → (∀ i, Realization w N (S i)) →
    Realization w (k*N) (SamplerCoupling.pi k A S)
  | 0, A, _, _, _ => by
    simpa only [Nat.zero_mul,SamplerCoupling.pi] using
      (pure (w := w) (fun i : Fin 0 => (Fin.elim0 i : A i)))
  | k+1, A, _, S, X => by
    have h := map (prod (X 0)
      (pi w N k (fun i => A i.succ) (fun i => S i.succ) (fun i => X i.succ)))
      (Fin.consEquiv A)
    simpa only [SamplerCoupling.pi,Nat.add_mul,Nat.one_mul,Nat.add_comm] using h

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

def rejectionSeed (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (N : ℕ) (f : Fin N → Ω) : Option (SuccessfulSeed (firstAcceptCoupling A N)) :=
  match h : firstAcceptSubtype A N f with
  | none => none
  | some a => some ⟨(f,a),a,h⟩

theorem rejectionSeed_observe (A : Ω → Prop) [DecidablePred A]
    [Nonempty {a : Ω // A a}] (N : ℕ) (f : Fin N → Ω) :
    observe (firstAcceptCoupling A N) (rejectionSeed A N f) = firstAcceptSubtype A N f := by
  unfold rejectionSeed
  split
  next h => exact h.symm
  next => rfl

theorem rejectionSeed_candidates (A : Ω → Prop) [DecidablePred A]
    [Nonempty {a : Ω // A a}] (N : ℕ) (f : Fin N → Ω)
    (s : SuccessfulSeed (firstAcceptCoupling A N)) (h : rejectionSeed A N f = some s) :
    s.val.1 = f := by
  unfold rejectionSeed at h
  split at h
  · contradiction
  · cases h
    rfl

def rejection (w k : ℕ) (hk : k ≤ w) (N : ℕ)
    (A : Fin (2^k) → Prop) [DecidablePred A] [Nonempty {a : Fin (2^k) // A a}] :
    Realization w N (firstAcceptCoupling A N) where
  program := WordProgram.map
    (fun f => rejectionSeed A N (fun i => ExactWordDraw.low w k (f i))) (WordTuple.sample N)
  faithful P := by
    rw [WordProgram.probability_map,WordProgram.probability_map]
    simp only [rejectionSeed_observe]
    rw [WordTuple.probability,SamplerCoupling.boundedLaw,FiniteLaw.map_probability]
    exact (ExactWordDraw.firstAccept_words w k hk A N P).symm
  bounded := by
    simpa only [WordProgram.map,Nat.add_zero] using
      WordProgram.bind_bound (WordTuple.sample (w := w) N) N (WordTuple.bounded N)
        (fun f => .pure (rejectionSeed A N (fun i => ExactWordDraw.low w k (f i)))) 0
        (fun _ => Bounded.pure _ 0)

end LowSpaceSubsetSum.WordSeedRealization

end

end OAI
