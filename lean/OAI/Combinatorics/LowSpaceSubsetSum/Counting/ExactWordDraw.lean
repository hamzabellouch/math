import OAI.Combinatorics.LowSpaceSubsetSum.Counting.RejectionSamplerCoupling

namespace OAI

/-! # Exact power-of-two draws from fair machine words

These projections discard high bits, so their law is exactly uniform.
The rejection sampler's independent eligible backup is absent from the
bounded execution and can be integrated out without changing its law.
-/

noncomputable section
namespace LowSpaceSubsetSum.ExactWordDraw

def low (w k : ℕ) (x : Fin (2^w)) : Fin (2^k) :=
  ⟨x.val % 2^k, Nat.mod_lt _ (by positivity)⟩

def wordSplit (w k : ℕ) (hk : k ≤ w) :
    Fin (2^w) ≃ Fin (2^k) × Fin (2^(w-k)) :=
  (finCongr (by rw [← pow_add, Nat.sub_add_cancel hk])).trans
    ((finProdFinEquiv (m := 2^(w-k)) (n := 2^k)).symm.trans (Equiv.prodComm _ _))

theorem wordSplit_low (w k : ℕ) (hk : k ≤ w) (x : Fin (2^w)) :
    (wordSplit w k hk x).1 = low w k x := by
  apply Fin.ext
  rfl

def tupleSplit (w k : ℕ) (hk : k ≤ w) (N : ℕ) :
    (Fin N → Fin (2^w)) ≃ (Fin N → Fin (2^k)) × (Fin N → Fin (2^(w-k))) where
  toFun f := (fun i => (wordSplit w k hk (f i)).1, fun i => (wordSplit w k hk (f i)).2)
  invFun p i := (wordSplit w k hk).symm (p.1 i, p.2 i)
  left_inv f := by
    funext i
    exact (wordSplit w k hk).symm_apply_apply (f i)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst ((wordSplit w k hk).apply_symm_apply (p.1 i, p.2 i))
    · funext i
      exact congrArg Prod.snd ((wordSplit w k hk).apply_symm_apply (p.1 i, p.2 i))

theorem uniform_tuple (w k : ℕ) (hk : k ≤ w) (N : ℕ)
    (P : (Fin N → Fin (2^k)) → Prop) :
    (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).probability
      (fun f => P (fun i => low w k (f i))) =
      (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^k))).probability P := by
  rw [FiniteLaw.uniform_probability, FiniteLaw.uniform_probability]
  have he := finiteUniformProbability_equiv (tupleSplit w k hk N) (fun p => P p.1)
  have hfun (f : Fin N → Fin (2^w)) :
      (tupleSplit w k hk N f).1 = fun i => low w k (f i) := by
    funext i
    exact wordSplit_low w k hk (f i)
  simpa only [hfun] using he.trans (finiteUniformProbability_fst P)

private theorem uniform_projection {Ω Ψ : Type} [Fintype Ω] [Fintype Ψ]
    [Nonempty Ω] [Nonempty Ψ] (P : Ω → Prop) :
    (FiniteLaw.uniform : FiniteLaw (Ω × Ψ)).probability (fun s => P s.1) =
      (FiniteLaw.uniform : FiniteLaw Ω).probability P := by
  rw [FiniteLaw.uniform_probability, FiniteLaw.uniform_probability]
  exact finiteUniformProbability_fst P

theorem firstAccept_no_backup {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (N : ℕ) (P : Option {a : Ω // A a} → Prop) :
    (firstAcceptCoupling A N).law.probability
      (fun s => P ((firstAcceptCoupling A N).bounded s)) =
      (FiniteLaw.uniform : FiniteLaw (Fin N → Ω)).probability
        (fun f => P (firstAcceptSubtype A N f)) := by
  change (FiniteLaw.uniform : FiniteLaw ((Fin N → Ω) × {a : Ω // A a})).probability
    (fun s => P (firstAcceptSubtype A N s.1)) = _
  exact uniform_projection (Ψ := {a : Ω // A a}) (fun f => P (firstAcceptSubtype A N f))

theorem firstAccept_words (w k : ℕ) (hk : k ≤ w)
    (A : Fin (2^k) → Prop) [DecidablePred A] [Nonempty {a : Fin (2^k) // A a}]
    (N : ℕ) (P : Option {a : Fin (2^k) // A a} → Prop) :
    (firstAcceptCoupling A N).law.probability
      (fun s => P ((firstAcceptCoupling A N).bounded s)) =
      (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).probability
        (fun f => P (firstAcceptSubtype A N (fun i => low w k (f i)))) := by
  rw [firstAccept_no_backup]
  exact (uniform_tuple w k hk N (fun f => P (firstAcceptSubtype A N f))).symm

/-- Full candidate observations may include the test and read counters. -/
theorem candidates_words (w k : ℕ) (hk : k ≤ w)
    (A : Fin (2^k) → Prop) [DecidablePred A] [Nonempty {a : Fin (2^k) // A a}]
    (N : ℕ) (P : (Fin N → Fin (2^k)) → Prop) :
    (firstAcceptCoupling A N).law.probability (fun s => P s.1) =
      (FiniteLaw.uniform : FiniteLaw (Fin N → Fin (2^w))).probability
        (fun f => P (fun i => low w k (f i))) := by
  exact (uniform_projection (Ψ := {a : Fin (2^k) // A a}) P).trans
    (uniform_tuple w k hk N P).symm

end LowSpaceSubsetSum.ExactWordDraw

end

end OAI
