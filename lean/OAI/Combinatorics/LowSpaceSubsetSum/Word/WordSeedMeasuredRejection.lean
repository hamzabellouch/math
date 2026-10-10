import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasured

namespace OAI

/-! # Measured rejection as a cached seed-generator primitive -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

open WordSeedRealization

variable {w k : ℕ} (A : Fin (2^k) → Prop) [DecidablePred A]
  [Nonempty {a : Fin (2^k) // A a}]

theorem rejectionSeed_backup (N : ℕ) (f : Fin N → Fin (2^k))
    (s : SuccessfulSeed (firstAcceptCoupling A N)) (h : rejectionSeed A N f = some s) :
    (firstAcceptCoupling A N).bounded s.val = some s.val.2 := by
  unfold rejectionSeed at h
  split at h
  · contradiction
  next a ha =>
    cases h
    exact ha

def cacheRejection (N : ℕ) (f : Fin N → Fin (2^k))
    (out : Option (SuccessfulSeed (firstAcceptCoupling A N)))
    (ho : out = rejectionSeed A N f) : Option (Accepted (firstAcceptCoupling A N)) :=
  out.pmap (fun s hs =>
    ⟨s,s.val.2,Option.some.inj ((rejectionSeed_backup A N f s (ho.symm.trans hs)).symm.trans
      (successful_agrees s))⟩) (fun _ h => h)

theorem cacheRejection_seed (N : ℕ) (f : Fin N → Fin (2^k))
    (out : Option (SuccessfulSeed (firstAcceptCoupling A N)))
    (ho : out = rejectionSeed A N f) :
    (cacheRejection A N f out ho).map Accepted.seed = out := by
  cases out <;> rfl

variable (evaluate : Fin (2^k) → (Bool × ℕ) × ℕ)
  (he : ∀ a, (evaluate a).1.1 = true ↔ A a)

def rejectionRun (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) : Result (firstAcceptCoupling A N) :=
  let r := WordSeedRejectionExecution.run A evaluate he stream modulus hm N cursor
  ⟨cacheRejection A N (fun i => ExactWordDraw.low w k (stream (cursor+i.val)))
      r.seed (WordSeedRejectionExecution.run_seed A evaluate he stream modulus hm N cursor),
    r.cursor,r.work+2,r.cells+8,N+8⟩

def rejection (hk : k ≤ w) (modulus : ℕ) (hm : modulus = 2^k) (N : ℕ) :
    Execution (WordSeedRealization.rejection w k hk N A) where
  run stream cursor := rejectionRun A evaluate he stream modulus hm N cursor
  value stream cursor := by
    dsimp only [rejectionRun]
    rw [cacheRejection_seed]
    exact WordSeedRejectionExecution.program_value A evaluate he hk stream modulus hm N cursor

theorem rejection_bounded (hk : k ≤ w) (modulus : ℕ) (hm : modulus = 2^k)
    (N K H : ℕ) (hK : ∀ a, (evaluate a).1.2 ≤ K) (hH : ∀ a, (evaluate a).2 ≤ H) :
    (rejection A evaluate he hk modulus hm N).Bounded
      (N*(K+11)+11) (2*N+H+64) (N+8) := by
  intro stream cursor
  have hw := WordSeedRejectionExecution.run_work A evaluate he stream modulus hm K N cursor hK
  have hc := WordSeedRejectionExecution.run_cells A evaluate he stream modulus hm H N cursor hH
  change _+2 ≤ _ ∧ _+8 ≤ _ ∧ N+8 ≤ N+8
  exact ⟨by omega,by omega,le_rfl⟩

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
