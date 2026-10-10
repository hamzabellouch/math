import OAI.Combinatorics.LowSpaceSubsetSum.Compression.PreparedCompressionPass

namespace OAI

/-! # A prepaid compression pass including all four initializations -/

namespace LowSpaceSubsetSum.BudgetedPreparedCompressionPass

open BudgetedSeparatorFlow
open PreparedCompressionPass (Arrays)
variable {n : ℕ}

def charge (I : Instance n) (A : Arrays) : ℕ := inputScale I ^ 6 * PreparedCompressionPass.size A + 1

def run (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P) (budget : ℕ) :=
  bind (BudgetedSeparatorCall.run (charge I A) (fun _ => PreparedCompressionPass.prepare A P t z hP) budget)
    (fun D remaining => BudgetedCompressionPass.run I C B D remaining)

def allowance (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P) : ℕ :=
  charge I A + BudgetedCompressionPass.allowance I C B (PreparedCompressionPass.prepare A P t z hP).1

theorem value (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P)
    (budget : ℕ) (v : Bool) (remaining : ℕ)
    (h : (run I C B A P t z hP budget).1 = some (v, remaining)) :
    v = BudgetedCompressionPass.reference I C B (PreparedCompressionPass.prepare A P t z hP).1 ∧
      remaining ≤ budget := by
  obtain ⟨D, first, hf, hp⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨rfl, hfirst, hcharge⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hf
  have hv := BudgetedCompressionPass.value I C B _ first v remaining hp
  exact ⟨hv.1, by omega⟩

theorem account (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P)
    (budget : ℕ) (hn : 10000 ≤ n)
    (hfirst : ∀ i, (A.first i).size ≤ 2 ^ n) (hsecond : ∀ i, (A.second i).size ≤ 2 ^ n)
    (hpass : ∀ b, Account b (BudgetedCompressionPass.run I C B
      (PreparedCompressionPass.prepare A P t z hP).1 b)) :
    Account budget (run I C B A P t z hP budget) := by
  have hc : (PreparedCompressionPass.prepare A P t z hP).2 + 1 ≤ charge I A :=
    Nat.add_le_add_right (PreparedCompressionPass.prepare_work I hn A P t z hP hfirst hsecond) 1
  apply bind_account
  · exact ⟨BudgetedSeparatorCall.work _ _ _ hc,
      fun D remaining h => BudgetedSeparatorCall.spent _ _ _ hc D remaining h⟩
  · intro D remaining h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ h
    exact hpass remaining

theorem complete (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P)
    (hn : 10000 ≤ n) (budget : ℕ) (hb : allowance I C B A P t z hP ≤ budget) :
    ∃ v remaining, (run I C B A P t z hP budget).1 = some (v, remaining) := by
  have hc : charge I A ≤ budget := by unfold allowance at hb; omega
  obtain ⟨v, remaining, hp⟩ := BudgetedCompressionPass.complete I C B
    (PreparedCompressionPass.prepare A P t z hP).1 hn (budget - charge I A)
    (by unfold allowance at hb; omega)
  refine ⟨v, remaining, bind_complete _ _ _ _ _ _ ?_ hp⟩
  exact congrArg Prod.fst (BudgetedSeparatorCall.complete _ _ _ hc)

theorem remaining (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P)
    (hn : 10000 ≤ n) (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (run I C B A P t z hP budget).1 = some (v, rest)) :
    budget ≤ rest + allowance I C B A P t z hP := by
  obtain ⟨D, first, hf, hp⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨rfl, hfirst, hcharge⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hf
  have hr := BudgetedCompressionPass.remaining I C B _ hn first v rest hp
  unfold allowance
  omega

theorem source_value (D : CompressionData n) (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (he : D.compactTests e = true)
    (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (run D.input (compressionDictionaryCapacity n) B (PreparedCompressionPass.source D e)
      q.val D.input.target z.val (by exact_mod_cast (primeRange_prime q.property).pos) budget).1 =
        some (v, rest)) : v = D.residuePass B e q z ∧ rest ≤ budget := by
  have hv := value D.input (compressionDictionaryCapacity n) B (PreparedCompressionPass.source D e)
    q.val D.input.target z.val _ budget v rest h
  rw [PreparedCompressionPass.source_value] at hv
  exact ⟨hv.1.trans (D.pass_reference B e q z he), hv.2⟩

theorem source_account (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (he : D.compactTests e = true)
    (budget : ℕ) (hn : 10000 ≤ n) :
    Account budget (run D.input (compressionDictionaryCapacity n) (representationBufferCapacity n)
      (PreparedCompressionPass.source D e) q.val D.input.target z.val
      (by exact_mod_cast (primeRange_prime q.property).pos) budget) := by
  have hs := PreparedCompressionPass.source_sizes D e he hn
  apply account _ _ _ _ _ _ _ _ _ hn hs.1 hs.2
  intro b
  rw [PreparedCompressionPass.source_value]
  exact D.pass_account e he q z b hn

end LowSpaceSubsetSum.BudgetedPreparedCompressionPass

end OAI
