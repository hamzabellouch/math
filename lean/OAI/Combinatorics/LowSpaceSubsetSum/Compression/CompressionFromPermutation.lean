import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDomains
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionTrial

namespace OAI

/-! # Compression execution from a stored permutation array

Domain construction is prepaid and its returned index lists are passed
directly into weight generation. No permutation oracle is used by the run.
-/

namespace LowSpaceSubsetSum.CompressionFromPermutation

open BudgetedSeparatorFlow
variable {n : ℕ}

def finish (D : CompressionData n) (V : CompressionArrayBuild.Blocks n)
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :=
  bind (BudgetedSeparatorCall.run (BudgetedCompressionTrial.charge D.input)
    (fun _ => CompressionArrayBuild.run D.weights V
      (2 ^ CompressionSetup.executableCapExponent n)) budget)
    (fun out left => match out with
      | none => BudgetedSeparatorFlow.pure false left
      | some A => BudgetedCompressionSchedule.run D.input (compressionDictionaryCapacity n)
          B A q.val (primeRange_prime q.property).pos left)

theorem finish_source (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :
    finish D (CompressionArrayBuild.source D e) q B budget =
      BudgetedCompressionTrial.run D e q B budget := rfl

def charge (n : ℕ) := 500 * (n + 1) ^ 2 + 1

def run (D : CompressionData n) (v : Vector (Fin n) n)
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :=
  bind (BudgetedSeparatorCall.run (charge n) (fun _ => CompressionDomains.prepare v) budget)
    (fun V left => finish D V q B left)

theorem account (D : CompressionData n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (q : CompressionSetup.PrimeSpace n)
    (hn : 10000 ≤ n) (budget : ℕ) :
    Account budget (run D v q (representationBufferCapacity n) budget) := by
  have hc : (CompressionDomains.prepare v).2 + 1 ≤ charge n :=
    Nat.add_le_add_right (CompressionDomains.prepare_work v) 1
  apply bind_account
  · exact ⟨BudgetedSeparatorCall.work _ _ _ hc,
      fun V left h => BudgetedSeparatorCall.spent _ _ _ hc V left h⟩
  · intro V left h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ h
    rw [CompressionDomains.prepare_value D v e hv, finish_source]
    exact BudgetedCompressionTrial.account D e q hn left

theorem sound (D : CompressionData n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (q : CompressionSetup.PrimeSpace n)
    (B budget rest : ℕ) (h : (run D v q B budget).1 = some (true, rest)) : Solvable D.input := by
  obtain ⟨V, left, hV, hf⟩ := (bind_eq_some _ _ _ _).mp h
  obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hV
  rw [CompressionDomains.prepare_value D v e hv, finish_source] at hf
  exact BudgetedCompressionTrial.sound D e q B left rest hf

theorem accepts (D : CompressionData n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (q : CompressionSetup.PrimeSpace n) (B : ℕ)
    (hn : 10000 ≤ n) (he : D.compactTests e = true) (hy : D.compressionTrial B e q = true) :
    ∃ rest, (run D v q B (charge n + 2 * trialWatchdog D.input)).1 = some (true, rest) := by
  have hc : charge n ≤ charge n + 2 * trialWatchdog D.input := Nat.le_add_right _ _
  have hp := congrArg Prod.fst (BudgetedSeparatorCall.complete (charge n)
    (fun _ => CompressionDomains.prepare v) (charge n + 2 * trialWatchdog D.input) hc)
  have hsub : charge n + 2 * trialWatchdog D.input - charge n = 2 * trialWatchdog D.input := by omega
  rw [hsub, CompressionDomains.prepare_value D v e hv] at hp
  obtain ⟨rest, ht⟩ := BudgetedCompressionTrial.accepts_watchdog D e q B hn he hy
  rw [← finish_source] at ht
  exact ⟨rest, bind_complete _ _ _ _ _ _ hp ht⟩

end LowSpaceSubsetSum.CompressionFromPermutation

end OAI
