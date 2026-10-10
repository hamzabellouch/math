import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionArrayWork
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionPreparationLedger

namespace OAI

/-! # The compression trial from stored-array construction through the last residue

The single budget covers compacting, the capacity test, raw-array creation,
every reader initialization, and all stopped joins. Sampling is separate.
-/

namespace LowSpaceSubsetSum.BudgetedCompressionTrial

open BudgetedSeparatorFlow
variable {n : ℕ}

def charge (I : Instance n) : ℕ := inputScale I ^ 5 * 2 ^ ((n + 1) / 2) + 1

def prepare (D : CompressionData n) (e : Equiv.Perm (Fin n)) (budget : ℕ) :=
  BudgetedSeparatorCall.run (charge D.input)
    (fun _ => CompressionArrayBuild.run D.weights (CompressionArrayBuild.source D e)
      (2 ^ CompressionSetup.executableCapExponent n)) budget

def run (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :=
  bind (prepare D e budget) (fun out left =>
    match out with
    | none => BudgetedSeparatorFlow.pure false left
    | some A => BudgetedCompressionSchedule.run D.input (compressionDictionaryCapacity n) B A
        q.val (primeRange_prime q.property).pos left)

theorem prepare_value (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (budget : ℕ) (A : Option PreparedCompressionPass.Arrays) (left : ℕ)
    (h : (prepare D e budget).1 = some (A, left)) :
    A = (if D.compactTests e then some (PreparedCompressionPass.source D e) else none) ∧
      left = budget - charge D.input ∧ charge D.input ≤ budget := by
  have hv := BudgetedSeparatorCall.value _ _ _ _ _ h
  rw [CompressionArrayBuild.run_source] at hv
  exact hv

theorem prepare_account (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) (budget : ℕ) : Account budget (prepare D e budget) := by
  have hc : (CompressionArrayBuild.run D.weights (CompressionArrayBuild.source D e)
      (2 ^ CompressionSetup.executableCapExponent n)).2 + 1 ≤ charge D.input :=
    Nat.add_le_add_right (CompressionArrayBuild.run_work_source D e hn) 1
  exact ⟨BudgetedSeparatorCall.work _ _ _ hc,
    fun A left h => BudgetedSeparatorCall.spent _ _ _ hc A left h⟩

theorem account (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (hn : 10000 ≤ n) (budget : ℕ) :
    Account budget (run D e q (representationBufferCapacity n) budget) := by
  apply bind_account
  · exact prepare_account D e hn budget
  · intro A left hA
    have hv := (prepare_value D e budget A left hA).1
    by_cases he : D.compactTests e = true
    · rw [ite_eq_left he] at hv
      subst A
      exact D.preparedSchedule_account e q he hn left
    · rw [ite_eq_right he] at hv
      subst A
      exact pure_account false left

theorem value_of_accepts (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (B budget rest : ℕ)
    (h : (run D e q B budget).1 = some (true, rest)) :
    D.compactTests e = true ∧ D.compressionTrial B e q = true := by
  obtain ⟨A, left, hA, ht⟩ := (bind_eq_some _ _ _ _).mp h
  have hv := (prepare_value D e budget A left hA).1
  by_cases he : D.compactTests e = true
  · rw [ite_eq_left he] at hv
    subst A
    exact ⟨he, (D.preparedSchedule_value B e q he left true rest ht).symm⟩
  · rw [ite_eq_right he] at hv
    subst A
    simp only [BudgetedSeparatorFlow.pure, Option.some.injEq, Prod.mk.injEq,
      Bool.false_eq_true, false_and] at ht

theorem sound (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (B budget rest : ℕ)
    (h : (run D e q B budget).1 = some (true, rest)) : Solvable D.input :=
  D.compressionTrial_sound B e q (value_of_accepts D e q B budget rest h).2

theorem accepts (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (B : ℕ) (hn : 10000 ≤ n)
    (he : D.compactTests e = true) (hy : D.compressionTrial B e q = true)
    (budget : ℕ) (hb : charge D.input + BudgetedCompressionSchedule.allowance D.input
      (compressionDictionaryCapacity n) B (PreparedCompressionPass.source D e) q.val
      (primeRange_prime q.property).pos ≤ budget) :
    ∃ rest, (run D e q B budget).1 = some (true, rest) := by
  have hc : charge D.input ≤ budget := by omega
  have hf := congrArg Prod.fst (BudgetedSeparatorCall.complete (charge D.input)
    (fun _ => CompressionArrayBuild.run D.weights (CompressionArrayBuild.source D e)
      (2 ^ CompressionSetup.executableCapExponent n)) budget hc)
  rw [CompressionArrayBuild.run_source, ite_eq_left he] at hf
  obtain ⟨v, rest, hv⟩ := BudgetedCompressionSchedule.complete D.input
    (compressionDictionaryCapacity n) B (PreparedCompressionPass.source D e) q.val
    (primeRange_prime q.property).pos hn (budget - charge D.input) (by omega)
  have hh := D.preparedSchedule_value B e q he _ v rest hv
  rw [hy] at hh
  subst v
  exact ⟨rest, bind_complete _ _ _ _ _ _ hf hv⟩

theorem accepts_watchdog (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (B : ℕ) (hn : 10000 ≤ n)
    (he : D.compactTests e = true) (hy : D.compressionTrial B e q = true) :
    ∃ rest, (run D e q B (2 * trialWatchdog D.input)).1 = some (true, rest) := by
  apply accepts D e q B hn he hy
  have hs := D.preparedSchedule_allowance B e q he hn
  have hu : 10000 ≤ inputScale D.input := by unfold inputScale; omega
  have hpow : inputScale D.input ^ 7 ≤ inputScale D.input ^ 500 :=
    pow_le_pow_right' (by omega) (by decide)
  have hlow : 2 * inputScale D.input ^ 5 ≤ inputScale D.input ^ 7 := by
    have h₆ : 2 * inputScale D.input ^ 5 ≤ inputScale D.input ^ 6 := by
      calc
        _ ≤ inputScale D.input * inputScale D.input ^ 5 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := (pow_succ' _ _).symm
    exact h₆.trans (pow_le_pow_right' (by omega) (by decide))
  have hT : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
  have hlarge : 1 ≤ inputScale D.input ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hs' := hs.trans (Nat.mul_le_mul_right _ hpow)
  have hc := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hlow
  have hpos := Nat.mul_le_mul hlarge hT
  have htop := Nat.mul_le_mul_right (2 ^ ((n + 1) / 2)) hpow
  unfold charge trialWatchdog
  nlinarith only [hs', hc, hpos, htop]

end LowSpaceSubsetSum.BudgetedCompressionTrial

end OAI
