import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedPreparedCompressionPass
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedResidueLoop

namespace OAI

/-! # Executed compression residue scan with one shared budget

Each residue constructs its four live readers from the shared arrays. A
completed pass releases those readers before the next residue is started.
-/

namespace LowSpaceSubsetSum.BudgetedCompressionSchedule

open BudgetedSeparatorFlow
open BudgetedSeparatorCall (Outcome)
open PreparedCompressionPass (Arrays)
open scoped BigOperators
variable {n : ℕ}

def bucket (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P)
    (z budget : ℕ) : Outcome Bool :=
  if z < P then
    BudgetedPreparedCompressionPass.run I C B A P I.target z (by exact_mod_cast hP) budget
  else BudgetedSeparatorFlow.pure false budget

def bill (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P) (z : ℕ) : ℕ :=
  if z < P then
    BudgetedPreparedCompressionPass.allowance I C B A P I.target z (by exact_mod_cast hP)
  else 0

def run (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P) (budget : ℕ) :=
  BudgetedResidueLoop.run (bucket I C B A P hP) 0 P budget

def allowance (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P) :=
  BudgetedResidueLoop.allowance (bill I C B A P hP) 0 P

theorem complete (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P)
    (hn : 10000 ≤ n) (budget : ℕ) (hb : allowance I C B A P hP ≤ budget) :
    ∃ v rest, (run I C B A P hP budget).1 = some (v, rest) := by
  apply BudgetedResidueLoop.complete _ (bill I C B A P hP) _ _ 0 P budget 0 hb
  · intro z b hz
    by_cases hp : z < P
    · simp only [bill, hp, ↓reduceIte] at hz
      simpa only [bucket, hp, ↓reduceIte] using
        BudgetedPreparedCompressionPass.complete I C B A P I.target z _ hn b hz
    · exact ⟨false, b, by simp only [bucket, hp, ↓reduceIte, BudgetedSeparatorFlow.pure]⟩
  · intro z b v rest hz
    by_cases hp : z < P
    · simp only [bucket, hp, ↓reduceIte] at hz
      simpa only [bill, hp, ↓reduceIte] using
        BudgetedPreparedCompressionPass.remaining I C B A P I.target z _ hn b v rest hz
    · simp only [bucket, hp, ↓reduceIte, BudgetedSeparatorFlow.pure] at hz
      cases hz
      simp only [bill, hp, ↓reduceIte, Nat.add_zero, le_refl]

private theorem range_sum_fin (f : ℕ → ℕ) (count : ℕ) :
    ((List.range count).map f).sum = ∑ i : Fin count, f i.val := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.sum_range_succ, Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last] using congrArg (· + f count) ih

theorem allowance_eq (I : Instance n) (C B : ℕ) (A : Arrays) (P : ℕ) (hP : 0 < P) :
    allowance I C B A P hP = 4 * (P + 1) +
      ∑ z : Fin P, BudgetedPreparedCompressionPass.allowance I C B A P I.target z.val
        (by exact_mod_cast hP) := by
  simp only [allowance, BudgetedResidueLoop.allowance_eq, Nat.zero_add, range_sum_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  simp only [bill, z.isLt, ↓reduceIte]

end LowSpaceSubsetSum.BudgetedCompressionSchedule

namespace LowSpaceSubsetSum.CompressionData

open BudgetedSeparatorFlow
variable {n : ℕ} (D : CompressionData n)

theorem preparedSchedule_reference (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z count : ℕ) :
    BudgetedResidueLoop.reference
      (fun z => if h : z < q.val then D.residuePass B e q ⟨z, h⟩ else false) z count =
      CompressionSetup.residueLoop
        (fun z => if h : z < q.val then D.residuePass B e q ⟨z, h⟩ else false) count z := by
  induction count generalizing z with
  | zero => rfl
  | succ count ih =>
    simp only [BudgetedResidueLoop.reference, CompressionSetup.residueLoop, ih]

theorem preparedSchedule_value (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (he : D.compactTests e = true)
    (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (BudgetedCompressionSchedule.run D.input (compressionDictionaryCapacity n) B
      (PreparedCompressionPass.source D e) q.val (primeRange_prime q.property).pos budget).1 =
        some (v, rest)) : v = D.compressionTrial B e q := by
  have hv := BudgetedResidueLoop.value
    (BudgetedCompressionSchedule.bucket D.input (compressionDictionaryCapacity n) B
      (PreparedCompressionPass.source D e) q.val (primeRange_prime q.property).pos)
    (fun z => if h : z < q.val then D.residuePass B e q ⟨z, h⟩ else false)
    (by
      intro z b v rest hz
      by_cases hp : z < q.val
      · simp only [BudgetedCompressionSchedule.bucket, hp, ↓reduceIte] at hz
        simpa only [hp, ↓reduceDIte] using
          (BudgetedPreparedCompressionPass.source_value D B e q ⟨z, hp⟩ he b v rest hz).1
      · simp only [BudgetedCompressionSchedule.bucket, hp, ↓reduceIte,
          BudgetedSeparatorFlow.pure] at hz
        cases hz
        simp only [hp, ↓reduceDIte]) 0 q.val budget 0 v rest h
  exact hv.trans (D.preparedSchedule_reference B e q 0 q.val)

theorem preparedSchedule_account (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (he : D.compactTests e = true)
    (hn : 10000 ≤ n) (budget : ℕ) :
    Account budget (BudgetedCompressionSchedule.run D.input (compressionDictionaryCapacity n)
      (representationBufferCapacity n) (PreparedCompressionPass.source D e) q.val
      (primeRange_prime q.property).pos budget) := by
  apply BudgetedResidueLoop.account
  intro z b
  by_cases hp : z < q.val
  · simp only [BudgetedCompressionSchedule.bucket, hp, ↓reduceIte]
    exact BudgetedPreparedCompressionPass.source_account D e q ⟨z, hp⟩ he b hn
  · simp only [BudgetedCompressionSchedule.bucket, hp, ↓reduceIte]
    exact pure_account false b

end LowSpaceSubsetSum.CompressionData

end OAI
