import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerAttemptCells
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerExecution

namespace OAI

/-! # Stored candidate tuples for certified bounded samplers

The runtime argument is a vector of candidate words. Its function view is
used only to identify the finite sampling law. Certification and the unused
ideal backup do not perform another candidate search.
-/

namespace LowSpaceSubsetSum.SamplerVectorCells

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

def candidates {N : ℕ} (v : Vector Ω N) : Fin N → Ω := fun i => v[i.val]

omit [Fintype Ω] [Nonempty Ω] in
theorem raw_value (test : Ω → (Bool × ℕ) × ℕ) (wordCells N : ℕ) (v : Vector Ω N) :
    (SamplerAttemptCells.run test v.toArray wordCells).1 =
      SamplerAttempts.runCostAcc (fun x => (test x).1) N (candidates v) 0 0 := by
  rcases v with ⟨v, rfl⟩
  exact SamplerAttemptCells.run_value test v wordCells

def test (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (evaluate : Ω → (Bool × ℕ) × ℕ) (he : ∀ a, (evaluate a).1.1 = true ↔ A a)
    (wordCells N : ℕ) (v : Vector Ω N) : SamplerExecution.Trace {a : Ω // A a} × ℕ :=
  let r := SamplerAttemptCells.run evaluate v.toArray wordCells
  have hv : r.1.1 = firstAccept A N (candidates v) := by
    rw [raw_value, SamplerAttempts.runCostAcc_value]
    congr 1
    funext a
    exact propext (he a)
  (⟨SamplerExecution.certify A r.1.1
      (fun a ha => firstAccept_some_eligible A N (candidates v) (hv.symm.trans ha)),
      r.1.2.1, r.1.2.2⟩, r.2+24)

theorem test_value (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (evaluate : Ω → (Bool × ℕ) × ℕ) (he : ∀ a, (evaluate a).1.1 = true ↔ A a)
    (wordCells N : ℕ) (v : Vector Ω N) (backup : {a : Ω // A a}) :
    (test A evaluate he wordCells N v).1 =
      (SamplerExecution.test A (fun x => (evaluate x).1) he N).run
        (candidates v, backup) := by
  unfold test SamplerExecution.test
  simp only [raw_value]

omit [Fintype Ω] [Nonempty Ω] in
theorem test_cells (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (evaluate : Ω → (Bool × ℕ) × ℕ) (he : ∀ a, (evaluate a).1.1 = true ↔ A a)
    (wordCells K N : ℕ) (v : Vector Ω N) (hK : ∀ a, (evaluate a).2 ≤ K) :
    (test A evaluate he wordCells N v).2 ≤ N*wordCells+K+40 := by
  have h := SamplerAttemptCells.run_cells evaluate v.toArray wordCells K hK
  simp only [Vector.size_toArray] at h
  change (SamplerAttemptCells.run evaluate v.toArray wordCells).2+24 ≤ _
  omega

theorem test_seed_independent (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}]
    (evaluate : Ω → (Bool × ℕ) × ℕ) (he : ∀ a, (evaluate a).1.1 = true ↔ A a)
    (N : ℕ) (v : Vector Ω N) (a b : {x : Ω // A x}) :
    (SamplerExecution.test A (fun x => (evaluate x).1) he N).run (candidates v, a) =
      (SamplerExecution.test A (fun x => (evaluate x).1) he N).run (candidates v, b) := by
  rfl

section Range

variable {D : ℕ} (hD : 1 < D) (n : ℕ)

include hD in
private theorem rangeNonempty : Nonempty {p : Fin (2^Nat.clog 2 D) // rangeEligible D p} :=
  ⟨(rangeEligibleEquiv D).symm ⟨0, by omega⟩⟩

def range (v : Vector (Fin (2^Nat.clog 2 D)) (n^3)) :
    SamplerExecution.Trace (Fin D) × ℕ := by
  letI := rangeNonempty hD
  let r := test (rangeEligible D) (fun p => ((decide (rangeEligible D p), 0), 8))
    (fun _ => by simp only [decide_eq_true_eq]) 1 (n^3) v
  exact (⟨r.1.value.map (rangeEligibleEquiv D), r.1.reads, r.1.tests⟩, r.2+8)

theorem range_value (v : Vector (Fin (2^Nat.clog 2 D)) (n^3))
    (backup : {p : Fin (2^Nat.clog 2 D) // rangeEligible D p}) :
    (range hD n v).1 = (SamplerExecution.range hD n).run (candidates v, backup) := by
  let _ := rangeNonempty hD
  have h := test_value (rangeEligible D) (fun p => ((decide (rangeEligible D p), 0), 8))
    (fun _ => by simp only [decide_eq_true_eq]) 1 (n^3) v backup
  simp only [range, SamplerExecution.range, SamplerExecution.map]
  rw [h]

theorem range_cells (v : Vector (Fin (2^Nat.clog 2 D)) (n^3)) :
    (range hD n v).2 ≤ n^3+56 := by
  let _ := rangeNonempty hD
  have h := test_cells (rangeEligible D) (fun p => ((decide (rangeEligible D p), 0), 8))
    (fun _ => by simp only [decide_eq_true_eq]) 1 8 (n^3) v (fun _ => le_rfl)
  change _+8 ≤ _
  simp only [Nat.mul_one] at h
  omega

/-- Tabulate the supplied finite random-word tuple once. The extra reserve
counts both tabulation storage and its construction stack. -/
def rangeSeed (s : (rangeCoupling hD n).Seed) : SamplerExecution.Trace (Fin D) × ℕ :=
  let v : Vector (Fin (2^Nat.clog 2 D)) (n^3) := Vector.ofFn s.1
  let r := range hD n v
  (r.1, r.2+2*n^3+8)

theorem rangeSeed_value (s : (rangeCoupling hD n).Seed) :
    (rangeSeed hD n s).1 = (SamplerExecution.range hD n).run s := by
  have h := range_value hD n (Vector.ofFn s.1) s.2
  have hv : candidates (Vector.ofFn s.1) = s.1 := by
    funext i
    simp only [candidates, Vector.getElem_ofFn, Fin.eta]
  rw [hv] at h
  exact h

theorem rangeSeed_cells (s : (rangeCoupling hD n).Seed) :
    (rangeSeed hD n s).2 ≤ 3*n^3+64 := by
  have h := range_cells hD n (Vector.ofFn s.1)
  change _+2*n^3+8 ≤ _
  omega

end Range

section Prime

variable {ell : ℕ} (hell : 4 ≤ ell) (n : ℕ)

include hell in
private theorem primeNonempty : Nonempty {p : Fin (2^ell) // primeEligible ell p} :=
  ⟨(primeEligibleEquiv hell).symm
    (Classical.choice (primeRange_nonempty hell).to_subtype)⟩

def prime (v : Vector (Fin (2^ell)) (n^3)) :
    SamplerExecution.Trace ↥(primeRange ell) × ℕ := by
  letI := primeNonempty hell
  let r := test (primeEligible ell) (PrimeTestCells.test ell)
    (fun p => by rw [PrimeTestCells.test_value]; exact SamplerAttempts.primeTest_correct ell p)
    1 (n^3) v
  exact (⟨r.1.value.map (primeEligibleEquiv hell), r.1.reads, r.1.tests⟩, r.2+8)

theorem prime_value (v : Vector (Fin (2^ell)) (n^3))
    (backup : {p : Fin (2^ell) // primeEligible ell p}) :
    (prime hell n v).1 = (SamplerExecution.prime hell n).run (candidates v, backup) := by
  let _ := primeNonempty hell
  have h := test_value (primeEligible ell) (PrimeTestCells.test ell)
    (fun p => by rw [PrimeTestCells.test_value]; exact SamplerAttempts.primeTest_correct ell p)
    1 (n^3) v backup
  simp only [prime, SamplerExecution.prime, SamplerExecution.map]
  rw [h]
  simp only [PrimeTestCells.test_value]

theorem prime_cells (v : Vector (Fin (2^ell)) (n^3)) :
    (prime hell n v).2 ≤ n^3+72 := by
  let _ := primeNonempty hell
  have h := test_cells (primeEligible ell) (PrimeTestCells.test ell)
    (fun p => by rw [PrimeTestCells.test_value]; exact SamplerAttempts.primeTest_correct ell p)
    1 24 (n^3) v (fun p => (PrimeTestCells.test_cells ell p).le)
  change _+8 ≤ _
  simp only [Nat.mul_one] at h
  omega

def primeSeed (s : (primeCoupling hell n).Seed) :
    SamplerExecution.Trace ↥(primeRange ell) × ℕ :=
  let v : Vector (Fin (2^ell)) (n^3) := Vector.ofFn s.1
  let r := prime hell n v
  (r.1, r.2+2*n^3+8)

theorem primeSeed_value (s : (primeCoupling hell n).Seed) :
    (primeSeed hell n s).1 = (SamplerExecution.prime hell n).run s := by
  have h := prime_value hell n (Vector.ofFn s.1) s.2
  have hv : candidates (Vector.ofFn s.1) = s.1 := by
    funext i
    simp only [candidates, Vector.getElem_ofFn, Fin.eta]
  rw [hv] at h
  exact h

theorem primeSeed_cells (s : (primeCoupling hell n).Seed) :
    (primeSeed hell n s).2 ≤ 3*n^3+80 := by
  have h := prime_cells hell n (Vector.ofFn s.1)
  change _+2*n^3+8 ≤ _
  omega

end Prime

end LowSpaceSubsetSum.SamplerVectorCells

end OAI
