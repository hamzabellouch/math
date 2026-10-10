import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionScheduleCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionArrayCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionDomainCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionFromPermutation

namespace OAI

/-! # Live compression storage from an actual stored permutation

Domain and weight construction are performed only after their prepaid
guards pass. The resulting arrays are shared across all residue passes.
-/

namespace LowSpaceSubsetSum.CompressionFromPermutationCells

variable {n : ℕ}

def finish (D : CompressionData n) (V : CompressionArrayBuild.Blocks n)
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :=
  if BudgetedCompressionTrial.charge D.input ≤ budget then
    let arrays := CompressionArrayCells.run D.weights V
      (2^CompressionSetup.executableCapExponent n)
    match arrays.1.1 with
    | none => ((some (false,budget-BudgetedCompressionTrial.charge D.input),
        arrays.1.2+1),arrays.2+32)
    | some A =>
      let out := CompressionScheduleCells.run D.input (compressionDictionaryCapacity n)
        B A q.val (primeRange_prime q.property).pos
          (budget-BudgetedCompressionTrial.charge D.input)
      ((out.1.1,(arrays.1.2+1)+out.1.2),
        arrays.2+out.2+4*PreparedCompressionPass.size A+32)
  else ((none,1),32)

theorem finish_value (D : CompressionData n) (V : CompressionArrayBuild.Blocks n)
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :
    (finish D V q B budget).1 = CompressionFromPermutation.finish D V q B budget := by
  unfold finish CompressionFromPermutation.finish BudgetedSeparatorCall.run
  dsimp only
  split
  · simp only [CompressionArrayCells.value,BudgetedSeparatorFlow.bind]
    cases (CompressionArrayBuild.run D.weights V
        (2^CompressionSetup.executableCapExponent n)).1 <;>
      simp only [CompressionScheduleCells.value,BudgetedSeparatorFlow.pure,Nat.add_zero]
  · rfl

theorem output_source (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (A : PreparedCompressionPass.Arrays)
    (h : (CompressionArrayCells.run D.weights (CompressionArrayBuild.source D e)
      (2^CompressionSetup.executableCapExponent n)).1.1 = some A) :
    D.compactTests e = true ∧ A = PreparedCompressionPass.source D e := by
  rw [congrArg Prod.fst (CompressionArrayCells.value _ _ _),
    CompressionArrayBuild.run_source] at h
  cases he : D.compactTests e
  · simp only [he, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · simp only [he, ↓reduceIte, Option.some.injEq] at h
    exact ⟨rfl,h.symm⟩

theorem output_lengths (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) (A : PreparedCompressionPass.Arrays)
    (h : (CompressionArrayCells.run D.weights (CompressionArrayBuild.source D e)
      (2^CompressionSetup.executableCapExponent n)).1.1 = some A) :
    (∀ i, (A.first i).size ≤ compressionDictionaryCapacity n) ∧
      (∀ i, (A.second i).size ≤ compressionDictionaryCapacity n) := by
  obtain ⟨he,rfl⟩ := output_source D e A h
  constructor
  · intro i
    exact (D.stored_lists_capacity e he (by omega) i).1
  · intro i
    exact (D.stored_lists_capacity e he (by omega) i).2

private theorem scale_step (u C k : ℕ) (hu : 3 ≤ u) :
    3*(u^k*(C+1)) ≤ u^(k+1)*(C+1) := by
  calc
    _ ≤ u*(u^k*(C+1)) := Nat.mul_le_mul_right _ hu
    _ = _ := by rw [pow_succ']; ring

theorem finish_cells (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (hn : 10000 ≤ n) (q : CompressionSetup.PrimeSpace n) (B budget : ℕ)
    (hB : B ≤ compressionDictionaryCapacity n) :
    (finish D (CompressionArrayBuild.source D e) q B budget).2 ≤
      inputScale D.input^10*(compressionDictionaryCapacity n+1) := by
  let u := inputScale D.input
  let C := compressionDictionaryCapacity n
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hpow : u^4 ≤ u^9 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 := Nat.mul_le_mul_right (C+1) hpow
  have hlarge : 100 ≤ u^9 := by
    have hx : u ≤ u^9 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega) (by decide : 1 ≤ 9)
    omega
  have hm := scale_step u C 9 (by omega)
  change 3*(u^9*(C+1)) ≤ u^10*(C+1) at hm
  have hlargeC := Nat.mul_le_mul_right (C+1) hlarge
  have ha := CompressionArrayCells.cells_scale D e hn
  change (CompressionArrayCells.run D.weights (CompressionArrayBuild.source D e)
    (2^CompressionSetup.executableCapExponent n)).2 ≤ u^4*(C+1) at ha
  have hC : C ≤ 2^n := by
    unfold C compressionDictionaryCapacity
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change _ ≤ u^10*(C+1)
  unfold finish
  split
  · dsimp only
    cases hA : (CompressionArrayCells.run D.weights (CompressionArrayBuild.source D e)
        (2^CompressionSetup.executableCapExponent n)).1.1 with
    | none =>
      dsimp only
      omega
    | some A =>
      have hl := output_lengths D e hn A hA
      have hs := CompressionScheduleCells.cells D.input hn C B A q.val
        (primeRange_prime q.property).pos (budget-BudgetedCompressionTrial.charge D.input)
        hB hl.1 hl.2 hC
      have hsize := CompressionPreparedCells.arrays_size A C hl.1 hl.2
      dsimp only
      change _ ≤ u^9*(C+1) at hs
      dsimp only [C] at hm hlargeC h4 ha hs ⊢
      omega
  · dsimp only
    omega

def run (D : CompressionData n) (v : Vector (Fin n) n)
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :=
  if CompressionFromPermutation.charge n ≤ budget then
    let domains := CompressionDomainCells.run v
    let out := finish D domains.1.1 q B (budget-CompressionFromPermutation.charge n)
    ((out.1.1,(domains.1.2+1)+out.1.2),domains.2+out.2+128*n+128)
  else ((none,1),4*n+16)

theorem value (D : CompressionData n) (v : Vector (Fin n) n)
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ) :
    (run D v q B budget).1 = CompressionFromPermutation.run D v q B budget := by
  simp only [run,CompressionFromPermutation.run,CompressionDomainCells.value,finish_value,
    BudgetedSeparatorCall.run,BudgetedSeparatorFlow.bind]
  split <;> rfl

theorem cells (D : CompressionData n) (v : Vector (Fin n) n) (e : Equiv.Perm (Fin n))
    (hv : ∀ i : Fin n, v[i.val] = e i) (hn : 10000 ≤ n)
    (q : CompressionSetup.PrimeSpace n) (B budget : ℕ)
    (hB : B ≤ compressionDictionaryCapacity n) :
    (run D v q B budget).2 ≤ inputScale D.input^11*(compressionDictionaryCapacity n+1) := by
  let u := inputScale D.input
  let C := compressionDictionaryCapacity n
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have hu0 : 10000 ≤ u := by omega
  have hd := CompressionDomainCells.cells v
  have hsource : (CompressionDomainCells.run v).1.1 = CompressionArrayBuild.source D e :=
    (congrArg Prod.fst (CompressionDomainCells.value v)).trans
      (CompressionDomains.prepare_value D v e hv)
  have hf := finish_cells D e hn q B (budget-CompressionFromPermutation.charge n) hB
  rw [←hsource] at hf
  change (finish D (CompressionDomainCells.run v).1.1 q B
    (budget-CompressionFromPermutation.charge n)).2 ≤ u^10*(C+1) at hf
  have h2 : (n+1)^2 ≤ u^2 := Nat.pow_le_pow_left hu 2
  have h8 : 4096 ≤ u^8 := by
    have hx : u ≤ u^8 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega) (by decide : 1 ≤ 8)
    omega
  have hsmall : 2048*(n+1)^2+128*n+128 ≤ u^10 := by
    have hm := Nat.mul_le_mul h8 h2
    have hline : 128*(n+1) ≤ 2048*(n+1)^2 := by nlinarith
    have he : u^8*u^2 = u^10 := by rw [←pow_add]
    rw [he] at hm
    nlinarith only [hm,hline]
  have hmul : u^10 ≤ u^10*(C+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hm := scale_step u C 10 (by omega)
  change 3*(u^10*(C+1)) ≤ u^11*(C+1) at hm
  change _ ≤ u^11*(C+1)
  unfold run
  split <;> dsimp only <;> omega

end LowSpaceSubsetSum.CompressionFromPermutationCells

end OAI
