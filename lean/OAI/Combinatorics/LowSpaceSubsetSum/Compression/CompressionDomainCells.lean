import OAI.Combinatorics.LowSpaceSubsetSum.Storage.IntervalDomainCells

namespace OAI

/-! # Live cells for the ten concrete compression domains

Only arithmetic interval tests, stored permutation lookups and list sorts
are executed. Completed domains are retained while subsequent rows are
constructed, and the source finite sets appear only in the value theorem.
-/

namespace LowSpaceSubsetSum.CompressionDomainCells

open scoped BigOperators
variable {n : ℕ}

def run (v : Vector (Fin n) n) : (CompressionArrayBuild.Blocks n × ℕ) × ℕ :=
  let compact := Vector.ofFn (fun i : Fin 7 =>
    IntervalDomainCells.run v (i.val*compressionHalfSize n) (compressionHalfSize n))
  let left := IntervalDomainCells.run v (7*compressionHalfSize n) (compressionLeftRawSize n)
  let right := Vector.ofFn (fun i : Fin 2 => IntervalDomainCells.run v
    (IntervalDomainExecution.rightStart n i) (IntervalDomainExecution.rightLength n i))
  ((⟨fun i => compact[i.val].1.1, left.1.1, fun i => right[i.val].1.1⟩,
      (∑ i : Fin 7, compact[i.val].1.2)+left.1.2+(∑ i : Fin 2, right[i.val].1.2)+20),
    (∑ i : Fin 7, compact[i.val].2)+left.2+(∑ i : Fin 2, right[i.val].2)+40*n+64)

theorem value (v : Vector (Fin n) n) : (run v).1 = CompressionDomains.prepare v := by
  rw [← IntervalDomainExecution.compression_source]
  simp only [run, IntervalDomainExecution.compression, Vector.getElem_ofFn,
    IntervalDomainCells.run_value]

theorem cells (v : Vector (Fin n) n) : (run v).2 ≤ 2048*(n+1)^2 := by
  have hc := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 7))) =>
    IntervalDomainCells.run_cells v (i.val*compressionHalfSize n) (compressionHalfSize n))
  have hr := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) =>
    IntervalDomainCells.run_cells v
      (IntervalDomainExecution.rightStart n i) (IntervalDomainExecution.rightLength n i))
  have hl := IntervalDomainCells.run_cells v (7*compressionHalfSize n) (compressionLeftRawSize n)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hc hr
  simp only [run, Vector.getElem_ofFn, Fin.eta]
  nlinarith only [hc, hr, hl, Nat.zero_le (n^2)]

end LowSpaceSubsetSum.CompressionDomainCells

end OAI
