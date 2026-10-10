import OAI.Combinatorics.MatrixRemoval.Model
import OAI.Combinatorics.MatrixRemoval.CopyBound

namespace OAI

namespace Problem348

/-- Ordered-copy specialization of the generic constrained-cell bound. -/
theorem copyCount_le_of_cell_mem {k n : ℕ}
    (H : BinaryMatrix (k + 1)) (A : BinaryMatrix n)
    (i j : Fin (k + 1)) (L : Finset (Fin n × Fin n))
    (hL : ∀ rc ∈ orderedCopies H A, (rc.1.val i, rc.2.val j) ∈ L) :
    copyCount H A ≤ L.card * n ^ (2 * k) :=
  CopyBound.card_le_card_mul_pow (orderedCopies H A) i j L hL

/-- Locate the top-left body entry (zero-based index 64) to count fixed-H copies. -/
theorem fixedCopyCount_le_of_body_cell_mem {n : ℕ}
    (A : BinaryMatrix n) (L : Finset (Fin n × Fin n))
    (hL : ∀ rc ∈ orderedCopies fixedH A, (rc.1.val 64, rc.2.val 64) ∈ L) :
    copyCount fixedH A ≤ L.card * n ^ 130 :=
  copyCount_le_of_cell_mem fixedH A 64 64 L hL

/-- The copy bound reduced to concrete leaf localization. -/
theorem fixedCopyDensity_le_of_body_cell_mem {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (A : BinaryMatrix (d * m))
    (L : Finset (Fin (d * m) × Fin (d * m))) (hcard : L.card ≤ m)
    (hL : ∀ rc ∈ orderedCopies fixedH A, (rc.1.val 64, rc.2.val 64) ∈ L) :
    (copyCount fixedH A : ℝ) / (((d * m : ℕ) : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) := by
  apply CopyBound.normalized_count_le hd hm
  exact (fixedCopyCount_le_of_body_cell_mem A L hL).trans
    (Nat.mul_le_mul_right _ hcard)

/-- The exact numerical upper bound appearing in counterexample_sequence. -/
theorem sequenceCopyDensity_le_of_body_cell_mem (h : ℕ)
    (A : BinaryMatrix ((386 * h + 2) * 2 ^ h))
    (L : Finset
      (Fin ((386 * h + 2) * 2 ^ h) × Fin ((386 * h + 2) * 2 ^ h)))
    (hcard : L.card ≤ 2 ^ h)
    (hL : ∀ rc ∈ orderedCopies fixedH A, (rc.1.val 64, rc.2.val 64) ∈ L) :
    (copyCount fixedH A : ℝ) / ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    fixedCopyDensity_le_of_body_cell_mem (by omega : 0 < 386 * h + 2)
      (by positivity : 0 < 2 ^ h) A L hcard hL

/-- A localization witness is enough; no separate leaf-cell set or injectivity
proof is required for the upper bound.  Images can only decrease cardinality. -/
theorem sequenceCopyDensity_le_of_leaf_witness (h : ℕ)
    (A : BinaryMatrix ((386 * h + 2) * 2 ^ h))
    (rowLeaf colLeaf : Fin (2 ^ h) → Fin ((386 * h + 2) * 2 ^ h))
    (hloc : ∀ r c : IncreasingMap 66 ((386 * h + 2) * 2 ^ h),
      (∀ i j, A (r.val i) (c.val j) = fixedH i j) →
      ∃ z, r.val 64 = rowLeaf z ∧ c.val 64 = colLeaf z) :
    (copyCount fixedH A : ℝ) / ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  classical
  let L := Finset.univ.image (fun z => (rowLeaf z, colLeaf z))
  apply sequenceCopyDensity_le_of_body_cell_mem h A L
  · exact Finset.card_image_le.trans (by simp)
  · intro rc hrc
    have hentries : ∀ i j, A (rc.1.val i) (rc.2.val j) = fixedH i j :=
      (Finset.mem_filter.mp hrc).2
    obtain ⟨z, hrow, hcol⟩ := hloc rc.1 rc.2 hentries
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, by simp [hrow, hcol]⟩

end Problem348

end OAI
