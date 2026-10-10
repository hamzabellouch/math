import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.CopyBoundFixed

namespace OAI

/-!
# Transfer raw-host copy localization to the fixed counting target

The row and column enumerations are independent.  This adapter does not assume
that either enumeration preserves an ambient order on the sum type: the raw
localization hypothesis uses exactly the two induced finite orders.
-/

noncomputable section
namespace Problem348.Construction

/-- The canonical host viewed through independent row/column enumerations. -/
def hostMatrix {h n : ℕ} (er ec : Position h ≃ Fin n) : BinaryMatrix n :=
  fun i j => host (er.symm i) (ec.symm j)

/-- A raw leaf is shared by the plus and minus names on both axes. -/
def countedLeaf {h : ℕ} (z : Fin (2 ^ h)) : Position h :=
  Sum.inr (Sum.inl (Fin.last (2 * h), z))

/-- The depth/node conclusion of the mode analysis is exactly a leaf-diagonal
witness in the raw-position type, including the shared leaf class. -/
theorem exists_countedLeaf_of_depth_node {h : ℕ} (r c : VariablePosition h)
    (hr : depth r = h) (hc : depth c = h) (hnode : node r = node c) :
    ∃ z, (Sum.inr (Sum.inl r) : Position h) = countedLeaf z ∧
      (Sum.inr (Sum.inl c) : Position h) = countedLeaf z := by
  have hrclass : r.1 = Fin.last (2 * h) := by
    apply Fin.ext
    have hb := r.1.isLt
    have hr' : r.1.val / 2 = h := hr
    simp only [Fin.val_last]
    omega
  have hcclass : c.1 = Fin.last (2 * h) := by
    apply Fin.ext
    have hb := c.1.isLt
    have hc' : c.1.val / 2 = h := hc
    simp only [Fin.val_last]
    omega
  have hoffset : r.2 = c.2 := by
    apply Fin.ext
    simpa [node, hr, hc] using hnode
  refine ⟨r.2, ?_, ?_⟩
  · simp only [countedLeaf, Sum.inr.injEq, Sum.inl.injEq]
    exact Prod.ext hrclass rfl
  · simp only [countedLeaf, Sum.inr.injEq, Sum.inl.injEq]
    exact Prod.ext hcclass hoffset.symm

/-- Exact localization of a raw copy transports without any count-equivalence
machinery.  The increasing-map hypotheses refer to the supplied enumerations. -/
theorem localization_on_fin {h n : ℕ} (er ec : Position h ≃ Fin n)
    (hloc : ∀ r c : Fin 66 → Position h,
      StrictMono (fun i => er (r i)) → StrictMono (fun j => ec (c j)) →
      (∀ i j, host (r i) (c j) = fixedH i j) →
      ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z)
    (r c : IncreasingMap 66 n)
    (hentries : ∀ i j, hostMatrix er ec (r.val i) (c.val j) = fixedH i j) :
    ∃ z, r.val 64 = er (countedLeaf z) ∧ c.val 64 = ec (countedLeaf z) := by
  obtain ⟨z, hr, hc⟩ := hloc (fun i => er.symm (r.val i))
    (fun j => ec.symm (c.val j)) (by simpa using r.property)
    (by simpa using c.property) hentries
  refine ⟨z, ?_, ?_⟩
  · simpa using congrArg er hr
  · simpa using congrArg ec hc

/-- Integer bound used by the sequence assembly, from raw-host localization. -/
theorem host_copyCount_le {h n : ℕ} (er ec : Position h ≃ Fin n)
    (hloc : ∀ r c : Fin 66 → Position h,
      StrictMono (fun i => er (r i)) → StrictMono (fun j => ec (c j)) →
      (∀ i j, host (r i) (c j) = fixedH i j) →
      ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z) :
    copyCount fixedH (hostMatrix er ec) ≤ 2 ^ h * n ^ 130 := by
  classical
  let L := Finset.univ.image (fun z : Fin (2 ^ h) =>
    (er (countedLeaf z), ec (countedLeaf z)))
  have hcard : L.card ≤ 2 ^ h := Finset.card_image_le.trans (by simp)
  apply (fixedCopyCount_le_of_body_cell_mem (hostMatrix er ec) L ?_).trans
    (Nat.mul_le_mul_right _ hcard)
  intro rc hrc
  obtain ⟨z, hr, hc⟩ := localization_on_fin er ec hloc rc.1 rc.2
    (Finset.mem_filter.mp hrc).2
  exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, by simp [hr, hc]⟩

/-- The exact density upper bound of counterexample_sequence for this raw host. -/
theorem host_copyDensity_le (h : ℕ)
    (er ec : Position h ≃ Fin ((386 * h + 2) * 2 ^ h))
    (hloc : ∀ r c : Fin 66 → Position h,
      StrictMono (fun i => er (r i)) → StrictMono (fun j => ec (c j)) →
      (∀ i j, host (r i) (c j) = fixedH i j) →
      ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z) :
    (copyCount fixedH (hostMatrix er ec) : ℝ) /
        ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  apply sequenceCopyDensity_le_of_leaf_witness h (hostMatrix er ec)
    (fun z => er (countedLeaf z)) (fun z => ec (countedLeaf z))
  exact localization_on_fin er ec hloc

end Problem348.Construction

end

end OAI
