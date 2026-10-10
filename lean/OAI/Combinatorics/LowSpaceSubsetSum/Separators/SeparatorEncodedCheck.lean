import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorCoverage

namespace OAI

/-! # Applying the four-block checker to original indexed top masks -/

namespace LowSpaceSubsetSum

structure TopCoordinates (n g : ℕ) where
  index : Fin 4 × Fin g → Fin n
  injective : Function.Injective index

namespace TopCoordinates

variable {n g : ℕ} (C : TopCoordinates n g)

def domain : Finset (Fin n) := Finset.univ.image C.index

def encodeMask (S : Finset (Fin n)) : Finset (Fin 4 × Fin g) :=
  Finset.univ.filter (fun j => C.index j ∈ S)

@[simp] theorem encodeMask_mem (S : Finset (Fin n)) (j : Fin 4 × Fin g) :
    j ∈ C.encodeMask S ↔ C.index j ∈ S := by simp [encodeMask]

def encodeEntry (x : Entry (Fin n)) : SeparatorCheck.Record g :=
  ⟨x.value, C.encodeMask x.mask⟩

theorem disjoint_of_encoded {S T : Finset (Fin n)} (hS : S ⊆ C.domain)
    (h : Disjoint (C.encodeMask S) (C.encodeMask T)) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, _, he⟩ := Finset.mem_image.mp (hS hi)
  apply Finset.disjoint_left.mp h (C.encodeMask_mem S j |>.mpr (he ▸ hi))
  exact (C.encodeMask_mem T j).mpr (he ▸ hj)

theorem encoded_disjoint {S T : Finset (Fin n)} (h : Disjoint S T) :
    Disjoint (C.encodeMask S) (C.encodeMask T) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  exact Finset.disjoint_left.mp h ((C.encodeMask_mem S j).mp hj) ((C.encodeMask_mem T j).mp hk)

def check (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Entry (Fin n))) : SeparatorTraversal.Result :=
  SeparatorCheck.run n families target (xs.map C.encodeEntry) (ys.map C.encodeEntry)

theorem sound (families : Fin 4 → Array (Finset (Fin g))) (target : ℤ)
    (xs ys : List (Entry (Fin n))) (hsize : xs.length + ys.length ≤ 2 ^ n)
    (htop : ∀ x ∈ xs, x.mask ⊆ C.domain)
    (hyes : (C.check families target xs ys).accepted = true) :
    ∃ x ∈ xs, ∃ y ∈ ys, Disjoint x.mask y.mask ∧ x.value + y.value = target := by
  obtain ⟨x, hxmap, y, hymap, hd, hw⟩ := SeparatorCheck.sound n families target
    (xs.map C.encodeEntry) (ys.map C.encodeEntry) (by simpa only [List.length_map] using hsize) hyes
  obtain ⟨x, hxOrig, rfl⟩ := List.mem_map.mp hxmap
  obtain ⟨y, hyOrig, rfl⟩ := List.mem_map.mp hymap
  exact ⟨x, hxOrig, y, hyOrig, C.disjoint_of_encoded (htop x hxOrig) hd, hw⟩

/-- The stored key witnesses suffice for original-input one-sided soundness. -/
theorem subset_sum_sound (I : Instance n) (F : Finset (Fin n))
    (families : Fin 4 → Array (Finset (Fin g)))
    (xs ys : List (Entry (Fin n))) (hsize : xs.length + ys.length ≤ 2 ^ n)
    (leftDomain rightDomain : Finset (Fin n))
    (hshared : leftDomain ∩ rightDomain ⊆ C.domain)
    (hleft : ∀ x ∈ xs, Represents (flip (fun i => (I.values i : ℤ)) F) leftDomain C.domain x)
    (hright : ∀ y ∈ ys, Represents (flip (fun i => (I.values i : ℤ)) F) rightDomain C.domain y)
    (hyes : (C.check families ((I.target : ℤ) - weight (fun i => (I.values i : ℤ)) F)
      xs ys).accepted = true) : Solvable I := by
  have htop (x : Entry (Fin n)) (hx : x ∈ xs) : x.mask ⊆ C.domain := by
    obtain ⟨S, _, _, hm⟩ := hleft x hx
    rw [← hm]
    exact Finset.inter_subset_right
  obtain ⟨x, hx, y, hy, hd, hw⟩ := C.sound families _ xs ys hsize htop hyes
  exact entry_match_sound I F hshared (hleft x hx) (hright y hy) hd hw

end TopCoordinates
end LowSpaceSubsetSum

end OAI
