import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorEncodedCheck
import Mathlib.Data.Finset.Sort

namespace OAI

/-! # Concrete local coordinates obtained by sorting the four top blocks -/

namespace LowSpaceSubsetSum.TopCoordinates

variable {n g : ℕ}

/-- Mathlib's increasing finite-set enumeration is implemented by sorting;
the coordinate map contains no choice of a solution subset. -/
def ofBlocks (B : Fin 4 → Finset (Fin n)) (hcard : ∀ i, (B i).card = g)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) : TopCoordinates n g where
  index p := ((B p.1).orderIsoOfFin (hcard p.1) p.2).val
  injective := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    change (((B i).orderIsoOfFin (hcard i)) j).val =
      (((B k).orderIsoOfFin (hcard k)) l).val at h
    have hik : i = k := by
      by_contra hne
      have hm := ((B i).orderIsoOfFin (hcard i) j).property
      have hn := ((B k).orderIsoOfFin (hcard k) l).property
      have hn' : (((B i).orderIsoOfFin (hcard i)) j).val ∈ B k := by
        rw [h]
        exact hn
      exact Finset.disjoint_left.mp (hdisj i k hne) hm hn'
    subst k
    have hjl : j = l := (B i).orderIsoOfFin (hcard i) |>.injective (Subtype.ext h)
    exact Prod.ext rfl hjl

variable (B : Fin 4 → Finset (Fin n)) (hcard : ∀ i, (B i).card = g)
  (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))

theorem ofBlocks_index_mem (i : Fin 4) (j : Fin g) :
    (ofBlocks B hcard hdisj).index (i, j) ∈ B i :=
  ((B i).orderIsoOfFin (hcard i) j).property

theorem ofBlocks_index_surjective (i : Fin 4) {x : Fin n} (hx : x ∈ B i) :
    ∃ j : Fin g, (ofBlocks B hcard hdisj).index (i, j) = x := by
  refine ⟨((B i).orderIsoOfFin (hcard i)).symm ⟨x, hx⟩, ?_⟩
  change (((B i).orderIsoOfFin (hcard i))
    (((B i).orderIsoOfFin (hcard i)).symm ⟨x, hx⟩)).val = x
  rw [OrderIso.apply_symm_apply]

theorem ofBlocks_domain :
    (ofBlocks B hcard hdisj).domain = Finset.univ.biUnion B := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ofBlocks_index_mem B hcard hdisj i j⟩
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, rfl⟩ := ofBlocks_index_surjective B hcard hdisj i hi
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

theorem ofBlocks_local_image (S : Finset (Fin n)) (i : Fin 4) :
    (SeparatorCheck.localMask i ((ofBlocks B hcard hdisj).encodeMask S)).image
      (fun j => (ofBlocks B hcard hdisj).index (i, j)) = S ∩ B i := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_inter.mpr ⟨((ofBlocks B hcard hdisj).encodeMask_mem S (i, j)).mp
      ((SeparatorCheck.localMask_mem i _ j).mp hj), ofBlocks_index_mem B hcard hdisj i j⟩
  · intro hx
    obtain ⟨hxS, hxB⟩ := Finset.mem_inter.mp hx
    obtain ⟨j, rfl⟩ := ofBlocks_index_surjective B hcard hdisj i hxB
    exact Finset.mem_image.mpr ⟨j, (SeparatorCheck.localMask_mem i _ j).mpr
      (((ofBlocks B hcard hdisj).encodeMask_mem S (i, j)).mpr hxS), rfl⟩

theorem ofBlocks_local_card (S : Finset (Fin n)) (i : Fin 4) :
    (SeparatorCheck.localMask i ((ofBlocks B hcard hdisj).encodeMask S)).card = (S ∩ B i).card := by
  have hinj : Function.Injective (fun j => (ofBlocks B hcard hdisj).index (i, j)) := by
    intro j k h
    exact Prod.mk.inj ((ofBlocks B hcard hdisj).injective h) |>.2
  have h := congrArg Finset.card (ofBlocks_local_image B hcard hdisj S i)
  rwa [Finset.card_image_of_injective _ hinj] at h

end LowSpaceSubsetSum.TopCoordinates

end OAI
