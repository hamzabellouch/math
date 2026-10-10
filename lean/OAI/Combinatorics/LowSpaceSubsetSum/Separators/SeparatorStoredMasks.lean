import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorIncidenceTable
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.WeightEncoding

namespace OAI

/-! # Bit-mask indexing of the stored containment and avoidance tables -/

namespace LowSpaceSubsetSum.SeparatorStoredMasks

open SeparatorIncidenceTable

variable {g : ℕ}

def code (S : Finset (Fin g)) : Fin (2 ^ g) :=
  PaddedRows.index g (fun i => decide (i ∈ S))

def decode (j : Fin (2 ^ g)) : Finset (Fin g) :=
  Finset.univ.filter (fun i => (PaddedRows.index g).symm j i = true)

theorem decode_code (S : Finset (Fin g)) : decode (code S) = S := by
  ext i
  simp [decode, code]

def containsStore (family : Array (Finset (Fin g))) : Array (Array ℕ) :=
  preprocess g family (fun j S => decide (decode j ⊆ S))

def avoidsStore (family : Array (Finset (Fin g))) : Array (Array ℕ) :=
  preprocess g family (fun j S => decide (Disjoint (decode j) S))

theorem containsStore_size (family : Array (Finset (Fin g))) :
    (containsStore family).size = 2 ^ g := by simp [containsStore, preprocess]

theorem avoidsStore_size (family : Array (Finset (Fin g))) :
    (avoidsStore family).size = 2 ^ g := by simp [avoidsStore, preprocess]

def containsList (store : Array (Array ℕ)) (hsize : store.size = 2 ^ g)
    (mask : Finset (Fin g)) : Array ℕ := store[(code mask).val]'(by rw [hsize]; exact (code mask).isLt)

def avoidsList (store : Array (Array ℕ)) (hsize : store.size = 2 ^ g)
    (mask : Finset (Fin g)) : Array ℕ := store[(code mask).val]'(by rw [hsize]; exact (code mask).isLt)

theorem containsList_eq (family : Array (Finset (Fin g))) (mask : Finset (Fin g)) :
    containsList (containsStore family) (containsStore_size family) mask =
      table family (fun D S => decide (D ⊆ S)) mask := by
  simp [containsList, containsStore, preprocess, decode_code, table]

theorem avoidsList_eq (family : Array (Finset (Fin g))) (mask : Finset (Fin g)) :
    avoidsList (avoidsStore family) (avoidsStore_size family) mask =
      table family (fun D S => decide (Disjoint D S)) mask := by
  simp [avoidsList, avoidsStore, preprocess, decode_code, table]

end LowSpaceSubsetSum.SeparatorStoredMasks

end OAI
