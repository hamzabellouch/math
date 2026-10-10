import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredInitialization
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredReader

namespace OAI

/-! # Measured initialization on the stored representation leaf arrays

The backing arrays have already been generated and sorted. The generic
initializer receives these arrays explicitly; the specialization below fixes
those shared arrays to the ones used by the parent stream. It executes every
row search, first read, and tournament comparison.
-/

namespace LowSpaceSubsetSum.RepresentationStoredInitialization

variable {n : ℕ}

private theorem key_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    (fun x => (RepresentationKeys.pairKey D.input F D.modulus (D.pair j).mode x).1) =
      RepresentationStoredReader.key (D.pair j) := by
  funext x
  exact RepresentationKeys.parent_pairKey_value D F hF j x

def tree (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :=
  FilteredStream.measuredInitialTree (D.pair j).leftRecords (D.pair j).rightRecords
    (RepresentationKeys.pairKey D.input F D.modulus (D.pair j).mode)
    (RepresentationKeys.parentRow D F hF j) (Nat.clog 2 (D.pair j).leftArray.size)

theorem tree_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    (tree D F hF j).1 = (RepresentationStoredReader.start (D.pair j)).tree := by
  rw [tree, FilteredStream.measuredInitialTree_value]
  simp only [key_value D F hF j, RepresentationKeys.parentRow_value D F hF j]
  rfl

def start (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    RepresentationStoredReader.State (D.pair j) × ℕ :=
  let out := tree D F hF j
  have he : out.1 = (RepresentationStoredReader.start (D.pair j)).tree := tree_value D F hF j
  (⟨out.1, he.symm ▸ (RepresentationStoredReader.start (D.pair j)).valid,
    he.symm ▸ (RepresentationStoredReader.start (D.pair j)).aligned,
    he.symm ▸ (RepresentationStoredReader.start (D.pair j)).sorted⟩, out.2)

theorem start_value (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) :
    (start D F hF j).1 = RepresentationStoredReader.start (D.pair j) := by
  have he := tree_value D F hF j
  have ext {a b : RepresentationStoredReader.State (D.pair j)}
      (h : a.tree = b.tree) : a = b := by
    cases a
    cases b
    cases h
    rfl
  apply ext
  exact he

private theorem padded_le (R : ℕ) : 2 ^ Nat.clog 2 R ≤ 2 * (R + 1) := by
  have h := Tournament.padded_nodes_le R (Tournament.build (fun _ : Unit => (0 : ℤ))
    (Nat.clog 2 R) (fun _ => none))
  rw [Tournament.nodes_exact, pow_succ] at h
  omega

private theorem initialization_polynomial {n u : ℕ} (hnu : n + 1 ≤ u) (hu : 10000 ≤ u) :
    2 * (4 * (n + 1) ^ 2 + u ^ 5 + 2 * u ^ 3 + 39) ≤ u ^ 8 := by
  have hu1 : 1 ≤ u := by omega
  have h2 := Nat.pow_le_pow_left hnu 2
  have h25 : u ^ 2 ≤ u ^ 5 := Nat.pow_le_pow_right hu1 (by decide)
  have h35 : u ^ 3 ≤ u ^ 5 := Nat.pow_le_pow_right hu1 (by decide)
  have hc : 39 ≤ 39 * u ^ 5 := Nat.le_mul_of_pos_right _ (by positivity)
  have hp : 92 * u ^ 5 ≤ u ^ 6 := by
    calc
      _ ≤ u * u ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' u 5).symm
  have h68 : u ^ 6 ≤ u ^ 8 := Nat.pow_le_pow_right hu1 (by decide)
  omega

theorem start_work (D : RepresentationParentData n) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (j : Fin 2) (hn : 10000 ≤ n)
    (hL : (D.pair j).leftArray.size ≤ 2 ^ n)
    (hR : (D.pair j).rightRecords.size ≤ 2 ^ n) :
    (start D F hF j).2 ≤ inputScale D.input ^ 8 * ((D.pair j).leftRecords.size + 1) := by
  have hw := FilteredStream.measuredInitialTree_work
    (D.pair j).leftRecords (D.pair j).rightRecords
    (RepresentationKeys.pairKey D.input F D.modulus (D.pair j).mode)
    (RepresentationKeys.parentRow D F hF j) (inputScale D.input ^ 3) (inputScale D.input ^ 5)
    (fun x => RepresentationKeys.pairKey_scale _ _ _ _ x hn)
    (fun x => RepresentationKeys.parentRow_scale D F hF j x hn hR)
    (Nat.clog 2 (D.pair j).leftArray.size)
  have hd := Nat.clog_le_of_le_pow hL
  have hds := Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 2
  have hb := padded_le (D.pair j).leftArray.size
  have hnu : n + 1 ≤ inputScale D.input := by unfold inputScale; omega
  have hp := initialization_polynomial hnu (by omega : 10000 ≤ inputScale D.input)
  change (tree D F hF j).2 ≤ _
  change (FilteredStream.measuredInitialTree _ _ _ _ _).2 ≤ _
  calc
    _ ≤ (4 * (Nat.clog 2 (D.pair j).leftArray.size + 1) ^ 2 + inputScale D.input ^ 5 +
        2 * inputScale D.input ^ 3 + 39) * 2 ^ Nat.clog 2 (D.pair j).leftArray.size := hw
    _ ≤ (4 * (n + 1) ^ 2 + inputScale D.input ^ 5 +
        2 * inputScale D.input ^ 3 + 39) * (2 * ((D.pair j).leftArray.size + 1)) :=
      Nat.mul_le_mul (by omega) hb
    _ = (2 * (4 * (n + 1) ^ 2 + inputScale D.input ^ 5 +
        2 * inputScale D.input ^ 3 + 39)) * ((D.pair j).leftArray.size + 1) := by ring
    _ ≤ _ := by
      rw [(D.pair j).leftRecords_size]
      exact Nat.mul_le_mul_right _ hp

end LowSpaceSubsetSum.RepresentationStoredInitialization

end OAI
