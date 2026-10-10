import Mathlib
import OAI.Computability.MinUncut.PCP.PreprocessingPaddingWords
import OAI.Computability.MinUncut.PCP.PreprocessingRegularLoopWords
import OAI.Computability.MinUncut.Machines.PreprocessingMachineBounds

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open MinUncutGames.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

theorem blocksPrefix_length_le {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    (blocksPrefix f k).length ≤ (List.ofFn f).flatten.length := by
  have h := congrArg List.length (blocksPrefix_append_suffix f k)
  simp only [List.length_append] at h
  omega

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

def ownerBits (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) : List Bool :=
  (List.ofFn (dummyVertexBits t p tables v)).flatten

def originalPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ blocksPrefix (originalVertexBits t p tables) k

def ownerPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ (List.ofFn (originalVertexBits t p tables)).flatten ++
    blocksPrefix (ownerBits t p tables) k

def dummyPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) (k : Nat) : List Bool :=
  ownerPrefix t p tables v.val ++ blocksPrefix (dummyVertexBits t p tables v) k

variable (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)

theorem originalPrefix_length_le (k : Nat) :
    (originalPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (originalVertexBits t p tables) k
  rw [tableBits_ofCloudTables]
  simp only [originalPrefix, header, List.length_append]
  omega

theorem ownerPrefix_length_le (k : Nat) :
    (ownerPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (ownerBits t p tables) k
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  rw [tableBits_ofCloudTables]
  simp only [ownerPrefix, header, List.length_append] at *
  simp only [he] at *
  omega

theorem dummyPrefix_length_le (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t p tables v k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have hi := blocksPrefix_length_le (dummyVertexBits t p tables v) k
  have ho := blocksPrefix_length_le (ownerBits t p tables) (v.val + 1)
  rw [blocksPrefix_succ _ _ v.isLt] at ho
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  simp only [Fin.eta] at ho
  rw [tableBits_ofCloudTables]
  simp only [dummyPrefix, ownerPrefix, header, ownerBits, List.length_append] at *
  simp only [he] at *
  omega

theorem regular_originalPrefix_le (H : BaseTable) (k : Nat) :
    (originalPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (originalPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_ownerPrefix_le (H : BaseTable) (k : Nat) :
    (ownerPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (ownerPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_dummyPrefix_le (H : BaseTable) (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t (padding t) (familyCloudTable H t) v k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (dummyPrefix_length_le t (padding t) (familyCloudTable H t) v k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem visits_le_input :
    t.darts + t.vertices + (∑ v, padding t v) + 1 ≤
      (ExpanderFamily.growth + 1) * PreprocessingMachineBounds.inputLength t + 1 := by
  have hv := PreprocessingMachineBounds.regularVertices_le_input t
  have hn := GraphTables.vertices_le_tableBits_length t
  change t.vertices ≤ PreprocessingMachineBounds.inputLength t at hn
  unfold vertexCount at hv
  rw [Nat.add_mul, one_mul]
  omega

theorem sum_body_costs_le (old : Fin t.darts → Nat) (owners : Fin t.vertices → Nat)
    (dummy : ∀ v : Fin t.vertices, Fin (padding t v) → Nat) (setup cap : Nat)
    (hs : setup ≤ cap) (ho : ∀ e, old e ≤ cap) (hv : ∀ v, owners v ≤ cap)
    (hd : ∀ v j, dummy v j ≤ cap) :
    setup + (∑ e, old e) + (∑ v, owners v) + (∑ v, ∑ j, dummy v j) ≤
      ((ExpanderFamily.growth + 1) * PreprocessingMachineBounds.inputLength t + 1) * cap := by
  have hOld : (∑ e, old e) ≤ t.darts * cap := by
    simpa using Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => ho e)
  have hOwners : (∑ v, owners v) ≤ t.vertices * cap := by
    simpa using Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hv v)
  have hDummy : (∑ v, ∑ j, dummy v j) ≤ (∑ v, padding t v) * cap := by
    calc
      _ ≤ ∑ v, padding t v * cap := by
        apply Finset.sum_le_sum
        intro v _
        simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd v j)
      _ = _ := (Finset.sum_mul ..).symm
  calc
    _ ≤ (t.darts + t.vertices + (∑ v, padding t v) + 1) * cap := by
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, one_mul]
      omega
    _ ≤ _ := Nat.mul_le_mul_right cap (visits_le_input t)

end MinUncutGames.Foundations.PCP.PreprocessingRegularBounds

end

end OAI
