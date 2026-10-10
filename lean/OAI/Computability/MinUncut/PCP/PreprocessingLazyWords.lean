import Mathlib
import OAI.Computability.MinUncut.PCP.GraphGap

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open MinUncutGames.Foundations.Complexity

variable {n d : Nat}

def row (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * d) :=
  ⟨v, table.reverseIndex[rowIndex n d (v, p)], table.relations[rowIndex n d (v, p)]⟩

def trueRelation : RelationTable := Vector.replicate 4096 true

def stayRow (d : Nat) (v : Fin n) (p : Fin d) : DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) (v, lazyPorts d (false, p)), trueRelation⟩

def moveRow (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) ((rotation table (v, p)).1,
    lazyPorts d (true, (rotation table (v, p)).2)),
    table.relations[rowIndex n d (v, p)]⟩

def reverseMap (d j : Nat) : Nat := 2 * d * (j / d) + d + j % d

theorem relation_ext {r s : RelationTable}
    (h : ∀ a b, relationAt r a b = relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [relationAt, Prod.eta, Equiv.apply_symm_apply, Fin.getElem_fin] using
    h (relationIndex.symm ⟨i, hi⟩).1 (relationIndex.symm ⟨i, hi⟩).2

theorem row_lazy_stay (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (false, p)) = stayRow d v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      rowIndex n (2 * d) (v, lazyPorts d (false, p)) := by
    rw [← rowIndex_rotation, lazy_rotation_false]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      trueRelation := by
    apply relation_ext
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation, Fin.getElem_fin,
      Vector.getElem_replicate] using lazy_accepts_false table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_lazy_move (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (true, p)) = moveRow table v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      rowIndex n (2 * d) ((rotation table (v, p)).1,
        lazyPorts d (true, (rotation table (v, p)).2)) := by
    rw [← rowIndex_rotation, lazy_rotation_true]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      table.relations[rowIndex n d (v, p)] := by
    apply relation_ext
    intro a b
    exact lazy_accepts_true table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem stayRow_reverse_val (v : Fin n) (p : Fin d) :
    (stayRow d v p).reverseIndex.val = 2 * d * v.val + p.val := by
  simp only [stayRow, rowIndex_val, lazyPorts_false_val]
  omega

theorem moveRow_reverse_val (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (moveRow table v p).reverseIndex.val =
      reverseMap d (row table v p).reverseIndex.val := by
  simp only [moveRow, rowIndex_val, lazyPorts_true_val, reverseMap, row]
  change (table.reverseIndex[rowIndex n d (v, p)]).val % d + d +
      (2 * d) * ((table.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem relationWords_true : relationWords trueRelation = List.replicate 4096 1 := by
  simp only [relationWords, trueRelation, Vector.toList_replicate,
    List.map_replicate, bitWord, ite_true]

theorem stayRow_words (v : Fin n) (p : Fin d) :
    rowWords (stayRow d v p) =
      [v.val, 2 * d * v.val + p.val] ++ List.replicate 4096 1 := by
  rw [rowWords, stayRow_reverse_val]
  exact congrArg (fun words => [v.val, 2 * d * v.val + p.val] ++ words) relationWords_true

theorem moveRow_words (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (moveRow table v p) =
      [v.val, reverseMap d (row table v p).reverseIndex.val] ++
        relationWords (row table v p).relation := by
  rw [rowWords, moveRow_reverse_val]
  rfl

theorem ofFn_rowIndex {α : Type*} (f : Fin (n * d) → α) :
    List.ofFn f = (List.ofFn fun v : Fin n =>
      List.ofFn fun p : Fin d => f (rowIndex n d (v, p))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  congr 1
  funext v
  congr 1
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val]
  ac_rfl

theorem flatRows_list (table : PortTables.Table n d) :
    (flatRows table).toList =
      (List.ofFn fun v : Fin n => List.ofFn (row table v)).flatten := by
  rw [flatRows, Vector.toList_ofFn, ofFn_rowIndex]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem ofFn_lazyPorts {α : Type*} (f : Fin (2 * d) → α) :
    List.ofFn f = List.ofFn (fun p => f (lazyPorts d (false, p))) ++
      List.ofFn (fun p => f (lazyPorts d (true, p))) := by
  have hf (p : Fin d) : rowIndex 2 d (0, p) = lazyPorts d (false, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero, lazyPorts_false_val]
  have ht (p : Fin d) : rowIndex 2 d ((0 : Fin 1).succ, p) = lazyPorts d (true, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_succ, Fin.val_zero, Nat.zero_add,
      Nat.mul_one, lazyPorts_true_val]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, hf, ht] using (ofFn_rowIndex (n := 2) (d := d) f)

def vertexRows (table : PortTables.Table n d) (v : Fin n) :
    List (DartRow n (n * (2 * d))) :=
  List.ofFn (stayRow d v) ++ List.ofFn (moveRow table v)

theorem vertexRows_length (table : PortTables.Table n d) (v : Fin n) :
    (vertexRows table v).length = 2 * d := by
  simp only [vertexRows, List.length_append, List.length_ofFn]
  omega

theorem flatRows_lazy (table : PortTables.Table n d) :
    (flatRows (lazy table)).toList = (List.ofFn (vertexRows table)).flatten := by
  rw [flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_lazyPorts]
  simp only [row_lazy_stay, row_lazy_move]
  rfl

theorem vertexRows_words (table : PortTables.Table n d) (v : Fin n) :
    (vertexRows table v).flatMap rowWords =
      (List.ofFn fun p : Fin d =>
        [v.val, 2 * d * v.val + p.val] ++ List.replicate 4096 1).flatten ++
      (List.ofFn fun p : Fin d =>
        [v.val, reverseMap d (row table v p).reverseIndex.val] ++
          relationWords (row table v p).relation).flatten := by
  have hs : rowWords ∘ stayRow d v = fun p : Fin d =>
      [v.val, 2 * d * v.val + p.val] ++ List.replicate 4096 1 := by
    funext p
    exact stayRow_words v p
  have hm : rowWords ∘ moveRow table v = fun p : Fin d =>
      [v.val, reverseMap d (row table v p).reverseIndex.val] ++
        relationWords (row table v p).relation := by
    funext p
    exact moveRow_words table v p
  simp only [vertexRows, List.flatMap_def, List.map_append, List.map_ofFn,
    List.flatten_append]
  rw [hs, hm]

theorem tableWords_lazy (table : PortTables.Table n d) :
    PortTables.tableWords (lazy table) =
      [n, n * (2 * d)] ++ (List.ofFn (vertexRows table)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_lazy]

theorem tableBits_lazy (table : PortTables.Table n d) :
    PortTables.tableBits (lazy table) =
      encodeWords ([n, n * (2 * d)] ++
        (List.ofFn (vertexRows table)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (lazy table)) = _
  rw [tableWords_lazy]

end MinUncutGames.Foundations.PCP.PreprocessingLazyWords

end

end OAI
