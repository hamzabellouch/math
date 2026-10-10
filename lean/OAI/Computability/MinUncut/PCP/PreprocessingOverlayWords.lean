import Mathlib
import OAI.Computability.MinUncut.PCP.ExpanderRowControl
import OAI.Computability.MinUncut.PCP.PreprocessingLazyWords

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

abbrev row := @PreprocessingLazyWords.row
abbrev trueRelation := PreprocessingLazyWords.trueRelation

def oldReverseMap (d e j : Nat) : Nat := (d + e) * (j / d) + j % d
def expanderReverseMap (d e j : Nat) : Nat := (d + e) * (j / e) + d + j % e

def oldRow (G : PortTables.Table n d) (e : Nat) (v : Fin n) (p : Fin d) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((rotation G (v, p)).1,
    overlayPorts d e (.inl (rotation G (v, p)).2)),
    G.relations[rowIndex n d (v, p)]⟩

def expanderRow (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
    overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)), trueRelation⟩

private theorem relation_ext {r s : RelationTable}
    (h : ∀ a b, relationAt r a b = relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [relationAt, Prod.eta, Equiv.apply_symm_apply, Fin.getElem_fin] using
    h (relationIndex.symm ⟨i, hi⟩).1 (relationIndex.symm ⟨i, hi⟩).2

theorem row_overlay_old (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin d) :
    row (overlay G H) v (overlayPorts d e (.inl p)) = oldRow G e v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      rowIndex n (d + e) ((rotation G (v, p)).1,
        overlayPorts d e (.inl (rotation G (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_old]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      G.relations[rowIndex n d (v, p)] := by
    apply relation_ext
    exact overlay_accepts_old G H v p
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_overlay_expander (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    row (overlay G H) v (overlayPorts d e (.inr p)) = expanderRow d H v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
        overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_expander]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      trueRelation := by
    apply relation_ext
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation,
      PreprocessingLazyWords.trueRelation, Fin.getElem_fin, Vector.getElem_replicate] using
      overlay_accepts_expander G H v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem oldRow_reverse_val (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (oldRow G e v p).reverseIndex.val = oldReverseMap d e (row G v p).reverseIndex.val := by
  simp only [oldRow, rowIndex_val, overlayPorts_inl_val, oldReverseMap, row,
    PreprocessingLazyWords.row]
  change (G.reverseIndex[rowIndex n d (v, p)]).val % d +
      (d + e) * ((G.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem expanderRow_reverse_val (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    (expanderRow d H v p).reverseIndex.val =
      expanderReverseMap d e (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val := by
  simp only [expanderRow, rowIndex_val, overlayPorts_inr_val, expanderReverseMap]
  change d + (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val % e +
      (d + e) * ((ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val / e) = _
  omega

theorem oldRow_words (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (oldRow G e v p) =
      [v.val, oldReverseMap d e (row G v p).reverseIndex.val] ++
        relationWords (row G v p).relation := by
  rw [rowWords, oldRow_reverse_val]
  rfl

theorem expanderRow_words (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    rowWords (expanderRow d H v p) =
      [v.val, expanderReverseMap d e
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++
        List.replicate 4096 1 := by
  rw [rowWords, expanderRow_reverse_val]
  exact congrArg (fun rs => [v.val, expanderReverseMap d e
    (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++ rs)
      PreprocessingLazyWords.relationWords_true

theorem ofFn_overlayPorts {α : Type*} (f : Fin (d + e) → α) :
    List.ofFn f = List.ofFn (fun p => f (overlayPorts d e (.inl p))) ++
      List.ofFn (fun p => f (overlayPorts d e (.inr p))) := by
  rw [List.ofFn_add]
  rfl

def vertexRows (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n) :
    List (DartRow n (n * (d + e))) :=
  List.ofFn (oldRow G e v) ++ List.ofFn (expanderRow d H v)

theorem vertexRows_length (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n) :
    (vertexRows G H v).length = d + e := by
  simp only [vertexRows, List.length_append, List.length_ofFn]

theorem flatRows_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    (flatRows (overlay G H)).toList = (List.ofFn (vertexRows G H)).flatten := by
  rw [PreprocessingLazyWords.flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_overlayPorts]
  simp only [row_overlay_old, row_overlay_expander]
  rfl

theorem vertexRows_words (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n) :
    (vertexRows G H v).flatMap rowWords =
      (List.ofFn fun p : Fin d =>
        [v.val, oldReverseMap d e (row G v p).reverseIndex.val] ++
          relationWords (row G v p).relation).flatten ++
      (List.ofFn fun p : Fin e =>
        [v.val, expanderReverseMap d e
          (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++
          List.replicate 4096 1).flatten := by
  have ho : rowWords ∘ oldRow G e v = fun p : Fin d =>
      [v.val, oldReverseMap d e (row G v p).reverseIndex.val] ++
        relationWords (row G v p).relation := by
    funext p
    exact oldRow_words G v p
  have he : rowWords ∘ expanderRow d H v = fun p : Fin e =>
      [v.val, expanderReverseMap d e
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++
        List.replicate 4096 1 := by
    funext p
    exact expanderRow_words H v p
  simp only [vertexRows, List.flatMap_def, List.map_append, List.map_ofFn, List.flatten_append]
  rw [ho, he]

theorem tableWords_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableWords (overlay G H) =
      [n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_overlay]

theorem tableBits_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableBits (overlay G H) = encodeWords
      ([n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (overlay G H)) = _
  rw [tableWords_overlay]

theorem rotationWords_vertices (H : ExpanderTables.Table n e) :
    ExpanderTableWords.rotationWords H =
      (List.ofFn fun v : Fin n => List.ofFn fun p : Fin e =>
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val).flatten := by
  have hflat : ExpanderTableWords.rotationWords H =
      List.ofFn (fun i : Fin (n * e) => (ExpanderTables.reverseIndex H i).val) := by
    apply List.ext_getElem
    · simp [ExpanderTableWords.rotationWords_length]
    · intro i hi hj
      rw [ExpanderTableWords.rotationWords_getElem H i (by simpa using hi)]
      simp only [List.getElem_ofFn]
  rw [hflat, PreprocessingLazyWords.ofFn_rowIndex]
  rfl

end MinUncutGames.Foundations.PCP.PreprocessingOverlayWords

end

end OAI
