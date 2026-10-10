import Mathlib
import OAI.Computability.MinUncut.Search.CodeFoldComputable
import OAI.Computability.MinUncut.Estimates.HeapInitializationMath

namespace OAI

section
namespace MinUncut.CodeEffective.Layout
open Turing.ToPartrec MinUncut.Costed.Arena
abbrev Cell := ℕ × ℕ × ℕ × ℕ
def shift (b : ℕ) (x : Cell) : Cell :=
  (x.1,rebasePointer b x.2.1,rebasePointer b x.2.2.1,x.2.2.2)
lemma p_pointer : Primrec₂ rebasePointer :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp Primrec.fst Primrec.snd)
lemma p_shift : Primrec₂ shift :=
  (Primrec.fst.comp Primrec.snd).pair
    ((p_pointer.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      ((p_pointer.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
def binary (tag : ℕ) (l r : List Cell) : List Cell :=
  (tag,l.length,l.length+r.length,0)::(r.map (shift l.length)++l)
def unary (l : List Cell) : List Cell := (6,l.length,0,0)::l
lemma p_binary (tag : ℕ) : Primrec₂ (binary tag) := by
  have hl : Primrec (fun p : List Cell × List Cell=>p.1.length) := Primrec.list_length.comp Primrec.fst
  have hr : Primrec (fun p : List Cell × List Cell=>p.2.length) := Primrec.list_length.comp Primrec.snd
  have hm : Primrec (fun p : List Cell × List Cell=>p.2.map (shift p.1.length)) :=
    Primrec.list_map Primrec.snd (p_shift.comp (hl.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_cons.comp
    ((Primrec.const tag).pair (hl.pair ((Primrec.nat_add.comp hl hr).pair (Primrec.const 0))))
    (Primrec.list_append.comp hm Primrec.fst)
lemma p_unary : Primrec unary :=
  Primrec.list_cons.comp
    ((Primrec.const 6).pair (Primrec.list_length.pair ((Primrec.const 0).pair (Primrec.const 0)))) Primrec.id

def cells : Code → List Cell := fold [(0,0,0,0)] [(1,0,0,0)] [(2,0,0,0)] (binary 3) (binary 4) (binary 5) unary
lemma p_cells : Primrec cells := primrec_fold _ _ _ (p_binary 3) (p_binary 4) (p_binary 5) p_unary

def pack (n : Node) : Cell := (n 0,n 1,n 2,n 3)
lemma pack_rebase (d : ℕ) (h : Heap) :
    (h.map (rebaseNode d)).map pack=(h.map pack).map (shift d) := by
  simp only [List.map_map]
  rfl
lemma cells_eq (c : Code) : cells c=(codeCells c 0).map pack := by
  induction c with
  | zero' | succ | tail => rfl
  | cons f g ih ih' | comp f g ih ih' | case f g ih ih' =>
    have hg:=codeCells_rebase g 0 (codeCells f 0).length
    simp only [Nat.zero_add] at hg
    change binary _ (cells f) (cells g)=_
    rw [binary,ih,ih']
    simp only [codeCells,Nat.zero_add,List.length_map,hg,List.map_cons,List.map_append,
      pack_rebase,pack,node_zero,node_one,node_two,node_three]
  | fix f ih =>
    change unary (cells f)=_
    rw [unary,ih]
    simp only [codeCells,Nat.zero_add,List.length_map,List.map_cons,pack,node_zero,node_one,node_two,node_three]

def flattenCell (x : Cell) : List ℕ := [x.1,x.2.1,x.2.2.1,x.2.2.2]
lemma p_flattenCell : Primrec flattenCell :=
  Primrec.list_cons.comp Primrec.fst (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const []))))
lemma p_words : Primrec (fun c=>words (codeCells c 0)) := by
  have hh : Primrec (fun c=>(cells c).flatMap flattenCell) :=
    Primrec.list_flatMap p_cells (p_flattenCell.comp Primrec.snd).to₂
  exact hh.of_eq (by intro c; simp only [cells_eq,List.flatMap_map,words]; congr 1)
lemma p_count : Primrec (fun c=>(codeCells c 0).length) :=
  (Primrec.list_length.comp p_cells).of_eq (by intro c; simp only [cells_eq,List.length_map])
lemma c_prefix : Computable (fun c=>(codeCells c 0).length::words (codeCells c 0)) :=
  (Primrec.list_cons.comp p_count p_words).to_comp
end MinUncut.CodeEffective.Layout

end

end OAI
