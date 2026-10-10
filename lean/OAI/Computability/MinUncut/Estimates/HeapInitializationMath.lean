import Mathlib
import OAI.Computability.MinUncut.Estimates.CodeContinuations

namespace OAI

section
namespace MinUncut.Costed.Arena
open Turing.ToPartrec

def rebasePointer (d a : ℕ) : ℕ := if a=0 then 0 else d+a
def rebaseNode (d : ℕ) (n : Node) : Node :=
  node (n 0) (rebasePointer d (n 1)) (rebasePointer d (n 2)) (n 3)

lemma codeCells_length_eq (c : Code) (a b : ℕ) :
    (codeCells c a).length=(codeCells c b).length := by
  induction c generalizing a b with
  | zero' | succ | tail => rfl
  | cons f g ih ih' | comp f g ih ih' | case f g ih ih' =>
    simp only [codeCells,List.length_cons,List.length_append]
    rw [ih a b, ih']
  | fix f ih => simp only [codeCells,List.length_cons,ih a b]

lemma codeCells_pos (c : Code) (b : ℕ) : 0<(codeCells c b).length := by
  cases c <;> simp [codeCells]

lemma codeCells_rebase (c : Code) (b d : ℕ) :
    codeCells c (b+d)=(codeCells c b).map (rebaseNode d) := by
  induction c generalizing b with
  | zero' | succ | tail => simp [codeCells,rebaseNode,rebasePointer]
  | cons f g ih ih' | comp f g ih ih' | case f g ih ih' =>
    have hf := codeCells_pos f b
    have hg := codeCells_pos g (b+(codeCells f b).length)
    have he := codeCells_length_eq f (b+d) b
    simp only [codeCells,List.map_cons,List.map_append]
    rw [he,show b+d+(codeCells f b).length=(b+(codeCells f b).length)+d by omega]
    rw [codeCells_length_eq g ((b+(codeCells f b).length)+d) (b+(codeCells f b).length),
      ih,ih']
    congr 1
    simp only [rebaseNode,node_zero,node_one,node_two,node_three,rebasePointer]
    erw [ite_eq_right (by omega : b+(codeCells f b).length≠0),
      ite_eq_right (by omega : b+(codeCells f b).length+(codeCells g (b+(codeCells f b).length)).length≠0)]
    congr 1 <;> omega
  | fix f ih =>
    have hf:=codeCells_pos f b
    simp only [codeCells,List.map_cons,ih]
    congr 1
    simp only [rebaseNode,node_zero,node_one,node_two,node_three,rebasePointer]
    erw [ite_eq_right (by omega : b+(codeCells f b).length≠0)]
    congr 1
    simp only [List.length_map]
    omega

lemma words_append (h g : Heap) : words (h++g)=words h++words g := by
  simp only [words,List.flatMap_append]

lemma listCells_ptr (v : List ℕ) (h : Heap) :
    (listCells v h).1=if v=[] then 0 else v.length+h.length := by
  cases v with
  | nil => rfl
  | cons a v => simp only [listCells,listCells_length,List.cons_ne_nil,ite_false,List.length_cons]; omega

def groupWords (v : List ℕ) : Heap :=
  (List.range (v.length/4)).map (fun i j=>((v.drop (4*i+j.val)).headI))
lemma groupWords_length (v : List ℕ) : (groupWords v).length=v.length/4 := by
  simp [groupWords]
lemma groupWords_words (v : List ℕ) (h : 4∣v.length) : words (groupWords v)=v := by
  apply List.ext_getElem
  · simp only [length_words,groupWords_length]
    omega
  · intro i hi hv
    have hq : i/4<v.length/4 := by omega
    have hr : i%4<4 := Nat.mod_lt _ (by decide)
    have hat:=words_at (groupWords v) (i/4) ⟨i%4,hr⟩
    have he : 4*(i/4)+i%4=i := by omega
    rw [he,List.drop_eq_getElem_cons hi] at hat
    simp only [List.headI_cons] at hat
    rw [hat]
    have hn : i/4<(groupWords v).length := by simpa only [groupWords_length] using hq
    rw [List.drop_eq_getElem_cons hn,List.headD_cons]
    simp only [groupWords]
    erw [List.getElem_map,List.getElem_range]
    rw [he,List.drop_eq_getElem_cons hv]
    rfl

end MinUncut.Costed.Arena

end

end OAI
