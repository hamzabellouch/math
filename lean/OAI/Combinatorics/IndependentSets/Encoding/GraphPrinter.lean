import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.BinaryNameTables

namespace OAI

namespace LargeIndependentSets.GraphPrinter
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open scoped Classical
noncomputable section

lemma matrix_eq (G : Graph) :
    (List.finRange G.vertices).flatMap (fun i => (List.finRange G.vertices).map (G.adj i)) =
      List.ofFn (fun i : Fin (G.vertices*G.vertices) => G.adj i.divNat i.modNat) := by
  rw [List.ofFn_mul]
  simp only [List.ofFn_eq_map,List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i _
  apply List.map_congr_left
  intro j _
  congr 1
  · apply Fin.ext
    simp only [Fin.divNat]
    rw [Nat.add_comm (i.val * G.vertices),Nat.add_mul_div_right _ _ G.nonempty,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  · apply Fin.ext
    simp [Fin.modNat,Nat.mod_eq_of_lt j.isLt]

lemma bits_get (G : Graph) (w : ℕ) (hw : w<(graphBits G).length) :
    ((graphBits G)[w]?).getD false=
      if h : w<(nameBits G.vertices).length then ((nameBits G.vertices)[w]?).getD false
      else G.adj
        (⟨w-(nameBits G.vertices).length,by
          apply Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h)
          simpa only [graphBits,List.length_append,matrix_eq,List.length_ofFn] using hw⟩ : Fin (G.vertices*G.vertices)).divNat
        (⟨w-(nameBits G.vertices).length,by
          apply Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h)
          simpa only [graphBits,List.length_append,matrix_eq,List.length_ofFn] using hw⟩ : Fin (G.vertices*G.vertices)).modNat := by
  simp only [graphBits,matrix_eq]
  split_ifs with h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (Nat.le_of_not_gt h),List.getElem?_ofFn]
    have hb : w-(nameBits G.vertices).length<G.vertices*G.vertices := by
      apply Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt h)
      simpa only [graphBits,List.length_append,matrix_eq,List.length_ofFn] using hw
    simp only [dite_eq_left hb,Option.getD_some]

def lengthExpr (n : Expr) : Expr := .add (Expr.framedLen n) (.mul n n)
def bitExpr (n adj : Expr) : Expr :=
  Expr.cond (Expr.lt (.arg 0) (Expr.framedLen n)) (Expr.framedBit n (.arg 0))
    (adj.subst (fun _ => .sub (.arg 0) (Expr.framedLen n)))

lemma printer_spec (n adj : Expr) (s : List Bool) (G : Graph)
    (hn : ∀ a, n.eval s a=G.vertices)
    (ha : ∀ i : Fin (G.vertices*G.vertices),
      decide (adj.eval s (fun _ => i.val)≠0)=G.adj i.divNat i.modNat) :
    table (lengthExpr n) (bitExpr n adj) s=graphBits G := by
  have hlen : (lengthExpr n).eval s (fun _ => 0)=(graphBits G).length := by
    simp only [lengthExpr,Expr.eval,Expr.framedLen_eval,hn,graphBits,List.length_append,
      matrix_eq,List.length_ofFn,nameBits,frame_length,Nat.size_eq_bits_len]
  apply List.ext_getElem
  · simpa only [table,List.length_ofFn] using hlen
  · intro w hw hg
    simp only [table,List.getElem_ofFn]
    have hget : ((graphBits G)[w]?).getD false=(graphBits G)[w] := by
      rw [List.getElem?_eq_getElem hg]; rfl
    rw [← hget]
    rw [bits_get G w hg]
    have hheader : (nameBits G.vertices).length=2*G.vertices.size+1 := by
      simp [nameBits,frame_length,Nat.size_eq_bits_len]
    simp only [bitExpr,Expr.cond_eval,Expr.lt_eval,Expr.eval,Expr.framedLen_eval,hn,
      Expr.subst_eval,Expr.framedBit_eval]
    by_cases h : w<2*G.vertices.size+1
    · simp only [hheader,h,ite_true,dite_eq_left]
      rw [ite_eq_left (show (1:ℕ)≠0 by decide)]
      simpa only [nameBits,BinaryNames.frame_eq,Nat.one_ne_zero,ite_true] using (frame_bits_get G.vertices w).symm
    · simp only [hheader,h,ite_false,ne_eq,not_true_eq_false]
      have hb : w-(2*G.vertices.size+1)<G.vertices*G.vertices := by
        have hg' := hg
        simp only [graphBits,List.length_append,matrix_eq,List.length_ofFn,hheader] at hg'
        omega
      exact ha ⟨w-(2*G.vertices.size+1),hb⟩

noncomputable def encodedComputer {α : Type} (ea : α → List Bool) (f : α → Graph)
    (n adj : Expr) (hn : ∀ x a, n.eval (ea x) a=(f x).vertices)
    (ha : ∀ x (i : Fin ((f x).vertices*(f x).vertices)),
      decide (adj.eval (ea x) (fun _ => i.val)≠0)=(f x).adj i.divNat i.modNat) :
    Turing.TM2ComputableInPolyTime ea graphBits f where
  tm := (tableComputer (lengthExpr n) (bitExpr n adj)).tm
  inputAlphabet := (tableComputer (lengthExpr n) (bitExpr n adj)).inputAlphabet
  outputAlphabet := (tableComputer (lengthExpr n) (bitExpr n adj)).outputAlphabet
  time := (tableComputer (lengthExpr n) (bitExpr n adj)).time
  outputsFun x := by
    simpa only [id_eq,printer_spec n adj (ea x) (f x) (hn x) (ha x)] using
      (tableComputer (lengthExpr n) (bitExpr n adj)).outputsFun (ea x)

lemma encodedComputer_finiteAlphabet {α : Type} (ea : α → List Bool) (f : α → Graph)
    (n adj : Expr) (hn) (ha) :
    MachineFiniteAlphabet.FiniteAlphabet (encodedComputer ea f n adj hn ha).tm :=
  tableComputer_finiteAlphabet _ _

end
end LargeIndependentSets.GraphPrinter

end OAI
