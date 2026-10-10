import Mathlib
import OAI.Probability.BinarySweep.Mixing.BinaryContraction

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

def longRowCells : Fin (μ.rowLen 0-μ.rowLen 1) ↪ Cell μ where
  toFun j := ⟨(0,μ.rowLen 1+j.val),YoungDiagram.mem_iff_lt_rowLen.mpr (by
    have hj := j.isLt
    have hm := μ.rowLen_anti 0 1 (by omega)
    omega)⟩
  inj' i j := by
    intro he
    apply Fin.ext
    have hh := congrArg (fun x : Cell μ => x.val.2) he
    dsimp at hh
    omega

lemma longRowCells_fixed (c : C μ) (j : Fin (μ.rowLen 0-μ.rowLen 1)) :
    c.val (longRowCells μ j)=longRowCells μ j := by
  have hc := c.property (longRowCells μ j)
  have hm := YoungDiagram.mem_iff_lt_rowLen.mp (c.val (longRowCells μ j)).property
  have hr : row (c.val (longRowCells μ j))=0 := by
    by_contra hne
    have ha := μ.rowLen_anti 1 (row (c.val (longRowCells μ j))) (by omega)
    change col (c.val (longRowCells μ j)) < μ.rowLen (row (c.val (longRowCells μ j))) at hm
    change col (c.val (longRowCells μ j))=μ.rowLen 1+j.val at hc
    omega
  apply Subtype.ext
  exact Prod.ext hr hc

theorem long_row_dimension (hrow : 0<μ.rowLen 1) :
    μ.rowLen 0-μ.rowLen 1 ≤ Module.finrank ℂ (SpechtSpace μ) := by
  let a : Cell μ := ⟨(1,0),YoungDiagram.mem_iff_lt_rowLen.mpr hrow⟩
  have hh := singleton_column_dimension μ a (by change (1:ℕ)≠0; omega)
    (longRowCells μ) (fun _ => rfl) (longRowCells_fixed μ)
  simpa only [Fintype.card_fin] using hh

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

def flatTail (μ : YoungDiagram) : ℕ := μ.card-max (μ.colLen 0) (μ.rowLen 0)
def longOriented (μ : YoungDiagram) : YoungDiagram :=
  if μ.colLen 0 ≤ μ.rowLen 0 then μ else μ.transpose

lemma transpose_card (μ : YoungDiagram) : μ.transpose.card=μ.card := by
  simp

lemma rowLens_sum (μ : YoungDiagram) : μ.rowLens.sum=μ.card := by
  have h := card_cellsOfRowLens μ.rowLens
  change (YoungDiagram.ofRowLens μ.rowLens μ.rowLens_sorted).card=_ at h
  rw [YoungDiagram.ofRowLens_to_rowLens_eq_self] at h
  exact h.symm

lemma rowLens_head (μ : YoungDiagram) : μ.rowLens.headD 0=μ.rowLen 0 := by
  by_cases h : μ.colLen 0=0
  · have hr : μ.rowLen 0=0 := by
      by_contra hn
      have hm : (0,0)∈μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
      omega
    simp [YoungDiagram.rowLens,h,hr]
  · obtain ⟨a,ha⟩ : ∃a, μ.colLen 0=a+1 := ⟨μ.colLen 0-1,by omega⟩
    simp [YoungDiagram.rowLens,ha,List.range_succ_eq_map]

lemma rowLens_tail_sum (μ : YoungDiagram) : μ.rowLens.tail.sum=μ.card-μ.rowLen 0 := by
  have hh : μ.rowLens.headD 0+μ.rowLens.tail.sum=μ.rowLens.sum := by
    cases μ.rowLens <;> simp
  rw [rowLens_head,rowLens_sum] at hh
  omega

lemma longOriented_card (μ : YoungDiagram) : (longOriented μ).card=μ.card := by
  unfold longOriented
  split <;> simp_all

lemma longOriented_row (μ : YoungDiagram) :
    (longOriented μ).rowLen 0=max (μ.colLen 0) (μ.rowLen 0) := by
  unfold longOriented
  split <;> simp_all [YoungDiagram.rowLen_transpose,Nat.le_of_lt]

lemma positive_list_tail_injective {a b : List ℕ}
    (ha : ∀x∈a,0<x) (hb : ∀x∈b,0<x)
    (hs : a.sum=b.sum) (ht : a.tail=b.tail) : a=b := by
  cases a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x b =>
      have hh := hb x (by simp)
      simp only [List.sum_nil,List.sum_cons] at hs
      omega
  | cons x a =>
    cases b with
    | nil =>
      have hh := ha x (by simp)
      simp only [List.sum_nil,List.sum_cons] at hs
      omega
    | cons y b =>
      simp only [List.tail_cons] at ht
      subst b
      simp only [List.sum_cons] at hs
      have he : x=y := by omega
      subst y
      rfl

def tailCode {n k : ℕ} (p : {p : n.Partition // flatTail (diagram p)=k}) :
    Bool × Composition k :=
  (decide ((diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0),
    ⟨(longOriented (diagram p.val)).rowLens.tail,
      fun {i} hi => YoungDiagram.pos_of_mem_rowLens _ _ (List.mem_of_mem_tail hi),by
        rw [rowLens_tail_sum,longOriented_card,longOriented_row]
        exact p.property⟩)

lemma tailCode_injective {n k : ℕ} : Function.Injective (tailCode (n:=n) (k:=k)) := by
  intro p q he
  have ho : longOriented (diagram p.val)=longOriented (diagram q.val) := by
    apply YoungDiagram.equivListRowLens.injective
    apply Subtype.ext
    apply positive_list_tail_injective (YoungDiagram.pos_of_mem_rowLens _) (YoungDiagram.pos_of_mem_rowLens _)
    · rw [rowLens_sum,rowLens_sum,longOriented_card,longOriented_card,diagram_card,diagram_card]
    · exact congrArg (fun c : Bool × Composition k => c.2.blocks) he
  have hb := congrArg Prod.fst he
  change decide ((diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0)=
    decide ((diagram q.val).colLen 0 ≤ (diagram q.val).rowLen 0) at hb
  have hi := of_decide_eq_true (show decide (((diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0) ↔
    ((diagram q.val).colLen 0 ≤ (diagram q.val).rowLen 0))=true from by simp [hb])
  apply Subtype.ext
  apply diagram_injective
  unfold longOriented at ho
  by_cases hp : (diagram p.val).colLen 0 ≤ (diagram p.val).rowLen 0
  · simpa [hp,hi.mp hp] using ho
  · have hq : ¬(diagram q.val).colLen 0 ≤ (diagram q.val).rowLen 0 := fun hh => hp (hi.mpr hh)
    have hh := congrArg YoungDiagram.transpose ho
    simpa [hp,hq] using hh

theorem flatTail_card (n k : ℕ) :
    Fintype.card {p : n.Partition // flatTail (diagram p)=k} ≤ 2*2^k := by
  have h := Fintype.card_le_of_injective (tailCode (n:=n) (k:=k)) tailCode_injective
  simp only [Fintype.card_prod,Fintype.card_bool,composition_card] at h
  exact h.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (by omega)))

end BinaryCoordinateSweeps.Young

end

end OAI
