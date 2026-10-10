import OAI.Computability.MatchingCount.RawSearchCompiler

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def augment (n : ℕ) (c : Matrix ℕ) (a z : ℕ) (b : Matrix ℤ) : Matrix ℤ :=
  match nth (search n c b a n) z with
  | none => b
  | some p => matrix n (fun i j => get b i j+pathFlow p i j)
def flow (n : ℕ) (c : Matrix ℕ) (a z k : ℕ) : Matrix ℤ :=
  (augment n c a z)^[k] (matrix n (fun _ _ => 0))
def sourceCapacity (n : ℕ) (c : Matrix ℕ) (a : ℕ) : ℕ := (tab n (get c a)).sum
def mincut (n : ℕ) (c : Matrix ℕ) (a z : ℕ) : Cut :=
  reached n (search n c (flow n c a z (sourceCapacity n c a)) a n)
def cutCapacity (n : ℕ) (c : Matrix ℕ) (S : Cut) : ℕ :=
  (tab n (fun i => (tab n (fun j => if mem S i && !mem S j then get c i j else 0)).sum)).sum

def pairs (n : ℕ) : List (ℕ×ℕ) := (List.range n).flatMap (fun i => (List.range n).map (i,·))
def pairCuts (n : ℕ) (c : Matrix ℕ) (U : Cut) : List Cut :=
  ((pairs n).filter (fun az => mem U az.1 && mem U az.2 && decide (az.1≠az.2))).map
    (fun az => mincut n c az.1 az.2)
def terminalCut (n : ℕ) (c : Matrix ℕ) (U : Cut) : Cut :=
  ((pairCuts n c U).argmin (cutCapacity n c)).getD (empty n)

lemma augment_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : UnitFlow.Matrix (Fin n)) :
    augment n (matrixRep c) a.val z.val (matrixRep b)=matrixRep (UnitMincut.augment c a z b) := by
  unfold augment
  rw [search_rep,nth_pathRep]
  unfold UnitMincut.augment
  cases h : ResidualSearch.search (UnitMincut.residual c b) a n z with
  | none => rfl
  | some p =>
    simp only [Option.map_some]
    apply matrix_eq_rep
    intro i j
    simp only [get_rep,pathFlow_rep]
lemma flow_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) (k : ℕ) :
    flow n (matrixRep c) a.val z.val k=matrixRep (UnitMincut.iterate c a z k) := by
  induction k with
  | zero => exact matrix_eq_rep _ _ (fun _ _ => rfl)
  | succ k ih =>
    simp only [flow,Function.iterate_succ_apply'] at *
    rw [ih,augment_rep]
    rfl
lemma sourceCapacity_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a : Fin n) :
    sourceCapacity n (matrixRep c) a.val=UnitMincut.sourceCapacity c a := by
  simp [sourceCapacity,sum_tab,UnitMincut.sourceCapacity]
lemma mincut_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (a z : Fin n) :
    mincut n (matrixRep c) a.val z.val=cutRep (UnitMincut.mincut c a z) := by
  simp only [mincut,sourceCapacity_rep,flow_rep,search_rep,reached_rep,UnitMincut.mincut]
lemma cutCapacity_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (S : Finset (Fin n)) :
    cutCapacity n (matrixRep c) (cutRep S)=UnitFlow.cutCapacity c S := by
  simp only [cutCapacity,sum_tab,mem_rep,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    decide_eq_false_iff_not,get_rep]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter]
  unfold UnitFlow.cutCapacity
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Sᶜ=univ.filter (fun j => j∉S) by ext; simp]
  simp only [Finset.sum_filter]

lemma pairs_rep (n : ℕ) : pairs n=(((List.finRange n).product (List.finRange n)).map
    (fun az => (az.1.val,az.2.val))) := by
  simp only [pairs,List.product,range_eq_fin,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

lemma pairCuts_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    pairCuts n (matrixRep c) (cutRep U)=(TerminalMincut.pairCuts c U).map cutRep := by
  unfold pairCuts TerminalMincut.pairCuts
  rw [pairs_rep,List.filter_map,List.map_map,List.map_map]
  have hp : (fun az : Fin n×Fin n => mem (cutRep U) az.1.val && mem (cutRep U) az.2.val &&
      decide (az.1.val≠az.2.val))=(fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2)) := by
    funext az
    simp [Fin.ext_iff,Bool.and_assoc]
  simp only [Function.comp_def]
  rw [hp]
  apply List.map_congr_left
  intro az haz
  exact mincut_rep c az.1 az.2

lemma argmin_map_eq {α β : Type} (f : α → β) (l : List α) (g : β → ℕ) :
    (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.map_append,List.map_singleton,List.argmin_concat,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

lemma terminalCut_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) :
    terminalCut n (matrixRep c) (cutRep U)=cutRep (TerminalMincut.terminalCut c U) := by
  unfold terminalCut TerminalMincut.terminalCut
  rw [pairCuts_rep,argmin_map_eq]
  have hg : cutCapacity n (matrixRep c) ∘ cutRep=UnitFlow.cutCapacity c := by
    funext S; exact cutCapacity_rep c S
  rw [hg,empty_rep]
  cases h : (TerminalMincut.pairCuts c U).argmin (UnitFlow.cutCapacity c) <;> rfl

end BinaryMatching.Raw
end

end OAI
