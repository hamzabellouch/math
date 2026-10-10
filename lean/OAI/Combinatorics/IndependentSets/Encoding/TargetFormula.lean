import Mathlib
import OAI.Combinatorics.IndependentSets.Model
import OAI.Combinatorics.IndependentSets.Encoding.Target

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators
namespace Normalization

abbrev TargetFormula := IndependentSetsGames.Foundations.Target.Formula
abbrev TargetClause := IndependentSetsGames.Foundations.Target.Clause
abbrev TargetLiteral := IndependentSetsGames.Foundations.Target.Literal

def names (F : Formula) : List ℕ := F.clauses.flatten.map Literal.name

def nameIndex (F : Formula) (v : ℕ) : Fin ((names F).length + 1) :=
  ⟨(names F).idxOf v, Nat.lt_succ_of_le List.idxOf_le_length⟩

def literal (F : Formula) (l : Literal) : TargetLiteral ((names F).length + 1) :=
  ⟨nameIndex F l.name, l.positive⟩

def pad (C : List Literal) (i : Fin 3) : Literal :=
  C[i.val]?.getD (C.headD ⟨0,true⟩)

def clause (F : Formula) (C : List Literal) : TargetClause ((names F).length + 1) :=
  Vector.ofFn (fun i => literal F (pad C i))

lemma literal_eval_true (F : Formula) (l : Literal) (a : Fin ((names F).length+1) → Bool) :
    (literal F l).eval a = true ↔ a (nameIndex F l.name) = l.positive := by
  simp only [literal, IndependentSetsGames.Foundations.Target.Literal.eval]
  have H : ∀ p x : Bool, (if p then x else !x) = true ↔ x = p := by
    intro p x; cases p <;> cases x <;> decide
  exact H _ _

lemma clause_eval_true (F : Formula) (C : List Literal) (hne : C ≠ []) (hw : C.length ≤ 3)
    (a : Fin ((names F).length+1) → Bool) :
    (clause F C).eval a = true ↔ ∃ l ∈ C, a (nameIndex F l.name) = l.positive := by
  cases C with
  | nil => exact False.elim (hne rfl)
  | cons x tail =>
    cases tail with
    | nil => simp [clause, pad, IndependentSetsGames.Foundations.Target.Clause.eval, literal_eval_true]
    | cons y tail =>
      cases tail with
      | nil => simp [clause, pad, IndependentSetsGames.Foundations.Target.Clause.eval, literal_eval_true, or_comm]
      | cons z tail =>
        have ht : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hw
          omega
        subst tail
        simp [clause, pad, IndependentSetsGames.Foundations.Target.Clause.eval, literal_eval_true, or_assoc]

lemma name_mem (F : Formula) (C : List Literal) (hC : C ∈ F.clauses) (l : Literal) (hl : l ∈ C) :
    l.name ∈ names F := by
  exact List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨C,hC,hl⟩,rfl⟩

lemma lookup_variable (F : Formula) {v : ℕ} (hv : v ∈ names F) :
    (names F)[(nameIndex F v).val]?.getD 0 = v := by
  simp only [nameIndex]
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hv), List.getElem_idxOf]
  rfl

def contradiction : TargetFormula where
  «variables» := 1
  clauses := [Vector.replicate 3 ⟨0,true⟩, Vector.replicate 3 ⟨0,false⟩]

lemma contradiction_unsat : ¬contradiction.Satisfiable := by
  unfold contradiction IndependentSetsGames.Foundations.Target.Formula.Satisfiable
  rintro ⟨a,ha⟩
  have hp := ha (Vector.replicate 3 ⟨0,true⟩) (by simp)
  have hn := ha (Vector.replicate 3 ⟨0,false⟩) (by simp)
  simp only [IndependentSetsGames.Foundations.Target.Clause.eval, Vector.getElem_replicate,
    IndependentSetsGames.Foundations.Target.Literal.eval, Bool.or_self] at hp hn
  cases h : a 0 <;> simp [h] at hp hn

def normalize (F : Formula) : TargetFormula :=
  if [] ∈ F.clauses then contradiction
  else ⟨(names F).length+1,F.clauses.map (clause F)⟩

lemma normalize_satisfiable_iff (F : Formula) : (normalize F).Satisfiable ↔ F.Satisfiable := by
  by_cases hempty : [] ∈ F.clauses
  · rw [normalize,ite_eq_left hempty]
    constructor
    · intro h; exact False.elim (contradiction_unsat h)
    · rintro ⟨a,ha⟩
      obtain ⟨l,hl,_⟩ := ha [] hempty
      simp at hl
  · rw [normalize,ite_eq_right hempty]
    constructor
    · rintro ⟨a,ha⟩
      refine ⟨fun v => a (nameIndex F v),?_⟩
      intro C hC
      exact (clause_eval_true F C (fun h => hempty (h ▸ hC)) (F.width C hC) a).mp
        (ha _ (List.mem_map.mpr ⟨C,hC,rfl⟩))
    · rintro ⟨a,ha⟩
      refine ⟨fun i => a ((names F)[i.val]?.getD 0),?_⟩
      intro C hC
      obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hC
      apply (clause_eval_true F D (fun h => hempty (h ▸ hD)) (F.width D hD) _).mpr
      obtain ⟨l,hl,hs⟩ := ha D hD
      refine ⟨l,hl,?_⟩
      rw [lookup_variable F (name_mem F D hD l hl)]
      exact hs

end Normalization
end LargeIndependentSets

end OAI
