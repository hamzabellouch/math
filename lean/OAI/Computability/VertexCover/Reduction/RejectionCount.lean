import Mathlib
import OAI.Computability.VertexCover.Reduction.CompatibleSingleton

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.ClauseProjection
open UniqueGames.Foundations.Target

abbrev Pattern := {s : Fin 3 → Bool // ∃ k, s k = true}

instance : Fintype Pattern := inferInstanceAs (Fintype {s : Fin 3 → Bool // ∃ k, s k = true})

theorem pattern_card : Fintype.card Pattern = 7 := by decide

noncomputable def patternEquiv : Pattern ≃ Fin 7 :=
  (Fintype.equivFin Pattern).trans (finCongr pattern_card)

def flipSign (positive b : Bool) : Bool := if positive then b else !b

@[simp] theorem flipSign_flipSign (p b : Bool) : flipSign p (flipSign p b) = b := by
  cases p <;> cases b <;> rfl

def literalAt (F : Formula) (i : Fin F.clauses.length) (k : Fin 3) : Literal F.«variables» :=
  (F.clauses.get i)[k]

noncomputable def game (F : Formula) (hne : F.clauses ≠ []) : LabelCover where
  u := F.clauses.length
  v := F.«variables»
  qU := 7
  qV := 2
  M := F.clauses.length * 3
  qU_pos := by decide
  qV_pos := by decide
  M_pos := Nat.mul_pos (List.length_pos_iff.mpr hne) (by decide)
  left e := (finProdFinEquiv.symm e).1
  right e := (literalAt F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).variableIndex
  projection e label := finTwoEquiv.symm
    (flipSign (literalAt F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).positive
      ((patternEquiv.symm label).val (finProdFinEquiv.symm e).2))

def clauseValue (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) (k : Fin 3) : Bool :=
  (literalAt F i k).eval a

theorem clause_eval_iff (F : Formula) (a : Fin F.«variables» → Bool)
    (i : Fin F.clauses.length) :
    (F.clauses.get i).eval a = true ↔ ∃ k : Fin 3, clauseValue F a i k = true := by
  simp only [Clause.eval, Bool.or_eq_true]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hk)
    · exact Or.inr hk

noncomputable def honestLabeling (F : Formula) (hne : F.clauses ≠ [])
    (a : Fin F.«variables» → Bool)
    (ha : ∀ clause ∈ F.clauses, clause.eval a = true) : (game F hne).Labeling :=
  (fun i => patternEquiv ⟨clauseValue F a i,
      (clause_eval_iff F a i).mp (ha _ (List.get_mem _ i))⟩,
   fun v => finTwoEquiv.symm (a v))

theorem honest_satisfies (F : Formula) (hne : F.clauses ≠ [])
    (a : Fin F.«variables» → Bool)
    (ha : ∀ clause ∈ F.clauses, clause.eval a = true) :
    ∀ e, (game F hne).Satisfies (honestLabeling F hne a ha) e := by
  intro e
  simp only [LabelCover.Satisfies, game, honestLabeling, Equiv.symm_apply_apply]
  congr 1
  change flipSign _ (flipSign _ _) = _
  exact flipSign_flipSign _ _

theorem perfect_complete (F : Formula) (hne : F.clauses ≠ []) (hF : F.Satisfiable) :
    ∃ A : (game F hne).Labeling, ∀ e, (game F hne).Satisfies A e := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨honestLabeling F hne a ha, honest_satisfies F hne a ha⟩

noncomputable def assignmentOf (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) (v : Fin F.«variables») : Bool := finTwoEquiv (A.2 v)

theorem satisfies_iff (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) (i : Fin F.clauses.length) (k : Fin 3) :
    (game F hne).Satisfies A (finProdFinEquiv (i,k)) ↔
      (patternEquiv.symm (A.1 i)).val k = clauseValue F (assignmentOf F hne A) i k := by
  simp only [LabelCover.Satisfies, game, Equiv.symm_apply_apply]
  change finTwoEquiv.symm (flipSign (literalAt F i k).positive
    ((patternEquiv.symm (A.1 i)).val k)) = A.2 (literalAt F i k).variableIndex ↔
    (patternEquiv.symm (A.1 i)).val k =
      flipSign (literalAt F i k).positive (assignmentOf F hne A (literalAt F i k).variableIndex)
  constructor
  · intro h
    have hh := congrArg finTwoEquiv h
    simp only [Equiv.apply_symm_apply] at hh
    have hf := congrArg (flipSign (literalAt F i k).positive) hh
    simpa only [flipSign_flipSign, assignmentOf] using hf
  · intro h
    rw [h, flipSign_flipSign]
    exact finTwoEquiv.symm_apply_apply _

def unsatisfiedClauses (F : Formula) (a : Fin F.«variables» → Bool) :
    Finset (Fin F.clauses.length) :=
  Finset.univ.filter (fun i => (F.clauses.get i).eval a = false)

theorem reject_of_unsatisfied (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) (i : Fin F.clauses.length)
    (hi : i ∈ unsatisfiedClauses F (assignmentOf F hne A)) :
    ∃ k : Fin 3, ¬(game F hne).Satisfies A (finProdFinEquiv (i,k)) := by
  obtain ⟨k, hk⟩ := (patternEquiv.symm (A.1 i)).property
  refine ⟨k, ?_⟩
  intro hsat
  have hclause := (clause_eval_iff F (assignmentOf F hne A) i).mpr
    ⟨k, (satisfies_iff F hne A i k).mp hsat ▸ hk⟩
  have hfalse := (Finset.mem_filter.mp hi).2
  rw [hfalse] at hclause
  cases hclause

theorem rejection_count (F : Formula) (hne : F.clauses ≠ [])
    (A : (game F hne).Labeling) :
    (unsatisfiedClauses F (assignmentOf F hne A)).card ≤
      (Finset.univ.filter (fun e => ¬(game F hne).Satisfies A e)).card := by
  classical
  let bad := unsatisfiedClauses F (assignmentOf F hne A)
  let witness : {i // i ∈ bad} → Fin 3 := fun i =>
    (reject_of_unsatisfied F hne A i.val i.property).choose
  let occurrence : {i // i ∈ bad} → Fin (game F hne).M :=
    fun i => finProdFinEquiv (i.val, witness i)
  have hmap : ∀ i, occurrence i ∈ Finset.univ.filter (fun e => ¬(game F hne).Satisfies A e) := by
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (reject_of_unsatisfied F hne A i.val i.property).choose_spec⟩
  have hinj : Function.Injective occurrence := by
    intro i j hij
    exact Subtype.ext (congrArg Prod.fst (finProdFinEquiv.injective hij))
  have hcard := Fintype.card_le_of_injective
    (fun i => (⟨occurrence i, hmap i⟩ :
      {e // e ∈ Finset.univ.filter (fun e => ¬(game F hne).Satisfies A e)}))
    (fun i j hij => hinj (congrArg Subtype.val hij))
  simpa only [Fintype.card_coe] using hcard

end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
