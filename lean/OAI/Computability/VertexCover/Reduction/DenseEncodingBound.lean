import Mathlib
import OAI.Computability.VertexCover.Encoding.BinaryFormula
import OAI.Computability.VertexCover.PCP.NameCompaction
import OAI.Computability.VertexCover.Reduction.GridBudget

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
namespace UniqueGames.BinaryFormula
open UniqueGames.Foundations

def activeNames (F : Formula) : List Nat :=
  (sourceNames F).eraseDups

theorem literal_mem_active (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) (i : Fin 3) : «c»[i].name ∈ activeNames F := by
  simp only [activeNames, List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨«c», hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def decodeName (F : Formula) (v : Fin (activeNames F).length) : Nat :=
  (activeNames F)[v.val]

def compactLiteral (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : Target.Literal (activeNames F).length :=
  ⟨compactIndex F l.name hl, l.positive⟩

def compactClause (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) : Target.Clause (activeNames F).length :=
  #v[compactLiteral F «c»[0] (literal_mem_active F «c» hc 0),
    compactLiteral F «c»[1] (literal_mem_active F «c» hc 1),
    compactLiteral F «c»[2] (literal_mem_active F «c» hc 2)]

def compactClauses (F : Formula) : List (Target.Clause (activeNames F).length) :=
  F.clauses.attach.map (fun «c» => compactClause F «c».val «c».property)

def dense (F : Formula) : Target.Formula where
  «variables» := (activeNames F).length
  clauses := compactClauses F

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (activeNames F).length → Bool := fun v => A (decodeName F v)

def extendAssignment (F : Formula) (B : Fin (activeNames F).length → Bool)
    (v : Nat) : Bool :=
  if hv : v ∈ activeNames F then B (compactIndex F v hv) else false

@[simp] theorem decode_compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : decodeName F (compactIndex F v hv) = v := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

theorem compactIndex_injective (F : Formula) (u v : Nat)
    (hu : u ∈ activeNames F) (hv : v ∈ activeNames F)
    (h : compactIndex F u hu = compactIndex F v hv) : u = v := by
  have decoded := congrArg (decodeName F) h
  simpa only [decode_compactIndex] using decoded

@[simp] theorem compactLiteral_positive (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : (compactLiteral F l hl).positive = l.positive := rfl

@[simp] theorem eval_compact_restrict (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) (A : Nat → Bool) :
    (compactClause F «c» hc).eval (restrictAssignment F A) = «c».eval A := by
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, restrictAssignment, decode_compactIndex]

@[simp] theorem eval_compact_extend (F : Formula) («c» : Clause)
    (hc : «c» ∈ F.clauses) (B : Fin (activeNames F).length → Bool) :
    (compactClause F «c» hc).eval B = «c».eval (extendAssignment F B) := by
  have h₀ : «c»[0].name ∈ activeNames F := literal_mem_active F «c» hc 0
  have h₁ : «c»[1].name ∈ activeNames F := literal_mem_active F «c» hc 1
  have h₂ : «c»[2].name ∈ activeNames F := literal_mem_active F «c» hc 2
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, extendAssignment, h₀, h₁, h₂] ; rfl

def evaluationList (F : Formula) (A : Nat → Bool) : List Bool :=
  F.clauses.map (fun «c» => «c».eval A)

theorem evaluationList_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.evaluationList (dense F) (restrictAssignment F A) =
      evaluationList F A := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  simpa only [Function.comp_def, eval_compact_restrict] using
    PCP.NameCompaction.map_attach_val F.clauses (fun «c» => «c».eval A)

theorem evaluationList_extend (F : Formula) (B : Fin (dense F).«variables» → Bool) :
    PCP.NameCompaction.evaluationList (dense F) B =
      evaluationList F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  change F.clauses.attach.map (fun «c» => (compactClause F «c».val «c».property).eval B) = _
  calc
    _ = F.clauses.attach.map (fun «c» => «c».val.eval (extendAssignment F B)) := by
      apply List.map_congr_left
      intro «c» _
      exact eval_compact_extend F «c».val «c».property B
    _ = _ := PCP.NameCompaction.map_attach_val F.clauses
      (fun «c» => «c».eval (extendAssignment F B))

def failedCount (F : Formula) (A : Nat → Bool) : Nat :=
  (evaluationList F A).count false

theorem failedCount_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.failedCount (dense F) (restrictAssignment F A) = failedCount F A := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_restrict]

theorem failedCount_extend (F : Formula) (B : Fin (dense F).«variables» → Bool) :
    PCP.NameCompaction.failedCount (dense F) B = failedCount F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_extend]

theorem clauseNames_flat_length (cs : List Clause) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons «c» cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

@[simp] theorem dense_clause_count (F : Formula) :
    (dense F).clauses.length = F.clauses.length := by
  simp [dense, compactClauses]

theorem dense_variable_bound (F : Formula) :
    (dense F).«variables» ≤ 3 * F.clauses.length := by
  have h := PCP.NameCompaction.length_eraseDups_le (sourceNames F)
  simpa only [sourceNames, clauseNames_flat_length, dense, activeNames] using h

theorem dense_completeness (F : Formula) (hs : F.Satisfiable) :
    (dense F).Satisfiable := by
  rcases hs with ⟨A, hA⟩
  refine ⟨restrictAssignment F A, ?_⟩
  intro d hd
  change d ∈ F.clauses.attach.map (fun «c» => compactClause F «c».val «c».property) at hd
  rcases List.mem_map.mp hd with ⟨«c», _, rfl⟩
  exact (eval_compact_restrict F «c».val «c».property A).trans (hA «c».val «c».property)

theorem dense_reflects (F : Formula) (hs : (dense F).Satisfiable) : F.Satisfiable := by
  rcases hs with ⟨B, hB⟩
  refine ⟨extendAssignment F B, ?_⟩
  intro «c» hc
  have hm : compactClause F «c» hc ∈ (dense F).clauses := by
    change _ ∈ F.clauses.attach.map (fun d => compactClause F d.val d.property)
    exact List.mem_map.mpr ⟨⟨«c», hc⟩, by simp, rfl⟩
  rw [← eval_compact_extend F «c» hc B]
  exact hB _ hm

theorem dense_satisfiable_iff (F : Formula) :
    (dense F).Satisfiable ↔ F.Satisfiable :=
  ⟨dense_reflects F, dense_completeness F⟩

theorem dense_preserves_gap (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * failedCount F A)
    (B : Fin (dense F).«variables» → Bool) :
    a * (dense F).clauses.length ≤ b * PCP.NameCompaction.failedCount (dense F) B := by
  rw [dense_clause_count, failedCount_extend]
  exact gap (extendAssignment F B)

theorem dense_encoding_bound (F : Formula) :
    (Complexity.formulaBits (dense F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have enc := Complexity.formulaBits_length_le (dense F)
  rw [dense_clause_count] at enc
  have active := dense_variable_bound F
  have h₁ := Nat.add_le_add_right active (F.clauses.length + 2)
  have h₂ := Nat.mul_le_mul_left F.clauses.length
    (Nat.mul_le_mul_left 3 (Nat.add_le_add_right active 2))
  have total := Nat.add_le_add h₁ h₂
  have polynomial : 3 * F.clauses.length + (F.clauses.length + 2) +
      F.clauses.length * (3 * (3 * F.clauses.length + 2)) =
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
    ring
  rw [polynomial] at total
  omega

end UniqueGames.BinaryFormula


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
