import Mathlib
import OAI.Computability.MinUncut.Machines.MachineBinaryFormula

namespace OAI

section
namespace MinUncutGames.BinaryOccurrenceRename

open BinaryFormula MinUncutGames.Foundations

theorem literal_mem_names (F : Formula) (c : Clause) (hc : c ∈ F.clauses)
    (i : Fin 3) : (c)[i].name ∈ sourceNames F := by
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def nameIndex (F : Formula) (name : Nat) (mem : name ∈ sourceNames F) :
    Fin (sourceNames F).length :=
  ⟨(sourceNames F).idxOf name, List.idxOf_lt_length_of_mem mem⟩

def literal (F : Formula) (l : Literal) (mem : l.name ∈ sourceNames F) :
    Target.Literal (sourceNames F).length :=
  ⟨nameIndex F l.name mem, l.positive⟩

def clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Target.Clause (sourceNames F).length :=
  #v[literal F (c)[0] (literal_mem_names F c mem 0),
    literal F (c)[1] (literal_mem_names F c mem 1),
    literal F (c)[2] (literal_mem_names F c mem 2)]

def renamed (F : Formula) : Target.Formula where
  «variables» := (sourceNames F).length
  clauses := F.clauses.attach.map (fun c => clause F c.val c.property)

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (sourceNames F).length → Bool :=
  fun i => A (sourceNames F)[i.val]

def extendAssignment (F : Formula) (A : Fin (sourceNames F).length → Bool) : Nat → Bool :=
  fun name => if mem : name ∈ sourceNames F then A (nameIndex F name mem) else false

@[simp] theorem nameIndex_reads_name (F : Formula) (name : Nat)
    (mem : name ∈ sourceNames F) : (sourceNames F)[(nameIndex F name mem).val] = name :=
  List.getElem_idxOf _

@[simp] theorem clause_eval_restrict (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Nat → Bool) : (clause F c mem).eval (restrictAssignment F A) = c.eval A := by
  simp [clause, literal, Target.Clause.eval, Target.Literal.eval,
    BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, restrictAssignment]

@[simp] theorem clause_eval_extend (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Fin (sourceNames F).length → Bool) :
    (clause F c mem).eval A = c.eval (extendAssignment F A) := by
  have evalLiteral (l : Literal) (hl : l.name ∈ sourceNames F) :
      (literal F l hl).eval A = l.eval (extendAssignment F A) := by
    simp only [literal, Target.Literal.eval, BinaryFormula.Literal.eval,
      extendAssignment, dite_eq_left hl]
    rfl
  simp [clause, Target.Clause.eval, BinaryFormula.Clause.eval, evalLiteral]

@[simp] theorem renamed_clause_count (F : Formula) :
    (renamed F).clauses.length = F.clauses.length := by simp [renamed]

@[simp] theorem renamed_variable_count (F : Formula) :
    (renamed F).«variables» = 3 * F.clauses.length := by
  exact clauseNames_flat_length F.clauses

theorem renamed_satisfiable_iff (F : Formula) : (renamed F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨extendAssignment F A, ?_⟩
    intro c mem
    have hc : clause F c mem ∈ (renamed F).clauses :=
      List.mem_map.mpr ⟨⟨c, mem⟩, by simp, rfl⟩
    exact (clause_eval_extend F c mem A).symm.trans (hA _ hc)
  · rintro ⟨A, hA⟩
    refine ⟨restrictAssignment F A, ?_⟩
    intro c mem
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp mem
    exact (clause_eval_restrict F original.val original.property A).trans
      (hA original.val original.property)

theorem nat_bits_injective : Function.Injective Nat.bits := by
  intro a b same
  have decoded := congrArg BinaryEncoding.bitsValue same
  simpa only [BinaryEncoding.bitsValue_bits] using decoded

theorem idxOf_binary_payloads (names : List Nat) (name : Nat) :
    (names.map Nat.bits).idxOf name.bits = names.idxOf name := by
  induction names with
  | nil => rfl
  | cons first names ih =>
      by_cases same : first = name
      · subst first
        simp
      · have different : first.bits ≠ name.bits := fun h => same (nat_bits_injective h)
        simp only [List.map_cons, List.idxOf_cons, beq_false_of_ne same,
          beq_false_of_ne different, ih]

theorem renamed_encoding_bound (F : Formula) :
    (Complexity.formulaBits (renamed F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have h := Complexity.formulaBits_length_le (renamed F)
  simp only [renamed_clause_count, renamed_variable_count] at h
  nlinarith

theorem renamed_encoding_bound_bits (F : Formula) :
    (Complexity.formulaBits (renamed F)).length ≤
      9 * (BinaryEncoding.formulaBits F).length * (BinaryEncoding.formulaBits F).length +
      10 * (BinaryEncoding.formulaBits F).length + 2 := by
  have h := renamed_encoding_bound F
  have hm : F.clauses.length ≤ (BinaryEncoding.formulaBits F).length :=
    (BinaryEncoding.clauses_length_lt_bits F.clauses).le
  have hsq := Nat.mul_self_le_mul_self hm
  nlinarith

end MinUncutGames.BinaryOccurrenceRename

end

end OAI
