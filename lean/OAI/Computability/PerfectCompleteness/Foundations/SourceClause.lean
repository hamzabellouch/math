import OAI.Computability.UniqueGames.Foundations.PinskerLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceClause

open UniqueGamesTheorem.Foundations.Target

abbrev Triple := Bool × Bool × Bool

def Triple.at (t : Triple) (i : Fin 3) : Bool :=
  match i.val with
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

def literalTruth (positive value : Bool) : Bool :=
  if positive then value else !value

def localEval (signs values : Triple) : Bool :=
  (literalTruth signs.1 values.1 || literalTruth signs.2.1 values.2.1) ||
    literalTruth signs.2.2 values.2.2

def allTriples : List Triple :=
  [(false, false, false), (false, false, true),
   (false, true, false), (false, true, true),
   (true, false, false), (true, false, true),
   (true, true, false), (true, true, true)]

def satisfyingTriples (signs : Triple) : List Triple :=
  allTriples.filter (localEval signs)

theorem mem_allTriples (t : Triple) : t ∈ allTriples := by
  rcases t with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

@[simp] theorem mem_satisfyingTriples (signs values : Triple) :
    values ∈ satisfyingTriples signs ↔ localEval signs values = true := by
  simp [satisfyingTriples, mem_allTriples]

theorem satisfyingTriples_nodup (signs : Triple) :
    (satisfyingTriples signs).Nodup := by
  rcases signs with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

@[simp] theorem satisfyingTriples_length (signs : Triple) :
    (satisfyingTriples signs).length = 7 := by
  rcases signs with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

private theorem coordinate_truth_table :
    ∀ s₀ s₁ s₂ : Bool, ∀ i : Fin 3, ∀ value : Bool,
      ∃ a b c : Bool,
        localEval (s₀, s₁, s₂) (a, b, c) = true ∧
        Triple.at (a, b, c) i = value := by
  decide

theorem coordinate_surjective (signs : Triple) (i : Fin 3) (value : Bool) :
    ∃ t ∈ satisfyingTriples signs, t.at i = value := by
  obtain ⟨a, b, c, hs, hv⟩ :=
    coordinate_truth_table signs.1 signs.2.1 signs.2.2 i value
  exact ⟨(a, b, c), (mem_satisfyingTriples signs _).mpr hs, hv⟩

private theorem pair_truth_table :
    ∀ s₀ s₁ s₂ : Bool, ∀ i j : Fin 3, i ≠ j → ∀ first second : Bool,
      ∃ a b c : Bool,
        localEval (s₀, s₁, s₂) (a, b, c) = true ∧
        Triple.at (a, b, c) i = first ∧ Triple.at (a, b, c) j = second := by
  decide

theorem pair_surjective (signs : Triple) (i j : Fin 3) (distinct : i ≠ j)
    (first second : Bool) :
    ∃ t ∈ satisfyingTriples signs, t.at i = first ∧ t.at j = second := by
  obtain ⟨a, b, c, hs, hv⟩ :=
    pair_truth_table signs.1 signs.2.1 signs.2.2 i j distinct first second
  exact ⟨(a, b, c), (mem_satisfyingTriples signs _).mpr hs, hv⟩

structure NormalizedClause («variables» : Nat) where
  clause : Clause «variables»
  distinct : ∀ i j : Fin 3,
    clause[i].variableIndex = clause[j].variableIndex → i = j

def NormalizedClause.variable {n : Nat} (c : NormalizedClause n) (i : Fin 3) : Fin n :=
  c.clause[i].variableIndex

def NormalizedClause.signs {n : Nat} (c : NormalizedClause n) : Triple :=
  (c.clause[0].positive, c.clause[1].positive, c.clause[2].positive)

def NormalizedClause.restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) : Triple :=
  (assignment (c.variable 0), assignment (c.variable 1), assignment (c.variable 2))

@[simp] theorem localEval_restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) :
    localEval c.signs (c.restrict assignment) = c.clause.eval assignment := by
  rfl

theorem variable_ne {n : Nat} (c : NormalizedClause n) {i j : Fin 3}
    (different : i ≠ j) : c.variable i ≠ c.variable j :=
  fun same => different (c.distinct i j same)

def NormalizedClause.extend {n : Nat} (c : NormalizedClause n) (t : Triple) :
    Fin n → Bool :=
  fun v => if v = c.variable 0 then t.1 else if v = c.variable 1 then t.2.1 else t.2.2

@[simp] theorem restrict_extend {n : Nat} (c : NormalizedClause n) (t : Triple) :
    c.restrict (c.extend t) = t := by
  have h10 := variable_ne c (by decide : (1 : Fin 3) ≠ 0)
  have h20 := variable_ne c (by decide : (2 : Fin 3) ≠ 0)
  have h21 := variable_ne c (by decide : (2 : Fin 3) ≠ 1)
  simp [NormalizedClause.restrict, NormalizedClause.extend, h10, h20, h21]

theorem satisfying_label_realized {n : Nat} (c : NormalizedClause n) (t : Triple)
    (valid : t ∈ satisfyingTriples c.signs) :
    ∃ assignment : Fin n → Bool,
      c.restrict assignment = t ∧ c.clause.eval assignment = true := by
  refine ⟨c.extend t, restrict_extend c t, ?_⟩
  rw [← localEval_restrict, restrict_extend]
  exact (mem_satisfyingTriples c.signs t).mp valid

abbrev Occurrence (clauseCount : Nat) := Fin clauseCount × Fin 3

def occurrenceVariable {n m : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrence m) : Fin n :=
  (clauses e.1).variable e.2

theorem occurrence_determined_by_endpoints {n m : Nat}
    (clauses : Fin m → NormalizedClause n) (e e' : Occurrence m)
    (sameClause : e.1 = e'.1)
    (sameVariable : occurrenceVariable clauses e = occurrenceVariable clauses e') :
    e = e' := by
  rcases e with ⟨c, i⟩
  rcases e' with ⟨c', j⟩
  dsimp only at sameClause
  subst c'
  have samePosition : i = j := (clauses c).distinct i j sameVariable
  subst j
  rfl

theorem projection_determined_by_endpoints {n m : Nat}
    (clauses : Fin m → NormalizedClause n) (e e' : Occurrence m)
    (sameClause : e.1 = e'.1)
    (sameVariable : occurrenceVariable clauses e = occurrenceVariable clauses e')
    (label : Triple) : label.at e.2 = label.at e'.2 := by
  rw [occurrence_determined_by_endpoints clauses e e' sameClause sameVariable]

def agreementCount {n : Nat} (c : NormalizedClause n) (label : Triple)
    (assignment : Fin n → Bool) : Nat :=
  (if label.1 = assignment (c.variable 0) then 1 else 0) +
  (if label.2.1 = assignment (c.variable 1) then 1 else 0) +
  (if label.2.2 = assignment (c.variable 2) then 1 else 0)

theorem agreementCount_le_three {n : Nat} (c : NormalizedClause n) (label : Triple)
    (assignment : Fin n → Bool) : agreementCount c label assignment ≤ 3 := by
  unfold agreementCount
  split <;> split <;> split <;> omega

theorem agreementCount_le_two_of_unsatisfied {n : Nat}
    (c : NormalizedClause n) (label : Triple) (assignment : Fin n → Bool)
    (valid : localEval c.signs label = true)
    (unsatisfied : c.clause.eval assignment = false) :
    agreementCount c label assignment ≤ 2 := by
  by_cases h0 : label.1 = assignment (c.variable 0)
  · by_cases h1 : label.2.1 = assignment (c.variable 1)
    · by_cases h2 : label.2.2 = assignment (c.variable 2)
      · have same : label = c.restrict assignment :=
          Prod.ext h0 (Prod.ext h1 h2)
        rw [same, localEval_restrict, unsatisfied] at valid
        contradiction
      · simp [agreementCount, h0, h1, h2]
    · unfold agreementCount
      simp only [h0, h1, ↓reduceIte]
      split <;> omega
  · unfold agreementCount
    simp only [h0, ↓reduceIte]
    split <;> split <;> omega

theorem agreementCount_le_two_add_satisfied {n : Nat}
    (c : NormalizedClause n) (label : Triple) (assignment : Fin n → Bool)
    (valid : localEval c.signs label = true) :
    agreementCount c label assignment ≤
      2 + (if c.clause.eval assignment then 1 else 0) := by
  cases h : c.clause.eval assignment with
  | false => simpa [h] using agreementCount_le_two_of_unsatisfied c label assignment valid h
  | true => simpa [h] using agreementCount_le_three c label assignment

theorem totalAgreement_le {n : Nat} (states : List (NormalizedClause n × Triple))
    (assignment : Fin n → Bool)
    (valid : ∀ p ∈ states, localEval p.1.signs p.2 = true) :
    (states.map (fun p => agreementCount p.1 p.2 assignment)).sum ≤
      2 * states.length + (states.filter (fun p => p.1.clause.eval assignment)).length := by
  induction states with
  | nil => simp
  | cons p rest ih =>
      have hp := agreementCount_le_two_add_satisfied p.1 p.2 assignment
        (valid p (by simp))
      have hr := ih (fun p h => valid p (by simp [h]))
      cases h : p.1.clause.eval assignment <;>
        simp [h] at hp ⊢ <;> omega

end PerfectCompleteness.SourceClause

end

end OAI
