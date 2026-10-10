import Mathlib
import OAI.Computability.MaxCut.PCP.RawInitialTables

namespace OAI

namespace MaxCutGames.Foundations.PCP.FinalBooleanVerifier

open Target

abbrev Label := Fin 6 → Bool

variable {V E : Type*} {n m : Nat}

def bitIndex (vertices : V ≃ Fin n) (v : V) (j : Fin 6) : Fin (n * 6) :=
  finProdFinEquiv (vertices v, j)

def labelsOfBits (vertices : V ≃ Fin n) (assignment : Fin (n * 6) → Bool) : V → Label :=
  fun v j => assignment (bitIndex vertices v j)

def bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) : Fin (n * 6) → Bool :=
  fun k =>
    let pair : Fin n × Fin 6 := finProdFinEquiv.symm k
    labeling (vertices.symm pair.1) pair.2

@[simp] theorem labelsOfBits_bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) :
    labelsOfBits vertices (bitsOfLabels vertices labeling) = labeling := by
  funext v j
  simp only [labelsOfBits, bitsOfLabels, bitIndex, Equiv.symm_apply_apply]

@[simp] theorem bitsOfLabels_labelsOfBits (vertices : V ≃ Fin n)
    (assignment : Fin (n * 6) → Bool) : bitsOfLabels vertices (labelsOfBits vertices assignment) = assignment := by
  funext k
  simp only [bitsOfLabels, labelsOfBits, bitIndex, Equiv.apply_symm_apply, Prod.eta]

abbrev verifier (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    VerifierToCNF.FiniteVerifier 12 where
  «variables» := n * 6
  events := m
  query := fun e i => Fin.addCases (motive := fun _ : Fin (6 + 6) => Fin (n * 6))
    (fun j : Fin 6 => bitIndex vertices (G.tail (edges.symm e)) j)
    (fun j : Fin 6 => bitIndex vertices (G.head (edges.symm e)) j) i
  accepts := fun e bits => G.accepts (edges.symm e)
    (fun j => bits (Fin.castAdd 6 j)) (fun j => bits (Fin.natAdd 6 j))

theorem query_tail (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.castAdd 6 j) =
      bitIndex vertices (G.tail (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_left]

theorem query_head (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.natAdd 6 j) =
      bitIndex vertices (G.head (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_right]

/-- Acceptance is the actual graph predicate on the two recovered labels. -/
theorem eventValue_eq (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) (e : Fin m) :
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e =
      G.edgeSatisfied (labelsOfBits vertices assignment) (edges.symm e) := by
  simp only [VerifierToCNF.eventValue, Fin.addCases_left, Fin.addCases_right,
    ConstraintGraph.edgeSatisfied]
  rfl

theorem count_false_map_filter {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.filter (fun x => decide (f x = false))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem count_false_finRange (f : Fin m → Bool) :
    ((List.finRange m).map f).count false =
      (Finset.univ.filter (fun e : Fin m => f e = false)).card := by
  classical
  calc
    _ = ((List.finRange m).filter (fun e => decide (f e = false))).length :=
      count_false_map_filter _ _
    _ = (((List.finRange m).filter (fun e => decide (f e = false))).toFinset).card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)).symm
    _ = _ := by
      congr 1
      ext e
      simp

/-- The enumeration preserves the exact directed-dart rejection count. -/
theorem rejection_count_eq [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) :
    VerifierToCNF.rejectedEventCount (verifier G vertices edges) assignment =
      G.rejectionCount (labelsOfBits vertices assignment) := by
  classical
  change ((List.finRange m).map
    (VerifierToCNF.eventValue (verifier G vertices edges) assignment)).count false = _
  rw [count_false_finRange]
  change (Finset.univ.filter (fun e : Fin m =>
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e = false)).card =
      (G.rejectedDarts (labelsOfBits vertices assignment)).card
  apply Finset.card_equiv edges.symm
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    ConstraintGraph.rejectedDarts, eventValue_eq]

theorem verifier_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (labeling : V → Label)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, VerifierToCNF.eventValue (verifier G vertices edges)
      (bitsOfLabels vertices labeling) e = true := by
  intro e
  rw [eventValue_eq, labelsOfBits_bitsOfLabels]
  exact satisfied (edges.symm e)

theorem verifier_reflects (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool)
    (accepted : ∀ e, VerifierToCNF.eventValue (verifier G vertices edges) assignment e = true) :
    ∀ e, G.edgeSatisfied (labelsOfBits vertices assignment) e = true := by
  intro e
  have h := accepted (edges e)
  simpa only [eventValue_eq, Equiv.symm_apply_apply] using h

def cnf (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) : Formula :=
  VerifierToCNF.convert (verifier G vertices edges) (by decide)

abbrev OutputAssignment (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) :=
  Fin (VerifierToCNF.outputVariables (verifier G vertices edges)) → Bool

def extractLabeling (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) : V → Label :=
  labelsOfBits vertices (VerifierToCNF.restrictAssignment (verifier G vertices edges) assignment)

theorem cnf_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (sat : G.Satisfiable) : (cnf G vertices edges).Satisfiable := by
  obtain ⟨labeling, satisfied⟩ := sat
  exact VerifierToCNF.convert_completeness (verifier G vertices edges) (by decide)
    (bitsOfLabels vertices labeling) (verifier_completeness G vertices edges labeling satisfied)

theorem cnf_count_bridge [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) :
    G.rejectionCount (extractLabeling G vertices edges assignment) ≤
      NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have h := VerifierToCNF.convert_count_bridge (verifier G vertices edges) (by decide) assignment
  rw [rejection_count_eq] at h
  exact h

theorem failedCount_zero_of_satisfied (F : Formula) (assignment : Fin F.«variables» → Bool)
    (satisfied : ∀ c ∈ F.clauses, c.eval assignment = true) :
    NameCompaction.failedCount F assignment = 0 := by
  apply (VerifierToCNF.zero_false_count_iff_all _).mpr
  have h := List.all_eq_true.mpr satisfied
  simpa only [NameCompaction.evaluationList, List.all_map, Function.comp_def, id_eq] using h

theorem all_satisfied_of_rejectionCount_zero [Fintype E] (G : ConstraintGraph V E Label)
    (labeling : V → Label) (zero : G.rejectionCount labeling = 0) :
    ∀ e, G.edgeSatisfied labeling e = true := by
  intro e
  cases h : G.edgeSatisfied labeling e with
  | true => rfl
  | false =>
    have member : e ∈ G.rejectedDarts labeling := (G.mem_rejectedDarts labeling e).mpr h
    have positive : 0 < G.rejectionCount labeling := Finset.card_pos.mpr ⟨e, member⟩
    omega

theorem cnf_reflects [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (sat : (cnf G vertices edges).Satisfiable) :
    G.Satisfiable := by
  obtain ⟨assignment, satisfied⟩ := sat
  have zero := failedCount_zero_of_satisfied (cnf G vertices edges) assignment satisfied
  have bound := cnf_count_bridge G vertices edges assignment
  have graphZero : G.rejectionCount (extractLabeling G vertices edges assignment) = 0 := by omega
  exact ⟨extractLabeling G vertices edges assignment,
    all_satisfied_of_rejectionCount_zero G _ graphZero⟩

theorem cnf_satisfiable_iff [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (cnf G vertices edges).Satisfiable ↔ G.Satisfiable :=
  ⟨cnf_reflects G vertices edges, cnf_completeness G vertices edges⟩

theorem cnf_clause_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).clauses.length = m * 40960 :=
  VerifierToCNF.twelve_query_clause_count (verifier G vertices edges)

theorem twelve_query_auxiliary_factor : 2 ^ 12 * (12 - 3) = 36864 := by decide

theorem cnf_variable_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).«variables» = n * 6 + m * 36864 := by
  change n * 6 + m * (VerifierToCNF.patterns 12).length * (12 - 3) = _
  rw [VerifierToCNF.patterns_length, Nat.mul_assoc, twelve_query_auxiliary_factor]

theorem cnf_nonempty (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (nonempty : 0 < m) : (cnf G vertices edges).clauses ≠ [] :=
  VerifierToCNF.convert_nonempty (verifier G vertices edges) (by decide) nonempty

theorem cnf_gap [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : Nat)
    (source : ∀ labeling : V → Label, a * Fintype.card E ≤ b * G.rejectionCount labeling)
    (assignment : OutputAssignment G vertices edges) :
    a * (cnf G vertices edges).clauses.length ≤
      (b * 40960) * NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have cardEdges : Fintype.card E = m := by simpa using Fintype.card_congr edges
  have testGap (bits : Fin (n * 6) → Bool) :
      a * m ≤ b * VerifierToCNF.rejectedEventCount (verifier G vertices edges) bits := by
    rw [rejection_count_eq]
    simpa only [cardEdges] using source (labelsOfBits vertices bits)
  simpa only [cnf, VerifierToCNF.twelve_query_factor] using
    VerifierToCNF.convert_gap (verifier G vertices edges) (by decide) a b testGap assignment

/-! Direct application to the checked alphabet-reduction graph. -/

abbrev ReducedVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev ReducedDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [DecidableEq V] [DecidableEq E]

noncomputable def alphabetCNF (G : ConstraintGraph V E A)
    (vertices : ReducedVertex V E A ≃ Fin n) (edges : ReducedDart E A ≃ Fin m) : Formula :=
  cnf (AlphabetGraph.graph G) vertices edges

omit [DecidableEq A] [Nonempty A] in
theorem alphabetCNF_completeness (G : ConstraintGraph V E A)
    (vertices : ReducedVertex V E A ≃ Fin n) (edges : ReducedDart E A ≃ Fin m)
    (sat : G.Satisfiable) : (alphabetCNF G vertices edges).Satisfiable :=
  cnf_completeness (AlphabetGraph.graph G) vertices edges (AlphabetGraph.perfect_completeness G sat)

omit [DecidableEq A] [Nonempty A] in
theorem alphabetCNF_clause_count (G : ConstraintGraph V E A)
    (vertices : ReducedVertex V E A ≃ Fin n) (edges : ReducedDart E A ≃ Fin m) :
    (alphabetCNF G vertices edges).clauses.length = m * 40960 :=
  cnf_clause_count (AlphabetGraph.graph G) vertices edges

theorem alphabetCNF_gap [Fintype E] (G : ConstraintGraph V E A)
    (vertices : ReducedVertex V E A ≃ Fin n) (edges : ReducedDart E A ≃ Fin m)
    (a b : Nat)
    (source : ∀ labeling : V → A, a * Fintype.card E ≤ b * G.rejectionCount labeling)
    (assignment : OutputAssignment (AlphabetGraph.graph G) vertices edges) :
    a * (alphabetCNF G vertices edges).clauses.length ≤
      (b * 503316480) * NameCompaction.failedCount (alphabetCNF G vertices edges) assignment := by
  have h := cnf_gap (AlphabetGraph.graph G) vertices edges a (b * 12288)
    (AlphabetGraph.gap_transfer G a b source) assignment
  have factor : (b * 12288) * 40960 = b * 503316480 := by omega
  simpa only [alphabetCNF, factor] using h

end MaxCutGames.Foundations.PCP.FinalBooleanVerifier

end OAI
