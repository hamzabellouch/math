import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.QueryIncidence
import OAI.Combinatorics.IndependentSets.PCP.AlphabetReduction

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AlphabetGraph

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators

abbrev Address (V E A : Type*) := (V × Cube A) ⊕ (E × Cube (A × A))

abbrev LocalEvent (A : Type*) := Fin 4 × AlphabetReduction.InputCoordinate A ×
  Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A)

abbrev Event (E A : Type*) := E × LocalEvent A

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev legal (G : ConstraintGraph V E A) (e : E) (p : A × A) : Prop :=
  G.accepts e p.1 p.2 = true

instance legalDecidable (G : ConstraintGraph V E A) (e : E) :
    DecidablePred (legal G e) :=
  fun p => inferInstanceAs (Decidable (G.accepts e p.1 p.2 = true))

def restrictTape (G : ConstraintGraph V E A) (e : E) (f : Cube (A × A)) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) := UniformRestriction.restrict (legal G e) f

def extendTape (G : ConstraintGraph V E A) (e : E)
    (f : Cube (AlphabetReduction.LegalPair (G.accepts e))) : Cube (A × A) :=
  UniformRestriction.extend (legal G e) f

def globalizeQuery (G : ConstraintGraph V E A) (e : E) :
    AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e)) → Address V E A
  | .inl (side, tape) => .inl ((if side then G.head e else G.tail e), tape)
  | .inr tape => .inr (e, extendTape G e tape)

def verifier (G : ConstraintGraph V E A) : QueryIncidence.Verifier (Event E A) (Address V E A) 6 where
  query := fun (e, kind, k, f, g, r₀, r₁, r₂) slot =>
    globalizeQuery G e (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
      (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
      (restrictTape G e r₁) (restrictTape G e r₂) slot)
  accepts := fun (_, kind, _, _, _, _, _, _) b => AssignmentTester.eventAccepts kind b

def vertexBlock (assignment : Address V E A → Bool) (v : V) : Cube A → Bool :=
  fun tape => assignment (.inl (v, tape))

def edgeOracle (G : ConstraintGraph V E A) (assignment : Address V E A → Bool) (e : E) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) → Bool :=
  fun tape => assignment (.inr (e, extendTape G e tape))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem oracleAnswer_globalize (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E)
    (x : AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    assignment (globalizeQuery G e x) =
      AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) x := by
  rcases x with ⟨side, tape⟩ | tape
  · cases side <;> rfl
  · rfl

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem response_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    QueryIncidence.response (verifier G) assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      fun slot => AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e)
        (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
          (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
          (restrictTape G e r₁) (restrictTape G e r₂) slot) := by
  funext slot
  exact oracleAnswer_globalize G assignment e _

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem eventReject_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    eventReject G assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind k
        (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
        (restrictTape G e r₁) (restrictTape G e r₂) := by
  unfold eventReject
  rw [response_eq_local]
  rfl

theorem expect_prod {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℝ) :
    (𝔼 z : I × J, f z) = 𝔼 i : I, 𝔼 j : J, f (i, j) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset I) (Finset.univ : Finset J) f

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

theorem expect_restrict_five {B : Type*} [Fintype B] [DecidableEq B]
    (p : B → Prop) [DecidablePred p]
    (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ({b // p b} → Bool) →
      ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool,
      𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
        h (UniformRestriction.restrict p f) (UniformRestriction.restrict p g)
          (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
          (UniformRestriction.restrict p r₂)) =
    𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool,
      𝔼 r₀ : {b // p b} → Bool, 𝔼 r₁ : {b // p b} → Bool,
        𝔼 r₂ : {b // p b} → Bool, h f g r₀ r₁ r₂ := by
  rw [UniformRestriction.expect_restrict p
    (fun f => 𝔼 g : B → Bool, 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool,
      𝔼 r₂ : B → Bool, h f (UniformRestriction.restrict p g)
        (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro f _
  rw [UniformRestriction.expect_restrict p
    (fun g => 𝔼 r₀ : B → Bool, 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g (UniformRestriction.restrict p r₀) (UniformRestriction.restrict p r₁)
        (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro g _
  rw [UniformRestriction.expect_restrict p
    (fun r₀ => 𝔼 r₁ : B → Bool, 𝔼 r₂ : B → Bool,
      h f g r₀ (UniformRestriction.restrict p r₁) (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₀ _
  rw [UniformRestriction.expect_restrict p
    (fun r₁ => 𝔼 r₂ : B → Bool, h f g r₀ r₁ (UniformRestriction.restrict p r₂))]
  apply Finset.expect_congr rfl
  intro r₁ _
  exact UniformRestriction.expect_restrict p (h f g r₀ r₁)

omit [Nonempty A] in
theorem localAverage_eq_tester (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    localAverage G assignment e = AlphabetReduction.edgeTesterReject (G.accepts e)
      (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
      (edgeOracle G assignment e) := by
  unfold localAverage AlphabetReduction.edgeTesterReject AssignmentTester.explicitTesterReject
  simp only [LocalEvent, expect_prod, eventReject_eq_local, restrictTape]
  apply Finset.expect_congr rfl
  intro kind _
  apply Finset.expect_congr rfl
  intro side _
  apply Finset.expect_congr rfl
  intro tape _
  exact expect_restrict_five (legal G e)
    (AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
      (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
        (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind (side, tape))

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

omit [Nonempty A] in
theorem average_eq_testers [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = 𝔼 e : E, AlphabetReduction.edgeTesterReject (G.accepts e)
      (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
      (edgeOracle G assignment e) := by
  unfold average
  rw [expect_prod]
  exact Finset.expect_congr rfl (fun e _ => localAverage_eq_tester G assignment e)

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

theorem local_gap (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e)) / 2048 ≤
      localAverage G assignment e := by
  cases h : G.edgeSatisfied (decodedLabeling assignment) e with
  | false =>
      rw [localAverage_eq_tester]
      simpa [AssignmentTester.truth] using
        AlphabetReduction.rejected_edge_tester_bound (G.accepts e)
          (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
          (edgeOracle G assignment e) h
  | true =>
      simp only [Bool.not_true, AssignmentTester.truth, Bool.false_eq_true, ite_false, zero_div]
      apply Finset.expect_nonneg
      intro sample _
      exact AssignmentTester.truth_nonneg _

theorem average_gap [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    (𝔼 e : E, AssignmentTester.truth (!(G.edgeSatisfied (decodedLabeling assignment) e))) / 2048 ≤
      average G assignment := by
  unfold average
  rw [expect_prod, Finset.expect_div]
  exact Finset.expect_le_expect (fun e _ => local_gap G assignment e)

theorem expect_rejection_eq_count {I : Type*} [Fintype I] (b : I → Bool) :
    (𝔼 i : I, AssignmentTester.truth (!(b i))) =
      ((Finset.univ.filter (fun i => b i = false)).card : ℝ) / Fintype.card I := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  calc
    (∑ i : I, AssignmentTester.truth (!(b i))) = ∑ i : I, if b i = false then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases b i <;> norm_num [AssignmentTester.truth]
    _ = _ := Finset.sum_boole _ _

omit [Nonempty A] in
theorem average_eq_count [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ) /
      Fintype.card (Event E A) :=
  expect_rejection_eq_count _

omit [Nonempty A] in
@[simp] theorem card_event [Fintype E] :
    Fintype.card (Event E A) = Fintype.card E * Fintype.card (LocalEvent A) :=
  Fintype.card_prod _ _

omit [Nonempty A] in
theorem card_localEvent :
    Fintype.card (LocalEvent A) =
      4 * (2 * 2 ^ Fintype.card A) * (2 ^ (Fintype.card A * Fintype.card A)) ^ 5 := by
  simp [LocalEvent, AlphabetReduction.InputCoordinate, Cube, Fintype.card_prod,
    pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

omit [Nonempty A] in
theorem card_address [Fintype V] [Fintype E] :
    Fintype.card (Address V E A) =
      Fintype.card V * 2 ^ Fintype.card A +
        Fintype.card E * 2 ^ (Fintype.card A * Fintype.card A) := by
  simp [Address, Cube, Fintype.card_sum, Fintype.card_prod]

theorem rejection_count_bound [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    Fintype.card (LocalEvent A) * G.rejectionCount (decodedLabeling assignment) ≤
      2048 * QueryIncidence.verifierRejectionCount (verifier G) assignment := by
  classical
  cases isEmpty_or_nonempty E with
  | inl empty =>
      let := empty
      simp [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts]
  | inr inhabited =>
      let := inhabited
      have h := average_gap G assignment
      rw [average_eq_count, expect_rejection_eq_count, card_event, Nat.cast_mul,
        div_div] at h
      have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
      have hl : (0 : ℝ) < Fintype.card (LocalEvent A) := by
        exact_mod_cast Fintype.card_pos
      have hc := (div_le_div_iff₀ (mul_pos he (by norm_num)) (mul_pos he hl)).mp h
      have hc' :
          ((Fintype.card (LocalEvent A) : ℝ) *
            (G.rejectionCount (decodedLabeling assignment) : ℝ)) * Fintype.card E ≤
          (2048 * (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ)) * Fintype.card E := by
        simpa only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
          mul_assoc, mul_comm, mul_left_comm] using hc
      have result := (mul_le_mul_iff_left₀ he).mp hc'
      exact_mod_cast result

def honestAssignment (G : ConstraintGraph V E A) (labeling : V → A) : Address V E A → Bool
  | .inl (v, tape) => tape (labeling v)
  | .inr (e, tape) => tape (labeling (G.tail e), labeling (G.head e))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem honest_vertexBlock (G : ConstraintGraph V E A) (labeling : V → A) (v : V) :
    vertexBlock (honestAssignment G labeling) v = CodeComposition.codeword (labeling v) := rfl

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_edgeOracle (G : ConstraintGraph V E A) (labeling : V → A) (e : E)
    (h : G.edgeSatisfied labeling e = true) :
    edgeOracle G (honestAssignment G labeling) e =
      fun tape => tape ⟨(labeling (G.tail e), labeling (G.head e)), h⟩ := by
  funext tape
  exact UniformRestriction.extend_apply_of_mem (legal G e) tape
    (labeling (G.tail e), labeling (G.head e)) h

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_event (G : ConstraintGraph V E A) (labeling : V → A)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) (event : Event E A) :
    (verifier G).accepts event (QueryIncidence.response (verifier G) (honestAssignment G labeling) event) =
      true := by
  rcases event with ⟨e, kind, k, f, g, r₀, r₁, r₂⟩
  rw [response_eq_local, honest_edgeOracle G labeling e (satisfied e)]
  simp only [honest_vertexBlock]
  exact AssignmentTester.event_perfect_completeness (AlphabetReduction.pairEncoding (G.accepts e))
    ⟨(labeling (G.tail e), labeling (G.head e)), satisfied e⟩ kind k
    (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
    (restrictTape G e r₁) (restrictTape G e r₂)

def graph [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A) :
    ConstraintGraph (QueryIncidence.Vertex (Event E A) (Address V E A))
      (QueryIncidence.Dart (Event E A) 6) (QueryIncidence.Label 6) := QueryIncidence.graph (verifier G) (by omega)

omit [DecidableEq A] [Nonempty A] in
theorem perfect_completeness [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A)
    (satisfied : G.Satisfiable) : (graph G).Satisfiable := by
  obtain ⟨labeling, h⟩ := satisfied
  exact QueryIncidence.satisfiable_of_verifier_satisfiable (verifier G) (by omega)
    ⟨honestAssignment G labeling, honest_event G labeling h⟩

theorem gap_transfer [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : ConstraintGraph V E A) (a b : Nat)
    (source : ∀ labeling : V → A,
      a * Fintype.card E ≤ b * G.rejectionCount labeling)
    (labeling : QueryIncidence.Vertex (Event E A) (Address V E A) → QueryIncidence.Label 6) :
    a * Fintype.card (QueryIncidence.Dart (Event E A) 6) ≤
      (b * 12288) * (graph G).rejectionCount labeling := by
  have verifierGap (assignment : Address V E A → Bool) :
      a * Fintype.card (Event E A) ≤
        (b * 2048) * QueryIncidence.verifierRejectionCount (verifier G) assignment := by
    rw [card_event]
    calc
      a * (Fintype.card E * Fintype.card (LocalEvent A)) =
          Fintype.card (LocalEvent A) * (a * Fintype.card E) := by ac_rfl
      _ ≤ Fintype.card (LocalEvent A) * (b * G.rejectionCount (decodedLabeling assignment)) :=
        Nat.mul_le_mul_left _ (source (decodedLabeling assignment))
      _ = b * (Fintype.card (LocalEvent A) * G.rejectionCount (decodedLabeling assignment)) := by
        ac_rfl
      _ ≤ b * (2048 * QueryIncidence.verifierRejectionCount (verifier G) assignment) :=
        Nat.mul_le_mul_left _ (rejection_count_bound G assignment)
      _ = (b * 2048) * QueryIncidence.verifierRejectionCount (verifier G) assignment := by ac_rfl
  have h := QueryIncidence.gap_transfer (verifier G) (by omega) a (b * 2048) verifierGap labeling
  have hcoef : b * 2048 * 6 = b * 12288 := by omega
  rw [hcoef] at h
  exact h

theorem alphabet_card : Fintype.card (QueryIncidence.Label 6) = 64 := QueryIncidence.six_query_alphabet

end IndependentSetsGames.Foundations.PCP.AlphabetGraph

end

end OAI
