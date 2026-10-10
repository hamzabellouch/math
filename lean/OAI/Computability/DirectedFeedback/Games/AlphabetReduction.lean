import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.PoweringTables

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.PCP.AlphabetReduction

open DFVSGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

abbrev InputCoordinate (A : Type*) := Bool × Cube A

def pairEncoding (accepts : A → A → Bool) (p : LegalPair accepts) :
    InputCoordinate A → Bool :=
  pairWord (codeword p.1.1) (codeword p.1.2)

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

theorem rejected_edge_tester_bound (accepts : A → A → Bool)
    (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool)
    (hbad : accepts (nearest left) (nearest right) = false) :
    1 / 2048 ≤ edgeTesterReject accepts left right F := by
  have hfar (p : LegalPair accepts) :
      (1 / 8 : ℝ) ≤ AssignmentTester.distance (pairWord left right) (pairEncoding accepts p) := by
    have h := rejected_pair_far accepts left right hbad p.1.1 p.1.2 p.2
    convert h using 1
    rfl
  have h := AssignmentTester.explicit_proximity_soundness (pairEncoding accepts)
    (pairWord left right) F (δ := 1 / 8) (by norm_num) (by norm_num) hfar
  norm_num at h
  exact h

omit [Nonempty A] in
theorem honest_edge_tester (accepts : A → A → Bool) (a b : A)
    (hab : accepts a b = true) :
    edgeTesterReject accepts (codeword a) (codeword b)
      (fun f => f ⟨(a, b), hab⟩) = 0 := by
  unfold edgeTesterReject
  rw [AssignmentTester.explicitTesterReject_eq]
  exact AssignmentTester.tester_perfect_completeness
    (pairEncoding accepts) ⟨(a, b), hab⟩

end DFVSGames.Foundations.PCP.AlphabetReduction
end


namespace DFVSGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

def canonicalize (f : B → Bool) : B → Bool := extend p (restrict p f)

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

@[simp] theorem canonicalize_apply_of_mem (f : B → Bool) (b : B) (hb : p b) :
    canonicalize p f b = f b := by
  simp [canonicalize, hb]

@[simp] theorem canonicalize_apply_of_not_mem (f : B → Bool) (b : B)
    (hb : ¬ p b) : canonicalize p f b = false := by
  simp [canonicalize, hb]

@[simp] theorem restrict_canonicalize (f : B → Bool) :
    restrict p (canonicalize p f) = restrict p f := by
  exact restrict_extend p (restrict p f)

@[simp] theorem canonicalize_idempotent (f : B → Bool) :
    canonicalize p (canonicalize p f) = canonicalize p f := by
  simp only [canonicalize, restrict_extend]

theorem canonicalize_eq_iff (f g : B → Bool) :
    canonicalize p f = canonicalize p g ↔ restrict p f = restrict p g := by
  constructor
  · intro h
    simpa only [restrict_canonicalize] using congrArg (restrict p) h
  · intro h
    exact congrArg (extend p) h


variable [Fintype B] [DecidableEq B]

theorem expect_restrict (h : ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (restrict p f)) = 𝔼 g : {b // p b} → Bool, h g := by
  calc
    (𝔼 f : B → Bool, h (restrict p f)) =
        𝔼 g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool), h g.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Bool))
        _ _ (fun _ => rfl)
    _ = 𝔼 g : {b // p b} → Bool, 𝔼 _k : {b // ¬ p b} → Bool, h g := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product
          (Finset.univ : Finset ({b // p b} → Bool))
          (Finset.univ : Finset ({b // ¬ p b} → Bool))
          (fun g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool) => h g.1)
    _ = 𝔼 g : {b // p b} → Bool, h g := by
      simp only [Fintype.expect_const]

theorem expect_canonicalize (h : (B → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (canonicalize p f)) =
      𝔼 g : {b // p b} → Bool, h (extend p g) :=
  expect_restrict p (fun g => h (extend p g))

theorem expect_restrict_pair (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, h (restrict p f) (restrict p g)) =
      𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool, h f g := by
  calc
    _ = 𝔼 f : B → Bool, 𝔼 g : {b // p b} → Bool, h (restrict p f) g := by
      apply Finset.expect_congr rfl
      intro f _
      exact expect_restrict p (h (restrict p f))
    _ = _ := expect_restrict p (fun f => 𝔼 g : {b // p b} → Bool, h f g)


end DFVSGames.Foundations.PCP.UniformRestriction


noncomputable section

namespace DFVSGames.Foundations.PCP.AlphabetGraph

open DFVSGames.Foundations.Hastad
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

end DFVSGames.Foundations.PCP.AlphabetGraph

end


namespace DFVSGames.Foundations.PCP.AlphabetTable.Enumeration

open DFVSGames.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem boolEquiv_val (bit : Bool) : (boolEquiv bit).val = bitValue bit := by
  cases bit <;> rfl

def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

@[simp] theorem productEquiv_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) (y : B) :
    (productEquiv left right (x, y)).val = (left x).val * b + (right y).val := by
  change (right y).val + b * (left x).val = _
  simp [Nat.mul_comm, Nat.add_comm]

def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

@[simp] theorem sumEquiv_inl_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) :
    (sumEquiv left right (.inl x)).val = (left x).val := rfl

@[simp] theorem sumEquiv_inr_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (y : B) :
    (sumEquiv left right (.inr y)).val = a + (right y).val := rfl

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

def cubeEquiv (q : Nat) : Cube (Fin q) ≃ Fin (tapeCount q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) boolEquiv).trans finFunctionFinEquiv

def cubeRank {q : Nat} (tape : Cube (Fin q)) : Fin (tapeCount q) := cubeEquiv q tape
def cubeUnrank {q : Nat} (index : Fin (tapeCount q)) : Cube (Fin q) :=
  (cubeEquiv q).symm index

@[simp] theorem cubeUnrank_cubeRank {q : Nat} (tape : Cube (Fin q)) :
    cubeUnrank (cubeRank tape) = tape := (cubeEquiv q).symm_apply_apply tape

@[simp] theorem cubeRank_cubeUnrank {q : Nat} (index : Fin (tapeCount q)) :
    cubeRank (cubeUnrank index) = index := (cubeEquiv q).apply_symm_apply index

theorem cubeUnrank_digit {q : Nat} (index : Fin (tapeCount q)) (i : Fin q) :
    bitValue (cubeUnrank index i) = index.val / 2 ^ i.val % 2 := by
  have digit : boolEquiv (cubeUnrank index i) =
      (⟨index.val / 2 ^ i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) := by
    change boolEquiv (boolEquiv.symm _) = _
    exact boolEquiv.apply_symm_apply _
  simpa only [boolEquiv_val] using congrArg Fin.val digit

theorem cubeEquiv_val (q : Nat) (tape : Cube (Fin q)) :
    (cubeEquiv q tape).val = ∑ i : Fin q, bitValue (tape i) * 2 ^ i.val := by
  change (finFunctionFinEquiv (fun i => boolEquiv (tape i))).val = _
  rw [finFunctionFinEquiv_apply]
  simp only [boolEquiv_val]

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

theorem pairIndex_val (q : Nat) (i j : Fin q) :
    (pairIndex q (i, j)).val = i.val * q + j.val := by
  change j.val + q * i.val = _
  simp [Nat.mul_comm, Nat.add_comm]

def pairCubeEquiv (q : Nat) : Cube (Fin q × Fin q) ≃ Fin (pairTapeCount q) :=
  (Equiv.arrowCongr (pairIndex q) (Equiv.refl Bool)).trans (cubeEquiv (q * q))

def pairCubeRank {q : Nat} (tape : Cube (Fin q × Fin q)) : Fin (pairTapeCount q) :=
  pairCubeEquiv q tape

def pairCubeUnrank {q : Nat} (index : Fin (pairTapeCount q)) : Cube (Fin q × Fin q) :=
  (pairCubeEquiv q).symm index

@[simp] theorem pairCubeUnrank_pairCubeRank {q : Nat} (tape : Cube (Fin q × Fin q)) :
    pairCubeUnrank (pairCubeRank tape) = tape := (pairCubeEquiv q).symm_apply_apply tape

@[simp] theorem pairCubeRank_pairCubeUnrank {q : Nat} (index : Fin (pairTapeCount q)) :
    pairCubeRank (pairCubeUnrank index) = index := (pairCubeEquiv q).apply_symm_apply index

theorem pairCubeEquiv_val (q : Nat) (tape : Cube (Fin q × Fin q)) :
    (pairCubeEquiv q tape).val =
      ∑ i : Fin (q * q), bitValue (tape ((pairIndex q).symm i)) * 2 ^ i.val :=
  cubeEquiv_val (q * q) _

def inputCoordinateEquiv (q : Nat) :
    AlphabetReduction.InputCoordinate (Fin q) ≃ Fin (2 * tapeCount q) :=
  productEquiv boolEquiv (cubeEquiv q)

def fivePairTapesEquiv (q : Nat) :
    (Cube (Fin q × Fin q) × Cube (Fin q × Fin q) × Cube (Fin q × Fin q) ×
      Cube (Fin q × Fin q) × Cube (Fin q × Fin q)) ≃ Fin (fiveTapeCount q) :=
  (productEquiv (pairCubeEquiv q)
    (productEquiv (pairCubeEquiv q)
      (productEquiv (pairCubeEquiv q)
        (productEquiv (pairCubeEquiv q) (pairCubeEquiv q))))).trans
    (finCongr (by simp [fiveTapeCount, pow_succ, Nat.mul_assoc]))

def localEventEquiv (q : Nat) : AlphabetGraph.LocalEvent (Fin q) ≃ Fin (localCount q) :=
  (productEquiv (Equiv.refl (Fin 4))
    (productEquiv (inputCoordinateEquiv q) (fivePairTapesEquiv q))).trans
    (finCongr (by simp [localCount, Nat.mul_assoc]))

def eventEquiv (m q : Nat) :
    AlphabetGraph.Event (Fin m) (Fin q) ≃ Fin (eventCount m q) :=
  productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)

def addressEquiv (n m q : Nat) :
    AlphabetGraph.Address (Fin n) (Fin m) (Fin q) ≃ Fin (addressCount n m q) :=
  sumEquiv (productEquiv (Equiv.refl (Fin n)) (cubeEquiv q))
    (productEquiv (Equiv.refl (Fin m)) (pairCubeEquiv q))

def vertexEquiv (n m q : Nat) :
    QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) ≃ Fin (vertexCount n m q) :=
  sumEquiv (eventEquiv m q) (addressEquiv n m q)

def dartEquiv (m q : Nat) :
    QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6 ≃ Fin (dartCount m q) :=
  (productEquiv (productEquiv (eventEquiv m q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [dartCount, Nat.mul_assoc]))

def labelEquiv : QueryIncidence.Label 6 ≃ Fin 64 := cubeEquiv 6

theorem labelEquiv_val (label : QueryIncidence.Label 6) :
    (labelEquiv label).val = ∑ i : Fin 6, bitValue (label i) * 2 ^ i.val :=
  cubeEquiv_val 6 label

@[simp] theorem inputCoordinateEquiv_val (q : Nat) (side : Bool) (tape : Cube (Fin q)) :
    (inputCoordinateEquiv q (side, tape)).val =
      bitValue side * tapeCount q + (cubeEquiv q tape).val := by
  simp [inputCoordinateEquiv]

theorem fivePairTapesEquiv_val (q : Nat) (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) :
    (fivePairTapesEquiv q (f, g, r₀, r₁, r₂)).val =
      (pairCubeEquiv q f).val * pairTapeCount q ^ 4 +
        (pairCubeEquiv q g).val * pairTapeCount q ^ 3 +
        (pairCubeEquiv q r₀).val * pairTapeCount q ^ 2 +
        (pairCubeEquiv q r₁).val * pairTapeCount q + (pairCubeEquiv q r₂).val := by
  simp [fivePairTapesEquiv, productEquiv_val, pow_succ, Nat.mul_assoc, Nat.add_assoc]

theorem localEventEquiv_val (q : Nat) (kind : Fin 4)
    (coordinate : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) :
    (localEventEquiv q (kind, coordinate, f, g, r₀, r₁, r₂)).val =
      kind.val * (2 * tapeCount q * fiveTapeCount q) +
        (inputCoordinateEquiv q coordinate).val * fiveTapeCount q +
        (fivePairTapesEquiv q (f, g, r₀, r₁, r₂)).val := by
  simp [localEventEquiv, productEquiv_val, Nat.add_assoc]

@[simp] theorem eventEquiv_val (m q : Nat) (edge : Fin m)
    (sample : AlphabetGraph.LocalEvent (Fin q)) :
    (eventEquiv m q (edge, sample)).val = edge.val * localCount q +
      (localEventEquiv q sample).val := by
  change (localEventEquiv q sample).val + localCount q * edge.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inl_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (addressEquiv n m q (.inl (vertex, tape))).val =
      vertex.val * tapeCount q + (cubeEquiv q tape).val := by
  change (cubeEquiv q tape).val + tapeCount q * vertex.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inr_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (addressEquiv n m q (.inr (edge, tape))).val =
      n * tapeCount q + (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val) := by
  change n * tapeCount q + ((pairCubeEquiv q tape).val + pairTapeCount q * edge.val) = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem vertexEquiv_event_val (n m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) :
    (vertexEquiv n m q (.inl event)).val = (eventEquiv m q event).val := rfl

@[simp] theorem vertexEquiv_vertexAddress_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (vertexEquiv n m q (.inr (.inl (vertex, tape)))).val =
      eventCount m q + (vertex.val * tapeCount q + (cubeEquiv q tape).val) := by
  change eventCount m q + (addressEquiv n m q (.inl (vertex, tape))).val = _
  rw [addressEquiv_inl_val]

@[simp] theorem vertexEquiv_edgeAddress_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (vertexEquiv n m q (.inr (.inr (edge, tape)))).val =
      eventCount m q + (n * tapeCount q +
        (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val)) := by
  change eventCount m q + (addressEquiv n m q (.inr (edge, tape))).val = _
  rw [addressEquiv_inr_val]

@[simp] theorem dartEquiv_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q ((event, slot), orientation)).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue orientation := by
  change (boolEquiv orientation).val + 2 * (slot.val + 6 * (eventEquiv m q event).val) = _
  rw [boolEquiv_val]
  omega

theorem dartEquiv_reverse_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q (QueryIncidence.reverse ((event, slot), orientation))).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue (!orientation) :=
  dartEquiv_val m q event slot (!orientation)

def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

@[simp] theorem ordered_length {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).length = count := by simp [ordered]

theorem mem_ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) (x : A) :
    x ∈ ordered order := by
  simp only [ordered, List.mem_ofFn]
  exact ⟨order x, order.symm_apply_apply x⟩

theorem ordered_nodup {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).Nodup := by
  rw [ordered, List.nodup_ofFn]
  exact order.symm.injective

@[simp] theorem ordered_refl (n : Nat) : ordered (Equiv.refl (Fin n)) = List.finRange n := rfl

@[simp] theorem ordered_bool : ordered boolEquiv = [false, true] := rfl

theorem ordered_trans_finCongr {A : Type*} {a b : Nat}
    (order : A ≃ Fin a) (sameCount : a = b) :
    ordered (order.trans (finCongr sameCount)) = ordered order := by
  cases sameCount
  rfl

theorem ordered_product {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) :
    ordered (productEquiv left right) =
      (ordered left).flatMap (fun x => (ordered right).map (fun y => (x, y))) := by
  have atIndex (i : Fin a) (j : Fin b) (h : i.val * b + j.val < a * b) :
      (productEquiv left right).symm ⟨i.val * b + j.val, h⟩ =
        (left.symm i, right.symm j) := by
    have same : (⟨i.val * b + j.val, h⟩ : Fin (a * b)) = finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [same]
    simp [productEquiv]
  unfold ordered
  rw [List.ofFn_mul]
  simp only [atIndex, List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem ordered_sum {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) :
    ordered (sumEquiv left right) =
      (ordered left).map Sum.inl ++ (ordered right).map Sum.inr := by
  have atLeft (i : Fin a) :
      (sumEquiv left right).symm (i.castLE (Nat.le_add_right a b)) =
        Sum.inl (left.symm i) := by
    change (Equiv.sumCongr left right).symm
      (finSumFinEquiv.symm (Fin.castAdd b i)) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  have atRight (j : Fin b) :
      (sumEquiv left right).symm (j.natAdd a) = Sum.inr (right.symm j) := by
    change (Equiv.sumCongr left right).symm (finSumFinEquiv.symm (j.natAdd a)) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  unfold ordered
  rw [List.ofFn_add]
  simp only [atLeft, atRight, List.map_ofFn, Function.comp_def]

def localEvents (q : Nat) : List (AlphabetGraph.LocalEvent (Fin q)) :=
  ordered (localEventEquiv q)

@[simp] theorem localEvents_length (q : Nat) : (localEvents q).length = localCount q :=
  ordered_length _

theorem ordered_event (m q : Nat) :
    ordered (eventEquiv m q) =
      (List.finRange m).flatMap (fun edge => (localEvents q).map (fun event => (edge, event))) := by
  change ordered (productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)) = _
  rw [ordered_product, ordered_refl]
  rfl

theorem ordered_dart (m q : Nat) :
    ordered (dartEquiv m q) =
      (List.finRange m).flatMap (fun edge =>
        (localEvents q).flatMap (fun event =>
          (List.finRange 6).flatMap (fun slot =>
            [(((edge, event), slot), false), (((edge, event), slot), true)]))) := by
  unfold dartEquiv dartCount
  rw [ordered_trans_finCongr, ordered_product, ordered_product, ordered_event]
  simp only [ordered_refl, ordered_bool, List.flatMap_assoc, List.flatMap_map,
    List.map_cons, List.map_nil]

@[simp] theorem card_cube (q : Nat) : Fintype.card (Cube (Fin q)) = tapeCount q := by
  simpa using Fintype.card_congr (cubeEquiv q)

@[simp] theorem card_pairCube (q : Nat) :
    Fintype.card (Cube (Fin q × Fin q)) = pairTapeCount q := by
  simpa using Fintype.card_congr (pairCubeEquiv q)

@[simp] theorem card_localEvent (q : Nat) :
    Fintype.card (AlphabetGraph.LocalEvent (Fin q)) = localCount q := by
  simpa using Fintype.card_congr (localEventEquiv q)

@[simp] theorem card_event (m q : Nat) :
    Fintype.card (AlphabetGraph.Event (Fin m) (Fin q)) = eventCount m q := by
  simpa using Fintype.card_congr (eventEquiv m q)

@[simp] theorem card_address (n m q : Nat) :
    Fintype.card (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) = addressCount n m q := by
  simpa using Fintype.card_congr (addressEquiv n m q)

@[simp] theorem card_vertex (n m q : Nat) :
    Fintype.card (QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q))) = vertexCount n m q := by
  simpa using Fintype.card_congr (vertexEquiv n m q)

@[simp] theorem card_dart (m q : Nat) :
    Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6) =
      dartCount m q := by
  simpa using Fintype.card_congr (dartEquiv m q)

@[simp] theorem localCount_formula (q : Nat) :
    localCount q = 4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5 := rfl

end DFVSGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
