import Mathlib
import OAI.Computability.MaxCut.Games.FinalCNFPattern
import OAI.Computability.MaxCut.PCP.GraphTableComplexity

namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

theorem powered_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label)
    (labeling : Preprocessing.Vertex G → PoweredAlphabet) :
    poweredLower G.gap * (Fintype.card (PoweredDart G) : ℝ) ≤
      ((powered addresses complete G).rejectionCount labeling : ℝ) := by
  let H := Overlay.originalPortGraph (Preprocessing.overlayGraph G)
  have certificate : SpectralReturn.SpectralCertificate
      (PoweringWalks.lazyGraph H) (31 / 32 : ℝ) :=
    Preprocessing.spectral_certificate G
  have lower : ∀ assignment : Preprocessing.Vertex G → Label,
      (G.gap / (Preprocessing.sizeFactor : ℝ)) *
          (Fintype.card (Preprocessing.Vertex G × Preprocessing.Port) : ℝ) ≤
        ((Preprocessing.graph G).rejectionCount assignment : ℝ) :=
    Preprocessing.gap_transfer_real G G.gap G.gap_nonnegative
      ((G.le_gap_iff G.gap).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have h := PoweringGap.uniform_count_gap H (31 / 32) certificate
    (Preprocessing.graph G).accepts (Preprocessing.accepts_reverse G)
    FinalConstants.windowHalf FinalConstants.windowHalf_positive
    (selectors addresses complete G)
    (G.gap / (Preprocessing.sizeFactor : ℝ)) (div_nonneg G.gap_nonnegative hs.le)
    lower labeling
  convert h using 1 <;>
    simp only [poweredLower, powered, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq]
  rfl

theorem amplifies (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    min (2 * G.gap) FinalConstants.cap ≤ (graph addresses complete G).gap := by
  apply ((graph addresses complete G).le_gap_iff _).mpr
  intro labeling
  have hcount := AlphabetGraphBounds.gap_transfer_real (powered addresses complete G)
    (poweredLower G.gap) (poweredLower_nonnegative G.gap G.gap_nonnegative)
    (powered_count_gap addresses complete G) labeling
  have hscalar : min (2 * G.gap) FinalConstants.cap ≤ poweredLower G.gap / 12288 := by
    simpa only [poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap G.gap G.gap_nonnegative
  exact (mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg _)).trans hcount

end MaxCutGames.Foundations.PCP.RoundGap
end

/-!
# Size of the actual fixed amplification round

All constants below depend only on the fixed port alphabet and walk length.
The round itself is the checked preprocessing, powering, and alphabet graph
construction in `AmplificationRound`; no second graph constructor is introduced.
Closed constants are kept symbolic rather than evaluated.
-/

namespace MaxCutGames.Foundations.PCP.RoundSize

open scoped BigOperators

noncomputable section

theorem card_padded_alphabet {D A : Type*} [Fintype D] [DecidableEq D]
    [Fintype A] (t : Nat) :
    Fintype.card (PoweringLabels.PaddedLabel D t A) =
      Fintype.card A ^ (∑ k : Fin (t + 1), Fintype.card D ^ k.val) := by
  simpa only [Nat.card_eq_fintype_card] using
    PoweringLabels.card_paddedLabel (D := D) (A := A) t

theorem card_powered_dart {V D : Type*} [Fintype V] [Fintype D]
    (n : Nat) : Fintype.card (PoweringTest.Dart V D n) =
      Fintype.card V * (2 * Fintype.card D ^ (n + 1)) := by
  simp only [PoweringTest.Dart, PoweringWalks.Walk, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
  ring

/- An opaque value with a checked equality prevents the kernel's closed-numeral
evaluator from expanding the astronomical powers. Its body is proved once for
an arbitrary natural number; no axiom or trusted evaluator is introduced.
Only size bounds use these constants, not the graph's algorithm definitions. -/
private opaque lockedNat (n : Nat) : {m : Nat // m = n} := ⟨n, rfl⟩

def poweredAlphabetSize : Nat :=
  (lockedNat (64 ^ (∑ k : Fin (FinalConstants.walkLength + 1),
    Preprocessing.degree ^ k.val))).val

def poweredDartFactor : Nat :=
  (lockedNat (2 * Preprocessing.degree ^ (2 * FinalConstants.endpointLength + 1))).val

def sizeFactor : Nat :=
  (lockedNat (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
    (1 + poweredDartFactor) * ExpanderFamily.growth ^ 2)).val

theorem poweredAlphabetSize_eq : poweredAlphabetSize =
    64 ^ (∑ k : Fin (FinalConstants.walkLength + 1), Preprocessing.degree ^ k.val) :=
  (lockedNat _).property

theorem poweredDartFactor_eq : poweredDartFactor =
    2 * Preprocessing.degree ^ (2 * FinalConstants.endpointLength + 1) :=
  (lockedNat _).property

theorem sizeFactor_eq : sizeFactor = AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
    (1 + poweredDartFactor) * ExpanderFamily.growth ^ 2 :=
  (lockedNat _).property

private theorem coefficient_positive_inline_RoundSize (q d g : Nat) (hg : 0 < g) :
    0 < AlphabetGraphBounds.sizeFactor q * (1 + d) * g ^ 2 := by
  exact Nat.mul_pos (Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive q)
    (Nat.zero_lt_one.trans_le (Nat.le_add_right 1 d))) (pow_pos hg 2)

theorem poweredAlphabet_card : Fintype.card AmplificationRound.PoweredAlphabet =
    poweredAlphabetSize := by
  have h := PoweringLabels.card_paddedLabel (D := Preprocessing.Port)
    (A := QueryIncidence.Label 6) FinalConstants.walkLength
  change Nat.card AmplificationRound.PoweredAlphabet = _ at h
  simp only [Nat.card_eq_fintype_card, ← Preprocessing.degree_eq_card,
    QueryIncidence.six_query_alphabet] at h
  exact h.trans poweredAlphabetSize_eq.symm

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hG : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  rw [sizeFactor_eq]
  exact coefficient_positive_inline_RoundSize _ _ _ hG

private theorem factor_total_inline_RoundSize (c v d : Nat) : c * (v + v * d) = c * (1 + d) * v := by
  ring

private theorem nat_card_output_vertex_inline_RoundSize {V E A : Type*}
    [Fintype V] [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputVertex V E A) =
      Nat.card V * 2 ^ Nat.card A +
        Nat.card E * AlphabetGraphBounds.vertexFactor (Nat.card A) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_vertex (V := V) (E := E) (A := A)

private theorem nat_card_output_dart_inline_RoundSize {E A : Type*}
    [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputDart E A) =
      Nat.card E * AlphabetGraphBounds.dartFactor (Nat.card A) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_dart (E := E) (A := A)

private theorem nat_card_output_total_le_inline_RoundSize {V E A : Type*}
    [Fintype V] [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputVertex V E A) +
        Nat.card (AlphabetGraphBounds.OutputDart E A) ≤
      AlphabetGraphBounds.sizeFactor (Nat.card A) * (Nat.card V + Nat.card E) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_total_le (V := V) (E := E) (A := A)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

omit [DecidableEq E] [Nonempty E] in
theorem poweredDart_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.PoweredDart G) =
      Fintype.card (Preprocessing.Vertex G) * poweredDartFactor := by
  have h := card_powered_dart (V := Preprocessing.Vertex G) (D := Preprocessing.Port)
    (2 * FinalConstants.endpointLength)
  rw [← Preprocessing.degree_eq_card] at h
  exact h.trans (congrArg (fun d => Fintype.card (Preprocessing.Vertex G) * d)
    poweredDartFactor_eq.symm)

omit [DecidableEq E] [Nonempty E] in
/-- The exact cardinality of the round's output vertex type. -/
theorem output_vertex_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) =
      Fintype.card (Preprocessing.Vertex G) * 2 ^ poweredAlphabetSize +
        (Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) *
          AlphabetGraphBounds.vertexFactor poweredAlphabetSize := by
  have h := nat_card_output_vertex_inline_RoundSize (V := Preprocessing.Vertex G)
    (E := AmplificationRound.PoweredDart G) (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Vertex G) =
    Nat.card (Preprocessing.Vertex G) * 2 ^ Nat.card AmplificationRound.PoweredAlphabet +
      Nat.card (AmplificationRound.PoweredDart G) *
        AlphabetGraphBounds.vertexFactor (Nat.card AmplificationRound.PoweredAlphabet) at h
  simpa only [Nat.card_eq_fintype_card, poweredAlphabet_card, poweredDart_card] using h

omit [DecidableEq E] [Nonempty E] in
/-- The exact cardinality of the round's output dart type. -/
theorem output_dart_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Dart G) =
      (Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) *
        AlphabetGraphBounds.dartFactor poweredAlphabetSize := by
  have h := nat_card_output_dart_inline_RoundSize (E := AmplificationRound.PoweredDart G)
    (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Dart G) = Nat.card (AmplificationRound.PoweredDart G) *
    AlphabetGraphBounds.dartFactor (Nat.card AmplificationRound.PoweredAlphabet) at h
  simpa only [Nat.card_eq_fintype_card, poweredAlphabet_card, poweredDart_card] using h

omit [DecidableEq E] in
/-- The actual round has linear total size, even in the old dart count alone. -/
theorem output_total_le_darts (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) + Fintype.card (AmplificationRound.Dart G) ≤
      sizeFactor * Fintype.card E := by
  have h := nat_card_output_total_le_inline_RoundSize
    (V := Preprocessing.Vertex G) (E := AmplificationRound.PoweredDart G)
    (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Vertex G) + Nat.card (AmplificationRound.Dart G) ≤
    AlphabetGraphBounds.sizeFactor (Nat.card AmplificationRound.PoweredAlphabet) *
      (Nat.card (Preprocessing.Vertex G) + Nat.card (AmplificationRound.PoweredDart G)) at h
  simp only [Nat.card_eq_fintype_card] at h
  rw [poweredAlphabet_card, poweredDart_card] at h
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (Fintype.card (Preprocessing.Vertex G) +
          Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) := h
    _ = (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (1 + poweredDartFactor)) * Fintype.card (Preprocessing.Vertex G) :=
      factor_total_inline_RoundSize _ _ _
    _ ≤ (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (1 + poweredDartFactor)) * (ExpanderFamily.growth ^ 2 * Fintype.card E) :=
      Nat.mul_le_mul_left _ (Preprocessing.vertex_count_le G)
    _ = sizeFactor * Fintype.card E := by
      rw [sizeFactor_eq]
      exact (Nat.mul_assoc _ _ _).symm

omit [DecidableEq E] in
theorem output_total_le (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) + Fintype.card (AmplificationRound.Dart G) ≤
      sizeFactor * (Fintype.card V + Fintype.card E) :=
  (output_total_le_darts G).trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))

end

end MaxCutGames.Foundations.PCP.RoundSize

namespace MaxCutGames.Foundations.Hastad.SourceNonempty

open Target PCP

/-- Convert an actual natural-number clause-count inequality to the real
inequality used by the clause-variable game. -/
theorem real_clause_gap_of_count (F : Formula) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.«variables» → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment)
    (assignment : Fin F.«variables» → Bool) :
    (a : ℝ) / (b : ℝ) * F.clauses.length ≤
      (failureCount F assignment (allIndices F) : ℝ) := by
  rw [NameCompaction.verifier_failureCount]
  have hreal : (a : ℝ) * F.clauses.length ≤
      (b : ℝ) * (NameCompaction.failedCount F assignment : ℝ) := by
    exact_mod_cast hgap assignment
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hb)).mpr
  simpa only [mul_comm] using hreal

theorem clauseGap_of_count (F : Formula) (a b : ℕ) (hne : F.clauses ≠ [])
    (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.«variables» → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment) :
    SourceGap.ClauseGap F ((a : ℚ) / (b : ℚ)) := by
  refine ⟨hne, fun assignment => ?_⟩
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    real_clause_gap_of_count F a b hb hgap assignment

variable {V E : Type*} {n m : ℕ}

/-- The actual final graph bundle carries a nonempty dart type, so its
explicitly numbered Boolean CNF is nonempty even before using any gap. -/
theorem cnf_nonempty_of_nonempty_darts [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (FinalBooleanVerifier.cnf G vertices edges).clauses ≠ [] := by
  have hcard : Fintype.card E = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr edges
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  exact FinalBooleanVerifier.cnf_nonempty G vertices edges hm

/-- The checked final Boolean-verifier count bound produces exactly the
nonempty clause-gap premise of SourceGap, with denominator `40960 * b`. -/
theorem cnf_clauseGap [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      a * Fintype.card E ≤ b * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      ((a : ℚ) / ((b : ℚ) * 40960)) := by
  have h := clauseGap_of_count (FinalBooleanVerifier.cnf G vertices edges) a (b * 40960)
    (cnf_nonempty_of_nonempty_darts G vertices edges)
    (Nat.mul_pos hb (by decide)) (FinalBooleanVerifier.cnf_gap G vertices edges a b hgap)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- The unit-numerator gap supplied by the final powering stage has the
fixed rational clause gap `1 / (40960 * walkLength)`. -/
theorem cnf_clauseGap_unit [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (walkLength : ℕ)
    (hwalk : 0 < walkLength)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      Fintype.card E ≤ walkLength * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      (1 / (40960 * (walkLength : ℚ))) := by
  have h := cnf_clauseGap G vertices edges 1 walkLength hwalk
    (by simpa only [one_mul] using hgap)
  simpa only [Nat.cast_one, mul_comm] using h

end MaxCutGames.Foundations.Hastad.SourceNonempty

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.PCPIteration

open FiniteGraph

abbrev Label := AlphabetRetraction.Label64
abbrev Graph := Bundle Label
abbrev Addresses := AmplificationRound.Addresses

def step (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) : Graph := by
  classical
  exact Bundle.ofGraph (AmplificationRound.graph addresses complete G.graph)

def run (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) : Nat → Graph → Graph :=
  AmplificationIteration.run (step addresses complete)

def initial (F : Target.Formula) : Graph := Bundle.ofGraph (AlphabetRetraction.initial64 F)

def iterationCount (F : Target.Formula) : Nat := AmplificationIteration.rounds (initial F).size

def output (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) : Graph := run addresses complete (iterationCount F) (initial F)

/-- Fixed exponent; the enormous fixed graph constants remain unevaluated. -/
def polynomialDegree : Nat := AmplificationIteration.rounds RoundSize.sizeFactor

def finalClauseGap : ℚ := 1 / (40960 * (FinalConstants.walkLength : ℚ))

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

theorem sizeFactor_le_power : RoundSize.sizeFactor ≤ 2 ^ polynomialDegree :=
  (AmplificationIteration.rounds_large RoundSize.sizeFactor).le

theorem initial_satisfiable_iff (F : Target.Formula) :
    (initial F).Satisfiable ↔ F.Satisfiable :=
  AlphabetRetraction.initial64_satisfiable_iff F

theorem initial_size_positive (F : Target.Formula) : 0 < (initial F).size :=
  (initial F).size_positive

theorem initial_size_bound (F : Target.Formula) :
    (initial F).size ≤ 10 * F.clauses.length + 2 := by
  change Fintype.card (InitialGraph.CompactVertex F) +
    Fintype.card (InitialGraph.CompactDart F) ≤ _
  rw [InitialGraph.build_dart_count]
  have h := InitialGraph.build_vertex_bound F
  omega

theorem step_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : Graph) (satisfied : G.Satisfiable) : (step addresses complete G).Satisfiable :=
  AmplificationRound.completeness addresses complete G.graph satisfied

theorem step_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) :
    min (2 * G.gap) FinalConstants.cap ≤ (step addresses complete G).gap :=
  RoundGap.amplifies addresses complete G.graph

theorem step_size (addresses : List Addresses) (complete : ∀ w, w ∈ addresses) (G : Graph) :
    (step addresses complete G).size ≤ RoundSize.sizeFactor * G.size :=
  RoundSize.output_total_le G.graph

theorem run_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) (satisfied : G.Satisfiable) :
    (run addresses complete n G).Satisfiable :=
  AmplificationIteration.run_preserves (step addresses complete) Bundle.Satisfiable
    (step_completeness addresses complete) n G satisfied

theorem run_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) :
    min (2 ^ n * G.gap) FinalConstants.cap ≤ (run addresses complete n G).gap :=
  AmplificationIteration.run_gap (step addresses complete) Bundle.gap
    FinalConstants.cap FinalConstants.cap_positive.le (step_gap addresses complete) n G

theorem run_size (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (n : Nat) (G : Graph) :
    (run addresses complete n G).size ≤ RoundSize.sizeFactor ^ n * G.size :=
  AmplificationIteration.run_size (step addresses complete) Bundle.size RoundSize.sizeFactor
    (step_size addresses complete) n G

theorem output_completeness (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (satisfied : F.Satisfiable) :
    (output addresses complete F).Satisfiable :=
  run_completeness addresses complete (iterationCount F) (initial F)
    ((initial_satisfiable_iff F).mpr satisfied)

/-- The actual graph reaches the fixed positive gap after the concrete number
of rounds determined by its initial total size. -/
theorem output_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ (output addresses complete F).gap := by
  have hinitial : ¬ (initial F).Satisfiable :=
    fun h => unsat ((initial_satisfiable_iff F).mp h)
  exact AmplificationIteration.run_reaches_cap (step addresses complete) Bundle.gap
    FinalConstants.cap FinalConstants.cap_positive.le FinalConstants.cap_le_one
    (step_gap addresses complete) (initial F).size (initial F)
    (initial F).gap_nonnegative ((initial F).one_le_size_mul_gap hinitial)

theorem output_satisfiable_iff (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) : (output addresses complete F).Satisfiable ↔ F.Satisfiable := by
  constructor
  · intro satisfied
    by_contra unsat
    have hgap := output_gap addresses complete F unsat
    rw [(output addresses complete F).gap_eq_zero_iff.mpr satisfied] at hgap
    exact (not_le_of_gt FinalConstants.cap_positive) hgap
  · exact output_completeness addresses complete F

theorem output_size_polynomial (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) :
    (output addresses complete F).size ≤
      (2 * (initial F).size) ^ polynomialDegree * (initial F).size :=
  AmplificationIteration.run_size_polynomial (step addresses complete) Bundle.size
    (initial_size_positive F) sizeFactor_le_power (step_size addresses complete) (initial F)

theorem output_size_clause_bound (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) :
    (output addresses complete F).size ≤
      (2 * (10 * F.clauses.length + 2)) ^ polynomialDegree * (10 * F.clauses.length + 2) := by
  have h := initial_size_bound F
  exact (output_size_polynomial addresses complete F).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 h) _) h)

theorem output_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (F : Target.Formula) (unsat : ¬ F.Satisfiable)
    (labeling : (output addresses complete F).Vertex → Label) :
    Fintype.card (output addresses complete F).Dart ≤
      FinalConstants.walkLength * (output addresses complete F).rejectionCount labeling := by
  have h := ((output addresses complete F).le_gap_iff FinalConstants.cap).mp
    (output_gap addresses complete F unsat) labeling
  have ht : (0 : ℝ) < FinalConstants.walkLength := by
    exact_mod_cast FinalConstants.walkLength_positive
  have h' : (Fintype.card (output addresses complete F).Dart : ℝ) /
      FinalConstants.walkLength ≤
      ((output addresses complete F).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using h
  have h'' := (div_le_iff₀ ht).mp h'
  exact_mod_cast (show (Fintype.card (output addresses complete F).Dart : ℝ) ≤
    (FinalConstants.walkLength : ℝ) *
      ((output addresses complete F).rejectionCount labeling : ℝ) by
        simpa only [mul_comm] using h'')

variable (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
  (F : Target.Formula) {n m : Nat}
  (vertices : (output addresses complete F).Vertex ≃ Fin n)
  (darts : (output addresses complete F).Dart ≃ Fin m)

def finalCNF : Target.Formula :=
  FinalBooleanVerifier.cnf (output addresses complete F).graph vertices darts

theorem finalCNF_satisfiable_iff :
    (finalCNF addresses complete F vertices darts).Satisfiable ↔ F.Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff _ vertices darts).trans
    (output_satisfiable_iff addresses complete F)

theorem finalCNF_clause_count :
    (finalCNF addresses complete F vertices darts).clauses.length = m * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ vertices darts

theorem finalCNF_variable_count :
    (finalCNF addresses complete F vertices darts).«variables» = n * 6 + m * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ vertices darts

theorem finalCNF_nonempty : (finalCNF addresses complete F vertices darts).clauses ≠ [] := by
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hpositive : 0 < m := hm ▸ (Fintype.card_pos :
    0 < Fintype.card (output addresses complete F).Dart)
  exact FinalBooleanVerifier.cnf_nonempty _ vertices darts hpositive

theorem finalCNF_gap (unsat : ¬ F.Satisfiable)
    (assignment : Fin (finalCNF addresses complete F vertices darts).«variables» → Bool) :
    (finalCNF addresses complete F vertices darts).clauses.length ≤
      (FinalConstants.walkLength * 40960) *
        NameCompaction.failedCount (finalCNF addresses complete F vertices darts) assignment := by
  have source (labeling : (output addresses complete F).Vertex → Label) :
      1 * Fintype.card (output addresses complete F).Dart ≤
        FinalConstants.walkLength * (output addresses complete F).graph.rejectionCount labeling := by
    simpa only [one_mul, Bundle.rejectionCount] using output_count_gap addresses complete F unsat labeling
  simpa only [one_mul, finalCNF] using FinalBooleanVerifier.cnf_gap
    (output addresses complete F).graph vertices darts 1 FinalConstants.walkLength source assignment

theorem finalCNF_clauseGap (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (finalCNF addresses complete F vertices darts) finalClauseGap :=
  Hastad.SourceNonempty.cnf_clauseGap_unit (output addresses complete F).graph
    vertices darts FinalConstants.walkLength FinalConstants.walkLength_positive
    (output_count_gap addresses complete F unsat)

theorem finalCNF_total_size :
    (finalCNF addresses complete F vertices darts).«variables» +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * (output addresses complete F).size := by
  have hn : Fintype.card (output addresses complete F).Vertex = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr vertices
  have hm : Fintype.card (output addresses complete F).Dart = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr darts
  have hsize : (output addresses complete F).size = n + m := congrArg₂ Nat.add hn hm
  calc
    _ = n * 6 + m * 36864 + m * 40960 :=
      congrArg₂ Nat.add (finalCNF_variable_count addresses complete F vertices darts)
        (finalCNF_clause_count addresses complete F vertices darts)
    _ ≤ 77824 * (n + m) := by omega
    _ = 77824 * (output addresses complete F).size :=
      congrArg (fun k => 77824 * k) hsize.symm

theorem finalCNF_polynomial_size :
    (finalCNF addresses complete F vertices darts).«variables» +
        (finalCNF addresses complete F vertices darts).clauses.length ≤
      77824 * ((2 * (10 * F.clauses.length + 2)) ^ polynomialDegree *
        (10 * F.clauses.length + 2)) :=
  (finalCNF_total_size addresses complete F vertices darts).trans
    (Nat.mul_le_mul_left _ (output_size_clause_bound addresses complete F))

end MaxCutGames.Foundations.PCP.PCPIteration

end

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace MaxCutGames.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem satisfiable_iff (table : GraphTables.Table) :
    (output table).Satisfiable ↔ (GraphTables.semantics table).Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _)).trans
      ((GraphTables.semantics table).satisfiable_reindex (Equiv.refl _) (Equiv.refl _)
        FinalCNFPattern.labelEquiv.symm)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).«variables» = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

theorem nonempty (table : GraphTables.Table) (hd : 0 < table.darts) :
    (output table).clauses ≠ [] :=
  FinalBooleanVerifier.cnf_nonempty _ (Equiv.refl _) (Equiv.refl _) hd

/-- Boolean labels and numeric labels have exactly the same rejected darts. -/
theorem tableGraph_rejectionCount (table : GraphTables.Table)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    (FinalCNFPattern.tableGraph table).rejectionCount labeling =
      (GraphTables.semantics table).rejectionCount
        (fun v => FinalCNFPattern.labelEquiv (labeling v)) := by
  have h := (GraphTables.semantics table).reindex_rejectionCount
    (Equiv.refl _) (Equiv.refl _) FinalCNFPattern.labelEquiv.symm
    (fun v => FinalCNFPattern.labelEquiv (labeling v))
  simpa [FinalCNFPattern.tableGraph, ConstraintGraph.labelingEquiv] using h

/-- A uniform numeric-label count bound transfers to the machine's Boolean-label graph. -/
theorem tableGraph_count_lower (table : GraphTables.Table) (walkLength : Nat)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ walkLength * (GraphTables.semantics table).rejectionCount labeling)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    Fintype.card (Fin table.darts) ≤
      walkLength * (FinalCNFPattern.tableGraph table).rejectionCount labeling := by
  rw [Fintype.card_fin, tableGraph_rejectionCount]
  exact hgap _

theorem clauseGap (table : GraphTables.Table) (hd : 0 < table.darts)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ FinalConstants.walkLength *
        (GraphTables.semantics table).rejectionCount labeling) :
    Hastad.SourceGap.ClauseGap (output table) PCPIteration.finalClauseGap := by
  let : Nonempty (Fin table.darts) := ⟨⟨0, hd⟩⟩
  exact Hastad.SourceNonempty.cnf_clauseGap_unit (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _) FinalConstants.walkLength
    FinalConstants.walkLength_positive (tableGraph_count_lower table _ hgap)

theorem total_size_le (table : GraphTables.Table) :
    (output table).«variables» + (output table).clauses.length ≤
      77824 * (table.vertices + table.darts) := by
  have hv := variable_count table
  have hc := clause_count table
  omega

/-- A fixed quadratic in the full serialized input length. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).«variables» ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).«variables» + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end MaxCutGames.Foundations.PCP.FinalTableFormula

end OAI
