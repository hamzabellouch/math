import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.AmplificationIteration
import OAI.Combinatorics.IndependentSets.PCP.RoundGap

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.PCPIteration

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

end IndependentSetsGames.Foundations.PCP.PCPIteration
end

end OAI
