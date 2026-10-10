import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.FinalBooleanVerifier
import OAI.Combinatorics.IndependentSets.Fourier.NumberedStorage
import OAI.Combinatorics.IndependentSets.Encoding.Bounds
import OAI.Combinatorics.IndependentSets.Reduction.Parameters

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceOccurrences SourceGame
open IndependentSetsGames.Integration.SourceParameters
open IndependentSetsGames.Reduction

def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.«variables» → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

theorem third_pos {η : ℚ} (hη : 0 < η) : 0 < η / 3 := by positivity

theorem third_le_one {η : ℚ} (hη : η ≤ 1) : η / 3 ≤ 1 := by linarith

def repetitionCount (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) : ℕ :=
  repetitionLength (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD

theorem repetitionCount_pos (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hξ : 0 < ξ) (D : ℕ) (hD : 0 < D) :
    0 < repetitionCount η ξ hη hη1 hξ D hD :=
  (repetitionLength_spec (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD).1

theorem repeated_game_bound (F : Formula) (η ξ : ℚ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) (D : ℕ) (hD : 0 < D)
    (hgap : ClauseGap F η) :
    ((baseGame F hgap.1).repetition
      (repetitionCount η ξ hη hη1 hξ D hD)).value ≤
        4 * (D : ℝ)⁻¹ * (ξ : ℝ)^2 := by
  have hb : (baseGame F hgap.1).value ≤ 1 - ((η / 3 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      base_value_le_of_clause_gap F hgap.1 (η : ℝ) hgap.2
  have hc : Fintype.card Bool * Fintype.card PCP.ClauseAnswer = 16 := by
    simp
  exact (game_repetition_rate (baseGame F hgap.1) (third_pos hη)
    (third_le_one hη1) hc hb _).trans
      (repetitionLength_real_bound (η / 3) ξ (third_pos hη)
        (third_le_one hη1) hξ D hD)

def source (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (F : Formula) : SourceEncoding.Input :=
  sourceInput F (repetitionCount η ξ hη hη1 hξ D hD) D hD

theorem source_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hnoise : (D : ℚ)⁻¹ ≤ ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool,
      1 - ξ ≤ (((source η ξ hη hη1 hξ D hD F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (source η ξ hη hη1 hξ D hD F).equations.length) := by
  obtain ⟨assignment, hs⟩ := hF
  refine ⟨SourceHonest.honestBits F _ assignment, ?_⟩
  have h := SourceHonest.sourceList_honest_acceptance_rat F
    (repetitionCount η ξ hη hη1 hξ D hD) D hD assignment hs
  exact (sub_le_sub_left hnoise 1).trans h

theorem source_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hDtwo : 2 ≤ D)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool) :
    ((source η ξ hη hη1 hξ D hD F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (source η ξ hη hη1 hξ D hD F).equations.length ≤ (1 + ξ) / 2 :=
  SourceSoundness.sourceList_sound_rat F hgap.1
    (repetitionCount η ξ hη hη1 hξ D hD) D hD hDtwo ξ hξ.le
      (repeated_game_bound F η ξ hη hη1 hξ D hD hgap) bits

theorem source_size (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) :
    ∃ p : Polynomial ℕ, ∀ F : Formula,
      (SourceEncoding.inputBits (source η ξ hη hη1 hξ D hD F)).length ≤
        p.eval (Complexity.formulaBits F).length :=
  SourceBounds.fixed_parameters_source_size (repetitionCount η ξ hη hη1 hξ D hD) D hD

end IndependentSetsGames.Foundations.Hastad.SourceGap

namespace IndependentSetsGames.Foundations.Hastad.SourceNonempty

open Target PCP

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

theorem cnf_nonempty_of_nonempty_darts [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (FinalBooleanVerifier.cnf G vertices edges).clauses ≠ [] := by
  have hcard : Fintype.card E = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr edges
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  exact FinalBooleanVerifier.cnf_nonempty G vertices edges hm

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

end IndependentSetsGames.Foundations.Hastad.SourceNonempty

end OAI
