import Mathlib.Data.Rat.Cast.Order
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.BinPacking.Configurations.K4Soundness
import OAI.Computability.BinPacking.Configurations.ReductionCompleteness
import OAI.Computability.BinPacking.Machines.GraphPackingOutput
import OAI.Computability.BinPacking.PCP.PCPSourceHardness
import OAI.Computability.BinPacking.Packing.LiteralSlotGap

namespace OAI

noncomputable section

namespace BinPackingGap.PCPFoundation

section

open BinPackingGames.Foundations
open Target
open BinPackingCompleteness

def gap : ℚ := PCPSource.sourceGap

def rho : ℝ := (gap : ℝ) / 6

theorem gap_pos : 0 < gap := PCPSource.sourceGap_pos

theorem gap_cast_pos : (0 : ℝ) < gap := by exact_mod_cast gap_pos

theorem rho_pos : 0 < rho := div_pos gap_cast_pos (by norm_num)

theorem rho_lt_gap_third : rho < (gap : ℝ) / 3 := by
  unfold rho
  nlinarith [gap_cast_pos]

def formula (F : Formula) : Formula := PCPSource.normalizedFormula F

def graph (F : Formula) : GraphInput := LiteralSlotGraph.graph (formula F)

def target (F : Formula) : ℕ := 2 * (formula F).clauses.length

theorem formula_nonempty (F : Formula) : (formula F).clauses ≠ [] :=
  PCPSource.normalizedFormula_nonempty F

theorem clause_count_pos (F : Formula) : 0 < (formula F).clauses.length :=
  List.length_pos_iff.mpr (formula_nonempty F)

theorem edges_nonempty (F : Formula) : (graph F).edges ≠ [] :=
  LiteralSlotGraph.graph_edges_nonempty (formula F) (formula_nonempty F)

theorem target_le_vertices (F : Formula) : target F ≤ (graph F).n := by
  change 2 * (formula F).clauses.length ≤ 3 * (formula F).clauses.length
  omega

theorem cover_complete (F : Formula) (hF : F.Satisfiable) :
    (graph F).CoverAtMost (target F) :=
  LiteralSlotGraph.coverAtMost_of_satisfiable (formula F)
    ((PCPSource.normalizedFormula_satisfiable_iff F).mpr hF)

theorem failedCount_eq_card (F : Formula) (A : Fin F.variables → Bool) :
    PCP.NameCompaction.failedCount F A = (LiteralSlotGraph.failedClauses F A).card := by
  rw [PCPSource.failedCount_eq_fin_sum]
  simpa only [PCP.clauseAt, Fin.getElem_fin] using! (LiteralSlotGraph.failedClauses_card_sum F A).symm

private theorem realGapOfRatGap (q : ℚ) (m n : ℕ)
    (h : q * (m : ℚ) ≤ (n : ℚ)) : (q : ℝ) * (m : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast h

private theorem realCountBound (a b c : ℕ) (h : a + b ≤ c) :
    (a : ℝ) + (b : ℝ) ≤ (c : ℝ) := by
  exact_mod_cast h

theorem normalized_failed_gap (F : Formula) (hF : ¬ F.Satisfiable)
    (A : Fin (PCPSource.normalizedFormula F).variables → Bool) :
    PCPSource.sourceGap * ((PCPSource.normalizedFormula F).clauses.length : ℚ) ≤
      ((LiteralSlotGraph.failedClauses (PCPSource.normalizedFormula F) A).card : ℚ) := by
  have bound := PCPSource.clauseGap F hF A
  rw [PCPSource.violatedCount_eq_failedCount F A, failedCount_eq_card] at bound
  exact bound

private theorem cover_bound_from_failed_gap (G : Formula) (q : ℚ)
    (bound : ∀ A : Fin G.variables → Bool,
      q * (G.clauses.length : ℚ) ≤ ((LiteralSlotGraph.failedClauses G A).card : ℚ))
    (C : Finset (LiteralSlotGraph.graph G).Vertex)
    (hC : (LiteralSlotGraph.graph G).IsCover C) :
    ((2 * G.clauses.length : ℕ) : ℝ) + (q : ℝ) * (G.clauses.length : ℝ) ≤
      (C.card : ℝ) := by
  obtain ⟨A, hA⟩ := LiteralSlotGraph.assignment_count_of_cover G C hC
  have hgap := realGapOfRatGap q G.clauses.length _ (bound A)
  have hcount := realCountBound (2 * G.clauses.length)
    (LiteralSlotGraph.failedClauses G A).card C.card hA
  linarith only [hgap, hcount]

theorem cover_sound (F : Formula) (hF : ¬ F.Satisfiable)
    (C : Finset (graph F).Vertex) (hC : (graph F).IsCover C) :
    (target F : ℝ) + (gap : ℝ) * ((formula F).clauses.length : ℝ) ≤ (C.card : ℝ) :=
  cover_bound_from_failed_gap (formula F) gap (normalized_failed_gap F hF) C hC

theorem no_small_cover (F : Formula) (hF : ¬ F.Satisfiable)
    (C : Finset (graph F).Vertex) (hC : (graph F).IsCover C) :
    ¬ (C.card : ℝ) ≤ (target F : ℝ) + rho * ((graph F).n : ℝ) := by
  intro hsmall
  have hlarge := cover_sound F hF C hC
  have hm : (0 : ℝ) < (formula F).clauses.length := by
    exact_mod_cast clause_count_pos F
  have hn : ((graph F).n : ℝ) = 3 * ((formula F).clauses.length : ℝ) := by
    norm_num [graph, LiteralSlotGraph.graph_n]
  rw [hn] at hsmall
  unfold rho at hsmall
  nlinarith [mul_pos gap_cast_pos hm]

theorem normalizedSource (language : List Bool → Prop)
    (membership : Complexity.CookLevin.InNP language) :
    ∃ source : Complexity.CookLevin.PolynomialThreeSATReduction language,
    ∃ runtime : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
        Complexity.formulaBits (PCPSourceHardness.formula source),
      Complexity.MachineFiniteAlphabet.FiniteAlphabet runtime.tm ∧
      ∀ input : List Bool,
        ((PCPSourceHardness.formula source input).Satisfiable ↔ language input) ∧
        (PCPSourceHardness.formula source input).clauses ≠ [] ∧
        (∀ (clause : Clause (PCPSourceHardness.formula source input).variables),
          clause ∈ (PCPSourceHardness.formula source input).clauses →
          ∀ i j : Fin 3, clause[i].variableIndex = clause[j].variableIndex → i = j) ∧
        (¬ language input →
          SourceAmplification.ClauseGap (PCPSource.clauseFamily (source.reduce input))
            PCPSource.sourceGap) :=
  PCPSourceHardness.normalizedSource language membership

end

open BinPackingGames.Foundations.Target

def graphInput (F : Formula) : GraphReductionInput where
  graph := graph F
  k := target F
  k_le := target_le_vertices F
  nonempty := edges_nonempty F

def packingOutput (c : Nat) (F : Formula) : RawReductionOutput :=
  graphPackingOutput c rho (graphInput F)

theorem packingOutput_valid (c : Nat) (F : Formula) :
    (packingOutput c F).2.Valid :=
  graphPackingOutput_valid c rho (graphInput F)

theorem packingOutput_count (c : Nat) (F : Formula) :
    (packingOutput c F).2.length = 5 * (packingOutput c F).1 :=
  graphPackingOutput_length c rho (graphInput F)

theorem packingOutput_size_lower (c : Nat) (F : Formula)
    (i : ((packingOutput c F).2.toInstance (packingOutput_valid c F)).Item) :
    (1 / 6 : ℚ) < ((packingOutput c F).2.toInstance (packingOutput_valid c F)).size i :=
  (graphPackingOutput_size_bounds c rho (graphInput F) i).1

theorem packingOutput_complete (c : Nat) (F : Formula) (hF : F.Satisfiable) :
    HasPacking ((packingOutput c F).2.toInstance (packingOutput_valid c F))
      (packingOutput c F).1 := by
  apply (graphPackingOutput_hasPacking_iff c rho (graphInput F) _).mpr
  exact cover_hasPacking_reduction c rho (graph F) (target F)
    (target_le_vertices F) (cover_complete F hF)

theorem packingOutput_sound (c : Nat) (F : Formula) (hF : ¬ F.Satisfiable) :
    ¬ HasPacking ((packingOutput c F).2.toInstance (packingOutput_valid c F))
      ((packingOutput c F).1 + c) := by
  intro hp
  obtain ⟨p⟩ := (graphPackingOutput_hasPacking_iff c rho (graphInput F) _).mp hp
  obtain ⟨C, hcover, hsmall⟩ := packing_extracts_cover c rho rho_pos
    (graph F) (target F) (target_le_vertices F) p (Nat.le_refl _)
  exact no_small_cover F hF C hcover hsmall

end BinPackingGap.PCPFoundation

end

end OAI
