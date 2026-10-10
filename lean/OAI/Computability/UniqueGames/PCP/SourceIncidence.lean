import OAI.Computability.UniqueGames.Decoding.IncidenceGap
import OAI.Computability.UniqueGames.PCP.Clone100
import OAI.Computability.UniqueGames.PCP.TableGapReductionLemmas
import OAI.Computability.UniqueGames.Reduction.ActualGame

namespace OAI

section

namespace UniqueGamesTheorem.Outer.SourceIncidence

open UniqueGamesTheorem.Reduction ActualSource
open UniqueGamesTheorem.Foundations Games Target PCP
open UniqueGamesTheorem.Soundness.IncidenceExtraction
open UniqueGamesTheorem.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

def incidence (S : Source) : Incidence (Fin S.occurrences) (Fin S.variables) where
  name := ActualGame.names S
  rhs i := (S.equation i).rhs

theorem names_distinct (S : Source) (hS : S.DistinctNames) :
    ∀ o i j, (incidence S).name o i = (incidence S).name o j → i = j := by
  intro o i j hij
  obtain ⟨h12, h13, h23⟩ := hS o
  fin_cases i <;> fin_cases j <;>
    simp_all [incidence, ActualGame.names, eq_comm]

private theorem uniform_probability_eq_expect {n : Nat} [Nonempty (Fin n)]
    (p : Fin n → Bool) :
    (FiniteDistribution.uniform (Fin n)).probability p =
      (Finset.univ.expect (fun i => if p i then (1 : ℚ) else 0) : ℚ) := by
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform, Fintype.card_fin]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  cases p i <;> simp

theorem paritySuccess_eq (S : Source) (a : Fin S.variables → Bool) :
    paritySuccess (incidence S) (FiniteDistribution.uniform (Fin S.occurrences)) a =
      (((S.sourceList.countP (fun e => CloneGap.satisfied e a) : ℚ) /
        S.occurrences : ℚ) : ℝ) := by
  unfold paritySuccess
  rw [uniform_probability_eq_expect]
  have hevent (o : Fin S.occurrences) :
      decide (xorTriple (fun i => a ((incidence S).name o i)) = (incidence S).rhs o) =
        S.satisfied a o := by
    have hb : ∀ x y : Bool, decide (x = y) = (x == y) := by decide
    exact hb _ _
  simp_rw [hevent]
  rw [IncidenceProbability.expect_bool_indicator_eq_count_ofFn]
  congr 2
  have hm : List.ofFn (S.satisfied a) =
      S.sourceList.map (fun e => CloneGap.satisfied e a) := by
    simp [Source.sourceList, List.map_ofFn, Function.comp_def]
    rfl
  simp [hm, List.countP_map]

theorem paritySuccess_input (input : SourceEncoding.Input)
    (a : Fin input.variables → Bool) :
    paritySuccess (incidence (HastadSource.asSource input))
      (FiniteDistribution.uniform (Fin (HastadSource.asSource input).occurrences)) a =
      (Clone100.success input.equations a : ℝ) := by
  have h := paritySuccess_eq (HastadSource.asSource input) a
  rw [show (HastadSource.asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

def input (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  Clone100.clonedInput (HastadSource.output H ξ hξ F)

def source (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : Source := HastadSource.asSource (input H ξ hξ F)

theorem source_distinct (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : (source H ξ hξ F).DistinctNames :=
  Clone100.clonedSource_distinct (HastadSource.output H ξ hξ F)

theorem source_complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ a, 1 - (ξ : ℝ) ≤ paritySuccess (incidence (source H ξ hξ F))
      (FiniteDistribution.uniform (Fin (source H ξ hξ F).occurrences)) a := by
  obtain ⟨a, ha⟩ := HastadSource.complete H ξ hξ F hF
  refine ⟨Clone100.lift a, ?_⟩
  have hvalue : 1 - ξ ≤ Clone100.success (input H ξ hξ F).equations
      (Clone100.lift a) := by
    change 1 - ξ ≤ Clone100.success
      (Clone100.clonedInput (HastadSource.output H ξ hξ F)).equations (Clone100.lift a)
    rw [Clone100.completeness]
    exact ha
  have hreal : 1 - (ξ : ℝ) ≤
      (Clone100.success (input H ξ hξ F).equations (Clone100.lift a) : ℝ) := by
    exact_mod_cast hvalue
  exact hreal.trans_eq (paritySuccess_input (input H ξ hξ F) (Clone100.lift a)).symm

theorem source_sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (hξsmall : ξ < 1 / 100)
    (F : Formula) (hF : ¬ F.Satisfiable) :
    parityValue (incidence (source H ξ hξ F))
      (FiniteDistribution.uniform (Fin (source H ξ hξ F).occurrences)) ≤ 4 / 5 := by
  unfold parityValue
  apply Finset.sup'_le
  intro a _
  have h := Clone100.soundness_four_fifths (HastadSource.output H ξ hξ F) ξ hξsmall
    (HastadSource.sound H certificate ξ hξ F hF) a
  have hq : Clone100.success (input H ξ hξ F).equations a ≤ (4 / 5 : ℚ) := h
  have hreal : (Clone100.success (input H ξ hξ F).equations a : ℝ) ≤ 4 / 5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr hq)
  exact (paritySuccess_input (input H ξ hξ F) a).trans_le hreal

def ordinaryGame (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) (F : Formula) :=
  fourAnswerGame (incidence (source H ξ hξ F))
    (FiniteDistribution.uniform (Fin (source H ξ hξ F).occurrences))

theorem ordinaryGame_projection (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : UniqueGamesTheorem.Repetition.IsProjection (ordinaryGame H ξ hξ F) :=
  fourAnswerGame_isProjection _ _ (names_distinct _ (source_distinct H ξ hξ F))

theorem ordinaryGame_sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (hξsmall : ξ < 1 / 100)
    (F : Formula) (hF : ¬ F.Satisfiable) :
    (ordinaryGame H ξ hξ F).value ≤ 14 / 15 :=
  fourAnswerGame_value_le_fourteen_fifteenths _ _
    (names_distinct _ (source_distinct H ξ hξ F))
    (source_sound H certificate ξ hξ hξsmall F hF)

end
end UniqueGamesTheorem.Outer.SourceIncidence

end

end OAI
