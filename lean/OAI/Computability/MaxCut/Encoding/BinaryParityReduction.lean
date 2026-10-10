import Mathlib
import OAI.Computability.MaxCut.Machines.MachineBinaryInputReduction

namespace OAI

namespace MaxCutGames.Outer.BinaryParityReduction

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

noncomputable section

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) : SourceEncoding.Input :=
  SourceIncidence.input H ξ hξ (BinaryLanguage.totalRename word)

def formulaMachine (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits
      (SourceIncidence.input H ξ hξ) :=
  MachineSequential.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation

theorem formulaMachine_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (formulaMachine H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation
    (HastadSource.finiteAlphabet H ξ hξ) Explicit.MachineClone100.finiteAlphabet

def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) SourceEncoding.inputBits
      (output H ξ hξ) :=
  MachineSequential.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)

theorem computation_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)
    BinaryInputReduction.computation_finiteAlphabet (formulaMachine_finite H ξ hξ)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) (yes : BinaryLanguage.language word) :
    ∃ a, 1 - ξ ≤ Clone100.success (output H ξ hξ word).equations a := by
  obtain ⟨a, ha⟩ := HastadSource.complete H ξ hξ (BinaryLanguage.totalRename word)
    ((BinaryLanguage.totalRename_satisfiable_iff word).mpr yes)
  refine ⟨Clone100.lift a, ?_⟩
  change 1 - ξ ≤ Clone100.success
    (Clone100.clonedInput (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word))).equations
      (Clone100.lift a)
  rw [Clone100.completeness]
  exact ha

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (small : ξ < 1 / 100)
    (word : List Bool) (no : ¬ BinaryLanguage.language word)
    (a : Fin (output H ξ hξ word).«variables» → Bool) :
    Clone100.success (output H ξ hξ word).equations a ≤ 4 / 5 := by
  have hno : ¬ (BinaryLanguage.totalRename word).Satisfiable :=
    fun h => no ((BinaryLanguage.totalRename_satisfiable_iff word).mp h)
  exact Clone100.soundness_four_fifths
    (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word)) ξ small
    (HastadSource.sound H certificate ξ hξ (BinaryLanguage.totalRename word) hno) a

structure Reduction (ξ : ℚ) where
  reduce : List Bool → SourceEncoding.Input
  distinct : ∀ word, (HastadSource.asSource (reduce word)).DistinctNames
  completeness : ∀ word, BinaryLanguage.language word →
    ∃ a, 1 - ξ ≤ Clone100.success (reduce word).equations a
  soundness : ∀ word, ¬ BinaryLanguage.language word →
    ∀ a, Clone100.success (reduce word).equations a ≤ 4 / 5
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    SourceEncoding.inputBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

theorem exists_reduction (ξ : ℚ) (positive : 0 < ξ) (small : ξ < 1 / 100) :
    Nonempty (Reduction ξ) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  exact ⟨⟨output H ξ positive,
    (fun word => SourceIncidence.source_distinct H ξ positive (BinaryLanguage.totalRename word)),
    complete H ξ positive, sound H certificate ξ positive small,
    computation H ξ positive, computation_finite H ξ positive⟩⟩

theorem failure_completeness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (yes : BinaryLanguage.language word) :
    ∃ a, (HastadSource.asSource (R.reduce word)).failure a ≤ ξ := by
  obtain ⟨a, ha⟩ := R.completeness word yes
  refine ⟨a, ?_⟩
  have hsum := HastadSource.failure_add_success (R.reduce word) a
  change _ + Clone100.success (R.reduce word).equations a = 1 at hsum
  linarith

theorem parity_soundness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (no : ¬ BinaryLanguage.language word) :
    MaxCutGames.Clean.IncidenceGap.parityValue
      (SourceIncidence.incidence (HastadSource.asSource (R.reduce word)))
      (MaxCutGames.Foundations.Games.FiniteDistribution.uniform
        (Fin (HastadSource.asSource (R.reduce word)).occurrences)) ≤ 4 / 5 := by
  unfold MaxCutGames.Clean.IncidenceGap.parityValue
  apply Finset.sup'_le
  intro a _
  have hq := R.soundness word no a
  have hreal : (Clone100.success (R.reduce word).equations a : ℝ) ≤ 4 / 5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr hq)
  exact (SourceIncidence.paritySuccess_input (R.reduce word) a).trans_le hreal

theorem ordinaryGame_soundness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (no : ¬ BinaryLanguage.language word) :
    (MaxCutGames.Clean.IncidenceGap.fourAnswerGame
      (SourceIncidence.incidence (HastadSource.asSource (R.reduce word)))
      (MaxCutGames.Foundations.Games.FiniteDistribution.uniform
        (Fin (HastadSource.asSource (R.reduce word)).occurrences))).value ≤ 14 / 15 :=
  MaxCutGames.Clean.IncidenceGap.fourAnswerGame_value_le_fourteen_fifteenths _ _
    (SourceIncidence.names_distinct _ (R.distinct word)) (parity_soundness R word no)

end
end MaxCutGames.Outer.BinaryParityReduction

end OAI
