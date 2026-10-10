import Mathlib
import OAI.Computability.MinUncut.Estimates.Bridge
import OAI.Computability.MinUncut.Machines.MachineBinaryRenameMachine

namespace OAI

section
noncomputable section
namespace MinUncut.SourceBridge
open MinUncutGames MinUncutGames.Reduction MinUncutGames.Foundations
open MinUncutGames.Foundations.Complexity
open Outer MinUncut.Inner

structure BinaryReduction (ξ : ℚ) where
  reduce : BinaryFormula.Formula → SourceEncoding.Input
  complete : ∀ F, F.Satisfiable → ∃ bits, 1-ξ≤Outer.HastadSource.success (reduce F) bits
  sound : ∀ F, ¬F.Satisfiable → ∀ bits, Outer.HastadSource.success (reduce F) bits≤(1+ξ)/2
  computation : Turing.TM2ComputableInPolyTime BinaryEncoding.formulaBits SourceEncoding.inputBits reduce
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm

def binaryReduction {ξ : ℚ} (R : Outer.HastadSource.Reduction ξ) : BinaryReduction ξ where
  reduce F := R.reduce (BinaryOccurrenceRename.renamed F)
  complete F hF := R.completeness _ ((BinaryOccurrenceRename.renamed_satisfiable_iff F).mpr hF)
  sound F hF := R.soundness _ (fun h => hF ((BinaryOccurrenceRename.renamed_satisfiable_iff F).mp h))
  computation := MachineSequential.composeBits BinaryRenameMachine.computableInPolyTime R.computation
  finiteAlphabet := MachineFiniteAlphabet.composeBits _ _
    BinaryRenameMachine.computation_finiteAlphabet R.finiteAlphabet

lemma binaryReduction_exists {ξ : ℚ} (hξ : 0<ξ) : Nonempty (BinaryReduction ξ) := by
  obtain ⟨R⟩ := Outer.HastadSource.exists_reduction ξ hξ
  exact ⟨binaryReduction R⟩

lemma binaryReduction_sound {ξ : ℚ} (hξ : ξ≤1/2) (R : BinaryReduction ξ)
    (F : BinaryFormula.Formula) (hF : ¬F.Satisfiable) (s : Fin (R.reduce F).«variables» → F₂) :
    equationFraction (equations (R.reduce F)) s≤3/4 := by
  rw [fraction_eq_assignment]
  have hh : (Outer.HastadSource.success (R.reduce F) (fun x => fieldBool (s x)):ℝ)≤
      ((1+ξ)/2:ℚ) := Rat.cast_le.mpr (R.sound F hF _)
  have hξ' : (ξ:ℝ)≤1/2 := by
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le.mpr hξ : (ξ:ℝ)≤((1/2:ℚ):ℝ))
  push_cast at hh
  linarith

lemma binaryReduction_complete {ξ : ℚ} (R : BinaryReduction ξ)
    (F : BinaryFormula.Formula) (hF : F.Satisfiable) (t : ℕ) (b : ℝ)
    (hξ : (t:ℝ)*(ξ:ℝ)≤b) :
    ∃ s : Fin (R.reduce F).«variables» → F₂,
      (t:ℝ)*(1-equationFraction (equations (R.reduce F)) s)≤b := by
  obtain ⟨bits,hb⟩ := R.complete F hF
  refine ⟨fun x => boolField (bits x),?_⟩
  rw [fraction_eq]
  have hb' : 1-(ξ:ℝ)≤(Outer.HastadSource.success (R.reduce F) bits:ℝ) := by exact_mod_cast hb
  exact (mul_le_mul_of_nonneg_left (by linarith :
    1-(Outer.HastadSource.success (R.reduce F) bits:ℝ)≤(ξ:ℝ)) (Nat.cast_nonneg t)).trans hξ
end MinUncut.SourceBridge

end
end

end OAI
