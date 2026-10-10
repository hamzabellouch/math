import OAI.Computability.PerfectCompleteness.Construction.FlexibleLocalCompletionLemmas
import OAI.Computability.PerfectCompleteness.Machines.EncodingLemmas
import OAI.Computability.PerfectCompleteness.Machines.LocalCompletionMachineLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CanonicalGameLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionOutputLemmas

namespace OAI

section

namespace PerfectCompleteness.LocalCompletionOutput

open scoped BigOperators Classical
open Turing
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness WeightRounding

noncomputable section

variable {m l r q : Nat} {L : Fin l → Type*} {R : Fin r → Type*}
  [∀ x, Fintype (L x)]
  (G : LegalProjectionGame (Fin m) (Fin l) (Fin r) L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)
  (defaultL : ∀ x, L x) (hq : 0 < q)
  (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)

def construct (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ) : Instance q :=
  CompletionRounding.output w
    (LocalCompletionGame.family G legalL legalR defaultL hq hsmall) δ hδ

def local_machine_output (e : Fin m) :
    TM2OutputsInTime (LocalCompletionMachine.computation hq).tm
      (LocalCompletionMachine.inputBits (LocalCompletionGame.input G legalL legalR defaultL e))
      (some (LocalCompletionMachine.resultBits
        (LocalCompletionGame.result G legalL legalR defaultL hq e))) 1 := by
  have h := (LocalCompletionMachine.computation hq).outputsFun
    (LocalCompletionGame.input G legalL legalR defaultL e)
  change TM2OutputsInTime (LocalCompletionMachine.computation hq).tm
    ((LocalCompletionMachine.inputBits
      (LocalCompletionGame.input G legalL legalR defaultL e)).map id)
    (some ((LocalCompletionMachine.resultBits
      (LocalCompletionGame.result G legalL legalR defaultL hq e)).map id))
    ((1 : Polynomial Nat).eval _) at h
  rw [Polynomial.eval_one] at h
  exact Eq.mp (congrArg₂
    (fun (i o : List Bool) => TM2OutputsInTime (LocalCompletionMachine.computation hq).tm
      i (some o) 1)
    (List.map_id (LocalCompletionMachine.inputBits
      (LocalCompletionGame.input G legalL legalR defaultL e)))
    (List.map_id (LocalCompletionMachine.resultBits
      (LocalCompletionGame.result G legalL legalR defaultL hq e)))) h

theorem total_active_seeds_le :
    (∑ e, (LocalCompletionGame.family G legalL legalR defaultL hq hsmall).size e) ≤
      m * (2 * q) := by
  calc
    _ ≤ ∑ _e : Fin m, 2 * q := by
      apply Finset.sum_le_sum
      intro e _
      exact LocalCompletionGame.family_size_le G legalL legalR defaultL hq hsmall e
    _ = m * (2 * q) := by simp

theorem edge_count (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ) :
    (construct G legalL legalR defaultL hq hsmall w δ hδ).edges.length ≤
      ⌈(3 : ℚ) / δ⌉₊ * m * (2 * q) := by
  exact (CompletionRounding.output_edge_count_le w
    (LocalCompletionGame.family G legalL legalR defaultL hq hsmall) δ hδ).trans
      (by
        have h := Nat.mul_le_mul_left (⌈(3 : ℚ) / δ⌉₊)
          (total_active_seeds_le G legalL legalR defaultL hq hsmall)
        simpa only [Nat.mul_assoc] using h)

theorem bit_count (w : PositiveWeights m) (δ : ℚ) (hδ : 0 < δ) :
    let M := ⌈(3 : ℚ) / δ⌉₊ * m * (2 * q)
    (Encoding.gameBits (construct G legalL legalR defaultL hq hsmall w δ hδ)).length ≤
      l + r + q + M + 4 + M * (l + r + 2 * q * q + 2 * q + 2) := by
  exact Encoding.gameBits_length_le_of_edge_count _ _
    (edge_count G legalL legalR defaultL hq hsmall w δ hδ)

section Values
variable [∀ y, Fintype (R y)] [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]

theorem value_le (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) :
    (construct G legalL legalR defaultL hq hsmall w δ hδ).value ≤
      G.value + G.occurrences.expectation
        (fun e => 2 / (2 * q - Fintype.card (L (G.left e)) : Nat)) + (δ : ℝ) / 3 :=
  CompletionRounding.output_value_le w
    (LocalCompletionGame.family G legalL legalR defaultL hq hsmall) hweights δ hδ hq

theorem value_le_delta (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hleft : ∀ x, Fintype.card (L x) ≤ q)
    (hbudget : (6 : ℝ) ≤ (δ : ℝ) * q) (hsound : G.value ≤ (δ : ℝ) / 3) :
    (construct G legalL legalR defaultL hq hsmall w δ hδ).value ≤ (δ : ℝ) := by
  have hδreal : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hres : ∀ e, 2 / (2 * q - Fintype.card (L (G.left e)) : Nat) ≤ (δ : ℝ) / 3 :=
    fun e => CompletionParameters.residual_le_third hq (hleft (G.left e)) hδreal hbudget
  have h := CompletionRounding.output_value_le_of_residual_bound w
    (LocalCompletionGame.family G legalL legalR defaultL hq hsmall)
    hweights δ hδ hq ((δ : ℝ) / 3) hres
  change (construct G legalL legalR defaultL hq hsmall w δ hδ).value ≤
    G.value + (δ : ℝ) / 3 + (δ : ℝ) / 3 at h
  linarith

theorem perfectlyComplete (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hcomplete : G.value = 1) :
    PerfectlyComplete (construct G legalL legalR defaultL hq hsmall w δ hδ) := by
  apply ((construct G legalL legalR defaultL hq hsmall w δ hδ).perfectlyComplete_iff_value_eq_one hq).2
  exact CompletionRounding.output_value_eq_one w
    (LocalCompletionGame.family G legalL legalR defaultL hq hsmall)
    hweights δ hδ hq hcomplete

end Values
end
end PerfectCompleteness.LocalCompletionOutput

end

end OAI
