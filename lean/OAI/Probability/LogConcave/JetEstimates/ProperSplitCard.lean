import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ProperSplit
import OAI.Probability.LogConcave.Sampling.NaturalMomentNorm

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

lemma properSplit_card_le : Fintype.card (ProperSplit S) ≤ 2^Fintype.card S := by
  calc
    _ ≤ Fintype.card (S → Bool) := Fintype.card_subtype_le _
    _ = _ := by simp

lemma measurable_splitMatrix_norm {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → (S → Fin d) → ℝ) (hT : ∀c,Measurable (fun x => T x c))
    (p : ProperSplit S) : Measurable (fun x => ‖splitMatrix (T x) p‖) := by
  let : MeasurableSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (MeasurableSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  have : BorelSpace (Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ) :=
    inferInstanceAs (BorelSpace ((OutSlots p → Fin d) → (InSlots p → Fin d) → ℝ))
  apply Measurable.norm
  exact Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => hT _))

lemma moment_splitEnvelope {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Ω → (S → Fin d) → ℝ) (hT : ∀c,Measurable (fun x => T x c))
    {n : ℕ} (hn : 0<n) (B : ℝ≥0∞)
    (hB : ∀p : ProperSplit S,
      (∫⁻x,ENNReal.ofReal ‖splitMatrix (T x) p‖^n ∂μ) ≤ B^n) :
    (∫⁻x,ENNReal.ofReal (splitEnvelope (T x))^n ∂μ) ≤
      ((2:ℝ≥0∞)^Fintype.card S*B)^n := by
  have hh := natural_moment_sum (μ:=μ) (fun p : ProperSplit S => fun x => ‖splitMatrix (T x) p‖)
    (fun p => (measurable_splitMatrix_norm T hT p).aestronglyMeasurable)
    (fun _ _ => norm_nonneg _) hn (fun _ => B) hB
  apply hh.trans
  apply pow_le_pow_left'
  simpa using mul_le_mul'
    (show (Fintype.card (ProperSplit S):ℝ≥0∞) ≤ 2^Fintype.card S by
      exact_mod_cast properSplit_card_le (S:=S)) (le_refl B)

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
