import OAI.Combinatorics.EditApproximation.Probability.RejectionRuntimeLaw
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-! Independent finite arrays of exact rejection executions. The accepted
array has the required product law; all discarded trial words are charged. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Array

variable {ι : Type*} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]

abbrev RejectionArrayExecution := ∀ i, ℕ × Fin (range i)

noncomputable def rejectionArrayCoordinateLaw (i : ι) : Measure (ℕ × Fin (range i)) :=
  rejectionExecutionLaw (range i) (2 ^ rejectionBitCount (range i))
    (Nat.pos_of_ne_zero (NeZero.ne (range i)))
    (rejectionWord_range (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))).1

instance rejectionArrayCoordinateLaw_probability (i : ι) :
    IsProbabilityMeasure (rejectionArrayCoordinateLaw range i) := by
  unfold rejectionArrayCoordinateLaw
  infer_instance

noncomputable def rejectionArrayLaw : Measure (RejectionArrayExecution range) :=
  Measure.pi (rejectionArrayCoordinateLaw range)

instance rejectionArrayLaw_probability : IsProbabilityMeasure (rejectionArrayLaw range) := by
  unfold rejectionArrayLaw
  infer_instance

def rejectionArrayAccepted (execution : RejectionArrayExecution range) : ∀ i, Fin (range i) :=
  fun i => (execution i).2

theorem rejectionArrayLaw_accepted :
    (rejectionArrayLaw range).map (rejectionArrayAccepted range) =
      Measure.pi (fun i => (PMF.uniformOfFintype (Fin (range i))).toMeasure) := by
  have hout (i : ι) : (rejectionArrayCoordinateLaw range i).map
      (Prod.snd : ℕ × Fin (range i) → Fin (range i)) =
        (PMF.uniformOfFintype (Fin (range i))).toMeasure :=
    rejectionExecutionLaw_output _ _ _ _
  let (i : ι) : SigmaFinite ((rejectionArrayCoordinateLaw range i).map
      (Prod.snd : ℕ × Fin (range i) → Fin (range i))) := by
    rw [hout]
    infer_instance
  have h := Measure.pi_map_pi (X := fun i => ℕ × Fin (range i)) (Y := fun i => Fin (range i))
    (f := fun _ => Prod.snd) (μ := rejectionArrayCoordinateLaw range)
    (fun _ => measurable_snd.aemeasurable)
  refine h.trans ?_
  congr 1
  funext i
  exact rejectionExecutionLaw_output _ _ _ _

noncomputable def rejectionArrayConsumedBits (execution : RejectionArrayExecution range) : ℝ :=
  ∑ i, (((execution i).1 : ℝ) + 1) * rejectionBitCount (range i)

omit [Fintype ι] in
theorem rejectionArrayCoordinate_bits_integrable (i : ι) :
    Integrable (fun value : ℕ × Fin (range i) =>
      ((value.1 : ℝ) + 1) * rejectionBitCount (range i)) (rejectionArrayCoordinateLaw range i) :=
  ((rejection_trials_integrable (range i) (2 ^ rejectionBitCount (range i))
    (Nat.pos_of_ne_zero (NeZero.ne (range i)))
    (rejectionWord_range (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))).1).comp_fst
      (PMF.uniformOfFintype (Fin (range i))).toMeasure).mul_const _

theorem rejectionArrayLaw_bits_integrable :
    Integrable (rejectionArrayConsumedBits range) (rejectionArrayLaw range) := by
  unfold rejectionArrayConsumedBits rejectionArrayLaw
  apply integrable_finsetSum
  intro i _
  exact integrable_comp_eval (X := fun i => ℕ × Fin (range i))
    (μ := rejectionArrayCoordinateLaw range) (i := i) (rejectionArrayCoordinate_bits_integrable range i)

theorem rejectionArrayLaw_bits_le :
    (∫ execution, rejectionArrayConsumedBits range execution ∂rejectionArrayLaw range) ≤
      2 * ∑ i, (rejectionBitCount (range i) : ℝ) := by
  unfold rejectionArrayConsumedBits rejectionArrayLaw
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [integral_comp_eval (X := fun i => ℕ × Fin (range i))
      (μ := rejectionArrayCoordinateLaw range) (i := i)
      (f := fun value : ℕ × Fin (range i) => ((value.1 : ℝ) + 1) * rejectionBitCount (range i))
      (rejectionArrayCoordinate_bits_integrable range i).aestronglyMeasurable]
    unfold rejectionArrayCoordinateLaw rejectionExecutionLaw
    rw [integral_fun_fst (ν := (PMF.uniformOfFintype (Fin (range i))).toMeasure)
      (fun failures : ℕ => ((failures : ℝ) + 1) * rejectionBitCount (range i)),
      probReal_univ, one_smul]
    exact rejection_consumed_bits_moment (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))
  · intro i _
    exact integrable_comp_eval (X := fun i => ℕ × Fin (range i))
      (μ := rejectionArrayCoordinateLaw range) (i := i) (rejectionArrayCoordinate_bits_integrable range i)

end Array

end EditApproximation

end OAI
