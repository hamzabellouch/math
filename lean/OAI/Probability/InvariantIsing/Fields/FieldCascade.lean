import OAI.Probability.InvariantIsing.Fields.CascadeMarking

namespace OAI

/-! The actual finite one-site functional as a Gaussian cascade expectation. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldCascadeVariance (h : FieldStep) (i : ℕ) : ℝ≥0 :=
  NNReal.mk ((IsingPerceptron.pathAmplitude (heightSequence h) (i + 1)) ^ 2)
    (sq_nonneg _)

def fieldCascadeLaw (h : FieldStep) : Measure (IsingPerceptron.NoiseTree ℝ h.depth) :=
  gaussianCascadeLaw h.depth (IsingPerceptron.chainExponent h.cut) (fieldCascadeVariance h)

lemma fieldCascadeFold_eq_magneticRecursion (h : FieldStep) :
    (List.ofFn (fun i : Fin h.depth =>
      (IsingPerceptron.chainExponent h.cut i, (fieldCascadeVariance h i : ℝ)))).foldr
      (fun av U => gaussianOperator av.1 av.2 U) (fun x => Real.log (Real.cosh x)) =
    IsingPerceptron.magneticRecursion h.depth
      (fun i => IsingPerceptron.pathAmplitude (heightSequence h) (i + 1))
      (IsingPerceptron.chainExponent h.cut) := by
  simp_rw [gaussianOperator_eq_transform]
  rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
    (g := fun sd U => IsingPerceptron.gaussianTransform sd.1 sd.2 U), List.map_ofFn]
  simp only [Function.comp_def, fieldCascadeVariance, NNReal.coe_mk]
  exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
    (fun i => IsingPerceptron.pathAmplitude (heightSequence h) (i + 1))
    (IsingPerceptron.chainExponent h.cut)).symm

theorem fieldCascadeLog_recursion (h : FieldStep) (x : ℝ) :
    Integrable (gaussianCascadeLog h.depth x) (fieldCascadeLaw h) ∧
      (∫ T, gaussianCascadeLog h.depth x T ∂fieldCascadeLaw h) =
        IsingPerceptron.magneticRecursion h.depth
          (fun i => IsingPerceptron.pathAmplitude (heightSequence h) (i + 1))
          (IsingPerceptron.chainExponent h.cut) x := by
  have hr := gaussianCascadeLog_recursion h.depth (IsingPerceptron.chainExponent h.cut)
    (fieldCascadeVariance h)
    (IsingPerceptron.chainExponent_admissible h.ordered_cut h.first h.last) x
  rw [fieldCascadeFold_eq_magneticRecursion] at hr
  exact hr

/-- The finite one-site entropy value equals the root Gaussian average of
the logarithm of the Gaussian-marked cascade integral, with its prescribed
diagonal covariance subtraction. -/
theorem fieldValue_eq_cascade_expectation (h : FieldStep) :
    fieldValue h 0 =
      (∫ g, (∫ T, gaussianCascadeLog h.depth (Real.sqrt (h.height 0) * g) T
        ∂fieldCascadeLaw h) ∂gaussianReal 0 1) - h.height (Fin.last h.depth) / 2 := by
  rw [fieldValue_eq_magneticFieldValue]
  unfold IsingPerceptron.magneticFieldValue
  have hlast : heightSequence h h.depth = h.height (Fin.last h.depth) :=
    heightSequence_eq h _ le_rfl
  rw [hlast]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with g
  rw [(fieldCascadeLog_recursion h (Real.sqrt (h.height 0) * g)).2]
  have hroot : IsingPerceptron.pathAmplitude (heightSequence h) 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, heightSequence]
  rw [hroot]

end InvariantIsing

end

end OAI
