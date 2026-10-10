import OAI.Probability.InvariantIsing.Fields.Field
import OAI.Probability.IsingPerceptron.VariationalFiniteness

namespace OAI

/-!
# Normalization of the one-site entropy

The finite Gaussian recursion agrees with the Ising recursion.
In particular the zero overlap path has entropy zero. This supplies the exact
variational normalization for a point-mass spectral law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianOperator_eq_transform (a v : ℝ) (f : ℝ → ℝ) :
    gaussianOperator a v f = IsingPerceptron.gaussianTransform v a f := by
  funext z
  simp only [gaussianOperator, IsingPerceptron.gaussianTransform, div_eq_mul_inv]
  split_ifs <;> ring

/-- Extend the last covariance height constantly. -/
def heightSequence (h : FieldStep) (i : ℕ) : ℝ :=
  h.height ⟨min i h.depth, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma heightSequence_mono (h : FieldStep) : Monotone (heightSequence h) := by
  intro i j hij
  apply h.ordered_height
  exact min_le_min_right h.depth hij

lemma heightSequence_nonneg (h : FieldStep) (i : ℕ) : 0 ≤ heightSequence h i :=
  h.nonneg _

lemma heightSequence_eq (h : FieldStep) (i : ℕ) (hi : i ≤ h.depth) :
    heightSequence h i = h.height ⟨i, by omega⟩ := by
  simp only [heightSequence, min_eq_left hi]

/-- Equality with the scalar recursion, including its root Gaussian average
and diagonal covariance subtraction. -/
lemma fieldValue_eq_magneticFieldValue (h : FieldStep) :
    fieldValue h 0 = IsingPerceptron.magneticFieldValue h.depth
      (IsingPerceptron.chainExponent h.cut) (heightSequence h) := by
  let w := heightSequence h
  have hw : Monotone w := heightSequence_mono h
  have hw0 : 0 ≤ w 0 := heightSequence_nonneg h 0
  have htail : List.ofFn (fun i : Fin h.depth =>
      ((fieldIncrement h i.succ).2, (fieldIncrement h i.succ).1)) =
      List.ofFn (fun i : Fin h.depth =>
        ((IsingPerceptron.pathAmplitude w (i + 1)) ^ 2,
          IsingPerceptron.chainExponent h.cut i)) := by
    apply congrArg List.ofFn
    funext i
    rw [IsingPerceptron.pathAmplitude_sq hw hw0]
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false,
      Nat.add_sub_cancel, IsingPerceptron.pathIncrement,
      IsingPerceptron.chainExponent_apply h.cut i.isLt]
    congr 1
    change h.height i.succ - h.height ⟨i.val, by omega⟩ =
      heightSequence h (i.val + 1) - heightSequence h i.val
    rw [heightSequence_eq h _ (by omega), heightSequence_eq h _ (by omega)]
    rfl
  have hfold : (List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)).foldr
      (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z)) =
      IsingPerceptron.magneticRecursion h.depth
        (fun i => IsingPerceptron.pathAmplitude w (i + 1))
        (IsingPerceptron.chainExponent h.cut) := by
    simp_rw [gaussianOperator_eq_transform]
    rw [← List.foldr_map (f := fun av : ℝ × ℝ => (av.2, av.1))
      (g := fun sd f => IsingPerceptron.gaussianTransform sd.1 sd.2 f)]
    rw [List.map_ofFn]
    simp only [Function.comp_def]
    rw [htail]
    exact (IsingPerceptron.magneticRecursion_eq_fold h.depth
      (fun i => IsingPerceptron.pathAmplitude w (i + 1))
      (IsingPerceptron.chainExponent h.cut)).symm
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    dsimp only [fieldIncrement]
    simp [h.first]
  have hzero : w 0 = h.height 0 := heightSequence_eq h 0 (Nat.zero_le _)
  have hlast : w h.depth = h.height (Fin.last h.depth) := heightSequence_eq h _ le_rfl
  have hamp : IsingPerceptron.pathAmplitude w 0 = Real.sqrt (h.height 0) := by
    simp [IsingPerceptron.pathAmplitude, IsingPerceptron.pathIncrement, hzero]
  rw [fieldValue, List.ofFn_succ, List.foldr_cons, hfold, hroot]
  simp only [gaussianOperator, ite_true, zero_add, IsingPerceptron.magneticFieldValue]
  dsimp only [w] at hamp hlast ⊢
  rw [hamp, hlast]

lemma fieldValue_nonpos (h : FieldStep) : fieldValue h 0 ≤ 0 := by
  rw [fieldValue_eq_magneticFieldValue]
  exact IsingPerceptron.magneticFieldValue_nonpos _ _
    (IsingPerceptron.chainExponent_admissible h.ordered_cut h.first h.last)
    (heightSequence_mono h) (heightSequence_nonneg h 0)

lemma entropyFunctional_zero : entropyFunctional (constantPath 0 (by constructor <;> norm_num)) = 0 := by
  apply le_antisymm _ (entropyFunctional_nonneg _)
  apply iSup_le
  intro h
  have hp : fieldPairing (constantPath 0 (by constructor <;> norm_num)) h = 0 := by
    simp [fieldPairing, constantPath]
  simp only [hp, zero_div, add_zero]
  exact_mod_cast fieldValue_nonpos h

lemma variationalFunctional_constant (a : ℝ) :
    variationalFunctional (fun _ => a) = ((a / 2 : ℝ) : EReal) := by
  apply le_antisymm
  · have hi := iInf_le (fun p : OverlapPath =>
      entropyFunctional p + (spectralFunctional (fun _ => a) p : EReal))
      (constantPath 0 (by constructor <;> norm_num))
    simpa only [variationalFunctional, entropyFunctional_zero, spectralFunctional_constant,
      zero_add] using hi
  · apply le_iInf
    intro p
    rw [spectralFunctional_constant]
    simpa only [zero_add] using add_le_add (entropyFunctional_nonneg p)
      (le_rfl : ((a / 2 : ℝ) : EReal) ≤ ((a / 2 : ℝ) : EReal))

end InvariantIsing

end

end OAI
