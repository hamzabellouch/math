import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyBlockTrace

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_nonneg (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (hg : ∀ z, 0 ≤ g z) (j : Fin (n+1)) (z : ParameterSpace n) :
    0 ≤ hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => exact hg z
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using hg z
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      apply ih
      intro x
      exact integral_nonneg (fun y => hg (x,y))

theorem hierarchyMomentLevel_const (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun _ => a) j = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      rw [gaussianAverage_const_prefix hf _ (fun _ => a),ih _ _ (hf.gaussianStep _)]

theorem hierarchyMomentLevel_const_mul (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => a*g z) j = fun z => a*hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => a*g z) =
          fun z => a*gaussianAverage (m (Fin.last n)) f g z := by
        funext z; exact integral_const_mul a _
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he,ih]

theorem hierarchyMomentLevel_sum {T : Type} [Fintype T] (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (g : T → ParameterSpace n → ℝ) (hg : ∀ t, Continuous (g t))
    (C : T → ℝ) (hC : ∀ t, 0 ≤ C t) (hb : ∀ t z, ‖g t z‖ ≤ C t) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => ∑ t, g t z) j =
      fun z => ∑ t, hierarchyMomentLevel n m f (g t) j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => ∑ t, g t z) =
          fun z => ∑ t, gaussianAverage (m (Fin.last n)) f (g t) z := by
        funext z
        let := gaussianStepLaw_probability hf (m (Fin.last n)) z
        apply integral_finsetSum
        intro t _
        exact Integrable.of_bound ((hg t).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          (C t) (ae_of_all _ (fun y => hb t (z,y)))
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he]
      rw [ih _ _ (hf.gaussianStep _) _
        (fun t => gaussianAverage_continuous hf _ (hg t) (hC t) (hb t))
        (fun t z => gaussianAverage_norm_le hf _ (hb t) z) j]

section Probability
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySpinWeight_regular (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (s : S) :
    Continuous (fun z => hierarchySpinWeight n m U j z s) ∧
      ∀ z, ‖hierarchySpinWeight n m U j z s‖ ≤ 1 :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (affineGibbs_continuous (fun _ => 0) U s) (by norm_num) (fun z => affineGibbs_norm_le_one (fun _ => 0) U z s) j

theorem hierarchySpinWeight_nonneg (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) (s : S) : 0 ≤ hierarchySpinWeight n m U j z s :=
  hierarchyMomentLevel_nonneg n m _ _ (fun z => le_of_lt (affineGibbs_pos (fun _ => 0) U z s)) j z

theorem hierarchySpinWeight_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) : ∑ s, hierarchySpinWeight n m U j z s = 1 := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => affineGibbs (fun _ => 0) U z s)
    (affineGibbs_continuous (fun _ => 0) U) (fun _ => 1) (fun _ => by norm_num)
    (fun s z => affineGibbs_norm_le_one (fun _ => 0) U z s) j
  have he : (fun z => ∑ s, affineGibbs (fun _ => 0) U z s) = fun _ => 1 :=
    funext (fun z => affineGibbs_sum (fun _ => 0) U z)
  rw [he,hierarchyMomentLevel_const n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U)] at H
  exact (congrFun H z).symm

theorem hierarchySpinMean_eq_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchySpinMean n m U v j z = ∑ s, hierarchySpinWeight n m U j z s*v s := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => v s*affineGibbs (fun _ => 0) U z s)
    (fun s => continuous_const.mul (affineGibbs_continuous (fun _ => 0) U s))
    (fun s => ‖v s‖) (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one (fun _ => 0) U z s) (norm_nonneg _)).trans_eq (mul_one _)) j
  simp_rw [hierarchyMomentLevel_const_mul] at H
  change hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
    (fun z => ∑ s, affineGibbs (fun _ => 0) U z s*v s) j z = _
  simpa only [hierarchySpinWeight,mul_comm] using congrFun H z
end Probability
end SK.Analytic

end
end

end

end OAI
