import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyJointMoment

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem gaussian_convex_tilt_integrable (n : ℕ) (G : ParameterSpace n → ℝ)
    (hG : ContDiff ℝ 2 G) (hGc : ConvexOn ℝ univ G)
    (U : ParameterSpace n →L[ℝ] ℝ) :
    let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
    Integrable (fun z => Real.exp (-V z)) (fiberMeasure n 0) ∧
    Integrable (fun z => coordinateSquare n z*Real.exp (-V z)) (fiberMeasure n 0) := by
  let V := fun z => (1/2 : ℝ)*coordinateSquare n z-U z+G z
  have hq := contDiff_coordinateSquare n
  have hV : ContDiff ℝ 2 V := ((contDiff_const.mul hq).sub U.contDiff).add hG
  apply integrable_stronglyConvex_density n V hV (by norm_num : (0 : ℝ) < 1)
  intro z u
  have he : V = fun z => ((1/2 : ℝ)*coordinateSquare n z + (-1)*U z)+G z := by
    funext z; dsimp only [V]; ring
  rw [he, hessian_add ((contDiff_const.mul hq).add (contDiff_const.mul U.contDiff)) hG,
    hessian_add (contDiff_const.mul hq) (contDiff_const.mul U.contDiff),
    hessian_const_mul hq, hessian_const_mul U.contDiff, hessian_linear,
    hessian_coordinateSquare]
  nlinarith [hessian_nonneg_of_convex G hG hGc z u]

def hierarchyLogDensity {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (s : S) (z : ParameterSpace n) : ℝ :=
  -(1/2 : ℝ)*coordinateSquare n z+U s z-
    hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z

theorem hierarchyLogDensity_continuous {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) :
    Continuous (hierarchyLogDensity n m U s) := by
  have hreg := hierarchyPenalty_regular n m 1 zero_le_one hm hmu hmono
    (affineLogPartition (fun _ => 0) U)
    ⟨affineLogPartition_boundedDerivs _ _,affineLogPartition_convex _ _⟩
  exact (((continuous_coordinateSquare n).const_mul _).add (U s).continuous).sub hreg.1.1.continuous

theorem hierarchyLogDensity_integrable {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) :
    Integrable (fun z => Real.exp (hierarchyLogDensity n m U s z)) (fiberMeasure n 0) ∧
    Integrable (fun z => coordinateSquare n z*Real.exp (hierarchyLogDensity n m U s z))
      (fiberMeasure n 0) := by
  have hreg := hierarchyPenalty_regular n m 1 zero_le_one hm hmu hmono
    (affineLogPartition (fun _ => 0) U)
    ⟨affineLogPartition_boundedDerivs _ _,affineLogPartition_convex _ _⟩
  have he (z : ParameterSpace n) :
      -((1/2 : ℝ)*coordinateSquare n z-U s z+
        hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) =
        hierarchyLogDensity n m U s z := by unfold hierarchyLogDensity; ring
  simpa only [he] using gaussian_convex_tilt_integrable n _ hreg.1.1 hreg.2 (U s)

theorem hierarchyLogDensity_moment_integrable {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    (s : S) {p : ℕ} (hp : p ≤ 2) :
    Integrable (fun z => (L s z)^p*Real.exp (hierarchyLogDensity n m U s z))
      (fiberMeasure n 0) := by
  obtain ⟨hI₀,hIq⟩ := hierarchyLogDensity_integrable n m hm hmu hmono U s
  have hc := hierarchyLogDensity_continuous n m hm hmu hmono U s
  have hI₂ : Integrable (fun z => (L s z)^2*Real.exp (hierarchyLogDensity n m U s z))
      (fiberMeasure n 0) := by
    apply (hIq.const_mul A).mono' (((L s).continuous.pow 2).mul (Real.continuous_exp.comp hc)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(L s z)^2*Real.exp (hierarchyLogDensity n m U s z)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_right (hL s z) (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _)
  interval_cases p
  · simpa only [pow_zero,one_mul] using hI₀
  · simp only [pow_one]
    apply (hI₀.add hI₂).mono' ((L s).continuous.mul (Real.continuous_exp.comp hc)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖L s z*Real.exp (hierarchyLogDensity n m U s z)‖ ≤
      Real.exp (hierarchyLogDensity n m U s z)+(L s z)^2*Real.exp (hierarchyLogDensity n m U s z)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hl : |L s z| ≤ 1+(L s z)^2 := by nlinarith [sq_nonneg (|L s z|-1),sq_abs (L s z)]
    nlinarith [mul_le_mul_of_nonneg_right hl (Real.exp_pos (hierarchyLogDensity n m U s z)).le]
  · exact hI₂

section JointLaw
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def hierarchyLaw (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) :
    Measure (S × ParameterSpace n) :=
  ((Measure.count : Measure S).prod (fiberMeasure n 0)).tilted
    (fun sz => hierarchyLogDensity n m U sz.1 sz.2)

theorem hierarchyJoint_integrable (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    {p : ℕ} (hp : p ≤ 2) :
    Integrable (fun sz : S × ParameterSpace n =>
      (L sz.1 sz.2)^p*Real.exp (hierarchyLogDensity n m U sz.1 sz.2))
      ((Measure.count : Measure S).prod (fiberMeasure n 0)) := by
  apply (integrable_prod_iff ?_).2
  · exact ⟨Filter.Eventually.of_forall fun s =>
      hierarchyLogDensity_moment_integrable n m hm hmu hmono U L hL s hp,
      Integrable.of_finite⟩
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro s
    exact (((L s).continuous.pow p).mul
      (Real.continuous_exp.comp (hierarchyLogDensity_continuous n m hm hmu hmono U s))).measurable

theorem hierarchyLaw_probability (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    IsProbabilityMeasure (hierarchyLaw n m U) := by
  let : NeZero ((Measure.count : Measure S).prod (fiberMeasure n 0)) := by
    refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
    rw [← univ_prod_univ,Measure.prod_prod]
    exact mul_ne_zero (NeZero.ne _) (NeZero.ne _)
  apply isProbabilityMeasure_tilted
  have hi := hierarchyJoint_integrable n m hm hmu hmono U (fun _ => 0)
    (A := 0) (by intro s z; simp) (p := 0) (by omega)
  simpa only [pow_zero,one_mul] using hi

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyJointMoment_pos (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ) :
    0 < hierarchyJointMoment n m U L 0 := by
  unfold hierarchyJointMoment
  simp only [pow_zero,one_mul]
  apply Finset.sum_pos (fun s _ => ?_) Finset.univ_nonempty
  exact integral_exp_pos (hierarchyLogDensity_integrable n m hm hmu hmono U s).1

theorem hierarchyLaw_moment (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z)
    {p : ℕ} (hp : p ≤ 2) :
    (∫ sz, (L sz.1 sz.2)^p ∂hierarchyLaw n m U) =
      hierarchyJointMoment n m U L p / hierarchyJointMoment n m U L 0 := by
  have he (r : ℕ) (hr : r ≤ 2) :
      (∫ sz : S × ParameterSpace n, (L sz.1 sz.2)^r*
        Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
        ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) = hierarchyJointMoment n m U L r := by
    rw [integral_prod _ (hierarchyJoint_integrable n m hm hmu hmono U L hL hr),integral_count]
    rfl
  unfold hierarchyLaw
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have hf : (fun sz : S × ParameterSpace n =>
      Real.exp (hierarchyLogDensity n m U sz.1 sz.2) /
        (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
          ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) * (L sz.1 sz.2)^p) =
      (fun sz => ((L sz.1 sz.2)^p*Real.exp (hierarchyLogDensity n m U sz.1 sz.2)) /
        (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
          ∂(Measure.count : Measure S).prod (fiberMeasure n 0))) := by funext sz; ring
  rw [hf,integral_div,he p hp]
  have he₀ := he 0 (by omega)
  simpa only [pow_zero,one_mul] using congrArg (fun z => hierarchyJointMoment n m U L p / z) he₀

theorem hierarchyLaw_variance (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U L : S → ParameterSpace n →L[ℝ] ℝ)
    {A : ℝ} (hL : ∀ s z, (L s z)^2 ≤ A*coordinateSquare n z) :
    ProbabilityTheory.variance (fun sz => L sz.1 sz.2) (hierarchyLaw n m U) =
      hierarchyJointMoment n m U L 2 / hierarchyJointMoment n m U L 0 -
        (hierarchyJointMoment n m U L 1 / hierarchyJointMoment n m U L 0)^2 := by
  let := hierarchyLaw_probability n m hm hmu hmono U
  have hmeas : Measurable (fun sz : S × ParameterSpace n => L sz.1 sz.2) :=
    measurable_from_prod_countable_right fun s => (L s).continuous.measurable
  have hi₀ := hierarchyJoint_integrable n m hm hmu hmono U L hL (p := 0) (by omega)
  simp only [pow_zero,one_mul] at hi₀
  have hi₂ := hierarchyJoint_integrable n m hm hmu hmono U L hL (p := 2) (by omega)
  have hL₂ : MemLp (fun sz : S × ParameterSpace n => L sz.1 sz.2) 2 (hierarchyLaw n m U) := by
    apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    apply (integrable_tilted_iff hi₀ _).2
    simpa only [smul_eq_mul,mul_comm] using hi₂
  rw [ProbabilityTheory.variance_eq_sub hL₂]
  change (∫ sz, (L sz.1 sz.2)^2 ∂hierarchyLaw n m U) -
    (∫ sz, L sz.1 sz.2 ∂hierarchyLaw n m U)^2 = _
  rw [hierarchyLaw_moment n m hm hmu hmono U L hL (by omega : 2 ≤ 2)]
  have h₁ := hierarchyLaw_moment n m hm hmu hmono U L hL (by omega : 1 ≤ 2)
  simpa only [pow_one] using congrArg (fun v =>
    hierarchyJointMoment n m U L 2/hierarchyJointMoment n m U L 0-v^2) h₁

end JointLaw
end SK.Analytic

end
end
end
end
end
end

end OAI
