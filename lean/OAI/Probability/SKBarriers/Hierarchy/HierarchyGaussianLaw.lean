import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyJointLaw
import OAI.Probability.SKBarriers.Gaussian.FiberGaussian

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
section LawIdentification
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]

def hierarchyTerminalGibbs (n : ℕ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (s : S) (z : ParameterSpace n) : ℝ :=
  Real.exp (U s z-affineLogPartition (fun _ => 0) U z)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyTerminalGibbs_sum (n : ℕ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (z : ParameterSpace n) : ∑ s, hierarchyTerminalGibbs n U s z = 1 := by
  have hp : 0 < ∑ s, Real.exp (U s z) :=
    Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [hierarchyTerminalGibbs,Real.exp_sub,affineLogPartition,zero_add,
    Real.exp_log hp,← Finset.sum_div,div_self hp.ne']

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyGaussian_density (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (s : S) (z : ParameterSpace n) :
    fiberGaussianDensity n z * (hierarchyPathWeight n m
      (affineLogPartition (fun _ => 0) U) z * hierarchyTerminalGibbs n U s z) =
      (Real.sqrt (2*Real.pi))⁻¹^n * Real.exp (hierarchyLogDensity n m U s z) := by
  rw [hierarchyTerminalGibbs,hierarchy_fixed_spin_density]
  unfold fiberGaussianDensity hierarchyLogDensity
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem hierarchyGaussian_normalizer (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    (Real.sqrt (2*Real.pi))⁻¹^n *
      (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
        ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) = 1 := by
  have hi := hierarchyJoint_integrable n m hm hmu hmono U (fun _ => 0)
    (A := 0) (by intro s z; simp) (p := 0) (by omega)
  simp only [pow_zero,one_mul] at hi
  rw [integral_prod _ hi,integral_count,← integral_finsetSum _
    (fun s _ => (hierarchyLogDensity_integrable n m hm hmu hmono U s).1),← integral_const_mul]
  have he (z : ParameterSpace n) :
      (Real.sqrt (2*Real.pi))⁻¹^n * ∑ s, Real.exp (hierarchyLogDensity n m U s z) =
      fiberGaussianDensity n z * hierarchyPathWeight n m (affineLogPartition (fun _ => 0) U) z := by
    rw [Finset.mul_sum]
    simp_rw [← hierarchyGaussian_density n m U]
    rw [← Finset.mul_sum,← Finset.mul_sum,hierarchyTerminalGibbs_sum,mul_one]
  simp_rw [he]
  have hn := (hierarchyPathWeight_normalized n m (affineLogPartition (fun _ => 0) U) (affineLogPartition_boundedDerivs (fun _ => 0) U) 0).2
  rw [fiberGaussian_eq_withDensity,integral_withDensity_eq_integral_toReal_smul
    (fiberGaussianDensity_continuous n).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hn
  simpa only [ENNReal.toReal_ofReal (fiberGaussianDensity_pos _ _).le,smul_eq_mul] using hn

def hierarchyGaussianLaw (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) : Measure (S × ParameterSpace n) :=
  ((Measure.count : Measure S).prod (fiberGaussian n 0)).withDensity
    (fun sz => ENNReal.ofReal (hierarchyPathWeight n m
      (affineLogPartition (fun _ => 0) U) sz.2 * hierarchyTerminalGibbs n U sz.1 sz.2))

theorem hierarchyGaussianLaw_eq (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (U : S → ParameterSpace n →L[ℝ] ℝ) :
    hierarchyGaussianLaw n m U = hierarchyLaw n m U := by
  have hn := hierarchyGaussian_normalizer n m hm hmu hmono U
  have hp : 0 < (Real.sqrt (2*Real.pi))⁻¹^n := by positivity
  have hZ : (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
      ∂(Measure.count : Measure S).prod (fiberMeasure n 0)) ≠ 0 := by
    intro h
    rw [h,mul_zero] at hn
    norm_num at hn
  unfold hierarchyGaussianLaw hierarchyLaw Measure.tilted
  rw [fiberGaussian_eq_withDensity,prod_withDensity_right
    (fiberGaussianDensity_continuous n).measurable.ennreal_ofReal]
  rw [← withDensity_mul]
  · apply congrArg (((Measure.count : Measure S).prod (fiberMeasure n 0)).withDensity)
    funext sz
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (fiberGaussianDensity_pos _ _).le,hierarchyGaussian_density]
    congr 1
    apply (eq_div_iff hZ).2
    calc
      _ = ((Real.sqrt (2*Real.pi))⁻¹^n *
          (∫ sz : S × ParameterSpace n, Real.exp (hierarchyLogDensity n m U sz.1 sz.2)
            ∂(Measure.count : Measure S).prod (fiberMeasure n 0))) *
          Real.exp (hierarchyLogDensity n m U sz.1 sz.2) := by ring
      _ = _ := by rw [hn,one_mul]
  · exact ((fiberGaussianDensity_continuous n).measurable.comp measurable_snd).ennreal_ofReal
  · apply Measurable.ennreal_ofReal
    apply measurable_from_prod_countable_right
    intro s
    exact ((hierarchyPathWeight_continuous n m _ (affineLogPartition_boundedDerivs _ _)).mul
      (Real.continuous_exp.comp ((U s).continuous.sub
        (affineLogPartition_boundedDerivs (fun _ => 0) U).1.continuous))).measurable

end LawIdentification
end SK.Analytic

end
end
end
end
end
end

end OAI
