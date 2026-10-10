import Mathlib
import OAI.Probability.Ballisticity.Crossings.PastCutoffs
import OAI.Probability.Ballisticity.Estimates.UniformRiemannMesh

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def cutoffMean (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) :
    C(unitInterval,ℝ) where
  toFun s := ∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ
  continuous_toFun := by
    apply continuous_of_dominated (bound := fun _ => 1)
    · intro s; exact (by fun_prop : Measurable (fun P : RealPathPair => nearDiagonalCutoff ρ (P.1 s-P.2 s))).aestronglyMeasurable
    · intro s; filter_upwards [] with P
      rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit ρ _).1]
      exact (nearDiagonalCutoff_unit ρ _).2
    · exact integrable_const 1
    · filter_upwards [] with P
      fun_prop

lemma cutoffMean_unit (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) (s : unitInterval) :
    0 ≤ cutoffMean μ ρ s ∧ cutoffMean μ ρ s ≤ 1 := by
  constructor
  · exact integral_nonneg (fun P => (nearDiagonalCutoff_unit ρ _).1)
  · have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun P : RealPathPair =>
        nearDiagonalCutoff ρ (P.1 s-P.2 s)) (C := 1) (by
        filter_upwards [] with P
        rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit ρ _).1]
        exact (nearDiagonalCutoff_unit ρ _).2)
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh

noncomputable def cutoffMeanExtension (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) : ℝ → ℝ :=
  fun s => cutoffMean μ ρ (Set.projIcc 0 1 zero_le_one s)

lemma cutoffMeanExtension_uniformContinuous (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) :
    UniformContinuous (cutoffMeanExtension μ ρ) := by
  exact (CompactSpace.uniformContinuous_of_continuous (cutoffMean μ ρ).continuous).comp
    (LipschitzWith.projIcc zero_le_one).uniformContinuous

lemma cutoff_riemann_tendsto (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ)
    {s t : ℝ} (hst : s < t) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, (t-s)/n*cutoffMeanExtension μ ρ (realMesh s t n j)) atTop
      (𝓝 (∫ u in s..t, cutoffMeanExtension μ ρ u)) :=
  tendsto_riemann_mesh _ (cutoffMeanExtension_uniformContinuous μ ρ) hst

lemma nearDiagonalCutoff_tendsto_zero {z : ℝ} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => nearDiagonalCutoff (1/((n:ℝ)+1)) z) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => 2*(1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop) :
      Tendsto (fun n : ℕ => (2:ℝ)/((n:ℝ)+1)) atTop (𝓝 0))
  apply tendsto_const_nhds.congr'
  filter_upwards [hh.eventually_lt_const (abs_pos.mpr hz)] with n hn
  exact (nearDiagonalCutoff_zero (by positivity : 0 < 1/((n:ℝ)+1)) hn.le).symm

lemma diagonal_zero_cutoff_integral_tendsto (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0) :
    Tendsto (fun n : ℕ => ∫ z : RealPathPair × unitInterval,
      nearDiagonalCutoff (1/((n:ℝ)+1)) (z.1.1 z.2-z.1.2 z.2) ∂μ.prod volume) atTop (𝓝 0) := by
  have hae : ∀ᵐ z : RealPathPair × unitInterval ∂μ.prod volume, z.1.1 z.2-z.1.2 z.2 ≠ 0 := by
    rw [ae_iff]
    simpa using hz
  have hh := tendsto_integral_of_dominated_convergence (μ := μ.prod volume) (fun _ => (1:ℝ))
    (fun n => (by fun_prop : Measurable (fun z : RealPathPair × unitInterval =>
      nearDiagonalCutoff (1/((n:ℝ)+1)) (z.1.1 z.2-z.1.2 z.2))).aestronglyMeasurable)
    (integrable_const 1) (fun n => by
      filter_upwards [] with z
      rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit _ _).1]
      exact (nearDiagonalCutoff_unit _ _).2) (show ∀ᵐ z : RealPathPair × unitInterval ∂μ.prod volume,
      Tendsto (fun n : ℕ => nearDiagonalCutoff (1/((n:ℝ)+1)) (z.1.1 z.2-z.1.2 z.2)) atTop (𝓝 0) by
      filter_upwards [hae] with z hz
      exact nearDiagonalCutoff_tendsto_zero hz)
  simpa using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma cutoffMean_integral_eq (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) :
    (∫ u in (0:ℝ)..1, cutoffMeanExtension μ ρ u)=
      ∫ z : RealPathPair × unitInterval, nearDiagonalCutoff ρ (z.1.1 z.2-z.1.2 z.2) ∂μ.prod volume := by
  have hi : Integrable (fun z : RealPathPair × unitInterval =>
      nearDiagonalCutoff ρ (z.1.1 z.2-z.1.2 z.2)) (μ.prod volume) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit ρ _).1]
    exact (nearDiagonalCutoff_unit ρ _).2
  rw [integral_prod_symm _ hi]
  have hid : (fun u : unitInterval => (∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ))=
      fun u : unitInterval => cutoffMeanExtension μ ρ (u:ℝ) := by
    funext u
    simp only [cutoffMeanExtension,Set.projIcc_of_mem zero_le_one u.property]
    rfl
  rw [hid,integral_subtype measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

lemma cutoffMean_subinterval_le (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ)
    (s t : unitInterval) (hst : s ≤ t) :
    (∫ u in (s:ℝ)..t, cutoffMeanExtension μ ρ u) ≤
      ∫ z : RealPathPair × unitInterval, nearDiagonalCutoff ρ (z.1.1 z.2-z.1.2 z.2) ∂μ.prod volume := by
  rw [← cutoffMean_integral_eq]
  exact intervalIntegral.integral_mono_interval s.property.1 hst t.property.2
    (ae_of_all _ (fun u => (cutoffMean_unit μ ρ _).1))
    ((cutoffMeanExtension_uniformContinuous μ ρ).continuous.intervalIntegrable 0 1)

lemma cutoffMean_subinterval_nonneg (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ)
    (s t : unitInterval) (hst : s ≤ t) :
    0 ≤ ∫ u in (s:ℝ)..t, cutoffMeanExtension μ ρ u := by
  exact intervalIntegral.integral_nonneg hst (fun u _ => (cutoffMean_unit μ ρ _).1)

lemma diagonal_zero_subinterval_cutoff_tendsto (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
    (s t : unitInterval) (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∫ u in (s:ℝ)..t, cutoffMeanExtension μ (1/((n:ℝ)+1)) u) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => cutoffMean_subinterval_nonneg μ _ s t hst)
    (fun n => cutoffMean_subinterval_le μ _ s t hst) (diagonal_zero_cutoff_integral_tendsto μ hz)

end DirectionalTransience

end

end

end OAI
