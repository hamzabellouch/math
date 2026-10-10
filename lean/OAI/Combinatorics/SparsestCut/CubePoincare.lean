import OAI.Combinatorics.SparsestCut.GaussianCDF

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubePoincare
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff ENNReal BigOperators
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def Ψ (x : E) : E := WithLp.toLp 2 (fun i => GaussianCDF.ψ (x i))
def cube : Measure E := (Measure.pi (fun _ : Fin m => GaussianCDF.uniform)).map (WithLp.toLp 2)

instance cube_probability : IsProbabilityMeasure (cube (m := m)) := by
  unfold cube
  infer_instance

def coordinate (i : Fin m) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap

@[simp] lemma coordinate_apply (i : Fin m) (x : E) : coordinate i x = x i := rfl

def derivative (x : E) : E →L[ℝ] E :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (2*GaussianCDF.φ (x i)) • coordinate i))

@[simp] lemma derivative_apply (x v : E) (i : Fin m) : derivative x v i = 2*GaussianCDF.φ (x i)*v i := rfl

lemma Ψ_hasFDeriv (x : E) : HasFDerivAt Ψ (derivative x) x := by
  have hi (i : Fin m) := (GaussianCDF.ψ_hasDeriv (x i)).comp_hasFDerivAt x (coordinate i).hasFDerivAt
  have hp := hasFDerivAt_pi.mpr hi
  have h := (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp x hp
  convert h using 1 <;> rfl

lemma Ψ_contDiff : ContDiff ℝ 1 (Ψ (m := m)) := by
  have h : ContDiff ℝ 1 (fun x : E => fun i => GaussianCDF.ψ (x i)) :=
    contDiff_pi.mpr (fun i => GaussianCDF.ψ_contDiff.comp (coordinate i).contDiff)
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.contDiff.comp h

lemma Ψ_norm (x : E) : ‖Ψ x‖ ≤ Real.sqrt m := by
  have h : ‖Ψ x‖^2 ≤ (m:ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin m, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := GaussianCDF.ψ_mem (x i)
        change ‖GaussianCDF.ψ (x i)‖^2 ≤ 1
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [hi.1,hi.2]
      _ = _ := by simp
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m), Real.sqrt_nonneg (m:ℝ), norm_nonneg (Ψ x)]

lemma derivative_norm (x : E) : ‖derivative x‖ ≤ 1 := by
  apply (derivative x).opNorm_le_bound (by norm_num)
  intro v
  simp only [one_mul]
  have h : ‖derivative x v‖^2 ≤ ‖v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change ‖2*GaussianCDF.φ (x i)*v i‖^2 ≤ ‖v i‖^2
    rw [norm_mul, mul_pow]
    have hi := GaussianCDF.ψ_deriv_bound (x i)
    have hh : ‖2*GaussianCDF.φ (x i)‖^2 ≤ 1 := by
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (2*GaussianCDF.φ (x i))]
    nlinarith [sq_nonneg ‖v i‖]
  nlinarith [norm_nonneg (derivative x v), norm_nonneg v]

lemma Ψ_map : (stdGaussian E).map Ψ = cube := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map Ψ_contDiff.continuous.measurable (by fun_prop)]
  have he : (Ψ (m := m)) ∘ WithLp.toLp 2 = WithLp.toLp 2 ∘
      (fun x : Fin m → ℝ => fun i => GaussianCDF.ψ (x i)) := rfl
  have hmeas : Measurable (fun x : Fin m → ℝ => fun i => GaussianCDF.ψ (x i)) :=
    Measurable.of_eval (fun i => GaussianCDF.ψ_contDiff.continuous.measurable.comp (measurable_pi_apply i))
  rw [he, ← Measure.map_map (by fun_prop) hmeas, Measure.pi_map_pi]
  · simp_rw [GaussianCDF.ψ_map]
    rfl
  · intro i
    exact GaussianCDF.ψ_contDiff.continuous.measurable.aemeasurable

lemma cube_first_moment (h : E → ℝ) (hh : ContDiff ℝ 1 h) :
    (∫ z : E × E, |h z.1-h z.2| ∂((cube (m := m)).prod cube)) ≤
      (Real.pi/2)*(∫ x : E, ‖fderiv ℝ h x‖ ∂cube) := by
  let μ := stdGaussian E
  let H : E → ℝ := h ∘ Ψ
  have hH : ContDiff ℝ 1 H := hh.comp Ψ_contDiff
  have hcompact := isCompact_closedBall (0:E) (Real.sqrt m)
  obtain ⟨B,hB⟩ := hcompact.exists_bound_of_continuousOn hh.continuous.continuousOn
  obtain ⟨M,hM⟩ := hcompact.exists_bound_of_continuousOn (hh.continuous_fderiv (by norm_num)).continuousOn
  have hmem (x : E) : Ψ x ∈ Metric.closedBall 0 (Real.sqrt m) := by simpa using Ψ_norm x
  have hB' (x : E) : ‖H x‖ ≤ max B 0 := (hB _ (hmem x)).trans (le_max_left _ _)
  have hcomp (x : E) : fderiv ℝ H x = (fderiv ℝ h (Ψ x)).comp (derivative x) :=
    ((hh.differentiable (by norm_num) (Ψ x)).hasFDerivAt.comp x (Ψ_hasFDeriv x)).fderiv
  have hnorm (x : E) : ‖fderiv ℝ H x‖ ≤ ‖fderiv ℝ h (Ψ x)‖ := by
    rw [hcomp]
    exact ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
      ((mul_le_mul_of_nonneg_left (derivative_norm x) (norm_nonneg _)).trans_eq (mul_one _))
  have hdB (x : E) : ‖fderiv ℝ H x‖ ≤ max M 0 :=
    (hnorm x).trans ((hM _ (hmem x)).trans (le_max_left _ _))
  have hint : Integrable (fun x : E => ‖fderiv ℝ h (Ψ x)‖) μ := by
    apply (integrable_const (max M 0)).mono' ((hh.continuous_fderiv (by norm_num)).comp Ψ_contDiff.continuous |>.norm.aestronglyMeasurable)
    filter_upwards with x
    simpa only [norm_norm, Function.comp_apply] using (hM _ (hmem x)).trans (le_max_left _ _)
  have hintH : Integrable (fun x : E => ‖fderiv ℝ H x‖) μ := by
    apply hint.mono' (by have hc := hH.continuous_fderiv (by norm_num); fun_prop)
    filter_upwards with x
    simpa only [norm_norm] using hnorm x
  have hp := GaussianPoincare.rotation_first_moment H hH (le_max_right M 0) hdB hB'
  have hmeasure : MeasurePreserving Ψ μ cube := ⟨Ψ_contDiff.continuous.measurable, Ψ_map⟩
  have hprod := hmeasure.prod hmeasure
  have heL : (∫ z : E × E, |H z.1-H z.2| ∂μ.prod μ) =
      ∫ z : E × E, |h z.1-h z.2| ∂((cube (m := m)).prod cube) := by
    rw [← hprod.map_eq]
    exact (integral_map (f := fun z : E × E => |h z.1-h z.2|) hprod.measurable.aemeasurable (by fun_prop)).symm
  have heR : (∫ x : E, ‖fderiv ℝ h (Ψ x)‖ ∂μ) = ∫ x : E, ‖fderiv ℝ h x‖ ∂cube := by
    rw [← hmeasure.map_eq]
    exact (integral_map (f := fun x : E => ‖fderiv ℝ h x‖) hmeasure.measurable.aemeasurable
      (by have hc := hh.continuous_fderiv (by norm_num); fun_prop)).symm
  rw [← heL, ← heR]
  exact hp.trans (mul_le_mul_of_nonneg_left (integral_mono hintH hint hnorm) (by positivity))

end UniformSparsestCut.CubePoincare

end

end OAI
