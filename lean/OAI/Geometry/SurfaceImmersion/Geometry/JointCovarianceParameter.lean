import OAI.Geometry.SurfaceImmersion.Geometry.CovarianceParameter
import OAI.Geometry.SurfaceImmersion.Correction.SmoothParameterIntegral
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicPrimitive

namespace OAI

/-! Smoothness of the covariance solve from the joint position-angle data. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contDiff_average_joint {V : P → C(Period, E)}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period))) :
    ContDiff ℝ ∞ (fun p => average (V p)) := by
  have hi := SmoothParameterIntegral.contDiff_integral hV 0 1
  simpa only [PeriodicPrimitive.integral_lift_eq_haar, average] using hi

theorem contDiff_covarianceCLM_joint {V : P → C(Period, E)}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period))) :
    ContDiff ℝ ∞ (fun p => covarianceCLM (V p)) := by
  have hc := hV.sub ((contDiff_average_joint hV).comp contDiff_fst)
  rw [contDiff_clm_apply_iff]
  intro m
  simp_rw [covarianceCLM_apply]
  have hi := SmoothParameterIntegral.contDiff_integral
    ((hc.inner ℝ (contDiff_const (c := m))).smul hc) 0 1
  convert hi using 1
  funext p
  exact (PeriodicPrimitive.integral_lift_eq_haar
    (fun t => inner ℝ (V p t - average (V p)) m • (V p t - average (V p)))).symm

omit [FiniteDimensional ℝ E] in
theorem contDiff_weightedAverage_joint {V : P → C(Period, E)} {r : P → C(Period, ℝ)}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period)))
    (hr : ContDiff ℝ ∞ (fun p : P × ℝ => r p.1 (p.2 : Period))) :
    ContDiff ℝ ∞ (fun p => weightedAverage (V p) (r p)) := by
  have hi := SmoothParameterIntegral.contDiff_integral (hr.smul hV) 0 1
  convert hi using 1
  funext p
  exact (PeriodicPrimitive.integral_lift_eq_haar (fun t => r p t • V p t)).symm

theorem contDiff_covarianceSolution_joint {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period)))
    (hr : ContDiff ℝ ∞ (fun p : P × ℝ => r p.1 (p.2 : Period)))
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p) :
    ContDiff ℝ ∞ (fun p => covarianceSolution (V p) (r p) (q p)) := by
  have hM : ContDiff ℝ ∞ (fun p => meanCLM (V p) (q p)) :=
    contDiff_const.sub ((hq.inv (fun p => (hqpos p).ne')).smul
      (contDiff_covarianceCLM_joint hV))
  have hi : ContDiff ℝ ∞ (fun p => (meanCLM (V p) (q p)).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    exact (meanCLM_isInvertible (hqpos p) (hcircle p)).contDiffAt_map_inverse.comp p hM.contDiffAt
  exact hi.clm_apply (contDiff_weightedAverage_joint hV hr)

/-- Joint smoothness of the explicitly defined periodic corrector on the
finite-dimensional family of geometric data. -/
theorem contDiff_parameterCorrector_joint {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period)))
    (hr : ContDiff ℝ ∞ (fun p : P × ℝ => r p.1 (p.2 : Period)))
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p) :
    ContDiff ℝ ∞ (fun p : P × ℝ => parameterCorrector V r q p.1 (p.2 : Period)) := by
  have hm : ContDiff ℝ ∞ (fun p : P × ℝ =>
      covarianceSolution (V p.1) (r p.1) (q p.1)) :=
    (contDiff_covarianceSolution_joint hV hr hq hqpos hcircle).comp contDiff_fst
  have hv : ContDiff ℝ ∞ (fun p : P × ℝ => average (V p.1)) :=
    (contDiff_average_joint hV).comp contDiff_fst
  have hi : ContDiff ℝ ∞ (fun p : P × ℝ => (q p.1)⁻¹) :=
    (hq.comp contDiff_fst).inv (fun p => (hqpos p.1).ne')
  have hs : ContDiff ℝ ∞ (fun p : P × ℝ =>
      correctedScalar (V p.1) (average (V p.1)) (q p.1) (r p.1)
        (covarianceSolution (V p.1) (r p.1) (q p.1)) (p.2 : Period)) := by
    simpa only [correctedScalar, div_eq_mul_inv] using
      hr.add (((hV.sub hv).inner ℝ hm).mul hi)
  exact hi.smul ((hs.smul hV).sub hm)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
