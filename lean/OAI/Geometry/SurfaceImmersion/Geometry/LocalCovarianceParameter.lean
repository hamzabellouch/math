import OAI.Geometry.SurfaceImmersion.Geometry.LocalParameterIntegral
import OAI.Geometry.SurfaceImmersion.Geometry.JointCovarianceParameter

namespace OAI

/-! The covariance correction is smooth on the open admissible geometric domain. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma contDiffOn_average_joint {V : P → C(Period, E)} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => average (V p)) S := by
  have hi := SmoothParameterIntegral.contDiffOn_integral hS hV 0 1
  simpa only [PeriodicPrimitive.integral_lift_eq_haar, average] using hi

lemma contDiffOn_covarianceCLM_joint {V : P → C(Period, E)} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => covarianceCLM (V p)) S := by
  have hc := hV.sub ((contDiffOn_average_joint hS hV).comp contDiffOn_fst (fun _ hz => hz.1))
  rw [contDiffOn_clm_apply]
  intro m
  simp_rw [covarianceCLM_apply]
  have hi := SmoothParameterIntegral.contDiffOn_integral hS
    ((hc.inner ℝ (contDiffOn_const (c := m))).smul hc) 0 1
  convert hi using 1
  funext p
  exact (PeriodicPrimitive.integral_lift_eq_haar
    (fun t => inner ℝ (V p t - average (V p)) m • (V p t - average (V p)))).symm

omit [FiniteDimensional ℝ E] in
lemma contDiffOn_weightedAverage_joint {V : P → C(Period, E)} {r : P → C(Period, ℝ)}
    {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => r z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => weightedAverage (V p) (r p)) S := by
  have hi := SmoothParameterIntegral.contDiffOn_integral hS (hr.smul hV) 0 1
  convert hi using 1
  funext p
  exact (PeriodicPrimitive.integral_lift_eq_haar (fun t => r p t • V p t)).symm

lemma contDiffOn_covarianceSolution_joint {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => r z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q S) (hqpos : ∀ p ∈ S, 0 < q p)
    (hcircle : ∀ p ∈ S, ∀ t, inner ℝ (V p t) (V p t) = q p) :
    ContDiffOn ℝ ∞ (fun p => covarianceSolution (V p) (r p) (q p)) S := by
  have hM : ContDiffOn ℝ ∞ (fun p => meanCLM (V p) (q p)) S :=
    contDiffOn_const.sub ((hq.inv (fun p hp => (hqpos p hp).ne')).smul
      (contDiffOn_covarianceCLM_joint hS hV))
  have hi : ContDiffOn ℝ ∞ (fun p => (meanCLM (V p) (q p)).inverse) S := by
    apply hS.contDiffOn_iff.mpr
    intro p hp
    exact (meanCLM_isInvertible (hqpos p hp) (hcircle p hp)).contDiffAt_map_inverse.comp p
      (hM.contDiffAt (hS.mem_nhds hp))
  exact hi.clm_apply (contDiffOn_weightedAverage_joint hS hV hr)

lemma contDiffOn_parameterCorrector_joint {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => r z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q S) (hqpos : ∀ p ∈ S, 0 < q p)
    (hcircle : ∀ p ∈ S, ∀ t, inner ℝ (V p t) (V p t) = q p) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => parameterCorrector V r q z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := by
  have hm : ContDiffOn ℝ ∞ (fun z : P × ℝ =>
      covarianceSolution (V z.1) (r z.1) (q z.1)) (S ×ˢ Set.univ) :=
    (contDiffOn_covarianceSolution_joint hS hV hr hq hqpos hcircle).comp
    contDiffOn_fst (fun _ hz => hz.1)
  have hv : ContDiffOn ℝ ∞ (fun z : P × ℝ => average (V z.1)) (S ×ˢ Set.univ) :=
    (contDiffOn_average_joint hS hV).comp contDiffOn_fst (fun _ hz => hz.1)
  have hi : ContDiffOn ℝ ∞ (fun z : P × ℝ => (q z.1)⁻¹) (S ×ˢ Set.univ) :=
    (hq.comp contDiffOn_fst (fun _ hz => hz.1)).inv (fun z hz => (hqpos z.1 hz.1).ne')
  have hs : ContDiffOn ℝ ∞ (fun z : P × ℝ =>
      correctedScalar (V z.1) (average (V z.1)) (q z.1) (r z.1)
        (covarianceSolution (V z.1) (r z.1) (q z.1)) (z.2 : Period)) (S ×ˢ Set.univ) := by
    simpa only [correctedScalar, div_eq_mul_inv] using
      hr.add (((hV.sub hv).inner ℝ hm).mul hi)
  exact hi.smul ((hs.smul hV).sub hm)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
