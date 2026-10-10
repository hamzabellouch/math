import OAI.Geometry.SurfaceImmersion.Correction.CovarianceCorrector

namespace OAI

/-!
Smooth parameter dependence of the actual finite covariance solve.  Averaging
is a bounded linear map on continuous periodic functions; the covariance is
a quadratic map on that Banach space.  Thus no regularity assumption on the
inverse matrix is needed.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

section PeriodicMaps

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Apply a continuous bilinear map pointwise to continuous periodic maps. -/
def periodicBilinear (B : E →L[ℝ] F →L[ℝ] G) :
    C(Period, E) →L[ℝ] C(Period, F) →L[ℝ] C(Period, G) := by
  let b : C(Period, E) → C(Period, F) → C(Period, G) := fun f g =>
    ⟨fun t => B (f t) (g t), (B.continuous.comp f.continuous).clm_apply g.continuous⟩
  let L : C(Period, E) →ₗ[ℝ] C(Period, F) →ₗ[ℝ] C(Period, G) :=
    LinearMap.mk₂ ℝ b
      (by intros; ext; simp [b, map_add])
      (by intros; ext; simp [b, map_smul])
      (by intros; ext; simp [b, map_add])
      (by intros; ext; simp [b, map_smul])
  exact L.mkContinuous₂ ‖B‖ (by
    intro f g
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    exact (B.le_opNorm₂ (f t) (g t)).trans (by
      gcongr
      · exact f.norm_coe_le_norm t
      · exact g.norm_coe_le_norm t))

@[simp] theorem periodicBilinear_apply (B : E →L[ℝ] F →L[ℝ] G)
    (f : C(Period, E)) (g : C(Period, F)) (t : Period) :
    periodicBilinear B f g t = B (f t) (g t) := rfl

variable [CompleteSpace E]

/-- The normalized Haar average, bundled with its norm bound. -/
def averageCLM : C(Period, E) →L[ℝ] E :=
  ({ toFun := fun f => ∫ t, f t ∂AddCircle.haarAddCircle
     map_add' := fun f g => integral_add
       (integrable_of_continuous f.continuous) (integrable_of_continuous g.continuous)
     map_smul' := fun c f => integral_smul c f } : C(Period, E) →ₗ[ℝ] E).mkContinuous
    1 (by
      intro f
      have h := norm_integral_le_of_norm_le_const
        (μ := AddCircle.haarAddCircle) (f := fun t => f t)
        (Filter.Eventually.of_forall f.norm_coe_le_norm)
      simpa using h)

omit [CompleteSpace E] in
@[simp] theorem averageCLM_apply (f : C(Period, E)) :
    averageCLM f = ∫ t, f t ∂AddCircle.haarAddCircle := rfl

def centeredPeriodic (V : C(Period, E)) : C(Period, E) :=
  V - ContinuousMap.const Period (averageCLM V)

omit [CompleteSpace E] in
theorem contDiff_centeredPeriodic : ContDiff ℝ ∞ (centeredPeriodic : C(Period, E) → _) := by
  let L : E →L[ℝ] C(Period, E) := ContinuousLinearMap.const ℝ Period
  exact contDiff_id.sub (L.contDiff.comp (averageCLM (E := E)).contDiff)

end PeriodicMaps

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The covariance as a quadratic expression in a continuous periodic map. -/
def covarianceCLM (V : C(Period, E)) : E →L[ℝ] E :=
  averageCLM (periodicBilinear (InnerProductSpace.rankOne ℝ)
    (centeredPeriodic V) (centeredPeriodic V))

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem covarianceCLM_apply (V : C(Period, E)) (m : E) :
    covarianceCLM V m = covariance V (average V) m := by
  unfold covarianceCLM
  rw [averageCLM_apply]
  change (∫ t, periodicBilinear (InnerProductSpace.rankOne ℝ)
    (centeredPeriodic V) (centeredPeriodic V) t ∂AddCircle.haarAddCircle) m = _
  rw [ContinuousLinearMap.integral_apply (integrable_of_continuous
    (periodicBilinear (InnerProductSpace.rankOne ℝ)
      (centeredPeriodic V) (centeredPeriodic V)).continuous)]
  rfl

omit [CompleteSpace E] in
theorem contDiff_covarianceCLM : ContDiff ℝ ∞ (covarianceCLM : C(Period, E) → _) := by
  rw [contDiff_clm_apply_iff]
  intro m
  let L : C(Period, E) →L[ℝ] C(Period, ℝ) :=
    (innerSL ℝ m).compLeftContinuous ℝ Period
  let B : C(Period, ℝ) →L[ℝ] C(Period, E) →L[ℝ] C(Period, E) :=
    periodicBilinear (ContinuousLinearMap.lsmul ℝ ℝ)
  have hB := B.isBoundedBilinearMap.contDiff.comp
    ((L.contDiff.comp contDiff_centeredPeriodic).prodMk contDiff_centeredPeriodic)
  have hh := averageCLM.contDiff.comp hB
  convert hh using 1
  ext V
  rw [covarianceCLM_apply]
  change (∫ t, inner ℝ (V t - average V) m • (V t - average V)
    ∂AddCircle.haarAddCircle) =
    ∫ t, inner ℝ m (V t - average V) • (V t - average V) ∂AddCircle.haarAddCircle
  congr 1
  funext t
  rw [real_inner_comm]

def meanCLM (V : C(Period, E)) (q : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - q⁻¹ • covarianceCLM V

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem meanCLM_apply (V : C(Period, E)) (q : ℝ) (m : E) :
    meanCLM V q m = m - q⁻¹ • covariance V (average V) m := by
  simp only [meanCLM, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, covarianceCLM_apply]

theorem meanCLM_isInvertible {V : C(Period, E)} {q : ℝ} (hq : 0 < q)
    (hcircle : ∀ t, inner ℝ (V t) (V t) = q) : (meanCLM V q).IsInvertible := by
  have hinj : Function.Injective (meanCLM V q) := by
    intro m n he
    apply sub_eq_zero.mp
    apply meanOperator_kernel_trivial V.continuous rfl hq hcircle
    change (m - n) - q⁻¹ • covariance V (average V) (m - n) = 0
    rw [← meanCLM_apply, map_sub, he, sub_self]
  have hsurj : Function.Surjective (meanCLM V q) :=
    LinearMap.surjective_of_injective (f := (meanCLM V q).toLinearMap) hinj
  refine ⟨(LinearEquiv.ofBijective (meanCLM V q).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  rfl

def weightedAverage (V : C(Period, E)) (r : C(Period, ℝ)) : E :=
  averageCLM (periodicBilinear (ContinuousLinearMap.lsmul ℝ ℝ) r V)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem weightedAverage_apply (V : C(Period, E)) (r : C(Period, ℝ)) :
    weightedAverage V r = average (fun t => r t • V t) := rfl

def covarianceSolution (V : C(Period, E)) (r : C(Period, ℝ)) (q : ℝ) : E :=
  (meanCLM V q).inverse (weightedAverage V r)

theorem covarianceSolution_equation {V : C(Period, E)} (r : C(Period, ℝ))
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    covarianceSolution V r q - q⁻¹ • covariance V (average V) (covarianceSolution V r q) =
      average (fun t => r t • V t) := by
  rw [← meanCLM_apply]
  exact (meanCLM_isInvertible hq hcircle).self_apply_inverse _

theorem contDiff_covarianceSolution {V : P → C(Period, E)} {r : P → C(Period, ℝ)}
    {q : P → ℝ} (hV : ContDiff ℝ ∞ V) (hr : ContDiff ℝ ∞ r)
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ x, 0 < q x)
    (hcircle : ∀ x t, inner ℝ (V x t) (V x t) = q x) :
    ContDiff ℝ ∞ (fun x => covarianceSolution (V x) (r x) (q x)) := by
  have hM : ContDiff ℝ ∞ (fun x => meanCLM (V x) (q x)) :=
    contDiff_const.sub ((hq.inv (fun x => (hqpos x).ne')).smul
      (contDiff_covarianceCLM.comp hV))
  have hMinv : ContDiff ℝ ∞ (fun x => (meanCLM (V x) (q x)).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (meanCLM_isInvertible (hqpos x) (hcircle x)).contDiffAt_map_inverse.comp x hM.contDiffAt
  have hsource : ContDiff ℝ ∞ (fun x => weightedAverage (V x) (r x)) :=
    by
      let B : C(Period, ℝ) →L[ℝ] C(Period, E) →L[ℝ] C(Period, E) :=
        periodicBilinear (ContinuousLinearMap.lsmul ℝ ℝ)
      exact averageCLM.contDiff.comp (B.isBoundedBilinearMap.contDiff.comp (hr.prodMk hV))
  exact hMinv.clm_apply hsource

def parameterCorrector (V : P → C(Period, E)) (r : P → C(Period, ℝ))
    (q : P → ℝ) (x : P) : Period → E :=
  correctedVector (V x) (average (V x)) (q x) (r x)
    (covarianceSolution (V x) (r x) (q x))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem parameterCorrector_average {V : P → C(Period, E)} {r : P → C(Period, ℝ)}
    {q : P → ℝ} (hqpos : ∀ x, 0 < q x)
    (hcircle : ∀ x t, inner ℝ (V x t) (V x t) = q x) (x : P) :
    average (parameterCorrector V r q x) = 0 :=
  average_correctedVector (V x).continuous rfl (r x).continuous (q x)
    (covarianceSolution (V x) (r x) (q x))
    (covarianceSolution_equation (r x) (hqpos x) (hcircle x))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem parameterCorrector_projection {V : P → C(Period, E)} {r : P → C(Period, ℝ)}
    {q : P → ℝ} (hr0 : ∀ x, average (r x) = 0) (hqpos : ∀ x, 0 < q x)
    (hcircle : ∀ x t, inner ℝ (V x t) (V x t) = q x) (x : P) :
    fluctuation (fun t => inner ℝ (V x t) (parameterCorrector V r q x t)) = r x :=
  corrected_projection (V x) (average (V x)) (r x).continuous (hr0 x)
    (hqpos x).ne' (hcircle x) _

/-- Smoothness in both the finite-dimensional parameters and the angular
variable. The Banach-space hypotheses ensure uniform parameter smoothness;
the real-lift hypotheses provide angular smoothness and mixed derivatives. -/
theorem contDiff_parameterCorrector {V : P → C(Period, E)} {r : P → C(Period, ℝ)}
    {q : P → ℝ} (hV : ContDiff ℝ ∞ V) (hr : ContDiff ℝ ∞ r)
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ x, 0 < q x)
    (hcircle : ∀ x t, inner ℝ (V x t) (V x t) = q x)
    (hVlift : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period)))
    (hrlift : ContDiff ℝ ∞ (fun p : P × ℝ => r p.1 (p.2 : Period))) :
    ContDiff ℝ ∞ (fun p : P × ℝ => parameterCorrector V r q p.1 (p.2 : Period)) := by
  have hm : ContDiff ℝ ∞ (fun p : P × ℝ =>
      covarianceSolution (V p.1) (r p.1) (q p.1)) :=
    (contDiff_covarianceSolution hV hr hq hqpos hcircle).comp contDiff_fst
  have hv : ContDiff ℝ ∞ (fun p : P × ℝ => average (V p.1)) :=
    (averageCLM.contDiff.comp hV).comp contDiff_fst
  have hi : ContDiff ℝ ∞ (fun p : P × ℝ => (q p.1)⁻¹) :=
    (hq.comp contDiff_fst).inv (fun p => (hqpos p.1).ne')
  have hs : ContDiff ℝ ∞ (fun p : P × ℝ =>
      correctedScalar (V p.1) (average (V p.1)) (q p.1) (r p.1)
        (covarianceSolution (V p.1) (r p.1) (q p.1)) (p.2 : Period)) := by
    simpa only [correctedScalar, div_eq_mul_inv] using
      hrlift.add (((hVlift.sub hv).inner ℝ hm).mul hi)
  exact hi.smul ((hs.smul hVlift).sub hm)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
