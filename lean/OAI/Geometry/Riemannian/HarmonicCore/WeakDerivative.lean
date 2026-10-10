import OAI.Geometry.Riemannian.HarmonicCore.Energy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace HarmonicCounterexample.Main.SmoothMetric3
lemma smooth_memLp {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcompact : HasCompactSupport φ) : MemLp φ 2 (volume : Measure E3) :=
  hφ.continuous.memLp_of_hasCompactSupport hcompact

lemma smooth_gradient_memLp {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcompact : HasCompactSupport φ) : MemLp (gradient φ) 2 (volume : Measure E3) :=
  (gradient_continuous hφ).memLp_of_hasCompactSupport (gradient_compact hcompact)

lemma smooth_direction_memLp {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcompact : HasCompactSupport φ) (v : E3) :
    MemLp (fun x ↦ fderiv ℝ φ x v) 2 (volume : Measure E3) := by
  simpa only [inner_gradient_left] using (smooth_gradient_memLp hφ hcompact).inner_const (𝕜 := ℝ) v

lemma smooth_smul_memLp {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcompact : HasCompactSupport φ) (v : E3) :
    MemLp (fun x ↦ φ x • v) 2 (volume : Measure E3) :=
  (hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport
    (hcompact.smul_right)

lemma test_integration_by_parts {R : ℝ} (u : DirichletTest R)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ) (v : E3) :
    ⟪u.value,(smooth_direction_memLp hφ hcompact v).toLp _⟫_ℝ =
      -⟪u.derivative,(smooth_smul_memLp hφ hcompact v).toLp _⟫_ℝ := by
  have he1 : ⟪u.value,(smooth_direction_memLp hφ hcompact v).toLp _⟫_ℝ =
      ∫ x, (u:E3 → ℝ) x * fderiv ℝ φ x v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [u.value_memLp.coeFn_toLp,
      (smooth_direction_memLp hφ hcompact v).coeFn_toLp] with x hx hy
    change ⟪(u.value_memLp.toLp _) x, _⟫_ℝ = _
    rw [hx,hy]
    simp [mul_comm]
  have he2 : ⟪u.derivative,(smooth_smul_memLp hφ hcompact v).toLp _⟫_ℝ =
      ∫ x, fderiv ℝ (u:E3 → ℝ) x v * φ x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [u.derivative_memLp.coeFn_toLp,
      (smooth_smul_memLp hφ hcompact v).coeFn_toLp] with x hx hy
    change ⟪(u.derivative_memLp.toLp _) x, _⟫_ℝ = _
    rw [hx,hy,inner_smul_right,inner_gradient_left]
    simp [mul_comm]
  rw [he1,he2]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((u.property.1.continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
        hφ.continuous).integrable_of_hasCompactSupport
      (hcompact.mul_left)
  · exact (u.property.1.continuous.mul
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (u.property.2.1.mul_right)
  · exact (u.property.1.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hcompact.mul_left)
  · intro x _; exact u.property.1.differentiable (by simp) x
  · intro x _; exact hφ.differentiable (by simp) x

lemma sobolev_integration_by_parts (R : ℝ) (u : ZeroSobolev R)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ) (v : E3) :
    ⟪sobolevValue R u,(smooth_direction_memLp hφ hcompact v).toLp _⟫_ℝ =
      -⟪sobolevDerivative R u,(smooth_smul_memLp hφ hcompact v).toLp _⟫_ℝ := by
  let D : ValueL2 := (smooth_direction_memLp hφ hcompact v).toLp _
  let V : DerivativeL2 := (smooth_smul_memLp hφ hcompact v).toLp _
  have hc : IsClosed {z : SobolevPair | ⟪z.fst,D⟫_ℝ = -⟪z.snd,V⟫_ℝ} :=
    isClosed_eq (((WithLp.fstL 2 ℝ ValueL2 DerivativeL2).continuous).inner continuous_const)
      ((((WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous).inner continuous_const).neg)
  have hs : Set.range (testGraph R) ⊆ {z : SobolevPair | ⟪z.fst,D⟫_ℝ = -⟪z.snd,V⟫_ℝ} := by
    rintro z ⟨w,rfl⟩
    exact test_integration_by_parts w hφ hcompact v
  exact closure_minimal hs hc u.property

lemma sobolev_weak_derivative (R : ℝ) (u : ZeroSobolev R)
    {φ : E3 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ) (v : E3) :
    (∫ x, (sobolevValue R u) x * fderiv ℝ φ x v) =
      -(∫ x, φ x * ⟪(sobolevDerivative R u) x,v⟫_ℝ) := by
  have hh := sobolev_integration_by_parts R u hφ hcompact v
  rw [L2.inner_def,L2.inner_def] at hh
  convert hh using 1
  · apply integral_congr_ae
    filter_upwards [(smooth_direction_memLp hφ hcompact v).coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  · congr 1
    apply integral_congr_ae
    filter_upwards [(smooth_smul_memLp hφ hcompact v).coeFn_toLp] with x hx
    rw [hx,inner_smul_right]

lemma sobolevDerivative_eq_zero_of_value_eq_zero (R : ℝ) (u : ZeroSobolev R)
    (hu : sobolevValue R u = 0) : sobolevDerivative R u = 0 := by
  have hd (v : E3) : ∀ᵐ x ∂(volume : Measure E3), ⟪(sobolevDerivative R u) x,v⟫_ℝ = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((Lp.memLp (sobolevDerivative R u)).inner_const (𝕜:=ℝ) v).locallyIntegrable (by norm_num))
    intro φ hφ hcompact
    have hh := sobolev_weak_derivative R u hφ hcompact v
    have hz : (∫ x, (sobolevValue R u) x * fderiv ℝ φ x v) = 0 := by
      rw [hu]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=(volume:Measure E3))] with x hx
      simp only [hx,Pi.zero_apply,zero_mul]
    rw [hz] at hh
    simpa only [smul_eq_mul,neg_eq_zero] using hh.symm
  have hcoord : ∀ᵐ x ∂(volume : Measure E3), ∀ i : Fin 3,
      ⟪(sobolevDerivative R u) x,coordinateVector i⟫_ℝ = 0 :=
    ae_all_iff.mpr (fun i ↦ hd (coordinateVector i))
  apply Lp.ext
  filter_upwards [hcoord,Lp.coeFn_zero (E:=E3) (p:=2) (μ:=(volume:Measure E3))] with x hx hz
  rw [hz]
  ext i
  simpa [coordinateVector,EuclideanSpace.inner_single_right] using hx i

lemma sobolevValue_injective (R : ℝ) : Function.Injective (sobolevValue R) := by
  intro u v h
  have hu : sobolevValue R (u-v) = 0 := by simp [map_sub,h]
  have hd := sobolevDerivative_eq_zero_of_value_eq_zero R (u-v) hu
  have hz : u-v=0 := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact Prod.ext hu hd
  exact sub_eq_zero.mp hz

def exteriorOperator (R : ℝ) : E3 → E3 →L[ℝ] E3 := by
  classical
  exact (Metric.closedBall (0:E3) R).piecewise (fun _ ↦ 0) (fun _ ↦ ContinuousLinearMap.id ℝ E3)

lemma exteriorOperator_measurable (R : ℝ) :
    AEStronglyMeasurable (exteriorOperator R) (volume : Measure E3) := by
  classical
  exact (measurable_const.piecewise Metric.isClosed_closedBall.measurableSet
    measurable_const).aestronglyMeasurable

lemma exteriorOperator_bound (R : ℝ) (x : E3) : ‖exteriorOperator R x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ Metric.closedBall (0:E3) R
  · simp [exteriorOperator,hx]
  · simp [exteriorOperator,hx]

lemma sobolevDerivative_supported (R : ℝ) (u : ZeroSobolev R) :
    ∀ᵐ x ∂(volume : Measure E3), x ∉ Metric.closedBall (0:E3) R →
      (sobolevDerivative R u) x = 0 := by
  classical
  let A := coefficientCLM (exteriorOperator R) 1 (exteriorOperator_measurable R)
    (exteriorOperator_bound R)
  have hz (w : DirichletTest R) : A w.derivative = 0 := by
    apply Lp.ext
    filter_upwards [(coefficient_memLp (exteriorOperator R) 1
        (exteriorOperator_measurable R) (exteriorOperator_bound R) w.derivative).coeFn_toLp,
      w.derivative_memLp.coeFn_toLp,
      Lp.coeFn_zero (E:=E3) (p:=2) (μ:=(volume:Measure E3))] with x hx hy hzero
    change ((coefficient_memLp (exteriorOperator R) 1
        (exteriorOperator_measurable R) (exteriorOperator_bound R) w.derivative).toLp _) x = _
    rw [hx,hzero]
    change exteriorOperator R x ((w.derivative_memLp.toLp _) x) = 0
    rw [hy]
    by_cases hb : x ∈ Metric.closedBall (0:E3) R
    · simp [exteriorOperator,hb]
    · have hts : x ∉ tsupport (w:E3 → ℝ) := by
        intro hh
        exact hb (Metric.ball_subset_closedBall (w.property.2.2 hh))
      simp [exteriorOperator,hb,gradient,fderiv_of_notMem_tsupport ℝ hts]
  have hc : IsClosed {z : SobolevPair | A z.snd = 0} :=
    isClosed_eq (A.continuous.comp (WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous)
      continuous_const
  have hs : Set.range (testGraph R) ⊆ {z : SobolevPair | A z.snd = 0} := by
    rintro z ⟨w,rfl⟩
    exact hz w
  have hu : A (sobolevDerivative R u) = 0 := closure_minimal hs hc u.property
  have he : ∀ᵐ x ∂(volume : Measure E3),
      (A (sobolevDerivative R u)) x = exteriorOperator R x ((sobolevDerivative R u) x) :=
    (coefficient_memLp (exteriorOperator R) 1 (exteriorOperator_measurable R)
      (exteriorOperator_bound R) (sobolevDerivative R u)).coeFn_toLp
  rw [hu] at he
  filter_upwards [he,Lp.coeFn_zero (E:=E3) (p:=2) (μ:=(volume:Measure E3))] with x hx hzero
  intro hb
  rw [hzero] at hx
  simpa [exteriorOperator,hb] using hx.symm

lemma clippedEnergy_integral_eq (g : SmoothMetric3) (R : ℝ) (D : E3 → E3)
    (v : ZeroSobolev R) :
    (∫ x, ⟪g.clippedEnergyOperator R x (D x),(sobolevDerivative R v) x⟫_ℝ) =
      ∫ x, ⟪g.energyOperator x (D x),(sobolevDerivative R v) x⟫_ℝ := by
  classical
  apply integral_congr_ae
  filter_upwards [sobolevDerivative_supported R v] with x hx
  by_cases hb : x ∈ Metric.closedBall (0:E3) R
  · simp [clippedEnergyOperator,hb]
  · simp [hx hb]

theorem metric_affine_weak_dirichlet (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R)
    {F : E3 → ℝ} (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F) :
    ∃! u : ZeroSobolev R, ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x (gradient F x + (sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ) = 0 := by
  let D := (smooth_gradient_memLp hF hcompact).toLp (gradient F)
  have he (u v : ZeroSobolev R) :
      (∫ x, ⟪g.clippedEnergyOperator R x (D x + (sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ) =
      (∫ x, ⟪g.energyOperator x (gradient F x + (sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ) := by
    rw [clippedEnergy_integral_eq]
    apply integral_congr_ae
    filter_upwards [(smooth_gradient_memLp hF hcompact).coeFn_toLp] with x hx
    change ⟪g.energyOperator x (((smooth_gradient_memLp hF hcompact).toLp _) x + _),_⟫_ℝ = _
    rw [hx]
  simpa only [he] using metric_affine_dirichlet_unique g R hR D

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
