import OAI.Analysis.HotSpots.Poisson

namespace OAI

section PoissonContinuous


noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)



def circleDatum (f : C(AddCircle τ,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ sphere 0 1 then
    f ((AddCircle.homeomorphCircle (by positivity : τ ≠ 0)).symm ⟨z,hz⟩)
  else 0

@[simp] lemma circleDatum_toCircle (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    circleDatum f s.toCircle = f s := by
  have hs : (s.toCircle:ℂ) ∈ sphere 0 1 := by
    simp only [mem_sphere_zero_iff_norm,Circle.norm_coe]
  classical
  rw [circleDatum,dite_eq_left hs]
  apply congrArg f
  have he : (⟨(s.toCircle:ℂ),hs⟩ : Circle) =
      (AddCircle.homeomorphCircle (by positivity : τ ≠ 0)) s := by
    rw [AddCircle.homeomorphCircle_apply]
    exact Subtype.ext rfl
  rw [he,Homeomorph.symm_apply_apply]

@[simp] lemma circleDatum_circleMap (f : C(AddCircle τ,ℂ)) (t : ℝ) :
    circleDatum f (circleMap 0 1 t) = f t := by
  rw [circleMap_eq_toCircle,circleDatum_toCircle]

lemma circleDatum_circleIntegrable (f : C(AddCircle τ,ℂ)) :
    CircleIntegrable (circleDatum f) 0 1 := by
  change IntervalIntegrable (fun t : ℝ => circleDatum f (circleMap 0 1 t)) volume 0 τ
  simp only [circleDatum_circleMap]
  exact (f.continuous.comp (AddCircle.continuous_mk' τ)).intervalIntegrable _ _

lemma poisson_angle_continuous (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t) • f t) := by
  have hk := poissonKernel_continuousOn_sphere hz
  have hkc : Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
    hk.comp_continuous (continuous_circleMap 0 1)
      (fun t => circleMap_mem_sphere (0:ℂ) (by norm_num) t)
  exact hkc.smul (f.continuous.comp (AddCircle.continuous_mk' τ))

lemma poissonExtension_eq_circleAverage (f : C(AddCircle τ,ℂ)) (z : ℂ) :
    poissonExtension f z = Real.circleAverage (poissonKernel 0 z • circleDatum f) 0 1 := by
  unfold poissonExtension Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Pi.smul_apply',circleDatum_circleMap]

lemma poissonExtension_re_eq_circleAverage (f : C(AddCircle τ,ℂ))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    (poissonExtension f z).re =
      Real.circleAverage (poissonKernel 0 z • (fun ζ => (circleDatum f ζ).re)) 0 1 := by
  rw [poissonExtension_eq_circleAverage]
  have hi : CircleIntegrable (poissonKernel 0 z • circleDatum f) 0 1 := by
    change IntervalIntegrable (fun t : ℝ =>
      (poissonKernel 0 z • circleDatum f) (circleMap 0 1 t)) volume 0 τ
    simp only [Pi.smul_apply',circleDatum_circleMap]
    exact (poisson_angle_continuous f hz).intervalIntegrable _ _
  have he := Complex.reCLM.circleAverage_comp_comm hi
  refine he.symm.trans (congrArg (fun F : ℂ → ℝ => Real.circleAverage F 0 1) ?_)
  funext ζ
  simp only [Function.comp_apply,Pi.smul_apply',Complex.reCLM_apply,Complex.smul_re,smul_eq_mul]

lemma circleDatum_re_circleIntegrable (f : C(AddCircle τ,ℂ)) :
    CircleIntegrable (fun ζ => (circleDatum f ζ).re) 0 1 := by
  change IntervalIntegrable (fun t : ℝ => (circleDatum f (circleMap 0 1 t)).re) volume 0 τ
  simp only [circleDatum_circleMap]
  exact (Complex.continuous_re.comp (f.continuous.comp (AddCircle.continuous_mk' τ))).intervalIntegrable _ _



theorem poissonExtension_re_harmonic (f : C(AddCircle τ,ℂ)) :
    InnerProductSpace.HarmonicOnNhd (fun z => (poissonExtension f z).re) (ball 0 1) := by
  have hh := PlaneGreen.poissonAverage_harmonic (circleDatum_re_circleIntegrable f)
  intro z hz
  apply (InnerProductSpace.harmonicAt_congr_nhds (f₂ := fun w =>
    Real.circleAverage (poissonKernel 0 w • (fun ζ => (circleDatum f ζ).re)) 0 1) ?_).2 (hh z hz)
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact poissonExtension_re_eq_circleAverage f hw

lemma poissonExtension_re_contDiffOn (f : C(AddCircle τ,ℂ)) :
    ContDiffOn ℝ ∞ (fun z => (poissonExtension f z).re) (ball 0 1) := by
  apply (poissonAverage_contDiffOn (circleDatum_re_circleIntegrable f)).congr
  intro z hz
  exact poissonExtension_re_eq_circleAverage f hz



def planePoisson (f : C(AddCircle τ,ℂ)) (x : Plane) : ℝ :=
  (poissonExtension f (complexIso.symm x)).re

lemma planePoisson_contDiffOn (f : C(AddCircle τ,ℂ)) :
    ContDiffOn ℝ ∞ (planePoisson f) disk := by
  apply (poissonExtension_re_contDiffOn f).comp complexIso.symm.contDiff.contDiffOn
  intro x hx
  simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx

lemma planePoisson_harmonic (f : C(AddCircle τ,ℂ)) :
    InnerProductSpace.HarmonicOnNhd (planePoisson f) disk := by
  intro x hx
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact harmonicAt_comp_linearIsometryEquiv complexIso.symm (poissonExtension_re_harmonic f _ hz)

end StrictHotSpots.Douglas
end
end PoissonContinuous

section PoissonBounds

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma poisson_angle_kernel_nonneg {z : ℂ} (hz : z ∈ ball 0 1) (t : ℝ) :
    0 ≤ poissonKernel 0 z (circleMap 0 1 t) := by
  have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have ht : ‖circleMap (0:ℂ) 1 t‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere (0:ℂ) (by norm_num) t)
  rw [poissonKernel_def,sub_zero,sub_zero,ht,one_pow]
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

lemma poisson_angle_kernel_continuous {z : ℂ} (hz : z ∈ ball 0 1) :
    Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
  (poissonKernel_continuousOn_sphere hz).comp_continuous (continuous_circleMap 0 1)
    (fun t => circleMap_mem_sphere (0:ℂ) (by norm_num) t)

lemma poisson_angle_mass {z : ℂ} (hz : z ∈ ball 0 1) :
    τ⁻¹ * (∫ t : ℝ in 0..τ, poissonKernel 0 z (circleMap 0 1 t)) = 1 := by
  have hc : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => (1:ℝ)) (closedBall 0 1) :=
    fun _ _ => InnerProductSpace.harmonicAt_const _
  have he := hc.circleAverage_poissonKernel_smul hz
  simpa only [Real.circleAverage,Pi.smul_apply',smul_eq_mul,mul_one] using he



theorem poissonExtension_norm_le (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖poissonExtension f z‖ ≤ ‖f‖ := by
  have ht : (0:ℝ) ≤ τ := le_of_lt (by positivity)
  have hi := (poisson_angle_continuous f hz).intervalIntegrable (μ := volume) 0 τ
  have hk := (poisson_angle_kernel_continuous hz).intervalIntegrable (μ := volume) 0 τ
  rw [poissonExtension,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr ht)]
  calc
    _ ≤ τ⁻¹ * (∫ t : ℝ in 0..τ, ‖poissonKernel 0 z (circleMap 0 1 t) • f t‖) :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm ht) (inv_nonneg.mpr ht)
    _ ≤ τ⁻¹ * (∫ t : ℝ in 0..τ, poissonKernel 0 z (circleMap 0 1 t)*‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht)
      apply intervalIntegral.integral_mono ht hi.norm (hk.mul_const ‖f‖)
      intro t
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (poisson_angle_kernel_nonneg hz t)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (poisson_angle_kernel_nonneg hz t)
    _ = ‖f‖ := by
      rw [intervalIntegral.integral_mul_const,← mul_assoc,poisson_angle_mass hz,one_mul]

lemma planePoisson_norm_le (f : C(AddCircle τ,ℂ)) {x : Plane} (hx : x ∈ disk) :
    ‖planePoisson f x‖ ≤ ‖f‖ := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact (Complex.abs_re_le_norm _).trans (poissonExtension_norm_le f hz)

lemma planePoisson_memLp (f : C(AddCircle τ,ℂ)) :
    MemLp (planePoisson f) 2 (volume.restrict disk) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Plane) 1)) :=
    isFiniteMeasure_restrict.mpr (isBounded_ball (x := (0:Plane)) (r := 1)).measure_lt_top.ne
  apply MemLp.of_bound ((planePoisson_contDiffOn f).continuousOn.aestronglyMeasurable measurableSet_ball) ‖f‖
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact planePoisson_norm_le f hx

lemma circleSmooth_sup_norm_le (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    ‖circleSmooth φ f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le (circleSmooth φ f) (norm_nonneg _)).mpr (circleSmooth_norm_le φ f)



theorem circleSmooth_planePoisson_tendsto_L2 {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → ContDiffBump (0:ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : C(AddCircle τ,ℂ)) :
    Tendsto (fun i => (planePoisson_memLp (circleSmooth (φ i) f)).toLp
      (planePoisson (circleSmooth (φ i) f))) l
      (𝓝 ((planePoisson_memLp f).toLp (planePoisson f))) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Plane) 1)) :=
    isFiniteMeasure_restrict.mpr (isBounded_ball (x := (0:Plane)) (r := 1)).measure_lt_top.ne
  apply L2Limits.tendsto_toLp_of_dominated (fun i => planePoisson_memLp (circleSmooth (φ i) f))
    (planePoisson_memLp f) (memLp_const (‖f‖ : ℝ))
  · exact Eventually.of_forall fun i => (ae_restrict_mem measurableSet_ball).mono fun x hx =>
      (planePoisson_norm_le (circleSmooth (φ i) f) hx).trans (circleSmooth_sup_norm_le (φ i) f)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
      simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
    exact Complex.continuous_re.continuousAt.tendsto.comp (circleSmooth_poisson_tendsto hφ f hz)

end StrictHotSpots.Douglas
end
end PoissonBounds

section SmoothPoissonH1

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma poissonExtension_sub (f g : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    poissonExtension (f-g) z = poissonExtension f z-poissonExtension g z := by
  change τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • (f t-g t)) =
    τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • f t) -
      τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • g t)
  simp_rw [smul_sub]
  rw [intervalIntegral.integral_sub ((poisson_angle_continuous f hz).intervalIntegrable _ _)
    ((poisson_angle_continuous g hz).intervalIntegrable _ _),smul_sub]

lemma planePoisson_sub (f g : C(AddCircle τ,ℂ)) {x : Plane} (hx : x ∈ disk) :
    planePoisson (f-g) x = planePoisson f x-planePoisson g x := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact congrArg Complex.re (poissonExtension_sub f g hz)

lemma planePoisson_eq_series (f : C(AddCircle τ,ℂ))
    (h0 : Summable (fun m => ‖fourierCoeff f m‖)) :
    EqOn (planePoisson f) (planeSeries (fourierCoeff f)) disk := by
  intro x hx
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact congrArg Complex.re (poissonExtension_eq_harmonicSeries f h0 hz)


lemma smooth_planePoisson_hasH1Gradient (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    HasH1Gradient disk (planePoisson f) (gradient (planePoisson f)) := by
  have h1 := summable_firstMoment_of_smooth_lift f hf
  have h0 := summable_norm_of_firstMoment h1
  have he := planePoisson_eq_series f h0
  apply (planeSeries_gradient h0 h1).congr
  · filter_upwards [ae_restrict_mem (show MeasurableSet disk from measurableSet_ball)] with x hx
    exact (he hx).symm
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    unfold gradient
    rw [(he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq]


def smoothPoissonH1 (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) : H1 disk :=
  (smooth_planePoisson_hasH1Gradient f hf).toH1

lemma smoothPoissonH1_value (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    H1.value (smoothPoissonH1 f hf) = (planePoisson_memLp f).toLp (planePoisson f) := rfl

lemma smoothPoissonH1_sub (f g : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t))
    (hg : ContDiff ℝ ∞ (fun t : ℝ => g t)) :
    smoothPoissonH1 (f-g) (hf.sub hg) = smoothPoissonH1 f hf-smoothPoissonH1 g hg := by
  apply H1.value_injective (Ω := disk) isOpen_ball
  rw [map_sub,smoothPoissonH1_value,smoothPoissonH1_value,smoothPoissonH1_value]
  rw [← MemLp.toLp_sub]
  apply Lp.ext
  filter_upwards [(planePoisson_memLp (f-g)).coeFn_toLp,
    ((planePoisson_memLp f).sub (planePoisson_memLp g)).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with x h1 h2 hx
  rw [h1,h2]
  exact planePoisson_sub f g hx

lemma lp_norm_sq_eq_integral_norm_sq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}
    (u : Lp E 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma norm_toLp_sq_eq_integral_norm_sq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}
    {u : X → E} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [lp_norm_sq_eq_integral_norm_sq]
  exact integral_congr_ae (hu.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])



lemma smoothPoissonH1_grad_energy_le (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    ‖H1.grad (smoothPoissonH1 f hf)‖^2 ≤ diskEnergy (poissonExtension f) := by
  have h1 := summable_firstMoment_of_smooth_lift f hf
  have h0 := summable_norm_of_firstMoment h1
  have he := planePoisson_eq_series f h0
  change ‖(smooth_planePoisson_hasH1Gradient f hf).2.1.toLp _‖^2 ≤ _
  rw [norm_toLp_sq_eq_integral_norm_sq]
  have hE : (∫ x : Plane in disk, ‖gradient (planePoisson f) x‖^2) =
      ∫ x : Plane in disk, ‖gradient (planeSeries (fourierCoeff f)) x‖^2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    unfold gradient
    rw [(he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq]
  rw [hE]
  have hC : diskEnergy (poissonExtension f) = diskEnergy (harmonicSeries (fourierCoeff f)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    have he' : EqOn (poissonExtension f) (harmonicSeries (fourierCoeff f)) (ball 0 1) :=
      fun z hz => poissonExtension_eq_harmonicSeries f h0 hz
    have hd := (he'.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).fderiv_eq (𝕜:=ℝ)
    dsimp only
    rw [hd]
  rw [hC]
  exact planeSeries_energy_le h0 h1

end StrictHotSpots.Douglas
end
end SmoothPoissonH1

section SmoothWeakGradient

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots





theorem HasH1Gradient.eq_gradient_of_contDiffOn {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {g : Plane → Plane} (hg : HasH1Gradient Ω v g)
    (hv : ContDiffOn ℝ ∞ v Ω) :
    g =ᵐ[volume.restrict Ω] gradient v := by
  have hgc : ContinuousOn (gradient v) Ω :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hv.continuousOn_fderiv_of_isOpen ho (by simp))
  have hi (e : Plane) : ∀ᵐ x ∂volume.restrict Ω, inner ℝ (g x - gradient v x) e = 0 := by
    have hgL := ((hg.2.1.inner_const (𝕜 := ℝ) e).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).locallyIntegrableOn Ω
    have hkc : ContinuousOn (fun x => inner ℝ (gradient v x) e) Ω :=
      hgc.inner continuousOn_const
    have hkL : LocallyIntegrableOn (fun x => inner ℝ (gradient v x) e) Ω
        (volume.restrict Ω) := hkc.locallyIntegrableOn ho.measurableSet
    have hl : LocallyIntegrableOn (fun x => inner ℝ (g x-gradient v x) e) Ω
        (volume.restrict Ω) := by
      have he : (fun x => inner ℝ (g x-gradient v x) e) =
          (fun x => inner ℝ (g x) e) - (fun x => inner ℝ (gradient v x) e) := by
        funext x
        exact inner_sub_left _ _ _
      rw [he]
      exact hgL.sub hkL
    have ht := ho.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (μ := volume.restrict Ω) hl
      (fun φ hφ hc hs => show (∫ x in Ω, φ x • inner ℝ (g x-gradient v x) e) = 0 from by
        have hgφ := hg.2.2 φ hφ hc hs e
        have hkφ := integral_mul_test_fderiv ho hv hφ hc hs e
        have hgi : Integrable (fun x => inner ℝ (g x) e * φ x) (volume.restrict Ω) :=
          (hg.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
        have hki : Integrable (fun x => inner ℝ (gradient v x) e * φ x) (volume.restrict Ω) :=
          (integrable_mul_test ho hkc hφ.continuous hc hs).restrict
        simp only [smul_eq_mul, inner_sub_left, mul_sub]
        rw [integral_sub (by simpa [Pi.mul_apply, mul_comm] using hgi)
          (by simpa [Pi.mul_apply, mul_comm] using hki)]
        simp_rw [mul_comm (φ _)]
        simp only [inner_gradient_left] at *
        linarith)
    filter_upwards [ht, ae_restrict_mem ho.measurableSet] with x hx hxΩ
    exact hx hxΩ
  have hb : ∀ᵐ x ∂volume.restrict Ω, ∀ i : Fin 2,
      inner ℝ (g x-gradient v x) (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 :=
    ae_all_iff.mpr fun i => hi _
  filter_upwards [hb] with x hx
  have hz : g x-gradient v x = 0 := by
    ext i
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right] using hx i
  exact sub_eq_zero.mp hz

lemma HasH1Gradient.actual_of_contDiffOn {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {g : Plane → Plane} (hg : HasH1Gradient Ω v g)
    (hv : ContDiffOn ℝ ∞ v Ω) : HasH1Gradient Ω v (gradient v) :=
  hg.congr (Filter.EventuallyEq.refl _ _) (hg.eq_gradient_of_contDiffOn ho hv)

end StrictHotSpots
end
end SmoothWeakGradient

section LipschitzPoissonH1

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma cauchySeq_of_pair_norm_sq_zero {E : Type*} [NormedAddCommGroup E] {u : ℕ → E}
    (hu : Tendsto (fun p : ℕ × ℕ => ‖u p.1-u p.2‖^2) (atTop ×ˢ atTop) (𝓝 0)) :
    CauchySeq u := by
  have ht : Tendsto (fun p : ℕ × ℕ => ‖u p.1-u p.2‖) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hu
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have h := ht.eventually (gt_mem_nhds hε)
  rw [prod_atTop_atTop_eq] at h
  obtain ⟨⟨N,M⟩,hNM⟩ := eventually_atTop.mp h
  refine ⟨max N M,fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  exact hNM (n,m) ⟨le_trans (le_max_left _ _) hn,le_trans (le_max_right _ _) hm⟩



theorem circleSmooth_cauchy_H1 {φ : ℕ → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) atTop (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    CauchySeq (fun i => smoothPoissonH1 (circleSmooth (φ i) f) (angleSmooth_smooth (φ i) f)) := by
  let u := fun i => smoothPoissonH1 (circleSmooth (φ i) f) (angleSmooth_smooth (φ i) f)
  have hv : Tendsto (fun i => H1.value (u i)) atTop
      (𝓝 ((planePoisson_memLp f).toLp (planePoisson f))) := by
    change Tendsto (fun i => (planePoisson_memLp (circleSmooth (φ i) f)).toLp
      (planePoisson (circleSmooth (φ i) f))) atTop _
    exact circleSmooth_planePoisson_tendsto_L2 hφ f
  have hv0 : Tendsto (fun p : ℕ × ℕ => ‖H1.value (u p.1)-H1.value (u p.2)‖^2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
      ((hv.comp tendsto_fst).sub (hv.comp tendsto_snd)).norm.pow 2
  have hg0 : Tendsto (fun p : ℕ × ℕ => ‖H1.grad (u p.1-u p.2)‖^2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ (circleSmooth_poisson_cauchy hφ f hK h)
    intro p
    rw [show u p.1-u p.2 = smoothPoissonH1
      (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f)
      ((angleSmooth_smooth (φ p.1) f).sub (angleSmooth_smooth (φ p.2) f)) from
        (smoothPoissonH1_sub _ _ _ _).symm]
    exact smoothPoissonH1_grad_energy_le _ _
  apply cauchySeq_of_pair_norm_sq_zero
  have hs := hv0.add hg0
  simpa only [H1.norm_sq,map_sub,add_zero] using hs




theorem hasH1Gradient_of_circleSmooth {φ : ℕ → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) atTop (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    HasH1Gradient disk (planePoisson f) (gradient (planePoisson f)) := by
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete (circleSmooth_cauchy_H1 hφ f hK h)
  have hv : H1.value u = (planePoisson_memLp f).toLp (planePoisson f) := by
    apply tendsto_nhds_unique (H1.value.continuous.continuousAt.tendsto.comp hu)
    change Tendsto (fun i => (planePoisson_memLp (circleSmooth (φ i) f)).toLp
      (planePoisson (circleSmooth (φ i) f))) atTop _
    exact circleSmooth_planePoisson_tendsto_L2 hφ f
  have hw : HasH1Gradient disk (planePoisson f) (H1.grad u) := by
    apply (H1.hasH1Gradient u).congr _ (Filter.EventuallyEq.refl _ _)
    rw [hv]
    exact (planePoisson_memLp f).coeFn_toLp
  exact hw.actual_of_contDiffOn isOpen_ball (planePoisson_contDiffOn f)



def circleApproxBump (n : ℕ) : ContDiffBump (0:ℝ) where
  rIn := (2*((n:ℝ)+1))⁻¹
  rOut := ((n:ℝ)+1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply inv_strictAnti₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

lemma circleApproxBump_rOut_tendsto :
    Tendsto (fun n => (circleApproxBump n).rOut) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)


theorem lipschitz_planePoisson_hasH1Gradient (f : C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    HasH1Gradient disk (planePoisson f) (gradient (planePoisson f)) :=
  hasH1Gradient_of_circleSmooth circleApproxBump_rOut_tendsto f hK h

end StrictHotSpots.Douglas
end
end LipschitzPoissonH1

section PoissonComponents

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace Convolution
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)


theorem circleSmooth_tendsto_H1 {φ : ℕ → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) atTop (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun i => smoothPoissonH1 (circleSmooth (φ i) f) (angleSmooth_smooth (φ i) f))
      atTop (𝓝 (lipschitz_planePoisson_hasH1Gradient f hK h).toH1) := by
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete (circleSmooth_cauchy_H1 hφ f hK h)
  have he : u = (lipschitz_planePoisson_hasH1Gradient f hK h).toH1 := by
    apply H1.value_injective (Ω:=disk) isOpen_ball
    change H1.value u = (planePoisson_memLp f).toLp (planePoisson f)
    apply tendsto_nhds_unique (H1.value.continuous.continuousAt.tendsto.comp hu)
    change Tendsto (fun i => (planePoisson_memLp (circleSmooth (φ i) f)).toLp
      (planePoisson (circleSmooth (φ i) f))) atTop _
    exact circleSmooth_planePoisson_tendsto_L2 hφ f
  simpa only [he] using hu

def poissonRealEnergy (f : C(AddCircle τ,ℂ)) : ℝ :=
  ∫ x : Plane in disk, ‖gradient (planePoisson f) x‖^2

lemma smoothPoissonH1_grad_norm_sq (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    ‖H1.grad (smoothPoissonH1 f hf)‖^2 = poissonRealEnergy f :=
  norm_toLp_sq_eq_integral_norm_sq (smooth_planePoisson_hasH1Gradient f hf).2.1

lemma lipschitzPoissonH1_grad_norm_sq (f : C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    ‖H1.grad (lipschitz_planePoisson_hasH1Gradient f hK h).toH1‖^2 = poissonRealEnergy f :=
  norm_toLp_sq_eq_integral_norm_sq (lipschitz_planePoisson_hasH1Gradient f hK h).2.1

lemma circleSmooth_realEnergy_tendsto {φ : ℕ → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) atTop (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun i => poissonRealEnergy (circleSmooth (φ i) f)) atTop
      (𝓝 (poissonRealEnergy f)) := by
  have ht := (H1.grad.continuous.continuousAt.tendsto.comp (circleSmooth_tendsto_H1 hφ f hK h)).norm.pow 2
  convert ht using 1
  · funext i
    exact (smoothPoissonH1_grad_norm_sq _ _).symm
  · exact congrArg nhds (lipschitzPoissonH1_grad_norm_sq f hK h).symm

lemma poissonExtension_smul (c : ℂ) (f : C(AddCircle τ,ℂ)) (z : ℂ) :
    poissonExtension (c • f : C(AddCircle τ,ℂ)) z = c • poissonExtension f z := by
  change τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • (c • f t)) =
    c • (τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • f t))
  simp_rw [smul_comm _ c]
  rw [intervalIntegral.integral_smul,smul_comm]

lemma circleSmooth_smul (φ : ContDiffBump (0:ℝ)) (c : ℂ) (f : C(AddCircle τ,ℂ)) :
    circleSmooth φ (c • f) = c • circleSmooth φ f := by
  ext s
  induction s using QuotientAddGroup.induction_on with | H t =>
    change (∫ u : ℝ, φ.normed volume u • (c • f ((t-u:ℝ):AddCircle τ))) =
      c • (∫ u : ℝ, φ.normed volume u • f ((t-u:ℝ):AddCircle τ))
    simp_rw [smul_comm _ c]
    rw [integral_smul]



def imagDatum (f : C(AddCircle τ,ℂ)) : C(AddCircle τ,ℂ) := (-Complex.I) • f

lemma imagDatum_chordLipschitz (f : C(AddCircle τ,ℂ)) {K : ℝ} (h : ChordLipschitz K f) :
    ChordLipschitz K (imagDatum f) := by
  intro s t
  change ‖(-Complex.I) • f s-(-Complex.I) • f t‖ ≤ _
  simpa only [← smul_sub,norm_smul,norm_neg,Complex.norm_I,one_mul] using h s t

lemma planePoisson_imagDatum (f : C(AddCircle τ,ℂ)) (x : Plane) :
    planePoisson (imagDatum f) x = (poissonExtension f (complexIso.symm x)).im := by
  unfold planePoisson imagDatum
  rw [poissonExtension_smul]
  simp only [smul_eq_mul,Complex.mul_re,Complex.neg_re,Complex.I_re,
    Complex.I_im,zero_mul,neg_mul,one_mul,zero_sub,neg_neg]

lemma circleSmooth_imagDatum (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    circleSmooth φ (imagDatum f) = imagDatum (circleSmooth φ f) :=
  circleSmooth_smul φ (-Complex.I) f

lemma poissonExtension_im_eq (f : C(AddCircle τ,ℂ)) :
    (fun z => (poissonExtension f z).im) = (fun z => (poissonExtension (imagDatum f) z).re) := by
  funext z
  have h := planePoisson_imagDatum f (complexIso z)
  simpa only [planePoisson,LinearIsometryEquiv.symm_apply_apply] using h.symm

lemma poissonExtension_contDiffOn (f : C(AddCircle τ,ℂ)) :
    ContDiffOn ℝ ∞ (poissonExtension f) (ball 0 1) := by
  have hr := poissonExtension_re_contDiffOn f
  have hi : ContDiffOn ℝ ∞ (fun z => (poissonExtension f z).im) (ball 0 1) := by
    rw [poissonExtension_im_eq]
    exact poissonExtension_re_contDiffOn (imagDatum f)
  have hc := (Complex.ofRealCLM.contDiff.comp_contDiffOn hr).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn hi).mul (contDiffOn_const (c:=Complex.I)))
  exact hc.congr fun z _ => (Complex.re_add_im (poissonExtension f z)).symm

end StrictHotSpots.Douglas
end
end PoissonComponents

section DouglasLipschitzEnergy

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma planeGradient_norm_sq (v : Plane → ℝ) (x : Plane) :
    ‖gradient v x‖^2 = (fderiv ℝ v x (complexIso 1))^2+
      (fderiv ℝ v x (complexIso Complex.I))^2 := by
  have he := (Complex.orthonormalBasisOneI.map complexIso).sum_inner_mul_inner
    (gradient v x) (gradient v x)
  simp only [Fin.sum_univ_two,OrthonormalBasis.map_apply,Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he
  have hi (z : ℂ) : inner ℝ (gradient v x) (complexIso z) = fderiv ℝ v x (complexIso z) :=
    inner_gradient_left (f := v) (x := x) (y := complexIso z)
  have hi' (z : ℂ) : inner ℝ (complexIso z) (gradient v x) = fderiv ℝ v x (complexIso z) := by
    rw [real_inner_comm]
    exact hi z
  simp only [hi,hi',real_inner_self_eq_norm_sq,← sq] at he
  exact he.symm

lemma planePoisson_fderiv (f : C(AddCircle τ,ℂ)) {x : Plane} (hx : x ∈ disk) (v : ℂ) :
    fderiv ℝ (planePoisson f) x (complexIso v) =
      (fderiv ℝ (poissonExtension f) (complexIso.symm x) v).re := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  have hd := ((poissonExtension_contDiffOn f).differentiableOn (by simp)).differentiableAt
    (isOpen_ball.mem_nhds hz)
  have hh := (Complex.reCLM.hasFDerivAt.comp _ hd.hasFDerivAt).comp x
    complexIso.symm.toContinuousLinearEquiv.hasFDerivAt
  rw [show fderiv ℝ (planePoisson f) x = _ from hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply,Complex.reCLM_apply]

lemma planePoisson_im_fderiv (f : C(AddCircle τ,ℂ)) {x : Plane} (hx : x ∈ disk) (v : ℂ) :
    fderiv ℝ (planePoisson (imagDatum f)) x (complexIso v) =
      (fderiv ℝ (poissonExtension f) (complexIso.symm x) v).im := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  have hd := ((poissonExtension_contDiffOn f).differentiableOn (by simp)).differentiableAt
    (isOpen_ball.mem_nhds hz)
  have hh := (Complex.imCLM.hasFDerivAt.comp _ hd.hasFDerivAt).comp x
    complexIso.symm.toContinuousLinearEquiv.hasFDerivAt
  have he : planePoisson (imagDatum f) = fun y => (poissonExtension f (complexIso.symm y)).im :=
    funext (planePoisson_imagDatum f)
  rw [he]
  change fderiv ℝ ((Complex.imCLM ∘ poissonExtension f) ∘ complexIso.symm) x (complexIso v) = _
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply,Complex.imCLM_apply]

lemma poisson_energy_pointwise (f : C(AddCircle τ,ℂ)) {x : Plane} (hx : x ∈ disk) :
    ‖gradient (planePoisson f) x‖^2+‖gradient (planePoisson (imagDatum f)) x‖^2 =
      ‖fderiv ℝ (poissonExtension f) (complexIso.symm x) 1‖^2+
      ‖fderiv ℝ (poissonExtension f) (complexIso.symm x) Complex.I‖^2 := by
  rw [planeGradient_norm_sq,planeGradient_norm_sq,
    planePoisson_fderiv f hx 1,planePoisson_fderiv f hx Complex.I,
    planePoisson_im_fderiv f hx 1,planePoisson_im_fderiv f hx Complex.I]
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring



theorem poisson_energy_components (f : C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    diskEnergy (poissonExtension f) = poissonRealEnergy f+poissonRealEnergy (imagDatum f) := by
  have hR := (lipschitz_planePoisson_hasH1Gradient f hK h).2.1
  have hI := (lipschitz_planePoisson_hasH1Gradient (imagDatum f) hK (imagDatum_chordLipschitz f h)).2.1
  have hiR := (memLp_two_iff_integrable_sq_norm hR.aestronglyMeasurable).mp hR
  have hiI := (memLp_two_iff_integrable_sq_norm hI.aestronglyMeasurable).mp hI
  unfold poissonRealEnergy
  rw [← integral_add hiR hiI]
  calc
    _ = ∫ x : Plane in disk,
        ‖fderiv ℝ (poissonExtension f) (complexIso.symm x) 1‖^2+
          ‖fderiv ℝ (poissonExtension f) (complexIso.symm x) Complex.I‖^2 :=
      (complexIso_disk_preserving.integral_comp complexIso.symm.toHomeomorph.measurableEmbedding
        (fun z : ℂ => ‖fderiv ℝ (poissonExtension f) z 1‖^2+
          ‖fderiv ℝ (poissonExtension f) z Complex.I‖^2)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact (poisson_energy_pointwise f hx).symm




theorem douglas_lipschitz (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    diskEnergy (poissonExtension f) = (1/τ)*boundaryEnergy f := by
  have hR := circleSmooth_realEnergy_tendsto circleApproxBump_rOut_tendsto f hK h
  have hI := circleSmooth_realEnergy_tendsto circleApproxBump_rOut_tendsto
    (imagDatum f) hK (imagDatum_chordLipschitz f h)
  have hsum : Tendsto (fun i => diskEnergy (poissonExtension (circleSmooth (circleApproxBump i) f)))
      atTop (𝓝 (diskEnergy (poissonExtension f))) := by
    rw [poisson_energy_components f hK h]
    have ht := hR.add hI
    convert ht using 1
    funext i
    rw [poisson_energy_components _ hK (circleSmooth_chordLipschitz (circleApproxBump i) f h),
      circleSmooth_imagDatum]
  exact tendsto_nhds_unique hsum (smooth_poisson_energy_tendsto circleApproxBump_rOut_tendsto f hK h)

end StrictHotSpots.Douglas
end
end DouglasLipschitzEnergy

section PoissonBoundaryContinuous

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma chordLipschitz_equicontinuous {ι : Type*} (F : ι → C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ i, ChordLipschitz K (F i)) :
    Equicontinuous (fun i => (F i : AddCircle τ → ℂ)) := by
  intro s
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hc : Continuous (fun t : AddCircle τ => ‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖) := by
    fun_prop
  have he : ∀ᶠ t in 𝓝 s, ‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖ < ε/(K+1) :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp; positivity))
  filter_upwards [he] with t ht i
  rw [dist_comm,dist_eq_norm]
  calc
    _ ≤ K*‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖ := h i t s
    _ ≤ (K+1)*‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := by nlinarith [(lt_div_iff₀ (by linarith : 0 < K+1)).mp ht]

lemma circleSmooth_tendsto_uniform {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0:ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun i => circleSmooth (φ i) f) l (𝓝 f) := by
  have he := chordLipschitz_equicontinuous (fun i => circleSmooth (φ i) f) hK
    (fun i => circleSmooth_chordLipschitz (φ i) f h)
  have ht := (he.tendsto_uniformFun_iff_pi l f).mpr
    (tendsto_pi_nhds.mpr (fun s => circleSmooth_tendsto hφ f s))
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp ht)




def closedPoisson (f : C(AddCircle τ,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ ball 0 1 then poissonExtension f z else circleDatum f z

lemma closedPoisson_interior (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    closedPoisson f z = poissonExtension f z := by
  classical
  exact ite_eq_left hz

lemma closedPoisson_boundary (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    closedPoisson f s.toCircle = f s := by
  classical
  rw [closedPoisson,ite_eq_right (by simp only [mem_ball_zero_iff,Circle.norm_coe,lt_self_iff_false,not_false_eq_true]),circleDatum_toCircle]

lemma exists_toCircle {z : ℂ} (hz : z ∈ sphere 0 1) :
    ∃ s : AddCircle τ, (s.toCircle:ℂ) = z := by
  obtain ⟨s,hs⟩ := (AddCircle.homeomorphCircle (by positivity : τ ≠ 0)).surjective ⟨z,hz⟩
  refine ⟨s,?_⟩
  have he := congrArg (fun c : Circle => (c:ℂ)) hs
  simpa only [AddCircle.homeomorphCircle_apply] using he

lemma smooth_closedPoisson_continuousOn (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    ContinuousOn (closedPoisson f) (closedBall 0 1) := by
  have h0 := summable_norm_of_firstMoment (summable_firstMoment_of_smooth_lift f hf)
  apply (harmonicSeries_continuousOn h0).congr
  intro z hz
  by_cases hi : z ∈ ball 0 1
  · exact (closedPoisson_interior f hi).trans (poissonExtension_eq_harmonicSeries f h0 hi)
  · have hs : z ∈ sphere 0 1 := by
      simp only [mem_ball_zero_iff,not_lt] at hi
      simp only [mem_closedBall_zero_iff] at hz
      exact mem_sphere_zero_iff_norm.mpr (le_antisymm hz hi)
    obtain ⟨s,rfl⟩ := exists_toCircle hs
    rw [closedPoisson_boundary,harmonicSeries_fourier_boundary f h0]

lemma closedPoisson_sub (f g : C(AddCircle τ,ℂ)) (z : ℂ) :
    closedPoisson (f-g) z = closedPoisson f z-closedPoisson g z := by
  classical
  by_cases hi : z ∈ ball 0 1
  · simp only [closedPoisson,ite_eq_left hi]
    exact poissonExtension_sub f g hi
  · simp only [closedPoisson,ite_eq_right hi,circleDatum]
    split_ifs <;> simp

lemma closedPoisson_norm_le (f : C(AddCircle τ,ℂ)) (z : ℂ) :
    ‖closedPoisson f z‖ ≤ ‖f‖ := by
  classical
  by_cases hi : z ∈ ball 0 1
  · rw [closedPoisson_interior f hi]
    exact poissonExtension_norm_le f hi
  · simp only [closedPoisson,ite_eq_right hi,circleDatum]
    split_ifs
    · exact f.norm_coe_le_norm _
    · simp



theorem closedPoisson_continuousOn (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    ContinuousOn (closedPoisson f) (closedBall 0 1) := by
  have ht := ((circleSmooth_tendsto_uniform circleApproxBump_rOut_tendsto f hK h).sub
    (tendsto_const_nhds (x:=f))).norm
  have hzero : Tendsto (fun n : ℕ => ‖circleSmooth (circleApproxBump n) f-f‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using ht
  have hu : TendstoUniformlyOn (fun n : ℕ => closedPoisson (circleSmooth (circleApproxBump n) f))
      (closedPoisson f) atTop (closedBall 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hzero.eventually (Iio_mem_nhds hε)] with n hn z _
    rw [dist_comm,dist_eq_norm,← closedPoisson_sub]
    exact (closedPoisson_norm_le _ z).trans_lt hn
  apply hu.continuousOn
  exact Eventually.frequently (Eventually.of_forall fun n =>
    smooth_closedPoisson_continuousOn _ (angleSmooth_smooth (circleApproxBump n) f))

end StrictHotSpots.Douglas
end
end PoissonBoundaryContinuous

section DouglasLipschitzBilinear

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma poissonExtension_im_zero (f : C(AddCircle τ,ℂ)) (hr : ∀ s, (f s).im = 0)
    {z : ℂ} (hz : z ∈ ball 0 1) : (poissonExtension f z).im = 0 := by
  have hi := (poisson_angle_continuous f hz).intervalIntegrable (μ:=volume) 0 τ
  unfold poissonExtension
  rw [Complex.smul_im]
  change τ⁻¹ • Complex.imCLM (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • f t) = 0
  rw [← Complex.imCLM.intervalIntegral_comp_comm hi]
  simp only [Complex.imCLM_apply,Complex.smul_im,hr,smul_zero,intervalIntegral.integral_zero]

lemma poissonRealEnergy_imag_zero (f : C(AddCircle τ,ℂ)) (hr : ∀ s, (f s).im = 0) :
    poissonRealEnergy (imagDatum f) = 0 := by
  have he : EqOn (planePoisson (imagDatum f)) (fun _ => 0) disk := by
    intro x hx
    rw [planePoisson_imagDatum]
    apply poissonExtension_im_zero f hr
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  calc
    _ = ∫ _ : Plane in disk, (0:ℝ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      dsimp only
      unfold gradient
      rw [(he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq]
      simp
    _ = 0 := by simp


theorem douglas_lipschitz_real (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) (hr : ∀ s, (f s).im = 0) :
    poissonRealEnergy f = (1/τ)*boundaryEnergy f := by
  have he := douglas_lipschitz f hK h
  rw [poisson_energy_components f hK h,poissonRealEnergy_imag_zero f hr,add_zero] at he
  exact he

lemma lipschitzPoissonH1_sub (f g : C(AddCircle τ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hf : ChordLipschitz K f) (hL : 0 ≤ L) (hg : ChordLipschitz L g) :
    (lipschitz_planePoisson_hasH1Gradient (f-g) (add_nonneg hK hL) (chordLipschitz_sub hf hg)).toH1 =
      (lipschitz_planePoisson_hasH1Gradient f hK hf).toH1-
      (lipschitz_planePoisson_hasH1Gradient g hL hg).toH1 := by
  apply H1.value_injective (Ω:=disk) isOpen_ball
  rw [map_sub,H1.value_toH1,H1.value_toH1,H1.value_toH1]
  rw [← MemLp.toLp_sub]
  apply Lp.ext
  filter_upwards [(planePoisson_memLp (f-g)).coeFn_toLp,
    ((planePoisson_memLp f).sub (planePoisson_memLp g)).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with x h1 h2 hx
  rw [h1,h2]
  exact planePoisson_sub f g hx

lemma boundaryDifference_sub (f g : AddCircle τ → ℂ) (p : AddCircle τ × AddCircle τ) :
    boundaryDifference (f-g) p = boundaryDifference f p-boundaryDifference g p := by
  simp only [boundaryDifference,Pi.sub_apply]
  ring

def boundaryRealCross (f g : AddCircle τ → ℂ) : ℝ :=
  ∫ p : AddCircle τ × AddCircle τ, inner ℝ (boundaryDifference f p) (boundaryDifference g p)

lemma boundaryRealCross_integrable (f g : C(AddCircle τ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hf : ChordLipschitz K f) (hL : 0 ≤ L) (hg : ChordLipschitz L g) :
    Integrable (fun p : AddCircle τ × AddCircle τ =>
      inner ℝ (boundaryDifference f p) (boundaryDifference g p)) := by
  apply Integrable.of_bound ((measurable_boundaryDifference f.continuous).inner
    (measurable_boundaryDifference g.continuous)).aestronglyMeasurable (K*L)
  exact ae_of_all _ fun p => (norm_inner_le_norm _ _).trans
    (mul_le_mul (boundaryDifference_bound hK hf p) (boundaryDifference_bound hL hg p)
      (norm_nonneg _) hK)

lemma boundaryEnergy_sub (f g : C(AddCircle τ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hf : ChordLipschitz K f) (hL : 0 ≤ L) (hg : ChordLipschitz L g) :
    boundaryEnergy (f-g : C(AddCircle τ,ℂ)) = boundaryEnergy f-
      2*boundaryRealCross f g+boundaryEnergy g := by
  have hiF := integrable_boundaryDifference_sq hK f.continuous hf
  have hiG := integrable_boundaryDifference_sq hL g.continuous hg
  have hi := boundaryRealCross_integrable f g hK hf hL hg
  unfold boundaryEnergy boundaryRealCross
  change (∫ p : AddCircle τ × AddCircle τ,
    ‖boundaryDifference ((f : AddCircle τ → ℂ)-(g : AddCircle τ → ℂ)) p‖^2) = _
  simp_rw [boundaryDifference_sub,norm_sub_sq_real]
  have he := integral_add (hiF.sub (hi.const_mul 2)) hiG
  have hs := integral_sub hiF (hi.const_mul 2)
  simp only [Pi.sub_apply] at he hs
  rw [he,hs,integral_const_mul]

lemma lipschitzPoisson_grad_sub_norm_sq (f g : C(AddCircle τ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hf : ChordLipschitz K f) (hL : 0 ≤ L) (hg : ChordLipschitz L g) :
    ‖H1.grad (lipschitz_planePoisson_hasH1Gradient f hK hf).toH1-
      H1.grad (lipschitz_planePoisson_hasH1Gradient g hL hg).toH1‖^2 = poissonRealEnergy (f-g) := by
  rw [← H1.grad.map_sub,← lipschitzPoissonH1_sub f g hK hf hL hg]
  exact lipschitzPoissonH1_grad_norm_sq (f-g) (add_nonneg hK hL) (chordLipschitz_sub hf hg)

lemma inner_eq_of_polarization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A B : E) (c x y z w : ℝ) (hA : ‖A‖^2 = c*x) (hB : ‖B‖^2 = c*y)
    (hD : ‖A-B‖^2 = c*z) (hb : z = x-2*w+y) : inner ℝ A B = c*w := by
  have he := norm_sub_sq_real A B
  rw [hA,hB,hD,hb] at he
  nlinarith only [he]

lemma lipschitzPoisson_grad_norm_sq_real (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (hf : ChordLipschitz K f) (hrf : ∀ s, (f s).im = 0) :
    ‖H1.grad (lipschitz_planePoisson_hasH1Gradient f hK hf).toH1‖^2 = (1/τ)*boundaryEnergy f :=
  (lipschitzPoissonH1_grad_norm_sq f hK hf).trans (douglas_lipschitz_real f hK hf hrf)

lemma lipschitzPoisson_grad_sub_norm_sq_real (f g : C(AddCircle τ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hf : ChordLipschitz K f) (hL : 0 ≤ L) (hg : ChordLipschitz L g)
    (hrf : ∀ s, (f s).im = 0) (hrg : ∀ s, (g s).im = 0) :
    ‖H1.grad (lipschitz_planePoisson_hasH1Gradient f hK hf).toH1-
      H1.grad (lipschitz_planePoisson_hasH1Gradient g hL hg).toH1‖^2 =
      (1/τ)*boundaryEnergy (f-g : C(AddCircle τ,ℂ)) := by
  have hrd : ∀ s, ((f-g) s).im = 0 := by
    intro s
    simp only [ContinuousMap.sub_apply,Complex.sub_im,hrf,hrg,sub_zero]
  exact (lipschitzPoisson_grad_sub_norm_sq f g hK hf hL hg).trans
    (douglas_lipschitz_real (f-g) (add_nonneg hK hL) (chordLipschitz_sub hf hg) hrd)



theorem douglas_lipschitz_bilinear (f g : C(AddCircle τ,ℂ)) {K L : ℝ}
    (hK : 0 ≤ K) (hf : ChordLipschitz K f) (hL : 0 ≤ L) (hg : ChordLipschitz L g)
    (hrf : ∀ s, (f s).im = 0) (hrg : ∀ s, (g s).im = 0) :
    inner ℝ (H1.grad (lipschitz_planePoisson_hasH1Gradient f hK hf).toH1)
      (H1.grad (lipschitz_planePoisson_hasH1Gradient g hL hg).toH1) =
      (1/τ)*boundaryRealCross f g := by
  exact inner_eq_of_polarization _ _ (1/τ) (boundaryEnergy f) (boundaryEnergy g)
    (boundaryEnergy (f-g : C(AddCircle τ,ℂ))) (boundaryRealCross f g)
    (lipschitzPoisson_grad_norm_sq_real f hK hf hrf)
    (lipschitzPoisson_grad_norm_sq_real g hL hg hrg)
    (lipschitzPoisson_grad_sub_norm_sq_real f g hK hf hL hg hrf hrg)
    (boundaryEnergy_sub f g hK hf hL hg)

end StrictHotSpots.Douglas
end
end DouglasLipschitzBilinear

section LipschitzPoissonVariational

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace Laplacian
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10 SubcriticalExtension
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma lipschitzPoisson_weak_harmonic (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Harmonic (show IsOpen disk from isOpen_ball) (lipschitz_planePoisson_hasH1Gradient f hK h).toH1 := by
  intro v
  rw [H1.grad_toH1]
  have hp : ∀ x ∈ disk, Laplacian.laplacian (planePoisson f) x = -(0:ℝ)*planePoisson f x := by
    intro x hx
    simpa using (planePoisson_harmonic f x hx).2.self_of_nhds
  simpa using H10.helmholtz_pair (Ω:=disk) isOpen_ball (planePoisson_contDiffOn f)
    (lipschitz_planePoisson_hasH1Gradient f hK h).1
    (lipschitz_planePoisson_hasH1Gradient f hK h).2.1 hp v

def closedPlanePoisson (f : C(AddCircle τ,ℂ)) (x : Plane) : ℝ :=
  (closedPoisson f (complexIso.symm x)).re

lemma closedPlanePoisson_eqOn (f : C(AddCircle τ,ℂ)) :
    EqOn (closedPlanePoisson f) (planePoisson f) disk := by
  intro x hx
  exact congrArg Complex.re (closedPoisson_interior f
    (by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx))

lemma closedPlanePoisson_boundary (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    closedPlanePoisson f (complexIso s.toCircle) = (f s).re := by
  simp only [closedPlanePoisson,LinearIsometryEquiv.symm_apply_apply,closedPoisson_boundary]

lemma closedPlanePoisson_contDiffOn (f : C(AddCircle τ,ℂ)) :
    ContDiffOn ℝ ∞ (closedPlanePoisson f) disk :=
  (planePoisson_contDiffOn f).congr (closedPlanePoisson_eqOn f)

lemma closedPlanePoisson_continuousOn (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    ContinuousOn (closedPlanePoisson f) (closure disk) := by
  apply Complex.continuous_re.comp_continuousOn
  apply (closedPoisson_continuousOn f hK h).comp complexIso.symm.continuous.continuousOn
  intro x hx
  simpa only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
    mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx

lemma closedPlanePoisson_hasH1Gradient (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    HasH1Gradient disk (closedPlanePoisson f) (gradient (closedPlanePoisson f)) := by
  apply (lipschitz_planePoisson_hasH1Gradient f hK h).congr
  · exact (ae_restrict_mem measurableSet_ball).mono (fun x hx => (closedPlanePoisson_eqOn f hx).symm)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    unfold gradient
    rw [((closedPlanePoisson_eqOn f).eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq]

lemma closedPlanePoisson_toH1 (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    (closedPlanePoisson_hasH1Gradient f hK h).toH1 =
      (lipschitz_planePoisson_hasH1Gradient f hK h).toH1 := by
  apply H1.value_injective (Ω:=disk) isOpen_ball
  rw [H1.value_toH1,H1.value_toH1]
  apply Lp.ext
  filter_upwards [(closedPlanePoisson_hasH1Gradient f hK h).1.coeFn_toLp,
    (lipschitz_planePoisson_hasH1Gradient f hK h).1.coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with x h1 h2 hx
  rw [h1,h2]
  exact closedPlanePoisson_eqOn f hx




theorem lipschitzPoisson_boundary_class (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f)
    {φ : Plane → ℝ} (hφ : ContDiffOn ℝ ∞ φ disk)
    (hc : ContinuousOn φ (closure disk)) (hv : HasH1Gradient disk φ (gradient φ))
    (hb : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (f s).re) :
    (lipschitz_planePoisson_hasH1Gradient f hK h).toH1-hv.toH1 ∈
      h10Submodule (show IsOpen disk from isOpen_ball) := by
  let hu := closedPlanePoisson_hasH1Gradient f hK h
  have hs := closedPlanePoisson_contDiffOn f
  have hsub : HasH1Gradient disk (closedPlanePoisson f-φ) (gradient (closedPlanePoisson f-φ)) := by
    apply (hu.sub hv).congr (ae_of_all _ (fun _ => rfl))
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [gradient,Pi.sub_apply]
    rw [fderiv_sub ((hs.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      ((hφ.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)),map_sub]
  have hz : ∀ x ∈ frontier disk, (closedPlanePoisson f-φ) x = 0 := by
    intro x hx
    have hn : complexIso.symm x ∈ sphere (0:ℂ) 1 := by
      simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
        mem_sphere_zero_iff_norm,LinearIsometryEquiv.norm_map] using hx
    obtain ⟨s,hs⟩ := exists_toCircle hn
    have hxc : complexIso s.toCircle = x := by rw [hs]; exact complexIso.apply_symm_apply x
    rw [← hxc]
    exact sub_eq_zero.mpr ((closedPlanePoisson_boundary f s).trans (hb s).symm)
  have hm := interior_smooth_zero_trace_memH10 (Ω:=disk) isOpen_ball (hs.sub hφ)
    ((closedPlanePoisson_continuousOn f hK h).sub hc) hsub isBounded_ball hz
  have he : hu.toH1-hv.toH1 = hsub.toH1 := by
    apply H1.value_injective (Ω:=disk) isOpen_ball
    rw [map_sub,H1.value_toH1,H1.value_toH1,H1.value_toH1]
    apply Lp.ext
    filter_upwards [hu.1.coeFn_toLp,hv.1.coeFn_toLp,hsub.1.coeFn_toLp,
      Lp.coeFn_sub (hu.1.toLp _) (hv.1.toLp _)] with x hux hvx hsx hdiff
    rw [hdiff,Pi.sub_apply,hux,hvx,hsx]
    rfl
  rw [← he] at hm
  change (closedPlanePoisson_hasH1Gradient f hK h).toH1-hv.toH1 ∈ _ at hm
  rw [closedPlanePoisson_toH1 f hK h] at hm
  exact hm

theorem lipschitzPoisson_eq_harmonicLift (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f)
    {φ : Plane → ℝ} (hφ : ContDiffOn ℝ ∞ φ disk)
    (hc : ContinuousOn φ (closure disk)) (hv : HasH1Gradient disk φ (gradient φ))
    (hb : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (f s).re) :
    (lipschitz_planePoisson_hasH1Gradient f hK h).toH1 =
      harmonicLift (show IsOpen disk from isOpen_ball) isBounded_ball hv.toH1 := by
  apply harmonicLift_unique (Ω:=disk) isOpen_ball isBounded_ball _ _
    (lipschitzPoisson_weak_harmonic f hK h)
  exact ⟨⟨_,lipschitzPoisson_boundary_class f hK h hφ hc hv hb⟩,rfl⟩

end StrictHotSpots.Douglas
end
end LipschitzPoissonVariational

end OAI
