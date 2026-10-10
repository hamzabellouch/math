import OAI.Analysis.HotSpots.BoundaryEnergy
import OAI.Analysis.HotSpots.ClosedChart

namespace OAI

section UniformL3

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StrictHotSpots.L2Limits



lemma unifIntegrable_two_of_three {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hb : ∀ i, eLpNorm (f i) 3 μ ≤ B) :
    UnifIntegrable f 2 μ := by
  apply unifIntegrable_iff'.2
  intro ε hε
  have ht : Tendsto (fun t : ℝ => B * (ENNReal.ofReal t) ^ (1/6 : ℝ)) (𝓝 0) (𝓝 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hB (by norm_num : (0:ℝ)<1/6)).comp
      (by simpa using ENNReal.continuous_ofReal.tendsto (0:ℝ))
  have he : ∀ᶠ t : ℝ in 𝓝 0, B * (ENNReal.ofReal t) ^ (1/6:ℝ) < ε :=
    ht.eventually (eventually_lt_nhds hε)
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ENNReal.ofReal (r/2), ENNReal.ofReal_pos.mpr (half_pos hr),
    fun i s hs hμs => ?_⟩
  have htt : B * (ENNReal.ofReal (r/2)) ^ (1/6:ℝ) < ε :=
    hrb (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
      using (half_lt_self hr))
  calc
    eLpNorm (f i) 2 (μ.restrict s) ≤ eLpNorm (f i) 3 (μ.restrict s) * (μ s)^(1/6:ℝ) := by
      simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
        ENNReal.toReal_ofNat, show (1/(2:ℝ)-1/3) = 1/6 by norm_num] using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s)
          (by norm_num : (2:ℝ≥0∞)≤3) (hf i).restrict)
    _ ≤ B * (ENNReal.ofReal (r/2)) ^ (1/6:ℝ) := by
      gcongr
      exact (eLpNorm_mono_measure (f i) Measure.restrict_le_self).trans (hb i)
    _ ≤ ε := htt.le

end StrictHotSpots.L2Limits
end
end UniformL3

section GreenRowContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma kernel_plane_formula (x y : Plane) : kernel x y =
    Real.log (1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2)/(4*Real.pi) := by
  simp only [kernel,DiskFormula.green,← map_sub,LinearIsometryEquiv.norm_map]

lemma kernel_continuousAt_left {x y : Plane} (hx : x ∈ disk) (hy : y ∈ disk)
    (hxy : x ≠ y) : ContinuousAt (fun z => kernel z y) x := by
  have hx1 : ‖x‖ < 1 := by simpa [disk] using hx
  have hy1 : ‖y‖ < 1 := by simpa [disk] using hy
  have hx2 : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hy2 : 0 ≤ 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hn : ‖x-y‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  have ha : 1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2 ≠ 0 := by positivity
  simp_rw [kernel_plane_formula]
  fun_prop (disch := assumption)

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma row_eq_toLp (x : disk) : row hC hν x =
    (kernel_memLp_weighted hC hν x x.property).toLp (kernel x) := by
  apply Lp.ext
  filter_upwards [(column_memLp hC hν x).coeFn_toLp,
    (kernel_memLp_weighted hC hν x x.property).coeFn_toLp] with y hy hx
  exact hy.trans ((kernel_symm y x).trans hx.symm)



theorem row_continuous [IsFiniteMeasure ν] : Continuous (row hC hν) := by
  apply continuous_iff_seqContinuous.mpr
  intro u x hu
  simp only [Function.comp_def]
  simp_rw [row_eq_toLp hC hν]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => kernel (u n))
    (fun n => kernel_memLp_weighted hC hν _ (u n).property) (kernel x)
    (kernel_memLp_weighted hC hν _ x.property)).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (kernel_memLp_weighted hC hν _ (u n).property).aestronglyMeasurable)
    (kernel_memLp_weighted hC hν _ x.property)
  · obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_weighted hC hν
    exact L2Limits.unifIntegrable_two_of_three
      (fun n => (kernel_memLp_three_weighted hC hν _ (u n).property).aestronglyMeasurable)
      hB (fun n => h _ (u n).property)
  · have hne : ∀ᵐ y ∂ν, y ≠ (x:Plane) :=
      ((volume.restrict disk).ae_ne (x:Plane)).filter_mono
        (Measure.absolutelyContinuous_of_le_smul hν).ae_le
    filter_upwards [ae_mem_disk hν,hne] with y hyd hyx
    exact (kernel_continuousAt_left x.property hyd hyx.symm).tendsto.comp
      ((continuous_subtype_val.tendsto x).comp hu)


lemma green_integral_eq_inner (f : Lp ℝ 2 ν) (x : disk) :
    (∫ y, kernel x y * f y ∂ν) = inner ℝ (row hC hν x) f := by
  rw [row_eq_toLp hC hν,MeasurableL2Kernel.integral_mul_eq_inner
    (kernel_memLp_weighted hC hν x x.property) (Lp.memLp f),Lp.toLp_coeFn]

include hC hν in
lemma green_integral_continuous [IsFiniteMeasure ν] (f : Lp ℝ 2 ν) :
    Continuous (fun x : disk => ∫ y, kernel x y * f y ∂ν) := by
  simp_rw [green_integral_eq_inner hC hν]
  exact (row_continuous hC hν).inner continuous_const

end StrictHotSpots.PlaneGreen
end
end GreenRowContinuous

section BoundaryPoissonTransport

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma angleBoundary_coe (s : AddCircle τ) :
    (angleBoundary s : Plane) = complexIso s.toCircle := by
  induction s using QuotientAddGroup.induction_on with
  | H θ =>
    change complexIso (Circle.exp θ : ℂ) = complexIso (AddCircle.toCircle (θ : AddCircle τ) : ℂ)
    congr 2
    rw [AddCircle.toCircle_apply_mk]
    congr 1
    field_simp

lemma angleBoundary_dist (s t : AddCircle τ) :
    dist (angleBoundary s) (angleBoundary t) = ‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ := by
  rw [Subtype.dist_eq,dist_eq_norm,angleBoundary_coe,angleBoundary_coe,
    ← map_sub,LinearIsometryEquiv.norm_map]



def boundaryAngleData (f : C(Boundary,ℝ)) : C(AddCircle τ,ℂ) :=
  ⟨fun s => (f (angleBoundary s):ℂ),
    Complex.continuous_ofReal.comp (f.continuous.comp angleBoundary.continuous)⟩

@[simp] lemma boundaryAngleData_apply (f : C(Boundary,ℝ)) (s : AddCircle τ) :
    boundaryAngleData f s = (f (angleBoundary s):ℂ) := rfl

lemma boundaryAngleData_lipschitz (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) : Douglas.ChordLipschitz (A:ℝ) (boundaryAngleData f) := by
  intro s t
  simpa only [boundaryAngleData_apply,← Complex.ofReal_sub,Complex.norm_real,
    ← Real.norm_eq_abs,← dist_eq_norm,angleBoundary_dist] using hf.dist_le_mul (angleBoundary s) (angleBoundary t)

lemma integral_boundary_angle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Boundary → E) : (∫ s, f s ∂boundaryMeasure) =
      ∫ s : AddCircle τ, f (angleBoundary s) := by
  change ∫ s, f s ∂Measure.map angleBoundary.toMeasurableEquiv volume = _
  rw [integral_map_equiv]
  rfl

lemma poissonExtension_eq_planePoisson (f : C(Boundary,ℝ)) {x : Plane} (hx : x ∈ disk) :
    poissonExtension f x = Douglas.planePoisson (boundaryAngleData f) x := by
  rw [poissonExtension,integral_boundary_angles]
  unfold Douglas.planePoisson
  rw [Douglas.poissonExtension_re_eq_circleAverage _
    (by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx)]
  unfold Real.circleAverage
  simp_rw [poisson_eq_standard]
  simp only [smul_eq_mul,Pi.mul_apply,mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Douglas.circleDatum_circleMap,boundaryAngleData_apply,Complex.ofReal_re]
  have ha : angleBoundary (θ : AddCircle τ) = circleBoundary (Circle.exp θ) := rfl
  rw [ha]
  change poissonKernel 0 (complexIso.symm x)
      (complexIso.symm (complexIso (Circle.exp θ : ℂ))) * _ =
    poissonKernel 0 (complexIso.symm x) (circleMap 0 1 θ) * _
  simp [circleMap,Circle.coe_exp]


def boundaryPoissonH1 (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) : H1 disk :=
  (Douglas.lipschitz_planePoisson_hasH1Gradient (boundaryAngleData f) A.coe_nonneg
    (boundaryAngleData_lipschitz f hf)).toH1

lemma boundaryPoissonH1_harmonic (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
    SubcriticalExtension.Harmonic (show IsOpen disk from isOpen_ball) (boundaryPoissonH1 f hf) :=
  Douglas.lipschitzPoisson_weak_harmonic (boundaryAngleData f) A.coe_nonneg
    (boundaryAngleData_lipschitz f hf)

lemma boundaryPoissonH1_value_ae (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
    (H1.value (boundaryPoissonH1 f hf) : Plane → ℝ) =ᵐ[volume.restrict disk]
      poissonExtension f := by
  rw [boundaryPoissonH1,H1.value_toH1]
  filter_upwards [(Douglas.lipschitz_planePoisson_hasH1Gradient (boundaryAngleData f)
    A.coe_nonneg (boundaryAngleData_lipschitz f hf)).1.coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with x hx hxd
  exact hx.trans (poissonExtension_eq_planePoisson f hxd).symm

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma boundaryPoissonH1_observe (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    SubcriticalExtension.observe hC hν (boundaryPoissonH1 f hf) =
      poissonL2 hν f.continuous.measurable hB := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value (boundaryPoissonH1 f hf)),
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (boundaryPoissonH1_value_ae f hf),
    (poissonExtension_memLp hν f.continuous.measurable hB).coeFn_toLp] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

end StrictHotSpots.PlaneGreen
end
end BoundaryPoissonTransport

section BoundaryHarmonicEnergy

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma integral_boundary_prod_angle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Boundary × Boundary → E) :
    (∫ st, f st ∂boundaryMeasure.prod boundaryMeasure) =
      ∫ st : AddCircle τ × AddCircle τ, f (angleBoundary st.1,angleBoundary st.2) := by
  rw [boundaryMeasure,Measure.map_prod_map _ _ angleBoundary.continuous.measurable
    angleBoundary.continuous.measurable]
  change (∫ st, f st ∂Measure.map
    (angleBoundary.toMeasurableEquiv.prodCongr angleBoundary.toMeasurableEquiv) volume) = _
  rw [integral_map_equiv]
  rfl

lemma real_complex_inner_quotient (a b : ℝ) (z : ℂ) :
    inner ℝ ((a:ℂ)/z) ((b:ℂ)/z) = a*b/‖z‖^2 := by
  have he (r : ℝ) : (r:ℂ)/z = r • z⁻¹ := by simp [div_eq_mul_inv,Complex.real_smul]
  rw [he,he,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,norm_inv]
  simp only [inv_pow,div_eq_mul_inv]
  ring

lemma boundaryRealCross_geometric (f g : C(Boundary,ℝ)) :
    (1/τ)*Douglas.boundaryRealCross (boundaryAngleData f) (boundaryAngleData g) =
    (1/2:ℝ)*(∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (f z.1-f z.2) (g z.1-g z.2) ∂boundaryMeasure.prod boundaryMeasure) := by
  rw [integral_boundary_prod_angle,Douglas.boundaryRealCross,← integral_const_mul,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Douglas.boundaryDifference,boundaryAngleData_apply,← Complex.ofReal_sub,
    real_complex_inner_quotient,boundaryInteraction_eq_dist,angleBoundary_dist]
  simp only [Real.inner_apply]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring



theorem boundaryPoissonH1_energy (f g : C(Boundary,ℝ)) {A B : ℝ≥0}
    (hf : LipschitzWith A f) (hg : LipschitzWith B g) :
    inner ℝ (H1.grad (boundaryPoissonH1 f hf)) (H1.grad (boundaryPoissonH1 g hg)) =
    (1/2:ℝ)*(∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (f z.1-f z.2) (g z.1-g z.2) ∂boundaryMeasure.prod boundaryMeasure) := by
  exact (Douglas.douglas_lipschitz_bilinear (boundaryAngleData f) (boundaryAngleData g)
    A.coe_nonneg (boundaryAngleData_lipschitz f hf) B.coe_nonneg
    (boundaryAngleData_lipschitz g hg) (fun _ => rfl) (fun _ => rfl)).trans
    (boundaryRealCross_geometric f g)

end StrictHotSpots.PlaneGreen
end
end BoundaryHarmonicEnergy

section BoundaryScalarEnergy

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)



def boundarySolution (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) : H1 disk :=
  SubcriticalExtension.extension diskOpen diskBounded hC hν (boundaryPoissonH1 f hf)

omit [IsFiniteMeasure ν] in
lemma boundarySolution_weak (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
    SubcriticalExtension.WeakPotential diskOpen hC hν (boundarySolution hC hν f hf) := by
  apply SubcriticalExtension.extension_weak diskOpen diskBounded hC hν
    ((weightedIntegralOperator_eq_greenOperator hC hν) ▸ hT)
  exact boundaryPoissonH1_harmonic f hf

omit [IsFiniteMeasure ν] in
lemma boundarySolution_class (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) :
    ∃ v : H10 diskOpen, boundarySolution hC hν f hf-boundaryPoissonH1 f hf=v.val :=
  SubcriticalExtension.extension_difference diskOpen diskBounded hC hν _




theorem boundarySolution_energy (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f g : C(Boundary,ℝ)) {A B : ℝ≥0} (hf : LipschitzWith A f) (hg : LipschitzWith B g) :
    inner ℝ (H1.grad (boundarySolution hC hν f hf)) (H1.grad (boundarySolution hC hν g hg)) -
      inner ℝ (SubcriticalExtension.observe hC hν (boundarySolution hC hν f hf))
        (SubcriticalExtension.observe hC hν (boundarySolution hC hν g hg)) =
      (1/2:ℝ)*(∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
        inner ℝ (f z.1-f z.2) (g z.1-g z.2) ∂boundaryMeasure.prod boundaryMeasure) -
      (∫ z : Boundary × Boundary, fullBoundaryR hC hν z.1 z.2 * f z.1 * g z.2
        ∂boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨M,_,hM⟩ := boundary_continuous_bound f.continuous
  obtain ⟨N,_,hN⟩ := boundary_continuous_bound g.continuous
  have hE := SubcriticalExtension.extension_energy diskOpen diskBounded hC hν
    ((weightedIntegralOperator_eq_greenOperator hC hν) ▸ hT)
    (boundaryPoissonH1 f hf) (boundaryPoissonH1 g hg)
    (boundaryPoissonH1_harmonic f hf) (boundaryPoissonH1_harmonic g hg)
  have hR : inner ℝ (SubcriticalExtension.observe hC hν (boundaryPoissonH1 f hf))
      (BanachResolvent.resolvent (H10.greenOperator diskOpen diskBounded hC hν)
        (SubcriticalExtension.observe hC hν (boundaryPoissonH1 g hg))) =
      ∫ z : Boundary × Boundary, fullBoundaryR hC hν z.1 z.2 * f z.1 * g z.2
        ∂boundaryMeasure.prod boundaryMeasure := by
    rw [boundaryPoissonH1_observe hC hν f hf hM,boundaryPoissonH1_observe hC hν g hg hN,
      ← weightedIntegralOperator_eq_greenOperator hC hν]
    exact (fullBoundaryR_representation hC hν hT f.continuous.measurable
      g.continuous.measurable hM hN).symm
  exact hE.trans (congrArg₂ (fun a b : ℝ => a-b) (boundaryPoissonH1_energy f g hf hg) hR)

end StrictHotSpots.PlaneGreen
end
end BoundaryScalarEnergy

section GreenSolveContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.DirichletOperator
variable {V H K : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
lemma solution_comp (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (L : H →L[ℝ] K) :
    solution B hB (L.comp J) = (solution B hB J).comp L.adjoint := by
  unfold solution
  rw [ContinuousLinearMap.adjoint_comp]
  rfl
end StrictHotSpots.DirichletOperator
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma solve_value_eq_integralOperator (f : Lp ℝ 2 ν) :
    H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν f) =
      integralOperator ((inclusion hC hν).adjoint f) := by
  have he := DirichletOperator.solution_comp (H10.energy diskOpen)
    (H10.energy_coercive diskOpen diskBounded) (H10.value diskOpen) (inclusion hC hν)
  have hev := congrArg (fun L => H10.value diskOpen (L f)) he
  exact hev.trans (congrArg (fun L => L ((inclusion hC hν).adjoint f))
    integralOperator_eq_variationalOperator.symm)



lemma solve_value_ae (f : Lp ℝ 2 ν) :
    (H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν f) : Plane → ℝ)
      =ᵐ[volume.restrict disk] fun x => ∫ y, kernel x y*f y ∂ν := by
  rw [solve_value_eq_integralOperator hC hν]
  filter_upwards [integralOperator_ae ((inclusion hC hν).adjoint f),
    ae_restrict_mem diskOpen.measurableSet] with x hx hxd
  exact hx.trans (integral_adjoint_row hC hν f x hxd)



def boundarySolutionValue [IsFiniteMeasure ν] (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) (x : Plane) : ℝ :=
  poissonExtension f x + ∫ y, kernel x y *
    (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
      (poissonL2 hν f.continuous.measurable hB)) y ∂ν

lemma boundarySolutionValue_eq_fullExtension [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundarySolutionValue hC hν f hB x = fullExtension hC hν f.continuous.measurable hB x := by
  rw [boundarySolutionValue,fullExtension,green_integral_eq_inner hC hν]

lemma poissonExtension_continuousOn (f : C(Boundary,ℝ)) :
    ContinuousOn (poissonExtension f) disk := by
  apply (Douglas.planePoisson_contDiffOn (boundaryAngleData f)).continuousOn.congr
  intro x hx
  exact poissonExtension_eq_planePoisson f hx

lemma boundarySolutionValue_continuousOn [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    ContinuousOn (boundarySolutionValue hC hν f hB) disk := by
  apply (poissonExtension_continuousOn f).add
  exact continuousOn_iff_continuous_domRestrict.mpr (green_integral_continuous hC hν _)

lemma boundarySolution_value_eq [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    H1.value (boundarySolution hC hν f hf) = H1.value (boundaryPoissonH1 f hf) +
      H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν
        (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
          (poissonL2 hν f.continuous.measurable hB))) := by
  have hr : BanachResolvent.resolvent (H10.greenOperator diskOpen diskBounded hC hν)
      (SubcriticalExtension.observe hC hν (boundaryPoissonH1 f hf)) =
      BanachResolvent.resolvent (weightedIntegralOperator hC hν)
        (poissonL2 hν f.continuous.measurable hB) := by
    rw [boundaryPoissonH1_observe hC hν f hf hB,
      ← weightedIntegralOperator_eq_greenOperator hC hν]
  have hv := H1.value.map_add (boundaryPoissonH1 f hf)
    (SubcriticalExtension.solve diskOpen diskBounded hC hν
      (BanachResolvent.resolvent (H10.greenOperator diskOpen diskBounded hC hν)
        (SubcriticalExtension.observe hC hν (boundaryPoissonH1 f hf)))).val
  exact hv.trans (congrArg (fun z => H1.value (boundaryPoissonH1 f hf) +
    H10.value diskOpen (SubcriticalExtension.solve diskOpen diskBounded hC hν z)) hr)

lemma value_add_ae (a b : Lp ℝ 2 (volume.restrict disk))
    (f g : Plane → ℝ) (ha : a =ᵐ[volume.restrict disk] f)
    (hb : b =ᵐ[volume.restrict disk] g) :
    (a+b : Lp ℝ 2 (volume.restrict disk)) =ᵐ[volume.restrict disk] fun x => f x+g x := by
  filter_upwards [Lp.coeFn_add a b,ha,hb] with x h h1 h2
  exact h.trans (congrArg₂ (fun a b : ℝ => a+b) h1 h2)

lemma boundarySolution_value_ae [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (H1.value (boundarySolution hC hν f hf) : Plane → ℝ) =ᵐ[volume.restrict disk]
      boundarySolutionValue hC hν f hB := by
  rw [boundarySolution_value_eq hC hν f hf hB]
  exact value_add_ae _ _ _ _ (boundaryPoissonH1_value_ae f hf)
    (solve_value_ae hC hν _)



theorem boundarySolution_K [IsFiniteMeasure ν]
    (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundarySolutionValue hC hν f hB x =
      ∫ s, fullBoundaryK hC hν x s * f s ∂boundaryMeasure := by
  rw [boundarySolutionValue_eq_fullExtension hC hν]
  exact (fullBoundaryK_representation hC hν hT x f.continuous.measurable hB).symm

end StrictHotSpots.PlaneGreen
end
end GreenSolveContinuous

section BoundarySolutionIdentification

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma boundaryPoissonH1_real_class (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s) :
    ∃ v : H10 diskOpen, hv.toH1-boundaryPoissonH1 f hf=v.val := by
  have ht : ∀ s : AddCircle τ, φ (complexIso s.toCircle) = (boundaryAngleData f s).re := by
    intro s
    simpa only [boundaryAngleData_apply,Complex.ofReal_re,angleBoundary_coe] using hb (angleBoundary s)
  have hm := Douglas.lipschitzPoisson_boundary_class (boundaryAngleData f) A.coe_nonneg
    (boundaryAngleData_lipschitz f hf) hφ hc hv ht
  refine ⟨⟨_,(h10Submodule diskOpen).neg_mem hm⟩,?_⟩
  change hv.toH1-boundaryPoissonH1 f hf = -(boundaryPoissonH1 f hf-hv.toH1)
  abel

variable {ν : Measure Plane} {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)




lemma boundarySolution_eq_of_trace {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν v‖^2 ≤ d*‖H10.grad diskOpen v‖^2)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s)
    (hp : SubcriticalExtension.WeakPotential diskOpen hC hν hv.toH1) :
    boundarySolution hC hν f hf = hv.toH1 := by
  have hn : ‖weightedIntegralOperator hC hν‖ < 1 :=
    (weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1
  exact SubcriticalExtension.weakPotential_unique diskOpen diskBounded hC hν hd1 hsub
    (boundarySolution_weak hC hν hn f hf) hp (boundarySolution_class hC hν f hf)
    (boundaryPoissonH1_real_class f hf hφ hc hv hb)

lemma boundarySolutionValue_eq_of_trace [IsFiniteMeasure ν]
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν v‖^2 ≤ d*‖H10.grad diskOpen v‖^2)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s)
    (hp : SubcriticalExtension.WeakPotential diskOpen hC hν hv.toH1) :
    EqOn (boundarySolutionValue hC hν f hB) φ disk := by
  have he := boundarySolution_value_ae hC hν f hf hB
  rw [boundarySolution_eq_of_trace hC hν hd0 hd1 hsub f hf hφ hc hv hb hp,H1.value_toH1] at he
  exact Measure.eqOn_open_of_ae_eq (he.symm.trans hv.1.coeFn_toLp) diskOpen
    (boundarySolutionValue_continuousOn hC hν f hB) hφ.continuousOn



theorem value_K_of_trace [IsFiniteMeasure ν]
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ v : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν v‖^2 ≤ d*‖H10.grad diskOpen v‖^2)
    (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) {φ : Plane → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ disk) (hc : ContinuousOn φ (closure disk))
    (hv : HasH1Gradient disk φ (gradient φ)) (hb : ∀ s : Boundary, φ s=f s)
    (hp : SubcriticalExtension.WeakPotential diskOpen hC hν hv.toH1) (x : disk) :
    φ x = ∫ s, fullBoundaryK hC hν x s*f s ∂boundaryMeasure := by
  obtain ⟨B,_,hB⟩ := boundary_continuous_bound f.continuous
  have he := boundarySolutionValue_eq_of_trace hC hν hd0 hd1 hsub f hf hB hφ hc hv hb hp x.property
  exact he.symm.trans (boundarySolution_K hC hν
    ((weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1) f hB x)

end StrictHotSpots.PlaneGreen
end
end BoundarySolutionIdentification

section ActualBoundaryDatum

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma boundary_mem_closed (s : Boundary) : (s : Plane) ∈ closure disk := by
  rw [disk, closure_ball (0 : Plane) (by norm_num : (1:ℝ) ≠ 0)]
  exact sphere_subset_closedBall (by simpa only [mem_sphere, dist_zero_right] using s.property)

def datumTrace (w : Plane → ℝ) (hw : ContinuousOn w (closure Ω)) : C(Boundary,ℝ) where
  toFun s := c.pullDatum w s
  continuous_toFun := (c.pullDatum_continuous hw).comp_continuous continuous_subtype_val
    boundary_mem_closed

lemma datumTrace_lipschitz (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ B : ℝ≥0, LipschitzWith B (c.datumTrace w hw.continuousOn) := by
  obtain ⟨B,hB⟩ := c.pullDatum_lipschitz hb hs hw
  refine ⟨B,fun x y => ?_⟩
  exact hB (boundary_mem_closed x) (boundary_mem_closed y)

lemma pullDatum_Poisson_class (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    ∃ v : H10 diskOpen, (c.pullDatum_H1 hb hs hw).toH1 -
      boundaryPoissonH1 (c.datumTrace w hw.continuousOn) hl = v.val :=
  boundaryPoissonH1_real_class (c.datumTrace w hw.continuousOn) hl
    (c.pullDatum_smooth (hw.mono subset_closure)) (c.pullDatum_continuous hw.continuousOn)
    (c.pullDatum_H1 hb hs hw) (fun _ => rfl)

lemma pullDatum_comp_H1 (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    HasH1Gradient disk (w ∘ c.diskMap) (gradient (w ∘ c.diskMap)) := by
  apply (c.pullDatum_H1 hb hs hw).congr
  · filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
    exact c.pullDatum_eq_inner hx
  · filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
    have he : c.pullDatum w =ᶠ[nhds x] w ∘ c.diskMap :=
      eventually_of_mem (diskOpen.mem_nhds hx) (fun _ hy => c.pullDatum_eq_inner hy)
    exact congrArg (InnerProductSpace.toDual ℝ Plane).symm he.fderiv_eq

lemma pullDatum_comp_toH1 (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    (c.pullDatum_comp_H1 hb hs hw).toH1 = (c.pullDatum_H1 hb hs hw).toH1 := by
  apply H1.value_injective diskOpen
  apply Lp.ext
  filter_upwards [(c.pullDatum_comp_H1 hb hs hw).1.coeFn_toLp,
    (c.pullDatum_H1 hb hs hw).1.coeFn_toLp,ae_restrict_mem diskOpen.measurableSet]
    with x hx hy hxd
  exact hx.trans ((c.pullDatum_eq_inner hxd).symm.trans hy.symm)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualBoundaryDatum


end OAI
