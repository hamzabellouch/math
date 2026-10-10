import OAI.Analysis.HotSpots.Dirichlet

namespace OAI

section ConformalCoordinates


noncomputable section
open Set MeasureTheory Complex ComplexConjugate InnerProductSpace
open scoped InnerProductSpace Topology ContDiff
namespace StrictHotSpots.Conformal

abbrev CoordinatePlane := EuclideanSpace ℝ (Fin 2)
def coordinate : ℂ ≃ₗᵢ[ℝ] CoordinatePlane := Complex.orthonormalBasisOneI.repr

def planeMul (a : ℂ) : CoordinatePlane →L[ℝ] CoordinatePlane :=
  coordinate.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).comp
      coordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma planeMul_apply (a : ℂ) (z : CoordinatePlane) :
    planeMul a z = coordinate (a*coordinate.symm z) := by
  simp [planeMul,mul_comm]

lemma planeMul_det (a : ℂ) : (planeMul a).det = ‖a‖^2 := by
  have hh := LinearMap.det_conj
    (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).toLinearMap) coordinate.toLinearEquiv
  change LinearMap.det _ = _
  have he : (planeMul a).toLinearMap =
      (coordinate.toLinearEquiv : ℂ →ₗ[ℝ] CoordinatePlane) ∘ₗ
        ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).toLinearMap ∘ₗ
        (coordinate.toLinearEquiv.symm : CoordinatePlane →ₗ[ℝ] ℂ) := by
    ext z
    rfl
  rw [he,hh]
  simp [LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

lemma plane_gradient_comp {f : CoordinatePlane → CoordinatePlane}
    {w : CoordinatePlane → ℝ} {a : ℂ} {x : CoordinatePlane}
    (hf : HasFDerivAt f (planeMul a) x) (hw : DifferentiableAt ℝ w (f x)) :
    gradient (w ∘ f) x = coordinate (conj a * coordinate.symm (gradient w (f x))) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,(hw.hasFDerivAt.comp x hf).fderiv]
  change fderiv ℝ w (f x) (planeMul a z) = _
  rw [planeMul_apply,← inner_gradient_left]
  have he (g : CoordinatePlane) (v : ℂ) :
      inner ℝ g (coordinate v) = inner ℝ (coordinate.symm g) v := by
    rw [← coordinate.inner_map_map (coordinate.symm g) v, coordinate.apply_symm_apply]
  rw [he,← coordinate.symm.inner_map_map (coordinate _) z,coordinate.symm_apply_apply]
  simp only [Complex.inner, map_mul, conj_conj]
  congr 1
  ring

lemma plane_norm_gradient_comp {f : CoordinatePlane → CoordinatePlane}
    {w : CoordinatePlane → ℝ} {a : ℂ} {x : CoordinatePlane}
    (hf : HasFDerivAt f (planeMul a) x) (hw : DifferentiableAt ℝ w (f x)) :
    ‖gradient (w ∘ f) x‖ = ‖a‖ * ‖gradient w (f x)‖ := by
  rw [plane_gradient_comp hf hw, coordinate.norm_map,norm_mul,norm_conj,
    coordinate.symm.norm_map]

lemma plane_integral_target (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane)
    (d : CoordinatePlane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (g : CoordinatePlane → ℝ) :
    (∫ y in e.target, g y) = ∫ x in e.source, ‖d x‖^2 * g (e x) := by
  have hh := integral_target_eq_integral_abs_det_fderiv_smul volume hd g
  simpa only [planeMul_det,abs_sq, smul_eq_mul] using hh

lemma plane_dirichlet_energy (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane)
    (d : CoordinatePlane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {w : CoordinatePlane → ℝ} (hw : DifferentiableOn ℝ w e.target) :
    (∫ y in e.target, ‖gradient w y‖^2) =
      ∫ x in e.source, ‖gradient (w ∘ e) x‖^2 := by
  rw [plane_integral_target e d hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  dsimp only
  rw [plane_norm_gradient_comp (hd x hx)
    ((hw (e x) (e.map_source hx)).differentiableAt
      (e.open_target.mem_nhds (e.map_source hx))),mul_pow]


def planeChart (e : OpenPartialHomeomorph ℂ ℂ) :
    OpenPartialHomeomorph CoordinatePlane CoordinatePlane :=
  coordinate.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (e.trans coordinate.toHomeomorph.toOpenPartialHomeomorph)

lemma planeChart_source (e : OpenPartialHomeomorph ℂ ℂ) :
    (planeChart e).source = coordinate.symm ⁻¹' e.source := by
  ext x
  simp [planeChart]

lemma planeChart_target (e : OpenPartialHomeomorph ℂ ℂ) :
    (planeChart e).target = coordinate.symm ⁻¹' e.target := by
  ext x
  simp [planeChart]

lemma planeChart_apply (e : OpenPartialHomeomorph ℂ ℂ) (x : CoordinatePlane) :
    planeChart e x = coordinate (e (coordinate.symm x)) := rfl

lemma planeChart_hasFDerivAt {e : OpenPartialHomeomorph ℂ ℂ}
    {x : CoordinatePlane} (hd : DifferentiableAt ℂ e (coordinate.symm x)) :
    HasFDerivAt (planeChart e) (planeMul (deriv e (coordinate.symm x))) x := by
  exact coordinate.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    ((hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp x
      coordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt)

end StrictHotSpots.Conformal
end
end ConformalCoordinates

section CompactChartTransport




noncomputable section
open Set Filter
open scoped Topology ContDiff Classical
namespace CompactChart
variable {E : Type*} [NormedAddCommGroup E]

variable (e : OpenPartialHomeomorph E E)

def transport (f : E → ℝ) : E → ℝ := fun y => if y ∈ e.target then f (e.symm y) else 0

lemma transport_apply {f : E → ℝ} {y : E} (hy : y ∈ e.target) :
    transport e f y = f (e.symm y) := ite_eq_left hy

lemma transport_source (f : E → ℝ) {x : E} (hx : x ∈ e.source) :
    transport e f (e x) = f x := by
  rw [transport_apply e (e.map_source hx),e.left_inv hx]

lemma support_transport_subset {f : E → ℝ} :
    Function.support (transport e f) ⊆ e '' tsupport f := by
  intro y hy
  by_cases hyt : y ∈ e.target
  · refine ⟨e.symm y,subset_tsupport _ ?_,e.right_inv hyt⟩
    simpa only [Function.mem_support,transport_apply e hyt] using hy
  · exact False.elim (hy (ite_eq_right hyt))

lemma compact_image_tsupport {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : IsCompact (e '' tsupport f) :=
  hc.image_of_continuousOn (e.continuousOn.mono hs)

lemma tsupport_transport_subset {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : tsupport (transport e f) ⊆ e '' tsupport f := by
  exact closure_minimal (support_transport_subset e) (compact_image_tsupport e hc hs).isClosed

lemma hasCompactSupport_transport {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : HasCompactSupport (transport e f) :=
  (compact_image_tsupport e hc hs).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_transport_subset e hc hs)

lemma transport_support_target {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : tsupport (transport e f) ⊆ e.target := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := tsupport_transport_subset e hc hs hy
  exact e.map_source (hs hx)

lemma transport_eventuallyEq {f : E → ℝ} {y : E} (hy : y ∈ e.target) :
    transport e f =ᶠ[𝓝 y] f ∘ e.symm := by
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact transport_apply e hz

lemma contDiff_transport [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (transport e f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · exact (hf.contDiffAt.comp y ((he y hy).contDiffAt (e.open_target.mem_nhds hy))).congr_of_eventuallyEq
      (transport_eventuallyEq e hy)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (transport_support_target e hc hs h)))

lemma transport_add (f g : E → ℝ) :
    transport e (f+g) = transport e f+transport e g := by
  funext y
  by_cases hy : y ∈ e.target <;> simp [transport,hy]

lemma transport_smul (c : ℝ) (f : E → ℝ) :
    transport e (c • f) = c • transport e f := by
  funext y
  by_cases hy : y ∈ e.target <;> simp [transport,hy]

lemma transport_comp_eventuallyEq {f : E → ℝ} {x : E} (hx : x ∈ e.source) :
    (transport e f) ∘ e =ᶠ[𝓝 x] f := by
  filter_upwards [e.open_source.mem_nhds hx] with z hz
  exact transport_source e f hz

lemma transport_symm_transport {f : E → ℝ} (hs : Function.support f ⊆ e.source) :
    transport e.symm (transport e f)=f := by
  funext x
  by_cases hx : x ∈ e.source
  · simpa only [transport_apply e.symm hx,e.symm_symm] using transport_source e f hx
  · rw [transport,OpenPartialHomeomorph.symm_target,ite_eq_right hx]
    exact (Function.notMem_support.mp (fun hh => hx (hs hh))).symm

end CompactChart
end
end CompactChartTransport

section ConformalH10Tests


noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

def transportTest : smoothTestSpace e.source →ₗ[ℝ] smoothTestSpace e.target where
  toFun f := ⟨CompactChart.transport e f,
    CompactChart.contDiff_transport e f.property.1 f.property.2.1 f.property.2.2 he,
    CompactChart.hasCompactSupport_transport e f.property.2.1 f.property.2.2,
    CompactChart.transport_support_target e f.property.2.1 f.property.2.2⟩
  map_add' f g := Subtype.ext (CompactChart.transport_add e f g)
  map_smul' c f := Subtype.ext (CompactChart.transport_smul e c f)

lemma test_grad_sq {Ω : Set Plane} (ho : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.grad ho (smoothTestToH10 ho f)‖^2 = ∫ x in Ω, ‖gradient (f : Plane → ℝ) x‖^2 := by
  rw [L2VectorLimits.norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [(test_gradient_memLp (Ω:=Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
  exact congrArg (fun t : Plane => ‖t‖^2) hx

lemma test_value_sq {Ω : Set Plane} (ho : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.value ho (smoothTestToH10 ho f)‖^2 = ∫ x in Ω, ((f : Plane → ℝ) x)^2 := by
  rw [L2Limits.norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [(test_memLp (Ω:=Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
  exact congrArg (fun t : ℝ => t^2) hx

lemma transportTest_grad_sq (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) (f : smoothTestSpace e.source) :
    ‖H10.grad e.open_target (smoothTestToH10 e.open_target (transportTest e he f))‖^2 =
      ‖H10.grad e.open_source (smoothTestToH10 e.open_source f)‖^2 := by
  rw [test_grad_sq,test_grad_sq,plane_dirichlet_energy e d hd
    ((transportTest e he f).property.1.differentiable (by simp)).differentiableOn]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  dsimp only
  congr 2
  change gradient ((CompactChart.transport e f) ∘ e) x = gradient (f : Plane → ℝ) x
  unfold gradient
  rw [(CompactChart.transport_comp_eventuallyEq e (f:=f) hx).fderiv_eq]

lemma transportTest_value_sq (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) (f : smoothTestSpace e.source) :
    ‖H10.value e.open_target (smoothTestToH10 e.open_target (transportTest e he f))‖^2 =
      ∫ x in e.source, ‖d x‖^2 * ((f : Plane → ℝ) x)^2 := by
  rw [test_value_sq,plane_integral_target e d hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  change ‖d x‖^2 * (CompactChart.transport e f (e x))^2 = _
  rw [CompactChart.transport_source e f hx]

private lemma scalar_norm_bound {s t a b C : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hsplit : t^2 = a^2+b^2) (hbsq : b^2 ≤ s^2) (hP : a ≤ C*b) :
    t ≤ (C+1)*s := by
  have hbs : b ≤ s := (sq_le_sq₀ hb hs).mp hbsq
  have ht' : t ≤ a+b := (sq_le_sq₀ ht (add_nonneg ha hb)).mp (by nlinarith)
  calc
    t ≤ a+b := ht'
    _ ≤ C*b+b := by linarith
    _ = (C+1)*b := by ring
    _ ≤ (C+1)*s := mul_le_mul_of_nonneg_left hbs (by linarith)

lemma transportTest_bound (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) :
    ∃ C : ℝ, ∀ f : smoothTestSpace e.source,
      ‖smoothTestToH10 e.open_target (transportTest e he f)‖ ≤
        C * ‖smoothTestToH10 e.open_source f‖ := by
  obtain ⟨C,hC,hP⟩ := H10.poincare e.open_target hb
  refine ⟨C+1,fun f => ?_⟩
  let v : H10 e.open_source := smoothTestToH10 e.open_source f
  let w : H10 e.open_target := smoothTestToH10 e.open_target (transportTest e he f)
  have hs := H10.norm_sq e.open_source v
  have ht := H10.norm_sq e.open_target w
  have heq : ‖H10.grad e.open_target w‖^2 = ‖H10.grad e.open_source v‖^2 :=
    transportTest_grad_sq e he d hd f
  have hp : ‖H10.value e.open_target w‖ ≤ C*‖H10.grad e.open_target w‖ := hP w
  have hle : ‖H10.grad e.open_source v‖^2 ≤ ‖v‖^2 := by
    calc
      ‖H10.grad e.open_source v‖^2 ≤
          ‖H10.value e.open_source v‖^2+‖H10.grad e.open_source v‖^2 :=
        le_add_of_nonneg_left (sq_nonneg _)
      _ = ‖v‖^2 := hs.symm
  exact scalar_norm_bound (norm_nonneg v) (norm_nonneg w)
    (norm_nonneg (H10.value e.open_target w)) (norm_nonneg (H10.grad e.open_target w))
    hC.le ht (heq.le.trans hle) hp

end StrictHotSpots.Conformal
end
end ConformalH10Tests

section ConformalH10





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

def transportH10 : H10 e.open_source →L[ℝ] H10 e.open_target :=
  ((smoothTestToH10 e.open_target).comp (transportTest e he)).extendOfNorm
    (smoothTestToH10 e.open_source)

lemma transportH10_test (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (f : smoothTestSpace e.source) :
    transportH10 e he (smoothTestToH10 e.open_source f) =
      smoothTestToH10 e.open_target (transportTest e he f) :=
  LinearMap.extendOfNorm_eq (dense_smoothTestToH10 e.open_source)
    (transportTest_bound e he d hd hb) f

lemma transportH10_grad_sq (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    ‖H10.grad e.open_target (transportH10 e he v)‖^2 =
      ‖H10.grad e.open_source v‖^2 := by
  have H : (fun v : H10 e.open_source => ‖H10.grad e.open_target (transportH10 e he v)‖^2) =
      (fun v => ‖H10.grad e.open_source v‖^2) := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      (((H10.grad e.open_target).continuous.comp (transportH10 e he).continuous).norm.pow 2)
      ((H10.grad e.open_source).continuous.norm.pow 2)
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (fun w : H10 e.open_target => ‖H10.grad e.open_target w‖^2)
      (transportH10_test e he d hd hb f)).trans (transportTest_grad_sq e he d hd f)
  exact congrFun H v

lemma transportH10_inner_grad (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (v w : H10 e.open_source) :
    inner ℝ (H10.grad e.open_target (transportH10 e he v))
      (H10.grad e.open_target (transportH10 e he w)) =
      inner ℝ (H10.grad e.open_source v) (H10.grad e.open_source w) := by
  have hv := transportH10_grad_sq e he d hd hb v
  have hw := transportH10_grad_sq e he d hd hb w
  have hsum := transportH10_grad_sq e he d hd hb (v+w)
  simp only [map_add,norm_add_sq_real] at hsum
  linarith

lemma transportTest_symm (he' : ContDiffOn ℝ ∞ e e.source)
    (f : smoothTestSpace e.source) :
    transportTest e.symm he' (transportTest e he f)=f := by
  apply Subtype.ext
  exact CompactChart.transport_symm_transport e ((subset_tsupport _).trans f.property.2.2)

lemma transportH10_symm (he' : ContDiffOn ℝ ∞ e e.source)
    (d d' : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hd' : ∀ y ∈ e.target, HasFDerivAt e.symm (planeMul (d' y)) y)
    (hb : Bornology.IsBounded e.target) (hb' : Bornology.IsBounded e.source)
    (v : H10 e.open_source) :
    transportH10 e.symm he' (transportH10 e he v)=v := by
  have H : (transportH10 e.symm he') ∘ (transportH10 e he) = id := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      ((transportH10 e.symm he').continuous.comp (transportH10 e he).continuous) continuous_id
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (transportH10 e.symm he') (transportH10_test e he d hd hb f)).trans
      ((transportH10_test e.symm he' d' hd' hb' (transportTest e he f)).trans
        (congrArg (smoothTestToH10 e.open_source) (transportTest_symm e he he' f)))
  exact congrFun H v



lemma transported_dirichlet (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) {L : ℝ}
    (hD : ∀ v : H10 e.open_target, L*‖H10.value e.open_target v‖^2 ≤
      ‖H10.grad e.open_target v‖^2) (v : H10 e.open_source) :
    L*‖H10.value e.open_target (transportH10 e he v)‖^2 ≤
      ‖H10.grad e.open_source v‖^2 := by
  exact (hD (transportH10 e he v)).trans_eq (transportH10_grad_sq e he d hd hb v)



lemma transported_subcritical (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (hne : e.target.Nonempty) :
    ∃ L : ℝ, 0 < L ∧ firstPositiveNeumannValue e.target < L ∧
      ∀ v : H10 e.open_source,
        L*‖H10.value e.open_target (transportH10 e he v)‖^2 ≤
          ‖H10.grad e.open_source v‖^2 := by
  apply Exists.elim (@H10.subcritical e.target e.open_target hne hb)
  intro L h
  exact Exists.intro L ⟨h.1,h.2.1,transported_dirichlet e he d hd hb h.2.2⟩

end StrictHotSpots.Conformal
end
end ConformalH10

section ConformalMeasure




noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane) (d : CoordinatePlane → ℂ)

def chartMeasure : Measure CoordinatePlane :=
  (volume.restrict e.source).withDensity (fun x => ENNReal.ofReal (‖d x‖^2))

lemma chartMeasure_ac : chartMeasure e d ≪ volume.restrict e.source :=
  withDensity_absolutelyContinuous _ _

lemma chart_aemeasurable : AEMeasurable e (chartMeasure e d) :=
  (e.continuousOn.aemeasurable e.open_source.measurableSet).mono_ac (chartMeasure_ac e d)

lemma map_chartMeasure
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) :
    (chartMeasure e d).map e = volume.restrict e.target := by
  have hh := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure CoordinatePlane)
    e.open_source.measurableSet.nullMeasurableSet
    (fun x hx => (hd x hx).hasFDerivWithinAt) e.injOn
  simpa only [chartMeasure, planeMul_det,abs_sq,OpenPartialHomeomorph.image_source_eq_target] using hh



def measurableChart : CoordinatePlane → CoordinatePlane :=
  (chart_aemeasurable e d).mk e

lemma measurableChart_ae : measurableChart e d =ᵐ[chartMeasure e d] e :=
  (chart_aemeasurable e d).ae_eq_mk.symm

lemma measurableChart_preserving
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) :
    MeasurePreserving (measurableChart e d) (chartMeasure e d) (volume.restrict e.target) := by
  refine ⟨(chart_aemeasurable e d).measurable_mk,?_⟩
  exact (Measure.map_congr (measurableChart_ae e d)).trans (map_chartMeasure e d hd)

def chartPull (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) :
    Lp ℝ 2 (volume.restrict e.target) →ₗᵢ[ℝ] Lp ℝ 2 (chartMeasure e d) :=
  Lp.compMeasurePreservingₗᵢ ℝ (measurableChart e d) (measurableChart_preserving e d hd)

lemma chartPull_ae (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (f : Lp ℝ 2 (volume.restrict e.target)) :
    chartPull e d hd f =ᵐ[chartMeasure e d] f ∘ e := by
  exact (Lp.coeFn_compMeasurePreserving f (measurableChart_preserving e d hd)).trans
    ((measurableChart_ae e d).fun_comp f)

lemma chartPull_test_ae
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {f : CoordinatePlane → ℝ} (hf : MemLp f 2 (volume.restrict e.target)) :
    chartPull e d hd (hf.toLp f) =ᵐ[chartMeasure e d] f ∘ e := by
  apply (chartPull_ae e d hd _).trans
  have hh : (hf.toLp f : CoordinatePlane → ℝ) =ᵐ[(chartMeasure e d).map e] f := by
    rw [map_chartMeasure e d hd]
    exact hf.coeFn_toLp
  exact ae_of_ae_map (chart_aemeasurable e d) hh

lemma ae_chart_source : ∀ᵐ x ∂chartMeasure e d, x ∈ e.source :=
  (chartMeasure_ac e d).ae_le (ae_restrict_mem e.open_source.measurableSet)

end StrictHotSpots.Conformal
end
end ConformalMeasure

section LpDensityClosure





noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace LpDensityClosure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

lemma ae_eq_of_tendsto (hν : ν ≪ μ)
    {f : ℕ → Lp E 2 μ} {g : ℕ → Lp E 2 ν} {u : Lp E 2 μ} {v : Lp E 2 ν}
    (he : ∀ n, (f n : α → E) =ᵐ[ν] (g n : α → E))
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v)) :
    (u : α → E) =ᵐ[ν] (v : α → E) := by
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨ψ,hψ,hψae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hν.ae_le hφae,hψae,ae_all_iff.mpr he] with x hx hx' heq
  apply tendsto_nhds_unique (hx.comp hψ.tendsto_atTop)
  exact hx'.congr' (Filter.Eventually.of_forall (fun n => (heq (φ (ψ n))).symm))

lemma isClosed_graph (hν : ν ≪ μ) :
    IsClosed {fg : Lp E 2 μ × Lp E 2 ν | (fg.1 : α → E) =ᵐ[ν] (fg.2 : α → E)} := by
  apply IsSeqClosed.isClosed
  intro fg uv hfg ht
  exact ae_eq_of_tendsto hν hfg (continuous_fst.tendsto uv |>.comp ht)
    (continuous_snd.tendsto uv |>.comp ht)

lemma ae_eq_of_dense {X Y : Type*} [TopologicalSpace X]
    {j : Y → X} (hj : DenseRange j) (hν : ν ≪ μ)
    {f : X → Lp E 2 μ} {g : X → Lp E 2 ν}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ y, (f (j y) : α → E) =ᵐ[ν] (g (j y) : α → E)) (x : X) :
    (f x : α → E) =ᵐ[ν] (g x : α → E) := by
  have hc : IsClosed {x | (f x : α → E) =ᵐ[ν] (g x : α → E)} :=
    (isClosed_graph hν).preimage (hf.prodMk hg)
  exact closure_minimal (by rintro _ ⟨y,rfl⟩; exact hfg y) hc (hj x)

end LpDensityClosure
end
end LpDensityClosure

section ConformalWeightedValue





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal
variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)
variable (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)


def weightedValue : H10 e.open_source →L[ℝ] Lp ℝ 2 (chartMeasure e d) :=
  (chartPull e d hd).toContinuousLinearMap.comp
    ((H10.value e.open_target).comp (transportH10 e he))

lemma weightedValue_test (hb : Bornology.IsBounded e.target)
    (f : smoothTestSpace e.source) :
    (weightedValue e he d hd (smoothTestToH10 e.open_source f) : Plane → ℝ)
      =ᵐ[chartMeasure e d] f := by
  have ht := transportH10_test e he d hd hb f
  have hp : weightedValue e he d hd (smoothTestToH10 e.open_source f) =
      chartPull e d hd (H10.value e.open_target
        (smoothTestToH10 e.open_target (transportTest e he f))) :=
    congrArg (fun w : H10 e.open_target => chartPull e d hd (H10.value e.open_target w)) ht
  rw [hp]
  have ha := chartPull_test_ae e d hd
    (test_memLp (Ω:=e.target) (transportTest e he f).property.1
      (transportTest e he f).property.2.1)
  apply ha.trans
  filter_upwards [ae_chart_source e d] with x hx
  exact CompactChart.transport_source e f hx



lemma weightedValue_ae (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    (H10.value e.open_source v : Plane → ℝ) =ᵐ[chartMeasure e d]
      (weightedValue e he d hd v : Plane → ℝ) := by
  apply LpDensityClosure.ae_eq_of_dense (dense_smoothTestToH10 e.open_source)
    (chartMeasure_ac e d) (H10.value e.open_source).continuous
    (weightedValue e he d hd).continuous _ v
  intro f
  have hs : (H10.value e.open_source (smoothTestToH10 e.open_source f) : Plane → ℝ)
      =ᵐ[chartMeasure e d] f :=
    (chartMeasure_ac e d).ae_le
      (test_memLp (Ω:=e.source) f.property.1 f.property.2.1).coeFn_toLp
  exact hs.trans (weightedValue_test e he d hd hb f).symm

lemma weightedValue_norm (v : H10 e.open_source) :
    ‖weightedValue e he d hd v‖ =
      ‖H10.value e.open_target (transportH10 e he v)‖ :=
  (chartPull e d hd).norm_map _

include he hd in
lemma value_memLp_chartMeasure (hb : Bornology.IsBounded e.target)
    (v : H10 e.open_source) :
    MemLp (H10.value e.open_source v : Plane → ℝ) 2 (chartMeasure e d) :=
  MemLp.ae_eq (weightedValue_ae e he d hd hb v).symm (Lp.memLp (weightedValue e he d hd v))

include hd in
lemma physical_value_sq (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    ‖H10.value e.open_target (transportH10 e he v)‖^2 =
      ∫ x, (H10.value e.open_source v x)^2 ∂chartMeasure e d := by
  calc
    _ = ‖weightedValue e he d hd v‖^2 :=
      congrArg (fun t : ℝ => t^2) (weightedValue_norm e he d hd v).symm
    _ = ∫ x, (weightedValue e he d hd v x)^2 ∂chartMeasure e d :=
      L2Limits.norm_sq_eq_integral_sq _
    _ = _ := integral_congr_ae ((weightedValue_ae e he d hd hb v).symm.fun_comp
      (fun t : ℝ => t^2))

include he hd in


theorem weighted_subcritical (hb : Bornology.IsBounded e.target)
    (hne : e.target.Nonempty) :
    ∃ L : ℝ, 0 < L ∧ firstPositiveNeumannValue e.target < L ∧
      ∀ v : H10 e.open_source,
        L*(∫ x, (H10.value e.open_source v x)^2 ∂chartMeasure e d) ≤
          ‖H10.grad e.open_source v‖^2 := by
  apply Exists.elim (transported_subcritical e he d hd hb hne)
  intro L h
  refine Exists.intro L ⟨h.1,h.2.1,fun v => ?_⟩
  exact (congrArg (fun t : ℝ => L*t) (physical_value_sq e he d hd hb v)).symm.le.trans (h.2.2 v)

end StrictHotSpots.Conformal
end
end ConformalWeightedValue


end OAI
