import Mathlib
import OAI.Geometry.BallPacking.Annuli.AnnularChartNormalization

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

def radial (H : AnnularHandleData E M) (b : ℝ) : ManifoldOneForm E M :=
  handlePushforwardOneForm H.chart (cylinderRadialForm b)

def density (H : AnnularHandleData E M) (b : ℝ) : ManifoldTwoForm E M :=
  manifoldWedge (H.radial b) H.dual

theorem density_smooth (H : AnnularHandleData E M) {b : ℝ} (hb : 0<b) (hbw : b<H.width) :
    SmoothTwoForm (H.density b) := by
  have hα := handlePushforwardOneForm_smooth H.chart (band_compact b) (H.band_subset_source hbw)
    (cylinderRadialForm_smooth b) (fun _ hx => cylinderRadialForm_zero hb hx)
  apply manifoldWedge_smooth
  · intro c
    exact (hα c).comp (f := fun y => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)
  · intro c
    exact (H.dual_smooth c).comp (f := fun y => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_pullback (H : AnnularHandleData E M) (b : ℝ) {z : HandleCylinder}
    (hz : z∈H.chart.source) (v w : CylinderModel) :
    H.density b (H.chart z)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z v)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z w)=
      (deriv (intervalClock (-b) b) z.1*H.clock z.2)*cylinderAreaForm z v w := by
  have hα := handlePushforwardOneForm_pullback H.chart (cylinderRadialForm b) hz
  have hαv (u : CylinderModel) := congrArg (fun L : CylinderModel →L[ℝ] ℝ => L u) hα
  simp only [manifoldPullbackOneForm, manifoldMapDifferential,
    cylinderRadialForm_apply] at hαv
  let A : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z
  have hαv' (u : CylinderModel) :
      H.radial b (H.chart z) (A u) = deriv (intervalClock (-b) b) z.1 * u.1 := by
    simpa only [radial] using! hαv u
  have hβv (u : CylinderModel) :
      H.dual (H.chart z) (A u) = H.clock z.2 * circleAngular z.2 u.2 :=
    H.dual_pullback z hz u
  change manifoldWedge (H.radial b) H.dual (H.chart z) (A v) (A w) = _
  rw [manifoldWedge_apply, hαv' v, hαv' w, hβv v, hβv w, cylinderAreaForm_apply]
  ring

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_band_zero (H : AnnularHandleData E M) {b : ℝ} (hb : 0<b)
    {x : M} (hx : x∉H.chart '' band b) : H.density b x=0 := by
  have hz : H.radial b x=0 :=
    handlePushforwardOneForm_zero H.chart (fun _ hy => cylinderRadialForm_zero hb hy) hx
  ext v w
  simp [density,manifoldWedge_apply,hz]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_core_zero (H : AnnularHandleData E M) {b : ℝ} (hb : 0<b) (hbw : b<H.width)
    {x : M} (hx : x∉H.chart '' H.core b) : H.density b x=0 := by
  by_cases hxb : x∈H.chart '' band b
  · obtain ⟨z,hz,rfl⟩ := hxb
    have hzs := H.band_subset_source hbw hz
    have hclk : H.clock z.2=0 := image_eq_zero_of_notMem_tsupport (fun ht => hx ⟨z,⟨hz.1,ht⟩,rfl⟩)
    let A := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) H.chart.symm (H.chart z)
    let B := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart z
    have hBA : B.comp A=ContinuousLinearMap.id ℝ E := by
      have h := handle_mfderiv_symm_comp H.chart.symm (H.chart.map_source hzs)
      change (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart (H.chart.symm (H.chart z))).comp A=_ at h
      erw [H.chart.left_inv hzs] at h
      exact h
    have hi (v : E) : B (A v)=v := congrArg (fun D : E →L[ℝ] E => D v) hBA
    ext v w
    have hp := H.density_pullback b hzs (A v) (A w)
    change H.density b (H.chart z) (B (A v)) (B (A w))=_ at hp
    simpa only [hi,hclk,mul_zero,zero_mul,zero_apply] using hp
  · exact H.density_band_zero hb hxb

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem density_compact (H : AnnularHandleData E M) {b : ℝ} (hb : 0<b) (hbw : b<H.width) :
    HasCompactSupport (H.density b) :=
  HasCompactSupport.intro (H.image_core_compact hbw) (fun _ hx => H.density_core_zero hb hbw hx)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem density_cover (H : AnnularHandleData E M) (b : ℝ) {q : Plane}
    (hq : cylinderCover q∈H.chart.source) (v w : Plane) :
    H.density b (H.chart (cylinderCover q))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (H.chart ∘ cylinderCover) q v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (H.chart ∘ cylinderCover) q w)=
      (deriv (intervalClock (-b) b) q.1*H.clock (circleTurn q.2))*(v.1*w.2-v.2*w.1) := by
  rw [mfderiv_comp q (H.chart.mdifferentiableAt (by simp) hq)
    (cylinderCover_smooth.mdifferentiableAt (by simp))]
  change H.density b (H.chart (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) H.chart (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q w))=_
  erw [H.density_pullback b hq]
  erw [cylinderAreaForm_apply]
  erw [cylinderCover_derivative q v,cylinderCover_derivative q w]
  change (deriv (intervalClock (-b) b) q.1*H.clock (circleTurn q.2))*
    (v.1*circleAngular (circleTurn q.2) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn q.2 w.2)-
     circleAngular (circleTurn q.2) (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn q.2 v.2)*w.1)=_
  erw [circleAngular_unit_pullback,circleAngular_unit_pullback]

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

def cylinderRectangleInverse (z : HandleCylinder) : Plane :=
  (z.1,positiveCircleArgument z.2)

theorem cylinderRectangleInverse_smooth {z : HandleCylinder}
    (hz : z.2∈positiveCircleCoordinate.target) :
    ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,Plane) ∞ cylinderRectangleInverse z := by
  have hg := positiveCircleCoordinate.contMDiffOn_invFun.contMDiffAt
    (positiveCircleCoordinate.open_target.mem_nhds hz)
  exact (contMDiffAt_prod_module_iff _).2
    ⟨cylinder_fst_smooth.contMDiffAt,hg.comp z cylinder_snd_smooth.contMDiffAt⟩

def cylinderRectangle :
    PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) Plane HandleCylinder ∞ where
  toFun := cylinderCover
  invFun := cylinderRectangleInverse
  source := univ ×ˢ Ioo (0:ℝ) 1
  target := univ ×ˢ positiveCircleCoordinate.target
  map_source' _z hz := ⟨mem_univ _,positiveCircleCoordinate.map_source hz.2⟩
  map_target' _z hz := ⟨mem_univ _,positiveCircleCoordinate.map_target hz.2⟩
  left_inv' _z hz := Prod.ext rfl (positiveCircleCoordinate.left_inv hz.2)
  right_inv' _z hz := Prod.ext rfl (positiveCircleCoordinate.right_inv hz.2)
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := isOpen_univ.prod positiveCircleCoordinate.open_target
  contMDiffOn_toFun := cylinderCover_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (cylinderRectangleInverse_smooth hz.2).contMDiffWithinAt

namespace AnnularHandleData
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def densityChart (H : AnnularHandleData Plane M) :
    PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) Plane M ∞ :=
  cylinderRectangle.trans H.chart

@[simp] theorem densityChart_apply (H : AnnularHandleData Plane M) (y : Plane) :
    H.densityChart y=H.chart (cylinderCover y) := rfl

theorem densityChart_source (H : AnnularHandleData Plane M) :
    H.densityChart.source=Ioo (-H.width) H.width ×ˢ Ioo (0:ℝ) 1 := by
  ext y
  change (y∈univ ×ˢ Ioo (0:ℝ) 1 ∧ cylinderCover y∈H.chart.source) ↔ _
  rw [H.source_eq]
  simp only [mem_prod,mem_univ,true_and,and_true,cylinderCover]
  exact and_comm

theorem densityChart_contains (H : AnnularHandleData Plane M) {b : ℝ}
    (hb : b<H.width) : H.chart '' H.core b⊆H.densityChart.target := by
  rintro x ⟨z,hz,rfl⟩
  have ht : z.2∈positiveCircleCoordinate.target := by
    rw [positiveCircleCoordinate_target]
    exact H.clock_support hz.2
  obtain ⟨t,ht,heq⟩ := ht
  have hy : (z.1,t)∈H.densityChart.source := by
    rw [H.densityChart_source]
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,ht⟩
  have hi := H.densityChart.map_source hy
  have hev : H.densityChart (z.1,t)=H.chart z := congrArg H.chart (Prod.ext rfl heq)
  exact hev ▸ hi

end AnnularHandleData

section

theorem torusFirstForm_clock_zero {b : ℝ} (hb : 0<b) {z : HandleTorus}
    (hz : z∉compactHandleBand b) : torusFirstForm (circleClockDensity b) z=0 := by
  have hn : z.1∉circleTurn '' Icc (-b) b := by
    rintro ⟨s,hs,he⟩
    apply hz
    exact ⟨(s,z.2),⟨hs,mem_univ _⟩,Prod.ext he rfl⟩
  have hzero : circleClockDensity b z.1=0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hn (circleClockDensity_tsupport hb hs))
  apply ContinuousLinearMap.ext
  intro v
  simp [torusFirstForm_apply,weightedCircleAngular,hzero]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

def globalHandleRadialForm
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (b : ℝ) : ManifoldOneForm E M :=
  handlePushforwardOneForm e (torusFirstForm (circleClockDensity b))

def globalHandleDensity
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (b : ℝ) (f : Circle → ℝ) : ManifoldTwoForm E M :=
  manifoldWedge (globalHandleRadialForm e b) (globalHandleForm e f)

theorem globalHandleDensity_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {b : ℝ} (hb : 0<b) (hb' : b<1/2) (he : compactHandleBand b⊆e.source)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfs : tsupport (torusHandleForm f)⊆e.source) :
    SmoothTwoForm (globalHandleDensity e b f) := by
  have hα := handlePushforwardOneForm_smooth e (compactHandleBand_isCompact b) he
    (torusFirstForm_smooth (circleClockDensity_smooth hb hb')) (fun _ hx => torusFirstForm_clock_zero hb hx)
  have hβ := (globalHandleForm_properties e hf hfs).1
  apply manifoldWedge_smooth
  · intro c
    exact (hα c).comp (f := fun y => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)
  · intro c
    exact (hβ c).comp (f := fun y => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem globalHandleDensity_zero
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {b : ℝ} (hb : 0<b) (f : Circle → ℝ) {x : M} (hx : x∉e '' compactHandleBand b) :
    globalHandleDensity e b f x=0 := by
  have hz : globalHandleRadialForm e b x=0 :=
    handlePushforwardOneForm_zero e (fun _ hy => torusFirstForm_clock_zero hb hy) hx
  ext v w
  simp [globalHandleDensity,manifoldWedge_apply,hz]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem globalHandleDensity_compact
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    {b : ℝ} (hb : 0<b) (he : compactHandleBand b⊆e.source) (f : Circle → ℝ) :
    HasCompactSupport (globalHandleDensity e b f) := by
  apply HasCompactSupport.intro ((compactHandleBand_isCompact b).image_of_continuousOn
    (e.contMDiffOn.continuousOn.mono he))
  exact fun _ hx => globalHandleDensity_zero e hb f hx

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem globalHandleDensity_pullback
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (b : ℝ) (f : Circle → ℝ) {z : HandleTorus} (hz : z∈e.source) (v w : TorusModel) :
    globalHandleDensity e b f (e z)
      (mfderiv 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) e z v)
      (mfderiv 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) e z w)=torusAnnularDensity b f z v w := by
  have hα := handlePushforwardOneForm_pullback e (torusFirstForm (circleClockDensity b)) hz
  have hβ := handlePushforwardOneForm_pullback e (torusHandleForm f) hz
  have hαv (u : TorusModel) := congrArg (fun L : TorusModel →L[ℝ] ℝ => L u) hα
  have hβv (u : TorusModel) := congrArg (fun L : TorusModel →L[ℝ] ℝ => L u) hβ
  simp only [globalHandleDensity,torusAnnularDensity,manifoldWedge_apply]
  change handlePushforwardOneForm e (torusFirstForm (circleClockDensity b)) (e z) _ *
      handlePushforwardOneForm e (torusHandleForm f) (e z) _ -
    handlePushforwardOneForm e (torusHandleForm f) (e z) _ *
      handlePushforwardOneForm e (torusFirstForm (circleClockDensity b)) (e z) _ = _
  simp only [manifoldPullbackOneForm,manifoldMapDifferential] at hαv hβv
  exact congrArg₂ (·-·) (congrArg₂ (·*·) (hαv v) (hβv w))
    (congrArg₂ (·*·) (hβv v) (hαv w))

omit [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] in
theorem globalHandleDensity_turns
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (b : ℝ) (f : Circle → ℝ) {z : Plane} (hz : torusTurns z∈e.source) (v w : Plane) :
    globalHandleDensity e b f (e (torusTurns z))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (e ∘ torusTurns) z v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (e ∘ torusTurns) z w)=
      circleClockDensity b (circleTurn z.1)*f (circleTurn z.2)*(v.1*w.2-v.2*w.1) := by
  rw [mfderiv_comp z (e.mdifferentiableAt (by simp) hz)
    (torusTurns_smooth.mdifferentiableAt (by simp))]
  exact (globalHandleDensity_pullback e b f hz _ _).trans (torusAnnularDensity_turns b f z v w)

end
section

theorem torusAnnulusMap_derivative (z : HandleCylinder) (v : CylinderModel) :
    mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) torusAnnulusMap z v=
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn z.1 v.1,v.2) := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,
    show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  have hd := mfderiv_prodMk
    (I := (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) (I' := 𝓘(ℝ,CircleModel))
    (I'' := 𝓘(ℝ,CircleModel))
    (f := fun z : HandleCylinder => circleTurn z.1) (g := Prod.snd) (x := z)
    ((circleTurn_smooth.comp contMDiff_fst).mdifferentiableAt (by simp))
    mdifferentiableAt_snd
  change (mfderiv ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel))
    ((𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel))
    (fun x : HandleCylinder => (circleTurn x.1,x.2)) z v)=_
  rw [hd]
  have hfst := mfderiv_comp z (circleTurn_smooth.mdifferentiableAt (by simp))
    (I := (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) (I' := 𝓘(ℝ,ℝ))
    (I'' := 𝓘(ℝ,CircleModel)) (f := (Prod.fst : HandleCylinder → ℝ)) mdifferentiableAt_fst
  change ((mfderiv ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,CircleModel)
    (circleTurn ∘ Prod.fst) z) v,
    (mfderiv ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,CircleModel) Prod.snd z) v)=_
  rw [hfst,mfderiv_fst,mfderiv_snd]
  rfl

theorem torusAnnularDensity_cylinder (b : ℝ) (f : Circle → ℝ)
    {z : HandleCylinder} (hz : z.1∈Ioo (-(1/2):ℝ) (1/2)) (v w : CylinderModel) :
    torusAnnularDensity b f (torusAnnulusMap z)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) torusAnnulusMap z v)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) torusAnnulusMap z w)=
      deriv (intervalClock (-b) b) z.1*f z.2*cylinderAreaForm z v w := by
  have hform (x : HandleTorus) (u₁ u₂ : TorusModel) :
      torusAnnularDensity b f x u₁ u₂ =
        weightedCircleAngular (circleClockDensity b) x.1 u₁.1 *
          weightedCircleAngular f x.2 u₂.2 -
        weightedCircleAngular f x.2 u₁.2 *
          weightedCircleAngular (circleClockDensity b) x.1 u₂.1 := by
    simp only [torusAnnularDensity, manifoldWedge_apply, torusFirstForm_apply,
      torusHandleForm_apply]
  let A : CylinderModel →L[ℝ] TorusModel :=
    mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) torusAnnulusMap z
  let D : ℝ →L[ℝ] CircleModel := mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn z.1
  have hA (u : CylinderModel) : A u = (D u.1, u.2) := torusAnnulusMap_derivative z u
  have hD (g : Circle → ℝ) (u : ℝ) :
      weightedCircleAngular g (circleTurn z.1) (D u) = g (circleTurn z.1) * u :=
    weightedCircleAngular_pullback g z.1 u
  have hf (u : CircleModel) : weightedCircleAngular f z.2 u = f z.2 * circleAngular z.2 u := rfl
  change torusAnnularDensity b f (torusAnnulusMap z) (A v) (A w) = _
  rw [hform, hA v, hA w]
  simp only [torusAnnulusMap, hD, hf, cylinderAreaForm_apply, circleClockDensity_turn hz]
  ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem globalHandleDensity_annular
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) {z : HandleCylinder}
    (hz : z∈(handleAnnularChart e a).source) (v w : CylinderModel) :
    globalHandleDensity e b f (handleAnnularChart e a z)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) z v)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) z w)=
      deriv (intervalClock (-b) b) z.1*f z.2*cylinderAreaForm z v w := by
  change globalHandleDensity e b f (e (torusAnnulusMap z))
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (e ∘ torusAnnulusMap) z v)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (e ∘ torusAnnulusMap) z w)=_
  have hcomp := mfderiv_comp z (f := torusAnnulusMap) (g := (e : HandleTorus → M))
    (e.mdifferentiableAt (by simp) hz.1.2)
    (torusAnnulusMap_smooth.mdifferentiableAt (by simp))
  rw [hcomp]
  exact (globalHandleDensity_pullback e b f hz.1.2 _ _).trans
    (torusAnnularDensity_cylinder b f hz.1.1.1 v w)

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem partial_inverse_oneForm_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {β : ManifoldOneForm E M}
    (hβ : ∀ z∈e.source,ContDiffAt ℝ ∞ (chartOneForm β z) (extChartAt 𝓘(ℝ,E) z z))
    {x : N} (hx : x∈e.target) :
    ContDiffAt ℝ ∞
      (chartOneForm (manifoldPullbackOneForm (E := E) (F := F) (fun _ => β) e.symm 0) x)
      (extChartAt 𝓘(ℝ,F) x x) := by
  have hform := (hβ (e.symm x) (e.map_target hx)).comp
    ((0:ℝ),extChartAt 𝓘(ℝ,E) (e.symm x) (e.symm x)) contDiffAt_snd
  have hp := parameterManifoldPullbackOneForm_contDiffAt (α := fun _ : ℝ => β)
    hform (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hx))
  exact hp.comp (extChartAt 𝓘(ℝ,F) x x) (contDiffAt_const.prodMk contDiffAt_id)

theorem partial_inverse_oneForm_exterior
    (e : PartialDiffeomorph 𝓘(ℝ,E) 𝓘(ℝ,F) M N ∞)
    {β : ManifoldOneForm E M} {Ω : ManifoldTwoForm F N}
    (hβ : ∀ z∈e.source,ContDiffAt ℝ ∞ (chartOneForm β z) (extChartAt 𝓘(ℝ,E) z z))
    (hcurv : ∀ z∈e.source,∀ v w,manifoldExteriorOneForm β z v w=Ω (e z)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e z v) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e z w))
    {x : N} (hx : x∈e.target) :
    manifoldExteriorOneForm
      (manifoldPullbackOneForm (E := E) (F := F) (fun _ => β) e.symm 0) x=Ω x := by
  rw [manifold_pullback_exterior_at (hβ (e.symm x) (e.map_target hx)) (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hx))]
  let A : F →L[ℝ] E := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e.symm x
  let B : E →L[ℝ] F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) e (e.symm x)
  have hAB : B.comp A=ContinuousLinearMap.id ℝ F := handle_mfderiv_symm_comp e.symm hx
  have hcancel (v : F) : B (A v)=v := congrArg (fun D : F →L[ℝ] F => D v) hAB
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change manifoldExteriorOneForm β (e.symm x) (A v) (A w)=Ω x v w
  have he := hcurv (e.symm x) (e.map_target hx) (A v) (A w)
  change manifoldExteriorOneForm β (e.symm x) (A v) (A w)=Ω (e (e.symm x)) (B (A v)) (B (A w)) at he
  rw [hcancel v,hcancel w] at he
  exact he.trans (congrArg (fun y => Ω y v w) (e.right_inv hx))

end
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def handleAnnularClockPrimitive
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) : ManifoldOneForm E M :=
  manifoldPullbackOneForm (E := CylinderModel) (F := E)
    (fun _ => cylinderClockPrimitive (intervalClock (-b) b) f)
    (handleAnnularChart e a).symm 0

theorem handleAnnularClockPrimitive_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    {x : M} (hx : x∈(handleAnnularChart e a).target) :
    ContDiffAt ℝ ∞ (chartOneForm (handleAnnularClockPrimitive e a b f) x)
      (extChartAt 𝓘(ℝ,E) x x) :=
  partial_inverse_oneForm_smooth (handleAnnularChart e a)
    (fun z _ => cylinderClockPrimitive_smoothAt (intervalClock_smooth (-b) b) hf z) hx

theorem handleAnnularClockPrimitive_exterior
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    {x : M} (hx : x∈(handleAnnularChart e a).target) :
    manifoldExteriorOneForm (handleAnnularClockPrimitive e a b f) x=globalHandleDensity e b f x := by
  apply partial_inverse_oneForm_exterior (handleAnnularChart e a)
    (fun z _ => cylinderClockPrimitive_smoothAt (intervalClock_smooth (-b) b) hf z) _ hx
  intro z hz v w
  rw [cylinderClockPrimitive_exterior (intervalClock_smooth (-b) b) hf]
  exact (globalHandleDensity_annular e a b f hz v w).symm

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem handleAnnularClockPrimitive_eq
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) (f : Circle → ℝ) {x : M} (hx : x∈(handleAnnularChart e a).target) :
    handleAnnularClockPrimitive e a b f x=
      intervalClock (-b) b ((handleAnnularChart e a).symm x).1 • globalHandleForm e f x := by
  let c := handleAnnularChart e a
  let z := c.symm x
  let A : E →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) c.symm x
  let B : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c z
  have hAB : B.comp A=ContinuousLinearMap.id ℝ E := handle_mfderiv_symm_comp c.symm hx
  have hc (v : E) : B (A v)=v := congrArg (fun D : E →L[ℝ] E => D v) hAB
  apply ContinuousLinearMap.ext
  intro v
  have hβ := handleAnnularChart_pullback e a f (c.map_target hx) (A v)
  change globalHandleForm e f (c z) (B (A v))=f z.2*circleAngular z.2 (A v).2 at hβ
  rw [hc v,show c z=x from c.right_inv hx] at hβ
  change (intervalClock (-b) b z.1*f z.2)*cylinderAngular z (A v)=
    intervalClock (-b) b z.1*globalHandleForm e f x v
  rw [cylinderAngular_apply,hβ]
  ring

end

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M] in
 theorem chartOneForm_coefficient (f : M → ℝ) (α : ManifoldOneForm E M)
    (c : M) (y : E) : chartOneForm (fun x => f x • α x) c y=
      f ((extChartAt 𝓘(ℝ,E) c).symm y) • chartOneForm α c y := by
  ext v
  rfl

theorem annular_coefficient_smooth_on {U : Set M} (hU : IsOpen U)
    {s : M → ℝ} (hs : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s U)
    {A : P × ℝ → ℝ} (hA : ContDiff ℝ ∞ A) {α : ManifoldOneForm E M}
    (hα : ∀ c,ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    (c : M) : ContDiffOn ℝ ∞
      (fun q : P × E => chartOneForm (fun x => A (q.1,s x) • α x) c q.2)
      (univ ×ˢ ((extChartAt 𝓘(ℝ,E) c).target ∩ (extChartAt 𝓘(ℝ,E) c).symm ⁻¹' U)) := by
  intro q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2.1)
  have hsc : ContDiffAt ℝ ∞ (fun y => s ((extChartAt 𝓘(ℝ,E) c).symm y)) q.2 :=
    ((hs.contMDiffAt (hU.mem_nhds hq.2.2)).comp q.2 hi).contDiffAt
  have hc := hA.contDiffAt.comp q (contDiffAt_fst.prodMk (hsc.comp q contDiffAt_snd))
  have ha := ((hα c).contDiffAt ((isOpen_extChartAt_target c).mem_nhds hq.2.1)).comp q contDiffAt_snd
  have hh := hc.smul ha
  change ContDiffAt ℝ ∞ (fun z : P × E =>
    A (z.1,s ((extChartAt 𝓘(ℝ,E) c).symm z.2)) • chartOneForm α c z.2) q at hh
  simpa only [chartOneForm_coefficient] using hh.contDiffWithinAt

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem annular_inverse_fst_smooth
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) HandleCylinder M ∞) :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun x => (e.symm x).1) e.target := by
  intro x hx
  have hf : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (fun z : HandleCylinder => z.1) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
      modelWithCornersSelf_prod]
    exact contMDiff_fst
  exact (hf.contMDiffAt.comp x (e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds hx))).contMDiffWithinAt

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem image_band_subset_target (D : AnnularHandleData E M) {b : ℝ} (hb : b<D.width) :
    D.chart '' band b⊆D.chart.target := by
  rintro x ⟨z,hz,rfl⟩
  exact D.chart.map_source (D.band_subset_source hb hz)

theorem off_band_inverse (D : AnnularHandleData E M) (b : ℝ) {x : M}
    (hx : x∈D.chart.target) (hn : x∉D.chart '' band b) : (D.chart.symm x).1∉Icc (-b) b := by
  intro hs
  exact hn ⟨D.chart.symm x,⟨hs,mem_univ _⟩,D.chart.right_inv hx⟩

theorem radial_zero (D : AnnularHandleData E M) {b : ℝ} (hb : 0<b)
    {x : M} (hx : x∉D.chart '' band b) : D.radial b x=0 :=
  handlePushforwardOneForm_zero D.chart (fun _ hy => cylinderRadialForm_zero hb hy) hx

theorem radial_pullback (D : AnnularHandleData E M) (b : ℝ) {z : HandleCylinder}
    (hz : z∈D.chart.source) (v : CylinderModel) :
    D.radial b (D.chart z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart z v)=
      deriv (intervalClock (-b) b) z.1*v.1 := by
  have h := handlePushforwardOneForm_pullback D.chart (cylinderRadialForm b) hz
  have hh := congrArg (fun A : CylinderModel →L[ℝ] ℝ => A v) h
  change D.radial b (D.chart z)
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) D.chart z v)=cylinderRadialForm b z v at hh
  exact hh.trans (cylinderRadialForm_apply b z v)

variable [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
theorem radial_smooth (D : AnnularHandleData E M) {b : ℝ} (hb : 0<b) (hbw : b<D.width) :
    SmoothOneFormFamily (fun _ : ℝ => D.radial b) :=
  handlePushforwardOneForm_smooth D.chart (band_compact b) (D.band_subset_source hbw)
    (cylinderRadialForm_smooth b) (fun _ hx => cylinderRadialForm_zero hb hx)

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
