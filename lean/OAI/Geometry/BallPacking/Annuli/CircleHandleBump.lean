import Mathlib
import OAI.Geometry.BallPacking.Annuli.BaseHorizontalForms

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem circle_oneForm_closed (α : ManifoldOneForm CircleModel Circle) (z : Circle) :
    manifoldExteriorOneForm α z=0 := by
  let e : CircleModel := EuclideanSpace.single 0 1
  have he (v : CircleModel) : v=(v 0) • e := by
    ext i
    fin_cases i
    simp [e]
  have hz := manifoldExteriorOneForm_skew α z e e
  have hzero : manifoldExteriorOneForm α z e e=0 := by linarith
  ext v w
  rw [he v,he w]
  simp only [map_smul,smul_apply,smul_eq_mul,hzero,mul_zero,zero_apply]

def weightedCircleAngular (f : Circle → ℝ) (z : Circle) : CircleModel →L[ℝ] ℝ := f z • circleAngular z

theorem weightedCircleAngular_chart (f : Circle → ℝ) (c : Circle) (y : CircleModel) :
    chartOneForm (weightedCircleAngular f) c y=
      f ((extChartAt 𝓘(ℝ,CircleModel) c).symm y) • chartOneForm circleAngular c y := by
  ext v
  rfl

theorem weightedCircleAngular_smooth {f : Circle → ℝ}
    (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (c : Circle) :
    ContDiffOn ℝ ∞ (chartOneForm (weightedCircleAngular f) c)
      (extChartAt 𝓘(ℝ,CircleModel) c).target := by
  have he : chartOneForm (weightedCircleAngular f) c =
      fun y => f ((extChartAt 𝓘(ℝ,CircleModel) c).symm y) • chartOneForm circleAngular c y :=
    funext (weightedCircleAngular_chart f c)
  rw [he]
  intro y hy
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,CircleModel)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,CircleModel)) c).mem_nhds hy)
  have hh : ContDiffAt ℝ ∞ (fun u => f ((extChartAt 𝓘(ℝ,CircleModel) c).symm u)) y :=
    (hf.contMDiffAt.comp y hi).contDiffAt
  exact (hh.smul ((circleAngular_smooth c).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,CircleModel)) c).mem_nhds hy))).contDiffWithinAt

@[simp] theorem weightedCircleAngular_pullback (f : Circle → ℝ) (t v : ℝ) :
    weightedCircleAngular f (circleTurn t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn t v)=f (circleTurn t)*v := by
  change f (circleTurn t)*circleAngular (circleTurn t) _=_
  rw [circleAngular_unit_pullback]

theorem exists_normalized_circle_bump {U : Set Circle}
    (hU : U ∈ 𝓝 (circleTurn (1/2))) :
    ∃ f : Circle → ℝ,ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f ∧
      (∀ z,0≤f z) ∧ tsupport f ⊆ U ∧
      (∫ t in (0:ℝ)..1,f (circleTurn t))=1 ∧
      0<f (circleTurn (1/2)) := by
  obtain ⟨b,_,hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := 𝓘(ℝ,CircleModel)) (circleTurn (1/2))).mem_iff.mp hU
  let J := ∫ t in (0:ℝ)..1,b (circleTurn t)
  have hc : Continuous (fun t : ℝ => b (circleTurn t)) :=
    b.continuous.comp circleTurn_smooth.continuous
  have hJ : 0<J := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => (0:ℝ)) (g := fun t => b (circleTurn t))
      (by norm_num : (0:ℝ)<1) continuousOn_const hc.continuousOn
      (fun _ _ => b.nonneg) ⟨1/2,by norm_num,by rw [b.eq_one]; norm_num⟩
    simpa only [intervalIntegral.integral_zero] using h
  let f : Circle → ℝ := fun z => J⁻¹*b z
  have hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f :=
    contMDiff_const.mul b.contMDiff
  have hsupp : support f ⊆ support b := by
    intro z hz
    show b z≠0
    intro hz0
    apply hz
    simp only [f,hz0,mul_zero]
  refine ⟨f,hf,(fun z => mul_nonneg (inv_nonneg.mpr hJ.le) b.nonneg),
    (closure_mono hsupp).trans hb,?_,?_⟩
  · change (∫ t in (0:ℝ)..1,J⁻¹*b (circleTurn t))=1
    rw [intervalIntegral.integral_const_mul,inv_mul_cancel₀ hJ.ne']
  · change 0<J⁻¹*b (circleTurn (1/2))
    rw [b.eq_one,mul_one]
    exact inv_pos.mpr hJ


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

abbrev TorusModel := CircleModel × CircleModel
abbrev HandleTorus := Circle × Circle

instance torus_chartedSpace : ChartedSpace TorusModel HandleTorus :=
  prodChartedSpace CircleModel Circle CircleModel Circle

instance torus_manifold : IsManifold 𝓘(ℝ,TorusModel) ∞ HandleTorus := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact IsManifold.prod Circle Circle

theorem torus_snd_smooth : ContMDiff 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
    (Prod.snd : HandleTorus → Circle) := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact contMDiff_snd

def torusHandleForm (f : Circle → ℝ) : ManifoldOneForm TorusModel HandleTorus :=
  manifoldPullbackOneForm (fun _ => weightedCircleAngular f) Prod.snd 0

@[simp] theorem torusHandleForm_apply (f : Circle → ℝ) (z : HandleTorus) (v : TorusModel) :
    torusHandleForm f z v = weightedCircleAngular f z.2 v.2 := by
  simp only [torusHandleForm,manifoldPullbackOneForm,manifoldMapDifferential]
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,mfderiv_snd]
  rfl

theorem torusHandleForm_smooth {f : Circle → ℝ}
    (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (c : HandleTorus) :
    ContDiffOn ℝ ∞ (chartOneForm (torusHandleForm f) c)
      (extChartAt 𝓘(ℝ,TorusModel) c).target := by
  have hα : ∀ b : Circle, ContDiffOn ℝ ∞
      (fun p : ℝ × CircleModel => chartOneForm (weightedCircleAngular f) b p.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,CircleModel) b).target) := by
    intro b
    exact (weightedCircleAngular_smooth hf b).comp contDiffOn_snd (fun _ hp => hp.2)
  have ht := manifoldPullbackOneForm_smooth
    (E := CircleModel) (F := TorusModel) (α := fun _ => weightedCircleAngular f)
    (e := (Prod.snd : HandleTorus → Circle)) torus_snd_smooth hα c
  exact ht.comp (f := fun y => ((0 : ℝ),y))
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

theorem torusHandleForm_closed {f : Circle → ℝ}
    (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (z : HandleTorus) :
    manifoldExteriorOneForm (torusHandleForm f) z=0 := by
  rw [torusHandleForm,manifold_pullback_exterior (weightedCircleAngular_smooth hf) torus_snd_smooth]
  simp only [manifoldPullbackTwoForm,circle_oneForm_closed]
  rfl

theorem torusHandleForm_support {f : Circle → ℝ} {U : Set Circle}
    (hU : tsupport f ⊆ U) : support (torusHandleForm f) ⊆ univ ×ˢ U := by
  intro z hz
  refine ⟨mem_univ _,hU (subset_closure ?_)⟩
  intro hzero
  apply hz
  apply ContinuousLinearMap.ext
  intro v
  change torusHandleForm f z v=0
  rw [torusHandleForm_apply]
  change f z.2*circleAngular z.2 v.2=0
  rw [hzero,zero_mul]

def transverseTorusCircle (z : Circle) (t : ℝ) : HandleTorus := (z,circleTurn t)

theorem transverseTorusCircle_smooth (z : Circle) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,TorusModel) ∞ (transverseTorusCircle z) :=
by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact contMDiff_const.prodMk circleTurn_smooth

theorem torusHandleForm_transverse (f : Circle → ℝ) (z : Circle) (t v : ℝ) :
    torusHandleForm f (transverseTorusCircle z t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,TorusModel) (transverseTorusCircle z) t v) =
      f (circleTurn t)*v := by
  have hd := mfderiv_prodMk (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,CircleModel))
    (I'' := 𝓘(ℝ,CircleModel)) (f := fun _ : ℝ => z) (g := circleTurn)
    mdifferentiableAt_const (circleTurn_smooth.mdifferentiable (by simp) t)
  erw [torusHandleForm_apply]
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  change weightedCircleAngular f (circleTurn t)
    ((mfderiv 𝓘(ℝ,ℝ) ((𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel))
      (fun x => (z,circleTurn x)) t v).2)=_
  rw [hd]
  exact weightedCircleAngular_pullback f t v

theorem exists_torus_handle_form {U : Set Circle}
    (hU : U ∈ 𝓝 (circleTurn (1/2))) :
    ∃ f : Circle → ℝ, ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f ∧
      (∀ z,0≤f z) ∧ tsupport f ⊆ U ∧
      (∀ z,manifoldExteriorOneForm (torusHandleForm f) z=0) ∧
      support (torusHandleForm f) ⊆ univ ×ˢ U ∧
      (∀ z : Circle, (∫ t in (0 : ℝ)..1,
        torusHandleForm f (transverseTorusCircle z t)
          (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,TorusModel) (transverseTorusCircle z) t 1))=1) := by
  obtain ⟨f,hf,hn,hs,hJ,_⟩ := exists_normalized_circle_bump hU
  refine ⟨f,hf,hn,hs,torusHandleForm_closed hf,torusHandleForm_support hs,?_⟩
  intro z
  refine Eq.trans ?_ hJ
  apply intervalIntegral.integral_congr
  intro t _
  exact (torusHandleForm_transverse f z t 1).trans (mul_one _)





abbrev CylinderModel := ℝ × CircleModel
abbrev HandleCylinder := ℝ × Circle

instance cylinder_chartedSpace : ChartedSpace CylinderModel HandleCylinder :=
  prodChartedSpace ℝ ℝ CircleModel Circle

instance cylinder_manifold : IsManifold 𝓘(ℝ,CylinderModel) ∞ HandleCylinder := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact IsManifold.prod ℝ Circle

def torusAnnulusMap (z : HandleCylinder) : HandleTorus := (circleTurn z.1,z.2)
def torusAnnulusInverse (z : HandleTorus) : HandleCylinder := (shortCircleArgument z.1,z.2)

theorem torusAnnulusMap_smooth : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) ∞
    torusAnnulusMap := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,
    show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (circleTurn_smooth.comp contMDiff_fst).prodMk contMDiff_snd

theorem torusAnnulusInverse_smooth {z : HandleTorus}
    (hz : z.1 ∈ circleBandCoordinate.target) :
    ContMDiffAt 𝓘(ℝ,TorusModel) 𝓘(ℝ,CylinderModel) ∞ torusAnnulusInverse z := by
  have h := circleBandCoordinate.contMDiffOn_invFun.contMDiffAt
    (circleBandCoordinate.open_target.mem_nhds hz)
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,
    show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (h.comp z contMDiffAt_fst).prodMk contMDiffAt_snd

def torusAnnulus : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel)
    HandleCylinder HandleTorus ∞ where
  toFun := torusAnnulusMap
  invFun := torusAnnulusInverse
  source := circleBandCoordinate.source ×ˢ univ
  target := circleBandCoordinate.target ×ˢ univ
  map_source' z hz := ⟨circleBandCoordinate.map_source hz.1,mem_univ _⟩
  map_target' z hz := ⟨circleBandCoordinate.map_target hz.1,mem_univ _⟩
  left_inv' z hz := by
    apply Prod.ext
    · exact circleBandCoordinate.left_inv hz.1
    · rfl
  right_inv' z hz := by
    apply Prod.ext
    · exact circleBandCoordinate.right_inv hz.1
    · rfl
  open_source := circleBandCoordinate.open_source.prod isOpen_univ
  open_target := circleBandCoordinate.open_target.prod isOpen_univ
  contMDiffOn_toFun := torusAnnulusMap_smooth.contMDiffOn
  contMDiffOn_invFun := fun _ hz => (torusAnnulusInverse_smooth hz.1).contMDiffWithinAt

theorem torusAnnulus_compact {a b : ℝ} :
    IsCompact (torusAnnulusMap '' (Icc a b ×ˢ (univ : Set Circle))) :=
  (isCompact_Icc.prod isCompact_univ).image torusAnnulusMap_smooth.continuous

theorem torusAnnulus_pullback (f : Circle → ℝ) (z : HandleCylinder) (v : CylinderModel) :
    torusHandleForm f (torusAnnulusMap z)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) torusAnnulusMap z v) =
      weightedCircleAngular f z.2 v.2 := by
  have hd := mfderiv_prodMk
    (I := (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) (I' := 𝓘(ℝ,CircleModel))
    (I'' := 𝓘(ℝ,CircleModel))
    (f := fun z : HandleCylinder => circleTurn z.1) (g := Prod.snd) (x := z)
    ((circleTurn_smooth.comp contMDiff_fst).mdifferentiableAt (by simp))
    mdifferentiableAt_snd
  erw [torusHandleForm_apply]
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,
    show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  change weightedCircleAngular f z.2
    ((mfderiv ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel))
      ((𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel))
      (fun x : HandleCylinder => (circleTurn x.1,x.2)) z v).2)=_
  rw [hd]
  change weightedCircleAngular f z.2
    (mfderiv ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,CircleModel) Prod.snd z v)=_
  rw [mfderiv_snd]
  rfl

theorem torusHandleForm_tsupport (f : Circle → ℝ) :
    tsupport (torusHandleForm f) ⊆ univ ×ˢ tsupport f := by
  exact closure_minimal (torusHandleForm_support (Subset.refl _))
    (isClosed_univ.prod isClosed_closure)





theorem cylinder_snd_smooth : ContMDiff 𝓘(ℝ,CylinderModel) 𝓘(ℝ,CircleModel) ∞
    (Prod.snd : HandleCylinder → Circle) := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact contMDiff_snd

def cylinderAngular : ManifoldOneForm CylinderModel HandleCylinder :=
  manifoldPullbackOneForm (fun _ => circleAngular) Prod.snd 0

@[simp] theorem cylinderAngular_apply (z : HandleCylinder) (v : CylinderModel) :
    cylinderAngular z v=circleAngular z.2 v.2 := by
  simp only [cylinderAngular,manifoldPullbackOneForm,manifoldMapDifferential]
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,mfderiv_snd]
  rfl

theorem cylinderAngular_smooth (c : HandleCylinder) :
    ContDiffOn ℝ ∞ (chartOneForm cylinderAngular c)
      (extChartAt 𝓘(ℝ,CylinderModel) c).target := by
  have ht := manifoldPullbackOneForm_smooth (α := fun _ => circleAngular)
    cylinder_snd_smooth circleAngular_joint_smooth c
  exact ht.comp (f := fun y => ((0:ℝ),y))
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

theorem cylinderAngular_closed (z : HandleCylinder) :
    manifoldExteriorOneForm cylinderAngular z=0 := by
  rw [cylinderAngular,manifold_pullback_exterior circleAngular_smooth cylinder_snd_smooth]
  simp only [manifoldPullbackTwoForm,circleAngular_closed]
  rfl

def cylinderCover (q : Plane) : HandleCylinder := (q.1,circleTurn q.2)

theorem cylinderCover_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) ∞ cylinderCover := by
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Plane → ℝ)).contMDiff.prodMk
    (circleTurn_smooth.comp (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Plane → ℝ)).contMDiff)

theorem cylinderCover_derivative (q v : Plane) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v=
      (v.1,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn q.2 v.2) := by
  have hf := (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Plane → ℝ)).contMDiff
  have hs := (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Plane → ℝ)).contMDiff
  rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  have hd := mfderiv_prodMk (I := 𝓘(ℝ,Plane)) (I' := 𝓘(ℝ,ℝ))
    (I'' := 𝓘(ℝ,CircleModel)) (f := (Prod.fst : Plane → ℝ))
    (g := fun z : Plane => circleTurn z.2) (x := q)
    (hf.mdifferentiableAt (by simp))
    ((circleTurn_smooth.comp hs).mdifferentiableAt (by simp))
  change (mfderiv 𝓘(ℝ,Plane) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel))
    (fun z : Plane => (z.1,circleTurn z.2)) q v)=_
  rw [hd]
  have hc := mfderiv_comp q (circleTurn_smooth.mdifferentiableAt (by simp))
    (I := 𝓘(ℝ,Plane)) (I' := 𝓘(ℝ,ℝ)) (I'' := 𝓘(ℝ,CircleModel))
    (f := (Prod.snd : Plane → ℝ)) (hs.mdifferentiableAt (by simp))
  change ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) Prod.fst q) v,
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CircleModel) (circleTurn ∘ Prod.snd) q) v)=_
  rw [hc,mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_fst,fderiv_snd]
  rfl

@[simp] theorem cylinderAngular_cover (q v : Plane) :
    cylinderAngular (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=v.2 := by
  erw [cylinderCover_derivative,cylinderAngular_apply]
  exact circleAngular_unit_pullback q.2 v.2

def weightedCylinderAngular (f : HandleCylinder → ℝ) (z : HandleCylinder) :
    CylinderModel →L[ℝ] ℝ := f z • cylinderAngular z

theorem weightedCylinderAngular_chart (f : HandleCylinder → ℝ) (c : HandleCylinder)
    (y : CylinderModel) : chartOneForm (weightedCylinderAngular f) c y=
      f ((extChartAt 𝓘(ℝ,CylinderModel) c).symm y) • chartOneForm cylinderAngular c y := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem weightedCylinderAngular_smoothAt {f : HandleCylinder → ℝ} {c : HandleCylinder}
    (hf : ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ f c) :
    ContDiffAt ℝ ∞ (chartOneForm (weightedCylinderAngular f) c)
      (extChartAt 𝓘(ℝ,CylinderModel) c c) := by
  have he : chartOneForm (weightedCylinderAngular f) c=
      fun y => f ((extChartAt 𝓘(ℝ,CylinderModel) c).symm y) • chartOneForm cylinderAngular c y :=
    funext (weightedCylinderAngular_chart f c)
  rw [he]
  have hc := (extChartAt 𝓘(ℝ,CylinderModel) c).map_source (mem_extChartAt_source c)
  have hn := (isOpen_extChartAt_target (I := 𝓘(ℝ,CylinderModel)) c).mem_nhds hc
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,CylinderModel)) (n := ∞) c).contMDiffAt hn
  have hfc : ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ f
      ((extChartAt 𝓘(ℝ,CylinderModel) c).symm (extChartAt 𝓘(ℝ,CylinderModel) c c)) := by
    simpa only [(extChartAt 𝓘(ℝ,CylinderModel) c).left_inv (mem_extChartAt_source c)] using hf
  exact ((hfc.comp _ hi).contDiffAt).smul ((cylinderAngular_smooth c).contDiffAt hn)





theorem circleTurn_eq_iff (s t : ℝ) :
    circleTurn s=circleTurn t ↔ ∃ m : ℤ, s=t+m := by
  rw [circleTurn,circleTurn,Circle.exp_eq_exp]
  constructor
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    apply mul_left_cancel₀ (show 2*Real.pi≠0 by positivity)
    calc
      2*Real.pi*s=2*Real.pi*t+(m:ℝ)*(2*Real.pi) := hm
      _ = 2*Real.pi*(t+(m:ℝ)) := by ring
  · rintro ⟨m,rfl⟩
    exact ⟨m,by ring⟩

theorem periodic_eq_of_circleTurn_eq {F : ℝ → ℝ} (hF : Periodic F 1)
    {s t : ℝ} (h : circleTurn s=circleTurn t) : F s=F t := by
  obtain ⟨m,rfl⟩ := (circleTurn_eq_iff s t).mp h
  simpa only [mul_one] using hF.int_mul m t

def circlePeriodicDescent (F : ℝ → ℝ) (z : Circle) : ℝ :=
  F (shortCircleArgument z)

theorem circlePeriodicDescent_turn {F : ℝ → ℝ} (hF : Periodic F 1) (t : ℝ) :
    circlePeriodicDescent F (circleTurn t)=F t :=
  periodic_eq_of_circleTurn_eq hF (circleTurn_shortCircleArgument _)

def localCircleLift (c z : Circle) : ℝ :=
  shortCircleArgument (z/c)+shortCircleArgument c

theorem circleTurn_add (s t : ℝ) : circleTurn (s+t)=circleTurn s*circleTurn t := by
  simp only [circleTurn,mul_add,Circle.exp_add]

theorem localCircleLift_turn (c z : Circle) : circleTurn (localCircleLift c z)=z := by
  rw [localCircleLift,circleTurn_add,circleTurn_shortCircleArgument,
    circleTurn_shortCircleArgument,div_mul_cancel]

theorem localCircleLift_smooth_at (c : Circle) :
    ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (localCircleLift c) c := by
  have hdiv : ContMDiffAt 𝓘(ℝ,CircleModel) 𝓘(ℝ,CircleModel) ∞
      (fun z : Circle => z/c) c := contMDiffAt_id.div contMDiffAt_const
  have hslit : ((c/c : Circle) : ℂ) ∈ Complex.slitPlane := by
    simpa only [div_self',Circle.coe_one] using Complex.one_mem_slitPlane
  exact ((shortCircleArgument_smooth_at hslit).comp (f := fun z : Circle => z/c) c hdiv).add contMDiffAt_const

theorem circlePeriodicDescent_local {F : ℝ → ℝ} (hF : Periodic F 1)
    (c z : Circle) : circlePeriodicDescent F z=F (localCircleLift c z) :=
  periodic_eq_of_circleTurn_eq hF ((circleTurn_shortCircleArgument z).trans
    (localCircleLift_turn c z).symm)

theorem circlePeriodicDescent_smooth {F : ℝ → ℝ} (hF : Periodic F 1)
    (hs : ContDiff ℝ ∞ F) :
    ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ (circlePeriodicDescent F) := by
  intro z
  have ht := hs.contMDiff.contMDiffAt.comp z (localCircleLift_smooth_at z)
  exact ht.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun w => circlePeriodicDescent_local hF z w))

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def circleFamilyDescent (F : P × ℝ → ℝ) (q : P × Circle) : ℝ :=
  circlePeriodicDescent (fun t => F (q.1,t)) q.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem circleFamilyDescent_turn {F : P × ℝ → ℝ} {p : P}
    (hp : Periodic (fun t => F (p,t)) 1) (t : ℝ) :
    circleFamilyDescent F (p,circleTurn t)=F (p,t) :=
  circlePeriodicDescent_turn hp t

theorem circleFamilyDescent_smoothOn {V : Set P} (hV : IsOpen V)
    {F : P × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ))
    (hp : ∀ p ∈ V, Periodic (fun t => F (p,t)) 1) :
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (circleFamilyDescent F) (V ×ˢ univ) := by
  intro q hq
  have hl : ContMDiffAt ((𝓘(ℝ,P)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (fun w : P × Circle => localCircleLift q.2 w.2) q :=
    (localCircleLift_smooth_at q.2).comp q contMDiffAt_snd
  have hm := (contMDiffAt_fst (I := 𝓘(ℝ,P))
    (J := 𝓘(ℝ,CircleModel)) (n := ∞) (p := q)).prodMk_space hl
  have hfat : ContDiffAt ℝ ∞ F (q.1,localCircleLift q.2 q.2) :=
    hF.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq.1,mem_univ _⟩)
  have ht := hfat.contMDiffAt.comp q hm
  apply (ht.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(hV.prod isOpen_univ).mem_nhds hq] with w hw
  exact circlePeriodicDescent_local (hp w.1 hw.1) q.2 w.2


end

open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def stripPrimitive (a : ℝ) (A B : Plane → ℝ) (q : Plane) : ℝ :=
  (∫ s in a..q.1, A (s,0)) + ∫ t in (0:ℝ)..q.2, B (q.1,t)

def annularPrimitive (a : ℝ) (A B : P × Plane → ℝ) (q : P × Plane) : ℝ :=
  stripPrimitive a (fun z => A (q.1,z)) (fun z => B (q.1,z)) q.2

theorem annularPrimitive_smooth {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a ∈ I)
    {A B : P × Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (V ×ˢ (I ×ˢ univ)))
    (hB : ContDiffOn ℝ ∞ B (V ×ˢ (I ×ˢ univ))) :
    ContDiffOn ℝ ∞ (annularPrimitive a A B) (V ×ˢ (I ×ˢ univ)) := by
  have hAf : ContDiffOn ℝ ∞ (fun q : P × ℝ => A (q.1,(q.2,0))) (V ×ˢ I) :=
    hA.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
      (fun _ hq => ⟨hq.1,hq.2,mem_univ _⟩)
  have hAi := contDiffOn_parameter_segment_integral hV hI hc a ha hAf
  have hAs : ContDiffOn ℝ ∞ (fun q : P × Plane => ∫ s in a..q.2.1, A (q.1,(s,0)))
      (V ×ˢ (I ×ˢ univ)) :=
    hAi.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
      (fun _ hq => ⟨hq.1,hq.2.1⟩)
  have hBf : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℝ => B (q.1.1,(q.1.2,q.2)))
      ((V ×ˢ I) ×ˢ univ) :=
    hB.comp ((contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
      (fun _ hq => ⟨hq.1.1,hq.1.2,hq.2⟩)
  have hBi := contDiffOn_parameter_segment_integral (hV.prod hI) isOpen_univ convex_univ
    (0:ℝ) (mem_univ _) hBf
  have hBs : ContDiffOn ℝ ∞ (fun q : P × Plane => ∫ t in (0:ℝ)..q.2.2, B (q.1,(q.2.1,t)))
      (V ×ˢ (I ×ˢ univ)) :=
    hBi.comp ((contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
      (contDiff_snd.comp contDiff_snd)).contDiffOn
      (fun _ hq => ⟨⟨hq.1,hq.2.1⟩,hq.2.2⟩)
  exact hAs.add hBs

theorem stripPrimitive_smooth {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I) {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (I ×ˢ univ)) (hB : ContDiffOn ℝ ∞ B (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (stripPrimitive a A B) (I ×ˢ univ) := by
  have hA' : ContDiffOn ℝ ∞ (fun q : ℝ × Plane => A q.2) (univ ×ˢ (I ×ˢ univ)) :=
    hA.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)
  have hB' : ContDiffOn ℝ ∞ (fun q : ℝ × Plane => B q.2) (univ ×ˢ (I ×ˢ univ)) :=
    hB.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)
  exact (annularPrimitive_smooth isOpen_univ hI hc ha hA' hB').comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hq => ⟨mem_univ (0:ℝ),hq⟩)



end PackingSufficiencySupport.Hamiltonian
end

end OAI
