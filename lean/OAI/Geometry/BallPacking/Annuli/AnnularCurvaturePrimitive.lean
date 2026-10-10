import Mathlib
import OAI.Geometry.BallPacking.Annuli.AnnularMean

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def annularRadialIntegral (a : ℝ) (κ : P × Plane → ℝ) (q : P × Plane) : ℝ :=
  ∫ s in a..q.2.1,κ (q.1,(s,q.2.2))

theorem annularRadialIntegral_smooth {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ))) :
    ContDiffOn ℝ ∞ (annularRadialIntegral a κ) (V ×ˢ (I ×ˢ univ)) := by
  have hG : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℝ => κ (q.1.1,(q.2,q.1.2)))
      ((V ×ˢ univ) ×ˢ I) :=
    hκ.comp (contDiff_fst.fst.prodMk (contDiff_snd.prodMk contDiff_fst.snd)).contDiffOn
      (fun _ hq => ⟨hq.1.1,hq.2,hq.1.2⟩)
  have hi := contDiffOn_parameter_segment_integral (hV.prod isOpen_univ) hI hc a ha hG
  exact hi.comp ((contDiff_fst.prodMk contDiff_snd.snd).prodMk contDiff_snd.fst).contDiffOn
    (fun _ hq => ⟨⟨hq.1,hq.2.2⟩,hq.2.1⟩)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem annularRadialIntegral_periodic {V : Set P} {I : Set ℝ} (hc : Convex ℝ I)
    {a : ℝ} (ha : a∈I) {κ : P × Plane → ℝ}
    (hκ : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {s : ℝ} (hs : s∈I) :
    Periodic (fun t => annularRadialIntegral a κ (p,(s,t))) 1 := by
  intro t
  apply intervalIntegral.integral_congr
  intro u hu
  have huI : u∈I := hc.segment_subset ha hs (by simpa only [segment_eq_uIcc] using hu)
  exact hκ p hp u huI t

omit [FiniteDimensional ℝ P] in
theorem annularRadialIntegral_hasDerivAt {V : Set P} {I : Set ℝ}
    (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) :
    HasDerivAt (fun s => annularRadialIntegral a κ (p,(s,q.2))) (κ (p,q)) q.1 := by
  change HasDerivAt (fun s => ∫ u in a..s,κ (p,(u,q.2))) (κ (p,(q.1,q.2))) q.1
  apply hasDerivAt_primitive_on hI hc _ ha hq
  exact hκ.continuousOn.comp
    (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
    (fun _ hs => ⟨hp,hs,mem_univ _⟩)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem planarCovector_exterior_at {U V : Plane → ℝ} {p : Plane}
    (hU : ContDiffAt ℝ ∞ U p) (hV : ContDiffAt ℝ ∞ V p) :
    euclideanExteriorOneForm (fun x => planarCovector (U x) (V x)) p=
      (fderiv ℝ V p (1,0)-fderiv ℝ U p (0,1)) • planarArea := by
  let α : Plane → Plane →L[ℝ] ℝ := fun x => planarCovector (U x) (V x)
  have ha : DifferentiableAt ℝ α p :=
    ((hU.smul contDiffAt_const).add (hV.smul contDiffAt_const)).differentiableAt (by simp)
  have hV' : fderiv ℝ α p (1,0) (0,1)=fderiv ℝ V p (1,0) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,zero_add]
  have hU' : fderiv ℝ α p (0,1) (1,0)=fderiv ℝ U p (0,1) := by
    rw [← fderiv_clm_eval ha]
    simp only [α,planarCovector_apply,mul_zero,mul_one,add_zero]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ α p u v-fderiv ℝ α p v u=_
  rw [bilinear_skew_plane,hV',hU']
  rfl

theorem annular_curvature_primitive {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1) :
    ContMDiffOn ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
      (annularScalarDescent (annularRadialIntegral a κ)) ((V ×ˢ I) ×ˢ univ) ∧
      (∀ p∈V,∀ q : Plane,q.1∈I →
        euclideanExteriorOneForm (fun z => planarCovector 0 (annularRadialIntegral a κ (p,z))) q=
          κ (p,q) • planarArea) := by
  have hB := annularRadialIntegral_smooth hV hI hc ha hκ
  refine ⟨annularScalarDescent_smoothOn hV hI hB
    (fun _ hp _ hs => annularRadialIntegral_periodic hc ha hper hp hs),?_⟩
  intro p hp q hq
  have hBp : ContDiffOn ℝ ∞ (fun z => annularRadialIntegral a κ (p,z)) (I ×ˢ univ) :=
    hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz⟩)
  have hBa := hBp.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hq,mem_univ _⟩)
  have hd := (hBa.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have he : fderiv ℝ (fun z => annularRadialIntegral a κ (p,z)) q (1,0)=κ (p,q) :=
    hd.unique (annularRadialIntegral_hasDerivAt hI hc ha hκ hp hq)
  rw [planarCovector_exterior_at contDiffAt_const hBa,he]
  simp


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold

def handleCutPoint : Circle := circleTurn (1/2)

theorem handleCutPoint_ne_one : handleCutPoint≠1 := by
  have he : handleCutPoint=Circle.exp Real.pi := by
    unfold handleCutPoint circleTurn
    congr 1
    ring
  rw [he]
  exact Circle.exp_pi_ne_one

theorem shortCircleArgument_cutPoint : shortCircleArgument handleCutPoint=1/2 := by
  have he : handleCutPoint=Circle.exp Real.pi := by
    unfold handleCutPoint circleTurn
    congr 1
    ring
  rw [he]
  unfold shortCircleArgument
  rw [Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl]
  field_simp

theorem handleCutPoint_not_band : handleCutPoint∉circleBandCoordinate.target := by
  rintro ⟨s,hs,he⟩
  have ht := congrArg shortCircleArgument he
  rw [shortCircleArgument_cutPoint,shortCircleArgument_turn hs] at ht
  exact hs.2.ne ht

def compactHandleBand (a : ℝ) : Set HandleTorus :=
  torusAnnulusMap '' (Icc (-a) a ×ˢ (univ : Set Circle))

theorem compactHandleBand_isCompact (a : ℝ) : IsCompact (compactHandleBand a) :=
  torusAnnulus_compact

def handlePuncture : HandleTorus := (handleCutPoint,1)

theorem handlePuncture_not_compactBand {a : ℝ} (ha : a<1/2) :
    handlePuncture∉compactHandleBand a := by
  rintro ⟨z,hz,he⟩
  have hs : z.1∈Ioo (-(1/2):ℝ) (1/2) := ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩
  apply handleCutPoint_not_band
  refine ⟨z.1,hs,?_⟩
  exact congrArg Prod.fst he

theorem exists_torus_handle_away_from_puncture {a : ℝ} (ha : a<1/2) :
    ∃ (f : Circle → ℝ) (U : Set HandleTorus),
      ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f ∧
      (∀ z,0≤f z) ∧
      (∀ z,manifoldExteriorOneForm (torusHandleForm f) z=0) ∧
      IsOpen U ∧ handlePuncture∈U ∧
      Disjoint U (compactHandleBand a) ∧
      Disjoint U (tsupport (torusHandleForm f)) ∧
      (∀ z : Circle, (∫ t in (0:ℝ)..1, torusHandleForm f (transverseTorusCircle z t)
        (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,TorusModel) (transverseTorusCircle z) t 1))=1) := by
  have hn : ({1}ᶜ : Set Circle) ∈ 𝓝 handleCutPoint :=
    isClosed_singleton.isOpen_compl.mem_nhds handleCutPoint_ne_one
  obtain ⟨f,hf,hpos,hsupp,hJ,_⟩ := exists_normalized_circle_bump hn
  let T := compactHandleBand a ∪ tsupport (torusHandleForm f)
  have hT : IsClosed T := (compactHandleBand_isCompact a).isClosed.union isClosed_closure
  have hp : handlePuncture∉T := by
    rintro (hband|hs)
    · exact handlePuncture_not_compactBand ha hband
    · have hh := hsupp (torusHandleForm_tsupport f hs).2
      exact hh rfl
  refine ⟨f,Tᶜ,hf,hpos,torusHandleForm_closed hf,hT.isOpen_compl,hp,?_,?_,?_⟩
  · exact disjoint_compl_left.mono_right subset_union_left
  · exact disjoint_compl_left.mono_right subset_union_right
  · intro z
    refine Eq.trans ?_ hJ
    apply intervalIntegral.integral_congr
    intro t _
    exact (torusHandleForm_transverse f z t 1).trans (mul_one _)


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

theorem torus_fst_smooth : ContMDiff 𝓘(ℝ,TorusModel) 𝓘(ℝ,CircleModel) ∞
    (Prod.fst : HandleTorus → Circle) := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact contMDiff_fst

def torusFirstForm (f : Circle → ℝ) : ManifoldOneForm TorusModel HandleTorus :=
  manifoldPullbackOneForm (fun _ => weightedCircleAngular f) Prod.fst 0

@[simp] theorem torusFirstForm_apply (f : Circle → ℝ) (z : HandleTorus) (v : TorusModel) :
    torusFirstForm f z v=weightedCircleAngular f z.1 v.1 := by
  simp only [torusFirstForm,manifoldPullbackOneForm,manifoldMapDifferential]
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod,mfderiv_fst]
  rfl

theorem torusFirstForm_smooth {f : Circle → ℝ}
    (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) (c : HandleTorus) :
    ContDiffOn ℝ ∞ (chartOneForm (torusFirstForm f) c)
      (extChartAt 𝓘(ℝ,TorusModel) c).target := by
  have hα : ∀ b : Circle, ContDiffOn ℝ ∞
      (fun p : ℝ × CircleModel => chartOneForm (weightedCircleAngular f) b p.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,CircleModel) b).target) := by
    intro b
    exact (weightedCircleAngular_smooth hf b).comp contDiffOn_snd (fun _ hp => hp.2)
  have ht := manifoldPullbackOneForm_smooth
    (E := CircleModel) (F := TorusModel) (α := fun _ => weightedCircleAngular f)
    (e := (Prod.fst : HandleTorus → Circle)) torus_fst_smooth hα c
  exact ht.comp (f := fun y => ((0 : ℝ),y))
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _,hy⟩)

def torusTurns (z : Plane) : HandleTorus := (circleTurn z.1,circleTurn z.2)

theorem flatPlane_fst_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (Prod.fst : Plane → ℝ) :=
  (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Plane → ℝ)).contMDiff

theorem flatPlane_snd_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (Prod.snd : Plane → ℝ) :=
  (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Plane → ℝ)).contMDiff

theorem torusTurns_smooth : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) ∞ torusTurns := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  exact (circleTurn_smooth.comp flatPlane_fst_smooth).prodMk
    (circleTurn_smooth.comp flatPlane_snd_smooth)

theorem torusTurns_derivative (z v : Plane) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns z v=
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn z.1 v.1,
       mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn z.2 v.2) := by
  rw [show 𝓘(ℝ,TorusModel) = (𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel) from
    modelWithCornersSelf_prod]
  have hd := mfderiv_prodMk (I := 𝓘(ℝ,Plane)) (I' := 𝓘(ℝ,CircleModel))
    (I'' := 𝓘(ℝ,CircleModel)) (f := fun z : Plane => circleTurn z.1)
    (g := fun z : Plane => circleTurn z.2) (x := z)
    ((circleTurn_smooth.comp flatPlane_fst_smooth).mdifferentiableAt (by simp))
    ((circleTurn_smooth.comp flatPlane_snd_smooth).mdifferentiableAt (by simp))
  change (mfderiv 𝓘(ℝ,Plane) ((𝓘(ℝ,CircleModel)).prod 𝓘(ℝ,CircleModel))
    (fun x : Plane => (circleTurn x.1,circleTurn x.2)) z v)=_
  rw [hd]
  have hfst := mfderiv_comp z (circleTurn_smooth.mdifferentiableAt (by simp))
    (I := 𝓘(ℝ,Plane)) (I' := 𝓘(ℝ,ℝ)) (I'' := 𝓘(ℝ,CircleModel))
    (f := (Prod.fst : Plane → ℝ)) (flatPlane_fst_smooth.mdifferentiableAt (by simp))
  have hsnd := mfderiv_comp z (circleTurn_smooth.mdifferentiableAt (by simp))
    (I := 𝓘(ℝ,Plane)) (I' := 𝓘(ℝ,ℝ)) (I'' := 𝓘(ℝ,CircleModel))
    (f := (Prod.snd : Plane → ℝ)) (flatPlane_snd_smooth.mdifferentiableAt (by simp))
  change ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CircleModel) (circleTurn ∘ Prod.fst) z) v,
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CircleModel) (circleTurn ∘ Prod.snd) z) v)=_
  rw [hfst,hsnd,mfderiv_eq_fderiv,mfderiv_eq_fderiv,fderiv_fst,fderiv_snd]
  rfl

def torusAnnularDensity (b : ℝ) (f : Circle → ℝ) : ManifoldTwoForm TorusModel HandleTorus :=
  manifoldWedge (torusFirstForm (circleClockDensity b)) (torusHandleForm f)

theorem torusAnnularDensity_smooth {b : ℝ} (hb : 0<b) (hsmall : b<1/2)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f) :
    SmoothTwoForm (torusAnnularDensity b f) :=
  manifoldWedge_smooth (torusFirstForm_smooth (circleClockDensity_smooth hb hsmall))
    (torusHandleForm_smooth hf)

theorem torusAnnularDensity_turns (b : ℝ) (f : Circle → ℝ) (z v w : Plane) :
    torusAnnularDensity b f (torusTurns z)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns z v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns z w)=
      circleClockDensity b (circleTurn z.1)*f (circleTurn z.2)*(v.1*w.2-v.2*w.1) := by
  have hform (x : HandleTorus) (u₁ u₂ : TorusModel) :
      torusAnnularDensity b f x u₁ u₂ =
        weightedCircleAngular (circleClockDensity b) x.1 u₁.1 *
          weightedCircleAngular f x.2 u₂.2 -
        weightedCircleAngular f x.2 u₁.2 *
          weightedCircleAngular (circleClockDensity b) x.1 u₂.1 := by
    simp only [torusAnnularDensity,manifoldWedge_apply,torusFirstForm_apply,
      torusHandleForm_apply]
  let A : Plane →L[ℝ] TorusModel :=
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns z
  let D₁ : ℝ →L[ℝ] CircleModel :=
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn z.1
  let D₂ : ℝ →L[ℝ] CircleModel :=
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn z.2
  have hA (u : Plane) : A u = (D₁ u.1,D₂ u.2) := torusTurns_derivative z u
  have hD₁ (g : Circle → ℝ) (u : ℝ) :
      weightedCircleAngular g (circleTurn z.1) (D₁ u) = g (circleTurn z.1)*u :=
    weightedCircleAngular_pullback g z.1 u
  have hD₂ (g : Circle → ℝ) (u : ℝ) :
      weightedCircleAngular g (circleTurn z.2) (D₂ u) = g (circleTurn z.2)*u :=
    weightedCircleAngular_pullback g z.2 u
  change torusAnnularDensity b f (torusTurns z) (A v) (A w) = _
  rw [hform,hA v,hA w]
  simp only [torusTurns,hD₁,hD₂]
  ring

theorem torusAnnularDensity_support {b : ℝ} (hb : 0<b) (f : Circle → ℝ) :
    support (torusAnnularDensity b f) ⊆ (circleTurn '' Icc (-b) b) ×ˢ tsupport f := by
  intro z hz
  have hnonzero₁ : circleClockDensity b z.1≠0 := by
    intro he
    apply hz
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change torusAnnularDensity b f z v w=0
    simp [torusAnnularDensity,torusFirstForm_apply,torusHandleForm_apply,
      weightedCircleAngular,he]
  have hnonzero₂ : f z.2≠0 := by
    intro he
    apply hz
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change torusAnnularDensity b f z v w=0
    simp [torusAnnularDensity,torusFirstForm_apply,torusHandleForm_apply,
      weightedCircleAngular,he]
  exact ⟨circleClockDensity_support hb hnonzero₁,subset_closure hnonzero₂⟩

theorem torusAnnularDensity_tsupport {b : ℝ} (hb : 0<b) (f : Circle → ℝ) :
    tsupport (torusAnnularDensity b f) ⊆ (circleTurn '' Icc (-b) b) ×ˢ tsupport f :=
  closure_minimal (torusAnnularDensity_support hb f)
    (circleBand_compact.isClosed.prod isClosed_closure)

theorem torusAnnularDensity_normalized {b : ℝ} (hb : 0<b) (hsmall : b<1/2)
    {f : Circle → ℝ} (hpos : ∀ z,0≤f z)
    (hJ : (∫ t in (0:ℝ)..1,f (circleTurn t))=1) :
    (∀ z : Plane,0≤torusAnnularDensity b f (torusTurns z)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns z (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns z (0,1))) ∧
    (∫ s in (-(1/2):ℝ)..(1/2), ∫ t in (0:ℝ)..1,
      torusAnnularDensity b f (torusTurns (s,t))
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns (s,t) (1,0))
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,TorusModel) torusTurns (s,t) (0,1)))=1 := by
  simp only [torusAnnularDensity_turns,zero_mul,sub_zero,mul_one]
  constructor
  · intro z
    exact mul_nonneg (circleClockDensity_nonneg hb _) (hpos _)
  · simp_rw [intervalIntegral.integral_const_mul,hJ,mul_one]
    exact circleClockDensity_integral hb hsmall





def angularUnitVector (z : Circle) : CircleModel :=
  mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn (shortCircleArgument z) 1

theorem angularUnitVector_value (z : Circle) : circleAngular z (angularUnitVector z)=1 := by
  have h := circleAngular_unit_pullback (shortCircleArgument z) 1
  rwa [circleTurn_shortCircleArgument] at h

theorem circleAngular_injective (z : Circle) : Injective (circleAngular z) := by
  let e : CircleModel := EuclideanSpace.single 0 1
  have he (v : CircleModel) : v=(v 0) • e := by
    ext i
    fin_cases i
    simp [e]
  have hz : circleAngular z e≠0 := by
    intro hzero
    have hv := angularUnitVector_value z
    rw [he (angularUnitVector z),map_smul,hzero,smul_zero] at hv
    norm_num at hv
  intro v w hvw
  have hce : v 0 * circleAngular z e=w 0 * circleAngular z e := by
    rwa [he v,he w,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at hvw
  have hcoords := mul_right_cancel₀ hz hce
  rw [he v,he w,hcoords]

def torusAreaForm : ManifoldTwoForm TorusModel HandleTorus :=
  manifoldWedge (torusFirstForm (fun _ => 1)) (torusHandleForm (fun _ => 1))

@[simp] theorem torusAreaForm_apply (z : HandleTorus) (v w : TorusModel) :
    torusAreaForm z v w=circleAngular z.1 v.1*circleAngular z.2 w.2-
      circleAngular z.2 v.2*circleAngular z.1 w.1 := by
  simp [torusAreaForm,manifoldWedge_apply,weightedCircleAngular]

theorem torusAreaForm_smooth : SmoothTwoForm torusAreaForm :=
  manifoldWedge_smooth (torusFirstForm_smooth contMDiff_const)
    (torusHandleForm_smooth contMDiff_const)

theorem torusAreaForm_skew (z : HandleTorus) (v w : TorusModel) :
    torusAreaForm z v w= -torusAreaForm z w v :=
  manifoldWedge_skew _ _ z v w

theorem torusAreaForm_isInvertible (z : HandleTorus) : (torusAreaForm z).IsInvertible := by
  let : ContinuousSMul ℝ TorusModel := IsBoundedSMul.continuousSMul
  have hBi : Injective (torusAreaForm z) := by
    apply (torusAreaForm z).toLinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have h₁ := congrArg (fun α : TorusModel →L[ℝ] ℝ => α (0,angularUnitVector z.2)) hv
    have h₂ := congrArg (fun α : TorusModel →L[ℝ] ℝ => α (angularUnitVector z.1,0)) hv
    change torusAreaForm z v (0,angularUnitVector z.2)=0 at h₁
    change torusAreaForm z v (angularUnitVector z.1,0)=0 at h₂
    simp only [torusAreaForm_apply,map_zero,mul_zero,mul_one,zero_sub,
      sub_zero,angularUnitVector_value] at h₁ h₂
    have h₁z : v.1=0 := circleAngular_injective z.1 (by simpa only [map_zero] using h₁)
    have h₂z : v.2=0 := circleAngular_injective z.2 (by simpa only [map_zero,neg_eq_zero] using h₂)
    exact Prod.ext h₁z h₂z
  have hd : Module.finrank ℝ TorusModel=Module.finrank ℝ (TorusModel →L[ℝ] ℝ) := by
    calc
      Module.finrank ℝ TorusModel=Module.finrank ℝ (TorusModel →ₗ[ℝ] ℝ) :=
        by simp
      _ = Module.finrank ℝ (TorusModel →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap.finrank_eq
  exact ⟨((torusAreaForm z).toLinearMap.linearEquivOfInjective hBi hd).toContinuousLinearEquiv,rfl⟩

theorem torusAnnularDensity_eq_multiple (b : ℝ) (f : Circle → ℝ) (z : HandleTorus) :
    torusAnnularDensity b f z=(circleClockDensity b z.1*f z.2) • torusAreaForm z := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [torusAnnularDensity,manifoldWedge_apply,torusFirstForm_apply,
    torusHandleForm_apply,weightedCircleAngular,smul_apply,smul_eq_mul,torusAreaForm_apply]
  ring


end

section

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def annularCylinderScalar (F : P × Plane → ℝ) (p : P) (z : HandleCylinder) : ℝ :=
  annularScalarDescent F ((p,z.1),z.2)

theorem annularCylinderScalar_smoothAt {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) {F : P × Plane → ℝ}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => F (p,(s,t))) 1)
    {p : P} (hp : p∈V) {z : HandleCylinder} (hz : z.1∈I) :
    ContMDiffAt 𝓘(ℝ,CylinderModel) 𝓘(ℝ,ℝ) ∞ (annularCylinderScalar F p) z := by
  have hd := (annularScalarDescent_smoothOn hV hI hF hper).contMDiffAt
    (((hV.prod hI).prod isOpen_univ).mem_nhds (show ((p,z.1),z.2)∈_
      from ⟨⟨hp,hz⟩,mem_univ _⟩))
  have hi : ContMDiff 𝓘(ℝ,CylinderModel) ((𝓘(ℝ,P × ℝ)).prod 𝓘(ℝ,CircleModel)) ∞
      (fun z : HandleCylinder => ((p,z.1),z.2)) := by
    rw [show 𝓘(ℝ,CylinderModel) = (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel) from
      modelWithCornersSelf_prod]
    have hfst : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,ℝ) ∞
        (Prod.fst : HandleCylinder → ℝ) := contMDiff_fst
    have hsnd : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,CircleModel) ∞
        (Prod.snd : HandleCylinder → Circle) := contMDiff_snd
    have hpair : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CircleModel)) 𝓘(ℝ,P × ℝ) ∞
        (fun z : HandleCylinder => (p,z.1)) :=
      ((contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun s : ℝ => (p,s))).contMDiff).comp hfst
    exact hpair.prodMk hsnd
  exact hd.comp z hi.contMDiffAt

variable [FiniteDimensional ℝ P]

def cylinderCurvaturePrimitive (a : ℝ) (κ : P × Plane → ℝ) (p : P) :
    ManifoldOneForm CylinderModel HandleCylinder :=
  weightedCylinderAngular (annularCylinderScalar (annularRadialIntegral a κ) p)

theorem cylinderCurvaturePrimitive_smoothAt {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {z : HandleCylinder} (hz : z.1∈I) :
    ContDiffAt ℝ ∞ (chartOneForm (cylinderCurvaturePrimitive a κ p) z)
      (extChartAt 𝓘(ℝ,CylinderModel) z z) :=
  weightedCylinderAngular_smoothAt (annularCylinderScalar_smoothAt hV hI
    (annularRadialIntegral_smooth hV hI hc ha hκ)
    (fun _ hp _ hs => annularRadialIntegral_periodic hc ha hper hp hs) hp hz)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem cylinderCurvaturePrimitive_cover {V : Set P} {I : Set ℝ}
    (hc : Convex ℝ I) {a : ℝ} (ha : a∈I) {κ : P × Plane → ℝ}
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) (v : Plane) :
    cylinderCurvaturePrimitive a κ p (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=
      annularRadialIntegral a κ (p,q)*v.2 := by
  change annularCylinderScalar (annularRadialIntegral a κ) p (cylinderCover q)*
    cylinderAngular (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v)=_
  rw [cylinderAngular_cover]
  change annularScalarDescent (annularRadialIntegral a κ) ((p,q.1),circleTurn q.2)*v.2=_
  rw [annularScalarDescent_turn (annularRadialIntegral_periodic hc ha hper hp hq)]

theorem cylinderCurvaturePrimitive_exterior_cover {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) :
    (manifoldExteriorOneForm (cylinderCurvaturePrimitive a κ p) (cylinderCover q)).bilinearComp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q)=κ (p,q) • planarArea := by
  have hn := euclidean_manifold_pullback_exterior_at cylinderCover_smooth.contMDiffAt
    (cylinderCurvaturePrimitive_smoothAt hV hI hc ha hκ hper hp hq)
  have he : (fun y => euclideanPullbackOneForm (fun _ => cylinderCurvaturePrimitive a κ p)
      cylinderCover (0,y)) =ᶠ[𝓝 q]
      (fun y => planarCovector 0 (annularRadialIntegral a κ (p,y))) := by
    filter_upwards [(hI.prod isOpen_univ).mem_nhds (show q∈I ×ˢ univ from ⟨hq,mem_univ _⟩)] with y hy
    apply ContinuousLinearMap.ext
    intro v
    change cylinderCurvaturePrimitive a κ p (cylinderCover y)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover y v)=_
    rw [cylinderCurvaturePrimitive_cover hc ha hper hp hy.1]
    simp only [planarCovector_apply,zero_mul,zero_add]
  calc
    _ = euclideanExteriorOneForm (fun y => euclideanPullbackOneForm
        (fun _ => cylinderCurvaturePrimitive a κ p) cylinderCover (0,y)) q := hn.symm
    _ = euclideanExteriorOneForm
        (fun y => planarCovector 0 (annularRadialIntegral a κ (p,y))) q := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := (annular_curvature_primitive hV hI hc ha hκ hper).2 p hp q hq


end


open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem circleTurn_derivative_right_inverse (t : ℝ) (v : CircleModel) :
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn t (circleAngular (circleTurn t) v)=v :=
  circleAngular_injective (circleTurn t) (circleAngular_unit_pullback t _)

theorem cylinderCover_derivative_right_inverse (q : Plane) (v : CylinderModel) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
      (v.1,circleAngular (circleTurn q.2) v.2)=v := by
  rw [cylinderCover_derivative,circleTurn_derivative_right_inverse]
  rfl

def cylinderAreaForm : ManifoldTwoForm CylinderModel HandleCylinder :=
  manifoldWedge (fun _ => ContinuousLinearMap.fst ℝ ℝ CircleModel) cylinderAngular

@[simp] theorem cylinderAreaForm_apply (z : HandleCylinder) (v w : CylinderModel) :
    cylinderAreaForm z v w=v.1*circleAngular z.2 w.2-circleAngular z.2 v.2*w.1 := by
  simp only [cylinderAreaForm,manifoldWedge_apply,cylinderAngular_apply]
  rfl

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem cylinderCurvaturePrimitive_exterior_covered {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {q : Plane} (hq : q.1∈I) :
    manifoldExteriorOneForm (cylinderCurvaturePrimitive a κ p) (cylinderCover q)=
      κ (p,q) • cylinderAreaForm (cylinderCover q) := by
  let L : Plane →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q
  have he : (manifoldExteriorOneForm (cylinderCurvaturePrimitive a κ p) (cylinderCover q)).bilinearComp
      L L=κ (p,q) • planarArea :=
    cylinderCurvaturePrimitive_exterior_cover hV hI hc ha hκ hper hp hq
  have hL (v : CylinderModel) : L (v.1,circleAngular (circleTurn q.2) v.2)=v :=
    cylinderCover_derivative_right_inverse q v
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    Ω (v.1,circleAngular (circleTurn q.2) v.2) (w.1,circleAngular (circleTurn q.2) w.2)) he
  simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,smul_eq_mul] at hv
  rw [hL v,hL w] at hv
  simpa only [planarArea_apply,cylinderAreaForm_apply,smul_apply,smul_eq_mul,cylinderCover] using hv

theorem cylinderCurvaturePrimitive_exterior {V : Set P} {I : Set ℝ}
    (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I) {a : ℝ} (ha : a∈I)
    {κ : P × Plane → ℝ} (hκ : ContDiffOn ℝ ∞ κ (V ×ˢ (I ×ˢ univ)))
    (hper : ∀ p∈V,∀ s∈I,Periodic (fun t => κ (p,(s,t))) 1)
    {p : P} (hp : p∈V) {z : HandleCylinder} (hz : z.1∈I) :
    manifoldExteriorOneForm (cylinderCurvaturePrimitive a κ p) z=
      annularCylinderScalar κ p z • cylinderAreaForm z := by
  let q : Plane := (z.1,shortCircleArgument z.2)
  have hq : cylinderCover q=z := by
    apply Prod.ext
    · rfl
    · exact circleTurn_shortCircleArgument z.2
  have hv : annularCylinderScalar κ p (cylinderCover q)=κ (p,q) :=
    annularScalarDescent_turn (hper p hp q.1 hz) q.2
  rw [← hq,hv]
  exact cylinderCurvaturePrimitive_exterior_covered hV hI hc ha hκ hper hp hz



end PackingSufficiencySupport.Hamiltonian
end

end OAI
