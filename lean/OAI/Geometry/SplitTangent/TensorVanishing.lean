import Mathlib
import OAI.Geometry.SplitTangent.BoxMonomials
import OAI.Geometry.SplitTangent.FiniteOpenMaps
import OAI.Geometry.SplitTangent.RationalFamilies
import OAI.Geometry.SplitTangent.GenericFiniteCovering
import OAI.Geometry.SplitTangent.HolomorphicLocalDiffeomorph
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.LeadingJetProduct
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.OpenManifold
import OAI.Geometry.SplitTangent.PolynomialSpecialization
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.DenseRationalVariation

namespace OAI

/-! Tensor Vanishing. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace HolomorphicFrobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def InvolutiveAt (P : E → E →L[ℂ] E) (x : E) : Prop :=
  ∀ V W : E → E, AnalyticAt ℂ V x → AnalyticAt ℂ W x →
    (∀ᶠ y in 𝓝 x, V y∈LinearMap.range (P y).toLinearMap) →
    (∀ᶠ y in 𝓝 x, W y∈LinearMap.range (P y).toLinearMap) →
    ∀ᶠ y in 𝓝 x, VectorField.lieBracket ℂ V W y∈LinearMap.range (P y).toLinearMap

end HolomorphicFrobenius

namespace SplitTangent.ProductTransition
variable {A B C D : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

lemma eventually_factors_snd {f : A × B → C} {x : A × B}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y)
    (hz : ∀ᶠ y in 𝓝 x, ∀a, fderiv ℂ f y (a,0)=0) :
    ∀ᶠ y in 𝓝 x, f y=f (x.1,y.2) := by
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp (hf.and hz)
  have hball : ∀a∈Metric.ball x.1 r, ∀b∈Metric.ball x.2 r,
      DifferentiableAt ℂ f (a,b) ∧ ∀v, fderiv ℂ f (a,b) (v,0)=0 := by
    intro a ha b hb
    exact hs (by simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro ha hb)
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have hab : y.1∈Metric.ball x.1 r ∧ y.2∈Metric.ball x.2 r := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using hy
  have ha := hab.1
  have hb := hab.2
  have hD (a : A) (h : a∈Metric.ball x.1 r) :
      HasFDerivAt (fun t => f (t,y.2)) (0 : A →L[ℂ] C) a := by
    have he : (fderiv ℂ f (a,y.2)).comp
        ((ContinuousLinearMap.id ℂ A).prod (0 : A →L[ℂ] B))=0 := by
      ext v
      exact (hball a h y.2 hb).2 v
    have hp : HasFDerivAt (fun t : A => (t,y.2))
        ((ContinuousLinearMap.id ℂ A).prod (0 : A →L[ℂ] B)) a :=
      (hasFDerivAt_id a).prodMk (hasFDerivAt_const y.2 a)
    simpa only [he,Function.comp_def] using (hball a h y.2 hb).1.hasFDerivAt.comp a hp
  exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero
    (convex_ball x.1 r).isPreconnected (fun a h => (hD a h).differentiableAt.differentiableWithinAt)
    (fun a h => (hD a h).fderiv) ha (Metric.mem_ball_self hr)

lemma eventually_factors_fst {f : A × B → C} {x : A × B}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y)
    (hz : ∀ᶠ y in 𝓝 x, ∀b, fderiv ℂ f y (0,b)=0) :
    ∀ᶠ y in 𝓝 x, f y=f (y.1,x.2) := by
  have hsw : Tendsto (Prod.swap : B × A → A × B) (𝓝 x.swap) (𝓝 x) :=
    continuous_swap.continuousAt
  have hd : ∀ᶠ y in 𝓝 x.swap, DifferentiableAt ℂ (f ∘ Prod.swap) y := by
    filter_upwards [hsw.eventually hf] with y hy
    exact hy.comp y (ContinuousLinearEquiv.prodComm ℂ B A).differentiableAt
  have hd0 : ∀ᶠ y in 𝓝 x.swap, ∀b,
      fderiv ℂ (f ∘ Prod.swap) y (b,0)=0 := by
    filter_upwards [hsw.eventually hf,hsw.eventually hz] with y hy hz
    intro b
    rw [fderiv_comp y hy (ContinuousLinearEquiv.prodComm ℂ B A).differentiableAt]
    change fderiv ℂ f y.swap (fderiv ℂ (ContinuousLinearEquiv.prodComm ℂ B A) y (b,0))=0
    rw [ContinuousLinearEquiv.fderiv]
    exact hz b
  have h := eventually_factors_snd hd hd0
  have hsw' : Tendsto (Prod.swap : A × B → B × A) (𝓝 x) (𝓝 x.swap) :=
    continuous_swap.continuousAt
  simpa using hsw'.eventually h

 
theorem eventually_product [CompleteSpace C] [CompleteSpace D] {f : A × B → C × D} {x : A × B}
    (hf : AnalyticAt ℂ f x)
    (haxes : ∀ᶠ y in 𝓝 x,
      (∀a, (fderiv ℂ f y (a,0)).2=0) ∧
      (∀b, (fderiv ℂ f y (0,b)).1=0)) :
    ∀ᶠ y in 𝓝 x, f y=((f (y.1,x.2)).1,(f (x.1,y.2)).2) := by
  have hd := hf.eventually_analyticAt.mono (fun y hy => hy.differentiableAt)
  have hfst : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (fun y => (f y).1) y :=
    hd.mono (fun y hy => hy.fst)
  have hsnd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ (fun y => (f y).2) y :=
    hd.mono (fun y hy => hy.snd)
  have hfst0 : ∀ᶠ y in 𝓝 x, ∀b, fderiv ℂ (fun y => (f y).1) y (0,b)=0 := by
    filter_upwards [hd,haxes] with y hy ha
    intro b
    rw [fderiv.fst hy]
    exact ha.2 b
  have hsnd0 : ∀ᶠ y in 𝓝 x, ∀a, fderiv ℂ (fun y => (f y).2) y (a,0)=0 := by
    filter_upwards [hd,haxes] with y hy ha
    intro a
    rw [fderiv.snd hy]
    exact ha.1 a
  filter_upwards [eventually_factors_fst hfst hfst0,eventually_factors_snd hsnd hsnd0] with y hy hz
  exact Prod.ext hy hz

end SplitTangent.ProductTransition

open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}

structure AlignedProductChart (S : TangentSplitting X)
    (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] where
  chart : OpenPartialHomeomorph X.Carrier (A × B)
  holomorphic : ContMDiffOn (ModelWithCorners X) 𝓘(ℂ,A × B) ω chart chart.source
  inverse_holomorphic : ContMDiffOn 𝓘(ℂ,A × B) (ModelWithCorners X) ω chart.symm chart.target
  first : ∀y∈chart.source,
    Submodule.map (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) chart y).toLinearMap (S.first y)=
      LinearMap.ker (ContinuousLinearMap.snd ℂ A B).toLinearMap
  second : ∀y∈chart.source,
    Submodule.map (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) chart y).toLinearMap (S.second y)=
      LinearMap.ker (ContinuousLinearMap.fst ℂ A B).toLinearMap

namespace AlignedProductChart
variable {A B C D : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

lemma mdifferentiable (P : AlignedProductChart S A B) :
    P.chart.MDifferentiable (ModelWithCorners X) 𝓘(ℂ,A × B) :=
  ⟨P.holomorphic.mdifferentiableOn (by simp),P.inverse_holomorphic.mdifferentiableOn (by simp)⟩

lemma holomorphicAt (P : AlignedProductChart S A B) {y : X.Carrier}
    (hy : y∈P.chart.source) : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,A × B) ω P.chart y :=
  P.holomorphic.contMDiffAt (P.chart.open_source.mem_nhds hy)

lemma inverse_holomorphicAt (P : AlignedProductChart S A B) {y : A × B}
    (hy : y∈P.chart.target) : ContMDiffAt 𝓘(ℂ,A × B) (ModelWithCorners X) ω P.chart.symm y :=
  P.inverse_holomorphic.contMDiffAt (P.chart.open_target.mem_nhds hy)

lemma inverse_first (P : AlignedProductChart S A B) {y : A × B}
    (hy : y∈P.chart.target) (a : A) :
    mfderiv 𝓘(ℂ,A × B) (ModelWithCorners X) P.chart.symm y (a,0) ∈ S.first (P.chart.symm y) := by
  have hp := P.chart.map_target hy
  have ha : (a,0)∈Submodule.map
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (P.chart.symm y)).toLinearMap
        (S.first (P.chart.symm y)) := by rw [P.first _ hp]; rfl
  obtain ⟨v,hv,he⟩ := ha
  let L : Model X →L[ℂ] A × B :=
    mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (P.chart.symm y)
  let R (z : A × B) : (A × B) →L[ℂ] Model X :=
    mfderiv 𝓘(ℂ,A × B) (ModelWithCorners X) P.chart.symm z
  have hi : R (P.chart (P.chart.symm y)) (L v)=v :=
    DFunLike.congr_fun (P.mdifferentiable.symm_comp_deriv hp) v
  have hi2 : R y (L v)=v :=
    (congrArg (fun z => R z (L v)) (P.chart.right_inv hy)).symm.trans hi
  have hi3 : R y (a,0)=v := (congrArg (R y) he.symm).trans hi2
  exact hi3.symm ▸ hv

lemma inverse_second (P : AlignedProductChart S A B) {y : A × B}
    (hy : y∈P.chart.target) (b : B) :
    mfderiv 𝓘(ℂ,A × B) (ModelWithCorners X) P.chart.symm y (0,b) ∈ S.second (P.chart.symm y) := by
  have hp := P.chart.map_target hy
  have ha : (0,b)∈Submodule.map
      (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (P.chart.symm y)).toLinearMap
        (S.second (P.chart.symm y)) := by rw [P.second _ hp]; rfl
  obtain ⟨v,hv,he⟩ := ha
  let L : Model X →L[ℂ] A × B :=
    mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (P.chart.symm y)
  let R (z : A × B) : (A × B) →L[ℂ] Model X :=
    mfderiv 𝓘(ℂ,A × B) (ModelWithCorners X) P.chart.symm z
  have hi : R (P.chart (P.chart.symm y)) (L v)=v :=
    DFunLike.congr_fun (P.mdifferentiable.symm_comp_deriv hp) v
  have hi2 : R y (L v)=v :=
    (congrArg (fun z => R z (L v)) (P.chart.right_inv hy)).symm.trans hi
  have hi3 : R y (0,b)=v := (congrArg (R y) he.symm).trans hi2
  exact hi3.symm ▸ hv

 

theorem transition_axes (P : AlignedProductChart S A B)
    (Q : AlignedProductChart S C D) {y : A × B}
    (hy : y∈P.chart.target) (hq : P.chart.symm y∈Q.chart.source) :
    ∀ᶠ z in 𝓝 y,
      (∀a, (fderiv ℂ (Q.chart ∘ P.chart.symm) z (a,0)).2=0) ∧
      (∀b, (fderiv ℂ (Q.chart ∘ P.chart.symm) z (0,b)).1=0) := by
  filter_upwards [P.chart.open_target.mem_nhds hy,
    (P.inverse_holomorphicAt hy).continuousAt.preimage_mem_nhds (Q.chart.open_source.mem_nhds hq)]
    with z hz hqz
  have hc := mfderiv_comp z
    ((Q.holomorphicAt hqz).mdifferentiableAt (by simp))
    ((P.inverse_holomorphicAt hz).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hc
  constructor
  · intro a
    have hm := Submodule.mem_map_of_mem
      (f := (mfderiv (ModelWithCorners X) 𝓘(ℂ,C × D) Q.chart (P.chart.symm z)).toLinearMap)
      (P.inverse_first hz a)
    rw [Q.first _ hqz] at hm
    rw [hc]
    exact hm
  · intro b
    have hm := Submodule.mem_map_of_mem
      (f := (mfderiv (ModelWithCorners X) 𝓘(ℂ,C × D) Q.chart (P.chart.symm z)).toLinearMap)
      (P.inverse_second hz b)
    rw [Q.second _ hqz] at hm
    rw [hc]
    exact hm

 

theorem transition_product [CompleteSpace C] [CompleteSpace D]
    (P : AlignedProductChart S A B) (Q : AlignedProductChart S C D) {y : A × B}
    (hy : y∈P.chart.target) (hq : P.chart.symm y∈Q.chart.source) :
    ∀ᶠ z in 𝓝 y, (Q.chart ∘ P.chart.symm) z=
      (((Q.chart ∘ P.chart.symm) (z.1,y.2)).1,
       ((Q.chart ∘ P.chart.symm) (y.1,z.2)).2) := by
  have ha : AnalyticAt ℂ (Q.chart ∘ P.chart.symm) y :=
    ((Q.holomorphicAt hq).comp y (P.inverse_holomorphicAt hy)).contDiffAt.analyticAt
  exact ProductTransition.eventually_product ha (P.transition_axes Q hy hq)

end AlignedProductChart

 


end SplitTangent

open Set Filter Topology Bundle
open scoped Manifold ContDiff
namespace SplitTangent
variable {X : ComplexManifold.{u}}

abbrev chartDerivative (x y : X.Carrier) : Tangent X y →L[ℂ] Model X :=
  mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) y

lemma chartDerivative_isInvertible (x : X.Carrier) {y : X.Carrier}
    (hy : y∈(chartAt (Model X) x).source) :
    (chartDerivative x y).IsInvertible := by
  have h := isInvertible_mfderiv_extChartAt (I := ModelWithCorners X) (x := x)
    (y := y) (by simpa using hy)
  simp only [ModelWithCorners, extChartAt, OpenPartialHomeomorph.extend,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.toFun_eq_coe, modelWithCornersSelf_coe, Function.id_comp] at h
  convert h using 1
  rfl

lemma chartDerivative_inverse (x : X.Carrier) {y : X.Carrier}
    (hy : y∈(chartAt (Model X) x).source) :
    (chartDerivative x y).inverse=
      (trivializationAt (Model X) (Tangent X) x).symmL ℂ y := by
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hy
  change (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ y=
    chartDerivative x y at ht
  rw [← ht]
  apply ContinuousLinearMap.inverse_eq
  · apply ContinuousLinearMap.ext
    intro v
    exact Bundle.Trivialization.continuousLinearMapAt_symmL (R := ℂ)
      (trivializationAt (Model X) (Tangent X) x) hy v
  · apply ContinuousLinearMap.ext
    intro v
    exact Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℂ)
      (trivializationAt (Model X) (Tangent X) x) hy v

lemma chartPullback_holomorphicAt (x : X.Carrier) {y : X.Carrier}
    (hy : y∈(chartAt (Model X) x).source) {V : Model X → Model X}
    (hV : AnalyticAt ℂ V ((chartAt (Model X) x) y)) :
    ContMDiffAt (ModelWithCorners X) ((ModelWithCorners X).prod 𝓘(ℂ,Model X)) ω
      (fun a => (⟨a,VectorField.mpullback (ModelWithCorners X) 𝓘(ℂ,Model X)
        (chartAt (Model X) x) V a⟩ : TangentBundle (ModelWithCorners X) X.Carrier)) y := by
  have hv : ContMDiffAt 𝓘(ℂ,Model X) (𝓘(ℂ,Model X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨z,V z⟩ : TangentBundle 𝓘(ℂ,Model X) (Model X))) ((chartAt (Model X) x) y) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr hV.contDiffAt
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hy
  exact hv.mpullback_vectorField_preimage hc (chartDerivative_isInvertible x hy) (by simp)

lemma chartPullback_bracket (x : X.Carrier) {y : X.Carrier}
    (hy : y∈(chartAt (Model X) x).source) {V W : Model X → Model X}
    (hV : AnalyticAt ℂ V ((chartAt (Model X) x) y))
    (hW : AnalyticAt ℂ W ((chartAt (Model X) x) y)) :
    VectorField.mlieBracket (ModelWithCorners X)
      (VectorField.mpullback (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) V)
      (VectorField.mpullback (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) W) y=
    (chartDerivative x y).inverse
      (VectorField.lieBracket ℂ V W ((chartAt (Model X) x) y)) := by
  have hv : ContMDiffAt 𝓘(ℂ,Model X) (𝓘(ℂ,Model X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨z,V z⟩ : TangentBundle 𝓘(ℂ,Model X) (Model X))) ((chartAt (Model X) x) y) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr hV.contDiffAt
  have hw : ContMDiffAt 𝓘(ℂ,Model X) (𝓘(ℂ,Model X).prod 𝓘(ℂ,Model X)) ω
      (fun z => (⟨z,W z⟩ : TangentBundle 𝓘(ℂ,Model X) (Model X))) ((chartAt (Model X) x) y) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr hW.contDiffAt
  have hc := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hy
  have hh := VectorField.mpullback_mlieBracket (hv.mdifferentiableAt (by simp))
    (hw.mdifferentiableAt (by simp)) hc (by simp)
  have he : VectorField.mlieBracket 𝓘(ℂ,Model X) V W=VectorField.lieBracket ℂ V W := by
    funext a
    unfold VectorField.mlieBracket
    erw [VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ]
  rw [he] at hh
  exact hh.symm

namespace TangentSplitting
variable (S : TangentSplitting X)

lemma coordinateProjector_range_iff (x : X.Carrier) {y : X.Carrier}
    (hy : y∈(chartAt (Model X) x).source) (v : Model X) :
    v∈LinearMap.range (S.coordinateProjector x ((chartAt (Model X) x) y)).toLinearMap ↔
    (chartDerivative x y).inverse v∈S.first y := by
  let D : Tangent X y →L[ℂ] Model X :=
    mfderiv (ModelWithCorners X) 𝓘(ℂ,Model X) (chartAt (Model X) x) y
  have hD : D.IsInvertible := chartDerivative_isInvertible x hy
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := ModelWithCorners X) hy
  change (trivializationAt (Model X) (Tangent X) x).continuousLinearMapAt ℂ y=D at ht
  have hp := S.coordinateProjector_fixed x hy (D.inverse v)
  rw [ht,hD.self_apply_inverse] at hp
  rw [S.mem_first_iff]
  constructor
  · rintro ⟨w,hw⟩
    change S.coordinateProjector x ((chartAt (Model X) x) y) w=v at hw
    have hf : S.coordinateProjector x ((chartAt (Model X) x) y) v=v := by
      rw [← hw,S.coordinateProjector_idempotent x ((chartAt (Model X) x).map_source hy)]
    apply hD.injective
    change D (S.projector y (D.inverse v))=D (D.inverse v)
    rw [← hp,hf,hD.self_apply_inverse]
  · intro hf
    change S.projector y (D.inverse v)=D.inverse v at hf
    refine ⟨v,?_⟩
    change S.coordinateProjector x ((chartAt (Model X) x) y) v=v
    rw [hp,hf,hD.self_apply_inverse]

 

theorem coordinateProjector_involutive (hI : Integrable X S.first)
    (x : X.Carrier) {z : Model X} (hz : z∈(chartAt (Model X) x).target) :
    HolomorphicFrobenius.InvolutiveAt (S.coordinateProjector x) z := by
  intro V W hV hW hPV hPW
  obtain ⟨O,hOsub,hO,hzO⟩ := mem_nhds_iff.mp
    (hV.eventually_analyticAt.and (hW.eventually_analyticAt.and (hPV.and hPW)))
  let c := chartAt (Model X) x
  let U := c.source∩c ⁻¹' O
  have hU : IsOpen U := c.isOpen_inter_preimage hO
  let V' := VectorField.mpullback (ModelWithCorners X) 𝓘(ℂ,Model X) c V
  let W' := VectorField.mpullback (ModelWithCorners X) 𝓘(ℂ,Model X) c W
  have hv' : HolomorphicSectionOn X V' U := by
    intro y hy
    exact (chartPullback_holomorphicAt x hy.1 (hOsub hy.2).1).contMDiffWithinAt
  have hw' : HolomorphicSectionOn X W' U := by
    intro y hy
    exact (chartPullback_holomorphicAt x hy.1 (hOsub hy.2).2.1).contMDiffWithinAt
  have hpv' : ∀y∈U, V' y∈S.first y := by
    intro y hy
    exact (S.coordinateProjector_range_iff x hy.1 _).mp (hOsub hy.2).2.2.1
  have hpw' : ∀y∈U, W' y∈S.first y := by
    intro y hy
    exact (S.coordinateProjector_range_iff x hy.1 _).mp (hOsub hy.2).2.2.2
  filter_upwards [hO.mem_nhds hzO,c.open_target.mem_nhds hz] with a ha hat
  have hay : c (c.symm a)=a := c.right_inv hat
  have hy : c.symm a∈c.source := c.map_target hat
  have hyU : c.symm a∈U := ⟨hy,by change c (c.symm a)∈O; rwa [hay]⟩
  have hb := hI U hU V' W' hv' hw' hpv' hpw' (c.symm a) hyU
  rw [VectorField.mlieBracketWithin_of_isOpen hU hyU] at hb
  have hVa : AnalyticAt ℂ V (c (c.symm a)) := hay.symm ▸ (hOsub ha).1
  have hWa : AnalyticAt ℂ W (c (c.symm a)) := hay.symm ▸ (hOsub ha).2.1
  have he := chartPullback_bracket x hy hVa hWa
  change VectorField.mlieBracket (ModelWithCorners X) V' W' (c.symm a)=_ at he
  rw [he] at hb
  have hh := (S.coordinateProjector_range_iff x hy _).mpr hb
  simpa only [show (chartAt (Model X) x) (c.symm a)=a from hay] using hh

 

lemma coordinateProjector_swap (x : X.Carrier) {z : Model X}
    (hz : z∈(chartAt (Model X) x).target) :
    S.swap.coordinateProjector x z=ContinuousLinearMap.id ℂ (Model X)-S.coordinateProjector x z := by
  let t := trivializationAt (Model X) (Tangent X) x
  have hy : (chartAt (Model X) x).symm z∈t.baseSet := (chartAt (Model X) x).map_target hz
  apply ContinuousLinearMap.ext
  intro v
  change t.continuousLinearMapAt ℂ _ (S.swap.projector _ (t.symmL ℂ _ v))=
    v-t.continuousLinearMapAt ℂ _ (S.projector _ (t.symmL ℂ _ v))
  change t.continuousLinearMapAt ℂ _ (t.symmL ℂ _ v-S.projector _ (t.symmL ℂ _ v))=_
  rw [map_sub,t.continuousLinearMapAt_symmL hy]

end TangentSplitting
end SplitTangent

namespace HolomorphicFrobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma InvolutiveAt.congr {P Q : E → E →L[ℂ] E} {x : E}
    (hP : InvolutiveAt P x) (hPQ : P=ᶠ[𝓝 x] Q) : InvolutiveAt Q x := by
  intro V W hV hW hVm hWm
  have hVm' : ∀ᶠ a in 𝓝 x, V a∈LinearMap.range (P a).toLinearMap := by
    filter_upwards [hPQ,hVm] with a ha hv
    rwa [ha]
  have hWm' : ∀ᶠ a in 𝓝 x, W a∈LinearMap.range (P a).toLinearMap := by
    filter_upwards [hPQ,hWm] with a ha hw
    rwa [ha]
  filter_upwards [hPQ,hP V W hV hW hVm' hWm'] with a ha hb
  rwa [← ha]
end HolomorphicFrobenius

universe v w

 

 

open Set Filter Topology

 

 

section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

namespace SplitTangent

attribute [instance] ComplexManifold.topology ComplexManifold.charts
  ComplexManifold.holomorphicAtlas ComplexManifold.hausdorff
  ComplexManifold.secondCountable

open Filter Topology
namespace TangentSplitting
variable {X : ComplexManifold.{u}} (S : TangentSplitting X)

theorem bracketTensor_eq_zero_of_integrable_firstAlternative (hI : Integrable X S.first) :
    ∀ x, S.bracketTensor x = 0 := by
  intro x
  ext v w
  let V := FiberBundle.extend (Model X) v
  let W := FiberBundle.extend (Model X) w
  obtain ⟨U, hUn, hVU⟩ := FiberBundle.exists_contMDiffOn_extend
    (k := ω) (ModelWithCorners X) (Model X) v
  obtain ⟨U', hUn', hWU'⟩ := FiberBundle.exists_contMDiffOn_extend
    (k := ω) (ModelWithCorners X) (Model X) w
  obtain ⟨O, hOsub, hO, hxO⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hUn hUn')
  have hV : HolomorphicSectionOn X V O := hVU.mono (fun y hy => (hOsub hy).1)
  have hW : HolomorphicSectionOn X W O := hWU'.mono (fun y hy => (hOsub hy).2)
  have hmem := hI O hO (S.projectField V) (S.projectField W)
    (S.holomorphicSectionOn_projectField hV) (S.holomorphicSectionOn_projectField hW)
    (fun y _ => ⟨V y,rfl⟩) (fun y _ => ⟨W y,rfl⟩) x hxO
  rw [S.mem_first_iff_complement_eq_zero,
    VectorField.mlieBracketWithin_of_isOpen hO hxO] at hmem
  have he := S.bracketTensor_apply
    ((hV x hxO).contMDiffAt (hO.mem_nhds hxO) |>.mdifferentiableAt (by simp))
    ((hW x hxO).contMDiffAt (hO.mem_nhds hxO) |>.mdifferentiableAt (by simp))
  simpa [V, W, bracketOperation, hmem] using he

end TangentSplitting

end SplitTangent

open scoped Topology
open Filter

end

open Filter Topology Set
open scoped ContDiff

open Filter Topology Set

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

open Filter Topology

 

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

 

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

 

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

 

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle

 

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
namespace SplitTangent

 

namespace FormalCauchy

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

instance (U : Set ℂ) : CoeFun (AnalyticFunction U) (fun _ => ℂ → ℂ) := ⟨Subtype.val⟩

open scoped MvPowerSeries.WithPiTopology

end FormalCauchy
end SplitTangent

open Set Filter Topology

open Filter Topology

section FiniteBaseImport
open Polynomial
namespace SplitTangent.RationalSurface

local instance tensorVanishingDecidableEqRatFunc : DecidableEq K := Classical.decEq K

variable {ι : Type*} [Fintype ι]

end SplitTangent.RationalSurface

end FiniteBaseImport

open Filter Topology

namespace SplitTangent.ProjectiveEmbedding
section
variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)

theorem cone_local_equationsAlternative [CompactSpace X.Carrier] {v : Fin (e.N+1) → ℂ}
    (hv : v ≠ 0) (hvX : ∃ x, e.Incidence x v) :
    ∃ D : (Fin (e.N+1) → ℂ) → (Fin (e.N+1) → ℂ), AnalyticAt ℂ D v ∧
      ∀ᶠ w in 𝓝 v, (∃ x, e.Incidence x w) ↔ D w = 0 := by
  obtain ⟨x,hx⟩ := hvX
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    ext j
    rw [(e.incidence_iff_coordinates hi).mp hx j,hz,zero_mul]
    rfl
  let c := chartAt (Model X) x
  let H := e.withinChart i x
  let n := e.normalize i
  have hcx : x ∈ c.source := mem_chart_source (Model X) x
  have hn : n v = H (c x) := by
    rw [e.incidence_iff_normalize hi hvi] at hx
    simpa [H,withinChart,c] using hx
  have hH : AnalyticAt ℂ H (c x) := e.withinChart_analytic i x hcx hi
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH
    (e.withinChart_immersion i x hcx hi)
  have hrn : AnalyticAt ℂ (r ∘ n) v := (hn ▸ hr).comp (e.normalize_analytic hvi)
  have hrn0 : r (n v) = c x := hn ▸ hr0
  have heq : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ (e.map y).rep i ≠ 0 ∧
      r (projectiveCoordinates i (e.map y)) = c y := by
    have hri' := (c.continuousAt hcx).eventually hri
    filter_upwards [c.open_source.mem_nhds hcx,(e.open_patch i).mem_nhds hi,hri'] with y hy hiy hry
    refine ⟨hy,hiy,?_⟩
    change r (projectiveCoordinates i (e.map (c.symm (c y)))) = c y at hry
    rwa [c.left_inv hy] at hry
  obtain ⟨U,hUsub,hU,hxU⟩ := _root_.mem_nhds_iff.mp heq
  have hloc := e.incidence_localizes hv hx hU hxU
  have hH' : AnalyticAt ℂ H ((r ∘ n) v) := by simpa only [Function.comp_apply,hrn0] using hH
  have hR : AnalyticAt ℂ (fun w => H (r (n w))) v := hH'.comp hrn
  let D := fun w => H (r (n w)) - n w
  refine ⟨D,hR.sub (e.normalize_analytic hvi),?_⟩
  have hc : ContinuousAt (fun w => c.symm (r (n w))) v := by
    apply (c.continuousAt_symm (c.map_source hcx)).comp_of_eq hrn.continuousAt
    exact hrn0
  have hx0 : c.symm (r (n v)) = x := by rw [hrn0,c.left_inv hcx]
  have hp : ∀ᶠ w in 𝓝 v, (e.map (c.symm (r (n w)))).rep i ≠ 0 :=
    hc.eventually (hx0 ▸ (e.open_patch i).mem_nhds hi)
  have hni : ∀ᶠ w in 𝓝 v, w i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hvi
  filter_upwards [hloc,hp,hni] with w hw hpw hiw
  change (∃ y, e.Incidence y w) ↔ H (r (n w)) - n w = 0
  rw [sub_eq_zero]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hcy,hiy,hry⟩ := hUsub (hw y hy)
    have hnw : n w = projectiveCoordinates i (e.map y) :=
      (e.incidence_iff_normalize hiy hiw).mp hy
    rw [hnw,hry]
    exact congrArg (projectiveCoordinates i ∘ e.map) (c.left_inv hcy)
  · intro h
    refine ⟨c.symm (r (n w)),(e.incidence_iff_normalize hpw hiw).mpr ?_⟩
    exact h.symm

end

variable {X : ComplexManifold.{u}} (e : ProjectiveEmbedding X)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_local_liftAlternative [CompactSpace X.Carrier] {x : X.Carrier}
    {v : Fin (e.N+1) → ℂ} (hv : v ≠ 0) (hx : e.Incidence x v) :
    ∃ L : (Fin (e.N+1) → ℂ) → X.Carrier,
      ContMDiffAt 𝓘(ℂ,Fin (e.N+1) → ℂ) (ModelWithCorners X) ω L v ∧
      ∀ᶠ w in 𝓝 v, ∀ y, e.Incidence y w → L w = y := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map x).rep_nonzero
  change (e.map x).rep i ≠ 0 at hi
  have hvi : v i ≠ 0 := by
    intro hz
    apply hv
    ext j
    rw [(e.incidence_iff_coordinates hi).mp hx j,hz,zero_mul]
    rfl
  let c := chartAt (Model X) x
  let H := e.withinChart i x
  let n := e.normalize i
  have hcx : x ∈ c.source := mem_chart_source (Model X) x
  have hn : n v = H (c x) := by
    rw [e.incidence_iff_normalize hi hvi] at hx
    simpa [H,withinChart,c] using hx
  have hH : AnalyticAt ℂ H (c x) := e.withinChart_analytic i x hcx hi
  obtain ⟨r,hr,hr0,hri⟩ := AnalyticRetraction.exists_left_inverse hH
    (e.withinChart_immersion i x hcx hi)
  have hrn : AnalyticAt ℂ (r ∘ n) v := (hn ▸ hr).comp (e.normalize_analytic hvi)
  have hrn0 : r (n v) = c x := hn ▸ hr0
  have heq : ∀ᶠ y in 𝓝 x, y ∈ c.source ∧ (e.map y).rep i ≠ 0 ∧
      r (projectiveCoordinates i (e.map y)) = c y := by
    have hri' := (c.continuousAt hcx).eventually hri
    filter_upwards [c.open_source.mem_nhds hcx,(e.open_patch i).mem_nhds hi,hri'] with y hy hiy hry
    refine ⟨hy,hiy,?_⟩
    change r (projectiveCoordinates i (e.map (c.symm (c y)))) = c y at hry
    rwa [c.left_inv hy] at hry
  obtain ⟨U,hUsub,hU,hxU⟩ := _root_.mem_nhds_iff.mp heq
  have hloc := e.incidence_localizes hv hx hU hxU
  refine ⟨c.symm ∘ (r ∘ n),?_,?_⟩
  · have hc := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x)
        (c.map_source hcx)
    exact hc.comp_of_eq hrn.contDiffAt.contMDiffAt hrn0
  · have hni : ∀ᶠ w in 𝓝 v, w i ≠ 0 := (continuous_apply i).continuousAt.eventually_ne hvi
    filter_upwards [hloc,hni] with w hw hiw y hy
    obtain ⟨hcy,hiy,hry⟩ := hUsub (hw y hy)
    have hnw : n w = projectiveCoordinates i (e.map y) :=
      (e.incidence_iff_normalize hiy hiw).mp hy
    dsimp only [Function.comp_apply]
    rw [hnw,hry,c.left_inv hcy]

end SplitTangent.ProjectiveEmbedding

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff

 

open Set Filter Topology
open scoped ContDiff ENNReal

 

open Set Filter Topology
open scoped ContDiff ENNReal

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

 

 

open Set Filter Topology
open scoped ContDiff ENNReal

namespace HolomorphicFlow
variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

 
def pointwiseMultilinear {n : ℕ} (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F) :
    MultilinearMap ℂ (fun _ : Fin n => C(K,E)) C(K,F) where
  toFun v := ⟨fun s => p (fun i => v i s),
    p.cont.comp (continuous_pi fun i => (v i).continuous)⟩
  map_update_add' v i a b := by
    ext s
    have he (w : C(K,E)) : (fun j => Function.update v i w j s) =
        Function.update (fun j => v j s) i (w s) := by
      funext j; by_cases h : j=i <;> simp [h]
    simpa only [ContinuousMap.coe_mk, ContinuousMap.add_apply, he] using
      p.map_update_add (fun j => v j s) i (a s) (b s)
  map_update_smul' v i a b := by
    ext s
    have he (w : C(K,E)) : (fun j => Function.update v i w j s) =
        Function.update (fun j => v j s) i (w s) := by
      funext j; by_cases h : j=i <;> simp [h]
    simpa only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, he] using
      p.map_update_smul (fun j => v j s) i a (b s)

lemma pointwiseMultilinear_bound {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F)
    (v : Fin n → C(K,E)) :
    ‖pointwiseMultilinear p v‖ ≤ ‖p‖ * ∏i, ‖v i‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro s
  change ‖p (fun i => v i s)‖ ≤ _
  exact p.le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => (v i).norm_coe_le_norm s))
    (norm_nonneg p))

def pointwiseCoefficient {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => C(K,E)) C(K,F) :=
  (pointwiseMultilinear (K := K) p).mkContinuous ‖p‖ (pointwiseMultilinear_bound (K := K) p)

@[simp] theorem pointwiseCoefficient_apply {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F)
    (v : Fin n → C(K,E)) (s : K) : pointwiseCoefficient p v s = p (fun i => v i s) := rfl

lemma pointwiseCoefficient_norm {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F) :
    ‖pointwiseCoefficient (K := K) p‖ ≤ ‖p‖ :=
  (pointwiseMultilinear (K := K) p).mkContinuous_norm_le (norm_nonneg p) (pointwiseMultilinear_bound (K := K) p)

def pointwiseSeries (p : FormalMultilinearSeries ℂ E F) :
    FormalMultilinearSeries ℂ C(K,E) C(K,F) := fun n => pointwiseCoefficient (p n)

lemma pointwiseSeries_radius (p : FormalMultilinearSeries ℂ E F) :
    p.radius ≤ (pointwiseSeries (K := K) p).radius := by
  apply iSup_le
  intro r
  apply iSup_le
  intro C
  apply iSup_le
  intro h
  apply FormalMultilinearSeries.le_radius_of_bound _ C
  intro n
  exact (mul_le_mul_of_nonneg_right (pointwiseCoefficient_norm (K := K) (p n))
    (by positivity)).trans (h n)

variable [CompleteSpace F]

lemma pointwiseSeries_sum {p : FormalMultilinearSeries ℂ E F} {v : C(K,E)}
    (hv : v ∈ Metric.eball 0 p.radius) (s : K) :
    (pointwiseSeries p).sum v s = p.sum (v s) := by
  have hv' : v ∈ Metric.eball 0 (pointwiseSeries (K := K) p).radius :=
    Metric.eball_subset_eball (pointwiseSeries_radius p) hv
  have h := ((pointwiseSeries (K := K) p).hasSum hv').mapL (ContinuousMap.evalCLM ℂ s)
  simpa only [ContinuousMap.evalCLM_apply, pointwiseSeries, pointwiseCoefficient_apply,
    FormalMultilinearSeries.sum] using h.tsum_eq.symm

 

theorem exists_analytic_path_map {f : E → F} {x₀ : E} (hf : AnalyticAt ℂ f x₀) :
    ∃ N : C(K,E) → C(K,F), AnalyticAt ℂ N 0 ∧
      ∀ᶠ v in 𝓝 0, ∀ s, N v s = f (x₀ + v s) := by
  obtain ⟨p,r,hp⟩ := hf
  let N := (pointwiseSeries (K := K) p).sum
  have hr : 0 < (pointwiseSeries (K := K) p).radius :=
    hp.r_pos.trans_le (hp.r_le.trans (pointwiseSeries_radius (K := K) p))
  refine ⟨N,((pointwiseSeries (K := K) p).hasFPowerSeriesOnBall hr).analyticAt,?_⟩
  filter_upwards [Metric.eball_mem_nhds (0 : C(K,E)) hp.r_pos] with v hv
  intro s
  have hvs : v s ∈ Metric.eball 0 r := by
    simp only [Metric.mem_eball, edist_zero_right] at hv ⊢
    have hn : ‖v s‖₊ ≤ ‖v‖₊ := v.norm_coe_le_norm s
    have hn' : (‖v s‖₊ : ℝ≥0∞) ≤ (‖v‖₊ : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hn
    exact lt_of_le_of_lt hn' hv
  exact (pointwiseSeries_sum (K := K) (p := p) (Metric.eball_subset_eball hp.r_le hv) s).trans
    (hp.sum hvs).symm

end HolomorphicFlow

 

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HolomorphicFlow
abbrev Time := Set.Icc (0 : ℝ) 1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def constantPath : E →L[ℂ] C(Time,E) where
  toFun x := ContinuousMap.const Time x
  map_add' x y := by ext; rfl
  map_smul' a x := by ext; rfl
  cont := ContinuousMap.continuous_const'

omit [CompleteSpace E] in
@[simp] lemma constantPath_apply (x : E) (s : Time) : constantPath x s = x := rfl

 
def extendPath (u : C(Time,E)) : ℝ → E := fun s => u (projIcc 0 1 (by norm_num) s)

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma extendPath_continuous (u : C(Time,E)) : Continuous (extendPath u) :=
  u.continuous.comp continuous_projIcc

omit [NormedSpace ℂ E] [CompleteSpace E] in
@[simp] lemma extendPath_val (u : C(Time,E)) (s : Time) : extendPath u s = u s := by
  simp [extendPath]

 
def volterraPath (u : C(Time,E)) : C(Time,E) where
  toFun s := ∫ t in (0 : ℝ)..s.1, extendPath u t
  continuous_toFun := by
    have hc : Continuous (fun s : ℝ => ∫t in (0 : ℝ)..s, extendPath u t) :=
      continuous_iff_continuousAt.mpr fun s =>
        (intervalIntegral.integral_hasDerivAt_right
          ((extendPath_continuous u).intervalIntegrable 0 s)
          (extendPath_continuous u).stronglyMeasurable.stronglyMeasurableAtFilter
          (extendPath_continuous u).continuousAt).continuousAt
    exact hc.comp continuous_subtype_val

lemma volterraPath_bound (u : C(Time,E)) : ‖volterraPath u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro s
  change ‖∫t in (0 : ℝ)..s.1, extendPath u t‖ ≤ ‖u‖
  calc
    _ ≤ ‖u‖ * |s.1 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _ => u.norm_coe_le_norm (projIcc 0 1 (by norm_num) t))
    _ ≤ ‖u‖ := by
      rw [sub_zero,abs_of_nonneg s.property.1]
      exact mul_le_of_le_one_right (norm_nonneg u) s.property.2

def volterraLinear : C(Time,E) →ₗ[ℂ] C(Time,E) where
  toFun := volterraPath
  map_add' u v := by
    ext s
    change (∫t in (0 : ℝ)..s.1, extendPath (u+v) t) = _
    simpa only [extendPath, ContinuousMap.add_apply, volterraPath, ContinuousMap.coe_mk]
      using intervalIntegral.integral_add
        ((extendPath_continuous u).intervalIntegrable 0 s.1)
        ((extendPath_continuous v).intervalIntegrable 0 s.1)
  map_smul' a u := by
    ext s
    change (∫t in (0 : ℝ)..s.1, extendPath (a • u) t) = _
    simpa only [extendPath, ContinuousMap.smul_apply, volterraPath, ContinuousMap.coe_mk, RingHom.id_apply]
      using intervalIntegral.integral_smul a (extendPath u)

 

def volterra : C(Time,E) →L[ℂ] C(Time,E) :=
  (volterraLinear (E := E)).mkContinuous 1 (by intro u; simpa only [one_mul, volterraLinear, LinearMap.coe_mk, AddHom.coe_mk] using volterraPath_bound u)

@[simp] lemma volterra_apply (u : C(Time,E)) (s : Time) :
    volterra u s = ∫t in (0 : ℝ)..s.1, extendPath u t := rfl

@[simp] lemma volterra_zero (u : C(Time,E)) : volterra u ⟨0, by constructor <;> norm_num⟩ = 0 := by
  simp

lemma volterra_hasDerivAt (u : C(Time,E)) (s : ℝ) :
    HasDerivAt (fun r => ∫t in (0 : ℝ)..r, extendPath u t) (extendPath u s) s := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((extendPath_continuous u).intervalIntegrable 0 s)
    (extendPath_continuous u).stronglyMeasurable.stronglyMeasurableAtFilter
    (extendPath_continuous u).continuousAt

end HolomorphicFlow

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFlow
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

 

theorem analytic_implicit_of_snd {H : A × B → B} (hH : AnalyticAt ℂ H 0)
    (hzero : H 0=0) (hder : fderiv ℂ H 0 = ContinuousLinearMap.snd ℂ A B) :
    ∃ g : A → B, AnalyticAt ℂ g 0 ∧ g 0=0 ∧
      (∀ᶠ a in 𝓝 0, H (a,g a)=0) ∧
      (∀ᶠ z : A × B in 𝓝 0, H z=0 ↔ g z.1=z.2) := by
  let φ : ImplicitFunctionData ℂ (A × B) B A :=
    { leftFun := H
      leftDeriv := ContinuousLinearMap.snd ℂ A B
      rightFun := Prod.fst
      rightDeriv := ContinuousLinearMap.fst ℂ A B
      pt := 0
      hasStrictFDerivAt_leftFun := by
        rw [← hder]
        exact (hH.contDiffAt (n := ω)).hasStrictFDerivAt (by simp)
      hasStrictFDerivAt_rightFun := hasStrictFDerivAt_fst
      range_leftDeriv := LinearMap.range_eq_top.mpr (fun b => ⟨(0,b),rfl⟩)
      range_rightDeriv := LinearMap.range_eq_top.mpr (fun a => ⟨(a,0),rfl⟩)
      isCompl_ker := by
        change IsCompl (LinearMap.ker (LinearMap.snd ℂ A B))
          (LinearMap.ker (LinearMap.fst ℂ A B))
        rw [LinearMap.ker_snd,LinearMap.ker_fst]
        exact LinearMap.isCompl_range_inl_inr }
  have hbase : φ.prodFun φ.pt = (0,0) := by
    simp [φ,ImplicitFunctionData.prodFun,hzero]
  have hana : AnalyticAt ℂ φ.implicitFunction.uncurry (0,0) := by
    rw [← hbase]
    exact (φ.contDiffAt_implicitFunction hH.contDiffAt contDiffAt_fst (by simp)).analyticAt
  let F : A → A × B := fun a => φ.implicitFunction 0 a
  let g : A → B := fun a => (F a).2
  have hF : AnalyticAt ℂ F 0 :=
    hana.comp (analyticAt_const.prod analyticAt_id)
  have hval : F 0=0 := by
    have hh := mem_of_mem_nhds φ.implicitFunction_apply_image
    simpa [φ,hzero,F] using hh
  have hgood : ∀ᶠ a in 𝓝 (0 : A), H (F a)=0 ∧ (F a).1=a := by
    have he := φ.prodFun_implicitFunction
    rw [hbase] at he
    have ht : Tendsto (fun a : A => ((0 : B),a)) (𝓝 0) (𝓝 (0,0)) := (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [ht.eventually he] with a ha
    exact ⟨congrArg Prod.fst ha,congrArg Prod.snd ha⟩
  refine ⟨g,analyticAt_snd.comp hF,congrArg Prod.snd hval,?_,?_⟩
  · filter_upwards [hgood] with a ha
    have he : (a,g a)=F a := Prod.ext ha.2.symm rfl
    rw [he]
    exact ha.1
  · have ht : Tendsto (Prod.fst : A × B → A) (𝓝 0) (𝓝 0) := continuous_fst.continuousAt
    filter_upwards [φ.leftFun_eq_iff_implicitFunction,ht.eventually hgood] with z hz hg
    have hz' : H z=0 ↔ F z.1=z := by
      change H z=H 0 ↔ φ.implicitFunction (H 0) z.1=z at hz
      rwa [hzero] at hz
    constructor
    · intro hh
      exact congrArg Prod.snd (hz'.mp hh)
    · intro hh
      apply hz'.mpr
      exact Prod.ext hg.2 hh

end HolomorphicFlow

 

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFlow
variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

 

theorem analytic_integral_equation_unique (C : E →L[ℂ] B) {Φ : B → B}
    (hΦ : AnalyticAt ℂ Φ 0) :
    ∃ u : ℂ × E → B, AnalyticAt ℂ u 0 ∧ u 0=0 ∧
      (∀ᶠ a in 𝓝 0, u a = C a.2 + a.1 • Φ (u a)) ∧
      (∀ᶠ z : (ℂ × E) × B in 𝓝 0,
        z.2 = C z.1.2 + z.1.1 • Φ z.2 ↔ u z.1=z.2) := by
  let Q := Φ 0
  let L : (ℂ × E) × B → B := fun z => C z.1.2 + z.1.1 • Q + z.2
  have hL : AnalyticAt ℂ L 0 :=
    (((C.analyticAt _).comp (analyticAt_snd.comp analyticAt_fst)).add
      ((analyticAt_fst.comp analyticAt_fst).smul analyticAt_const)).add analyticAt_snd
  have hL0 : L 0=0 := by simp [L]
  let R : (ℂ × E) × B → B := fun z => Φ (L z)-Q
  have hR : AnalyticAt ℂ R 0 := by
    have hΦL : AnalyticAt ℂ Φ (L 0) := hL0.symm ▸ hΦ
    exact (hΦL.comp hL).sub analyticAt_const
  have hR0 : R 0=0 := by simp [R,hL0,Q]
  let H : (ℂ × E) × B → B := fun z => z.2-z.1.1 • R z
  have hH : AnalyticAt ℂ H 0 :=
    analyticAt_snd.sub ((analyticAt_fst.comp analyticAt_fst).smul hR)
  have hH0 : H 0=0 := by simp [H]
  have hd : fderiv ℂ H 0 = ContinuousLinearMap.snd ℂ (ℂ × E) B := by
    have ht : HasFDerivAt (fun z : (ℂ × E) × B => z.1.1)
        ((ContinuousLinearMap.fst ℂ ℂ E).comp (ContinuousLinearMap.fst ℂ (ℂ × E) B)) 0 :=
      hasFDerivAt_fst.comp _ hasFDerivAt_fst
    have hh := hasFDerivAt_snd.sub (ht.smul hR.differentiableAt.hasFDerivAt)
    simpa only [hR0, Prod.fst_zero, zero_smul, Pi.smul_def', Pi.sub_def, H,
      ContinuousLinearMap.smulRight_zero, add_zero, sub_zero] using hh.fderiv
  obtain ⟨w,hw,hw0,he,huniq⟩ := analytic_implicit_of_snd hH hH0 hd
  let u : ℂ × E → B := fun a => C a.2 + a.1 • Q + w a
  have hu : AnalyticAt ℂ u 0 :=
    (((C.analyticAt _).comp analyticAt_snd).add (analyticAt_fst.smul analyticAt_const)).add hw
  refine ⟨u,hu,by simp [u,hw0],?_,?_⟩
  · filter_upwards [he] with a ha
    change w a-a.1 • (Φ (u a)-Q)=0 at ha
    have ha' : w a = a.1 • Φ (u a)-a.1 • Q := by
      rw [← smul_sub]
      exact sub_eq_zero.mp ha
    calc
      u a = C a.2 + a.1 • Q + w a := rfl
      _ = C a.2 + a.1 • Φ (u a) := by rw [ha']; abel
  · let G : (ℂ × E) × B → (ℂ × E) × B :=
      fun z => (z.1,z.2-(C z.1.2+z.1.1 • Q))
    have hG : Continuous G := by dsimp [G]; fun_prop
    have hG0 : G 0=0 := by simp [G]
    have ht : Tendsto G (𝓝 0) (𝓝 0) := by
      have hh : Tendsto G (𝓝 0) (𝓝 (G 0)) := hG.continuousAt
      simpa only [hG0] using hh
    filter_upwards [ht.eventually huniq] with z hz
    have hLG : L (G z)=z.2 := by dsimp [L,G]; abel
    have hHG : H (G z)=z.2-(C z.1.2+z.1.1 • Φ z.2) := by
      dsimp only [H,R]
      rw [hLG]
      dsimp only [G]
      rw [smul_sub]
      abel
    have heq : H (G z)=0 ↔ z.2=C z.1.2+z.1.1 • Φ z.2 := by
      rw [hHG,sub_eq_zero]
    have heq' : w (G z).1=(G z).2 ↔ u z.1=z.2 := by
      change w z.1=z.2-(C z.1.2+z.1.1 • Q) ↔
        (C z.1.2+z.1.1 • Q)+w z.1=z.2
      rw [eq_sub_iff_add_eq,add_comm (w z.1)]
    exact heq.symm.trans (hz.trans heq')

 
theorem analytic_integral_equation (C : E →L[ℂ] B) {Φ : B → B}
    (hΦ : AnalyticAt ℂ Φ 0) :
    ∃ u : ℂ × E → B, AnalyticAt ℂ u 0 ∧ u 0=0 ∧
      (∀ᶠ a in 𝓝 0, u a = C a.2 + a.1 • Φ (u a)) := by
  obtain ⟨u,hu,hu0,he,_⟩ := analytic_integral_equation_unique C hΦ
  exact ⟨u,hu,hu0,he⟩

end HolomorphicFlow

 

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HolomorphicFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def PathEquation (f : E → E) (x₀ : E) (a : ℂ × E) (v : C(Time,E)) : Prop :=
  ∀ s : Time, v s = a.2 + a.1 • ∫r in (0 : ℝ)..s.1, f (x₀ + extendPath v r)

lemma pathEquation_iff {f : E → E} {x₀ : E} {a : ℂ × E}
    {v Nv : C(Time,E)} (hNv : ∀s, Nv s=f (x₀+v s)) :
    PathEquation f x₀ a v ↔ v=constantPath a.2+a.1 • volterra Nv := by
  have he (r : ℝ) : extendPath Nv r=f (x₀+extendPath v r) := hNv _
  rw [ContinuousMap.ext_iff]
  simp only [PathEquation,ContinuousMap.add_apply,constantPath_apply,
    ContinuousMap.smul_apply,volterra_apply,he]

 

theorem exists_analytic_paths {f : E → E} {x₀ : E} (hf : AnalyticAt ℂ f x₀) :
    ∃ u : ℂ × E → C(Time,E), AnalyticAt ℂ u 0 ∧ u 0=0 ∧
      (∀ᶠ a in 𝓝 0, PathEquation f x₀ a (u a)) ∧
      (∀ᶠ z : (ℂ × E) × C(Time,E) in 𝓝 0,
        PathEquation f x₀ z.1 z.2 ↔ u z.1=z.2) := by
  obtain ⟨N,hN,hNa⟩ := exists_analytic_path_map (K := Time) hf
  let Φ : C(Time,E) → C(Time,E) := fun v => volterra (N v)
  have hΦ : AnalyticAt ℂ Φ 0 := ((volterra (E := E)).analyticAt (N 0)).comp hN
  obtain ⟨u,hu,hu0,he,huniq⟩ := analytic_integral_equation_unique (constantPath (E := E)) hΦ
  have ht : Tendsto u (𝓝 0) (𝓝 0) := hu0 ▸ hu.continuousAt
  refine ⟨u,hu,hu0,?_,?_⟩
  · filter_upwards [he,ht.eventually hNa] with a ha hna
    exact (pathEquation_iff hna).mpr ha
  · have ht' : Tendsto (Prod.snd : (ℂ × E) × C(Time,E) → C(Time,E))
        (𝓝 0) (𝓝 0) := continuous_snd.continuousAt
    filter_upwards [huniq,ht'.eventually hNa] with z hz hna
    exact (pathEquation_iff hna).trans hz

 
omit [CompleteSpace E] in
lemma PathEquation.zero {f : E → E} {x₀ : E} {a : ℂ × E} {v : C(Time,E)}
    (h : PathEquation f x₀ a v) : v ⟨0,by constructor <;> norm_num⟩=a.2 := by
  simpa only [intervalIntegral.integral_same, smul_zero, add_zero] using
    h ⟨0,by constructor <;> norm_num⟩

 
omit [CompleteSpace E] in
lemma PathEquation.at_zero_time {f : E → E} {x₀ x : E} {v : C(Time,E)}
    (h : PathEquation f x₀ (0,x) v) : v=constantPath x := by
  ext s
  simpa using h s

end HolomorphicFlow

 

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HolomorphicFlow
variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma eventually_pointwise {P : E → Prop} {x₀ : E} (hP : ∀ᶠ x in 𝓝 x₀, P x) :
    ∀ᶠ v : C(K,E) in 𝓝 0, ∀s, P (x₀+v s) := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hP
  filter_upwards [Metric.ball_mem_nhds (0 : C(K,E)) hr] with v hv
  intro s
  apply hsub
  simp only [Metric.mem_ball,dist_zero_right] at hv
  simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
  exact (v.norm_coe_le_norm s).trans_lt hv

lemma eventually_continuous_integrand {f : E → E} {x₀ : E} (hf : AnalyticAt ℂ f x₀) :
    ∀ᶠ v : C(Time,E) in 𝓝 0, Continuous (fun r : ℝ => f (x₀+extendPath v r)) := by
  filter_upwards [eventually_pointwise hf.eventually_analyticAt] with v hv
  apply continuous_iff_continuousAt.mpr
  intro r
  have hf' : ContinuousAt f (x₀+extendPath v r) :=
    (hv (projIcc 0 1 (by norm_num) r)).continuousAt
  have hg : ContinuousAt (fun r : ℝ => x₀+extendPath v r) r :=
    (continuous_const.add (extendPath_continuous v)).continuousAt
  exact hf'.tendsto.comp hg.tendsto

 
def realizedPath (f : E → E) (x₀ : E) (a : ℂ × E) (v : C(Time,E)) (r : ℝ) : E :=
  x₀+a.2+a.1 • ∫s in (0 : ℝ)..r, f (x₀+extendPath v s)

omit [CompleteSpace E] in
lemma PathEquation.realized_eq {f : E → E} {x₀ : E} {a : ℂ × E} {v : C(Time,E)}
    (h : PathEquation f x₀ a v) (s : Time) : realizedPath f x₀ a v s.1=x₀+v s := by
  rw [h s]
  exact add_assoc _ _ _

lemma realizedPath_hasDerivAt {f : E → E} {x₀ : E} {a : ℂ × E} {v : C(Time,E)}
    (hc : Continuous (fun r : ℝ => f (x₀+extendPath v r))) (r : ℝ) :
    HasDerivAt (realizedPath f x₀ a v) (a.1 • f (x₀+extendPath v r)) r := by
  exact ((intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_smul a.1).const_add _

end HolomorphicFlow

 

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HolomorphicFlow
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def scaleTime (c s : Time) : Time := ⟨c.1*s.1,
  ⟨mul_nonneg c.property.1 s.property.1,
    (mul_le_mul_of_nonneg_left s.property.2 c.property.1).trans
      (by simpa using c.property.2)⟩⟩

def rescale (c : Time) (v : C(Time,E)) : C(Time,E) where
  toFun s := v (scaleTime c s)
  continuous_toFun := v.continuous.comp
    ((continuous_const.mul continuous_subtype_val).subtype_mk _)

omit [NormedSpace ℂ E] [CompleteSpace E] in
@[simp] lemma rescale_apply (c s : Time) (v : C(Time,E)) :
    HolomorphicFlow.rescale c v s = v (scaleTime c s) := rfl

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma rescale_norm (c : Time) (v : C(Time,E)) : ‖HolomorphicFlow.rescale c v‖ ≤ ‖v‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg v)).mpr fun _ => v.norm_coe_le_norm _

def scaleParameter (c : Time) (a : ℂ × E) : ℂ × E := (c.1 • a.1,a.2)

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma scaleParameter_norm (c : Time) (a : ℂ × E) :
    ‖scaleParameter c a‖ ≤ ‖a‖ := by
  simp only [scaleParameter,Prod.norm_def,norm_smul,Real.norm_of_nonneg c.property.1]
  exact max_le_max (mul_le_of_le_one_left (norm_nonneg a.1) c.property.2) le_rfl

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma extendPath_rescale (c s : Time) (v : C(Time,E)) {r : ℝ}
    (hr : r∈Icc 0 s.1) : extendPath (HolomorphicFlow.rescale c v) r=extendPath v (c.1*r) := by
  have hr' : r∈Icc (0 : ℝ) 1 := ⟨hr.1,hr.2.trans s.property.2⟩
  have hcr : c.1*r∈Icc (0 : ℝ) 1 := (scaleTime c ⟨r,hr'⟩).property
  simp only [extendPath,projIcc_of_mem _ hr',projIcc_of_mem _ hcr,
    rescale_apply,scaleTime]

omit [CompleteSpace E] in
lemma PathEquation.rescale {f : E → E} {x₀ : E} {a : ℂ × E} {v : C(Time,E)}
    (h : PathEquation f x₀ a v) (c : Time) :
    PathEquation f x₀ (scaleParameter c a) (HolomorphicFlow.rescale c v) := by
  intro s
  change v (scaleTime c s)=a.2+(c.1 • a.1) • _
  rw [h (scaleTime c s)]
  change a.2+a.1 • (∫r in (0 : ℝ)..c.1*s.1, f (x₀+extendPath v r)) = _
  by_cases hc : c.1=0
  · simp [hc]
  · have hi : (∫r in (0 : ℝ)..c.1*s.1, f (x₀+extendPath v r)) =
        c.1 • (∫r in (0 : ℝ)..s.1, f (x₀+extendPath v (c.1*r))) := by
      rw [intervalIntegral.integral_comp_mul_left (fun r => f (x₀+extendPath v r)) hc]
      simp only [smul_smul,mul_inv_cancel₀ hc,one_smul,mul_zero]
    rw [hi]
    have hj : (∫r in (0 : ℝ)..s.1, f (x₀+extendPath v (c.1*r))) =
        ∫r in (0 : ℝ)..s.1, f (x₀+extendPath (HolomorphicFlow.rescale c v) r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le s.property.1] at hr
      exact congrArg (fun w : E => f (x₀+w)) (extendPath_rescale c s v hr).symm
    rw [hj,smul_comm,smul_assoc]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

omit [CompleteSpace E] in
theorem eventually_rescale {f : E → E} {x₀ : E} {u : ℂ × E → C(Time,E)}
    (hu : ContinuousAt u 0) (hu0 : u 0=0)
    (he : ∀ᶠ a in 𝓝 0, PathEquation f x₀ a (u a))
    (huniq : ∀ᶠ z : (ℂ × E) × C(Time,E) in 𝓝 0,
      PathEquation f x₀ z.1 z.2 ↔ u z.1=z.2) :
    ∀ᶠ a in 𝓝 0, ∀c : Time, u (scaleParameter c a)=rescale c (u a) := by
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp huniq
  have ht : Tendsto u (𝓝 0) (𝓝 0) := by
    have hh : Tendsto u (𝓝 0) (𝓝 (u 0)) := hu
    simpa only [hu0] using hh
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ × E) hε,
    ht.eventually (Metric.ball_mem_nhds (0 : C(Time,E)) hε),he] with a ha hua hea
  intro c
  have hz : (scaleParameter c a,rescale c (u a))∈Metric.ball 0 ε := by
    simp only [Metric.mem_ball,dist_zero_right] at ha hua
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def]
    exact max_lt ((scaleParameter_norm c a).trans_lt ha) ((rescale_norm c (u a)).trans_lt hua)
  exact (hsub hz).mp (hea.rescale c)

end HolomorphicFlow

 

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace HolomorphicFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

abbrev finalTime : Time := ⟨1, by constructor <;> norm_num⟩

def endpoint (x₀ : E) (u : ℂ × E → C(Time,E)) (a : ℂ × E) : E :=
  x₀+u a finalTime

omit [CompleteSpace E] in
lemma endpoint_analytic {x₀ : E} {u : ℂ × E → C(Time,E)}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (endpoint x₀ u) 0 := by
  have hv : AnalyticAt ℂ (fun v : C(Time,E) => v finalTime) (u 0) :=
    (ContinuousMap.evalCLM ℂ finalTime).analyticAt (u 0)
  exact analyticAt_const.add (hv.comp hu)

lemma rescale_endpoint_derivative {f : E → E} {x₀ : E}
    {u : ℂ × E → C(Time,E)} {a : ℂ × E}
    (hA : AnalyticAt ℂ (endpoint x₀ u) a)
    (he : PathEquation f x₀ a (u a))
    (hc : Continuous (fun r : ℝ => f (x₀+extendPath (u a) r)))
    (hs : ∀c : Time, u (scaleParameter c a)=rescale c (u a)) :
    fderiv ℂ (endpoint x₀ u) a (a.1,0)=a.1 • f (endpoint x₀ u a) := by
  let c : ℝ → ℂ × E := fun r => (r • a.1,a.2)
  have hca : c 1=a := by simp [c]
  have hcd : HasDerivAt c (a.1,0) 1 := by
    simpa only [one_smul,id_eq,c] using ((hasDerivAt_id (1 : ℝ)).smul_const a.1).prodMk
      (hasDerivAt_const (1 : ℝ) a.2)
  have hd : HasDerivAt ((endpoint x₀ u) ∘ c)
      (fderiv ℂ (endpoint x₀ u) a (a.1,0)) (1 : ℝ) := by
    have hdf : HasFDerivAt (endpoint x₀ u)
        (fderiv ℂ (endpoint x₀ u) a) (c 1) := hca.symm ▸ hA.differentiableAt.hasFDerivAt
    exact (hdf.restrictScalars ℝ).comp_hasDerivAt 1 hcd
  have heq (r : ℝ) (hr : r∈Icc 0 1) :
      ((endpoint x₀ u) ∘ c) r=realizedPath f x₀ a (u a) r := by
    let s : Time := ⟨r,hr⟩
    have hd := he.realized_eq s
    rw [hd]
    change x₀+u (scaleParameter s a) finalTime=x₀+u a s
    rw [hs s]
    congr 1
    change u a (scaleTime s finalTime)=u a s
    congr 1
    apply Subtype.ext
    simp [scaleTime]
  have hr := (realizedPath_hasDerivAt (a := a) hc 1).hasDerivWithinAt (s := Icc 0 1)
  have hr' := hr.congr heq (heq 1 (by constructor <;> norm_num))
  have hud : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 1 :=
    uniqueDiffOn_Icc (show (0 : ℝ)<1 by norm_num) 1 (by constructor <;> norm_num)
  have hh := hd.hasDerivWithinAt.derivWithin hud
  have hh' := hr'.derivWithin hud
  have hend : extendPath (u a) (1 : ℝ)=u a finalTime := extendPath_val (u a) finalTime
  exact hh.symm.trans (by simpa only [hend,endpoint] using hh')

lemma rescale_endpoint_time_derivative {f : E → E} {x₀ : E}
    {u : ℂ × E → C(Time,E)} {a : ℂ × E}
    (hA : AnalyticAt ℂ (endpoint x₀ u) a)
    (he : PathEquation f x₀ a (u a))
    (hc : Continuous (fun r : ℝ => f (x₀+extendPath (u a) r)))
    (hs : ∀c : Time, u (scaleParameter c a)=rescale c (u a)) (ha : a.1≠0) :
    fderiv ℂ (endpoint x₀ u) a (1,0)=f (endpoint x₀ u a) := by
  apply smul_right_injective E ha
  have hh := rescale_endpoint_derivative hA he hc hs
  have hv : ((a.1,0) : ℂ × E)=a.1 • (1,0) := by simp
  rwa [hv,map_smul] at hh

 
omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma eq_of_nonzero_time {F G : ℂ × E → E} {a : ℂ × E}
    (hF : ContinuousAt F a) (hG : ContinuousAt G a)
    (he : ∀ᶠ b in 𝓝 a, b.1≠0 → F b=G b) : F a=G a := by
  have hc : Tendsto (fun z : ℂ => (z,a.2)) (𝓝 a.1) (𝓝 a) := by
    have hh : ContinuousAt (fun z : ℂ => (z,a.2)) a.1 :=
      (continuous_id.prodMk continuous_const).continuousAt
    simpa only [Prod.mk.eta] using hh.tendsto
  apply tendsto_nhds_unique_of_frequently_eq (hF.tendsto.comp hc) (hG.tendsto.comp hc)
  have hfreq : ∃ᶠ z : ℂ in 𝓝 a.1, z≠0 :=
    mem_closure_iff_frequently.mp ((dense_compl_singleton (0 : ℂ)) a.1)
  exact (hfreq.and_eventually (hc.eventually he)).mono fun z hz => hz.2 hz.1

 

theorem exists_analytic_flow {f : E → E} {x₀ : E} (hf : AnalyticAt ℂ f x₀) :
    ∃ F : ℂ × E → E, AnalyticAt ℂ F 0 ∧ F 0=x₀ ∧
      (∀ᶠ x in 𝓝 (0 : E), F (0,x)=x₀+x) ∧
      (∀ᶠ a in 𝓝 0, HasDerivAt (fun t : ℂ => F (t,a.2)) (f (F a)) a.1) := by
  obtain ⟨u,hu,hu0,he,huniq⟩ := exists_analytic_paths hf
  let F := endpoint x₀ u
  have hF : AnalyticAt ℂ F 0 := endpoint_analytic hu
  have hF0 : F 0=x₀ := by simp [F,endpoint,hu0]
  have ht : Tendsto u (𝓝 0) (𝓝 0) := by simpa only [hu0] using hu.continuousAt.tendsto
  have hs := eventually_rescale hu.continuousAt hu0 he huniq
  have hnonzero : ∀ᶠ a in 𝓝 0, a.1≠0 → fderiv ℂ F a (1,0)=f (F a) := by
    filter_upwards [hF.eventually_analyticAt,he,hs,
      ht.eventually (eventually_continuous_integrand hf)] with a ha hea hsa hca
    exact rescale_endpoint_time_derivative ha hea hca hsa
  have hfF : AnalyticAt ℂ (fun a => f (F a)) 0 :=
    (hF0.symm ▸ hf).comp hF
  have hEval : AnalyticAt ℂ (fun L : (ℂ × E) →L[ℂ] E => L (1,0)) (fderiv ℂ F 0) :=
    (ContinuousLinearMap.apply ℂ E ((1,0) : ℂ × E)).analyticAt _
  have hD : AnalyticAt ℂ (fun a => fderiv ℂ F a (1,0)) 0 := hEval.comp hF.fderiv
  have hderiv : ∀ᶠ a in 𝓝 0, fderiv ℂ F a (1,0)=f (F a) := by
    filter_upwards [hD.eventually_analyticAt,hfF.eventually_analyticAt,
      hnonzero.eventually_nhds] with a ha hb heq
    exact eq_of_nonzero_time ha.continuousAt hb.continuousAt heq
  refine ⟨F,hF,hF0,?_,?_⟩
  · have hz : Tendsto (fun x : E => ((0 : ℂ),x)) (𝓝 0) (𝓝 0) :=
      continuous_const.continuousAt.prodMk continuous_id.continuousAt
    filter_upwards [hz.eventually he] with x hx
    have hp := hx.at_zero_time
    simp [F,endpoint,hp,constantPath_apply]
  · filter_upwards [hF.eventually_analyticAt,hderiv] with a ha hd
    have hc : HasDerivAt (fun t : ℂ => (t,a.2)) (1,0) a.1 :=
      (hasDerivAt_id a.1).prodMk (hasDerivAt_const a.1 a.2)
    simpa only [Function.comp_def,Prod.mk.eta,hd] using
      ha.differentiableAt.hasFDerivAt.comp_hasDerivAt a.1 hc

end HolomorphicFlow

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def initialDerivative (v : E) : (ℂ × E) →L[ℂ] E :=
  (ContinuousLinearMap.fst ℂ ℂ E).smulRight v + ContinuousLinearMap.snd ℂ ℂ E

omit [CompleteSpace E] in
@[simp] lemma initialDerivative_apply (v : E) (a : ℂ × E) :
    initialDerivative v a=a.1 • v+a.2 := rfl

 

omit [CompleteSpace E] in
lemma flow_initial_derivative {F : ℂ × E → E} {x₀ v : E}
    (hF : AnalyticAt ℂ F 0)
    (hi : ∀ᶠ x in 𝓝 (0 : E), F (0,x)=x₀+x)
    (ht : HasDerivAt (fun t : ℂ => F (t,0)) v 0) :
    HasFDerivAt F (initialDerivative v) 0 := by
  let D := fderiv ℂ F 0
  have hd := hF.differentiableAt.hasFDerivAt
  have htd : HasDerivAt (fun t : ℂ => F (t,0)) (D (1,0)) 0 :=
    hd.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const 0 (0 : E)))
  have hDv : D (1,0)=v := htd.deriv.symm.trans ht.deriv
  have hid : HasFDerivAt (fun x : E => F (0,x)) (ContinuousLinearMap.id ℂ E) 0 :=
    ((hasFDerivAt_id (0 : E)).const_add x₀).congr_of_eventuallyEq hi
  have hdi : HasFDerivAt (fun x : E => F (0,x))
      (D.comp (ContinuousLinearMap.inr ℂ ℂ E)) 0 :=
    hd.comp 0 (ContinuousLinearMap.inr ℂ ℂ E).hasFDerivAt
  have hDix (x : E) : D (0,x)=x :=
    congrArg (fun L : E →L[ℂ] E => L x) (hdi.unique hid)
  have hdeq : D=initialDerivative v := by
    apply ContinuousLinearMap.ext
    intro a
    have hp : a=a.1 • ((1,0) : ℂ × E)+(0,a.2) := by simp
    rw [hp,map_add,map_smul,hDv,hDix]
    simp
  exact hdeq ▸ hd

 
def transverseParameters : (ℂ × E) →L[ℂ] (ℂ × (ℂ × E)) :=
  (ContinuousLinearMap.fst ℂ ℂ E).prod
    ((0 : (ℂ × E) →L[ℂ] ℂ).prod (ContinuousLinearMap.snd ℂ ℂ E))

omit [CompleteSpace E] in
@[simp] lemma transverseParameters_apply (a : ℂ × E) :
    transverseParameters a=(a.1,(0,a.2)) := rfl

 

theorem exists_normalized_flow_box {f : ℂ × E → ℂ × E}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=(1,0)) :
    ∃ Φ : OpenPartialHomeomorph (ℂ × E) (ℂ × E),
      (0 : ℂ × E)∈Φ.source ∧ Φ 0=0 ∧ AnalyticAt ℂ Φ 0 ∧ AnalyticAt ℂ Φ.symm 0 ∧
      (∀ᶠ a in 𝓝 0, fderiv ℂ Φ a (1,0)=f (Φ a)) := by
  obtain ⟨F,hF,hF0,hi,ht⟩ := exists_analytic_flow hf
  have ht0 : HasDerivAt (fun t : ℂ => F (t,0)) (1,0) 0 := by
    have hh := ht.self_of_nhds
    change HasDerivAt (fun t : ℂ => F (t,0)) (f (F 0)) 0 at hh
    simpa only [hF0,hf0] using hh
  have hDF := flow_initial_derivative hF hi ht0
  let L := transverseParameters (E := E)
  let ψ : ℂ × E → ℂ × E := F ∘ L
  have hFL : AnalyticAt ℂ F (L 0) := by simpa only [map_zero] using hF
  have hψ : AnalyticAt ℂ ψ 0 := hFL.comp (L.analyticAt 0)
  have hψ0 : ψ 0=0 := by simpa [ψ] using hF0
  have hd : HasFDerivAt ψ (ContinuousLinearEquiv.refl ℂ (ℂ × E) :
        (ℂ × E) →L[ℂ] (ℂ × E)) 0 := by
    have hDFL : HasFDerivAt F (initialDerivative ((1,0) : ℂ × E)) (L 0) := by
      simpa only [map_zero] using hDF
    have hh := hDFL.comp (0 : ℂ × E) L.hasFDerivAt
    have heq : (initialDerivative ((1,0) : ℂ × E)).comp L=
        (ContinuousLinearEquiv.refl ℂ (ℂ × E) : (ℂ × E) →L[ℂ] (ℂ × E)) := by
      ext a <;> simp [L,initialDerivative_apply]
    exact heq ▸ hh
  let hc : ContDiffAt ℂ ω ψ 0 := hψ.contDiffAt
  let Φ := hc.toOpenPartialHomeomorph ψ hd (by simp)
  have hΦ : (Φ : (ℂ × E) → ℂ × E)=ψ := rfl
  have hΦa : AnalyticAt ℂ Φ.symm 0 := by
    have hh := (hc.to_localInverse hd (by simp)).analyticAt
    rwa [hψ0] at hh
  refine ⟨Φ,hc.mem_toOpenPartialHomeomorph_source hd (by simp),hψ0,hψ,hΦa,?_⟩
  have hl : Tendsto L (𝓝 0) (𝓝 0) := by
    have hh : Tendsto L (𝓝 0) (𝓝 (L 0)) := L.continuous.continuousAt
    simpa only [L.map_zero] using hh
  filter_upwards [hl.eventually ht,hψ.eventually_analyticAt] with a hta ha
  have hta' : HasDerivAt (fun t : ℂ => Φ (t,a.2)) (f (Φ a)) a.1 := hta
  have htda : HasDerivAt (fun t : ℂ => Φ (t,a.2)) (fderiv ℂ Φ a (1,0)) a.1 :=
    ha.differentiableAt.hasFDerivAt.comp_hasDerivAt a.1
      ((hasDerivAt_id a.1).prodMk (hasDerivAt_const a.1 a.2))
  exact htda.deriv.symm.trans hta'.deriv

end HolomorphicFlow

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma norm_real_smul_le {r : ℝ} (hr : r∈Icc (0:ℝ) 1) (z : ℂ) : ‖r • z‖≤‖z‖ := by
  rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg hr.1]
  exact mul_le_of_le_one_left (norm_nonneg z) hr.2

 

theorem ode_unique_germ {f : E → E} {g h : ℂ → E}
    (hf : ContDiffAt ℂ 1 f (g 0)) (hg : ContinuousAt g 0) (hh : ContinuousAt h 0)
    (hi : g 0=h 0)
    (hgd : ∀ᶠ t in 𝓝 (0:ℂ), HasDerivAt g (f (g t)) t)
    (hhd : ∀ᶠ t in 𝓝 (0:ℂ), HasDerivAt h (f (h t)) t) :
    g =ᶠ[𝓝 (0:ℂ)] h := by
  obtain ⟨K,U,hU,hLip⟩ := hf.exists_lipschitzOnWith
  have hgm : ∀ᶠ t in 𝓝 (0:ℂ), g t∈U := hg.preimage_mem_nhds hU
  have hhm : ∀ᶠ t in 𝓝 (0:ℂ), h t∈U := hh.preimage_mem_nhds (hi ▸ hU)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hgd.and (hhd.and (hgm.and hhm)))
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hε] with z hz
  have hz' : ‖z‖<ε := by simpa using hz
  have hm (r : ℝ) (hr : r∈Icc (0:ℝ) 1) : r • z∈Metric.ball (0:ℂ) ε := by
    simpa using (norm_real_smul_le hr z).trans_lt hz'
  have hp (r : ℝ) (hr : r∈Icc (0:ℝ) 1) := hball (hm r hr)
  let v : ℝ → E → E := fun _ x => z • f x
  have gd (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s : ℝ => g (s • z)) (v r (g (r • z))) r := by
    have ht : HasDerivAt (fun s : ℝ => s • z) z r :=
      by simpa only [id_eq,one_smul] using (hasDerivAt_id r).smul_const z
    have hd := ((hp r hr).1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r ht
    simpa [v,ContinuousLinearMap.smulRight_apply,Function.comp_def] using hd
  have hd (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s : ℝ => h (s • z)) (v r (h (r • z))) r := by
    have ht : HasDerivAt (fun s : ℝ => s • z) z r :=
      by simpa only [id_eq,one_smul] using (hasDerivAt_id r).smul_const z
    have hd := ((hp r hr).2.1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r ht
    simpa [v,ContinuousLinearMap.smulRight_apply,Function.comp_def] using hd
  have he := ODE_solution_unique_of_mem_Icc_right
    (v := v) (s := fun _ => U) (K := ‖z‖₊*K)
    (fun _ _ => (lipschitzWith_smul z).comp_lipschitzOnWith hLip)
    (fun r hr => (gd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (gd r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (fun r hr => (hp r ⟨hr.1,hr.2.le⟩).2.2.1)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (fun r hr => (hp r ⟨hr.1,hr.2.le⟩).2.2.2)
    (by simpa using hi)
  simpa using he (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)

 

theorem ode_unique_parameter_germ {P : Type*} [NormedAddCommGroup P]
    {f : E → E} {g h : ℂ × P → E}
    (hf : ContDiffAt ℂ 1 f (g 0)) (hg : ContinuousAt g 0) (hh : ContinuousAt h 0)
    (hi : ∀ᶠ x in 𝓝 (0:P), g (0,x)=h (0,x))
    (hgd : ∀ᶠ a in 𝓝 (0:ℂ×P), HasDerivAt (fun t => g (t,a.2)) (f (g a)) a.1)
    (hhd : ∀ᶠ a in 𝓝 (0:ℂ×P), HasDerivAt (fun t => h (t,a.2)) (f (h a)) a.1) :
    g =ᶠ[𝓝 (0:ℂ×P)] h := by
  obtain ⟨K,U,hU,hLip⟩ := hf.exists_lipschitzOnWith
  have hi0 : g 0=h 0 := hi.self_of_nhds
  have hgm : ∀ᶠ a in 𝓝 (0:ℂ×P), g a∈U := hg.preimage_mem_nhds hU
  have hhm : ∀ᶠ a in 𝓝 (0:ℂ×P), h a∈U := hh.preimage_mem_nhds (hi0 ▸ hU)
  have hia : ∀ᶠ a in 𝓝 (0:ℂ×P), g (0,a.2)=h (0,a.2) := by
    have hs : Tendsto (Prod.snd : ℂ×P → P) (𝓝 0) (𝓝 0) := continuous_snd.continuousAt
    exact hs.eventually hi
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp
    (hgd.and (hhd.and (hgm.and (hhm.and hia))))
  filter_upwards [Metric.ball_mem_nhds (0:ℂ×P) hε] with a ha
  have ha' : ‖a‖<ε := by simpa using ha
  have hm (r : ℝ) (hr : r∈Icc (0:ℝ) 1) : (r • a.1,a.2)∈Metric.ball (0:ℂ×P) ε := by
    have hn : ‖(r • a.1,a.2)‖≤‖a‖ := by
      simp only [Prod.norm_def]
      exact max_le_max (norm_real_smul_le hr a.1) le_rfl
    simpa using hn.trans_lt ha'
  have hp (r : ℝ) (hr : r∈Icc (0:ℝ) 1) := hball (hm r hr)
  let v : ℝ → E → E := fun _ x => a.1 • f x
  have gd (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s : ℝ => g (s • a.1,a.2)) (v r (g (r • a.1,a.2))) r := by
    have ht : HasDerivAt (fun s : ℝ => s • a.1) a.1 r := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id r).smul_const a.1
    have hd := ((hp r hr).1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r ht
    simpa [v,ContinuousLinearMap.smulRight_apply,Function.comp_def] using hd
  have hd (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s : ℝ => h (s • a.1,a.2)) (v r (h (r • a.1,a.2))) r := by
    have ht : HasDerivAt (fun s : ℝ => s • a.1) a.1 r := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id r).smul_const a.1
    have hd := ((hp r hr).2.1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r ht
    simpa [v,ContinuousLinearMap.smulRight_apply,Function.comp_def] using hd
  have he := ODE_solution_unique_of_mem_Icc_right
    (v := v) (s := fun _ => U) (K := ‖a.1‖₊*K)
    (fun _ _ => (lipschitzWith_smul a.1).comp_lipschitzOnWith hLip)
    (fun r hr => (gd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (gd r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (fun r hr => (hp r ⟨hr.1,hr.2.le⟩).2.2.1)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (fun r hr => (hp r ⟨hr.1,hr.2.le⟩).2.2.2.1)
    (by simpa using (hball ha).2.2.2.2)
  simpa using he (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)

end HolomorphicFlow

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma analytic_fderiv {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    {F : D → E} {a : D} (hF : AnalyticAt ℂ F a) : AnalyticAt ℂ (fderiv ℂ F) a :=
  ((hF.contDiffAt (n := ω)).fderiv_right (m := ω) (by simp)).analyticAt

 

lemma variational_equation_at {F : ℂ × E → E} {f : E → E} {a : ℂ × E}
    (hF : AnalyticAt ℂ F a) (hf : DifferentiableAt ℂ f (F a))
    (he : (fun b => fderiv ℂ F b (1,0)) =ᶠ[𝓝 a] (fun b => f (F b))) (v : E) :
    HasDerivAt (fun t : ℂ => fderiv ℂ F (t,a.2) (0,v))
      (fderiv ℂ f (F a) (fderiv ℂ F a (0,v))) a.1 := by
  have hD := (analytic_fderiv hF).differentiableAt.hasFDerivAt
  have hE : HasFDerivAt (fun b => fderiv ℂ F b (1,0))
      ((ContinuousLinearMap.apply ℂ E ((1,0) : ℂ × E)).comp
        (fderiv ℂ (fderiv ℂ F) a)) a :=
    (ContinuousLinearMap.apply ℂ E ((1,0) : ℂ × E)).hasFDerivAt.comp a hD
  have hC := hf.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt
  have heD := (hE.congr_of_eventuallyEq he.symm).unique hC
  have hev := congrArg (fun L : (ℂ × E) →L[ℂ] E => L (0,v)) heD
  have hsym := (hF.contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega
  have hd := hD.comp_hasDerivAt a.1
    ((hasDerivAt_id a.1).prodMk (hasDerivAt_const a.1 a.2))
  have hd' := hd.clm_apply (hasDerivAt_const a.1 ((0,v) : ℂ × E))
  have hv : fderiv ℂ (fderiv ℂ F) a (1,0) (0,v)=
      fderiv ℂ f (F a) (fderiv ℂ F a (0,v)) := by
    rw [hsym (1,0) (0,v)]
    exact hev
  simpa only [Function.comp_def,map_zero,add_zero,hv,id_eq] using hd'

 
def jetField (f : E → E) (a : E × E) : E × E :=
  (f a.1,fderiv ℂ f a.1 a.2)

lemma jetField_analytic {f : E → E} {x v : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (jetField f) (x,v) := by
  have hd : ContDiffAt ℂ ω (fun a : E × E => fderiv ℂ f a.1) (x,v) :=
    ((analytic_fderiv hf).contDiffAt (n := ω)).comp (x,v) contDiffAt_fst
  exact ((hf.contDiffAt.comp (x,v) contDiffAt_fst).prodMk
    (hd.clm_apply contDiffAt_snd)).analyticAt

lemma initial_spatial_derivative {F : ℂ × E → E} {x₀ : E}
    (hF : AnalyticAt ℂ F 0) (hi : ∀ᶠ x in 𝓝 (0:E), F (0,x)=x₀+x) :
    ∀ᶠ x in 𝓝 (0:E), ∀v : E, fderiv ℂ F (0,x) (0,v)=v := by
  have ht : Tendsto (fun x : E => ((0,x) : ℂ × E)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hi' : (fun x => F (0,x)) =ᶠ[𝓝 (0:E)] (fun x => x₀+x) := hi
  filter_upwards [ht.eventually hF.eventually_analyticAt,hi'.eventuallyEq_nhds] with x hFx hix
  have hd := hFx.differentiableAt.hasFDerivAt.comp x
    (ContinuousLinearMap.inr ℂ ℂ E).hasFDerivAt
  have he : HasFDerivAt (fun x : E => F (0,x)) (ContinuousLinearMap.id ℂ E) x :=
    ((hasFDerivAt_id x).const_add x₀).congr_of_eventuallyEq hix
  intro v
  exact congrArg (fun L : E →L[ℂ] E => L v) (hd.unique he)

 

theorem flow_preserves_commuting {F : ℂ × E → E} {f g : E → E} {x₀ : E}
    (hf : AnalyticAt ℂ f x₀) (hg : AnalyticAt ℂ g x₀)
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0=x₀)
    (hi : ∀ᶠ x in 𝓝 (0:E), F (0,x)=x₀+x)
    (ht : ∀ᶠ a in 𝓝 (0:ℂ×E), HasDerivAt (fun t => F (t,a.2)) (f (F a)) a.1)
    (hcomm : ∀ᶠ x in 𝓝 x₀, VectorField.lieBracket ℂ f g x=0) :
    ∀ᶠ a in 𝓝 (0:ℂ×E), fderiv ℂ F a (0,g (x₀+a.2))=g (F a) := by
  let G : ℂ × E → E × E := fun a => (F a,fderiv ℂ F a (0,g (x₀+a.2)))
  let H : ℂ × E → E × E := fun a => (F a,g (F a))
  have hFt : Tendsto F (𝓝 0) (𝓝 x₀) := by simpa only [hF0] using hF.continuousAt.tendsto
  have eqPDE : (fun b => fderiv ℂ F b (1,0)) =ᶠ[𝓝 (0:ℂ×E)] (fun b => f (F b)) := by
    filter_upwards [hF.eventually_analyticAt,ht] with a ha hta
    have htd := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt a.1
      ((hasDerivAt_id a.1).prodMk (hasDerivAt_const a.1 a.2))
    exact htd.unique hta
  have hG : AnalyticAt ℂ G 0 := by
    have htrans : AnalyticAt ℂ (fun a : ℂ×E => x₀+a.2) 0 := analyticAt_const.add analyticAt_snd
    have hg' : AnalyticAt ℂ (fun a : ℂ×E => g (x₀+a.2)) 0 := by
      have hh : AnalyticAt ℂ g (x₀+(0:ℂ×E).2) := by simpa using hg
      exact AnalyticAt.comp (f := fun a : ℂ×E => x₀+a.2) hh htrans
    exact (hF.contDiffAt.prodMk
      ((analytic_fderiv hF).contDiffAt.clm_apply
        (contDiffAt_const.prodMk hg'.contDiffAt))).analyticAt
  have hH : AnalyticAt ℂ H 0 := by
    have hgF : AnalyticAt ℂ g (F 0) := hF0.symm ▸ hg
    exact (hF.contDiffAt.prodMk ((hgF.comp hF).contDiffAt)).analyticAt
  have hinit : ∀ᶠ x in 𝓝 (0:E), G (0,x)=H (0,x) := by
    filter_upwards [hi,initial_spatial_derivative hF hi] with x hix hdix
    simp only [G,H,hdix,hix]
  have hG0 : G 0=(x₀,g x₀) := by
    have hh := (initial_spatial_derivative hF hi).self_of_nhds
    change (F 0,fderiv ℂ F (0,0) (0,g (x₀+0)))=(x₀,g x₀)
    rw [hF0,hh,add_zero]
  have hjet : ContDiffAt ℂ 1 (jetField f) (G 0) := by
    rw [hG0]
    exact (jetField_analytic hf).contDiffAt
  have hGD : ∀ᶠ a in 𝓝 (0:ℂ×E),
      HasDerivAt (fun t => G (t,a.2)) (jetField f (G a)) a.1 := by
    filter_upwards [hF.eventually_analyticAt,hFt.eventually hf.eventually_analyticAt,
      eqPDE.eventuallyEq_nhds,ht] with a hFa hfa hEa hta
    exact hta.prodMk (variational_equation_at hFa hfa.differentiableAt hEa (g (x₀+a.2)))
  have hHD : ∀ᶠ a in 𝓝 (0:ℂ×E),
      HasDerivAt (fun t => H (t,a.2)) (jetField f (H a)) a.1 := by
    filter_upwards [hFt.eventually hg.eventually_analyticAt,hFt.eventually hcomm,ht]
      with a hga hca hta
    have he : fderiv ℂ g (F a) (f (F a))=fderiv ℂ f (F a) (g (F a)) :=
      sub_eq_zero.mp hca
    have hd := hga.differentiableAt.hasFDerivAt.comp_hasDerivAt a.1 hta
    rw [he] at hd
    exact hta.prodMk hd
  have hh := ode_unique_parameter_germ hjet hG.continuousAt hH.continuousAt hinit hGD hHD
  exact hh.mono fun a ha => congrArg Prod.snd ha

end HolomorphicFlow

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 

def graphField (A : E × F → E →L[ℂ] F) (v : E) (a : E × F) : E × F :=
  (v,A a v)

def graphSpace (A : E × F → E →L[ℂ] F) (a : E × F) : Submodule ℂ (E × F) :=
  LinearMap.range ((ContinuousLinearMap.id ℂ E).prod (A a)).toLinearMap

omit [CompleteSpace E] [CompleteSpace F] in
lemma mem_graphSpace {A : E × F → E →L[ℂ] F} {a w : E × F} :
    w∈graphSpace A a ↔ w.2=A a w.1 := by
  constructor
  · rintro ⟨v,hv⟩
    cases hv
    rfl
  · intro hw
    exact ⟨w.1,Prod.ext rfl hw.symm⟩

omit [CompleteSpace E] in
lemma graphField_analytic {A : E × F → E →L[ℂ] F} {a : E × F}
    (hA : AnalyticAt ℂ A a) (v : E) : AnalyticAt ℂ (graphField A v) a :=
  (contDiffAt_const.prodMk (hA.contDiffAt.clm_apply contDiffAt_const)).analyticAt

omit [CompleteSpace E] in
lemma graphField_fderiv_fst {A : E × F → E →L[ℂ] F} {a : E × F}
    (hA : AnalyticAt ℂ A a) (v : E) (w : E × F) :
    (fderiv ℂ (graphField A v) a w).1=0 := by
  have hd := (graphField_analytic hA v).differentiableAt.hasFDerivAt.fst
  have hc : HasFDerivAt (fun a : E×F => (graphField A v a).1) (0 : (E×F) →L[ℂ] E) a :=
    hasFDerivAt_const v a
  exact congrArg (fun L : (E×F) →L[ℂ] E => L w) (hd.unique hc)

 

omit [CompleteSpace E] in
lemma graphField_commute {A : E × F → E →L[ℂ] F} {a : E × F}
    (hA : AnalyticAt ℂ A a) (v w : E)
    (hm : VectorField.lieBracket ℂ (graphField A v) (graphField A w) a∈graphSpace A a) :
    VectorField.lieBracket ℂ (graphField A v) (graphField A w) a=0 := by
  have hz : (VectorField.lieBracket ℂ (graphField A v) (graphField A w) a).1=0 := by
    simp only [VectorField.lieBracket,Prod.fst_sub,graphField_fderiv_fst hA,sub_self]
  apply Prod.ext
  · exact hz
  · rw [(mem_graphSpace.mp hm),hz,map_zero]
    rfl

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def horizontalProjection : (E×F) →L[ℂ] (E×F) :=
  (ContinuousLinearMap.fst ℂ E F).prod 0

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma horizontalProjection_apply (a : E×F) :
    horizontalProjection a=(a.1,0) := rfl

def projectorStraightener (P : (E×F) →L[ℂ] (E×F)) : (E×F) →L[ℂ] (E×F) :=
  P * horizontalProjection + (1-P)*(1-horizontalProjection)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma projectorStraightener_horizontal :
    projectorStraightener (horizontalProjection : (E×F) →L[ℂ] (E×F))=1 := by
  apply ContinuousLinearMap.ext
  intro a
  apply Prod.ext <;> simp [projectorStraightener]

omit [CompleteSpace E] [CompleteSpace F] in
lemma projector_straightener_intertwine {P : (E×F) →L[ℂ] (E×F)} (hP : P*P=P) :
    P*projectorStraightener P=projectorStraightener P*horizontalProjection := by
  have hH : (horizontalProjection : (E×F) →L[ℂ] (E×F))*horizontalProjection=horizontalProjection := by
    ext a <;> simp
  have hPC : P*(1-P)=0 := by rw [mul_sub,mul_one,hP,sub_self]
  have hCH : (1-horizontalProjection)*horizontalProjection=
      (0 : (E×F) →L[ℂ] (E×F)) := by rw [sub_mul,one_mul,hH,sub_self]
  calc
    P*projectorStraightener P=P*horizontalProjection := by
      rw [projectorStraightener,mul_add,← mul_assoc,hP,← mul_assoc,hPC,zero_mul,add_zero]
    _=projectorStraightener P*horizontalProjection := by
      rw [projectorStraightener,add_mul,mul_assoc,hH,mul_assoc,hCH,mul_zero,add_zero]

def firstBlock (P : (E×F) →L[ℂ] (E×F)) : E →L[ℂ] E :=
  (ContinuousLinearMap.fst ℂ E F).comp (P.comp (ContinuousLinearMap.inl ℂ E F))

def secondBlock (P : (E×F) →L[ℂ] (E×F)) : E →L[ℂ] F :=
  (ContinuousLinearMap.snd ℂ E F).comp (P.comp (ContinuousLinearMap.inl ℂ E F))

def projectorGraph (P : (E×F) →L[ℂ] (E×F)) : E →L[ℂ] F :=
  (secondBlock P).comp (Ring.inverse (firstBlock P))

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma firstBlock_horizontal :
    firstBlock (horizontalProjection : (E×F) →L[ℂ] (E×F))=1 := by ext a; rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma secondBlock_horizontal :
    secondBlock (horizontalProjection : (E×F) →L[ℂ] (E×F))=0 := by ext a; rfl

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma projectorGraph_horizontal :
    projectorGraph (horizontalProjection : (E×F) →L[ℂ] (E×F))=0 := by
  simp [projectorGraph]

lemma firstBlock_analytic {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {P : G → (E×F) →L[ℂ] (E×F)} {x : G} (hP : AnalyticAt ℂ P x) :
    AnalyticAt ℂ (fun x => firstBlock (P x)) x :=
  (contDiffAt_const.clm_comp (hP.contDiffAt.clm_comp contDiffAt_const)).analyticAt

lemma secondBlock_analytic {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {P : G → (E×F) →L[ℂ] (E×F)} {x : G} (hP : AnalyticAt ℂ P x) :
    AnalyticAt ℂ (fun x => secondBlock (P x)) x :=
  (contDiffAt_const.clm_comp (hP.contDiffAt.clm_comp contDiffAt_const)).analyticAt

lemma projectorGraph_analytic {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {P : G → (E×F) →L[ℂ] (E×F)} {x : G} (hP : AnalyticAt ℂ P x)
    (hP0 : P x=horizontalProjection) :
    AnalyticAt ℂ (fun x => projectorGraph (P x)) x := by
  have hi : AnalyticAt ℂ (fun x => Ring.inverse (firstBlock (P x))) x := by
    have hi0 : AnalyticAt ℂ (Ring.inverse : (E →L[ℂ] E) → E →L[ℂ] E) (firstBlock (P x)) := by
      rw [hP0,firstBlock_horizontal]
      exact analyticAt_inverse (𝕜 := ℂ) (1 : (E →L[ℂ] E)ˣ)
    exact hi0.comp (f := fun x => firstBlock (P x)) (firstBlock_analytic hP)
  exact ((secondBlock_analytic hP).contDiffAt.clm_comp hi.contDiffAt).analyticAt

lemma projector_range_eq_graph {P : (E×F) →L[ℂ] (E×F)} (hP : P*P=P)
    (hQ : IsUnit (projectorStraightener P)) (hR : IsUnit (firstBlock P)) :
    LinearMap.range P.toLinearMap=graphSpace (fun _ : E×F => projectorGraph P) 0 := by
  have hQi := (ContinuousLinearMap.isUnit_iff_bijective.mp hQ).1
  have hQs := (ContinuousLinearMap.isUnit_iff_bijective.mp hQ).2
  have hRi := (ContinuousLinearMap.isUnit_iff_bijective.mp hR).1
  have hRinv := Ring.mul_inverse_cancel _ hR
  have hRinvl := Ring.inverse_mul_cancel _ hR
  have hQH (u : E) : projectorStraightener P (u,0)=P (u,0) := by
    simp [projectorStraightener]
  ext w
  rw [mem_graphSpace]
  constructor
  · rintro ⟨v,hv⟩
    have hPw : P w=w := by
      rw [← hv]
      exact congrArg (fun L : (E×F) →L[ℂ] (E×F) => L v) hP
    obtain ⟨z,hz⟩ := hQs w
    have hHz : horizontalProjection z=z := hQi (by
      have hh := congrArg (fun L : (E×F) →L[ℂ] (E×F) => L z)
        (projector_straightener_intertwine hP)
      simpa only [mul_apply_eq_comp,hz,hPw] using hh.symm)
    have hz2 : z.2=0 := (congrArg Prod.snd hHz).symm
    have hw : w=P (z.1,0) := by
      have hze : z=(z.1,0) := Prod.ext rfl hz2
      rw [hze,hQH] at hz
      exact hz.symm
    have hw1 : w.1=firstBlock P z.1 := congrArg Prod.fst hw
    have hw2 : w.2=secondBlock P z.1 := congrArg Prod.snd hw
    rw [hw2,projectorGraph,ContinuousLinearMap.comp_apply,hw1]
    have hh := congrArg (fun L : E →L[ℂ] E => L z.1) hRinvl
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using
      congrArg (secondBlock P) hh.symm
  · intro hw
    refine ⟨((Ring.inverse (firstBlock P)) w.1,0),?_⟩
    apply Prod.ext
    · have hh := congrArg (fun L : E →L[ℂ] E => L w.1) hRinv
      exact hh
    · exact hw.symm

 

theorem exists_projector_graph
    {P : E×F → (E×F) →L[ℂ] (E×F)} (hP : AnalyticAt ℂ P 0)
    (hP0 : P 0=horizontalProjection)
    (hid : ∀ᶠ a in 𝓝 (0:E×F), P a*P a=P a) :
    ∃ A : E×F → E →L[ℂ] F, AnalyticAt ℂ A 0 ∧ A 0=0 ∧
      ∀ᶠ a in 𝓝 (0:E×F), LinearMap.range (P a).toLinearMap=graphSpace A a := by
  refine ⟨fun a => projectorGraph (P a),projectorGraph_analytic hP hP0,?_,?_⟩
  · simp only [hP0,projectorGraph_horizontal]
  have hQ : AnalyticAt ℂ (fun a => projectorStraightener (P a)) 0 :=
    (hP.mul analyticAt_const).add ((analyticAt_const.sub hP).mul
      (analyticAt_const.sub analyticAt_const))
  have hQ0 : IsUnit (projectorStraightener (P 0)) := by simp [hP0]
  have hR0 : IsUnit (firstBlock (P 0)) := by simp [hP0]
  have hQn := hQ.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hQ0)
  have hRn := (firstBlock_analytic hP).continuousAt.preimage_mem_nhds
    (Units.isOpen.mem_nhds hR0)
  filter_upwards [hid,hQn,hRn] with a ha hqa hra
  exact projector_range_eq_graph ha hqa hra

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {n : ℕ}
abbrev FrameModel (n : ℕ) (F : Type*) := (Fin n → ℂ) × F

def horizontalBasis (i : Fin n) : FrameModel n F := (Pi.single i 1,0)

def timeCoordinate (i : Fin n) : FrameModel n F →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) F)

omit [CompleteSpace F] in
@[simp] lemma timeCoordinate_apply (i : Fin n) (a : FrameModel n F) :
    timeCoordinate i a=a.1 i := rfl

omit [CompleteSpace F] in
@[simp] lemma timeCoordinate_basis (i j : Fin n) :
    timeCoordinate (F := F) i (horizontalBasis j)=if i=j then 1 else 0 := by
  simp [horizontalBasis,Pi.single_apply]

lemma flow_comp_fderiv {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : ℂ × E → E} {ψ : D → E} (c : D →L[ℂ] ℂ) {a : D}
    (hΦ : DifferentiableAt ℂ Φ (c a,ψ a)) (hψ : DifferentiableAt ℂ ψ a) (v : D) :
    fderiv ℂ (fun x => Φ (c x,ψ x)) a v=
      fderiv ℂ Φ (c a,ψ a) (c v,fderiv ℂ ψ a v) := by
  have hd := hΦ.hasFDerivAt.comp a (c.hasFDerivAt.prodMk hψ.hasFDerivAt)
  exact congrArg (fun L : D →L[ℂ] E => L v) hd.fderiv

lemma flow_time_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Φ : ℂ × E → E} {f : E → E} {a : ℂ × E}
    (hΦ : DifferentiableAt ℂ Φ a)
    (ht : HasDerivAt (fun t => Φ (t,a.2)) (f (Φ a)) a.1) :
    fderiv ℂ Φ a (1,0)=f (Φ a) := by
  have hd := hΦ.hasFDerivAt.comp_hasDerivAt a.1
    ((hasDerivAt_id a.1).prodMk (hasDerivAt_const a.1 a.2))
  exact hd.unique ht

 

theorem exists_partial_frame_coordinates
    (V : Fin n → FrameModel n F → FrameModel n F)
    (hV : ∀i, AnalyticAt ℂ (V i) 0)
    (hcomm : ∀i j, ∀ᶠ x in 𝓝 (0:FrameModel n F), VectorField.lieBracket ℂ (V i) (V j) x=0)
    (s : Finset (Fin n)) :
    ∃ ψ : FrameModel n F → FrameModel n F,
      AnalyticAt ℂ ψ 0 ∧ ψ 0=0 ∧
      (∀ᶠ y in 𝓝 (0:F), ψ (0,y)=(0,y)) ∧
      ∀j, ∀ᶠ a in 𝓝 (0:FrameModel n F),
        fderiv ℂ ψ a (horizontalBasis j)=if j∈s then V j (ψ a) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let L : FrameModel n F →L[ℂ] FrameModel n F :=
      (0 : FrameModel n F →L[ℂ] (Fin n → ℂ)).prod (ContinuousLinearMap.snd ℂ _ _)
    refine ⟨L,L.analyticAt 0,L.map_zero,?_,?_⟩
    · exact Filter.Eventually.of_forall fun y => rfl
    · intro j
      exact Filter.Eventually.of_forall fun a => by simp [L,horizontalBasis]
  | @insert i s his ih =>
    obtain ⟨ψ,hψ,hψ0,hψi,hψd⟩ := ih
    obtain ⟨Φ,hΦ,hΦ0,hΦi,hΦt⟩ := HolomorphicFlow.exists_analytic_flow (hV i)
    let c := timeCoordinate (F := F) i
    let q : FrameModel n F → ℂ × FrameModel n F := fun a => (c a,ψ a)
    let θ : FrameModel n F → FrameModel n F := Φ ∘ q
    have hq0 : q 0=0 := by simp [q,hψ0]
    have hq : AnalyticAt ℂ q 0 := (c.contDiff.contDiffAt.prodMk hψ.contDiffAt).analyticAt
    have hθ : AnalyticAt ℂ θ 0 := hΦ.comp_of_eq hq hq0
    have hθ0 : θ 0=0 := by simp [θ,hq0,hΦ0]
    have hqt : Tendsto q (𝓝 0) (𝓝 0) := by simpa only [hq0] using hq.continuousAt.tendsto
    have hψt : Tendsto (fun y : F => ψ (0,y)) (𝓝 0) (𝓝 0) := by
      have h₁ : Tendsto (fun y : F => ((0,y) : FrameModel n F)) (𝓝 0) (𝓝 0) :=
        (continuous_const.prodMk continuous_id).continuousAt
      have h₂ : Tendsto ψ (𝓝 0) (𝓝 0) := by simpa only [hψ0] using hψ.continuousAt.tendsto
      exact h₂.comp h₁
    refine ⟨θ,hθ,hθ0,?_,?_⟩
    · filter_upwards [hψi,hψt.eventually hΦi] with y hy hiy
      simpa [θ,q,c,hy] using hiy
    · intro j
      have hp := HolomorphicFlow.flow_preserves_commuting (hV i) (hV j)
        hΦ hΦ0 hΦi hΦt (hcomm i j)
      filter_upwards [hψ.eventually_analyticAt,hqt.eventually hΦ.eventually_analyticAt,
        hψd j,hqt.eventually hp,hqt.eventually hΦt] with a hψa hΦa hda hpa hta
      change fderiv ℂ (fun a => Φ (c a,ψ a)) a (horizontalBasis j)=_
      rw [flow_comp_fderiv c hΦa.differentiableAt hψa.differentiableAt,hda]
      by_cases hij : i=j
      · subst j
        have hci : c (horizontalBasis i)=1 := by
          change timeCoordinate i (horizontalBasis (F := F) i)=1
          rw [timeCoordinate_basis,ite_eq_left rfl]
        simp only [hci,his,ite_false,Finset.mem_insert_self,ite_true]
        exact flow_time_fderiv hΦa.differentiableAt hta
      · have hcj : c (horizontalBasis j)=0 := by
          change timeCoordinate i (horizontalBasis (F := F) j)=0
          rw [timeCoordinate_basis,ite_eq_right hij]
        rw [hcj]
        by_cases hjs : j∈s
        · simp only [hjs,ite_true,Finset.mem_insert_of_mem hjs]
          simpa only [zero_add,q,θ,Function.comp_def] using hpa
        · have hji : j≠i := Ne.symm hij
          simp only [hjs,Finset.mem_insert, hji,false_or,↓reduceIte]
          exact map_zero _

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {n : ℕ}

omit [CompleteSpace F] in
lemma sum_horizontalBasis (v : Fin n → ℂ) :
    (∑i, v i • horizontalBasis (F := F) i)=((v,0) : FrameModel n F) := by
  apply Prod.ext
  · ext j
    simp [horizontalBasis,Pi.single_apply,Finset.sum_apply,Prod.fst_sum]
  · simp [horizontalBasis,Prod.snd_sum]

omit [CompleteSpace F] in
lemma eq_id_of_basis_and_transverse (D : FrameModel n F →L[ℂ] FrameModel n F)
    (hD : ∀i, D (horizontalBasis i)=horizontalBasis i)
    (hT : ∀v : F, D (0,v)=(0,v)) : D=ContinuousLinearMap.id ℂ (FrameModel n F) := by
  have hh (v : Fin n → ℂ) : D (v,0)=(v,0) := by
    rw [← sum_horizontalBasis (F := F) v,map_sum]
    simp only [map_smul,hD]
  apply ContinuousLinearMap.ext
  intro a
  have he : a=(a.1,0)+(0,a.2) := by simp
  rw [he,map_add,hh,hT]
  rfl

omit [CompleteSpace F] in
lemma frame_initial_derivative {ψ : FrameModel n F → FrameModel n F}
    (hψ : AnalyticAt ℂ ψ 0)
    (hi : ∀ᶠ y in 𝓝 (0:F), ψ (0,y)=(0,y))
    (hD : ∀i, fderiv ℂ ψ 0 (horizontalBasis i)=horizontalBasis i) :
    HasFDerivAt ψ (ContinuousLinearEquiv.refl ℂ (FrameModel n F) :
      FrameModel n F →L[ℂ] FrameModel n F) 0 := by
  have ht := hψ.differentiableAt.hasFDerivAt.comp (0:F)
    (ContinuousLinearMap.inr ℂ (Fin n → ℂ) F).hasFDerivAt
  have hid : HasFDerivAt (fun y : F => ψ (0,y))
      (ContinuousLinearMap.inr ℂ (Fin n → ℂ) F) 0 :=
    (ContinuousLinearMap.inr ℂ (Fin n → ℂ) F).hasFDerivAt.congr_of_eventuallyEq hi
  have hT (v : F) : fderiv ℂ ψ 0 (0,v)=(0,v) :=
    congrArg (fun L : F →L[ℂ] FrameModel n F => L v) (ht.unique hid)
  have he := eq_id_of_basis_and_transverse _ hD hT
  change HasFDerivAt ψ (ContinuousLinearMap.id ℂ (FrameModel n F)) 0
  rw [← he]
  exact hψ.differentiableAt.hasFDerivAt

 

theorem exists_commuting_frame_chart_strong
    (V : Fin n → FrameModel n F → FrameModel n F)
    (hV : ∀i, AnalyticAt ℂ (V i) 0)
    (hV0 : ∀i, V i 0=horizontalBasis i)
    (hcomm : ∀i j, ∀ᶠ x in 𝓝 (0:FrameModel n F), VectorField.lieBracket ℂ (V i) (V j) x=0) :
    ∃ Φ : OpenPartialHomeomorph (FrameModel n F) (FrameModel n F),
      (0 : FrameModel n F)∈Φ.source ∧ Φ 0=0 ∧
      AnalyticAt ℂ Φ 0 ∧ AnalyticAt ℂ Φ.symm 0 ∧
      fderiv ℂ Φ 0=ContinuousLinearMap.id ℂ (FrameModel n F) ∧
      ∀ᶠ a in 𝓝 (0:FrameModel n F), ∀i,
        fderiv ℂ Φ a (horizontalBasis i)=V i (Φ a) := by
  obtain ⟨ψ,hψ,hψ0,hi,hD⟩ := exists_partial_frame_coordinates V hV hcomm Finset.univ
  have hDi (i : Fin n) : fderiv ℂ ψ 0 (horizontalBasis i)=horizontalBasis i := by
    simpa only [Finset.mem_univ,ite_true,hψ0,hV0] using (hD i).self_of_nhds
  have hd := frame_initial_derivative hψ hi hDi
  let hc : ContDiffAt ℂ ω ψ 0 := hψ.contDiffAt
  let Φ := hc.toOpenPartialHomeomorph ψ hd (by simp)
  have hΦa : AnalyticAt ℂ Φ.symm 0 := by
    have hh := (hc.to_localInverse hd (by simp)).analyticAt
    rwa [hψ0] at hh
  refine ⟨Φ,hc.mem_toOpenPartialHomeomorph_source hd (by simp),hψ0,hψ,hΦa,hd.fderiv,?_⟩
  have hh := Filter.eventually_all.mpr hD
  change ∀ᶠ a in 𝓝 (0:FrameModel n F), ∀ i, fderiv ℂ ψ a (horizontalBasis i)=V i (ψ a)
  exact hh.mono fun a ha i => by simpa only [Finset.mem_univ,ite_true] using ha i

theorem exists_commuting_frame_chart
    (V : Fin n → FrameModel n F → FrameModel n F)
    (hV : ∀i, AnalyticAt ℂ (V i) 0)
    (hV0 : ∀i, V i 0=horizontalBasis i)
    (hcomm : ∀i j, ∀ᶠ x in 𝓝 (0:FrameModel n F), VectorField.lieBracket ℂ (V i) (V j) x=0) :
    ∃ Φ : OpenPartialHomeomorph (FrameModel n F) (FrameModel n F),
      (0 : FrameModel n F)∈Φ.source ∧ Φ 0=0 ∧
      AnalyticAt ℂ Φ 0 ∧ AnalyticAt ℂ Φ.symm 0 ∧
      ∀ᶠ a in 𝓝 (0:FrameModel n F), ∀i,
        fderiv ℂ Φ a (horizontalBasis i)=V i (Φ a) := by
  obtain ⟨Φ,h0,h00,hΦ,hΦs,_,hD⟩ := exists_commuting_frame_chart_strong V hV hV0 hcomm
  exact ⟨Φ,h0,h00,hΦ,hΦs,hD⟩

 

theorem exists_graph_frobenius_chart_strong
    (A : FrameModel n F → (Fin n → ℂ) →L[ℂ] F)
    (hA : AnalyticAt ℂ A 0) (hA0 : A 0=0)
    (hInv : ∀i j : Fin n, ∀ᶠ a in 𝓝 (0:FrameModel n F),
      VectorField.lieBracket ℂ (graphField A (Pi.single i 1))
        (graphField A (Pi.single j 1)) a∈graphSpace A a) :
    ∃ Φ : OpenPartialHomeomorph (FrameModel n F) (FrameModel n F),
      (0 : FrameModel n F)∈Φ.source ∧ Φ 0=0 ∧
      AnalyticAt ℂ Φ 0 ∧ AnalyticAt ℂ Φ.symm 0 ∧
      fderiv ℂ Φ 0=ContinuousLinearMap.id ℂ (FrameModel n F) ∧
      ∀ᶠ a in 𝓝 (0:FrameModel n F), ∀v : Fin n → ℂ,
        fderiv ℂ Φ a (v,0)=(v,A (Φ a) v) := by
  let V : Fin n → FrameModel n F → FrameModel n F := fun i => graphField A (Pi.single i 1)
  have hV (i : Fin n) : AnalyticAt ℂ (V i) 0 := graphField_analytic hA _
  have hV0 (i : Fin n) : V i 0=horizontalBasis i := by simp [V,graphField,hA0,horizontalBasis]
  have hc (i j : Fin n) : ∀ᶠ a in 𝓝 (0:FrameModel n F), VectorField.lieBracket ℂ (V i) (V j) a=0 := by
    filter_upwards [hA.eventually_analyticAt,hInv i j] with a ha hia
    exact graphField_commute ha _ _ hia
  obtain ⟨Φ,hΦ0,hΦ00,hΦ,hΦs,hD0,hΦd⟩ := exists_commuting_frame_chart_strong V hV hV0 hc
  refine ⟨Φ,hΦ0,hΦ00,hΦ,hΦs,hD0,?_⟩
  filter_upwards [hΦd] with a ha
  intro v
  have he := sum_horizontalBasis (F := F) v
  rw [← he,map_sum]
  simp only [map_smul,ha]
  let L : (Fin n → ℂ) →L[ℂ] FrameModel n F := (ContinuousLinearMap.id ℂ _).prod (A (Φ a))
  change ∑i, v i • L (Pi.single i 1)=L v
  simp only [← map_smul,← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply,Finset.sum_apply]

theorem exists_graph_frobenius_chart
    (A : FrameModel n F → (Fin n → ℂ) →L[ℂ] F)
    (hA : AnalyticAt ℂ A 0) (hA0 : A 0=0)
    (hInv : ∀i j : Fin n, ∀ᶠ a in 𝓝 (0:FrameModel n F),
      VectorField.lieBracket ℂ (graphField A (Pi.single i 1))
        (graphField A (Pi.single j 1)) a∈graphSpace A a) :
    ∃ Φ : OpenPartialHomeomorph (FrameModel n F) (FrameModel n F),
      (0 : FrameModel n F)∈Φ.source ∧ Φ 0=0 ∧
      AnalyticAt ℂ Φ 0 ∧ AnalyticAt ℂ Φ.symm 0 ∧
      ∀ᶠ a in 𝓝 (0:FrameModel n F), ∀v : Fin n → ℂ,
        fderiv ℂ Φ a (v,0)=(v,A (Φ a) v) := by
  obtain ⟨Φ,h0,h00,hΦ,hΦs,_,hD⟩ := exists_graph_frobenius_chart_strong A hA hA0 hInv
  exact ⟨Φ,h0,h00,hΦ,hΦs,hD⟩

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 



variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {n : ℕ}

omit [CompleteSpace F] in
lemma image_horizontal_eq_graph {A : FrameModel n F → (Fin n → ℂ) →L[ℂ] F}
    {a : FrameModel n F} {D : FrameModel n F →L[ℂ] FrameModel n F}
    (hD : ∀v : Fin n → ℂ, D (v,0)=(v,A a v)) :
    Submodule.map D.toLinearMap
      (LinearMap.ker (ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).toLinearMap)=graphSpace A a := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    have hv0 : v.2=0 := hv
    have hve : v=(v.1,0) := Prod.ext rfl hv0
    change D v ∈ graphSpace A a
    rw [hve,hD]
    exact mem_graphSpace.mpr rfl
  · intro hw
    refine ⟨(w.1,0),rfl,?_⟩
    change D (w.1,0)=w
    rw [hD]
    exact Prod.ext rfl (mem_graphSpace.mp hw).symm

 

theorem exists_normalized_projector_frobenius_strong
    {P : FrameModel n F → FrameModel n F →L[ℂ] FrameModel n F}
    (hP : AnalyticAt ℂ P 0) (hP0 : P 0=horizontalProjection)
    (hid : ∀ᶠ a in 𝓝 (0:FrameModel n F), P a*P a=P a)
    (hInv : InvolutiveAt P 0) :
    ∃ Φ : OpenPartialHomeomorph (FrameModel n F) (FrameModel n F),
      (0 : FrameModel n F)∈Φ.source ∧ Φ 0=0 ∧
      AnalyticAt ℂ Φ 0 ∧ AnalyticAt ℂ Φ.symm 0 ∧
      fderiv ℂ Φ 0=ContinuousLinearMap.id ℂ (FrameModel n F) ∧
      ∀ᶠ a in 𝓝 (0:FrameModel n F),
        Submodule.map (fderiv ℂ Φ a).toLinearMap
          (LinearMap.ker (ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).toLinearMap)=
            LinearMap.range (P (Φ a)).toLinearMap := by
  obtain ⟨A,hA,hA0,hgraph⟩ := exists_projector_graph hP hP0 hid
  have hm (v : Fin n → ℂ) : ∀ᶠ a in 𝓝 (0:FrameModel n F),
      graphField A v a∈LinearMap.range (P a).toLinearMap := by
    filter_upwards [hgraph] with a ha
    rw [ha]
    exact mem_graphSpace.mpr rfl
  have hc (i j : Fin n) : ∀ᶠ a in 𝓝 (0:FrameModel n F),
      VectorField.lieBracket ℂ (graphField A (Pi.single i 1))
        (graphField A (Pi.single j 1)) a∈graphSpace A a := by
    have hh := hInv (graphField A (Pi.single i 1)) (graphField A (Pi.single j 1))
      (graphField_analytic hA _) (graphField_analytic hA _) (hm _) (hm _)
    filter_upwards [hh,hgraph] with a ha hga
    rwa [← hga]
  obtain ⟨Φ,hΦ0,hΦ00,hΦ,hΦs,hD0,hΦd⟩ := exists_graph_frobenius_chart_strong A hA hA0 hc
  refine ⟨Φ,hΦ0,hΦ00,hΦ,hΦs,hD0,?_⟩
  have ht : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have hh : Tendsto Φ (𝓝 0) (𝓝 (Φ 0)) := hΦ.continuousAt
    rwa [hΦ00] at hh
  filter_upwards [hΦd,ht.eventually hgraph] with a ha hga
  rw [hga]
  exact image_horizontal_eq_graph ha

theorem exists_normalized_projector_frobenius
    {P : FrameModel n F → FrameModel n F →L[ℂ] FrameModel n F}
    (hP : AnalyticAt ℂ P 0) (hP0 : P 0=horizontalProjection)
    (hid : ∀ᶠ a in 𝓝 (0:FrameModel n F), P a*P a=P a)
    (hInv : InvolutiveAt P 0) :
    ∃ Φ : OpenPartialHomeomorph (FrameModel n F) (FrameModel n F),
      (0 : FrameModel n F)∈Φ.source ∧ Φ 0=0 ∧
      AnalyticAt ℂ Φ 0 ∧ AnalyticAt ℂ Φ.symm 0 ∧
      ∀ᶠ a in 𝓝 (0:FrameModel n F),
        Submodule.map (fderiv ℂ Φ a).toLinearMap
          (LinearMap.ker (ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).toLinearMap)=
            LinearMap.range (P (Φ a)).toLinearMap := by
  obtain ⟨Φ,h0,h00,hΦ,hΦs,_,hD⟩ := exists_normalized_projector_frobenius_strong hP hP0 hid hInv
  exact ⟨Φ,h0,h00,hΦ,hΦs,hD⟩

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

def affineCoordinates (L : E ≃L[ℂ] F) (a : E) (x : E) : F := L (x-a)
def affineUncoordinates (L : E ≃L[ℂ] F) (a : E) (y : F) : E := a+L.symm y

def changedProjector (L : E ≃L[ℂ] F) (a : E) (P : E → E →L[ℂ] E)
    (y : F) : F →L[ℂ] F := L.toContinuousLinearMap.comp
      ((P (affineUncoordinates L a y)).comp L.symm.toContinuousLinearMap)

def liftedField (L : E ≃L[ℂ] F) (a : E) (V : F → F) (x : E) : E :=
  L.symm (V (affineCoordinates L a x))

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma affineCoordinates_uncoordinates (L : E ≃L[ℂ] F) (a : E) (y : F) :
    affineCoordinates L a (affineUncoordinates L a y)=y := by
  simp [affineCoordinates,affineUncoordinates]

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma affineUncoordinates_coordinates (L : E ≃L[ℂ] F) (a x : E) :
    affineUncoordinates L a (affineCoordinates L a x)=x := by
  simp [affineCoordinates,affineUncoordinates]

omit [CompleteSpace E] [CompleteSpace F] in
lemma affineCoordinates_hasFDerivAt (L : E ≃L[ℂ] F) (a x : E) :
    HasFDerivAt (affineCoordinates L a) L.toContinuousLinearMap x := by
  change HasFDerivAt (fun x => L (x-a)) L.toContinuousLinearMap x
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
    L.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)

omit [CompleteSpace E] [CompleteSpace F] in
lemma affineUncoordinates_hasFDerivAt (L : E ≃L[ℂ] F) (a : E) (y : F) :
    HasFDerivAt (affineUncoordinates L a) L.symm.toContinuousLinearMap y :=
  L.symm.hasFDerivAt.const_add a

omit [CompleteSpace E] [CompleteSpace F] in
lemma affineCoordinates_analytic (L : E ≃L[ℂ] F) (a x : E) :
    AnalyticAt ℂ (affineCoordinates L a) x :=
  L.toContinuousLinearMap.analyticAt _ |>.comp (analyticAt_id.sub analyticAt_const)

omit [CompleteSpace E] [CompleteSpace F] in
lemma affineUncoordinates_analytic (L : E ≃L[ℂ] F) (a : E) (y : F) :
    AnalyticAt ℂ (affineUncoordinates L a) y :=
  analyticAt_const.add (L.symm.toContinuousLinearMap.analyticAt _)

omit [CompleteSpace E] [CompleteSpace F] in
lemma liftedField_analytic (L : E ≃L[ℂ] F) (a x : E) {V : F → F}
    (hV : AnalyticAt ℂ V (affineCoordinates L a x)) :
    AnalyticAt ℂ (liftedField L a V) x :=
  L.symm.toContinuousLinearMap.analyticAt _ |>.comp
    (hV.comp (affineCoordinates_analytic L a x))

omit [CompleteSpace E] [CompleteSpace F] in
lemma liftedField_hasFDerivAt (L : E ≃L[ℂ] F) (a x : E) {V : F → F}
    (hV : DifferentiableAt ℂ V (affineCoordinates L a x)) :
    HasFDerivAt (liftedField L a V)
      (L.symm.toContinuousLinearMap.comp
        ((fderiv ℂ V (affineCoordinates L a x)).comp L.toContinuousLinearMap)) x :=
  L.symm.hasFDerivAt.comp x (hV.hasFDerivAt.comp x (affineCoordinates_hasFDerivAt L a x))

omit [CompleteSpace E] [CompleteSpace F] in
lemma liftedField_bracket (L : E ≃L[ℂ] F) (a x : E) {V W : F → F}
    (hV : DifferentiableAt ℂ V (affineCoordinates L a x))
    (hW : DifferentiableAt ℂ W (affineCoordinates L a x)) :
    VectorField.lieBracket ℂ (liftedField L a V) (liftedField L a W) x=
      L.symm (VectorField.lieBracket ℂ V W (affineCoordinates L a x)) := by
  rw [VectorField.lieBracket, (liftedField_hasFDerivAt L a x hW).fderiv,
    (liftedField_hasFDerivAt L a x hV).fderiv]
  simp [liftedField,VectorField.lieBracket]

omit [CompleteSpace E] [CompleteSpace F] in
lemma mem_changedProjector_range_iff (L : E ≃L[ℂ] F) (a : E)
    (P : E → E →L[ℂ] E) (y v : F) :
    v∈LinearMap.range (changedProjector L a P y).toLinearMap ↔
      L.symm v∈LinearMap.range (P (affineUncoordinates L a y)).toLinearMap := by
  constructor
  · rintro ⟨w,hw⟩
    refine ⟨L.symm w,?_⟩
    have hh := congrArg L.symm hw
    simpa [changedProjector] using hh
  · rintro ⟨w,hw⟩
    refine ⟨L w,?_⟩
    change L (P (affineUncoordinates L a y) (L.symm (L w)))=v
    change P (affineUncoordinates L a y) w=L.symm v at hw
    simp only [ContinuousLinearEquiv.symm_apply_apply,hw,ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace F] in
lemma changedProjector_analytic (L : E ≃L[ℂ] F) (a : E)
    {P : E → E →L[ℂ] E} (hP : AnalyticAt ℂ P a) :
    AnalyticAt ℂ (changedProjector L a P) 0 := by
  have hP' : AnalyticAt ℂ P (affineUncoordinates L a 0) := by
    simpa [affineUncoordinates] using hP
  exact (contDiffAt_const.clm_comp ((hP'.comp
    (affineUncoordinates_analytic L a 0)).contDiffAt.clm_comp contDiffAt_const)).analyticAt

 

omit [CompleteSpace E] in
theorem InvolutiveAt.changed (L : E ≃L[ℂ] F) (a : E)
    {P : E → E →L[ℂ] E} (hI : InvolutiveAt P a) :
    InvolutiveAt (changedProjector L a P) 0 := by
  intro V W hV hW hVm hWm
  have hcoord : Tendsto (affineCoordinates L a) (𝓝 a) (𝓝 0) := by
    have hh : Tendsto (affineCoordinates L a) (𝓝 a) (𝓝 (affineCoordinates L a a)) :=
      (affineCoordinates_analytic L a a).continuousAt
    simpa only [affineCoordinates,sub_self,map_zero] using hh
  have hunc : Tendsto (affineUncoordinates L a) (𝓝 0) (𝓝 a) := by
    have hh := (affineUncoordinates_analytic L a 0).continuousAt
    simpa [ContinuousAt,affineUncoordinates] using hh
  have hVL : AnalyticAt ℂ (liftedField L a V) a :=
    liftedField_analytic L a a (by simpa [affineCoordinates] using hV)
  have hWL : AnalyticAt ℂ (liftedField L a W) a :=
    liftedField_analytic L a a (by simpa [affineCoordinates] using hW)
  have hm (U : F → F) (hUm : ∀ᶠ y in 𝓝 (0:F),
      U y∈LinearMap.range (changedProjector L a P y).toLinearMap) :
      ∀ᶠ x in 𝓝 a, liftedField L a U x∈LinearMap.range (P x).toLinearMap := by
    filter_upwards [hcoord.eventually hUm] with x hx
    have hh := (mem_changedProjector_range_iff L a P _ _).mp hx
    simpa [liftedField] using hh
  have hb := hI _ _ hVL hWL (hm V hVm) (hm W hWm)
  filter_upwards [hunc.eventually hb,hV.eventually_analyticAt,hW.eventually_analyticAt]
    with y hy hya hyb
  apply (mem_changedProjector_range_iff L a P y _).mpr
  have hh := liftedField_bracket L a (affineUncoordinates L a y)
    (V := V) (W := W) (by simpa using hya.differentiableAt)
    (by simpa using hyb.differentiableAt)
  rw [hh] at hy
  simpa only [affineCoordinates_uncoordinates] using hy

end

 

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

 

def projectorDecomposition (P : E →L[ℂ] E) (hP : ∀ v, P (P v)=P v) :
    E ≃L[ℂ] ((LinearMap.range P.toLinearMap) × (LinearMap.ker P.toLinearMap)) :=
  ({ toFun := fun v => (⟨P v,⟨v,rfl⟩⟩,⟨v-P v,by
        change P (v-P v)=0
        rw [map_sub,hP,sub_self]⟩)
     invFun := fun w => (w.1:E)+(w.2:E)
     left_inv := fun v => add_sub_cancel _ _
     right_inv := by
       intro w
       have hfix : P w.1=w.1 := by
         obtain ⟨v,hv⟩ := w.1.2
         change P v=(w.1:E) at hv
         rw [← hv,hP]
       have hz : P w.2=0 := w.2.2
       apply Prod.ext <;> apply Subtype.ext
       · simp [map_add,hfix,hz]
       · simp [map_add,hfix,hz]
     map_add' := by
       intro v w
       apply Prod.ext <;> apply Subtype.ext <;> simp [map_add]
       abel
     map_smul' := by
       intro c v
       apply Prod.ext <;> apply Subtype.ext <;> simp [map_smul,smul_sub]
   } : E ≃ₗ[ℂ] ((LinearMap.range P.toLinearMap) × (LinearMap.ker P.toLinearMap))).toContinuousLinearEquiv

@[simp] lemma projectorDecomposition_apply (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v)
    (v : E) :
    ((projectorDecomposition P hP v).1:E)=P v ∧
    ((projectorDecomposition P hP v).2:E)=v-P v := ⟨rfl,rfl⟩

@[simp] lemma projectorDecomposition_project (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v)
    (v : E) :
    projectorDecomposition P hP (P v)=((projectorDecomposition P hP v).1,0) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact hP v
  · change P v-P (P v)=0
    rw [hP,sub_self]

 

def projectorCoordinates (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v) :
    E ≃L[ℂ] ((Fin (Module.finrank ℂ (LinearMap.range P.toLinearMap)) → ℂ) ×
      (Fin (Module.finrank ℂ (LinearMap.ker P.toLinearMap)) → ℂ)) :=
  (projectorDecomposition P hP).trans
    (((Module.finBasis ℂ (LinearMap.range P.toLinearMap)).equivFun.toContinuousLinearEquiv).prodCongr
      ((Module.finBasis ℂ (LinearMap.ker P.toLinearMap)).equivFun.toContinuousLinearEquiv))

lemma projectorCoordinates_project (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v)
    (v : E) :
    projectorCoordinates P hP (P v)=((projectorCoordinates P hP v).1,0) := by
  simp [projectorCoordinates,projectorDecomposition_project]

lemma projectorCoordinates_project_symm (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v)
    (w : (Fin (Module.finrank ℂ (LinearMap.range P.toLinearMap)) → ℂ) ×
      (Fin (Module.finrank ℂ (LinearMap.ker P.toLinearMap)) → ℂ)) :
    projectorCoordinates P hP (P ((projectorCoordinates P hP).symm w))=(w.1,0) := by
  rw [projectorCoordinates_project,ContinuousLinearEquiv.apply_symm_apply]

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma localHomeomorph_fderiv_left_inverse (Φ : OpenPartialHomeomorph E F) {a : E}
    (ha : a∈Φ.source) (hΦ : DifferentiableAt ℂ Φ a)
    (hΦs : DifferentiableAt ℂ Φ.symm (Φ a)) :
    (fderiv ℂ Φ.symm (Φ a)).comp (fderiv ℂ Φ a)=ContinuousLinearMap.id ℂ E := by
  have he : (fun x => Φ.symm (Φ x))=ᶠ[𝓝 a] id := by
    filter_upwards [Φ.open_source.mem_nhds ha] with x hx
    exact Φ.left_inv hx
  have hd := hΦs.hasFDerivAt.comp a hΦ.hasFDerivAt
  exact hd.fderiv.symm.trans ((he.fderiv_eq).trans (fderiv_id))

lemma localHomeomorph_fderiv_right_inverse (Φ : OpenPartialHomeomorph E F) {a : E}
    (ha : a∈Φ.source) (hΦ : DifferentiableAt ℂ Φ a)
    (hΦs : DifferentiableAt ℂ Φ.symm (Φ a)) :
    (fderiv ℂ Φ a).comp (fderiv ℂ Φ.symm (Φ a))=ContinuousLinearMap.id ℂ F := by
  have hh := localHomeomorph_fderiv_left_inverse Φ.symm (Φ.map_source ha) hΦs
    (by simpa only [Φ.left_inv ha,OpenPartialHomeomorph.symm_symm] using hΦ)
  simpa only [Φ.left_inv ha,OpenPartialHomeomorph.symm_symm] using hh

variable [CompleteSpace F] {n : ℕ}

 

theorem exists_normalized_leaf_submersion
    {P : FrameModel n F → FrameModel n F →L[ℂ] FrameModel n F}
    (hP : AnalyticAt ℂ P 0) (hP0 : P 0=horizontalProjection)
    (hid : ∀ᶠ a in 𝓝 (0:FrameModel n F), P a*P a=P a)
    (hInv : InvolutiveAt P 0) :
    ∃ q : FrameModel n F → F, AnalyticAt ℂ q 0 ∧ q 0=0 ∧
      fderiv ℂ q 0=ContinuousLinearMap.snd ℂ (Fin n → ℂ) F ∧
      ∀ᶠ a in 𝓝 (0:FrameModel n F),
        LinearMap.ker (fderiv ℂ q a).toLinearMap=LinearMap.range (P a).toLinearMap := by
  obtain ⟨Φ,h0,h00,hΦ,hΦs,hD0,hD⟩ :=
    exists_normalized_projector_frobenius_strong hP hP0 hid hInv
  have h0t : (0:FrameModel n F)∈Φ.target := by simpa only [h00] using Φ.map_source h0
  have hi0 : Φ.symm 0=0 := by simpa only [h00] using Φ.left_inv h0
  let q : FrameModel n F → F := fun a => (Φ.symm a).2
  have hq : AnalyticAt ℂ q 0 :=
    (ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).analyticAt _ |>.comp hΦs
  have hDs0 : fderiv ℂ Φ.symm 0=ContinuousLinearMap.id ℂ (FrameModel n F) := by
    have hh := localHomeomorph_fderiv_left_inverse Φ h0 hΦ.differentiableAt
      (by simpa only [h00] using hΦs.differentiableAt)
    simpa only [h00,hD0,ContinuousLinearMap.comp_id] using hh
  refine ⟨q,hq,?_,?_,?_⟩
  · simp only [q,hi0,Prod.snd_zero]
  · have hd := (ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).hasFDerivAt.comp 0
      hΦs.differentiableAt.hasFDerivAt
    have hh : fderiv ℂ q 0=(ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).comp (fderiv ℂ Φ.symm 0) := hd.fderiv
    simpa only [hDs0,ContinuousLinearMap.comp_id] using hh
  have ht : Tendsto Φ.symm (𝓝 0) (𝓝 0) := by
    have hh : Tendsto Φ.symm (𝓝 0) (𝓝 (Φ.symm 0)) := hΦs.continuousAt
    rwa [hi0] at hh
  filter_upwards [Φ.open_target.mem_nhds h0t,hΦs.eventually_analyticAt,
    ht.eventually hΦ.eventually_analyticAt,ht.eventually hD] with b hb hbs hba hbd
  have hab : Φ (Φ.symm b)=b := Φ.right_inv hb
  have hsrc := Φ.map_target hb
  have hl := localHomeomorph_fderiv_left_inverse Φ hsrc hba.differentiableAt
    (by simpa only [hab] using hbs.differentiableAt)
  have hr := localHomeomorph_fderiv_right_inverse Φ hsrc hba.differentiableAt
    (by simpa only [hab] using hbs.differentiableAt)
  rw [hab] at hl hr hbd
  have hdq : fderiv ℂ q b=(ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).comp
      (fderiv ℂ Φ.symm b) :=
    ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) F).hasFDerivAt.comp b
      hbs.differentiableAt.hasFDerivAt).fderiv
  rw [← hbd]
  ext v
  constructor
  · intro hv
    refine ⟨fderiv ℂ Φ.symm b v,?_,?_⟩
    · change (fderiv ℂ Φ.symm b v).2=0
      change fderiv ℂ q b v=0 at hv
      rw [hdq] at hv
      exact hv
    · exact congrArg (fun L : FrameModel n F →L[ℂ] FrameModel n F => L v) hr
  · rintro ⟨w,hw,rfl⟩
    change fderiv ℂ q b (fderiv ℂ Φ (Φ.symm b) w)=0
    rw [hdq]
    change (fderiv ℂ Φ.symm b (fderiv ℂ Φ (Φ.symm b) w)).2=0
    have hh := congrArg (fun L : FrameModel n F →L[ℂ] FrameModel n F => L w) hl
    change fderiv ℂ Φ.symm b (fderiv ℂ Φ (Φ.symm b) w)=w at hh
    rw [hh]
    exact hw

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma changedProjector_idempotent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E ≃L[ℂ] F) (a : E) {P : E → E →L[ℂ] E} {y : F}
    (hP : ∀v, P (affineUncoordinates L a y) (P (affineUncoordinates L a y) v)=
      P (affineUncoordinates L a y) v) :
    changedProjector L a P y*changedProjector L a P y=changedProjector L a P y := by
  apply ContinuousLinearMap.ext
  intro v
  change L (P (affineUncoordinates L a y) (L.symm
    (L (P (affineUncoordinates L a y) (L.symm v)))))=
      L (P (affineUncoordinates L a y) (L.symm v))
  rw [ContinuousLinearEquiv.symm_apply_apply,hP]

 

theorem exists_leaf_submersion {P : E → E →L[ℂ] E} {x : E}
    (hP : AnalyticAt ℂ P x)
    (hid : ∀ᶠ a in 𝓝 x, ∀v, P a (P a v)=P a v)
    (hI : InvolutiveAt P x) :
    ∃ q : E → (Fin (Module.finrank ℂ (LinearMap.ker (P x).toLinearMap)) → ℂ),
      AnalyticAt ℂ q x ∧ q x=0 ∧ Function.Surjective (fderiv ℂ q x) ∧
      ∀ᶠ a in 𝓝 x,
        LinearMap.ker (fderiv ℂ q a).toLinearMap=LinearMap.range (P a).toLinearMap := by
  let hpx := hid.self_of_nhds
  let L := projectorCoordinates (P x) hpx
  let Q := changedProjector L x P
  have hQ : AnalyticAt ℂ Q 0 := changedProjector_analytic L x hP
  have hQ0 : Q 0=horizontalProjection := by
    apply ContinuousLinearMap.ext
    intro w
    change L (P (affineUncoordinates L x 0) (L.symm w))=(w.1,0)
    simp only [affineUncoordinates,map_zero,add_zero]
    exact projectorCoordinates_project_symm (P x) hpx w
  have hunc : Tendsto (affineUncoordinates L x) (𝓝 0) (𝓝 x) := by
    have hh : Tendsto (affineUncoordinates L x) (𝓝 0) (𝓝 (affineUncoordinates L x 0)) :=
      (affineUncoordinates_analytic L x 0).continuousAt
    simpa only [affineUncoordinates,map_zero,add_zero] using hh
  have hQid : ∀ᶠ a in 𝓝 0, Q a*Q a=Q a :=
    (hunc.eventually hid).mono fun a ha => changedProjector_idempotent L x ha
  obtain ⟨q,hq,hq0,hdq,hker⟩ := exists_normalized_leaf_submersion hQ hQ0 hQid
    (hI.changed L x)
  let q' := q ∘ affineCoordinates L x
  have hcoord0 : affineCoordinates L x x=0 := by simp [affineCoordinates]
  have hqa : AnalyticAt ℂ q (affineCoordinates L x x) := hcoord0.symm ▸ hq
  have hq' : AnalyticAt ℂ q' x := hqa.comp (affineCoordinates_analytic L x x)
  have hdq' : fderiv ℂ q' x=(ContinuousLinearMap.snd ℂ _ _).comp L.toContinuousLinearMap := by
    have hh := hqa.differentiableAt.hasFDerivAt.comp x (affineCoordinates_hasFDerivAt L x x)
    simpa only [hcoord0,hdq] using hh.fderiv
  refine ⟨q',hq',?_,?_,?_⟩
  · change q (affineCoordinates L x x)=0
    rw [hcoord0,hq0]
  · rw [hdq']
    intro v
    refine ⟨L.symm (0,v),?_⟩
    simp
  have hct : Tendsto (affineCoordinates L x) (𝓝 x) (𝓝 0) := by
    have hh : Tendsto (affineCoordinates L x) (𝓝 x) (𝓝 (affineCoordinates L x x)) :=
      (affineCoordinates_analytic L x x).continuousAt
    rwa [hcoord0] at hh
  filter_upwards [hct.eventually hq.eventually_analyticAt,hct.eventually hker] with a ha hka
  have hda := ha.differentiableAt.hasFDerivAt.comp a (affineCoordinates_hasFDerivAt L x a)
  ext v
  change fderiv ℂ q' a v=0 ↔ v∈LinearMap.range (P a).toLinearMap
  have hder : fderiv ℂ q' a=(fderiv ℂ q (affineCoordinates L x a)).comp L.toContinuousLinearMap :=
    hda.fderiv
  rw [hder]
  change L v∈LinearMap.ker (fderiv ℂ q (affineCoordinates L x a)).toLinearMap ↔ _
  rw [hka,mem_changedProjector_range_iff]
  simp only [ContinuousLinearEquiv.symm_apply_apply,affineUncoordinates_coordinates]

end

 

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma range_complementary_projector (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v) :
    LinearMap.range (ContinuousLinearMap.id ℂ E-P).toLinearMap=LinearMap.ker P.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change P (w-P w)=0
    rw [map_sub,hP,sub_self]
  · intro hv
    refine ⟨v,?_⟩
    change v-P v=v
    have hh : P v=0 := hv
    rw [hh,sub_zero]

lemma complementary_projector_idempotent (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v) (v : E) :
    (ContinuousLinearMap.id ℂ E-P) ((ContinuousLinearMap.id ℂ E-P) v)=
      (ContinuousLinearMap.id ℂ E-P) v := by
  change (v-P v)-P (v-P v)=v-P v
  rw [map_sub,hP,sub_self,sub_zero]

 

lemma complementary_quotients_bijective (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v)
    (A : E →L[ℂ] F) (B : E →L[ℂ] G)
    (hA : Function.Surjective A) (hB : Function.Surjective B)
    (hkA : LinearMap.ker A.toLinearMap=LinearMap.ker P.toLinearMap)
    (hkB : LinearMap.ker B.toLinearMap=LinearMap.range P.toLinearMap) :
    Function.Bijective (A.prod B) := by
  have hAP (v : E) : A (P v)=A v := by
    have hh : v-P v∈LinearMap.ker P.toLinearMap := by
      change P (v-P v)=0
      rw [map_sub,hP,sub_self]
    rw [← hkA] at hh
    change A (v-P v)=0 at hh
    rw [map_sub,sub_eq_zero] at hh
    exact hh.symm
  have hBP (v : E) : B (P v)=0 := by
    have hh : P v∈LinearMap.range P.toLinearMap := ⟨v,rfl⟩
    rw [← hkB] at hh
    exact hh
  constructor
  · apply (A.prod B).toLinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    have ha : A v=0 := congrArg Prod.fst hv
    have hb : B v=0 := congrArg Prod.snd hv
    have hpv : P v=0 := by
      have hh : v∈LinearMap.ker A.toLinearMap := ha
      rw [hkA] at hh
      exact hh
    have hr : v∈LinearMap.range P.toLinearMap := by rw [← hkB]; exact hb
    obtain ⟨w,hw⟩ := hr
    change P w=v at hw
    change v=0
    rw [← hw] at hpv ⊢
    rwa [hP] at hpv
  · rintro ⟨u,v⟩
    obtain ⟨a,ha⟩ := hA u
    obtain ⟨b,hb⟩ := hB v
    refine ⟨P a+(b-P b),?_⟩
    apply Prod.ext
    · change A (P a+(b-P b))=u
      rw [map_add,map_sub,hAP,hAP,sub_self,add_zero,ha]
    · change B (P a+(b-P b))=v
      rw [map_add,map_sub,hBP,hBP,sub_zero,zero_add,hb]

lemma image_range_projector_of_quotients (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v)
    (A : E →L[ℂ] F) (B : E →L[ℂ] G)
    (hA : Function.Surjective A)
    (hkA : LinearMap.ker A.toLinearMap=LinearMap.ker P.toLinearMap)
    (hkB : LinearMap.ker B.toLinearMap=LinearMap.range P.toLinearMap) :
    Submodule.map (A.prod B).toLinearMap (LinearMap.range P.toLinearMap)=
      LinearMap.ker (ContinuousLinearMap.snd ℂ F G).toLinearMap := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change B v=0
    rwa [← hkB] at hv
  · intro hw
    have hw0 : w.2=0 := hw
    obtain ⟨v,hv⟩ := hA w.1
    refine ⟨P v,⟨v,rfl⟩,?_⟩
    apply Prod.ext
    · change A (P v)=w.1
      have hh : v-P v∈LinearMap.ker P.toLinearMap := by
        change P (v-P v)=0
        rw [map_sub,hP,sub_self]
      rw [← hkA] at hh
      change A (v-P v)=0 at hh
      rw [map_sub,sub_eq_zero] at hh
      exact hh.symm.trans hv
    · change B (P v)=w.2
      rw [hw0]
      have hh : P v∈LinearMap.range P.toLinearMap := ⟨v,rfl⟩
      rwa [← hkB] at hh

lemma image_kernel_projector_of_quotients (P : E →L[ℂ] E) (hP : ∀v, P (P v)=P v)
    (A : E →L[ℂ] F) (B : E →L[ℂ] G)
    (hB : Function.Surjective B)
    (hkA : LinearMap.ker A.toLinearMap=LinearMap.ker P.toLinearMap)
    (hkB : LinearMap.ker B.toLinearMap=LinearMap.range P.toLinearMap) :
    Submodule.map (A.prod B).toLinearMap (LinearMap.ker P.toLinearMap)=
      LinearMap.ker (ContinuousLinearMap.fst ℂ F G).toLinearMap := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change A v=0
    rwa [← hkA] at hv
  · intro hw
    have hw0 : w.1=0 := hw
    obtain ⟨v,hv⟩ := hB w.2
    have hpk : v-P v∈LinearMap.ker P.toLinearMap := by
      change P (v-P v)=0
      rw [map_sub,hP,sub_self]
    refine ⟨v-P v,hpk,?_⟩
    apply Prod.ext
    · change A (v-P v)=w.1
      rw [hw0]
      rwa [← hkA] at hpk
    · change B (v-P v)=w.2
      have hh : P v∈LinearMap.range P.toLinearMap := ⟨v,rfl⟩
      rw [← hkB] at hh
      change B (P v)=0 at hh
      rw [map_sub,hh,sub_zero,hv]

end HolomorphicFrobenius

 

open Set Filter Topology
open scoped ContDiff
namespace HolomorphicFrobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

abbrev FirstQuotient (P : E → E →L[ℂ] E) (x : E) :=
  Fin (Module.finrank ℂ (LinearMap.ker (ContinuousLinearMap.id ℂ E-P x).toLinearMap)) → ℂ
abbrev SecondQuotient (P : E → E →L[ℂ] E) (x : E) :=
  Fin (Module.finrank ℂ (LinearMap.ker (P x).toLinearMap)) → ℂ

 

theorem exists_local_product_chart {P : E → E →L[ℂ] E} {x : E}
    (hP : AnalyticAt ℂ P x)
    (hid : ∀ᶠ a in 𝓝 x, ∀v, P a (P a v)=P a v)
    (hI : InvolutiveAt P x)
    (hIc : InvolutiveAt (fun a => ContinuousLinearMap.id ℂ E-P a) x) :
    ∃ Φ : OpenPartialHomeomorph E (FirstQuotient P x × SecondQuotient P x),
      x∈Φ.source ∧ Φ x=0 ∧ AnalyticAt ℂ Φ x ∧ AnalyticAt ℂ Φ.symm 0 ∧
      ∀ᶠ a in 𝓝 x,
        Submodule.map (fderiv ℂ Φ a).toLinearMap (LinearMap.range (P a).toLinearMap)=
          LinearMap.ker (ContinuousLinearMap.snd ℂ (FirstQuotient P x) (SecondQuotient P x)).toLinearMap ∧
        Submodule.map (fderiv ℂ Φ a).toLinearMap (LinearMap.ker (P a).toLinearMap)=
          LinearMap.ker (ContinuousLinearMap.fst ℂ (FirstQuotient P x) (SecondQuotient P x)).toLinearMap := by
  have hPc : AnalyticAt ℂ (fun a => ContinuousLinearMap.id ℂ E-P a) x := analyticAt_const.sub hP
  have hidc : ∀ᶠ a in 𝓝 x, ∀v, (ContinuousLinearMap.id ℂ E-P a)
      ((ContinuousLinearMap.id ℂ E-P a) v)=(ContinuousLinearMap.id ℂ E-P a) v :=
    hid.mono fun a ha => complementary_projector_idempotent (P a) ha
  obtain ⟨q₂,hq₂,hq₂0,hs₂,hk₂⟩ := exists_leaf_submersion hP hid hI
  obtain ⟨q₁,hq₁,hq₁0,hs₁,hk₁⟩ := exists_leaf_submersion hPc hidc hIc
  let ψ : E → FirstQuotient P x × SecondQuotient P x := fun a => (q₁ a,q₂ a)
  have hψ : AnalyticAt ℂ ψ x := hq₁.prod hq₂
  have hψ0 : ψ x=0 := Prod.ext hq₁0 hq₂0
  have hdψ : fderiv ℂ ψ x=(fderiv ℂ q₁ x).prod (fderiv ℂ q₂ x) :=
    (hq₁.differentiableAt.hasFDerivAt.prodMk hq₂.differentiableAt.hasFDerivAt).fderiv
  have hker₁ : LinearMap.ker (fderiv ℂ q₁ x).toLinearMap=LinearMap.ker (P x).toLinearMap :=
    hk₁.self_of_nhds.trans (range_complementary_projector _ hid.self_of_nhds)
  have hbij : Function.Bijective (fderiv ℂ ψ x) := by
    rw [hdψ]
    exact complementary_quotients_bijective (P x) hid.self_of_nhds _ _ hs₁ hs₂ hker₁ hk₂.self_of_nhds
  let L : E ≃L[ℂ] (FirstQuotient P x × SecondQuotient P x) :=
    (LinearEquiv.ofBijective (fderiv ℂ ψ x).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt ψ (L : E →L[ℂ] (FirstQuotient P x × SecondQuotient P x)) x :=
    hψ.differentiableAt.hasFDerivAt
  let hc : ContDiffAt ℂ ω ψ x := hψ.contDiffAt
  let Φ := hc.toOpenPartialHomeomorph ψ hd (by simp)
  have hΦ : (Φ : E → FirstQuotient P x × SecondQuotient P x)=ψ := rfl
  have hxΦ : x∈Φ.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hΦs : AnalyticAt ℂ Φ.symm 0 := by
    have hh := (hc.to_localInverse hd (by simp)).analyticAt
    rwa [hψ0] at hh
  refine ⟨Φ,hxΦ,hψ0,hψ,hΦs,?_⟩
  have ht : Tendsto Φ (𝓝 x) (𝓝 0) := by
    have hh : Tendsto Φ (𝓝 x) (𝓝 (Φ x)) := hψ.continuousAt
    rwa [show Φ x=0 from hψ0] at hh
  filter_upwards [Φ.open_source.mem_nhds hxΦ,hψ.eventually_analyticAt,
    ht.eventually hΦs.eventually_analyticAt,hq₁.eventually_analyticAt,
    hq₂.eventually_analyticAt,hk₁,hk₂,hid] with a ha hpa hpsa h₁ h₂ hk₁a hk₂a hida
  have hdr := localHomeomorph_fderiv_right_inverse Φ ha hpa.differentiableAt hpsa.differentiableAt
  have hsur : Function.Surjective (fderiv ℂ Φ a) := by
    intro w
    refine ⟨fderiv ℂ Φ.symm (Φ a) w,?_⟩
    exact congrArg (fun D : (FirstQuotient P x × SecondQuotient P x) →L[ℂ]
      (FirstQuotient P x × SecondQuotient P x) => D w) hdr
  have hdpa : fderiv ℂ Φ a=(fderiv ℂ q₁ a).prod (fderiv ℂ q₂ a) :=
    (h₁.differentiableAt.hasFDerivAt.prodMk h₂.differentiableAt.hasFDerivAt).fderiv
  have hs₁a : Function.Surjective (fderiv ℂ q₁ a) := by
    intro v
    obtain ⟨w,hw⟩ := hsur (v,0)
    rw [hdpa] at hw
    exact ⟨w,congrArg Prod.fst hw⟩
  have hs₂a : Function.Surjective (fderiv ℂ q₂ a) := by
    intro v
    obtain ⟨w,hw⟩ := hsur (0,v)
    rw [hdpa] at hw
    exact ⟨w,congrArg Prod.snd hw⟩
  have hka : LinearMap.ker (fderiv ℂ q₁ a).toLinearMap=LinearMap.ker (P a).toLinearMap :=
    hk₁a.trans (range_complementary_projector _ hida)
  rw [hdpa]
  exact ⟨image_range_projector_of_quotients (P a) hida _ _ hs₁a hka hk₂a,
    image_kernel_projector_of_quotients (P a) hida _ _ hs₂a hka hk₂a⟩

end HolomorphicFrobenius

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff
namespace SplitTangent
variable {X : ComplexManifold.{u}}

namespace TangentSplitting
variable (S : TangentSplitting X)

theorem coordinateProjector_involutiveAlternative (hI : Integrable X S.first)
    (x : X.Carrier) {z : Model X} (hz : z∈(chartAt (Model X) x).target) :
    HolomorphicFrobenius.InvolutiveAt (S.coordinateProjector x) z := by
  intro V W hV hW hPV hPW
  obtain ⟨O,hOsub,hO,hzO⟩ := _root_.mem_nhds_iff.mp
    (hV.eventually_analyticAt.and (hW.eventually_analyticAt.and (hPV.and hPW)))
  let c := chartAt (Model X) x
  let U := c.source∩c ⁻¹' O
  have hU : IsOpen U := c.isOpen_inter_preimage hO
  let V' := VectorField.mpullback (ModelWithCorners X) 𝓘(ℂ,Model X) c V
  let W' := VectorField.mpullback (ModelWithCorners X) 𝓘(ℂ,Model X) c W
  have hv' : HolomorphicSectionOn X V' U := by
    intro y hy
    exact (chartPullback_holomorphicAt x hy.1 (hOsub hy.2).1).contMDiffWithinAt
  have hw' : HolomorphicSectionOn X W' U := by
    intro y hy
    exact (chartPullback_holomorphicAt x hy.1 (hOsub hy.2).2.1).contMDiffWithinAt
  have hpv' : ∀y∈U, V' y∈S.first y := by
    intro y hy
    exact (S.coordinateProjector_range_iff x hy.1 _).mp (hOsub hy.2).2.2.1
  have hpw' : ∀y∈U, W' y∈S.first y := by
    intro y hy
    exact (S.coordinateProjector_range_iff x hy.1 _).mp (hOsub hy.2).2.2.2
  filter_upwards [hO.mem_nhds hzO,c.open_target.mem_nhds hz] with a ha hat
  have hay : c (c.symm a)=a := c.right_inv hat
  have hy : c.symm a∈c.source := c.map_target hat
  have hyU : c.symm a∈U := ⟨hy,by change c (c.symm a)∈O; rwa [hay]⟩
  have hb := hI U hU V' W' hv' hw' hpv' hpw' (c.symm a) hyU
  rw [VectorField.mlieBracketWithin_of_isOpen hU hyU] at hb
  have hVa : AnalyticAt ℂ V (c (c.symm a)) := hay.symm ▸ (hOsub ha).1
  have hWa : AnalyticAt ℂ W (c (c.symm a)) := hay.symm ▸ (hOsub ha).2.1
  have he := chartPullback_bracket x hy hVa hWa
  change VectorField.mlieBracket (ModelWithCorners X) V' W' (c.symm a)=_ at he
  rw [he] at hb
  have hh := (S.coordinateProjector_range_iff x hy _).mpr hb
  simpa only [show (chartAt (Model X) x) (c.symm a)=a from hay] using hh

end TangentSplitting
end SplitTangent

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

open Set Filter
open scoped Topology

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

open scoped Topology ENNReal
open Filter Function
namespace SplitTangent.LeadingJet
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma composition_leading (p : FormalMultilinearSeries ℂ F G)
    (q : FormalMultilinearSeries ℂ E F) (m : ℕ)
    (hp : ∀n, n < m → p n=0) (v : Fin m → E) :
    (p.comp q) m v=p m (fun i => q 1 (fun _ => v i)) := by
  classical
  simp only [FormalMultilinearSeries.comp,sum_apply]
  rw [Finset.sum_eq_single (Composition.ones m)]
  · rw [FormalMultilinearSeries.compAlongComposition_apply]
    apply p.congr (Composition.ones_length m)
    intro i him him'
    simp only [FormalMultilinearSeries.applyComposition_ones]
    rfl
  · intro c hc hne
    have hlt : c.length < m := lt_of_le_of_ne c.length_le
      (fun he => hne (Composition.eq_ones_iff_length.mpr he))
    rw [FormalMultilinearSeries.compAlongComposition_apply,hp _ hlt]
    rfl
  · simp

def cut (p : FormalMultilinearSeries ℂ E F) (m : ℕ) : FormalMultilinearSeries ℂ E F :=
  fun n => if n < m then 0 else p n

lemma cut_hasFPowerSeries [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries ℂ E F} {x : E} {r : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f p x r) (m : ℕ)
    (hf : ∀n, n < m → iteratedFDeriv ℂ n f x=0) :
    HasFPowerSeriesOnBall f (cut p m) x r := by
  have hz (n : ℕ) (hn : n < m) (v : E) : p n (fun _ => v)=0 := by
    have he := h.factorial_smul v n
    rw [hf n hn,zero_apply,← Nat.cast_smul_eq_nsmul ℂ] at he
    exact (smul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  refine ⟨h.r_le.trans (FormalMultilinearSeries.radius_le_of_le ?_),h.r_pos,?_⟩
  · intro n
    dsimp only [cut]
    split_ifs <;> simp
  · intro v hv
    apply (h.hasSum hv).congr
    intro t
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [cut]
    split_ifs with hn
    · simp [hz n hn v]
    · rfl

 

theorem iteratedFDeriv_comp_of_lower_zero [CompleteSpace F] [CompleteSpace G]
    {f : F → G} {g : E → F} {x : E} (hf : AnalyticAt ℂ f (g x))
    (hg : AnalyticAt ℂ g x) (m : ℕ)
    (hzero : ∀n, n < m → iteratedFDeriv ℂ n f (g x)=0) :
    iteratedFDeriv ℂ m (f ∘ g) x=
      (iteratedFDeriv ℂ m f (g x)).compContinuousLinearMap (fun _ => fderiv ℂ g x) := by
  obtain ⟨p,r,hp⟩ := hf
  obtain ⟨q,s,hq⟩ := hg
  have hp' := cut_hasFPowerSeries hp m hzero
  obtain ⟨t,ht⟩ := hp'.hasFPowerSeriesAt.comp hq.hasFPowerSeriesAt
  have hq1 (v : E) : q 1 (fun _ => v)=fderiv ℂ g x v := by
    simpa using hq.factorial_smul v 1
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ht.iteratedFDeriv_eq_sum_of_completeSpace]
  change _ = iteratedFDeriv ℂ m f (g x) (fun i => fderiv ℂ g x (v i))
  rw [hp.iteratedFDeriv_eq_sum_of_completeSpace]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [composition_leading _ _ m (fun n hn => by simp [cut,hn])]
  simp only [cut,lt_self_iff_false,ite_false,hq1]

end SplitTangent.LeadingJet

 

open Set Filter
open scoped Topology ContDiff
namespace SplitTangent.LeadingJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma iteratedFDeriv_smul_zeroAlternative {f : E → F} {u : E → ℂ} {x : E}
    (hf : AnalyticAt ℂ f x) (hu : AnalyticAt ℂ u x) (m : ℕ)
    (hu0 : u x=0) (hz : ∀n,n < m → iteratedFDeriv ℂ n f x=0) :
    iteratedFDeriv ℂ m (fun y => u y • f y) x=0 := by
  obtain ⟨s,hsub,hs,hxs⟩ := _root_.mem_nhds_iff.mp
    (hu.eventually_analyticAt.and hf.eventually_analyticAt)
  have hu' : ContDiffOn ℂ ω u s := fun y hy => (hsub hy).1.contDiffAt.contDiffWithinAt
  have hf' : ContDiffOn ℂ ω f s := fun y hy => (hsub hy).2.contDiffAt.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_smul_le hu' hf' hs.uniqueDiffOn hxs
    (n := m) (by simp only [le_top])
  have he (n : ℕ) (g : E → F) : iteratedFDerivWithin ℂ n g s x=iteratedFDeriv ℂ n g x :=
    iteratedFDerivWithin_of_isOpen n hs hxs
  have heu (n : ℕ) : iteratedFDerivWithin ℂ n u s x=iteratedFDeriv ℂ n u x :=
    iteratedFDerivWithin_of_isOpen n hs hxs
  simp only [he,heu] at hb
  have hs0 : (∑i∈Finset.range (m+1), (m.choose i : ℝ)*‖iteratedFDeriv ℂ i u x‖*
      ‖iteratedFDeriv ℂ (m-i) f x‖)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have him : i ≤ m := Finset.mem_range_succ_iff.mp hi
    by_cases hi0 : i=0
    · subst i
      rw [norm_iteratedFDeriv_zero,hu0,norm_zero,mul_zero,zero_mul]
    · rw [hz (m-i) (by omega),norm_zero,mul_zero]
  rw [hs0] at hb
  exact norm_le_zero_iff.mp hb

end SplitTangent.LeadingJet

 

open Set Filter
open scoped Topology ContDiff
namespace SplitTangent.HorizontalJet
section
variable {A B C D F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def value (f : A × B → F) (x : A × B) (m : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => A × B) F :=
  (iteratedFDeriv ℂ m (fun a => f (a,x.2)) x.1).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.fst ℂ A B)

omit [CompleteSpace A] [CompleteSpace B] [CompleteSpace F] in
lemma slice_analytic {f : A × B → F} {x : A × B} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun a => f (a,x.2)) x.1 :=
  hf.comp (analyticAt_id.prod analyticAt_const)

omit [CompleteSpace A] [CompleteSpace B] [CompleteSpace F] in
lemma value_eq_zero_iff (f : A × B → F) (x : A × B) (m : ℕ) :
    value f x m=0 ↔ iteratedFDeriv ℂ m (fun a => f (a,x.2)) x.1=0 := by
  constructor
  · intro h
    ext v
    exact congrArg (fun T => T (fun i => (v i,0))) h
  · intro h
    ext v
    simp [value,h]

omit [CompleteSpace A] [CompleteSpace B] [CompleteSpace F] in
lemma value_congr {f g : A × B → F} {x : A × B}
    (h : f =ᶠ[𝓝 x] g) (m : ℕ) : value f x m=value g x m := by
  have ht : Tendsto (fun a : A => (a,x.2)) (𝓝 x.1) (𝓝 x) :=
    continuousAt_id.prodMk continuousAt_const
  have he : (fun a => f (a,x.2)) =ᶠ[𝓝 x.1] (fun a => g (a,x.2)) := ht.eventually h
  unfold value
  rw [(he.iteratedFDeriv ℂ m).self_of_nhds]

omit [CompleteSpace A] [CompleteSpace B] in
lemma value_smul {f : A × B → F} {v : A × B → ℂ} {x : A × B}
    (hf : AnalyticAt ℂ f x) (hv : AnalyticAt ℂ v x) (m : ℕ)
    (hz : ∀n,n < m → value f x n=0) :
    value (fun y => v y • f y) x m=v x • value f x m := by
  unfold value
  rw [LeadingJet.iteratedFDeriv_smul_of_lower_zero (slice_analytic hf) (slice_analytic hv) m
    (fun n hn => (value_eq_zero_iff f x n).mp (hz n hn))]
  rfl

 

omit [CompleteSpace A] [CompleteSpace B] in
theorem value_comp {f : C × D → F} {T : A × B → C × D} {x : A × B}
    (hf : AnalyticAt ℂ f (T x)) (hT : AnalyticAt ℂ T x)
    (haxes : ∀ᶠ y in 𝓝 x,
      (∀a, (fderiv ℂ T y (a,0)).2=0) ∧ (∀b, (fderiv ℂ T y (0,b)).1=0))
    (m : ℕ) (hz : ∀n,n < m → value f (T x) n=0) :
    value (f ∘ T) x m =
      (value f (T x) m).compContinuousLinearMap (fun _ => fderiv ℂ T x) := by
  let g : A → C := fun a => (T (a,x.2)).1
  have hg : AnalyticAt ℂ g x.1 := analyticAt_fst.comp (slice_analytic hT)
  have he : (fun a => (f ∘ T) (a,x.2)) =ᶠ[𝓝 x.1]
      ((fun c => f (c,(T x).2)) ∘ g) := by
    have ht : Tendsto (fun a : A => (a,x.2)) (𝓝 x.1) (𝓝 x) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually (ProductTransition.eventually_product hT haxes)] with a ha
    change f (T (a,x.2))=f ((T (a,x.2)).1,(T x).2)
    congr 1
    
  have hcomp := LeadingJet.iteratedFDeriv_comp_of_lower_zero
    (g := g) (x := x.1) (slice_analytic hf) hg m
    (fun n hn => (value_eq_zero_iff f (T x) n).mp (hz n hn))
  have hder : fderiv ℂ g x.1=
      (ContinuousLinearMap.fst ℂ C D).comp ((fderiv ℂ T x).comp
        ((ContinuousLinearMap.id ℂ A).prod (0 : A →L[ℂ] B))) := by
    have hp : HasFDerivAt (fun a : A => (a,x.2))
        ((ContinuousLinearMap.id ℂ A).prod (0 : A →L[ℂ] B)) x.1 :=
      (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const x.2 x.1)
    exact ((hT.differentiableAt.hasFDerivAt.comp x.1 hp).fst).fderiv
  have hdblock (v : A × B) : (fderiv ℂ T x (v.1,0)).1=(fderiv ℂ T x v).1 := by
    have hx0 := haxes.self_of_nhds.2 v.2
    have heq : v=(v.1,0)+(0,v.2) := by simp
    conv_rhs => rw [heq,map_add,Prod.fst_add,hx0,add_zero]
  ext w
  dsimp only [value,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [(he.iteratedFDeriv ℂ m).self_of_nhds,hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hder,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    zero_apply]
  change (iteratedFDeriv ℂ m (fun a => f (a,(T x).2)) (T x).1)
    (fun i => (fderiv ℂ T x ((w i).1,0)).1) =
    (iteratedFDeriv ℂ m (fun a => f (a,(T x).2)) (T x).1)
      (fun i => (fderiv ℂ T x (w i)).1)
  congr 1
  funext i
  exact hdblock (w i)

 

omit [CompleteSpace A] [CompleteSpace B] in
theorem eventually_zero_of_all_zero {f : A × B → F} {x : A × B}
    (hf : AnalyticAt ℂ f x) (hz : ∀m,value f x m=0) :
    (fun a => f (a,x.2)) =ᶠ[𝓝 x.1] 0 := by
  obtain ⟨p,r,hp⟩ := slice_analytic hf
  have hp0 (n : ℕ) (v : A) : p n (fun _ => v)=0 := by
    have he := hp.factorial_smul v n
    rw [(value_eq_zero_iff f x n).mp (hz n),zero_apply,
      ←Nat.cast_smul_eq_nsmul ℂ] at he
    exact (smul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have heq : ∀y∈Metric.eball x.1 r, f (y,x.2)=0 := by
    intro y hy
    have hv : y-x.1∈Metric.eball 0 r := by
      change edist (y-x.1) 0 < r
      change edist y x.1 < r at hy
      simpa [edist_eq_enorm_sub] using hy
    have h := hp.hasSum hv
    simp only [hp0] at h
    have hh := h.unique hasSum_zero
    simpa using hh
  exact Filter.mem_of_superset (Metric.eball_mem_nhds x.1 hp.r_pos) heq

end

variable {E G H A B F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma iterated_comp_linear {f : G → H} (L : E →L[ℂ] G) {x : E}
    (hf : AnalyticAt ℂ f (L x)) (m : ℕ) :
    iteratedFDeriv ℂ m (f ∘ L) x=
      (iteratedFDeriv ℂ m f (L x)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨p,r,hp⟩ := hf
  have hq := hp.compContinuousLinearMap (u := L)
  ext w
  rw [hq.iteratedFDeriv_eq_sum_of_completeSpace]
  change _ = iteratedFDeriv ℂ m f (L x) (fun i => L (w i))
  rw [hp.iteratedFDeriv_eq_sum_of_completeSpace]
  rfl

 

omit [CompleteSpace A] [CompleteSpace B] in
lemma value_eq_total {f : A × B → F} {x : A × B} (hf : AnalyticAt ℂ f x)
    (m : ℕ) : value f x m=(iteratedFDeriv ℂ m f x).compContinuousLinearMap
      (fun _ => (ContinuousLinearMap.fst ℂ A B).prod (0 : A × B →L[ℂ] B)) := by
  let L : A →L[ℂ] A × B := (ContinuousLinearMap.id ℂ A).prod (0 : A →L[ℂ] B)
  let h : A × B → F := fun v => f (v+(0,x.2))
  have hh : AnalyticAt ℂ h (L x.1) := by
    have hx : L x.1 + (0,x.2) = x := by simp [L]
    have hf' : AnalyticAt ℂ f (L x.1+(0,x.2)) := by simpa only [hx] using hf
    have hc : AnalyticAt ℂ (fun v : A × B => v+(0,x.2)) (L x.1) :=
      analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (g := f) (f := fun v : A × B => v+(0,x.2)) hf' hc
  have he := iterated_comp_linear L hh m
  have heq : h ∘ L = (fun a => f (a,x.2)) := by
    funext a
    simp [h,L]
  rw [heq] at he
  ext w
  change iteratedFDeriv ℂ m (fun a => f (a,x.2)) x.1 (fun i => (w i).1) = _
  rw [he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℂ m (fun v : A × B => f (v+(0,x.2))) (x.1,0)
    (fun i => ((w i).1,0)) = iteratedFDeriv ℂ m f x (fun i => ((w i).1,0))
  rw [iteratedFDeriv_comp_add_right]
  simp

omit [CompleteSpace A] [CompleteSpace B] in
theorem analytic_value {f : A × B → F} {x : A × B} (hf : AnalyticAt ℂ f x)
    (m : ℕ) : AnalyticAt ℂ (fun y => value f y m) x := by
  obtain ⟨U,hUsub,hU,hUx⟩ := _root_.mem_nhds_iff.mp hf.eventually_analyticAt
  have hfU : AnalyticOnNhd ℂ f U := fun y hy => hUsub hy
  have hi := hfU.iteratedFDeriv m x hUx
  let L : (A × B) →L[ℂ] A × B := (ContinuousLinearMap.fst ℂ A B).prod (0 : A × B →L[ℂ] B)
  have ha := (ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin m => L)).analyticAt _ |>.comp hi
  apply ha.congr
  filter_upwards [hU.mem_nhds hUx] with y hy
  exact (value_eq_total (hfU y hy) m).symm

omit [CompleteSpace A] [CompleteSpace B] in
lemma value_symmetric {f : A × B → F} {x : A × B} (hf : AnalyticAt ℂ f x)
    (m : ℕ) (w : Fin m → A × B) (σ : Equiv.Perm (Fin m)) :
    value f x m (w ∘ σ)=value f x m w :=
  (slice_analytic hf).contDiffAt.iteratedFDeriv_comp_perm (fun i => (w i).1) σ

 

omit [CompleteSpace A] [CompleteSpace B] in
lemma analytic_parameter_value [CompleteSpace E]
    {f : E × (A × B) → F} {g : E → A × B} {z₀ : E}
    (hf : AnalyticAt ℂ f (z₀,g z₀)) (hg : AnalyticAt ℂ g z₀) (m : ℕ) :
    AnalyticAt ℂ (fun z => value (fun y => f (z,y)) (g z) m) z₀ := by
  let h : A × (E × B) → F := fun w => f (w.2.1,(w.1,w.2.2))
  have hh : AnalyticAt ℂ h ((g z₀).1,(z₀,(g z₀).2)) :=
    AnalyticAt.comp (g := f) (f := fun w : A × (E × B) => (w.2.1,(w.1,w.2.2)))
      hf ((analyticAt_fst.comp analyticAt_snd).prod
        (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)))
  have hp : AnalyticAt ℂ (fun z => ((g z).1,(z,(g z).2))) z₀ :=
    (analyticAt_fst.comp hg).prod (analyticAt_id.prod (analyticAt_snd.comp hg))
  have hv := AnalyticAt.comp (g := fun y => value h y m)
    (f := fun z => ((g z).1,(z,(g z).2))) (analytic_value hh m) hp
  let L : A × B →L[ℂ] A × (E × B) :=
    (ContinuousLinearMap.fst ℂ A B).prod
      ((0 : A × B →L[ℂ] E).prod (ContinuousLinearMap.snd ℂ A B))
  have he := (ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin m => L)).analyticAt _ |>.comp hv
  convert he using 1
  ext z w
  rfl

end SplitTangent.HorizontalJet

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

open Set Filter
open scoped Topology ContDiff
namespace SplitTangent.HorizontalJet
variable {E G H A B F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace A] [CompleteSpace B] in
theorem analytic_valueAlternative {f : A × B → F} {x : A × B} (hf : AnalyticAt ℂ f x)
    (m : ℕ) : AnalyticAt ℂ (fun y => value f y m) x := by
  obtain ⟨U,hUsub,hU,hUx⟩ := _root_.mem_nhds_iff.mp hf.eventually_analyticAt
  have hfU : AnalyticOnNhd ℂ f U := fun y hy => hUsub hy
  have hi := hfU.iteratedFDeriv m x hUx
  let L : (A × B) →L[ℂ] A × B := (ContinuousLinearMap.fst ℂ A B).prod (0 : A × B →L[ℂ] B)
  have ha := (ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin m => L)).analyticAt _ |>.comp hi
  apply ha.congr
  filter_upwards [hU.mem_nhds hUx] with y hy
  exact (value_eq_total (hfU y hy) m).symm

end SplitTangent.HorizontalJet

 

 

open Set Filter Topology
namespace SplitTangent.PositiveTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 

omit [CompleteSpace E] in
theorem contraction_order {m : ℕ}
    (A : ℂ → ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (hA : AnalyticAt ℂ A 0) (v : Fin m → ℂ → E)
    (hv : ∀i, AnalyticAt ℂ (v i) 0) (hv0 : ∀i, v i 0 = 0) :
    (m : ℕ∞) ≤ analyticOrderAt (fun z => A z (fun i => v i z)) 0 := by
  let w : Fin m → ℂ → E := fun i => dslope (v i) 0
  have hw : ∀i, AnalyticAt ℂ (w i) 0 := by
    intro i
    obtain ⟨p,hp⟩ := hv i
    exact ⟨_,hp.has_fpower_series_dslope_fslope⟩
  have ha : AnalyticAt ℂ (fun z => A z (fun i => v i z)) 0 :=
    (ContinuousLinearMap.id ℂ
      (ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)).analyticAt_uncurry_of_multilinear.comp
      (hA.prod (AnalyticAt.pi hv))
  have hb : AnalyticAt ℂ (fun z => A z (fun i => w i z)) 0 :=
    (ContinuousLinearMap.id ℂ
      (ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)).analyticAt_uncurry_of_multilinear.comp
      (hA.prod (AnalyticAt.pi hw))
  apply (natCast_le_analyticOrderAt ha).2
  refine ⟨fun z => A z (fun i => w i z),hb,Filter.Eventually.of_forall fun z => ?_⟩
  have he : (fun i => v i z) = fun i => z • w i z := by
    funext i
    simpa [w] using (sub_smul_dslope_of_zero (hv0 i) z).symm
  rw [he,ContinuousMultilinearMap.map_smul_univ]
  simp

open DiagonalRationality

 
theorem lineSection_zero_of_order {d m : ℕ} (s : lineSections (d : ℤ))
    (hdm : d < m) (hm : (m : ℕ∞) ≤ analyticOrderAt s.val.1 0) : s = 0 := by
  apply sectionJet_injective d
  rw [map_zero]
  ext i
  change iteratedDeriv i.val s.val.1 0 = 0
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (s.property.1.analyticAt 0)).mp hm i.val (lt_of_lt_of_le i.isLt (by omega))

 

omit [CompleteSpace E] in
theorem lineSection_zero_of_contraction {d m : ℕ} (hdm : d < m)
    (s : lineSections (d : ℤ))
    (A : ℂ → ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (hA : AnalyticAt ℂ A 0) (v : Fin m → ℂ → E)
    (hv : ∀i, AnalyticAt ℂ (v i) 0) (hv0 : ∀i, v i 0 = 0)
    (hs : s.val.1 =ᶠ[𝓝 0] fun z => A z (fun i => v i z)) : s = 0 := by
  apply lineSection_zero_of_order s hdm
  rw [analyticOrderAt_congr hs]
  exact contraction_order A hA v hv hv0

end SplitTangent.PositiveTensor

 

open Set Filter Topology
open scoped ContDiff Manifold

 

open Set Filter Topology Bundle
open scoped ContDiff Manifold

 

open Set Filter Topology Bundle
open scoped ContDiff Manifold

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 
open Set Filter Topology
open scoped Manifold ContDiff

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators
namespace MvPolynomial
open scoped _root_.MvPolynomial

lemma contMDiffAt_eval_comp {σ E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
    (p : MvPolynomial σ ℂ) {v : M → σ → ℂ} {x : M}
    (hv : ∀i,ContMDiffAt I 𝓘(ℂ,ℂ) ω (fun y => v y i) x) :
    ContMDiffAt I 𝓘(ℂ,ℂ) ω (fun y => _root_.MvPolynomial.eval (v y) p) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [_root_.MvPolynomial.eval_C] using (contMDiffAt_const (c := a))
  | add p q hp hq =>
    have he : (fun y => _root_.MvPolynomial.eval (v y) (p+q)) = ((fun y => _root_.MvPolynomial.eval (v y) p)+(fun y => _root_.MvPolynomial.eval (v y) q)) := by
      funext y
      exact _root_.MvPolynomial.eval_add
    rw [he]
    exact hp.add hq
  | mul_X p i hp =>
    have he : (fun y => _root_.MvPolynomial.eval (v y) (p*_root_.MvPolynomial.X i)) = ((fun y => _root_.MvPolynomial.eval (v y) p)*(fun y => v y i)) := by
      funext y
      simp only [_root_.MvPolynomial.eval_mul,_root_.MvPolynomial.eval_X,Pi.mul_apply]
    rw [he]
    exact hp.mul (hv i)

lemma IsHomogeneous.eval_scale {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℂ} {k : ℕ} (hp : p.IsHomogeneous k)
    (c : ℂ) (v : σ → ℂ) : _root_.MvPolynomial.eval (c • v) p=c^k*_root_.MvPolynomial.eval v p := by
  classical
  rw [_root_.MvPolynomial.eval_eq',_root_.MvPolynomial.eval_eq']
  change (∑m∈p.support,p.coeff m * ∏i,(c*v i)^(m i))=_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hn : (∑i,m i)=k := by
    rw [hp.degree_eq_sum_deg_support hm]
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hn]
  ring

end MvPolynomial

 

 

open Set Filter Topology
namespace AnalyticGermContinuation
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

def LocallyAnalyticZeroSet (Z T : Set A) : Prop := ∀a∈T,
  ∃(r : ℝ),0<r ∧ ∃f : A → ℂ,AnalyticOnNhd ℂ f (Metric.ball a r) ∧
    ∀b∈Metric.ball a r,b∈Z ↔ f b=0

lemma closure_interior_subset {Z T : Set A} (h : LocallyAnalyticZeroSet Z T) :
    closure (interior Z) ∩ T ⊆ interior Z := by
  intro a ha
  obtain ⟨r,hr,f,hf,he⟩ := h a ha.2
  obtain ⟨b,hbz,hbr⟩ := ((mem_closure_iff_frequently.mp ha.1).and_eventually
    (Metric.ball_mem_nhds a hr)).exists
  have hz : f =ᶠ[𝓝 b] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hbz,Metric.isOpen_ball.mem_nhds hbr] with c hc hcr
    exact (he c hcr).mp (interior_subset hc)
  have hi := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball a r).isPreconnected hbr hz
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (Metric.ball_mem_nhds a hr)
  intro c hc
  exact (he c hc).mpr (hi hc)

 

theorem propagate {Z U : Set A} (hU : IsPreconnected U)
    (h : LocallyAnalyticZeroSet Z U) {a b : A} (ha : a∈U) (hb : b∈U)
    (hz : Z∈𝓝 a) : Z∈𝓝 b := by
  have hai : a∈interior Z := mem_interior_iff_mem_nhds.mpr hz
  exact mem_interior_iff_mem_nhds.mp
    (hU.subset_of_closure_inter_subset isOpen_interior ⟨a,ha,hai⟩
      (closure_interior_subset h) hb)

end AnalyticGermContinuation

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

open Set Filter Topology
namespace UniformPlaqueSlices
variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [TopologicalSpace B]

lemma connected_rectangle {x : A × B} {W : Set (A × B)} (hW : W∈𝓝 x) :
    ∃ U V,IsOpen U ∧ IsPreconnected U ∧ IsOpen V ∧ x∈U ×ˢ V ∧ U ×ˢ V ⊆ W := by
  obtain ⟨U,V,hU,hx,hV,hy,hUV⟩ := mem_nhds_prod_iff'.mp hW
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  exact ⟨Metric.ball x.1 r,V,Metric.isOpen_ball,(convex_ball _ _).isPreconnected,hV,
    ⟨Metric.mem_ball_self hr,hy⟩,fun t ht => hUV ⟨hsub ht.1,ht.2⟩⟩

 

theorem exists_slices (Q : OpenPartialHomeomorph (A × B) (A × B))
    {x : A × B} (hx : x∈Q.source) (hsecond : ∀z,(Q z).2=z.2)
    {U : Set A} {V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hxUV : x∈U ×ˢ V) :
    ∃ U' V',IsOpen U' ∧ IsPreconnected U' ∧ IsOpen V' ∧
      (Q x).1∈U' ∧ x.2∈V' ∧ V'⊆V ∧ U' ×ˢ V' ⊆ Q.target ∧
      ∀a∈U',∀b∈V',Q.symm (a,b)∈U ×ˢ V ∧ (Q.symm (a,b)).2=b := by
  have hT := Q.map_source hx
  have hinv : Q.symm ⁻¹' (U ×ˢ V)∈𝓝 (Q x) :=
    (Q.symm.continuousAt hT).preimage_mem_nhds (by
      rw [Q.left_inv hx]
      exact (hU.prod hV).mem_nhds hxUV)
  obtain ⟨U',V',hU',hUc,hV',hx',hsub⟩ := connected_rectangle
    (Filter.inter_mem (Q.open_target.mem_nhds hT) hinv)
  refine ⟨U',V'∩V,hU',hUc,hV'.inter hV,hx'.1,?_,inter_subset_right,?_,?_⟩
  · exact ⟨hsecond x ▸ hx'.2,hxUV.2⟩
  · intro t ht
    exact (hsub ⟨ht.1,ht.2.1⟩).1
  · intro a ha b hb
    have ht := hsub (show (a,b)∈U' ×ˢ V' from ⟨ha,hb.1⟩)
    refine ⟨ht.2,?_⟩
    have he := congrArg Prod.snd (Q.right_inv ht.1)
    rwa [hsecond] at he

end UniformPlaqueSlices

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 
open scoped Manifold ContDiff BigOperators
namespace HolomorphicDeterminant
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}
lemma contMDiffAt_det {v : M → Matrix (Fin n) (Fin n) ℂ} {x : M}
    (h : ∀i j,ContMDiffAt I 𝓘(ℂ,ℂ) ω (fun t => v t i j) x) :
    ContMDiffAt I 𝓘(ℂ,ℂ) ω (fun t => Matrix.det (v t)) x := by
  classical
  simp only [Matrix.det_apply']
  apply ContMDiffAt.sum
  intro σ hσ
  apply contMDiffAt_const.mul
  apply ContMDiffAt.prod
  intro i hi
  exact h _ _
end HolomorphicDeterminant

 

 

open Set
open scoped BigOperators
namespace FiniteSampling

lemma exists_nonsingular_samples {A : Type*} {n : ℕ}
    (v : A → Fin n → ℂ)
    (h : ∀c : Fin n → ℂ,c≠0 → ∃a,∑i,v a i*c i≠0) :
    ∃s : Fin n → A, Matrix.det (fun i j => v (s i) j)≠0 := by
  classical
  let l : A → Module.Dual ℂ (Fin n → ℂ) := fun a => dotProductEquiv ℂ (Fin n) (v a)
  have htop : Submodule.span ℂ (Set.range l)=⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro c hc
    obtain ⟨a,ha⟩ := h c hc
    exact ⟨l a,⟨a,rfl⟩,ha⟩
  have hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range l))=n := by
    rw [htop,finrank_top,←(dotProductEquiv ℂ (Fin n)).finrank_eq]
    simp
  have H := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range l)
  rw [hdim] at H
  obtain ⟨f,hf,hspan,hlin⟩ := H
  choose s hs using hf
  refine ⟨s,?_⟩
  have hli : LinearIndependent ℂ (fun i => v (s i)) := by
    have hh := hlin.map' (dotProductEquiv ℂ (Fin n)).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (dotProductEquiv ℂ (Fin n)).symm.injective)
    convert! hh using 1
    funext i
    change v (s i)=(dotProductEquiv ℂ (Fin n)).symm (f i)
    rw [←hs i]
    exact ((dotProductEquiv ℂ (Fin n)).symm_apply_apply (v (s i))).symm
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hli)

lemma relation_iff_det_zero {A : Type*} {n : ℕ} (v : A → Fin n → ℂ) :
    (∃c : Fin n → ℂ,c≠0 ∧ ∀a,∑i,v a i*c i=0) ↔
      ∀s : Fin n → A,Matrix.det (fun i j => v (s i) j)=0 := by
  classical
  constructor
  · rintro ⟨c,hc,hz⟩ s
    by_contra hd
    have hinj := Matrix.mulVec_injective_of_det_ne_zero hd
    apply hc
    apply hinj
    ext i
    change (∑j,v (s i) j*c j)=(Matrix.mulVec (fun i j => v (s i) j) (0 : Fin n → ℂ)) i
    simp [Matrix.mulVec,dotProduct,hz]
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨s,hs⟩ := exists_nonsingular_samples v hn
    exact hs (h s)

end FiniteSampling

 

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

open Set Filter Topology
namespace SplitTangent.ProjectorSpanning
variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [TopologicalSpace B]

 

theorem eventually_range_eq {P M : B → E →L[ℂ] E} {x : B}
    (hP : ContinuousAt P x) (hM : ContinuousAt M x) (hx : M x=P x)
    (hPP : ∀ᶠy in 𝓝 x, ∀v,P y (P y v)=P y v)
    (hPM : ∀ᶠy in 𝓝 x, ∀v,P y (M y v)=M y v) :
    ∀ᶠy in 𝓝 x,LinearMap.range (M y).toLinearMap=LinearMap.range (P y).toLinearMap := by
  let L : B → E →L[ℂ] E := fun y => M y+1-P y
  have hL : ContinuousAt L x := (hM.add continuousAt_const).sub hP
  have hLx : L x=1 := by simp [L,hx]
  have hInv : ∀ᶠy in 𝓝 x,IsUnit (L y) :=
    hL.preimage_mem_nhds (Units.isOpen.mem_nhds (by rw [hLx]; exact isUnit_one))
  filter_upwards [hInv,hPP,hPM] with y hy hPP hPM
  apply le_antisymm
  · rintro v ⟨w,rfl⟩
    exact ⟨M y w,hPM w⟩
  · rintro v ⟨w,rfl⟩
    obtain ⟨a,ha⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hy).2 w
    refine ⟨a,?_⟩
    rw [←ha]
    change M y a=P y (M y a+a-P y a)
    rw [map_sub,map_add,hPM a,hPP a]
    abel

 

omit [CompleteSpace E] in
theorem multilinear_zero_of_basis_range {n m : ℕ}
    (M : (Fin n → ℂ) →L[ℂ] E)
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin m => E) ℂ)
    (hA : ∀j : Fin m → Fin n,A (fun i => M ((Pi.basisFun ℂ (Fin n)) (j i)))=0)
    (v : Fin m → E) (hv : ∀i,v i∈LinearMap.range M.toLinearMap) : A v=0 := by
  classical
  let C := A.compContinuousLinearMap (fun _ => M)
  have hz : C.toMultilinearMap=0 := by
    apply Module.Basis.ext_multilinear (fun _ : Fin m => Pi.basisFun ℂ (Fin n))
    exact hA
  choose w hw using hv
  have hc := congrArg (fun A : MultilinearMap ℂ (fun _ : Fin m => Fin n → ℂ) ℂ => A w) hz
  change A (fun i => M (w i))=0 at hc
  have he : (fun i => M (w i))=v := funext hw
  rwa [he] at hc

end SplitTangent.ProjectorSpanning

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

open Function
namespace SplitTangent.SymmetricIndex

 

abbrev Sorted (r m : ℕ) := {j : Fin m → Fin r // Monotone j}

def toSym {r m : ℕ} (j : Sorted r m) : Sym (Fin r) m :=
  ⟨(List.ofFn j.val : Multiset (Fin r)),by simp⟩

theorem toSym_injective {r m : ℕ} : Function.Injective (@toSym r m) := by
  intro j k he
  have hp : List.Perm (List.ofFn j.val) (List.ofFn k.val) :=
    Quotient.exact (congrArg Subtype.val he)
  apply Subtype.ext
  exact List.ofFn_injective (hp.eq_of_pairwise'
    j.property.sortedLE_ofFn.pairwise k.property.sortedLE_ofFn.pairwise)

theorem card_le (r m : ℕ) : Fintype.card (Sorted r m)≤(r+m-1).choose m := by
  simpa only [Sym.card_sym_eq_choose,Fintype.card_fin] using
    Fintype.card_le_of_injective (@toSym r m) toSym_injective

def sort {r m : ℕ} (j : Fin m → Fin r) : Sorted r m :=
  ⟨j ∘ Tuple.sort j,Tuple.monotone_sort j⟩

 
theorem zero_of_sorted {r m : ℕ} {V W : Type*} [Zero W]
    (A : (Fin m → V) → W) (σ : Fin r → V)
    (hA : ∀(v : Fin m → V) (p : Equiv.Perm (Fin m)),A (v ∘ p)=A v)
    (h : ∀j : Sorted r m,A (σ ∘ j.val)=0) : ∀j : Fin m → Fin r,A (σ ∘ j)=0 := by
  intro j
  rw [←hA (σ ∘ j) (Tuple.sort j)]
  exact h (sort j)

end SplitTangent.SymmetricIndex

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

namespace SeparatedQuotientFiltration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (F : ℕ → Submodule K V) (hF : Antitone F)

abbrev zeroPart : Submodule K V := ⨅m,F m
abbrev Space := V ⧸ zeroPart F
abbrev stage (m : ℕ) : Submodule K (Space F) := (F m).map (zeroPart F).mkQ

lemma zeroPart_le (m : ℕ) : zeroPart F ≤ F m := iInf_le F m
include hF in
lemma stage_antitone : Antitone (stage F) := fun _ _ h => Submodule.map_mono (hF h)

def project (m : ℕ) : F m →ₗ[K] stage F m where
  toFun v := ⟨(zeroPart F).mkQ v,⟨v,v.property,rfl⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

lemma project_surjective (m : ℕ) : Function.Surjective (project F m) := by
  intro w
  obtain ⟨v,hv,he⟩ := w.property
  exact ⟨⟨v,hv⟩,Subtype.ext he⟩

lemma project_zero_iff (m : ℕ) (v : F m) : project F m v=0 ↔ v.val∈zeroPart F := by
  change (⟨(zeroPart F).mkQ v,_⟩ : stage F m)=0 ↔ _
  rw [Subtype.ext_iff]
  exact Submodule.Quotient.mk_eq_zero _

lemma separated (w : Space F) (hw : ∀m,w∈stage F m) : w=0 := by
  obtain ⟨v,rfl⟩ := (zeroPart F).mkQ_surjective w
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine (Submodule.mem_iInf _).mpr fun m => ?_
  obtain ⟨b,hb,he⟩ := hw m
  have hvb : v-b∈zeroPart F := (Submodule.Quotient.eq _).mp he.symm
  have hdiff : v-b∈F m := zeroPart_le F m hvb
  simpa only [sub_add_cancel] using (F m).add_mem hdiff hb

variable {G : ℕ → Type*} [∀m,AddCommGroup (G m)] [∀m,Module K (G m)]
  (L : ∀m,F m →ₗ[K] G m)
  (hker : ∀m v,L m v=0 ↔ v.val∈F (m+1))

include hker in
lemma descends (m : ℕ) : LinearMap.ker (project F m) ≤ LinearMap.ker (L m) := by
  intro v hv
  exact (hker m v).mpr (zeroPart_le F (m+1) ((project_zero_iff F m v).mp hv))

def leading (m : ℕ) : stage F m →ₗ[K] G m :=
  ((LinearMap.ker (project F m)).liftQ (L m) (descends F L hker m)).comp
    ((project F m).quotKerEquivOfSurjective (project_surjective F m)).symm.toLinearMap

@[simp] lemma leading_project (m : ℕ) (v : F m) :
    leading F L hker m (project F m v)=L m v := by
  simp [leading]

lemma leading_kernel (m : ℕ) (w : stage F m) :
    leading F L hker m w=0 ↔ w.val∈stage F (m+1) := by
  obtain ⟨v,rfl⟩ := project_surjective F m w
  rw [leading_project,hker]
  constructor
  · intro hv
    exact ⟨v,hv,rfl⟩
  · rintro ⟨b,hb,he⟩
    have hd : v.val-b∈zeroPart F := (Submodule.Quotient.eq _).mp he.symm
    exact sub_add_cancel v.val b ▸ (F (m+1)).add_mem (zeroPart_le F (m+1) hd) hb

end SeparatedQuotientFiltration

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

 

open Set Filter Topology
namespace AnalyticFlatFamily
variable {E A F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace A] in
lemma germ_zero_of_derivatives {f : A → F} {a : A} (hf : AnalyticAt ℂ f a)
    (hz : ∀m,iteratedFDeriv ℂ m f a=0) : f =ᶠ[𝓝 a] 0 := by
  obtain ⟨p,r,hp⟩ := hf
  have hp0 (n : ℕ) (v : A) : p n (fun _ => v)=0 := by
    have he := hp.factorial_smul v n
    rw [hz n,zero_apply,←Nat.cast_smul_eq_nsmul ℂ] at he
    exact (smul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  apply Filter.mem_of_superset (Metric.eball_mem_nhds a hp.r_pos)
  intro y hy
  have hv : y-a∈Metric.eball 0 r := by
    change edist (y-a) 0 < r
    change edist y a < r at hy
    simpa [edist_eq_enorm_sub] using hy
  have h := hp.hasSum hv
  simp only [hp0] at h
  simpa using h.unique hasSum_zero

 

omit [CompleteSpace E] [CompleteSpace A] in
theorem joint_germ_zero {f : E × A → F} {c : E → A} {z₀ : E}
    (hf : AnalyticAt ℂ f (z₀,c z₀)) (hc : ContinuousAt c z₀)
    (hz : ∀ᶠ z in 𝓝 z₀,(fun a => f (z,a)) =ᶠ[𝓝 (c z)] 0) :
    f =ᶠ[𝓝 (z₀,c z₀)] 0 := by
  obtain ⟨r,hr,ha⟩ := hf.exists_ball_analyticOnNhd
  have hc' : ∀ᶠ z in 𝓝 z₀,c z∈Metric.ball (c z₀) r :=
    hc.eventually (Metric.ball_mem_nhds _ hr)
  have hz' : ∀ᶠ z in 𝓝 z₀,∀a∈Metric.ball (c z₀) r,f (z,a)=0 := by
    filter_upwards [hz,hc',Metric.ball_mem_nhds z₀ hr] with z hzg hcz hzz
    have hs : AnalyticOnNhd ℂ (fun a => f (z,a)) (Metric.ball (c z₀) r) := by
      intro a haz
      have hp : (z,a)∈Metric.ball (z₀,c z₀) r := by
        simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hzz haz
      exact (ha (z,a) hp).comp (analyticAt_const.prod analyticAt_id)
    exact hs.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (c z₀) r).isPreconnected hcz hzg
  have h1 : Tendsto (Prod.fst : E × A → E) (𝓝 (z₀,c z₀)) (𝓝 z₀) := continuousAt_fst
  have h2 : Tendsto (Prod.snd : E × A → A) (𝓝 (z₀,c z₀)) (𝓝 (c z₀)) := continuousAt_snd
  filter_upwards [h1.eventually hz',h2.eventually (Metric.ball_mem_nhds _ hr)] with q hq1 hq2
  exact hq1 q.2 hq2

end AnalyticFlatFamily

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped BigOperators
namespace PolynomialCoefficientGerms

lemma coefficients_zero {n : ℕ} (c : Fin n → ℂ) (z₀ : ℂ)
    (h : (fun z : ℂ => ∑i : Fin n,z^i.val*c i) =ᶠ[𝓝 z₀] 0) : ∀i,c i=0 := by
  classical
  let p : Polynomial ℂ := ∑i : Fin n,Polynomial.monomial i.val (c i)
  have hroot : {z : ℂ | p.IsRoot z}∈𝓝 z₀ := by
    filter_upwards [h] with z hz
    simpa only [p,Polynomial.IsRoot,Polynomial.eval_finsetSum,Polynomial.eval_monomial,mul_comm,Pi.zero_apply]
      using hz
  have hp : p=0 := p.eq_zero_of_infinite_isRoot (infinite_of_mem_nhds z₀ hroot)
  intro i
  have hh := congrArg (fun q : Polynomial ℂ => q.coeff i.val) hp
  simpa only [p,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Polynomial.coeff_zero,Fin.val_inj,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

 

theorem coefficient_germs {A : Type*} [TopologicalSpace A] {a₀ : A} {n : ℕ}
    (c : Fin n → A → ℂ) (z₀ : ℂ)
    (h : (fun q : ℂ × A => ∑i : Fin n,q.1^i.val*c i q.2) =ᶠ[𝓝 (z₀,a₀)] 0) :
    ∀i,c i =ᶠ[𝓝 a₀] 0 := by
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp h
  intro i
  filter_upwards [hV] with a ha
  apply coefficients_zero (fun j => c j a) z₀ (i := i)
  filter_upwards [hU] with z hz
  exact hUV (show (z,a)∈U ×ˢ V from ⟨hz,ha⟩)

end PolynomialCoefficientGerms

 

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

 

namespace LinearKernelDimension
variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]

def factor (f : V →ₗ[K] W) (g : V →ₗ[K] U) (h : f.ker ≤ g.ker) :
    f.range →ₗ[K] U :=
  (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap

@[simp] lemma factor_apply (f : V →ₗ[K] W) (g : V →ₗ[K] U) (h : f.ker ≤ g.ker) (v : V) :
    factor f g h (f.rangeRestrict v)=g v := by
  change (f.ker.liftQ g h) (f.quotKerEquivRange.symm (f.rangeRestrict v))=g v
  have he : f.quotKerEquivRange (f.ker.mkQ v)=f.rangeRestrict v := rfl
  rw [←he,LinearEquiv.symm_apply_apply]
  rfl

theorem finite_and_bound [Module.Finite K W] (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (h : f.ker ≤ g.ker) (hg : Function.Surjective g) :
    Module.Finite K U ∧ Module.finrank K U ≤ Module.finrank K W := by
  have hs : Function.Surjective (factor f g h) := by
    intro u
    obtain ⟨v,rfl⟩ := hg u
    exact ⟨f.rangeRestrict v,factor_apply f g h v⟩
  let : Module.Finite K U := Module.Finite.of_surjective (factor f g h) hs
  exact ⟨inferInstance,(LinearMap.finrank_le_finrank_of_surjective hs).trans
    (Submodule.finrank_le f.range)⟩

end LinearKernelDimension

 

 

namespace PolynomialGrowthArithmetic

lemma cancel_graph_dimension (k d r n : ℕ)
    (h : (k+1)*n ≤ (k+k*d+r).choose r*(k+k*d+1)) :
    n ≤ (d+r+1)^r*(d+1)*(k+1)^r := by
  have h₁ : k+k*d+r ≤ (d+r+1)*(k+1) := by nlinarith
  have h₂ : k+k*d+1 ≤ (d+1)*(k+1) := by nlinarith
  have hb := h.trans (Nat.mul_le_mul
    ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left h₁ r)) h₂)
  have he : ((d+r+1)*(k+1))^r*((d+1)*(k+1)) =
      (k+1)*((d+r+1)^r*(d+1)*(k+1)^r) := by rw [mul_pow]; ring
  rw [he] at hb
  exact Nat.le_of_mul_le_mul_left hb (by omega)

lemma box_exceeds (C r : ℕ) : ∃t : ℕ,
    C*((r+1)*t+1)^r < (t+1)^(r+1) := by
  let t := C*(r+1)^r+1
  refine ⟨t,?_⟩
  have ha : (r+1)*t+1 ≤ (r+1)*(t+1) := by nlinarith
  have hb : C*(r+1)^r < t+1 := by dsimp [t]; omega
  calc
    C*((r+1)*t+1)^r ≤ C*((r+1)*(t+1))^r :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha r)
    _ = (C*(r+1)^r)*(t+1)^r := by rw [mul_pow]; ring
    _ < (t+1)*(t+1)^r := Nat.mul_lt_mul_of_pos_right hb (by positivity)
    _ = (t+1)^(r+1) := by rw [pow_succ]; ring

end PolynomialGrowthArithmetic

 

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

 

open scoped BigOperators
namespace BoxMonomials
open _root_.MvPolynomial

def homogeneousAlternative {σ : Type*} {m t : ℕ} (j : σ) (v : Fin m → σ) (e : Box m t) :
    homogeneousSubmodule σ ℂ (m*t) :=
  ⟨MvPolynomial.X j^(m*t-∑i,(e i).val)*∏i,MvPolynomial.X (v i)^(e i).val,by
    apply (mem_homogeneousSubmodule _ _).mpr
    have h₁ := isHomogeneous_X_pow (R := ℂ) j (m*t-∑i,(e i).val)
    have h₂ := IsHomogeneous.prod Finset.univ (fun i => (MvPolynomial.X (v i) : MvPolynomial σ ℂ)^(e i).val)
      (fun i => (e i).val) (fun i _ => isHomogeneous_X_pow _ _)
    simpa only [Nat.sub_add_cancel (degree_le e)] using h₁.mul h₂⟩

end BoxMonomials

 

open scoped BigOperators
namespace BoxMonomials
open _root_.MvPolynomial

 

def homogeneousForms {σ : Type*} {m t : ℕ}
    (D : homogeneousSubmodule σ ℂ 1) (H : Fin m → homogeneousSubmodule σ ℂ 1)
    (e : Box m t) : homogeneousSubmodule σ ℂ (m*t) :=
  ⟨D.val^(m*t-∑i,(e i).val)*∏i,(H i).val^(e i).val,by
    apply (mem_homogeneousSubmodule _ _).mpr
    have hD : D.val.IsHomogeneous 1 := (mem_homogeneousSubmodule _ _).mp D.property
    have hH : ∀i,(H i).val.IsHomogeneous 1 :=
      fun i => (mem_homogeneousSubmodule _ _).mp (H i).property
    have h₁ : (D.val^(m*t-∑i,(e i).val)).IsHomogeneous (m*t-∑i,(e i).val) := by
      simpa using hD.pow (m*t-∑i,(e i).val)
    have h₂ := IsHomogeneous.prod Finset.univ (fun i => (H i).val^(e i).val)
      (fun i => (e i).val) (fun i _ => by simpa using (hH i).pow (e i).val)
    simpa only [Nat.sub_add_cancel (degree_le e)] using h₁.mul h₂⟩

lemma eval_homogeneousForms {σ : Type*} {m t : ℕ}
    (D : homogeneousSubmodule σ ℂ 1) (H : Fin m → homogeneousSubmodule σ ℂ 1)
    (e : Box m t) (x : σ → ℂ) (hD : eval x D.val≠0) :
    eval x (homogeneousForms D H e).val = (eval x D.val)^(m*t)*
      eval (fun i => eval x (H i).val/eval x D.val) (affine e) := by
  classical
  simp only [homogeneousForms,eval_mul,map_pow,map_prod,eval_affine,div_pow,
    Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
  rw [pow_sub₀ _ hD (degree_le e)]
  field_simp

end BoxMonomials

 

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

 

open Set Filter Topology
open scoped ContDiff
namespace RectangularInverse
variable {A B V : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ A] in
lemma exists_continuous_left_inverse (D : A →L[ℂ] V) (hi : Function.Injective D) :
    ∃p : V →L[ℂ] A,p.comp D=ContinuousLinearMap.id ℂ A := by
  obtain ⟨p,hp⟩ := D.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨p.toContinuousLinearMap,?_⟩
  ext a
  exact LinearMap.congr_fun hp a

omit [FiniteDimensional ℂ A] [FiniteDimensional ℂ B] in
lemma triangular_bijective (D : A × B →L[ℂ] A)
    (hD : ∀a,D (a,0)=a) : Function.Bijective (D.prod (ContinuousLinearMap.snd ℂ A B)) := by
  have he (a : A) (b : B) : D (a,b)=a+D (0,b) := by
    have hd := D.map_add (a,0) (0,b)
    simpa only [Prod.mk_add_mk,add_zero,zero_add,hD] using hd
  constructor
  · intro x y h
    have hb := congrArg Prod.snd h
    have ha := congrArg Prod.fst h
    change x.2=y.2 at hb
    change D x=D y at ha
    change D (x.1,x.2)=D (y.1,y.2) at ha
    rw [he x.1 x.2,he y.1 y.2,hb] at ha
    exact Prod.ext (add_right_cancel ha) hb
  · intro y
    refine ⟨(y.1-D (0,y.2),y.2),?_⟩
    apply Prod.ext
    · change D (y.1-D (0,y.2),y.2)=y.1
      rw [he,sub_add_cancel]
    · rfl

 

theorem exists_chart {f : A × B → V} {x : A × B} (hf : AnalyticAt ℂ f x)
    (hi : Function.Injective ((fderiv ℂ f x).comp (ContinuousLinearMap.inl ℂ A B))) :
    ∃(p : V →L[ℂ] A) (Q : OpenPartialHomeomorph (A × B) (A × B)),
      x∈Q.source ∧ (∀z,Q z=(p (f z),z.2)) ∧
      AnalyticAt ℂ Q x ∧ AnalyticAt ℂ Q.symm (Q x) := by
  obtain ⟨p,hp⟩ := exists_continuous_left_inverse _ hi
  let ψ : A × B → A × B := fun z => (p (f z),z.2)
  have hψ : AnalyticAt ℂ ψ x := ((p.analyticAt (f x)).comp hf).prod analyticAt_snd
  have hdψ : fderiv ℂ ψ x=((p.comp (fderiv ℂ f x)).prod (ContinuousLinearMap.snd ℂ A B)) :=
    ((p.hasFDerivAt.comp x hf.differentiableAt.hasFDerivAt).prodMk
      (ContinuousLinearMap.snd ℂ A B).hasFDerivAt).fderiv
  have hbij : Function.Bijective (fderiv ℂ ψ x) := by
    rw [hdψ]
    apply triangular_bijective
    intro a
    exact DFunLike.congr_fun hp a
  let E := (LinearEquiv.ofBijective (fderiv ℂ ψ x).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasFDerivAt ψ (E : A × B →L[ℂ] A × B) x := hψ.differentiableAt.hasFDerivAt
  let hc : ContDiffAt ℂ ω ψ x := hψ.contDiffAt
  let Q := hc.toOpenPartialHomeomorph ψ hd (by simp)
  refine ⟨p,Q,hc.mem_toOpenPartialHomeomorph_source hd (by simp),fun _ => rfl,hψ,?_⟩
  exact (hc.to_localInverse hd (by simp)).analyticAt

end RectangularInverse

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators
namespace PolynomialSpecialization
open _root_.MvPolynomial

lemma eval_analyticAtAlternative {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    AnalyticAt ℂ (fun y => eval y p) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (analyticAt_const (v := c) (x := x))
  | add p q hp hq =>
      have he : (fun y => eval y (p+q))=((fun y => eval y p)+(fun y => eval y q)) := by
        funext y
        exact eval_add
      rw [he]
      exact hp.add hq
  | mul_X p i hp =>
      have he : (fun y => eval y (p*MvPolynomial.X i))=((fun y => eval y p)*(fun y => y i)) := by
        funext y
        simp only [eval_mul,eval_X,Pi.mul_apply]
      rw [he]
      exact hp.mul ((ContinuousLinearMap.proj i : (σ → ℂ) →L[ℂ] ℂ).analyticAt x)

end PolynomialSpecialization

 

 

open Set Filter Topology
namespace PolynomialSpecialization
open _root_.MvPolynomial
variable {σ ι A B Y : Type*} [Fintype σ] [Fintype ι]
  [NormedAddCommGroup A] [NormedSpace ℂ A]

 

theorem finite_transversal
    (T : Set B) {U : Set A} (hU : IsOpen U) (hne : U.Nonempty)
    (E : A ≃L[ℂ] (σ → ℂ)) (lift : A → B → Y)
    (coord : Y → ι → ℂ) (first : Y → σ → ℂ)
    (hfirst : ∀a∈U,∀b∈T,first (lift a b)=E a)
    (hinj : ∀a∈U,Set.InjOn (fun b => coord (lift a b)) T)
    (p : ι → MvPolynomial (Option σ) ℂ) (hp : ∀i,p i≠0)
    (hroot : ∀a∈U,∀b∈T,∀i,
      eval (fun t => Option.elim t (coord (lift a b) i) (first (lift a b))) (p i)=0) :
    T.Finite := by
  obtain ⟨a,ha,hn⟩ := generic_specialization p hp (E.isOpenMap U hU) (hne.image E)
  obtain ⟨c,hc,hca⟩ := ha
  apply finite_fiber T (fun b => coord (lift c b)) (hinj c hc)
    (fun i => Polynomial.map (eval a) (optionEquivLeft ℂ σ (p i))) hn
  intro b hb i
  have hr := hroot c hc b hb i
  rw [hfirst c hc b hb,hca,optionEquivLeft_elim_eval] at hr
  exact hr

end PolynomialSpecialization

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

open Set Filter Topology

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

open Set Filter Topology
open scoped Manifold ContDiff

namespace HolomorphicLocalDiffeomorph
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ,E) ω M] [IsManifold 𝓘(ℂ,F) ω N]

 

theorem of_analytic_partial_homeomorphAlternative (φ : OpenPartialHomeomorph M N)
    {x : M} (hx : x∈φ.source)
    (hφ : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω φ x)
    (hφs : ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,E) ω φ.symm (φ x)) :
    IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω φ x := by
  have he : ∀ᶠ y in 𝓝 x,
      ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω φ y ∧
      ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,E) ω φ.symm (φ y) :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hφ).and
      (hφ.continuousAt.eventually ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hφs))
  obtain ⟨U,hUsub,hU,hxU⟩ := _root_.mem_nhds_iff.mp he
  let ψ := φ.restrOpen U hU
  let Φ : PartialDiffeomorph 𝓘(ℂ,E) 𝓘(ℂ,F) M N ω := {
    ψ.toPartialEquiv with
    open_source := ψ.open_source
    open_target := ψ.open_target
    contMDiffOn_toFun := by
      intro y hy
      exact (hUsub hy.2).1.contMDiffWithinAt
    contMDiffOn_invFun := by
      intro y hy
      have hz : φ.symm y∈ψ.source := ψ.map_target hy
      have hh := (hUsub hz.2).2
      change ContMDiffWithinAt 𝓘(ℂ,F) 𝓘(ℂ,E) ω φ.symm ψ.target y
      simpa only [φ.right_inv hy.1] using hh.contMDiffWithinAt }
  exact ⟨Φ,⟨hx,hxU⟩,fun _ _ => rfl⟩

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ,E) ω M] [IsManifold 𝓘(ℂ,F) ω N]

omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℂ, F) ω N] in
theorem congr_eventuallyAlternative {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x)
    (he : f=ᶠ[𝓝 x]g) : IsLocalDiffeomorphAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω g x := by
  obtain ⟨φ,hx,hφ⟩ := hf
  obtain ⟨U,hUsub,hU,hxU⟩ := _root_.mem_nhds_iff.mp he
  let ψ := φ.toOpenPartialHomeomorph.restrOpen U hU
  let Φ : PartialDiffeomorph 𝓘(ℂ,E) 𝓘(ℂ,F) M N ω := {
    ψ.toPartialEquiv with
    open_source := ψ.open_source
    open_target := ψ.open_target
    contMDiffOn_toFun := φ.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨Φ,⟨hx,hxU⟩,?_⟩
  intro y hy
  exact (hUsub hy.2).symm.trans (hφ hy.1)

end HolomorphicLocalDiffeomorph

 

 

open Set Filter Topology
open scoped Manifold ContDiff
namespace HolomorphicLocalDiffeomorph
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]
  [IsManifold 𝓘(ℂ,E) ω M] [IsManifold 𝓘(ℂ,F) ω N]

lemma map_nhds_of_surjective_mfderiv {f : M → N} {x : M}
    (hf : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f x)
    (hs : Function.Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x)) :
    Filter.map f (𝓝 x)=𝓝 (f x) := by
  let c := chartAt E x
  let d := chartAt F (f x)
  have hc : x∈c.source := mem_chart_source E x
  have hd : f x∈d.source := mem_chart_source F (f x)
  have hcs : c.symm (c x)=x := c.left_inv hc
  have hdl := chart_local hd
  have hcsl := chart_symm_local (c.map_source hc)
  let g : E → F := d ∘ f ∘ c.symm
  have hfcs : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,F) ω f (c.symm (c x)) := by simpa only [hcs]
  have hinner := hfcs.comp (c x) hcsl.contMDiffAt
  have hdcs : ContMDiffAt 𝓘(ℂ,F) 𝓘(ℂ,F) ω d (f (c.symm (c x))) := by
    simpa only [hcs] using hdl.contMDiffAt
  have hg : ContDiffAt ℂ ω g (c x) := (hdcs.comp (c x) hinner).contDiffAt
  have hsg : Function.Surjective (fderiv ℂ g (c x)) := by
    rw [←mfderiv_eq_fderiv]
    change Function.Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) (d ∘ (f ∘ c.symm)) (c x))
    rw [mfderiv_comp (c x) (f := f ∘ c.symm) (g := d) (hdcs.mdifferentiableAt (by simp))
      (hinner.mdifferentiableAt (by simp)),
      mfderiv_comp (c x) (f := c.symm) (g := f) (hfcs.mdifferentiableAt (by simp))
        (hcsl.mdifferentiableAt (by simp))]
    have hs' : Function.Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f (c.symm (c x))) := by
      rw [hcs]
      exact hs
    have hd' : Function.Surjective (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,F) d (f (c.symm (c x)))) := by
      rw [hcs]
      exact (hdl.mfderivToContinuousLinearEquiv (by simp)).surjective
    exact hd'.comp (hs'.comp (hcsl.mfderivToContinuousLinearEquiv (by simp)).surjective)
  have hgmap := (hg.hasStrictFDerivAt (by simp)).map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsg)
  have he : (d.symm ∘ g ∘ c)=ᶠ[𝓝 x] f := by
    filter_upwards [c.open_source.mem_nhds hc,
      hf.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hd)] with y hy hfy
    change d.symm (d (f (c.symm (c y))))=f y
    rw [c.left_inv hy,d.left_inv hfy]
  rw [←Filter.map_congr he,←Filter.map_map,←Filter.map_map,c.map_nhds_eq hc,hgmap]
  have heq : g (c x)=d (f x) := by simp only [g,Function.comp_apply,hcs]
  rw [heq,d.symm.map_nhds_eq (d.map_source hd),d.left_inv hd]

lemma isOpenMap_of_surjective_mfderiv {f : M → N}
    (hf : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) ω f)
    (hs : ∀x,Function.Surjective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f x)) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.mpr (fun x => (map_nhds_of_surjective_mfderiv (hf x) (hs x)).ge)

end HolomorphicLocalDiffeomorph

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

open Set Filter Topology IsManifold
open scoped ContDiff Manifold
namespace SplitTangent
open AnalyticZeroCover RationalParameters

theorem RationallyConnected.exists_submersive_family_in_openAlternative {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (hdim : 0<X.dim) (V₀ : Set (X.Carrier × X.Carrier))
    (hV₀ : IsOpen V₀) (hV₀n : V₀.Nonempty) :
    ∃T : ComplexManifold.{u}, Nonempty T.Carrier ∧
      ∃G : RationalFamily X T, (∀τ,G.twoPointEvaluation 0 1 τ∈V₀) ∧ ∀τ, Function.Surjective
        (mfderiv (ModelWithCorners T) ((ModelWithCorners X).prod (ModelWithCorners X))
          (G.twoPointEvaluation 0 1) τ) := by
  classical
  let : ChartedSpace (Model X × Model X) (X.Carrier × X.Carrier) :=
    prodChartedSpace (Model X) X.Carrier (Model X) X.Carrier
  let : IsManifold 𝓘(ℂ,Model X × Model X) ω (X.Carrier × X.Carrier) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod X.Carrier X.Carrier
  obtain ⟨xy,hxy⟩ := hRC.choose_spec.2.1
  let x₀ := xy.1
  obtain ⟨C,hC,hCP,V,hV,hVn,hVd,hcov⟩ := hRC.countable_dense_family_cover e x₀
  let : ∀d, Countable (C d) := fun d => (hC d).to_subtype
  let A := Σd, C d
  let d (a : A) := a.2.val.dim
  let f (a : A) := pairEvaluation e x₀ a.2.val
  let U (a : A) : Set (Space (d a)) := a.2.val.domain ∩ (f a) ⁻¹' V₀
  have hU (a : A) : IsOpen (U a) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.inter_mem (a.2.val.isOpen_domain.mem_nhds hx.1)
      ((pairEvaluation_holomorphicAt e x₀ a.2.val
        (hCP a.1 a.2.val a.2.property) hx.1).continuousAt.preimage_mem_nhds (hV₀.mem_nhds hx.2))
  have hf (a : A) (x) (hx : x∈U a) :
      ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) x := by
    rw [modelWithCornersSelf_prod]
    exact pairEvaluation_holomorphicAt e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hx.1
  have hcover : V∩V₀ ⊆ ⋃a,f a '' U a := by
    intro v hv
    obtain ⟨n,hn⟩ := mem_iUnion.mp (hcov hv.1)
    obtain ⟨P,hP,x,hx,hfx⟩ := mem_iUnion₂.mp hn
    exact mem_iUnion.mpr ⟨⟨n,⟨P,hP⟩⟩,x,⟨hx,by
      change pairEvaluation e x₀ P x ∈ V₀
      rw [hfx]
      exact hv.2⟩,hfx⟩
  have hdim' : 0<Module.finrank ℂ (Model X × Model X) := by
    simp only [Module.finrank_prod,Model,Module.finrank_fin_fun]
    omega
  obtain ⟨y,a,x,hx,hfx,hs⟩ := exists_chart_submersion_of_cover d U f hU hf
    (hV.inter hV₀) (by simpa only [Set.inter_comm] using hVd.inter_open_nonempty V₀ hV₀ hV₀n) hcover hdim'
  let c := chartAt (Model X × Model X) y
  have hc : c ∈ maximalAtlas 𝓘(ℂ,Model X × Model X) ω _ :=
    IsManifold.chart_mem_maximalAtlas y
  have hcoord : AnalyticAt ℂ (c ∘ f a) x :=
    ((contMDiffAt_of_mem_maximalAtlas hc hfx).comp x (hf a x hx)).contDiffAt.analyticAt
  have hn : ∀ᶠz in 𝓝 x, z∈U a ∧ f a z∈c.source ∧
      Function.Surjective (fderiv ℂ (c ∘ f a) z) :=
    Filter.Eventually.and ((hU a).mem_nhds hx) (Filter.Eventually.and
      ((hf a x hx).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hfx))
      (eventually_surjective_fderiv hcoord hs))
  obtain ⟨W,hWsub,hW,hxW⟩ := _root_.mem_nhds_iff.mp hn
  have hWn : W.Nonempty := ⟨x,hxW⟩
  have hWP : W⊆U a := fun z hz => (hWsub hz).1
  let T := OpenManifold.manifold.{u} W hW hWn
  let G := family e x₀ a.2.val (hCP a.1 a.2.val a.2.property) hW hWn (fun z hz => (hWP hz).1)
  refine ⟨T,OpenManifold.nonempty W hWn,G,?_,?_⟩
  · intro τ
    exact (hWP τ.down.property).2
  intro τ
  let z := OpenManifold.val W τ
  have hz : z∈W := τ.down.property
  have hzf : ContMDiffAt 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) ω (f a) z :=
    hf a z (hWP hz)
  have hsurj : Function.Surjective
      (mfderiv 𝓘(ℂ,Space (d a)) 𝓘(ℂ,Model X × Model X) (f a) z) :=
    surjective_mfderiv_of_chart hzf y (hWsub hz).2.1 (hWsub hz).2.2
  have hv := (OpenManifold.val_mfderiv_bijective W hW hWn τ).2
  have hchain := mfderiv_comp τ (hzf.mdifferentiableAt (by decide))
    ((OpenManifold.val_holomorphic W hW hWn τ).mdifferentiableAt (by decide))
  rw [← modelWithCornersSelf_prod]
  change Function.Surjective (mfderiv (ModelWithCorners (OpenManifold.manifold.{u} W hW hWn))
    𝓘(ℂ,Model X × Model X)
    ((f a) ∘ (fun τ : (OpenManifold.manifold.{u} W hW hWn).Carrier => OpenManifold.val W τ)) τ)
  rw [hchain]
  exact hsurj.comp hv

end SplitTangent

 

 

open Set Filter Topology
open scoped ContDiff Manifold

 

 

open Set Filter Topology
open scoped ContDiff Manifold BigOperators

 

open Set Filter Topology
open scoped Manifold ContDiff BigOperators

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 
open Set Filter Topology TopologicalSpace

 

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff BigOperators

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff BigOperators

 

open Set Filter Topology

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

 

open Set Filter Topology
namespace FiniteOpenMaps
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] (f : X → Y) (ho : IsOpenMap f)
  (hfin : ∀ y, (f ⁻¹' {y}).Finite)

omit [TopologicalSpace X] [T2Space X] in
lemma constantCardLocus_isOpenAlternative : IsOpen (constantCardLocus f) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨U,hsub,hU,hyU⟩ := _root_.mem_nhds_iff.mp hy
  apply Filter.mem_of_superset (hU.mem_nhds hyU)
  intro z hz
  change ∀ᶠ w in 𝓝 z, fiberCard f w=fiberCard f z
  filter_upwards [hU.mem_nhds hz] with w hw
  exact (hsub hw).trans (hsub hz).symm

end FiniteOpenMaps

 

 

open Set Filter Topology
namespace FiniteOpenMaps
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] (f : X → Y) (ho : IsOpenMap f)
  (hfin : ∀ y, (f ⁻¹' {y}).Finite)

include ho hfin in
lemma locally_injective_of_card_constantAlternative (hf : Continuous f) {x : X}
    (hx : f x∈constantCardLocus f) :
    ∃ U : Set X, IsOpen U ∧ x∈U ∧ Set.InjOn f U := by
  classical
  obtain ⟨N,hNs,hNo,hxN⟩ := _root_.mem_nhds_iff.mp hx
  obtain ⟨U,hU,hdis⟩ := (hfin (f x)).t2_separation
  let V : Set Y := N ∩ ⋂k∈f ⁻¹' {f x}, f '' U k
  have hVo : IsOpen V := hNo.inter
    ((hfin (f x)).isOpen_biInter (fun k _ => ho _ (hU k).2))
  have hxV : f x∈V := ⟨hxN,Set.mem_iInter₂.mpr fun k hk => ⟨k,(hU k).1,hk⟩⟩
  refine ⟨U x ∩ f ⁻¹' V,(hU x).2.inter (hVo.preimage hf),⟨(hU x).1,hxV⟩,?_⟩
  intro a ha b hb hab
  exact unique_in_branch f hfin hdis ha.2.2 (le_of_eq (hNs ha.2.1)) rfl
    ha.1 hb.1 rfl hab.symm

end FiniteOpenMaps

 

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

 

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff
namespace SplitTangent

 

lemma holomorphicAt_tangentMapAlternative {X Y : ComplexManifold.{u}}
    {f : X.Carrier → Y.Carrier} {x : X.Carrier}
    (hf : ContMDiffAt (ModelWithCorners X) (ModelWithCorners Y) ω f x)
    (v : Tangent X x) :
    ContMDiffAt ((ModelWithCorners X).prod 𝓘(ℂ,Model X))
      ((ModelWithCorners Y).prod 𝓘(ℂ,Model Y)) ω
      (tangentMap (ModelWithCorners X) (ModelWithCorners Y) f)
      (⟨x,v⟩ : TangentBundle (ModelWithCorners X) X.Carrier) := by
  obtain ⟨s,hs,hfs⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp : (ω : WithTop ℕ∞)≠(∞ : WithTop ℕ∞))).mp hf
  obtain ⟨U,hUs,hU,hxU⟩ := _root_.mem_nhds_iff.mp hs
  have hFU := hfs.mono hUs
  have hTU := hFU.contMDiffOn_tangentMapWithin (m := ω) (by simp) hU.uniqueMDiffOn
  have hπ : Continuous (fun p : TangentBundle (ModelWithCorners X) X.Carrier => p.proj) :=
    (contMDiff_proj (IB := ModelWithCorners X) (n := ω) (TangentSpace (ModelWithCorners X))).continuous
  have hn : (fun p : TangentBundle (ModelWithCorners X) X.Carrier => p.proj) ⁻¹' U ∈
      𝓝 (⟨x,v⟩ : TangentBundle (ModelWithCorners X) X.Carrier) :=
    hπ.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
  apply (hTU.contMDiffAt hn).congr_of_eventuallyEq
  filter_upwards [hn] with p hp
  exact (tangentMapWithin_eq_tangentMap (hU.uniqueMDiffOn p.proj hp)
    ((hFU.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))).symm

end SplitTangent

 

 

open Set Filter Topology Bundle
open scoped Manifold ContDiff

 

 

open Set Filter Topology
open scoped Manifold ContDiff

end

end OAI
