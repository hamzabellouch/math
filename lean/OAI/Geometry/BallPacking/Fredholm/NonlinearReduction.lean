import Mathlib
import OAI.Geometry.BallPacking.Continuation.ParameterizedImplicit

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {D : E →L[ℝ] F} (pkg : D.FredholmPackage)

omit [CompleteSpace E] in
lemma fredholm_original_coords [CompleteSpace E] (x : E) :
    (codCoords pkg) (D x) = (pkg.equiv ((domCoords pkg) x).1,0) := by
  have hz : finitePerturbation pkg (0 : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [_root_.OAI.ContinuousLinearMap.FredholmPackage.finitePerturbation,
      ContinuousLinearMap.comp_apply,zero_apply,map_zero]
  have hh := finitePerturbation_coords pkg (0 : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) x
  simpa only [hz,add_zero,zero_apply] using hh

def fredholmNonlinearCoords (f : E → F) (x : E) : pkg.decCodom.X₁ × pkg.decDom.X₀ :=
  (((codCoords pkg) (f x)).1,((domCoords pkg) x).2)

def fredholmCoordEquiv : E ≃L[ℝ] (pkg.decCodom.X₁ × pkg.decDom.X₀) :=
  (domCoords pkg).trans (pkg.equiv.prodCongr (ContinuousLinearEquiv.refl ℝ pkg.decDom.X₀))

omit [CompleteSpace E] in
lemma fredholmNonlinearCoords_contDiff [CompleteSpace E] {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fredholmNonlinearCoords pkg f) :=
  ((((codCoords pkg).contDiff.comp hf).fst).prodMk (domCoords pkg).contDiff.snd)

lemma fredholmNonlinearCoords_hasFDerivAt {f : E → F} {a : E} (hf : HasFDerivAt f D a) :
    HasFDerivAt (fredholmNonlinearCoords pkg f) (fredholmCoordEquiv pkg).toContinuousLinearMap a := by
  have h₁ := ((ContinuousLinearMap.fst ℝ pkg.decCodom.X₁ pkg.decCodom.X₀).comp
    (codCoords pkg).toContinuousLinearMap).hasFDerivAt.comp a hf
  have h₂ := ((ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp
    (domCoords pkg).toContinuousLinearMap).hasFDerivAt (x := a)
  have he : (((ContinuousLinearMap.fst ℝ pkg.decCodom.X₁ pkg.decCodom.X₀).comp
        (codCoords pkg).toContinuousLinearMap).comp D).prod
      ((ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp
        (domCoords pkg).toContinuousLinearMap) = (fredholmCoordEquiv pkg).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · change ((codCoords pkg) (D x)).1 = pkg.equiv ((domCoords pkg) x).1
      exact congrArg Prod.fst (fredholm_original_coords pkg x)
    · rfl
  exact he ▸ h₁.prodMk h₂

variable {f : E → F} (hf : ContDiff ℝ ∞ f) {a : E} (hD : HasFDerivAt f D a)

def fredholmCoordChart : OpenPartialHomeomorph E (pkg.decCodom.X₁ × pkg.decDom.X₀) :=
  (fredholmNonlinearCoords_contDiff pkg hf).contDiffAt.toOpenPartialHomeomorph
    (fredholmNonlinearCoords pkg f) (fredholmNonlinearCoords_hasFDerivAt pkg hD) (by simp)

lemma fredholmCoordChart_value (x : E) :
    fredholmCoordChart pkg hf hD x = fredholmNonlinearCoords pkg f x := rfl

lemma fredholmCoordChart_base_mem : a ∈ (fredholmCoordChart pkg hf hD).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source
    (fredholmNonlinearCoords_contDiff pkg hf).contDiffAt
    (fredholmNonlinearCoords_hasFDerivAt pkg hD) (by simp)

lemma fredholmCoordChart_inverse_smooth :
    ContDiffAt ℝ ∞ (fredholmCoordChart pkg hf hD).symm (fredholmNonlinearCoords pkg f a) :=
  ContDiffAt.to_localInverse (fredholmNonlinearCoords_contDiff pkg hf).contDiffAt
    (fredholmNonlinearCoords_hasFDerivAt pkg hD) (by simp)

def fredholmObstruction (k : pkg.decDom.X₀) : pkg.decCodom.X₀ :=
  ((codCoords pkg) (f ((fredholmCoordChart pkg hf hD).symm (0,k)))).2

def fredholmSolutionParam (k : pkg.decDom.X₀) : E :=
  (fredholmCoordChart pkg hf hD).symm (0,k)

lemma fredholmSolutionParam_base {ha : f a = 0} :
    fredholmSolutionParam pkg hf hD ((domCoords pkg) a).2 = a := by
  have he : fredholmNonlinearCoords pkg f a = (0,((domCoords pkg) a).2) := by
    change (((codCoords pkg) (f a)).1,_) = _
    rw [ha,map_zero]; rfl
  have hx := (fredholmCoordChart pkg hf hD).left_inv (fredholmCoordChart_base_mem pkg hf hD)
  change (fredholmCoordChart pkg hf hD).symm (fredholmNonlinearCoords pkg f a) = a at hx
  unfold fredholmSolutionParam
  rw [←he]
  exact hx

lemma fredholmSolutionParam_smooth {ha : f a = 0} :
    ContDiffAt ℝ ∞ (fredholmSolutionParam pkg hf hD) ((domCoords pkg) a).2 := by
  have he : fredholmNonlinearCoords pkg f a = (0,((domCoords pkg) a).2) := by
    change (((codCoords pkg) (f a)).1,_) = _
    rw [ha,map_zero]; rfl
  have hs := fredholmCoordChart_inverse_smooth pkg hf hD
  rw [he] at hs
  exact hs.comp _ (contDiffAt_const.prodMk contDiffAt_id)

lemma fredholmObstruction_smooth {ha : f a = 0} :
    ContDiffAt ℝ ∞ (fredholmObstruction pkg hf hD) ((domCoords pkg) a).2 := by
  exact (((codCoords pkg).contDiff.contDiffAt.comp _
    (hf.contDiffAt.comp _ (fredholmSolutionParam_smooth pkg hf hD (ha := ha)))).snd)

lemma fredholmParam_zero_iff (k : pkg.decDom.X₀)
    (hk : (0,k) ∈ (fredholmCoordChart pkg hf hD).target) :
    f (fredholmSolutionParam pkg hf hD k) = 0 ↔ fredholmObstruction pkg hf hD k = 0 := by
  have he := (fredholmCoordChart pkg hf hD).right_inv hk
  change fredholmNonlinearCoords pkg f (fredholmSolutionParam pkg hf hD k) = (0,k) at he
  have hfirst := congrArg Prod.fst he
  constructor
  · intro hz
    change ((codCoords pkg) (f (fredholmSolutionParam pkg hf hD k))).2 = 0
    rw [hz,map_zero]; rfl
  · intro hz
    apply (codCoords pkg).injective
    rw [map_zero]
    exact Prod.ext hfirst hz

lemma fredholm_zero_coord_iff (x : E) (hx : x ∈ (fredholmCoordChart pkg hf hD).source) :
    f x = 0 ↔ ((codCoords pkg) (f x)).1 = 0 ∧
      fredholmObstruction pkg hf hD ((domCoords pkg) x).2 = 0 := by
  constructor
  · intro hz
    have h1 : ((codCoords pkg) (f x)).1 = 0 := by rw [hz,map_zero]; rfl
    have he : fredholmSolutionParam pkg hf hD ((domCoords pkg) x).2 = x := by
      have hh := (fredholmCoordChart pkg hf hD).left_inv hx
      change (fredholmCoordChart pkg hf hD).symm (((codCoords pkg) (f x)).1,((domCoords pkg) x).2)=x at hh
      rw [h1] at hh
      exact hh
    refine ⟨h1,?_⟩
    change ((codCoords pkg) (f (fredholmSolutionParam pkg hf hD ((domCoords pkg) x).2))).2 = 0
    rw [he,hz,map_zero]; rfl
  · rintro ⟨h1,h2⟩
    have he : fredholmSolutionParam pkg hf hD ((domCoords pkg) x).2 = x := by
      have hh := (fredholmCoordChart pkg hf hD).left_inv hx
      change (fredholmCoordChart pkg hf hD).symm (((codCoords pkg) (f x)).1,((domCoords pkg) x).2)=x at hh
      rw [h1] at hh
      exact hh
    apply (codCoords pkg).injective
    rw [map_zero]
    apply Prod.ext h1
    change ((codCoords pkg) (f (fredholmSolutionParam pkg hf hD ((domCoords pkg) x).2))).2=0 at h2
    rw [he] at h2
    exact h2

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
section Generic
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {D : X →L[ℝ] Y}
lemma fredholmPackage_balanced (pkg : D.FredholmPackage) (hi : IsIndexZeroFredholm D) :
    Module.finrank ℝ pkg.decDom.X₀ = Module.finrank ℝ pkg.decCodom.X₀ := by
  have h := hi.2
  rw [pkg.ker_eq,pkg.range_eq] at h
  exact h.trans (Submodule.quotientEquivOfIsCompl pkg.decCodom.X₁ pkg.decCodom.X₀
    pkg.decCodom.isTopCompl.isCompl).finrank_eq

lemma fredholmObstruction_smooth_zero [CompleteSpace X] (pkg : D.FredholmPackage)
    {f : X → Y} (hf : ContDiff ℝ ∞ f) (hD : HasFDerivAt f D 0) (hz : f 0 = 0) :
    ContDiffAt ℝ ∞ (fredholmObstruction pkg hf hD) 0 := by
  have hh := fredholmObstruction_smooth pkg hf hD (ha := hz)
  simpa only [map_zero,Prod.snd_zero] using hh
end Generic

variable {n : ℕ}
local instance actRedInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance actRedInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance actRedInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance actRedInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance actRedInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance actRedInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (b : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance actRedInst7 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actRedInst8 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actRedInst9 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actRedInst7 (n := n) b).toAddCommGroup
local instance actRedInst10 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actRedInst8 (n := n) b).toModule
local instance actRedInst11 : TopologicalSpace (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (actRedInst7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance actRedInst12 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actRedInst13 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance actRedInst14 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actRedInst12 (n := n) b).toAddCommGroup
local instance actRedInst15 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (actRedInst13 (n := n) b).toModule
variable (u : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ᶠ h in 𝓝 (0 : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z : ℂ, b.rIn ≤ ‖z‖ → B < ‖markedCurve p q (u.val+h.val) z‖ ∧
      B < ‖truncatedCurve b p q u.val h.val z‖)

def actualMarkedPackage := Classical.choice
  (actualMarkedChart_derivative_fredholm hJ hc hstd b p q u he).1.nonempty_fredholmPackage

lemma actualMarked_package_balanced :
    Module.finrank ℝ (actualMarkedPackage hJ hc hstd b p q u he).decDom.X₀ =
      Module.finrank ℝ (actualMarkedPackage hJ hc hstd b p q u he).decCodom.X₀ :=
  fredholmPackage_balanced _ (actualMarkedChart_derivative_fredholm hJ hc hstd b p q u he)

def actualMarkedLocalChart := fredholmCoordChart
  (actualMarkedPackage hJ hc hstd b p q u he)
  (actualMarkedChart_contDiff hJ hstd b p q u)
  ((actualMarkedChart_contDiff hJ hstd b p q u).differentiable (by simp) 0).hasFDerivAt

def actualMarkedFiniteObstruction := fredholmObstruction
  (actualMarkedPackage hJ hc hstd b p q u he)
  (actualMarkedChart_contDiff hJ hstd b p q u)
  ((actualMarkedChart_contDiff hJ hstd b p q u).differentiable (by simp) 0).hasFDerivAt

def actualMarkedLocalParam := fredholmSolutionParam
  (actualMarkedPackage hJ hc hstd b p q u he)
  (actualMarkedChart_contDiff hJ hstd b p q u)
  ((actualMarkedChart_contDiff hJ hstd b p q u).differentiable (by simp) 0).hasFDerivAt

lemma actualMarkedLocalChart_base_mem :
    0 ∈ (actualMarkedLocalChart hJ hc hstd b p q u he).source :=
  fredholmCoordChart_base_mem _ _ _

lemma actualMarked_reduced_zero_iff
    (k : (actualMarkedPackage hJ hc hstd b p q u he).decDom.X₀)
    (hk : (0,k) ∈ (actualMarkedLocalChart hJ hc hstd b p q u he).target) :
    actualMarkedChart hJ hstd b p q u (actualMarkedLocalParam hJ hc hstd b p q u he k) = 0 ↔
      actualMarkedFiniteObstruction hJ hc hstd b p q u he k = 0 :=
  fredholmParam_zero_iff _ _ _ k hk

lemma actualMarked_reduced_smooth (hz : actualMarkedChart hJ hstd b p q u 0 = 0) :
    ContDiffAt ℝ ∞ (actualMarkedFiniteObstruction hJ hc hstd b p q u he) 0 :=
  fredholmObstruction_smooth_zero _ _ _ hz

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma indexZero_finite_stabilizer {D : X →L[ℝ] Y} (hD : IsIndexZeroFredholm D) :
    ∃ E : Submodule ℝ Y,FiniteDimensional ℝ E ∧
      ∃ P : X →L[ℝ] E,(D+E.subtypeL.comp P).IsInvertible := by
  obtain ⟨pkg⟩ := hD.1.nonempty_fredholmPackage
  let : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  let : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
  let L : pkg.decDom.X₀ ≃L[ℝ] pkg.decCodom.X₀ :=
    ContinuousLinearEquiv.ofFinrankEq (fredholmPackage_balanced pkg hD)
  let P : X →L[ℝ] pkg.decCodom.X₀ := L.toContinuousLinearMap.comp
    (pkg.decDom.X₀.projectionOntoL _ pkg.decDom.isTopCompl.symm)
  have hinj : Injective (D+finitePerturbation pkg L.toContinuousLinearMap) :=
    (finitePerturbation_injective pkg L.toContinuousLinearMap).mpr L.injective
  have hsurj : Surjective (D+finitePerturbation pkg L.toContinuousLinearMap) :=
    (finitePerturbation_surjective pkg L.toContinuousLinearMap).mpr L.surjective
  refine ⟨pkg.decCodom.X₀,inferInstance,P,?_⟩
  let e := ContinuousLinearEquiv.ofBijective (D+finitePerturbation pkg L.toContinuousLinearMap)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  exact ⟨e,ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

lemma local_indexZero_supplement {Z : Type*} [TopologicalSpace Z]
    {D : Z → X →L[ℝ] Y} (hD : Continuous D) {z : Z} (hDz : IsIndexZeroFredholm (D z)) :
    ∃ E : Submodule ℝ Y,FiniteDimensional ℝ E ∧
      ∃ V : Set Z,IsOpen V ∧ z∈V ∧ ∀ v∈V,Surjective ((D v).coprod E.subtypeL) := by
  obtain ⟨E,hE,P,hP⟩ := indexZero_finite_stabilizer hDz
  let V := {v : Z | (D v+E.subtypeL.comp P).IsInvertible}
  have hVo : IsOpen V :=
    (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := X) (F := Y)).preimage (hD.add continuous_const)
  refine ⟨E,hE,V,hVo,hP,?_⟩
  intro v hv y
  obtain ⟨x,hx⟩ := hv.surjective y
  exact ⟨(x,P x),hx⟩

theorem compact_indexZero_supplement {Z : Type*} [TopologicalSpace Z]
    {D : Z → X →L[ℝ] Y} (hD : Continuous D) {K : Set Z} (hK : IsCompact K)
    (hDK : ∀ z∈K,IsIndexZeroFredholm (D z)) :
    ∃ E : Submodule ℝ Y,FiniteDimensional ℝ E ∧
      ∃ V : Set Z,IsOpen V ∧ K⊆V ∧ ∀ v∈V,Surjective ((D v).coprod E.subtypeL) := by
  classical
  choose E hE V hVo hVz hVS using fun z : K => local_indexZero_supplement hD (hDK z.val z.property)
  let (z : K) : FiniteDimensional ℝ (E z) := hE z
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hVo (by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hVz ⟨z,hz⟩⟩)
  let W := s.sup E
  refine ⟨W,inferInstance,⋃ z∈s,V z,isOpen_biUnion (fun z hz => hVo z),hs,?_⟩
  intro v hv y
  obtain ⟨z,hzs,hvz⟩ := mem_iUnion₂.mp hv
  obtain ⟨⟨x,e⟩,hxe⟩ := hVS z v hvz y
  have hEW : E z≤W := Finset.le_sup hzs
  refine ⟨(x,⟨(e:Y),hEW e.property⟩),?_⟩
  exact hxe

def pathSpatialDerivative (F : ℝ × X → Y) (v : ℝ × X) : X →L[ℝ] Y :=
  (fderiv ℝ F v).comp (ContinuousLinearMap.inr ℝ ℝ X)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma pathSpatialDerivative_eq [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) (v : ℝ × X) :
    pathSpatialDerivative F v=fderiv ℝ (fun y => F (v.1,y)) v.2 := by
  have hD := (hF.differentiable (by simp) v).hasFDerivAt
  have hi : HasFDerivAt (fun y : X => (v.1,y)) (ContinuousLinearMap.inr ℝ ℝ X) v.2 :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have hh := hD.comp v.2 hi
  exact hh.fderiv.symm

omit [CompleteSpace X] [CompleteSpace Y] in
lemma pathSpatialDerivative_continuous [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) :
    Continuous (pathSpatialDerivative F) :=
  ((hF.fderiv_right (m := ∞) (by simp)).continuous).clm_comp continuous_const

def finiteTargetAugment (F : ℝ × X → Y) (E : Submodule ℝ Y) (v : ℝ × (X × E)) : Y :=
  F (v.1,v.2.1)+(v.2.2:Y)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma finiteTargetAugment_smooth [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) (E : Submodule ℝ Y) :
    ContDiff ℝ ∞ (finiteTargetAugment F E) :=
  (hF.comp (contDiff_fst.prodMk contDiff_snd.fst)).add
    (E.subtypeL.contDiff.comp contDiff_snd.snd)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma finiteTargetAugment_spatial_derivative [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F)
    (E : Submodule ℝ Y) (t : ℝ) (x : X) (e : E) :
    fderiv ℝ (fun v : X × E => finiteTargetAugment F E (t,v)) (x,e)=
      (pathSpatialDerivative F (t,x)).coprod E.subtypeL := by
  have hi : HasFDerivAt (fun v : X × E => (t,v.1))
      ((0 : X × E →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ X E)) (x,e) :=
    (hasFDerivAt_const _ _).prodMk hasFDerivAt_fst
  have hD := ((hF.differentiable (by simp) (t,x)).hasFDerivAt.comp (x,e) hi).add
      (E.subtypeL.hasFDerivAt.comp (x,e) hasFDerivAt_snd)
  change fderiv ℝ ((F ∘ fun v : X × E => (t,v.1)) + E.subtypeL ∘ Prod.snd) (x,e)=_
  rw [hD.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem ProperIndexZeroPath.finite_target_supplement {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ E : Submodule ℝ Y,FiniteDimensional ℝ E ∧
      ∃ V : Set (ℝ × X),IsOpen V ∧
        {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}⊆V ∧
        ∀ t x,(t,x)∈V → ∀ e : E,
          Surjective (fderiv ℝ (fun v : X × E => finiteTargetAugment F E (t,v)) (x,e)) := by
  obtain ⟨E,hE,V,hVo,hZ,hV⟩ := compact_indexZero_supplement
    (pathSpatialDerivative_continuous h.smooth) h.zeroSet_compact (by
      intro v hv
      rw [pathSpatialDerivative_eq h.smooth]
      exact h.fredholm v.1 hv.1 v.2 hv.2.1)
  refine ⟨E,hE,V,hVo,hZ,?_⟩
  intro t x hv e
  rw [finiteTargetAugment_spatial_derivative h.smooth]
  exact hV (t,x) hv

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
local instance pfrK : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
local instance pfrC : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
local instance pfrX : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe
local instance pfrY : CompleteSpace pkg.decCodom.X₁ := pkg.decCodom.isTopCompl.isClosed.completeSpace_coe

def parametricEssential (F : ℝ × X → Y) (v : (ℝ × pkg.decDom.X₀) × pkg.decDom.X₁) : pkg.decCodom.X₁ :=
  ((codCoords pkg) (F (v.1.1,(domCoords pkg).symm (v.2,v.1.2)))).1

def parametricBase (t : ℝ) (x : X) : (ℝ × pkg.decDom.X₀) × pkg.decDom.X₁ :=
  ((t,((domCoords pkg) x).2),((domCoords pkg) x).1)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma parametricEssential_smooth [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parametricEssential pkg F) :=
  ((codCoords pkg).contDiff.comp (hF.comp (contDiff_fst.fst.prodMk
    ((domCoords pkg).symm.contDiff.comp (contDiff_snd.prodMk contDiff_fst.snd))))).fst

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

include hD in
omit [CompleteSpace Y] in
lemma parametricEssential_vertical_derivative [CompleteSpace Y] :
    HasFDerivAt (fun y : pkg.decDom.X₁ => parametricEssential pkg F ((t,((domCoords pkg) x).2),y))
      pkg.equiv.toContinuousLinearMap ((domCoords pkg) x).1 := by
  have hi : HasFDerivAt (fun y : pkg.decDom.X₁ => (domCoords pkg).symm (y,((domCoords pkg) x).2))
      ((domCoords pkg).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ pkg.decDom.X₁ pkg.decDom.X₀))
      ((domCoords pkg) x).1 :=
    (domCoords pkg).symm.hasFDerivAt.comp _ (hasFDerivAt_id _ |>.prodMk (hasFDerivAt_const _ _))
  have hx : (domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)=x :=
    (domCoords pkg).symm_apply_apply x
  have hD' : HasFDerivAt (fun y => F (t,y)) D
      ((domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)) := hx.symm ▸ hD
  have hd := hD'.comp (((domCoords pkg) x).1) hi
  have ho := ((codCoords pkg).hasFDerivAt.comp _ hd).fst
  have he : (ContinuousLinearMap.fst ℝ pkg.decCodom.X₁ pkg.decCodom.X₀).comp
      ((codCoords pkg).toContinuousLinearMap.comp (D.comp
        ((domCoords pkg).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ pkg.decDom.X₁ pkg.decDom.X₀))))=
        pkg.equiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    change ((codCoords pkg) (D ((domCoords pkg).symm (y,0)))).1=pkg.equiv y
    rw [fredholm_original_coords,(domCoords pkg).apply_symm_apply]
  exact he ▸ ho

include hF hD in
lemma parametricEssential_invertible :
    ((fderiv ℝ (parametricEssential pkg F) (parametricBase pkg t x)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × pkg.decDom.X₀) pkg.decDom.X₁)).IsInvertible := by
  have hd := ((parametricEssential_smooth pkg hF).differentiable (by simp) (parametricBase pkg t x)).hasFDerivAt
  have hi : HasFDerivAt (fun y : pkg.decDom.X₁ => ((t,((domCoords pkg) x).2),y))
      (ContinuousLinearMap.inr ℝ (ℝ × pkg.decDom.X₀) pkg.decDom.X₁) ((domCoords pkg) x).1 :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have hh := hd.comp (((domCoords pkg) x).1) hi
  have he := hh.unique (parametricEssential_vertical_derivative pkg hD)
  rw [he]
  exact ⟨pkg.equiv,rfl⟩

def parametricInfiniteSolution : ℝ × pkg.decDom.X₀ → pkg.decDom.X₁ :=
  (parametricEssential_smooth pkg hF).contDiffAt.implicitFunction (by simp)
    (parametricEssential_invertible pkg hF hD)

def parametricSolution (v : ℝ × pkg.decDom.X₀) : X :=
  (domCoords pkg).symm (parametricInfiniteSolution pkg hF hD v,v.2)

def parametricObstruction (v : ℝ × pkg.decDom.X₀) : pkg.decCodom.X₀ :=
  ((codCoords pkg) (F (v.1,parametricSolution pkg hF hD v))).2

lemma parametricInfiniteSolution_base :
    parametricInfiniteSolution pkg hF hD (t,((domCoords pkg) x).2)=((domCoords pkg) x).1 :=
  (parametricEssential_smooth pkg hF).contDiffAt.implicitFunction_apply_self (by simp)
    (parametricEssential_invertible pkg hF hD)

lemma parametricSolution_base : parametricSolution pkg hF hD (t,((domCoords pkg) x).2)=x := by
  rw [parametricSolution,parametricInfiniteSolution_base]
  exact (domCoords pkg).symm_apply_apply x

lemma parametricSolution_smooth :
    ContDiffAt ℝ ∞ (parametricSolution pkg hF hD) (t,((domCoords pkg) x).2) :=
  (domCoords pkg).symm.contDiff.contDiffAt.comp _
    (((parametricEssential_smooth pkg hF).contDiffAt.contDiffAt_implicitFunction (by simp)
      (parametricEssential_invertible pkg hF hD)).prodMk contDiffAt_snd)

lemma parametricObstruction_smooth :
    ContDiffAt ℝ ∞ (parametricObstruction pkg hF hD) (t,((domCoords pkg) x).2) :=
  ((codCoords pkg).contDiff.contDiffAt.comp _ (hF.contDiffAt.comp _
    (contDiffAt_fst.prodMk (parametricSolution_smooth pkg hF hD)))).snd

include hD in
lemma parametricSolution_zero_iff (hz : F (t,x)=0) :
    ∀ᶠ v in 𝓝 (t,((domCoords pkg) x).2),
      F (v.1,parametricSolution pkg hF hD v)=0 ↔ parametricObstruction pkg hF hD v=0 := by
  have hh := (parametricEssential_smooth pkg hF).contDiffAt.eventually_apply_implicitFunction
    (by simp) (parametricEssential_invertible pkg hF hD)
  have hb : parametricEssential pkg F (parametricBase pkg t x)=0 := by
    change ((codCoords pkg) (F (t,(domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)))).1=0
    rw [(domCoords pkg).symm_apply_apply,hz,map_zero]; rfl
  filter_upwards [hh] with v hv
  have hfirst : ((codCoords pkg) (F (v.1,parametricSolution pkg hF hD v))).1=0 := hv.trans hb
  constructor
  · intro he
    change ((codCoords pkg) (F (v.1,parametricSolution pkg hF hD v))).2=0
    rw [he,map_zero]; rfl
  · intro he
    apply (codCoords pkg).injective
    rw [map_zero]
    exact Prod.ext hfirst he

include hD in
lemma parametric_zero_is_solution (hz : F (t,x)=0) :
    ∀ᶠ v in 𝓝 (t,x),F v=0 →
      parametricSolution pkg hF hD (v.1,((domCoords pkg) v.2).2)=v.2 := by
  have hh := (parametricEssential_smooth pkg hF).contDiffAt.eventually_apply_eq_iff_implicitFunction
    (by simp) (parametricEssential_invertible pkg hF hD)
  have hm : Continuous (fun v : ℝ × X => parametricBase pkg v.1 v.2) := by
    exact (continuous_fst.prodMk ((domCoords pkg).continuous.comp continuous_snd).snd).prodMk
      ((domCoords pkg).continuous.comp continuous_snd).fst
  have hb : parametricEssential pkg F (parametricBase pkg t x)=0 := by
    change ((codCoords pkg) (F (t,(domCoords pkg).symm (((domCoords pkg) x).1,((domCoords pkg) x).2)))).1=0
    rw [(domCoords pkg).symm_apply_apply,hz,map_zero]; rfl
  filter_upwards [(hm.tendsto (t,x)).eventually hh] with v hv hv0
  have he : parametricEssential pkg F (parametricBase pkg v.1 v.2)=0 := by
    change ((codCoords pkg) (F (v.1,(domCoords pkg).symm (((domCoords pkg) v.2).1,((domCoords pkg) v.2).2)))).1=0
    rw [(domCoords pkg).symm_apply_apply,hv0,map_zero]; rfl
  have hu := hv.mp (he.trans hb.symm)
  change parametricInfiniteSolution pkg hF hD (v.1,((domCoords pkg) v.2).2)=((domCoords pkg) v.2).1 at hu
  rw [parametricSolution,hu]
  exact (domCoords pkg).symm_apply_apply v.2

end
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (hD : D.IsFredholm)
  (E : Submodule ℝ Y) [FiniteDimensional ℝ E]

include hD in
omit [CompleteSpace Y] in
lemma finite_ker_augment [CompleteSpace Y] : FiniteDimensional ℝ (D.coprod E.subtypeL).ker := by
  obtain ⟨pkg⟩ := hD.nonempty_fredholmPackage
  let : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  let G := D.coprod E.subtypeL
  let A : X × E →L[ℝ] pkg.decDom.X₀ × E :=
    ((ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp
      ((domCoords pkg).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ X E))).prod
        (ContinuousLinearMap.snd ℝ X E)
  let AK := A.comp G.ker.subtypeL
  have hAK : Injective AK := by
    intro v w he
    change (((domCoords pkg) v.val.1).2,v.val.2)=(((domCoords pkg) w.val.1).2,w.val.2) at he
    have hk : ((domCoords pkg) v.val.1).2=((domCoords pkg) w.val.1).2 := congrArg (Prod.fst : pkg.decDom.X₀ × E → pkg.decDom.X₀) he
    have hee : v.val.2=w.val.2 := congrArg (Prod.snd : pkg.decDom.X₀ × E → E) he
    have hv : D v.val.1+(v.val.2:Y)=0 := v.property
    have hw : D w.val.1+(w.val.2:Y)=0 := w.property
    have hxx : D v.val.1=D w.val.1 := add_right_cancel (hv.trans hw.symm |>.trans (by rw [hee]))
    have hc := congrArg (fun y => ((codCoords pkg) y).1) hxx
    simp only [fredholm_original_coords] at hc
    have hx1 := pkg.equiv.injective hc
    apply Subtype.ext
    exact Prod.ext ((domCoords pkg).injective (Prod.ext hx1 hk)) hee
  exact FiniteDimensional.of_injective AK.toLinearMap hAK

include hD in
lemma augment_fredholm (hG : Surjective (D.coprod E.subtypeL)) :
    (D.coprod E.subtypeL).IsFredholm := by
  let G := D.coprod E.subtypeL
  let : FiniteDimensional ℝ G.ker := finite_ker_augment hD E
  have htop : G.range=⊤ := LinearMap.range_eq_top.mpr hG
  refine ⟨(G.isOpenMap hG).isStrictMap G.continuous,?_,inferInstance,?_,?_⟩
  · rw [htop]
    exact isClosed_univ
  · rw [htop]
    infer_instance
  · exact Submodule.ClosedComplemented.of_finiteDimensional _

end HigherDimensionalBallPacking.Rigidity
end

end OAI
