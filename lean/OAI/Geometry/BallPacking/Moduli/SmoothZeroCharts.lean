import Mathlib
import OAI.Geometry.BallPacking.Degree.EuclideanAtlasTransport
import OAI.Geometry.BallPacking.Moduli.ZeroCharts

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y}

def ZeroGraphChart.restrict (c : ZeroGraphChart F E)
    (D : Set (ℝ × E)) (hD : IsOpen D) (hDc : D⊆c.domain)
    (hb : (c.base.1,c.coordinate c.base.2)∈D) : ZeroGraphChart F E where
  base := c.base
  zero_base := c.zero_base
  coordinate := c.coordinate
  reconstruct := c.reconstruct
  domain := D
  ambient := c.ambient
  domain_open := hD
  ambient_open := c.ambient_open
  base_domain := hb
  base_ambient := c.base_ambient
  smooth := c.smooth.mono hDc
  left_inv := c.left_inv
  zero := fun q hq => c.zero q (hDc hq)
  image_ambient := fun q hq => c.image_ambient q (hDc hq)
  complete := c.complete

omit [NormedSpace ℝ Y] in
lemma ZeroGraphChart.reparam_smooth [NormedSpace ℝ Y] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (c : ZeroGraphChart F E) (hc : ContDiffOn ℝ ∞ c.reconstruct c.domain) (e : E ≃L[ℝ] E') :
    ContDiffOn ℝ ∞ (c.reparam e).reconstruct (c.reparam e).domain :=
  hc.comp ((contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)).contDiffOn) (fun _ h => h)

variable [CompleteSpace X] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
local instance szcK : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
local instance szcC : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
local instance szcX : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe
local instance szcY : CompleteSpace pkg.decCodom.X₁ := pkg.decCodom.isTopCompl.isClosed.completeSpace_coe
variable (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
    (hD : HasFDerivAt (fun y => F (t,y)) D x)

lemma parametricSolution_smooth_neighborhood :
    ∃ S : Set (ℝ × pkg.decDom.X₀),IsOpen S ∧ (t,((domCoords pkg) x).2)∈S ∧
      ContDiffOn ℝ ∞ (parametricSolution pkg hF hD) S := by
  obtain ⟨S,hSo,hSt,hSs⟩ := implicitFunction_smooth_neighborhood (parametricEssential_smooth pkg hF)
    (parametricEssential_invertible pkg hF hD)
  refine ⟨S,hSo,hSt,?_⟩
  exact (domCoords pkg).symm.contDiff.comp_contDiffOn (hSs.prodMk contDiffOn_snd)

include hF hD in
lemma surjective_smooth_zero_chart (hs : Surjective D) (hz : F (t,x)=0) :
    ∃ c : ZeroGraphChart F pkg.decDom.X₀,c.base=(t,x) ∧ ContDiffOn ℝ ∞ c.reconstruct c.domain := by
  let P : X →L[ℝ] pkg.decDom.X₀ :=
    (ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp (domCoords pkg).toContinuousLinearMap
  let g : FiniteZeroGerm F t x (Module.finrank ℝ pkg.decDom.X₀) := {
    kernelSpace := pkg.decDom.X₀
    finite_kernel := inferInstance
    dimension := rfl
    coordinate := P
    reconstruct := parametricSolution pkg hF hD
    base := parametricSolution_base pkg hF hD
    smooth := parametricSolution_smooth pkg hF hD
    left_inv := parametricSolution_kernel_coordinate pkg hF hD
    zero := surjective_parametricSolution_zero pkg hF hD hs hz
    complete := parametric_zero_is_solution pkg hF hD hz }
  obtain ⟨c,hb,hp,hr⟩ := g.graphChart hz
  obtain ⟨S,hSo,hSa,hSs⟩ := parametricSolution_smooth_neighborhood pkg hF hD
  have hbase : (c.base.1,c.coordinate c.base.2)∈S := by
    rw [hb,hp]
    exact hSa
  let c' := c.restrict (c.domain∩S) (c.domain_open.inter hSo) inter_subset_left ⟨c.base_domain,hbase⟩
  refine ⟨c',hb,?_⟩
  change ContDiffOn ℝ ∞ c.reconstruct (c.domain∩S)
  rw [hr]
  exact hSs.mono inter_subset_right

include hF hD in
lemma smooth_common_zero_chart [FiniteDimensional ℝ E]
    (hFr : D.IsFredholm) (hs : Surjective D) (hz : F (t,x)=0)
    (hdim : Module.finrank ℝ D.ker=Module.finrank ℝ E) :
    ∃ c : ZeroGraphChart F E,c.base=(t,x) ∧ ContDiffOn ℝ ∞ c.reconstruct c.domain := by
  obtain ⟨pkg⟩ := hFr.nonempty_fredholmPackage
  let := pkg.decDom.finite_X₀
  let e : pkg.decDom.X₀ ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by rwa [←pkg.ker_eq])
  obtain ⟨c,hb,hc⟩ := surjective_smooth_zero_chart pkg hF hD hs hz
  exact ⟨c.reparam e,hb,c.reparam_smooth hc e⟩


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y}

structure SmoothZeroAtlas (F : ℝ × X → Y) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : TopologicalSpace.Opens {v : ℝ × X // F v=0}) where
  chart : s → ZeroGraphChart F E
  base : ∀ x,(chart x).base=x.val.val
  smooth : ∀ x,ContDiffOn ℝ ∞ (chart x).reconstruct (chart x).domain

namespace SmoothZeroAtlas
variable {s : TopologicalSpace.Opens {v : ℝ × X // F v=0}}
  (a : SmoothZeroAtlas F E s)

def localChart (x : s) : OpenPartialHomeomorph s (ℝ × E) :=
  (a.chart x).partialHomeomorph.subtypeRestr ⟨x⟩

lemma localChart_apply (x z : s) : a.localChart x z=(z.val.val.1,(a.chart x).coordinate z.val.val.2) := rfl

lemma localChart_target (x : s) : (a.localChart x).target⊆(a.chart x).domain :=
  (a.chart x).partialHomeomorph.subtypeRestr_target_subset ⟨x⟩

lemma localChart_symm_val (x : s) {q : ℝ × E} (hq : q∈(a.localChart x).target) :
    ((a.localChart x).symm q).val.val=(q.1,(a.chart x).reconstruct q) := by
  have he := (a.chart x).partialHomeomorph.subtypeRestr_symm_apply ⟨x⟩ hq
  change ((a.localChart x).symm q).val=(a.chart x).partialHomeomorph.symm q at he
  rw [he]
  exact (a.chart x).partialHomeomorph_symm_val (a.localChart_target x hq)

@[instance_reducible]
def chartedSpace : ChartedSpace (ℝ × E) s where
  atlas := range a.localChart
  chartAt := a.localChart
  mem_chart_source x := by
    rw [localChart,OpenPartialHomeomorph.subtypeRestr_source]
    change x.val∈(a.chart x).partialHomeomorph.source
    have hb := (a.chart x).base_mem_source
    have he : (⟨(a.chart x).base,(a.chart x).zero_base⟩ : {v : ℝ × X // F v=0})=x.val :=
      Subtype.ext (a.base x)
    rwa [he] at hb
  chart_mem_atlas x := mem_range_self x

lemma transition_smooth (x y : s) :
    ContDiffOn ℝ ∞ ((a.localChart x).symm ≫ₕ a.localChart y)
      ((a.localChart x).symm ≫ₕ a.localChart y).source := by
  have hc : ContDiffOn ℝ ∞ (fun q : ℝ × E => (q.1,(a.chart y).coordinate ((a.chart x).reconstruct q)))
      (a.chart x).domain :=
    contDiffOn_fst.prodMk ((a.chart y).coordinate.contDiff.comp_contDiffOn (a.smooth x))
  apply (hc.mono (fun q hq => a.localChart_target x hq.1)).congr
  intro q hq
  change a.localChart y ((a.localChart x).symm q)=
    (q.1,(a.chart y).coordinate ((a.chart x).reconstruct q))
  rw [a.localChart_apply,a.localChart_symm_val x hq.1]

lemma isManifold : @IsManifold ℝ _ (ℝ × E) _ _ (ℝ × E) _ (𝓘(ℝ,ℝ × E)) ∞ s _ a.chartedSpace := by
  let := a.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using a.transition_smooth x y

end SmoothZeroAtlas

end
section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma timePreserving_linear_det (A : ℝ × E →L[ℝ] E) :
    ((ContinuousLinearMap.fst ℝ ℝ E).prod A).det =
      (A.comp (ContinuousLinearMap.inr ℝ ℝ E)).det := by
  classical
  let b := Module.Free.chooseBasis ℝ ℝ
  let c := Module.Free.chooseBasis ℝ E
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c)
      ((ContinuousLinearMap.fst ℝ ℝ E).prod A).toLinearMap =
      Matrix.fromBlocks (1 : Matrix _ _ ℝ) 0
        (LinearMap.toMatrix b c (A.comp (ContinuousLinearMap.inl ℝ ℝ E)).toLinearMap)
        (LinearMap.toMatrix c c (A.comp (ContinuousLinearMap.inr ℝ ℝ E)).toLinearMap) := by
    ext (i|i) (j|j) <;> simp [LinearMap.toMatrix_apply,Matrix.one_apply,Finsupp.single_apply,eq_comm]
  change LinearMap.det _ = LinearMap.det _
  rw [←LinearMap.det_toMatrix (b.prod c),hm,Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one,one_mul,LinearMap.det_toMatrix]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {F : ℝ × X → Y}

omit [NormedSpace ℝ Y] in
lemma zeroChart_time_transition_det [NormedSpace ℝ Y] (c d : ZeroGraphChart F E) {q : ℝ × E}
    (hq : q∈c.domain) :
    (fderiv ℝ (fun r : ℝ × E => (r.1,d.coordinate (c.reconstruct r))) q).det =
      (d.coordinate.comp (c.spatialDerivative q)).det := by
  have hc := (c.smooth.contDiffAt (c.domain_open.mem_nhds hq)).differentiableAt (by norm_num)
  have hd := (hasFDerivAt_fst (p := q)).prodMk (d.coordinate.hasFDerivAt.comp q hc.hasFDerivAt)
  simp only [Function.comp_def] at hd
  rw [hd.fderiv,timePreserving_linear_det]
  rfl


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)

include fr in
lemma StabilizedKernelFrame.smooth_zero_chart (hF : ContDiff ℝ ∞ F)
    {t : ℝ} {x : X} {e : E} (hv : (t,x)∈V)
    (hs : Surjective ((pathSpatialDerivative F (t,x)).coprod E.subtypeL))
    (hz : finiteTargetAugment F E (t,(x,e))=0) :
    ∃ c : ZeroGraphChart (finiteTargetAugment F E) E,
      c.base=(t,(x,e)) ∧ ContDiffOn ℝ ∞ c.reconstruct c.domain := by
  let A := (pathSpatialDerivative F (t,x)).coprod E.subtypeL
  have hd : HasFDerivAt (fun w : X × E => finiteTargetAugment F E (t,w)) A (x,e) := by
    have hsl : ContDiff ℝ ∞ (fun w : X × E => finiteTargetAugment F E (t,w)) :=
      (finiteTargetAugment_smooth hF E).comp (contDiff_const.prodMk contDiff_id)
    have h := (hsl.differentiable (by simp) (x,e)).hasFDerivAt
    rwa [finiteTargetAugment_spatial_derivative hF E t x e] at h
  exact smooth_common_zero_chart (finiteTargetAugment_smooth hF E) hd
    (fr.fredholm hv hs) hs hz (fr.kernelEquiv hv).finrank_eq.symm


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)}

def framedZeroOpen (F : ℝ × X → Y) (E : Submodule ℝ Y)
    (V : Set (ℝ × X)) (hV : IsOpen V) :
    TopologicalSpace.Opens {v : ℝ × (X × E) // finiteTargetAugment F E v=0} :=
  ⟨{v | (v.val.1,v.val.2.1)∈V},hV.preimage
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)))⟩

def StabilizedKernelFrame.smoothZeroAtlas (fr : StabilizedKernelFrame F E V)
    (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
    (hs : ∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) :
    SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV) := by
  classical
  have hc (v : framedZeroOpen F E V hV) :=
    fr.smooth_zero_chart hF v.property (hs _ v.property) v.val.property
  exact {
    chart := fun v => (hc v).choose
    base := fun v => (hc v).choose_spec.1
    smooth := fun v => (hc v).choose_spec.2 }

theorem ProperIndexZeroPath.smooth_stabilized_moduli
    {U : Set X} (h : ProperIndexZeroPath F U) :
    ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
      ∃ V : Set (ℝ × X),∃ hV : IsOpen V,
        ∃ _ : SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV),
          (∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →(t,x)∈V) ∧
          ∃ _ : StabilizedKernelFrame F E V,
            ∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL) := by
  obtain ⟨K,hK,hKU,h0K,hZ,E,hE,V,hV,hKV,hs,⟨fr⟩⟩ := h.stabilized_kernel_frame
  let := hE
  refine ⟨E,hE,V,hV,fr.smoothZeroAtlas h.smooth hV hs,?_,fr,hs⟩
  intro t ht x hx hz
  exact hKV ⟨ht,hZ t ht x hx hz⟩


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
  (a : SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV))

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedLocalChart_V [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E]
    (x : framedZeroOpen F E V hV) {q : ℝ × E}
    (hq : q∈(a.localChart x).target) : (q.1,((a.chart x).reconstruct q).1)∈V := by
  have hv := ((a.localChart x).symm q).property
  change (((a.localChart x).symm q).val.val.1,((a.localChart x).symm q).val.val.2.1)∈V at hv
  rwa [a.localChart_symm_val x hq] at hv

include hF in
lemma framedLocalChart_signed_transition (x y : framedZeroOpen F E V hV)
    {q : ℝ × E} (hq : q∈((a.localChart x).symm ≫ₕ a.localChart y).source) :
    Real.sign (framedChartJacobian fr (a.chart x) q).det *
      (fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det =
    Real.sign (framedChartJacobian fr (a.chart y) (a.localChart y ((a.localChart x).symm q))).det *
      |(fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det| := by
  have hqx := a.localChart_target x hq.1
  have hh : ((a.localChart x).symm q).val∈(a.chart y).partialHomeomorph.source := by
    simpa only [OpenPartialHomeomorph.symm_symm,Set.mem_preimage,SmoothZeroAtlas.localChart,
      OpenPartialHomeomorph.subtypeRestr_source] using hq.2
  change ((a.localChart x).symm q).val.val∈(a.chart y).ambient ∧
    (((a.localChart x).symm q).val.val.1,(a.chart y).coordinate ((a.localChart x).symm q).val.val.2)∈
      (a.chart y).domain at hh
  rw [a.localChart_symm_val x hq.1] at hh
  have he : (a.localChart y ∘ (a.localChart x).symm) =ᶠ[𝓝 q]
      (fun r => (r.1,(a.chart y).coordinate ((a.chart x).reconstruct r))) := by
    filter_upwards [((a.localChart x).symm ≫ₕ a.localChart y).open_source.mem_nhds hq] with r hr
    change a.localChart y ((a.localChart x).symm r)=_
    rw [a.localChart_apply,a.localChart_symm_val x hr.1]
  rw [he.fderiv_eq,zeroChart_time_transition_det _ _ hqx]
  rw [a.localChart_apply,a.localChart_symm_val x hq.1]
  exact framedChart_transition_signed_det fr (a.chart x) (a.chart y) hF hqx
    (framedLocalChart_V hV a x hq.1) hh.1 hh.2

lemma sign_eq_of_mul_pos {r s : ℝ} (h : 0<r*s) : Real.sign r=Real.sign s := by
  rcases mul_pos_iff.mp h with h|h
  · rw [Real.sign_of_pos h.1,Real.sign_of_pos h.2]
  · rw [Real.sign_of_neg h.1,Real.sign_of_neg h.2]

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedLocalChart_base_target [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E]
    (x : framedZeroOpen F E V hV) :
    a.localChart x x∈(a.localChart x).target :=
  (a.localChart x).map_source (a.chartedSpace.mem_chart_source x)

def StabilizedKernelFrame.orientedZeroAtlas :
    Degree.SignedModelAtlas (framedZeroOpen F E V hV) (framedZeroOpen F E V hV) (ℝ × E) := by
  classical
  have ho (x : framedZeroOpen F E V hV) := framedChart_orientation_neighborhood fr (a.chart x) hF hV
    (a.localChart_target x (framedLocalChart_base_target hV a x))
    (framedLocalChart_V hV a x (framedLocalChart_base_target hV a x))
  let O := fun x => (ho x).choose
  have hO (x) := (ho x).choose_spec
  let c := fun x => ((a.localChart x).symm.restrOpen (O x) (hO x).1).symm
  refine {
    chart := c
    cover := ?_
    sign := fun x => Real.sign (framedChartJacobian fr (a.chart x) (a.localChart x x)).det
    sign_sq := ?_
    transition_smooth := ?_
    orientation := ?_ }
  · intro x
    refine ⟨x,?_⟩
    exact ⟨a.chartedSpace.mem_chart_source x,(hO x).2.1⟩
  · intro x
    have hn := framedChartJacobian_det_ne_zero fr (a.chart x) hF
      (a.localChart_target x (framedLocalChart_base_target hV a x))
      (framedLocalChart_V hV a x (framedLocalChart_base_target hV a x))
    rcases Real.sign_apply_eq_of_ne_zero _ hn with h|h <;> rw [h] <;> norm_num
  · intro x y
    apply (a.transition_smooth x y).mono
    intro q hq
    exact ⟨hq.1.1,hq.2.1⟩
  · intro x y q hq
    have hq' : q∈((a.localChart x).symm ≫ₕ a.localChart y).source := ⟨hq.1.1,hq.2.1⟩
    have hx := sign_eq_of_mul_pos ((hO x).2.2.2 q hq.1.2)
    have hy := sign_eq_of_mul_pos ((hO y).2.2.2 (a.localChart y ((a.localChart x).symm q)) hq.2.2)
    change Real.sign (framedChartJacobian fr (a.chart x) (a.localChart x x)).det *
        (fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det =
      Real.sign (framedChartJacobian fr (a.chart y) (a.localChart y y)).det *
        |(fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det|
    rw [←hx,←hy]
    exact framedLocalChart_signed_transition fr hF hV a x y hq'


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
  (a : SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV))

lemma orientedZeroAtlas_chart_apply (x z : framedZeroOpen F E V hV) :
    (fr.orientedZeroAtlas hF hV a).chart x z=a.localChart x z := rfl
lemma orientedZeroAtlas_symm_apply (x : framedZeroOpen F E V hV) (q : ℝ × E) :
    ((fr.orientedZeroAtlas hF hV a).chart x).symm q=(a.localChart x).symm q := rfl
lemma orientedZeroAtlas_target (x : framedZeroOpen F E V hV) :
    ((fr.orientedZeroAtlas hF hV a).chart x).target⊆(a.localChart x).target := by
  intro q hq
  exact hq.1

 def StabilizedKernelFrame.physicalProjection :
    Degree.ModelAtlasSmoothMap (fr.orientedZeroAtlas hF hV a) (ℝ × E) where
  map z := (z.val.val.1,z.val.val.2.2)
  smooth x := by
    have hs : ContDiffOn ℝ ∞ (fun q : ℝ × E => (q.1,((a.chart x).reconstruct q).2))
        (a.chart x).domain := contDiffOn_fst.prodMk (contDiff_snd.comp_contDiffOn (a.smooth x))
    apply (hs.mono (fun q hq => a.localChart_target x (orientedZeroAtlas_target fr hF hV a x hq))).congr
    intro q hq
    change (((a.localChart x).symm q).val.val.1,((a.localChart x).symm q).val.val.2.2)=_
    rw [a.localChart_symm_val x (orientedZeroAtlas_target fr hF hV a x hq)]


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] [NormedSpace ℝ Y] [CompleteSpace Y] in
lemma FiniteZeroGerm.compact_zero_neighborhood [CompleteSpace X] [NormedSpace ℝ Y] [CompleteSpace Y]
    {F : ℝ × X → Y} {t : ℝ} {x : X} {m : ℕ}
    (g : FiniteZeroGerm F t x m) {W : Set (ℝ × X)} (hW : IsOpen W) (hw : (t,x)∈W) :
    ∃ C O : Set (ℝ × X),IsCompact C ∧ C⊆W ∧ C⊆{v | F v=0} ∧
      IsOpen O ∧ (t,x)∈O ∧ ∀ v∈O,F v=0 →v∈C := by
  let : FiniteDimensional ℝ g.kernelSpace := g.finite_kernel
  let a : ℝ × g.kernelSpace := (t,g.coordinate x)
  let ψ : ℝ × g.kernelSpace → ℝ × X := fun v => (v.1,g.reconstruct v)
  let P : ℝ × X → ℝ × g.kernelSpace := fun v => (v.1,g.coordinate v.2)
  have hP : Continuous P := continuous_fst.prodMk (g.coordinate.continuous.comp continuous_snd)
  have hψ : ContDiffAt ℝ ∞ ψ a := contDiffAt_fst.prodMk g.smooth
  have hψa : ψ a=(t,x) := Prod.ext rfl g.base
  have hWa : ∀ᶠ v in 𝓝 a,ψ v∈W := hψ.continuousAt (hψa.symm ▸ hW.mem_nhds hw)
  obtain ⟨S,hS,hψS⟩ := hψ.contDiffOn (m := 0) (by simp) (by simp)
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (inter_mem hS (inter_mem g.zero hWa))
  have hrb : Metric.closedBall a (r/2)⊆Metric.ball a r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  let C := ψ '' Metric.closedBall a (r/2)
  have hC : IsCompact C := (isCompact_closedBall a (r/2)).image_of_continuousOn
    (hψS.continuousOn.mono (fun v hv => (hrS (hrb hv)).1))
  have hCW : C⊆W := by rintro _ ⟨v,hv,rfl⟩; exact (hrS (hrb hv)).2.2
  have hCz : C⊆{v | F v=0} := by rintro _ ⟨v,hv,rfl⟩; exact (hrS (hrb hv)).2.1
  have hnear : ∀ᶠ v in 𝓝 (t,x),F v=0 →v∈C := by
    filter_upwards [g.complete,hP.continuousAt (Metric.ball_mem_nhds a (half_pos hr))] with v hv hp hz
    have he : ψ (P v)=v := Prod.ext rfl (hv hz)
    exact ⟨P v,Metric.ball_subset_closedBall hp,he⟩
  let O := interior {v : ℝ × X | F v=0 →v∈C}
  refine ⟨C,O,hC,hCW,hCz,isOpen_interior,mem_interior_iff_mem_nhds.mpr hnear,?_⟩
  intro v hv hz
  exact interior_subset hv hz

lemma compact_zero_reservoir {F : ℝ × X → Y} {K W : Set (ℝ × X)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K⊆W)
    (hcharts : ∀ v∈K,∃ m,Nonempty (FiniteZeroGerm F v.1 v.2 m)) :
    ∃ C O : Set (ℝ × X),IsCompact C ∧ C⊆W ∧ C⊆{v | F v=0} ∧
      IsOpen O ∧ K⊆O ∧ ∀ v∈O,F v=0 →v∈C := by
  classical
  have hl (v : K) : ∃ C O : Set (ℝ × X),IsCompact C ∧ C⊆W ∧ C⊆{v | F v=0} ∧
      IsOpen O ∧ v.val∈O ∧ ∀ y∈O,F y=0 →y∈C := by
    obtain ⟨m,⟨g⟩⟩ := hcharts v.val v.property
    exact g.compact_zero_neighborhood hW (hKW v.property)
  choose C O hC hCW hCz hO hv hOz using hl
  have hcover : K⊆⋃ v : K,O v := by
    intro v hvK
    exact mem_iUnion.mpr ⟨⟨v,hvK⟩,hv ⟨v,hvK⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover O hO hcover
  refine ⟨⋃ v∈s,C v,⋃ v∈s,O v,s.isCompact_biUnion (fun v _ => hC v),?_,?_,
    isOpen_biUnion (fun v hv => hO v),hs,?_⟩
  · exact iUnion₂_subset (fun v _ => hCW v)
  · exact iUnion₂_subset (fun v _ => hCz v)
  · intro y hy hz
    obtain ⟨v,hv,hy⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨v,hv,hOz v y hy hz⟩


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma compact_zero_isolating_neighborhood {F : ℝ × X → Y} (hF : Continuous F)
    {K W : Set (ℝ × X)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K⊆W)
    (hcharts : ∀ v∈K,∃ m,Nonempty (FiniteZeroGerm F v.1 v.2 m)) :
    ∃ N : Set (ℝ × X),IsOpen N ∧ K⊆N ∧
      IsCompact (closure N ∩ {v | F v=0}) ∧ (closure N ∩ {v | F v=0})⊆W := by
  obtain ⟨C,O,hC,hCW,hCz,hO,hKO,hnear⟩ := compact_zero_reservoir hK hW hKW hcharts
  obtain ⟨r,hr,hrO⟩ := hK.exists_cthickening_subset_open hO hKO
  let N := Metric.thickening r K
  have hcl : closure N⊆O :=
    (closure_minimal (Metric.thickening_subset_cthickening r K) Metric.isClosed_cthickening).trans hrO
  have hres : (closure N ∩ {v | F v=0})⊆C := fun v hv => hnear v (hcl hv.1) hv.2
  refine ⟨N,Metric.isOpen_thickening,Metric.self_subset_thickening hr K,?_,hres.trans hCW⟩
  exact hC.of_isClosed_subset (isClosed_closure.inter (isClosed_eq hF continuous_const)) hres

structure IsolatingStabilization (F : ℝ × X → Y) (U : Set X)
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (N : Set (ℝ × (X × E))) : Prop where
  isOpen : IsOpen N
  contains : ∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →(t,(x,0))∈N
  compact : IsCompact (closure N ∩ {v | finiteTargetAugment F E v=0})
  domain : ∀ v∈closure N,finiteTargetAugment F E v=0 →v.2.1∈U
  germs : ∀ v∈closure N,v.1∈Icc (0:ℝ) 1 →finiteTargetAugment F E v=0 →
    Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 (Module.finrank ℝ E))

lemma ProperIndexZeroPath.isolating_stabilization {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
      ∃ N : Set (ℝ × (X × E)),IsolatingStabilization F U E N := by
  obtain ⟨E,hE,V,hV,hZ,hcharts⟩ := h.stabilized_zero_germs
  let := hE
  let B : ℝ × X → ℝ × (X × E) := fun v => (v.1,(v.2,0))
  have hB : Continuous B := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let K := B '' {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  let W : Set (ℝ × (X × E)) := {v | v.2.1∈U ∧ (v.1,v.2.1)∈V}
  have hK : IsCompact K := h.zeroSet_compact.image hB
  have hW : IsOpen W :=
    (h.domain_open.preimage (continuous_fst.comp continuous_snd)).inter
      (hV.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
  have hKW : K⊆W := by
    rintro _ ⟨⟨t,x⟩,hv,rfl⟩
    exact ⟨hv.2.1,hZ hv⟩
  have hg : ∀ v∈K,∃ m,Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 m) := by
    rintro _ ⟨⟨t,x⟩,hv,rfl⟩
    exact ⟨Module.finrank ℝ E,hcharts t hv.1 x hv.2.1 (hZ hv) 0 (by
      change F (t,x)+(0:Y)=0
      simpa only [add_zero] using hv.2.2)⟩
  obtain ⟨N,hN,hKN,hNc,hNW⟩ := compact_zero_isolating_neighborhood
    (finiteTargetAugment_smooth h.smooth E).continuous hK hW hKW hg
  refine ⟨E,hE,N,hN,?_,hNc,?_,?_⟩
  · intro t ht x hx hz
    exact hKN ⟨(t,x),⟨ht,hx,hz⟩,rfl⟩
  · intro v hv hz
    exact (hNW ⟨hv,hz⟩).1
  · intro v hv ht hz
    have hw := hNW ⟨hv,hz⟩
    exact hcharts v.1 ht v.2.1 hw.1 hw.2 v.2.2 hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {U : Set X} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {N : Set (ℝ × (X × E))}

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_target_boundary_avoid [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization F U E N) :
    ∃ δ : ℝ,0<δ ∧ ∀ v∈frontier N,v.1∈Icc (0:ℝ) 1 →‖v.2.2‖≤δ →finiteTargetAugment F E v≠0 := by
  let C := (closure N ∩ {v | finiteTargetAugment F E v=0}) ∩
    (frontier N ∩ {v | v.1∈Icc (0:ℝ) 1})
  have hC : IsCompact C := h.compact.inter_right
    (isClosed_frontier.inter (isClosed_Icc.preimage continuous_fst))
  let B := (fun v : ℝ × (X × E) => v.2.2) '' C
  have hB : IsCompact B := hC.image (continuous_snd.comp continuous_snd)
  have hB0 : (0:E)∉B := by
    rintro ⟨⟨t,x,e⟩,⟨⟨hcl,hz⟩,hf,ht⟩,he⟩
    have he0 : e=0 := he
    subst e
    have hx := h.domain (t,(x,0)) hcl hz
    have hz' : F (t,x)=0 := by simpa only [Set.mem_ofPred_eq,finiteTargetAugment,ZeroMemClass.coe_zero,add_zero] using hz
    have hn := h.contains t ht x hx hz'
    rw [h.isOpen.frontier_eq] at hf
    exact hf.2 hn
  obtain ⟨r,hr,hrB⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl 0 hB0
  refine ⟨r/2,half_pos hr,?_⟩
  intro v hv ht he hz
  have hm : v.2.2∈B := ⟨v,⟨⟨frontier_subset_closure hv,hz⟩,hv,ht⟩,rfl⟩
  apply hrB (show v.2.2∈Metric.ball 0 r from ?_) hm
  simpa only [Metric.mem_ball,dist_zero_right] using he.trans_lt (half_lt_self hr)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_target_endpoint_avoid [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization F U E N) (hn : ∀ x∈U,F (1,x)≠0) :
    ∃ δ : ℝ,0<δ ∧ ∀ x : X,∀ e : E,(1,(x,e))∈closure N →‖e‖≤δ →
      finiteTargetAugment F E (1,(x,e))≠0 := by
  let C := (closure N ∩ {v | finiteTargetAugment F E v=0}) ∩ {v | v.1=1}
  have hC : IsCompact C := h.compact.inter_right (isClosed_eq continuous_fst continuous_const)
  let B := (fun v : ℝ × (X × E) => v.2.2) '' C
  have hB : IsCompact B := hC.image (continuous_snd.comp continuous_snd)
  have hB0 : (0:E)∉B := by
    rintro ⟨⟨t,x,e⟩,⟨⟨hcl,hz⟩,ht⟩,he⟩
    have ht1 : t=1 := ht
    have he0 : e=0 := he
    subst t e
    have hx := h.domain (1,(x,0)) hcl hz
    have hz' : F (1,x)=0 := by simpa only [Set.mem_ofPred_eq,finiteTargetAugment,ZeroMemClass.coe_zero,add_zero] using hz
    exact hn x hx hz'
  obtain ⟨r,hr,hrB⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl 0 hB0
  refine ⟨r/2,half_pos hr,?_⟩
  intro x e hx he hz
  apply hrB (show e∈Metric.ball 0 r from ?_) ⟨(1,(x,e)),⟨⟨hx,hz⟩,rfl⟩,rfl⟩
  simpa only [Metric.mem_ball,dist_zero_right] using he.trans_lt (half_lt_self hr)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_initial_graph [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization F U E N)
    (hp : ProperIndexZeroPath F U) :
    ∃ L : X ≃L[ℝ] Y, (∀ x,F (0,x)=L x) ∧ ∃ δ : ℝ,0<δ ∧
      ∀ e : E,‖e‖≤δ →(0,(-L.symm (e:Y),e))∈N ∧
        finiteTargetAugment F E (0,(-L.symm (e:Y),e))=0 := by
  obtain ⟨L,hL⟩ := hp.initial
  let ψ : E → ℝ × (X × E) := fun e => (0,(-L.symm (e:Y),e))
  have hψ : Continuous ψ := continuous_const.prodMk
    ((L.symm.continuous.comp E.subtypeL.continuous).neg.prodMk continuous_id)
  have h0N : ψ 0∈N := by
    have hz : F (0,0)=0 := (hL 0).trans (map_zero L)
    simpa only [ψ,ZeroMemClass.coe_zero,map_zero,neg_zero] using
      h.contains 0 (by constructor <;> norm_num) 0 hp.origin_mem hz
  obtain ⟨r,hr,hrN⟩ := Metric.mem_nhds_iff.mp (hψ.continuousAt (h.isOpen.mem_nhds h0N))
  refine ⟨L,hL,r/2,half_pos hr,?_⟩
  intro e he
  refine ⟨hrN (show e∈Metric.ball 0 r from ?_),?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right] using he.trans_lt (half_lt_self hr)
  · change F (0,-L.symm (e:Y))+(e:Y)=0
    rw [hL,map_neg,L.apply_symm_apply,neg_add_cancel]


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem ProperIndexZeroPath.framed_isolating_stabilization
    {F : ℝ × X → Y} {U : Set X} (h : ProperIndexZeroPath F U) :
    ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
      ∃ V : Set (ℝ × X),IsOpen V ∧
        ∃ _ : StabilizedKernelFrame F E V,
          ∃ N : Set (ℝ × (X × E)),IsolatingStabilization F U E N ∧
            (∀ v∈closure N,finiteTargetAugment F E v=0 →(v.1,v.2.1)∈V) ∧
            (∀ v∈closure N,finiteTargetAugment F E v=0 →
              ∃ c : ZeroGraphChart (finiteTargetAugment F E) E,c.base=v) := by
  obtain ⟨K,hK,hKU,h0K,hZ,E,hE,V,hVo,hKV,hs,⟨fr⟩⟩ := h.stabilized_kernel_frame
  let := hE
  let B : ℝ × X → ℝ × (X × E) := fun v => (v.1,(v.2,0))
  have hB : Continuous B := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let Z := B '' {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  let W : Set (ℝ × (X × E)) := {v | v.2.1∈U ∧ (v.1,v.2.1)∈V}
  have hZc : IsCompact Z := h.zeroSet_compact.image hB
  have hWo : IsOpen W := (h.domain_open.preimage (continuous_fst.comp continuous_snd)).inter
    (hVo.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
  have hZW : Z⊆W := by
    rintro _ ⟨⟨t,x⟩,hv,rfl⟩
    exact ⟨hv.2.1,hKV ⟨hv.1,hZ t hv.1 x hv.2.1 hv.2.2⟩⟩
  have hg (v : ℝ × (X × E)) (hv : v∈W) (hz : finiteTargetAugment F E v=0) :
      Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 (Module.finrank ℝ E)) :=
    fr.zero_germ h.smooth hv.2 (hs _ hv.2) hz
  have hcharts : ∀ v∈Z,∃ m,Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 m) := by
    intro v hv
    refine ⟨Module.finrank ℝ E,hg v (hZW hv) ?_⟩
    rcases hv with ⟨⟨t,x⟩,hv,rfl⟩
    simpa only [B,finiteTargetAugment,ZeroMemClass.coe_zero,add_zero] using hv.2.2
  obtain ⟨N,hNo,hZN,hNc,hNW⟩ := compact_zero_isolating_neighborhood
    (finiteTargetAugment_smooth h.smooth E).continuous hZc hWo hZW hcharts
  refine ⟨E,hE,V,hVo,fr,N,⟨hNo,?_,hNc,?_,?_⟩,?_,?_⟩
  · intro t ht x hx hz
    exact hZN ⟨(t,x),⟨ht,hx,hz⟩,rfl⟩
  · intro v hv hz
    exact (hNW ⟨hv,hz⟩).1
  · intro v hv ht hz
    exact hg v (hNW ⟨hv,hz⟩) hz
  · intro v hv hz
    exact (hNW ⟨hv,hz⟩).2
  · intro v hv hz
    obtain ⟨g⟩ := hg v (hNW ⟨hv,hz⟩) hz
    exact g.common_graphChart hz rfl


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
