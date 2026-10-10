import Mathlib
import OAI.Geometry.BallPacking.Fredholm.ProjectionTimeGrid

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ZeroGraphChart (F : ℝ × X → Y) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  base : ℝ × X
  zero_base : F base=0
  coordinate : X →L[ℝ] E
  reconstruct : ℝ × E → X
  domain : Set (ℝ × E)
  ambient : Set (ℝ × X)
  domain_open : IsOpen domain
  ambient_open : IsOpen ambient
  base_domain : (base.1,coordinate base.2)∈domain
  base_ambient : base∈ambient
  smooth : ContDiffOn ℝ 2 reconstruct domain
  left_inv : ∀ v,coordinate (reconstruct v)=v.2
  zero : ∀ v∈domain,F (v.1,reconstruct v)=0
  image_ambient : ∀ v∈domain,(v.1,reconstruct v)∈ambient
  complete : ∀ v∈ambient,F v=0 → reconstruct (v.1,coordinate v.2)=v.2

omit [NormedSpace ℝ Y] in
lemma FiniteZeroGerm.graphChart [NormedSpace ℝ Y] {F : ℝ × X → Y} {t : ℝ} {x : X} {m : ℕ}
    (g : FiniteZeroGerm F t x m) (hz : F (t,x)=0) :
    ∃ c : ZeroGraphChart F g.kernelSpace,c.base=(t,x) ∧ c.coordinate=g.coordinate ∧ c.reconstruct=g.reconstruct := by
  let a : ℝ × g.kernelSpace := (t,g.coordinate x)
  let ψ : ℝ × g.kernelSpace → ℝ × X := fun q => (q.1,g.reconstruct q)
  have hψ : ContDiffAt ℝ ∞ ψ a := contDiffAt_fst.prodMk g.smooth
  obtain ⟨O,hOc,hOo,hOx⟩ := mem_nhds_iff.mp g.complete
  obtain ⟨S,hS,hSs⟩ := g.smooth.contDiffOn (m := 2) (WithTop.coe_le_coe.mpr le_top) (by norm_num)
  have hψa : ψ a=(t,x) := Prod.ext rfl g.base
  have hψO : ∀ᶠ q in 𝓝 a,ψ q∈O := hψ.continuousAt (hψa.symm ▸ hOo.mem_nhds hOx)
  obtain ⟨D,hD,hDo,hDa⟩ := mem_nhds_iff.mp (inter_mem hS (inter_mem g.zero hψO))
  refine ⟨{
    base := (t,x)
    zero_base := hz
    coordinate := g.coordinate
    reconstruct := g.reconstruct
    domain := D
    ambient := O
    domain_open := hDo
    ambient_open := hOo
    base_domain := hDa
    base_ambient := hOx
    smooth := hSs.mono (fun q hq => (hD hq).1)
    left_inv := g.left_inv
    zero := fun q hq => (hD hq).2.1
    image_ambient := fun q hq => (hD hq).2.2
    complete := fun v hv => hOc hv },rfl,rfl,rfl⟩

namespace ZeroGraphChart
variable {F : ℝ × X → Y} (c : ZeroGraphChart F E)

def inverse (q : ℝ × E) : {v : ℝ × X // F v=0} := by
  classical
  exact if hq : q∈c.domain then ⟨(q.1,c.reconstruct q),c.zero q hq⟩ else ⟨c.base,c.zero_base⟩

omit [NormedSpace ℝ Y] in
lemma inverse_val [NormedSpace ℝ Y] {q : ℝ × E} (hq : q∈c.domain) : (c.inverse q).val=(q.1,c.reconstruct q) := by
  rw [inverse,dite_eq_left hq]

lemma inverse_continuousOn : ContinuousOn c.inverse c.domain := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_induced_rng.mpr
  have hc : Continuous (fun q : c.domain => (q.val.1,c.reconstruct q.val)) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (continuousOn_iff_continuous_domRestrict.mp c.smooth.continuousOn)
  convert hc using 1
  funext q
  exact c.inverse_val q.property

def partialHomeomorph : OpenPartialHomeomorph {v : ℝ × X // F v=0} (ℝ × E) where
  toFun v := (v.val.1,c.coordinate v.val.2)
  invFun := c.inverse
  source := {v | v.val∈c.ambient ∧ (v.val.1,c.coordinate v.val.2)∈c.domain}
  target := c.domain
  map_source' v hv := hv.2
  map_target' q hq := by
    change (c.inverse q).val∈c.ambient ∧ ((c.inverse q).val.1,c.coordinate (c.inverse q).val.2)∈c.domain
    rw [c.inverse_val hq]
    exact ⟨c.image_ambient q hq,by simpa only [c.left_inv,Prod.mk.eta] using hq⟩
  left_inv' v hv := by
    apply Subtype.ext
    rw [c.inverse_val hv.2]
    exact Prod.ext rfl (c.complete v.val hv.1 v.property)
  right_inv' q hq := by
    rw [c.inverse_val hq]
    exact Prod.ext rfl (c.left_inv q)
  continuousOn_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (c.coordinate.continuous.comp (continuous_snd.comp continuous_subtype_val))).continuousOn
  continuousOn_invFun := c.inverse_continuousOn
  open_source := (c.ambient_open.preimage continuous_subtype_val).inter
    (c.domain_open.preimage ((continuous_fst.comp continuous_subtype_val).prodMk
      (c.coordinate.continuous.comp (continuous_snd.comp continuous_subtype_val))))
  open_target := c.domain_open

lemma base_mem_source : (⟨c.base,c.zero_base⟩ : {v : ℝ × X // F v=0})∈c.partialHomeomorph.source :=
  ⟨c.base_ambient,c.base_domain⟩

lemma partialHomeomorph_apply (v : {v : ℝ × X // F v=0}) :
    c.partialHomeomorph v=(v.val.1,c.coordinate v.val.2) := rfl

lemma partialHomeomorph_symm_val {q : ℝ × E} (hq : q∈c.partialHomeomorph.target) :
    (c.partialHomeomorph.symm q).val=(q.1,c.reconstruct q) := c.inverse_val hq

omit [NormedSpace ℝ Y] in
lemma transition_smooth [NormedSpace ℝ Y] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (d : ZeroGraphChart F E') :
    ContDiffOn ℝ 2 (fun q : ℝ × E => (q.1,d.coordinate (c.reconstruct q))) c.domain :=
  contDiffOn_fst.prodMk (d.coordinate.contDiff.comp_contDiffOn c.smooth)

lemma transition_eq {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (d : ZeroGraphChart F E') {q : ℝ × E} (hq : q∈c.domain) :
    d.partialHomeomorph (c.partialHomeomorph.symm q)=(q.1,d.coordinate (c.reconstruct q)) := by
  rw [d.partialHomeomorph_apply,c.partialHomeomorph_symm_val hq]

end ZeroGraphChart

end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)

def StabilizedKernelFrame.kernelEquiv {v : ℝ × X} (hv : v∈V) :
    E ≃ₗ[ℝ] ((pathSpatialDerivative F v).coprod E.subtypeL).ker := by
  let A := (pathSpatialDerivative F v).coprod E.subtypeL
  let B : E →ₗ[ℝ] A.ker := (fr.frame v).toLinearMap.codRestrict A.ker (fr.kernel v hv)
  refine LinearEquiv.ofBijective B ⟨?_,?_⟩
  · intro e f he
    have hh := congrArg (fun z : A.ker => fr.coordinate v z.val) he
    change fr.coordinate v (fr.frame v e)=fr.coordinate v (fr.frame v f) at hh
    simpa only [fr.left_inv v hv] using hh
  · intro w
    refine ⟨fr.coordinate v w.val,?_⟩
    apply Subtype.ext
    exact fr.right_inv v hv w.val w.property

include fr in
lemma StabilizedKernelFrame.fredholm {v : ℝ × X} (hv : v∈V)
    (hs : Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) :
    ((pathSpatialDerivative F v).coprod E.subtypeL).IsFredholm := by
  let A := (pathSpatialDerivative F v).coprod E.subtypeL
  let e := fr.kernelEquiv hv
  let : FiniteDimensional ℝ A.ker := Module.Finite.equiv e
  have htop : A.range=⊤ := LinearMap.range_eq_top.mpr hs
  refine ⟨(A.isOpenMap hs).isStrictMap A.continuous,?_,inferInstance,?_,?_⟩
  · rw [htop]
    exact isClosed_univ
  · rw [htop]
    infer_instance
  · exact Submodule.ClosedComplemented.of_finiteDimensional _

include fr in
lemma StabilizedKernelFrame.zero_germ (hF : ContDiff ℝ ∞ F)
    {t : ℝ} {x : X} {e : E} (hv : (t,x)∈V)
    (hs : Surjective ((pathSpatialDerivative F (t,x)).coprod E.subtypeL))
    (hz : finiteTargetAugment F E (t,(x,e))=0) :
    Nonempty (FiniteZeroGerm (finiteTargetAugment F E) t (x,e) (Module.finrank ℝ E)) := by
  let A := (pathSpatialDerivative F (t,x)).coprod E.subtypeL
  have hd : HasFDerivAt (fun w : X × E => finiteTargetAugment F E (t,w)) A (x,e) := by
    have hsl : ContDiff ℝ ∞ (fun w : X × E => finiteTargetAugment F E (t,w)) :=
      (finiteTargetAugment_smooth hF E).comp (contDiff_const.prodMk contDiff_id)
    have h := (hsl.differentiable (by simp) (x,e)).hasFDerivAt
    rwa [finiteTargetAugment_spatial_derivative hF E t x e] at h
  have hdim : Module.finrank ℝ E=Module.finrank ℝ A.ker := (fr.kernelEquiv hv).finrank_eq
  rw [hdim]
  exact finiteZeroGerm_of_surjective (finiteTargetAugment_smooth hF E) hd (fr.fredholm hv hs) hs hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E E' : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {F : ℝ × X → Y}

def ZeroGraphChart.reparam (c : ZeroGraphChart F E) (e : E ≃L[ℝ] E') : ZeroGraphChart F E' where
  base := c.base
  zero_base := c.zero_base
  coordinate := e.toContinuousLinearMap.comp c.coordinate
  reconstruct := fun q => c.reconstruct (q.1,e.symm q.2)
  domain := (fun q : ℝ × E' => (q.1,e.symm q.2)) ⁻¹' c.domain
  ambient := c.ambient
  domain_open := c.domain_open.preimage (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
  ambient_open := c.ambient_open
  base_domain := by
    change (c.base.1,e.symm (e (c.coordinate c.base.2)))∈c.domain
    simpa only [e.symm_apply_apply] using c.base_domain
  base_ambient := c.base_ambient
  smooth := c.smooth.comp (contDiffOn_fst.prodMk (e.symm.contDiff.contDiffOn.comp contDiffOn_snd (mapsTo_univ _ _)))
    (fun _ h => h)
  left_inv := by
    intro q
    change e (c.coordinate (c.reconstruct (q.1,e.symm q.2)))=q.2
    rw [c.left_inv,e.apply_symm_apply]
  zero := by
    intro q hq
    exact c.zero (q.1,e.symm q.2) hq
  image_ambient := fun q hq => c.image_ambient (q.1,e.symm q.2) hq
  complete := by
    intro v hv hz
    change c.reconstruct (v.1,e.symm (e (c.coordinate v.2)))=v.2
    rw [e.symm_apply_apply]
    exact c.complete v hv hz

lemma FiniteZeroGerm.common_graphChart {t : ℝ} {x : X} {m : ℕ}
    (g : FiniteZeroGerm F t x m) (hz : F (t,x)=0)
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E=m) :
    ∃ c : ZeroGraphChart F E,c.base=(t,x) := by
  let := g.finite_kernel
  let e : g.kernelSpace ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (g.dimension.trans hd.symm)
  obtain ⟨c,hb,hp,hr⟩ := g.graphChart hz
  exact ⟨c.reparam e,hb⟩


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y} (c : ZeroGraphChart F E)

def ZeroGraphChart.spatialDerivative (q : ℝ × E) : E →L[ℝ] X :=
  (fderiv ℝ c.reconstruct q).comp (ContinuousLinearMap.inr ℝ ℝ E)

omit [NormedSpace ℝ Y] in
lemma ZeroGraphChart.spatialDerivative_continuous [NormedSpace ℝ Y] : ContinuousOn c.spatialDerivative c.domain := by
  exact (c.smooth.continuousOn_fderiv_of_isOpen c.domain_open (by norm_num)).clm_comp continuousOn_const

omit [NormedSpace ℝ Y] in
lemma ZeroGraphChart.hasSpatialDerivative [NormedSpace ℝ Y] {q : ℝ × E} (hq : q∈c.domain) :
    HasFDerivAt (fun e => c.reconstruct (q.1,e)) (c.spatialDerivative q) q.2 := by
  have hd : DifferentiableAt ℝ c.reconstruct q :=
    (c.smooth.contDiffAt (c.domain_open.mem_nhds hq)).differentiableAt (by norm_num)
  exact hd.hasFDerivAt.comp q.2 ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2))

lemma ZeroGraphChart.spatialDerivative_coordinate {q : ℝ × E} (hq : q∈c.domain) (e : E) :
    c.coordinate (c.spatialDerivative q e)=e := by
  have hd := c.coordinate.hasFDerivAt.comp q.2 (c.hasSpatialDerivative hq)
  have he : (fun z => c.coordinate (c.reconstruct (q.1,z)))=id := funext (fun z => c.left_inv _)
  simp only [Function.comp_def] at hd
  rw [he] at hd
  have hh := hd.unique (hasFDerivAt_id q.2)
  exact congrArg (fun A : E →L[ℝ] E => A e) hh

lemma ZeroGraphChart.spatialDerivative_injective {q : ℝ × E} (hq : q∈c.domain) :
    Injective (c.spatialDerivative q) := by
  intro e f he
  have hh := congrArg c.coordinate he
  simpa only [c.spatialDerivative_coordinate hq] using hh

variable [CompleteSpace X] [CompleteSpace Y]

lemma ZeroGraphChart.spatialDerivative_kernel (hF : ContDiff ℝ ∞ F)
    {q : ℝ × E} (hq : q∈c.domain) (e : E) :
    pathSpatialDerivative F (q.1,c.reconstruct q) (c.spatialDerivative q e)=0 := by
  have hsl : ContDiff ℝ ∞ (fun x => F (q.1,x)) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hd := (hsl.differentiable (by simp) (c.reconstruct q)).hasFDerivAt.comp q.2
    (c.hasSpatialDerivative hq)
  have he : (fun z => F (q.1,c.reconstruct (q.1,z))) =ᶠ[𝓝 q.2] (fun _ => 0) := by
    have hm : ∀ᶠ z in 𝓝 q.2,(q.1,z)∈c.domain :=
      (continuousAt_const.prodMk continuousAt_id) (c.domain_open.mem_nhds hq)
    filter_upwards [hm] with z hz
    exact c.zero (q.1,z) hz
  have hz := hd.fderiv.symm.trans (he.fderiv_eq)
  simp only [fderiv_fun_const] at hz
  rw [pathSpatialDerivative_eq hF]
  exact congrArg (fun A : E →L[ℝ] Y => A e) hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (c : ZeroGraphChart (finiteTargetAugment F E) E)

def framedChartJacobian (q : ℝ × E) : E →L[ℝ] E :=
  (fr.coordinate (q.1,(c.reconstruct q).1)).comp (c.spatialDerivative q)

lemma framedChartJacobian_injective (hF : ContDiff ℝ ∞ F) {q : ℝ × E}
    (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    Injective (framedChartJacobian fr c q) := by
  have hk (e : E) : ((pathSpatialDerivative F (q.1,(c.reconstruct q).1)).coprod E.subtypeL)
      (c.spatialDerivative q e)=0 := by
    have hh := c.spatialDerivative_kernel (finiteTargetAugment_smooth hF E) hq e
    rw [pathSpatialDerivative_eq (finiteTargetAugment_smooth hF E),finiteTargetAugment_spatial_derivative hF] at hh
    exact hh
  intro e f he
  apply c.spatialDerivative_injective hq
  have hh := congrArg (fr.frame (q.1,(c.reconstruct q).1)) he
  exact (fr.right_inv _ hv _ (hk e)).symm.trans (hh.trans (fr.right_inv _ hv _ (hk f)))

lemma framedChartJacobian_bijective (hF : ContDiff ℝ ∞ F) {q : ℝ × E}
    (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    Bijective (framedChartJacobian fr c q) :=
  ⟨framedChartJacobian_injective fr c hF hq hv,
    (LinearMap.injective_iff_surjective).mp (framedChartJacobian_injective fr c hF hq hv)⟩

lemma framedChartJacobian_det_ne_zero (hF : ContDiff ℝ ∞ F) {q : ℝ × E}
    (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    (framedChartJacobian fr c q).det≠0 := by
  let A := LinearEquiv.ofBijective (framedChartJacobian fr c q).toLinearMap
    (framedChartJacobian_bijective fr c hF hq hv)
  exact A.isUnit_det'.ne_zero

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedChartJacobian_continuous [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] :
    ContinuousOn (framedChartJacobian fr c) (c.domain ∩ {q | (q.1,(c.reconstruct q).1)∈V}) := by
  apply ContinuousOn.clm_comp
  · exact fr.coordinate_continuous.comp
      ((continuousOn_fst.mono inter_subset_left).prodMk
        (continuous_fst.continuousOn.comp (c.smooth.continuousOn.mono inter_subset_left)
          (mapsTo_univ _ _))) (fun _ h => h.2)
  · exact c.spatialDerivative_continuous.mono inter_subset_left

lemma framedChart_orientation_neighborhood (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
    {q : ℝ × E} (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    ∃ O : Set (ℝ × E),IsOpen O ∧ q∈O ∧ O⊆c.domain ∧
      ∀ r∈O,0<(framedChartJacobian fr c r).det*(framedChartJacobian fr c q).det := by
  have hn := framedChartJacobian_det_ne_zero fr c hF hq hv
  have hm : c.domain ∩ {r | (r.1,(c.reconstruct r).1)∈V}∈𝓝 q := by
    apply inter_mem (c.domain_open.mem_nhds hq)
    exact (continuousAt_fst.prodMk
      (continuous_fst.continuousAt.comp (c.smooth.contDiffAt (c.domain_open.mem_nhds hq)).continuousAt))
        (hV.mem_nhds hv)
  have hc : ContinuousAt (fun r => (framedChartJacobian fr c r).det) q :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((framedChartJacobian_continuous fr c q ⟨hq,hv⟩).continuousAt hm)
  have hp : ∀ᶠ r in 𝓝 q,0<(framedChartJacobian fr c r).det*(framedChartJacobian fr c q).det :=
    (hc.mul_const _).eventually (lt_mem_nhds (mul_self_pos.mpr hn))
  obtain ⟨O,hO,hOo,hOq⟩ := mem_nhds_iff.mp (inter_mem (c.domain_open.mem_nhds hq) hp)
  exact ⟨O,hOo,hOq,fun _ h => (hO h).1,fun _ h => (hO h).2⟩


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y} (c d : ZeroGraphChart F E)

lemma zeroChart_transition_derivative {q : ℝ × E} (hq : q∈c.domain)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    (d.spatialDerivative (q.1,d.coordinate (c.reconstruct q))).comp
      (d.coordinate.comp (c.spatialDerivative q))=c.spatialDerivative q := by
  have hc := c.hasSpatialDerivative hq
  have hd := (d.hasSpatialDerivative hr).comp q.2 (d.coordinate.hasFDerivAt.comp q.2 hc)
  have he : (fun z => d.reconstruct (q.1,d.coordinate (c.reconstruct (q.1,z)))) =ᶠ[𝓝 q.2]
      (fun z => c.reconstruct (q.1,z)) := by
    have hm : ∀ᶠ z in 𝓝 q.2,(q.1,z)∈c.domain :=
      (continuousAt_const.prodMk continuousAt_id) (c.domain_open.mem_nhds hq)
    have hn : ∀ᶠ z in 𝓝 q.2,(q.1,c.reconstruct (q.1,z))∈d.ambient :=
      (continuousAt_const.prodMk hc.continuousAt) (d.ambient_open.mem_nhds ha)
    filter_upwards [hm,hn] with z hz hza
    exact d.complete (q.1,c.reconstruct (q.1,z)) hza (c.zero (q.1,z) hz)
  exact hd.fderiv.symm.trans (he.fderiv_eq.trans hc.fderiv)


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (c d : ZeroGraphChart (finiteTargetAugment F E) E)

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedChart_transition_identity [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E]
    {q : ℝ × E} (hq : q∈c.domain)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).comp
      (d.coordinate.comp (c.spatialDerivative q))=framedChartJacobian fr c q := by
  have he := d.complete (q.1,c.reconstruct q) ha (c.zero q hq)
  change ((fr.coordinate (q.1,(d.reconstruct (q.1,d.coordinate (c.reconstruct q))).1)).comp
    (d.spatialDerivative (q.1,d.coordinate (c.reconstruct q)))).comp _=_
  rw [he,ContinuousLinearMap.comp_assoc,zeroChart_transition_derivative c d hq ha hr]
  rfl

lemma framedChart_transition_det {q : ℝ × E} (hq : q∈c.domain)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).det *
      (d.coordinate.comp (c.spatialDerivative q)).det=(framedChartJacobian fr c q).det := by
  have he := congrArg (fun A : E →L[ℝ] E => A.det) (framedChart_transition_identity fr c d hq ha hr)
  change LinearMap.det ((framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).toLinearMap.comp
    (d.coordinate.comp (c.spatialDerivative q)).toLinearMap)=_ at he
  simpa only [LinearMap.det_comp] using he

lemma framedChart_transition_signed_det (hF : ContDiff ℝ ∞ F)
    {q : ℝ × E} (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    Real.sign (framedChartJacobian fr c q).det * (d.coordinate.comp (c.spatialDerivative q)).det =
      Real.sign (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).det *
        |(d.coordinate.comp (c.spatialDerivative q)).det| := by
  have he := framedChart_transition_det fr c d hq ha hr
  have hn := framedChartJacobian_det_ne_zero fr c hF hq hv
  have hn' : (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).det≠0 := by
    intro hz
    rw [hz,zero_mul] at he
    exact hn he.symm
  have htn : (d.coordinate.comp (c.spatialDerivative q)).det≠0 := by
    intro hz
    rw [hz,mul_zero] at he
    exact hn he.symm
  rw [←he]
  rcases lt_or_gt_of_ne hn' with hd | hd <;> rcases lt_or_gt_of_ne htn with ht | ht
  · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg hd ht),Real.sign_of_neg hd,abs_of_neg ht]
    ring
  · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos hd ht),Real.sign_of_neg hd,abs_of_pos ht]
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hd ht),Real.sign_of_pos hd,abs_of_neg ht]
    ring
  · rw [Real.sign_of_pos (mul_pos hd ht),Real.sign_of_pos hd,abs_of_pos ht]


end
open scoped ContDiff Topology
open Set Function Filter
variable {P Q Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma smooth_actual_implicit_branch {f : P × Q → Y} (hf : ContDiff ℝ ∞ f)
    {ψ : P → Q} {D : Set P} (hD : IsOpen D) (hψ : ContinuousOn ψ D) (z : Y)
    (hz : ∀ p∈D,f (p,ψ p)=z)
    (hi : ∀ p∈D,((fderiv ℝ f (p,ψ p)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible) :
    ContDiffOn ℝ ∞ ψ D := by
  intro p hp
  let g := hf.contDiffAt.implicitFunction (by simp) (hi p hp)
  have hg : ContDiffAt ℝ ∞ g p := hf.contDiffAt.contDiffAt_implicitFunction (by simp) (hi p hp)
  have he : ψ =ᶠ[𝓝 p] g := by
    have hh := hf.contDiffAt.eventually_apply_eq_iff_implicitFunction (by simp) (hi p hp)
    have hc : ContinuousAt (fun r => (r,ψ r)) p :=
      continuousAt_id.prodMk ((hψ p hp).continuousAt (hD.mem_nhds hp))
    have hm := hc hh
    filter_upwards [hm,hD.mem_nhds hp] with r hr hrD
    exact ((hr).mp ((hz r hrD).trans (hz p hp).symm)).symm
  exact (hg.congr_of_eventuallyEq he).contDiffWithinAt

lemma implicitFunction_smooth_neighborhood {f : P × Q → Y} (hf : ContDiff ℝ ∞ f)
    {u : P × Q} (hi : ((fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible) :
    ∃ D : Set P,IsOpen D ∧ u.1∈D ∧
      ContDiffOn ℝ ∞ (hf.contDiffAt.implicitFunction (by simp) hi) D := by
  let ψ := hf.contDiffAt.implicitFunction (by simp) hi
  have hs : ContDiffAt ℝ ∞ ψ u.1 := hf.contDiffAt.contDiffAt_implicitFunction (by simp) hi
  have hb : ψ u.1=u.2 := hf.contDiffAt.implicitFunction_apply_self (by simp) hi
  obtain ⟨S,hSn,hSs⟩ := hs.contDiffOn (m := 1) (by simp) (by simp)
  have hψf : ∀ᶠ p in 𝓝 u.1,f (p,ψ p)=f u := hf.contDiffAt.eventually_apply_implicitFunction (by simp) hi
  have hder : Continuous (fun v : P × Q => (fderiv ℝ f v).comp (ContinuousLinearMap.inr ℝ P Q)) :=
    (hf.continuous_fderiv (by simp)).clm_comp continuous_const
  have hival : ((fderiv ℝ f (u.1,ψ u.1)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible := by
    simpa only [hb,Prod.mk.eta] using hi
  have hin : ∀ᶠ p in 𝓝 u.1,((fderiv ℝ f (p,ψ p)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible :=
    (hder.continuousAt.comp (continuousAt_id.prodMk hs.continuousAt))
      (ContinuousLinearEquiv.isOpen.mem_nhds hival)
  obtain ⟨D,hD,hDo,hDu⟩ := mem_nhds_iff.mp (inter_mem hSn (inter_mem hψf hin))
  refine ⟨D,hDo,hDu,smooth_actual_implicit_branch hf hDo (hSs.continuousOn.mono (fun _ h => (hD h).1))
    (f u) (fun _ h => (hD h).2.1) (fun _ h => (hD h).2.2)⟩



end HigherDimensionalBallPacking.Rigidity
end

end OAI
