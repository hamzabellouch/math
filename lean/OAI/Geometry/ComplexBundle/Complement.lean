import OAI.Geometry.ComplexBundle.Kernel
import OAI.Geometry.ComplexBundle.Orthonormal

namespace OAI

noncomputable section

/-! Local and global topology and splitting of frame complement bundles. -/

section
open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
namespace ContinuousOrthonormalStageFrame

section
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)

/-- The complement is the kernel of the actual frame coefficient map. -/
theorem analysis_ker (y : ProjectiveProduct K) :
    LinearMap.ker (frameAnalysis (f.vector y)) =
      (Submodule.span ℂ (Set.range (f.vector y)))ᗮ := by
  ext v
  rw [LinearMap.mem_ker,Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    have hz (i : Fin d) : inner ℂ (f.vector y i) v=0 :=
      congrArg (fun w : EuclideanSpace ℂ (Fin d) => w i) h
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      exact hz i
    | zero => exact inner_zero_left _
    | add u w hu hw ihu ihw =>
      exact (inner_add_left u w _).trans (by rw [ihu, ihw, zero_add])
    | smul c u hu ihu =>
      exact (inner_smul_left u _ c).trans (by rw [ihu, mul_zero])
  · intro h
    apply (EuclideanSpace.equiv (Fin d) ℂ).injective
    funext i
    exact h _ (Submodule.subset_span ⟨i,rfl⟩)

theorem analysis_surjective (y : ProjectiveProduct K) :
    Function.Surjective (frameAnalysis (f.vector y)) :=
  fun v => ⟨frameSynthesis (f.vector y) v,frameAnalysis_synthesis _ (f.orthonormal y) v⟩

/-- The actual kernel has constant rank, with no complement-bundle premise. -/
theorem analysis_kernel_finrank (y : ProjectiveProduct K) :
    Module.finrank ℂ (LinearMap.ker (frameAnalysis (f.vector y))) = Fintype.card a.Slot-d := by
  rw [f.analysis_ker]
  have h := f.complement_finrank y
  omega

end

section
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)
variable (e : Trivialization a.Model (π a.Model a.Fiber)) [e.IsLinear ℂ]

/-- The coefficient map in an ambient chart. -/
def localAnalysis (y : e.baseSet) : a.Model →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  ((frameAnalysis (f.vector y.val)).comp (e.symmL ℂ y.val).toLinearMap).toContinuousLinearMap

theorem continuous_localAnalysis : Continuous (f.localAnalysis e) := by
  apply continuous_clm_apply.mpr
  intro v
  have hc : Continuous (fun y : e.baseSet =>
      TotalSpace.mk' a.Model y.val (e.symmL ℂ y.val v)) := by
    have h := e.continuousOn_symm.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun y : e.baseSet => show (y.val,v) ∈ e.baseSet ×ˢ Set.univ from ⟨y.property,Set.mem_univ _⟩)
    exact h.congr (fun y => by simp only [Function.comp_apply,e.symmL_apply y.property])
  exact f.continuous_analysis.comp hc

theorem localAnalysis_surjective (y : e.baseSet) : Function.Surjective (f.localAnalysis e y) := by
  intro v
  refine ⟨e.continuousLinearMapAt ℂ y.val (frameSynthesis (f.vector y.val) v),?_⟩
  change frameAnalysis (f.vector y.val)
    (e.symmL ℂ y.val (e.continuousLinearMapAt ℂ y.val (frameSynthesis (f.vector y.val) v)))=v
  rw [e.symmL_continuousLinearMapAt y.property,frameAnalysis_synthesis _ (f.orthonormal y.val)]

/-- A continuous surjective family on every ambient chart, constructed from
an arbitrary continuous orthonormal frame. -/
def localKernelFamily : SmoothKernel.SurjectiveFamily e.baseSet a.Model (EuclideanSpace ℂ (Fin d)) where
  map := f.localAnalysis e
  continuous := f.continuous_localAnalysis e
  surjective := f.localAnalysis_surjective e

end

section
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)

/-- The actual complement, with the ambient bundle's subspace topology. -/
abbrev ComplementTotal := {z : TotalSpace a.Model a.Fiber //
  z.2 ∈ (Submodule.span ℂ (Set.range (f.vector z.proj)))ᗮ}

variable (e : Trivialization a.Model (π a.Model a.Fiber)) [e.IsLinear ℂ]
abbrev LocalComplementTotal := {z : f.ComplementTotal // z.val.proj ∈ e.baseSet}

def complementToLocalKernel (z : f.LocalComplementTotal e) :
    (f.localKernelFamily e).IncidenceTotal := by
  refine ⟨(⟨z.val.val.proj,z.property⟩,e.continuousLinearMapAt ℂ z.val.val.proj z.val.val.2),?_⟩
  change frameAnalysis (f.vector z.val.val.proj)
    (e.symmL ℂ z.val.val.proj (e.continuousLinearMapAt ℂ z.val.val.proj z.val.val.2))=0
  rw [e.symmL_continuousLinearMapAt z.property]
  exact (show z.val.val.2 ∈ LinearMap.ker (frameAnalysis (f.vector z.val.val.proj)) from
    (f.analysis_ker z.val.val.proj).symm ▸ z.val.property)

def localKernelToComplement (z : (f.localKernelFamily e).IncidenceTotal) :
    f.LocalComplementTotal e := by
  refine ⟨⟨⟨z.val.1.val,e.symmL ℂ z.val.1.val z.val.2⟩,?_⟩,z.val.1.property⟩
  rw [← f.analysis_ker]
  exact z.property

theorem continuous_complementToLocalKernel : Continuous (f.complementToLocalKernel e) := by
  have hp : Continuous (fun z : f.LocalComplementTotal e => z.val.val.proj) :=
    (FiberBundle.continuous_proj _ _).comp (continuous_subtype_val.comp continuous_subtype_val)
  have he : Continuous (fun z : f.LocalComplementTotal e =>
      e.continuousLinearMapAt ℂ z.val.val.proj z.val.val.2) := by
    have hc := (e.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z : f.LocalComplementTotal e => e.mem_source.mpr z.property)).snd
    exact hc.congr (fun z => (e.continuousLinearMapAt_apply_of_mem ℂ z.property _).symm)
  exact ((hp.subtype_mk _).prodMk he).subtype_mk _

theorem continuous_localKernelToComplement : Continuous (f.localKernelToComplement e) := by
  have hp : Continuous (fun z : (f.localKernelFamily e).IncidenceTotal => z.val.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hv : Continuous (fun z : (f.localKernelFamily e).IncidenceTotal => z.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hc := e.continuousOn_symm.comp_continuous (hp.prodMk hv)
    (fun z : (f.localKernelFamily e).IncidenceTotal =>
      show (z.val.1.val,z.val.2) ∈ e.baseSet ×ˢ Set.univ from ⟨z.val.1.property,Set.mem_univ _⟩)
  have hs : Continuous (fun z : (f.localKernelFamily e).IncidenceTotal =>
      TotalSpace.mk' a.Model z.val.1.val (e.symmL ℂ z.val.1.val z.val.2)) :=
    hc.congr (fun z => by simp only [Function.comp_apply,e.symmL_apply z.val.1.property])
  exact (hs.subtype_mk _).subtype_mk _

/-- A homeomorphism to the genuine kernel incidence set over an ambient
chart. Both spaces retain their ambient subspace topologies. -/
def localComplementKernelHomeomorph : f.LocalComplementTotal e ≃ₜ
    (f.localKernelFamily e).IncidenceTotal where
  toFun := f.complementToLocalKernel e
  invFun := f.localKernelToComplement e
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨⟨⟨y,v⟩,hv⟩,hy⟩ := z
    exact congrArg (TotalSpace.mk' a.Model y) (e.symmL_continuousLinearMapAt hy v)
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact e.continuousLinearMapAt_symmL z.val.1.property z.val.2
  continuous_toFun := f.continuous_complementToLocalKernel e
  continuous_invFun := f.continuous_localKernelToComplement e

/-- The local ordinary kernel bundle realizes the exact orthogonal
complement, not an independently assigned topology on the same fibers. -/
def localComplementBundleHomeomorph :
    TotalSpace (SmoothKernel.KernelModel a.Model (EuclideanSpace ℂ (Fin d)))
      (f.localKernelFamily e).realCore.Fiber ≃ₜ f.LocalComplementTotal e :=
  (f.localKernelFamily e).incidenceHomeomorph.trans (f.localComplementKernelHomeomorph e).symm

end

section
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)

abbrev ComplementModel (_ : ContinuousOrthonormalStageFrame a d) := SmoothKernel.KernelModel a.Model (EuclideanSpace ℂ (Fin d))
abbrev ComplementFiber (y : ProjectiveProduct K) :=
  ↥(Submodule.span ℂ (Set.range (f.vector y)))ᗮ

def complementTotalEquiv : TotalSpace f.ComplementModel f.ComplementFiber ≃ f.ComplementTotal where
  toFun z := ⟨⟨z.proj,z.2.val⟩,z.2.property⟩
  invFun z := ⟨z.val.proj,⟨z.val.2,z.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance complementTotalTopology : TopologicalSpace (TotalSpace f.ComplementModel f.ComplementFiber) :=
  TopologicalSpace.induced f.complementTotalEquiv inferInstance

def complementTotalHomeomorph : TotalSpace f.ComplementModel f.ComplementFiber ≃ₜ f.ComplementTotal :=
  f.complementTotalEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

def complementInclusion (z : TotalSpace f.ComplementModel f.ComplementFiber) : TotalSpace a.Model a.Fiber :=
  ⟨z.proj,z.2.val⟩

theorem complementInclusion_isInducing : IsInducing f.complementInclusion :=
  IsInducing.subtypeVal.comp f.complementTotalHomeomorph.isInducing

theorem complement_totalSpaceMk_isInducing (y : ProjectiveProduct K) :
    IsInducing (TotalSpace.mk (F := f.ComplementModel) (E := f.ComplementFiber) y) := by
  have h : IsInducing (fun v : f.ComplementFiber y =>
      TotalSpace.mk' a.Model y v.val) :=
    (FiberBundle.totalSpaceMk_isInducing a.Model a.Fiber y).comp IsInducing.subtypeVal
  exact (f.complementInclusion_isInducing.of_comp_iff).mp h

end

section
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)
variable (e : Trivialization a.Model (π a.Model a.Fiber)) [e.IsLinear ℂ]

def complementLocalTriv (i : e.baseSet) : Trivialization f.ComplementModel
    (fun z : f.LocalComplementTotal e => (⟨z.val.val.proj,z.property⟩ : e.baseSet)) :=
  ((f.localKernelFamily e).realCore.localTriv i).compHomeomorph
    (f.localComplementBundleHomeomorph e).symm

theorem complementLocalTriv_apply (i : e.baseSet) (z : f.LocalComplementTotal e) :
    (f.complementLocalTriv e i z).2 =
      (f.localKernelFamily e).toModel i (e.continuousLinearMapAt ℂ z.val.val.proj z.val.val.2) := by
  exact (f.localKernelFamily e).fromIncidence_chart (f.complementToLocalKernel e z) i

/-- Extend the locally constructed kernel chart over its open base into
the actual global complement total space. -/
def complementAmbientTriv (i : e.baseSet) : Trivialization f.ComplementModel
    (fun z : f.ComplementTotal => z.val.proj) :=
  Trivialization.domExtend
    (e.open_baseSet.preimage ((FiberBundle.continuous_proj _ _).comp continuous_subtype_val))
    ((f.complementLocalTriv e i).codExtend e.open_baseSet ⟨i.val,i.property⟩)

def complementTriv (i : e.baseSet) : Trivialization f.ComplementModel
    (π f.ComplementModel f.ComplementFiber) :=
  (f.complementAmbientTriv e i).compHomeomorph f.complementTotalHomeomorph

theorem complementTriv_baseSet (i : e.baseSet) :
    (f.complementTriv e i).baseSet = Subtype.val '' (f.localKernelFamily e).baseSet i := rfl

theorem complementTriv_apply (i : e.baseSet) (y : ProjectiveProduct K) (hy : y ∈ e.baseSet)
    (v : f.ComplementFiber y) :
    (f.complementTriv e i ⟨y,v⟩).2 =
      (f.localKernelFamily e).toModel i (e.continuousLinearMapAt ℂ y v.val) := by
  classical
  change (((f.complementLocalTriv e i).codExtend e.open_baseSet ⟨i.val,i.property⟩).toPretrivialization.domExtend
    (f.complementTotalEquiv ⟨y,v⟩)).2 = _
  dsimp only [Pretrivialization.domExtend]
  change (if h : y ∈ e.baseSet then
    ((f.complementLocalTriv e i).codExtend e.open_baseSet ⟨i.val,i.property⟩)
      ⟨f.complementTotalEquiv ⟨y,v⟩,h⟩ else _).2 = _
  rw [dite_eq_left hy]
  exact f.complementLocalTriv_apply e i ⟨f.complementTotalEquiv ⟨y,v⟩,hy⟩

instance complementTriv_isLinear (i : e.baseSet) : (f.complementTriv e i).IsLinear ℂ where
  linear y hy := by
    rw [f.complementTriv_baseSet] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    let L : f.ComplementFiber z.val →ₗ[ℂ] f.ComplementModel :=
      ((f.localKernelFamily e).toModel i).toLinearMap.comp
        ((e.continuousLinearMapAt ℂ z.val).toLinearMap.comp (Submodule.subtype _))
    have he : (fun v : f.ComplementFiber z.val => (f.complementTriv e i ⟨z.val,v⟩).2)=L := by
      funext v
      exact f.complementTriv_apply e i z.val z.property v
    rw [he]
    exact L.isLinear

end

variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)

def complementTrivializationAt (y : ProjectiveProduct K) :
    Trivialization f.ComplementModel (π f.ComplementModel f.ComplementFiber) :=
  f.complementTriv (trivializationAt a.Model a.Fiber y)
    ⟨y,mem_baseSet_trivializationAt a.Model a.Fiber y⟩

theorem mem_complementTrivializationAt (y : ProjectiveProduct K) :
    y ∈ (f.complementTrivializationAt y).baseSet := by
  rw [complementTrivializationAt,f.complementTriv_baseSet]
  exact ⟨_,(f.localKernelFamily (trivializationAt a.Model a.Fiber y)).center_mem _,rfl⟩

instance complementFiberBundle : FiberBundle f.ComplementModel f.ComplementFiber where
  totalSpaceMk_isInducing' := f.complement_totalSpaceMk_isInducing
  trivializationAtlas' := Set.range f.complementTrivializationAt
  trivializationAt' := f.complementTrivializationAt
  mem_baseSet_trivializationAt' := f.mem_complementTrivializationAt
  trivialization_mem_atlas' y := ⟨y,rfl⟩

instance complementTrivializationAt_isLinear (y : ProjectiveProduct K) :
    (f.complementTrivializationAt y).IsLinear ℂ := by
  unfold complementTrivializationAt
  infer_instance

theorem continuousOn_complement_coordChange
    (e e' : Trivialization f.ComplementModel (π f.ComplementModel f.ComplementFiber))
    [e.IsLinear ℂ] [e'.IsLinear ℂ] :
    ContinuousOn (fun y => (e.coordChangeL ℂ e' y : f.ComplementModel →L[ℂ] f.ComplementModel))
      (e.baseSet ∩ e'.baseSet) := by
  apply continuousOn_clm_apply.mpr
  intro v
  have hi : ContinuousOn (fun y : ProjectiveProduct K =>
      TotalSpace.mk' f.ComplementModel y (e.symm y v)) (e.baseSet ∩ e'.baseSet) :=
    e.continuousOn_symm.comp (continuousOn_id.prodMk continuousOn_const)
      (fun y hy => ⟨hy.1,Set.mem_univ _⟩)
  have hc := (e'.continuousOn.comp hi (fun y hy => e'.mem_source.mpr hy.2)).snd
  exact hc.congr (fun y hy => e.coordChangeL_apply e' hy v)

/-- The full orthogonal complement is an ordinary complex vector bundle,
with charts constructed from the frame and the inherited ambient topology. -/
instance complementVectorBundle : VectorBundle ℂ f.ComplementModel f.ComplementFiber where
  trivialization_linear' := by
    rintro _ ⟨y,rfl⟩
    exact f.complementTrivializationAt_isLinear y
  continuousOn_coordChange' := by
    rintro _ _ ⟨y,rfl⟩ ⟨z,rfl⟩
    exact f.continuousOn_complement_coordChange _ _

theorem complementBundle_rank (y : ProjectiveProduct K) :
    Module.finrank ℂ (f.ComplementFiber y) = Fintype.card a.Slot-d := by
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (f.vector y)))ᗮ = _
  have h := f.complement_finrank y
  omega

end ContinuousOrthonormalStageFrame
end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
namespace ContinuousOrthonormalStageFrame
variable {ι : Type*} {K : ι → ℕ} {a : LineStage K} {d : ℕ}
variable (f : ContinuousOrthonormalStageFrame a d)

theorem analysis_complement (y : ProjectiveProduct K) (v : f.ComplementFiber y) :
    frameAnalysis (f.vector y) v.val=0 := by
  change v.val ∈ LinearMap.ker (frameAnalysis (f.vector y))
  rw [f.analysis_ker]
  exact v.property

theorem projection_synthesis (y : ProjectiveProduct K) (v : EuclideanSpace ℂ (Fin d)) :
    f.projection y (frameSynthesis (f.vector y) v)=frameSynthesis (f.vector y) v := by
  change frameSynthesis (f.vector y) (frameAnalysis (f.vector y) (frameSynthesis (f.vector y) v))=_
  rw [frameAnalysis_synthesis _ (f.orthonormal y)]

/-- The actual fiber decomposition into the full orthogonal complement and
the trivial frame summand. No alignment with the original line summands. -/
def complementSplitLinearEquiv (y : ProjectiveProduct K) :
    (f.ComplementFiber y × EuclideanSpace ℂ (Fin d)) ≃ₗ[ℂ] a.Fiber y where
  toFun v := v.1.val+frameSynthesis (f.vector y) v.2
  invFun v := (⟨f.complementProjection y v,f.complementProjection_mem y v⟩,frameAnalysis (f.vector y) v)
  left_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      change (v.1.val+frameSynthesis (f.vector y) v.2) -
        f.projection y (v.1.val+frameSynthesis (f.vector y) v.2)=v.1.val
      rw [map_add,f.projection_eq_zero_of_orthogonal y v.1.val v.1.property,f.projection_synthesis]
      simp
    · change frameAnalysis (f.vector y) (v.1.val+frameSynthesis (f.vector y) v.2)=v.2
      rw [map_add,f.analysis_complement,frameAnalysis_synthesis _ (f.orthonormal y),zero_add]
  right_inv v := by
    change v-f.projection y v+f.projection y v=v
    exact sub_add_cancel _ _
  map_add' v w := by
    change v.1.val+w.1.val+frameSynthesis (f.vector y) (v.2+w.2)=_
    rw [map_add]
    abel
  map_smul' c v := by
    change c • v.1.val+frameSynthesis (f.vector y) (c • v.2)=_
    exact (congrArg (fun w => c • v.1.val + w)
      ((frameSynthesis (f.vector y)).map_smul c v.2)).trans
        (smul_add c v.1.val (frameSynthesis (f.vector y) v.2)).symm

abbrev ComplementSplitTotal :=
  TotalSpace f.ComplementModel f.ComplementFiber × EuclideanSpace ℂ (Fin d)

def complementAssemble (z : f.ComplementSplitTotal) : TotalSpace a.Model a.Fiber :=
  ⟨z.1.proj,f.complementSplitLinearEquiv z.1.proj (z.1.2,z.2)⟩

def complementDisassemble (z : TotalSpace a.Model a.Fiber) : f.ComplementSplitTotal :=
  (⟨z.proj,(f.complementSplitLinearEquiv z.proj).symm z.2 |>.1⟩,
    (f.complementSplitLinearEquiv z.proj).symm z.2 |>.2)

theorem continuous_complementAssemble : Continuous f.complementAssemble := by
  have hv : Continuous (fun z : f.ComplementSplitTotal =>
      TotalSpace.mk' a.Model z.1.proj z.1.2.val) :=
    f.complementInclusion_isInducing.continuous.comp continuous_fst
  have hp : Continuous (fun z : f.ComplementSplitTotal => z.1.proj) :=
    (FiberBundle.continuous_proj _ _).comp continuous_fst
  have hw : Continuous (fun z : f.ComplementSplitTotal =>
      TotalSpace.mk' a.Model z.1.proj (frameSynthesis (f.vector z.1.proj) z.2)) :=
    f.continuous_synthesis.comp (hp.prodMk continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hp.continuousAt,?_⟩
  have hvc := (FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := z)).mp hv.continuousAt |>.2
  have hwc := (FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := z)).mp hw.continuousAt |>.2
  apply (hvc.add hwc).congr_of_eventuallyEq
  let e := trivializationAt a.Model a.Fiber z.1.proj
  have hn := hp.continuousAt (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt a.Model a.Fiber z.1.proj))
  filter_upwards [hn] with w hw
  exact (e.linear ℂ hw).map_add w.1.2.val (frameSynthesis (f.vector w.1.proj) w.2)

theorem continuous_complementDisassemble : Continuous f.complementDisassemble := by
  have hc : Continuous (fun z : TotalSpace a.Model a.Fiber =>
      (⟨z.proj,⟨f.complementProjection z.proj z.2,f.complementProjection_mem z.proj z.2⟩⟩ :
        TotalSpace f.ComplementModel f.ComplementFiber)) :=
    f.complementInclusion_isInducing.continuous_iff.mpr f.continuous_complementProjection
  exact hc.prodMk f.continuous_analysis

/-- Global topological splitting of the actual bundle. The first factor
is the constructed complement vector bundle and the other factor is trivial. -/
def complementSplitHomeomorph : f.ComplementSplitTotal ≃ₜ TotalSpace a.Model a.Fiber where
  toFun := f.complementAssemble
  invFun := f.complementDisassemble
  left_inv z := by
    obtain ⟨⟨y,v⟩,w⟩ := z
    have h := (f.complementSplitLinearEquiv y).symm_apply_apply (v,w)
    change ((⟨y,((f.complementSplitLinearEquiv y).symm (f.complementSplitLinearEquiv y (v,w))).1⟩ : TotalSpace f.ComplementModel f.ComplementFiber),
      ((f.complementSplitLinearEquiv y).symm (f.complementSplitLinearEquiv y (v,w))).2)=((⟨y,v⟩ : TotalSpace f.ComplementModel f.ComplementFiber),w)
    rw [h]
  right_inv z := by
    obtain ⟨y,v⟩ := z
    exact congrArg (TotalSpace.mk' a.Model y) ((f.complementSplitLinearEquiv y).apply_symm_apply v)
  continuous_toFun := f.continuous_complementAssemble
  continuous_invFun := f.continuous_complementDisassemble

@[simp] theorem complementSplitHomeomorph_base (z : f.ComplementSplitTotal) :
    (f.complementSplitHomeomorph z).proj=z.1.proj := rfl

end ContinuousOrthonormalStageFrame
end Kaplansky

end

end OAI
