import OAI.Geometry.ComplexBundle.DirectSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.VectorBundle.Constructions

namespace OAI

noncomputable section

/-! Pullback line bundles and their continuous chart identifications. -/

section
open Bundle Topology
namespace Kaplansky

section
variable {B X J : Type*} [TopologicalSpace B] [TopologicalSpace X]
  (C : VectorBundleCore ℂ B ℂ J) (f : C(X,B))

/-- Pull a line core back along a continuous base map. -/
def pullbackLineCore : VectorBundleCore ℂ X ℂ J where
  baseSet j := f ⁻¹' C.baseSet j
  isOpen_baseSet j := (C.isOpen_baseSet j).preimage f.continuous
  indexAt x := C.indexAt (f x)
  mem_baseSet_at x := C.mem_baseSet_at (f x)
  coordChange i j x := C.coordChange i j (f x)
  coordChange_self i x hx z := C.coordChange_self i (f x) hx z
  continuousOn_coordChange i j := (C.continuousOn_coordChange i j).comp
    f.continuous.continuousOn (fun _ h => h)
  coordChange_comp i j k x hx z := C.coordChange_comp i j k (f x) hx z

/-- This is the ordinary topological pullback, not just a fiberwise copy. -/
def pullbackLineCoreTotalHomeomorph :
    TotalSpace ℂ (pullbackLineCore C f).Fiber ≃ₜ TotalSpace ℂ (f *ᵖ C.Fiber) where
  toFun z := ⟨z.proj,z.2⟩
  invFun z := ⟨z.proj,z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    constructor
    · exact (FiberBundle.continuous_proj ℂ (pullbackLineCore C f).Fiber).continuousAt
    · exact (((pullbackLineCore C f).localTriv (C.indexAt (f z.proj))).continuousAt
        (((pullbackLineCore C f).localTriv _).mem_source.mpr (C.mem_baseSet_at (f z.proj)))).snd
  continuous_invFun := by
    apply continuous_iff_continuousAt.mpr
    intro z
    rw [FiberBundle.continuousAt_totalSpace]
    constructor
    · exact (FiberBundle.continuous_proj ℂ (f *ᵖ C.Fiber)).continuousAt
    · exact ((trivializationAt ℂ (f *ᵖ C.Fiber) z.proj).continuousAt
        (FiberBundle.mem_trivializationAt_proj_source)).snd

/-- A single global identity chart for the trivial complex line. -/
def trivialLineCore (B : Type*) [TopologicalSpace B] : VectorBundleCore ℂ B ℂ Unit where
  baseSet _ := Set.univ
  isOpen_baseSet _ := isOpen_univ
  indexAt _ := ()
  mem_baseSet_at _ := Set.mem_univ _
  coordChange _ _ _ := ContinuousLinearMap.id ℂ ℂ
  coordChange_self _ _ _ _ := rfl
  continuousOn_coordChange _ _ := continuousOn_const
  coordChange_comp _ _ _ _ _ _ := rfl

end

variable {B A X J : Type} [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace X]

/-- Continuity into the core pullback is exactly continuity in the base
and continuity of the induced map to the original total space. -/
theorem continuous_pullbackLineCore_total_iff (C : VectorBundleCore ℂ B ℂ J)
    (f : C(A,B)) (g : X → A) (v : X → ℂ) :
    Continuous (fun x => TotalSpace.mk' ℂ (g x)
      (show (pullbackLineCore C f).Fiber (g x) from v x)) ↔
    Continuous g ∧ Continuous (fun x => TotalSpace.mk' ℂ (f (g x))
      (show C.Fiber (f (g x)) from v x)) := by
  constructor
  · intro h
    have hg := (FiberBundle.continuous_proj ℂ (pullbackLineCore C f).Fiber).comp h
    refine ⟨hg, continuous_iff_continuousAt.mpr (fun x => ?_)⟩
    rw [FiberBundle.continuousAt_totalSpace]
    exact ⟨(f.continuous.comp hg).continuousAt,
      ((FiberBundle.continuousAt_totalSpace ℂ _).mp h.continuousAt).2⟩
  · rintro ⟨hg,hv⟩
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [FiberBundle.continuousAt_totalSpace]
    exact ⟨hg.continuousAt,
      ((FiberBundle.continuousAt_totalSpace ℂ _).mp hv.continuousAt).2⟩

variable {S : Type} [Fintype S] {J : S → Type}

/-- The same assertion for the actual finite Hermitian sum. -/
theorem continuous_pullbackLineSum_total_iff (C : ∀ s, VectorBundleCore ℂ B ℂ (J s))
    (f : C(A,B)) (g : X → A) (v : X → EuclideanSpace ℂ S) :
    Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) (g x)
      (show (finiteLineSumCore (fun s => pullbackLineCore (C s) f)).Fiber (g x) from v x)) ↔
    Continuous g ∧ Continuous (fun x => TotalSpace.mk' (EuclideanSpace ℂ S) (f (g x))
      (show (finiteLineSumCore C).Fiber (f (g x)) from v x)) := by
  rw [continuous_finiteLineSum_iff, continuous_finiteLineSum_iff]
  constructor
  · rintro ⟨hg,hv⟩
    exact ⟨hg, f.continuous.comp hg, fun s =>
      (continuous_pullbackLineCore_total_iff (C s) f g (fun x => v x s)).mp (hv s) |>.2⟩
  · rintro ⟨hg,_,hv⟩
    exact ⟨hg, fun s =>
      (continuous_pullbackLineCore_total_iff (C s) f g (fun x => v x s)).mpr ⟨hg,hv s⟩⟩

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
variable {B A S : Type} [TopologicalSpace B] [TopologicalSpace A]
  [Fintype S] {J : S → Type}
  (C : ∀ s, VectorBundleCore ℂ B ℂ (J s)) (U : Set B) (e : U ≃ₜ A)

def chartBaseMap : C(A,B) :=
  ⟨fun a => (e.symm a).val, continuous_subtype_val.comp e.symm.continuous⟩

/-- Pulling the actual sum into full chart coordinates gives exactly the
restriction of its original total space, with its inherited topology. -/
def lineSumChartPullbackHomeomorph :
    TotalSpace (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun s => pullbackLineCore (C s) (chartBaseMap U e))).Fiber ≃ₜ
    {z : TotalSpace (EuclideanSpace ℂ S) (finiteLineSumCore C).Fiber | z.proj ∈ U} where
  toFun z := ⟨⟨chartBaseMap U e z.proj,z.2⟩,(e.symm z.proj).2⟩
  invFun z := ⟨e ⟨z.1.proj,z.2⟩,z.1.2⟩
  left_inv z := by
    obtain ⟨a,v⟩ := z
    change TotalSpace.mk' _ (e (e.symm a)) v = TotalSpace.mk' _ a v
    rw [e.apply_symm_apply]
  right_inv z := by
    apply Subtype.ext
    obtain ⟨⟨b,v⟩,hb⟩ := z
    change TotalSpace.mk' _ (e.symm (e ⟨b,hb⟩)).val v = TotalSpace.mk' _ b v
    rw [e.symm_apply_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_pullbackLineSum_total_iff C (chartBaseMap U e)
      (fun z : TotalSpace (EuclideanSpace ℂ S)
        (finiteLineSumCore (fun s => pullbackLineCore (C s) (chartBaseMap U e))).Fiber => z.proj)
      (fun z => z.2)).mp continuous_id |>.2
  continuous_invFun := by
    apply (continuous_pullbackLineSum_total_iff C (chartBaseMap U e) _ _).mpr
    constructor
    · exact e.continuous.comp
        (((FiberBundle.continuous_proj _ _).comp continuous_subtype_val).subtype_mk _)
    · convert continuous_subtype_val using 1
      funext z
      change TotalSpace.mk' _ (e.symm (e ⟨z.1.proj,z.2⟩)).val z.1.2 = z.1
      rw [e.symm_apply_apply]

theorem lineSumChartPullbackHomeomorph_base
    (z : TotalSpace (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun s => pullbackLineCore (C s) (chartBaseMap U e))).Fiber) :
    (lineSumChartPullbackHomeomorph C U e z).1.proj = chartBaseMap U e z.proj := rfl

theorem lineSumChartPullbackHomeomorph_fiber
    (z : TotalSpace (EuclideanSpace ℂ S)
      (finiteLineSumCore (fun s => pullbackLineCore (C s) (chartBaseMap U e))).Fiber) :
    (lineSumChartPullbackHomeomorph C U e z).1.2 = z.2 := rfl

end Kaplansky

end

end OAI
