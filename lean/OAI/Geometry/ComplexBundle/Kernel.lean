import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.VectorBundle.Basic

namespace OAI

noncomputable section

/-! Smooth splittings, kernel charts, and realization of kernel bundles. -/

section
open scoped ContDiff
namespace Kaplansky.SmoothKernel

section
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Right inverse on the open neighborhood where A R is invertible. -/
def localRightInverse (R : W →L[ℂ] V) (A : V →L[ℂ] W) : W →L[ℂ] V :=
  R.comp (Ring.inverse (A.comp R))

def kernelProjection (R : W →L[ℂ] V) (A : V →L[ℂ] W) : V →L[ℂ] V :=
  ContinuousLinearMap.id ℂ V - (localRightInverse R A).comp A

def splitDomain (R : W →L[ℂ] V) : Set (V →L[ℂ] W) := {A | IsUnit (A.comp R)}

theorem splitDomain_open [CompleteSpace W] (R : W →L[ℂ] V) : IsOpen (splitDomain R) := by
  change IsOpen ((fun A : V →L[ℂ] W => A.comp R) ⁻¹' {B : W →L[ℂ] W | IsUnit B})
  exact Units.isOpen.preimage (continuous_id.clm_comp continuous_const)

theorem localRightInverse_right (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (w : W) : A (localRightInverse R A w)=w := by
  exact congrArg (fun T : W →L[ℂ] W => T w) (Ring.mul_inverse_cancel (A.comp R) hA)

theorem localRightInverse_on_range (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (w : W) : localRightInverse R A (A (R w))=R w := by
  have h := congrArg (fun T : W →L[ℂ] W => T w) (Ring.inverse_mul_cancel (A.comp R) hA)
  exact congrArg R h

theorem kernelProjection_mem (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (v : V) : A (kernelProjection R A v)=0 := by
  change A (v-localRightInverse R A (A v))=0
  rw [map_sub,localRightInverse_right R A hA,sub_self]

theorem kernelProjection_fix (R : W →L[ℂ] V) (A : V →L[ℂ] W) (v : V)
    (hv : A v=0) : kernelProjection R A v=v := by
  change v-localRightInverse R A (A v)=v
  rw [hv,map_zero,sub_zero]

theorem kernelProjection_kill (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (w : W) : kernelProjection R A (R w)=0 := by
  change R w-localRightInverse R A (A (R w))=0
  rw [localRightInverse_on_range R A hA,sub_self]

theorem kernelProjection_absorb (R : W →L[ℂ] V) (A B : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (v : V) :
    kernelProjection R A (kernelProjection R B v)=kernelProjection R A v := by
  change kernelProjection R A (v-R (Ring.inverse (B.comp R) (B v)))=_
  rw [map_sub,kernelProjection_kill R A hA,sub_zero]

/-- Explicit linear identification of the actual kernels throughout the split
neighborhood. Both maps are restrictions of the constructed projections. -/
def kernelEquiv (R : W →L[ℂ] V) (L A : V →L[ℂ] W)
    (hL : L ∈ splitDomain R) (hA : A ∈ splitDomain R) :
    LinearMap.ker L.toLinearMap ≃ₗ[ℂ] LinearMap.ker A.toLinearMap where
  toFun v := ⟨kernelProjection R A v.val,kernelProjection_mem R A hA v.val⟩
  invFun v := ⟨kernelProjection R L v.val,kernelProjection_mem R L hL v.val⟩
  left_inv v := by
    apply Subtype.ext
    exact (kernelProjection_absorb R L A hL v.val).trans (kernelProjection_fix R L v.val v.property)
  right_inv v := by
    apply Subtype.ext
    exact (kernelProjection_absorb R A L hA v.val).trans (kernelProjection_fix R A v.val v.property)
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c v := by apply Subtype.ext; exact map_smul _ _ _

variable [CompleteSpace W]

theorem localRightInverse_smooth (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) : ContDiffAt ℂ ∞ (localRightInverse R) A := by
  obtain ⟨u,hu⟩ := hA
  have hi : ContDiffAt ℂ ∞ Ring.inverse (A.comp R) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℂ u
  exact contDiffAt_const.clm_comp (hi.comp A (contDiffAt_id.clm_comp contDiffAt_const))

theorem kernelProjection_smooth (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) : ContDiffAt ℂ ∞ (kernelProjection R) A :=
  contDiffAt_const.sub ((localRightInverse_smooth R A hA).clm_comp contDiffAt_id)

theorem kernelProjection_apply_smooth (R : W →L[ℂ] V) (A : V →L[ℂ] W)
    (hA : A ∈ splitDomain R) (v : V) :
    ContDiffAt ℂ ∞ (fun p : (V →L[ℂ] W) × V => kernelProjection R p.1 p.2) (A,v) :=
  ((kernelProjection_smooth R A hA).comp (A,v) contDiffAt_fst).clm_apply contDiffAt_snd

end

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

def kernelRetraction (R : W →L[ℂ] V) (L : V →L[ℂ] W) (hL : L ∈ splitDomain R) :
    V →L[ℂ] LinearMap.ker L.toLinearMap :=
  (kernelProjection R L).codRestrict _ (kernelProjection_mem R L hL)

abbrev SplitBase (R : W →L[ℂ] V) := {A : V →L[ℂ] W // A ∈ splitDomain R}

/-- The actual incidence subset, with the topology induced from parameters and V. -/
abbrev SplitIncidence (R : W →L[ℂ] V) := {p : SplitBase R × V // p.1.val p.2=0}

/-- A homeomorphism over the parameter base between the actual local kernel
incidence space and the product with one fixed kernel. -/
def kernelChartHomeomorph (R : W →L[ℂ] V) (L : V →L[ℂ] W) (hL : L ∈ splitDomain R) :
    SplitIncidence R ≃ₜ SplitBase R × LinearMap.ker L.toLinearMap where
  toFun p := (p.val.1, kernelRetraction R L hL p.val.2)
  invFun p := ⟨(p.1,kernelProjection R p.1.val p.2.val),kernelProjection_mem R _ p.1.property _⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (kernelProjection_absorb R p.val.1.val L p.val.1.property p.val.2).trans
        (kernelProjection_fix R _ _ p.property)
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (kernelProjection_absorb R L p.1.val hL p.2.val).trans
        (kernelProjection_fix R L p.2.val p.2.property)
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((kernelRetraction R L hL).continuous.comp (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    have hc : Continuous (fun A : SplitBase R => kernelProjection R A.val) := by
      apply continuous_iff_continuousAt.mpr
      intro A
      exact (kernelProjection_smooth R A.val A.property).continuousAt.comp
        continuous_subtype_val.continuousAt
    exact (continuous_fst.prodMk ((hc.comp continuous_fst).clm_apply
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The fiber coordinate transition really is projection onto the second
fixed kernel after reconstruction in the varying kernel. -/
def kernelCoordinateChange (R R' : W →L[ℂ] V) (L L' : V →L[ℂ] W)
    (hL' : L' ∈ splitDomain R') (A : V →L[ℂ] W) :
    LinearMap.ker L.toLinearMap →L[ℂ] LinearMap.ker L'.toLinearMap :=
  (kernelRetraction R' L' hL').comp ((kernelProjection R A).comp
    (LinearMap.ker L.toLinearMap).subtypeL)

theorem kernelCoordinateChange_smooth (R R' : W →L[ℂ] V) (L L' : V →L[ℂ] W)
    (hL' : L' ∈ splitDomain R') (A : V →L[ℂ] W) (hA : A ∈ splitDomain R) :
    ContDiffAt ℂ ∞ (kernelCoordinateChange R R' L L' hL') A :=
  contDiffAt_const.clm_comp ((kernelProjection_smooth R A hA).clm_comp contDiffAt_const)

theorem kernelCoordinateChange_smooth_real (R R' : W →L[ℂ] V) (L L' : V →L[ℂ] W)
    (hL' : L' ∈ splitDomain R') (A : V →L[ℂ] W) (hA : A ∈ splitDomain R) :
    ContDiffAt ℝ ∞ (kernelCoordinateChange R R' L L' hL') A :=
  (kernelCoordinateChange_smooth R R' L L' hL' A hA).restrict_scalars ℝ

end Kaplansky.SmoothKernel

end

namespace Kaplansky.SmoothKernel
variable {B V W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

abbrev KernelModel (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] :=
  Fin (Module.finrank ℂ V-Module.finrank ℂ W) → ℂ

/-- Ordinary continuous, surjective linear families. No kernel bundle is part
of the input: the following construction supplies it. -/
structure SurjectiveFamily (B V W : Type*) [TopologicalSpace B]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] where
  map : B → V →L[ℂ] W
  continuous : Continuous map
  surjective : ∀ b, Function.Surjective (map b)

local instance : CompleteSpace W := FiniteDimensional.complete ℂ W

namespace SurjectiveFamily
variable (A : SurjectiveFamily B V W)

def rightInverse (b : B) : W →L[ℂ] V :=
  ((A.map b).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (A.surjective b))).choose.toContinuousLinearMap

omit [FiniteDimensional ℂ V] in
theorem rightInverse_spec (b : B) : (A.map b).comp (A.rightInverse b)=1 := by
  apply ContinuousLinearMap.ext
  intro w
  exact congrArg (fun T : W →ₗ[ℂ] W => T w)
    ((A.map b).toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (A.surjective b))).choose_spec

omit [FiniteDimensional ℂ V] in
theorem center_mem (b : B) : A.map b ∈ splitDomain (A.rightInverse b) := by
  change IsUnit ((A.map b).comp (A.rightInverse b))
  rw [A.rightInverse_spec]
  exact isUnit_one

omit [FiniteDimensional ℂ W] in
theorem kernel_finrank (b : B) : Module.finrank ℂ (LinearMap.ker (A.map b).toLinearMap)=
    Module.finrank ℂ V-Module.finrank ℂ W := by
  have h := (A.map b).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (A.surjective b),finrank_top] at h
  omega

def modelEquiv (b : B) : KernelModel V W ≃L[ℂ] LinearMap.ker (A.map b).toLinearMap :=
  ((FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
    (R := ℂ) (M := KernelModel V W) (M' := LinearMap.ker (A.map b).toLinearMap)).mpr
      (by simp [KernelModel,A.kernel_finrank])).some.toContinuousLinearEquiv

def baseSet (i : B) : Set B := {b | A.map b ∈ splitDomain (A.rightInverse i)}

omit [FiniteDimensional ℂ V] in
theorem baseSet_open (i : B) : IsOpen (A.baseSet i) :=
  (splitDomain_open (A.rightInverse i)).preimage A.continuous

def toModel (i : B) : V →L[ℂ] KernelModel V W :=
  (A.modelEquiv i).symm.toContinuousLinearMap.comp
    (kernelRetraction (A.rightInverse i) (A.map i) (A.center_mem i))

def fromModel (i b : B) : KernelModel V W →L[ℂ] V :=
  (kernelProjection (A.rightInverse i) (A.map b)).comp
    (((LinearMap.ker (A.map i).toLinearMap).subtypeL).comp (A.modelEquiv i).toContinuousLinearMap)

theorem fromModel_mem (i b : B) (hb : b ∈ A.baseSet i) (z : KernelModel V W) :
    A.map b (A.fromModel i b z)=0 :=
  kernelProjection_mem (A.rightInverse i) (A.map b) hb _

theorem toModel_fromModel (i b : B) (z : KernelModel V W) :
    A.toModel i (A.fromModel i b z)=z := by
  change (A.modelEquiv i).symm
    ⟨kernelProjection (A.rightInverse i) (A.map i)
      (kernelProjection (A.rightInverse i) (A.map b) (A.modelEquiv i z).val),_⟩=z
  have h := kernelProjection_absorb (A.rightInverse i) (A.map i) (A.map b)
    (A.center_mem i) (A.modelEquiv i z).val
  have hf := kernelProjection_fix (A.rightInverse i) (A.map i)
    (A.modelEquiv i z).val (A.modelEquiv i z).property
  have he : (⟨kernelProjection (A.rightInverse i) (A.map i)
      (kernelProjection (A.rightInverse i) (A.map b) (A.modelEquiv i z).val),
      kernelProjection_mem _ _ (A.center_mem i) _⟩ : LinearMap.ker (A.map i).toLinearMap)=
        A.modelEquiv i z := Subtype.ext (h.trans hf)
  rw [he,(A.modelEquiv i).symm_apply_apply]

theorem fromModel_toModel (i b : B) (hb : b ∈ A.baseSet i) (v : V)
    (hv : A.map b v=0) : A.fromModel i b (A.toModel i v)=v := by
  change kernelProjection (A.rightInverse i) (A.map b)
    (A.modelEquiv i ((A.modelEquiv i).symm (kernelRetraction _ _ _ v))).val=v
  rw [(A.modelEquiv i).apply_symm_apply]
  exact (kernelProjection_absorb (A.rightInverse i) (A.map b) (A.map i) hb v).trans
    (kernelProjection_fix _ _ v hv)

def transition (i j b : B) : KernelModel V W →L[ℂ] KernelModel V W :=
  (A.toModel j).comp (A.fromModel i b)

theorem transition_self (i b : B) (z : KernelModel V W) : A.transition i i b z=z :=
  A.toModel_fromModel i b z

theorem transition_comp (i j k b : B) (hi : b ∈ A.baseSet i) (hj : b ∈ A.baseSet j)
    (z : KernelModel V W) :
    A.transition j k b (A.transition i j b z)=A.transition i k b z := by
  change A.toModel k (A.fromModel j b (A.toModel j (A.fromModel i b z)))=_
  rw [A.fromModel_toModel j b hj _ (A.fromModel_mem i b hi z)]
  rfl

theorem continuousOn_fromModel (i : B) : ContinuousOn (A.fromModel i) (A.baseSet i) := by
  intro b hb
  exact (((kernelProjection_smooth (A.rightInverse i) (A.map b) hb).continuousAt.comp
    A.continuous.continuousAt).clm_comp continuousAt_const).continuousWithinAt

/-- The kernel bundle core has the actual rank dim(V)-dim(W), with local
transitions constructed from the family and its right inverses. -/
def core : VectorBundleCore ℂ B (KernelModel V W) B where
  baseSet := A.baseSet
  isOpen_baseSet := A.baseSet_open
  indexAt b := b
  mem_baseSet_at b := A.center_mem b
  coordChange := A.transition
  coordChange_self i b _ z := A.transition_self i b z
  continuousOn_coordChange i j :=
    (continuousOn_const (c := A.toModel j)).clm_comp
      ((A.continuousOn_fromModel i).mono Set.inter_subset_left)
  coordChange_comp i j k b hb z := A.transition_comp i j k b hb.1.1 hb.1.2 z

/-- Every constructed fiber is linearly identified with the actual kernel. -/
def fiberEquiv (b : B) : A.core.Fiber b ≃ₗ[ℂ] LinearMap.ker (A.map b).toLinearMap :=
  (A.modelEquiv b).toLinearEquiv

end SurjectiveFamily
end Kaplansky.SmoothKernel

section
open scoped ContDiff Manifold
namespace Kaplansky.SmoothKernel.SurjectiveFamily
variable {B V W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
local instance : CompleteSpace W := FiniteDimensional.complete ℂ W
variable (A : SurjectiveFamily B V W)

def realCore : VectorBundleCore ℝ B (KernelModel V W) B where
  baseSet := A.baseSet
  isOpen_baseSet := A.baseSet_open
  indexAt b := b
  mem_baseSet_at b := A.center_mem b
  coordChange i j b := (A.transition i j b).restrictScalars ℝ
  coordChange_self i b _ z := A.transition_self i b z
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.restrictScalarsL ℂ (KernelModel V W) (KernelModel V W) ℝ ℝ).continuous.comp_continuousOn
      ((continuousOn_const (c := A.toModel j)).clm_comp
        ((A.continuousOn_fromModel i).mono Set.inter_subset_left))
  coordChange_comp i j k b hb z := A.transition_comp i j k b hb.1.1 hb.1.2 z

instance realFiberComplexModule (b : B) : Module ℂ (A.realCore.Fiber b) :=
  inferInstanceAs (Module ℂ (KernelModel V W))

def realFiberEquiv (b : B) : A.realCore.Fiber b ≃ₗ[ℂ] LinearMap.ker (A.map b).toLinearMap :=
  (A.modelEquiv b).toLinearEquiv

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem kernel_model_real_finrank : Module.finrank ℝ (KernelModel V W)=
    2*(Module.finrank ℂ V-Module.finrank ℂ W) := by
  rw [finrank_real_of_complex]
  simp [KernelModel]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (D : SurjectiveFamily X V W)

theorem transition_contDiffAt (hD : ContDiff ℝ ∞ D.map) (i j x : X) (hx : x ∈ D.baseSet i) :
    ContDiffAt ℝ ∞ (D.transition i j) x := by
  have hc : ContDiff ℂ ∞ (fun P : V →L[ℂ] V => (D.toModel j).comp
      (P.comp (((LinearMap.ker (D.map i).toLinearMap).subtypeL).comp
        (D.modelEquiv i).toContinuousLinearMap))) :=
    contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)
  exact (hc.restrict_scalars ℝ).contDiffAt.comp x
    (((kernelProjection_smooth (D.rightInverse i) (D.map x) hx).restrict_scalars ℝ).comp x
      hD.contDiffAt)

/-- A genuinely smooth kernel bundle, derived from smoothness and surjectivity
of the original family. Smoothness of the kernel bundle is not an assumption. -/
theorem realCore_isContMDiff (hD : ContDiff ℝ ∞ D.map) :
    D.realCore.IsContMDiff 𝓘(ℝ,X) ∞ where
  contMDiffOn_coordChange i j := by
    apply ContDiffOn.contMDiffOn
    intro x hx
    exact ((ContinuousLinearMap.restrictScalarsL ℂ (KernelModel V W) (KernelModel V W) ℝ ℝ).contDiff.contDiffAt.comp x
      (D.transition_contDiffAt hD i j x hx.1)).contDiffWithinAt

end Kaplansky.SmoothKernel.SurjectiveFamily

end

open Topology Bundle
namespace Kaplansky.SmoothKernel.SurjectiveFamily
variable {B V W : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
local instance : CompleteSpace W := FiniteDimensional.complete ℂ W
variable (A : SurjectiveFamily B V W)

theorem fromModel_center (b : B) (z : KernelModel V W) :
    A.fromModel b b z=(A.modelEquiv b z).val :=
  kernelProjection_fix _ _ _ (A.modelEquiv b z).property

abbrev IncidenceTotal := {z : B × V // A.map z.1 z.2=0}

def realization (z : TotalSpace (KernelModel V W) A.realCore.Fiber) : V :=
  (A.realFiberEquiv z.proj z.2).val

theorem realization_chart (b : B) (z : A.realCore.Fiber b) (i : B) (hi : b ∈ A.baseSet i) :
    (A.realFiberEquiv b z).val=A.fromModel i b ((A.realCore.localTriv i ⟨b,z⟩).2) := by
  change KernelModel V W at z
  change (A.modelEquiv b z).val=A.fromModel i b (A.toModel i (A.fromModel b b z))
  rw [A.fromModel_center,A.fromModel_toModel i b hi _ (A.modelEquiv b z).property]

theorem continuous_realization : Continuous A.realization := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let C := A.realCore
  let i := z.proj
  have hi : z.proj ∈ A.baseSet i := A.center_mem z.proj
  have hp : Continuous (π (KernelModel V W) C.Fiber) := FiberBundle.continuous_proj _ _
  have hx : z ∈ (C.localTriv i).source := (C.localTriv i).mem_source.mpr hi
  have hc := ((C.localTriv i).continuousAt hx).snd
  have hf := ((A.continuousOn_fromModel i z.proj hi).continuousAt
    ((A.baseSet_open i).mem_nhds hi)).comp hp.continuousAt
  apply (hf.clm_apply hc).congr_of_eventuallyEq
  filter_upwards [hp.continuousAt ((A.baseSet_open i).mem_nhds hi)] with w hw
  exact A.realization_chart w.proj w.2 i hw

def toIncidence (z : TotalSpace (KernelModel V W) A.realCore.Fiber) : A.IncidenceTotal :=
  ⟨(z.proj,A.realization z),(A.realFiberEquiv z.proj z.2).property⟩

def fromIncidence (z : A.IncidenceTotal) : TotalSpace (KernelModel V W) A.realCore.Fiber :=
  ⟨z.val.1,(A.realFiberEquiv z.val.1).symm ⟨z.val.2,z.property⟩⟩

theorem fromIncidence_chart (z : A.IncidenceTotal) (i : B) :
    ((A.realCore.localTriv i) (A.fromIncidence z)).2=A.toModel i z.val.2 := by
  change A.toModel i (A.fromModel z.val.1 z.val.1
    ((A.modelEquiv z.val.1).symm ⟨z.val.2,z.property⟩))=_
  rw [A.fromModel_center,(A.modelEquiv z.val.1).apply_symm_apply]

theorem continuous_fromIncidence : Continuous A.fromIncidence := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  have hp : Continuous (fun z : A.IncidenceTotal => z.val.1) := continuous_subtype_val.fst
  refine ⟨hp.continuousAt,?_⟩
  let i := z.val.1
  have hc : ContinuousAt (fun w : A.IncidenceTotal => A.toModel i w.val.2) z :=
    (A.toModel i).continuous.continuousAt.comp continuous_subtype_val.snd.continuousAt
  exact hc.congr (Filter.Eventually.of_forall (fun w => (A.fromIncidence_chart w i).symm))

/-- The constructed smooth real bundle realizes the exact complex kernel
incidence subset, including its ambient subspace topology. -/
def incidenceHomeomorph : TotalSpace (KernelModel V W) A.realCore.Fiber ≃ₜ A.IncidenceTotal where
  toFun := A.toIncidence
  invFun := A.fromIncidence
  left_inv z := by
    rcases z with ⟨b,v⟩
    change (⟨b,(A.realFiberEquiv b).symm (A.realFiberEquiv b v)⟩ :
      TotalSpace (KernelModel V W) A.realCore.Fiber)=⟨b,v⟩
    rw [LinearEquiv.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val ((A.realFiberEquiv z.val.1).apply_symm_apply ⟨z.val.2,z.property⟩)
  continuous_toFun := (FiberBundle.continuous_proj _ _).prodMk A.continuous_realization |>.subtype_mk _
  continuous_invFun := A.continuous_fromIncidence

end Kaplansky.SmoothKernel.SurjectiveFamily

end

end OAI
