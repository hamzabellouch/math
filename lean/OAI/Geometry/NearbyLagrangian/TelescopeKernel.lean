import Mathlib
import OAI.Geometry.NearbyLagrangian.TelescopeClasses
import OAI.Topology.Homotopy.CubicalSpheres

namespace OAI

/-! The ninth telescope homotopy group and stable tube kernels. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.Tubes
open ContinuousMap CubicalSphere
open scoped Topology Topology.Homotopy

def telescopeBase : Telescope := telescopeStage 0 (standardTube 0 0)

variable (B : Type) [TopologicalSpace B]

def standardTelescopeClass : TelescopeClass B :=
  telescopeClass B (ContinuousMap.const B telescopeBase)

theorem telescope_nullhomotopic_iff_standard (f : C(B,Telescope)) :
    f.Nullhomotopic ↔ f.Homotopic (ContinuousMap.const B telescopeBase) := by
  constructor
  · rintro ⟨c,h⟩
    obtain ⟨p⟩ := PathConnectedSpace.joined c telescopeBase
    exact h.trans ⟨p.toHomotopyConst⟩
  · exact fun h => ⟨telescopeBase,h⟩

theorem telescopeClass_eq_standard_iff (f : C(B,Telescope)) :
    telescopeClass B f = standardTelescopeClass B ↔ f.Nullhomotopic := by
  change (Quotient.mk'' f : TelescopeClass B) = Quotient.mk'' (ContinuousMap.const B telescopeBase) ↔ _
  rw [Quotient.eq]
  exact (telescope_nullhomotopic_iff_standard B f).symm

@[simp] theorem stableClassTelescopeEquiv_standard [CompactSpace B] :
    stableClassTelescopeEquiv B (standardStableClass B) = standardTelescopeClass B := by
  change telescopeClass B ((telescopeStage 0).comp (ContinuousMap.const B (standardTube 0 0))) = _
  rw [ContinuousMap.comp_const]
  rfl

abbrev TelescopePi9 := HomotopyGroup.Pi 9 Telescope telescopeBase

def telescopePi9ToFree : TelescopePi9 → TelescopeClass (Metric.sphere (0 : Euclidean 10) 1) :=
  Quotient.lift (fun f => telescopeClass _ (sphereMap f)) (by
    intro f g h
    obtain ⟨H⟩ := h
    exact Quotient.sound ⟨sphereHomotopy H⟩)

theorem telescopePi9ToFree_surjective : Function.Surjective telescopePi9ToFree := by
  intro z
  induction z using Quotient.inductionOn with
  | h a =>
    obtain ⟨f,hf⟩ := exists_based_representative a telescopeBase
    exact ⟨⟦f⟧,Quotient.sound hf.symm⟩

theorem telescopePi9ToFree_eq_standard_iff (a : TelescopePi9) :
    telescopePi9ToFree a = standardTelescopeClass (Metric.sphere (0 : Euclidean 10) 1) ↔
      a = (1 : TelescopePi9) := by
  induction a using Quotient.inductionOn with
  | h f =>
    change telescopeClass _ (sphereMap f) = standardTelescopeClass _ ↔ _
    rw [telescopeClass_eq_standard_iff]
    exact sphereMap_null_iff_class_one f

def telescopePi9ToStable : TelescopePi9 → StableTubeClass (Metric.sphere (0 : Euclidean 10) 1) :=
  fun a => (stableClassTelescopeEquiv _).symm (telescopePi9ToFree a)

theorem telescopePi9ToStable_surjective : Function.Surjective telescopePi9ToStable := by
  intro x
  obtain ⟨a,ha⟩ := telescopePi9ToFree_surjective (stableClassTelescopeEquiv _ x)
  refine ⟨a,?_⟩
  change (stableClassTelescopeEquiv _).symm (telescopePi9ToFree a) = x
  rw [ha,Equiv.symm_apply_apply]

theorem telescopePi9ToStable_eq_standard_iff (a : TelescopePi9) :
    telescopePi9ToStable a = standardStableClass (Metric.sphere (0 : Euclidean 10) 1) ↔
      a = (1 : TelescopePi9) := by
  rw [← telescopePi9ToFree_eq_standard_iff]
  change (stableClassTelescopeEquiv _).symm (telescopePi9ToFree a) = _ ↔ _
  rw [Equiv.symm_apply_eq,stableClassTelescopeEquiv_standard]

def telescopePi9NegativeClass (a : TelescopePi9) :
    FiberFamily.StableClass (Metric.sphere (0 : Euclidean 10) 1) :=
  stableNegativeClass (V:=Euclidean 9) (telescopePi9ToStable a)

theorem kernelFamilyGoal_iff_telescope_pi9_kernel : KernelFamilyGoal ↔
    ∃ a : TelescopePi9, a ≠ (1 : TelescopePi9) ∧
      telescopePi9NegativeClass a = standardSphericalClass (Metric.sphere (0 : Euclidean 10) 1) := by
  rw [kernelFamilyGoal_iff_actual_nontrivial_fiber]
  constructor
  · rintro ⟨x,hx,ht⟩
    obtain ⟨a,rfl⟩ := telescopePi9ToStable_surjective x
    exact ⟨a,fun h => hx ((telescopePi9ToStable_eq_standard_iff a).mpr h),ht⟩
  · rintro ⟨a,ha,ht⟩
    exact ⟨telescopePi9ToStable a,fun h => ha ((telescopePi9ToStable_eq_standard_iff a).mp h),ht⟩

end NearbyLagrangian.Tubes

end

end OAI
