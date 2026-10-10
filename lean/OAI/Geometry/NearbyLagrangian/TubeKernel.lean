import Mathlib
import OAI.Geometry.NearbyLagrangian.TelescopeKernel
import OAI.Topology.Homotopy.FiberKernel

namespace OAI

/-! The tube-family reduction from a classifying map and homotopy-size hypotheses. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.Tubes
open ContinuousMap CubicalSphere BasedHomotopy
open scoped Topology Topology.Homotopy
local notation "S9" => Metric.sphere (0 : Euclidean 10) 1
variable {Y : Type*} [TopologicalSpace Y]

theorem telescope_negative_class_iff_classifying_zero (γ : C(Telescope,Y))
    (classifies : ∀ (m : ℕ), 20 ≤ m → ∀ a : C(S9,Tube m m),
      (γ.comp ((telescopeStage m).comp a)).Nullhomotopic ↔ StableNegativeTrivial a)
    (a : TelescopePi9) :
    telescopePi9NegativeClass a = standardSphericalClass S9 ↔
      groupMap γ rfl a = 1 := by
  induction a using Quotient.inductionOn with
  | h f =>
    obtain ⟨m,hm,b,hb⟩ := stableClass_rep_above (telescopePi9ToStable ⟦f⟧) 20
    have hrep : telescopeClass S9 ((telescopeStage m).comp b) = telescopeClass S9 (sphereMap f) := by
      have he := congrArg (stableClassTelescopeEquiv S9) hb
      simpa only [stableClassTelescopeEquiv_apply,telescopePi9ToStable,
        Equiv.apply_symm_apply, telescopePi9ToFree, Quotient.lift_mk] using he
    have H : ((telescopeStage m).comp b).Homotopic (sphereMap f) := Quotient.exact hrep
    have HG : (γ.comp ((telescopeStage m).comp b)).Homotopic (γ.comp (sphereMap f)) :=
      (Homotopic.refl γ).comp H
    have hn : (γ.comp ((telescopeStage m).comp b)).Nullhomotopic ↔
        (γ.comp (sphereMap f)).Nullhomotopic := by
      constructor
      · rintro ⟨y,hy⟩; exact ⟨y,HG.symm.trans hy⟩
      · rintro ⟨y,hy⟩; exact ⟨y,HG.trans hy⟩
    have hf : (γ.comp (sphereMap f)).Nullhomotopic ↔
        groupMap γ rfl (⟦f⟧ : TelescopePi9) = 1 := by
      change (γ.comp (sphereMap f)).Nullhomotopic ↔
        (⟦SphereConnectivity.genLoopMap γ f⟧ : π_ 9 Y (γ telescopeBase)) =
        (1 : π_ 9 Y (γ telescopeBase))
      simpa only [sphereMap_natural] using
        sphereMap_null_iff_class_one (n := 8) (SphereConnectivity.genLoopMap γ f)
    change stableNegativeClass (V:=Euclidean 9) (telescopePi9ToStable ⟦f⟧) = _ ↔ _
    rw [← hb,stableNegativeClass_apply,negativeStableClass_eq_standard_iff (V:=Euclidean 9) (by omega)]
    exact (classifies m hm b).symm.trans (hn.trans hf)

theorem kernelFamilyGoal_of_classifying_map_and_source_sizes (γ : C(Telescope,Y))
    (classifies : ∀ (m : ℕ), 20 ≤ m → ∀ a : C(S9,Tube m m),
      (γ.comp ((telescopeStage m).comp a)).Nullhomotopic ↔ StableNegativeTrivial a)
    (sphereCalculation : π_ 10 Y (γ telescopeBase) ≃ (Fin 3 → ZMod 2))
    (whiteheadClasses : (ZMod 8 × (ZMod 2 × ZMod 2)) ↪
      π_ 9 (HomotopyFiber.Fiber γ (γ telescopeBase)) (HomotopyFiber.base γ telescopeBase)) :
    KernelFamilyGoal := by
  obtain ⟨a,ha,hγ⟩ := HomotopyFiber.nontrivial_pi9_kernel_of_source_sizes γ telescopeBase
    sphereCalculation whiteheadClasses
  exact kernelFamilyGoal_iff_telescope_pi9_kernel.mpr
    ⟨a,ha,(telescope_negative_class_iff_classifying_zero γ classifies a).mpr hγ⟩

end NearbyLagrangian.Tubes

end

end OAI
