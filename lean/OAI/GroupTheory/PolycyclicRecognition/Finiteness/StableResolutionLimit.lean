import OAI.GroupTheory.PolycyclicRecognition.Finiteness.StableSyzygyMap
import Mathlib.Algebra.Colimit.Module

namespace OAI

/-! # The limiting identity in a projective resolution

The limiting identity vanishes precisely when one syzygy is projective.
This proves the finite-dimension detection step; it does not assert that
FP-infinity or elementary amenability makes this identity vanish.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G] (P : ProjectiveResolution (trivialIntegral G))

abbrev resolutionStableEnd (n : ℕ) :=
  StableRepresentationHom (resolutionSyzygy P n) (resolutionSyzygy P n)

local instance stableEnd_add : ∀ n, AddCommMonoid (resolutionStableEnd P n) :=
  fun n => Submodule.Quotient.addCommMonoid (projectiveFactorSubmodule
    (resolutionSyzygy P n) (resolutionSyzygy P n))

local instance stableEnd_module : ∀ n, Module ℤ (resolutionStableEnd P n) :=
  fun n => Submodule.Quotient.module (projectiveFactorSubmodule
    (resolutionSyzygy P n) (resolutionSyzygy P n))

def resolutionStableForward (i j : ℕ) (h : i ≤ j) :
    resolutionStableEnd P i →ₗ[ℤ] resolutionStableEnd P j where
  toFun := Nat.leRecOn h (fun {k} => resolutionStableSyzygyTransition P k)
  map_add' x y := by
    induction h with
    | refl => simp only [Nat.leRecOn_self]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, map_add, ih]
  map_smul' r x := by
    induction h with
    | refl => simp only [Nat.leRecOn_self, RingHom.id_apply]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, ih, RingHom.id_apply]
      exact (resolutionStableSyzygyTransition P j).map_smul r _

instance resolutionStableForward_directed : DirectedSystem (resolutionStableEnd P)
    (fun i j h => resolutionStableForward P i j h) where
  map_self := by intro i x; exact Nat.leRecOn_self x
  map_map := by intro k j i hij hjk x; exact (Nat.leRecOn_trans hij hjk x).symm

def resolutionStableIdentity (n : ℕ) : resolutionStableEnd P n :=
  stableRepresentationClass _ _ (𝟙 (resolutionSyzygy P n))

theorem resolutionStableForward_identity (i j : ℕ) (h : i ≤ j) :
    resolutionStableForward P i j h (resolutionStableIdentity P i) =
      resolutionStableIdentity P j := by
  induction h with
  | refl => exact Nat.leRecOn_self _
  | @step j h ih =>
    change Nat.leRecOn (C := resolutionStableEnd P) _
      (fun {k} => resolutionStableSyzygyTransition P k) (resolutionStableIdentity P i) = _
    rw [Nat.leRecOn_succ h]
    change resolutionStableSyzygyTransition P j
      (resolutionStableForward P i j h (resolutionStableIdentity P i)) = _
    rw [ih]
    exact resolutionStableSyzygyTransition_identity P j

abbrev StableResolutionLimit :=
  Module.DirectLimit (resolutionStableEnd P) (resolutionStableForward P)

def stableResolutionLimitingIdentity : StableResolutionLimit P :=
  Module.DirectLimit.of ℤ ℕ (resolutionStableEnd P) (resolutionStableForward P) 0
    (resolutionStableIdentity P 0)

theorem stableResolutionLimitingIdentity_eq_zero_iff :
    stableResolutionLimitingIdentity P = 0 ↔ HasFiniteIntegralCohomologicalDimension G := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := Module.DirectLimit.of.zero_exact h
    rw [resolutionStableForward_identity] at he
    exact ⟨j, (stableResolutionIdentity_eq_zero_iff_dimension P j).mp he⟩
  · rintro ⟨j, hj⟩
    have he : resolutionStableIdentity P j = 0 :=
      (stableResolutionIdentity_eq_zero_iff_dimension P j).mpr hj
    have hcompat := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
      (G := resolutionStableEnd P) (f := resolutionStableForward P)
      (hij := Nat.zero_le j) (x := resolutionStableIdentity P 0)
    rw [resolutionStableForward_identity, he, map_zero] at hcompat
    exact hcompat.symm

end PolycyclicRecognition

end

end OAI
