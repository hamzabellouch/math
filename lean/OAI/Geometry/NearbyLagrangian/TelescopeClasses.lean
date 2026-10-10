import Mathlib
import OAI.Geometry.NearbyLagrangian.TubeClasses
import OAI.Topology.Homotopy.RayTelescope

namespace OAI

/-! Equivalence of stable tube classes with telescope homotopy classes. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.Tubes
open ContinuousMap

instance tubeSpaceDirectedSystem : DirectedSystem (fun n => Tube n n)
    (fun {m n} h => (stabilizeTo m n h : _ → _)) where
  map_self := by intro m a; simp
  map_map := by
    intro p n m h j a
    exact DFunLike.congr_fun (stabilizeTo_comp m n p h j) a

abbrev Telescope := RayTelescope.Space (fun n => Tube n n) stabilizeTo

def telescopeStage (m : ℕ) : C(Tube m m,Telescope) :=
  RayTelescope.stage (fun n => Tube n n) stabilizeTo m

variable (B : Type) [TopologicalSpace B]

def telescopeHomotopySetoid : Setoid C(B,Telescope) where
  r := ContinuousMap.Homotopic
  iseqv := ContinuousMap.Homotopic.equivalence

abbrev TelescopeClass := Quotient (telescopeHomotopySetoid B)

def telescopeClass (f : C(B,Telescope)) : TelescopeClass B := Quotient.mk'' f

def telescopeClassOnStage (m : ℕ) : TubeHomotopyClass B m → TelescopeClass B :=
  Quotient.map (fun f => (telescopeStage m).comp f)
    (fun _ _ h => (Homotopic.refl (telescopeStage m)).comp h)

@[simp] theorem telescopeClassOnStage_stabilize {m n : ℕ} (h : m ≤ n)
    (a : TubeHomotopyClass B m) :
    telescopeClassOnStage B n (stabilizeClass B m n h a) = telescopeClassOnStage B m a := by
  induction a using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    exact ((RayTelescope.stage_stabilize_homotopic (fun n => Tube n n) stabilizeTo m n h).comp
      (Homotopic.refl a)).symm

def stableClassToTelescope : StableTubeClass B → TelescopeClass B :=
  DirectLimit.lift (stabilizeClass B) (telescopeClassOnStage B) (fun _m _n h a =>
    (telescopeClassOnStage_stabilize B h a).symm)

@[simp] theorem stableClassToTelescope_apply {m : ℕ} (a : C(B,Tube m m)) :
    stableClassToTelescope B (stableClass B a) = telescopeClass B ((telescopeStage m).comp a) := rfl

theorem stableClassToTelescope_surjective [CompactSpace B] :
    Function.Surjective (stableClassToTelescope B) := by
  intro z
  induction z using Quotient.inductionOn with
  | h f =>
    obtain ⟨m,a,ha⟩ := RayTelescope.exists_finite_representative
      (fun n => Tube n n) stabilizeTo f
    exact ⟨stableClass B a,Quotient.sound ha.symm⟩

theorem stableClassToTelescope_injective [CompactSpace B] :
    Function.Injective (stableClassToTelescope B) := by
  intro x y h
  obtain ⟨m,_,a,rfl⟩ := stableClass_rep_above x 0
  obtain ⟨n,_,b,rfl⟩ := stableClass_rep_above y 0
  apply (stableClass_eq_iff B a b).mpr
  exact (RayTelescope.stage_homotopic_iff (fun n => Tube n n) stabilizeTo a b).mp
    (Quotient.exact h)

def stableClassTelescopeEquiv [CompactSpace B] : StableTubeClass B ≃ TelescopeClass B :=
  Equiv.ofBijective (stableClassToTelescope B)
    ⟨stableClassToTelescope_injective B,stableClassToTelescope_surjective B⟩

@[simp] theorem stableClassTelescopeEquiv_apply [CompactSpace B] {m : ℕ}
    (a : C(B,Tube m m)) :
    stableClassTelescopeEquiv B (stableClass B a) =
      telescopeClass B ((telescopeStage m).comp a) := rfl

theorem telescope_stage_null_iff [CompactSpace B] {m : ℕ} (a : C(B,Tube m m)) :
    ((telescopeStage m).comp a).Nullhomotopic ↔
      ∃ r : ℕ, ((stabilizeFor m r).comp a).Nullhomotopic := by
  unfold telescopeStage
  rw [RayTelescope.stage_nullhomotopic_iff (fun n => Tube n n) stabilizeTo]
  constructor
  · rintro ⟨N,h,H⟩
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨r,by simpa only [stabilizeTo_add] using H⟩
  · rintro ⟨r,H⟩
    exact ⟨m+r,Nat.le_add_right m r,by simpa only [stabilizeTo_add] using H⟩

theorem stablyNonNull_iff_telescope_nonnull [CompactSpace B] {m : ℕ}
    (a : C(B,Tube m m)) :
    StablyNonNull a ↔ ¬ ((telescopeStage m).comp a).Nullhomotopic := by
  rw [telescope_stage_null_iff,not_exists]
  rfl

end NearbyLagrangian.Tubes

end

end OAI
