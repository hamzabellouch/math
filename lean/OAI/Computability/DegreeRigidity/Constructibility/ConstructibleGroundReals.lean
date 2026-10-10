import OAI.Computability.DegreeRigidity.Constructibility.ConstructibleSeparation
import OAI.Computability.DegreeRigidity.SetModels.ModelReals

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

noncomputable def groundReals (M : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.powerset ZFSet.omega).sep (fun x => x ∈ M)

theorem mem_groundReals (M x : ZFSet.{u}) :
    x ∈ groundReals M ↔ x ∈ M ∧ x ⊆ ZFSet.omega := by
  rw [groundReals,ZFSet.mem_sep,ZFSet.mem_powerset,and_comm]

theorem groundReals_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    groundReals M ∈ M := by
  obtain ⟨R,hR,hdef⟩ := internal_power M hM hT.powerSet (sourceT_omega_mem M hM hT)
  have heq : R = groundReals M := by
    apply ZFSet.ext; intro x
    exact (hdef x).trans (mem_groundReals M x).symm
  exact heq ▸ hR

theorem realCode_mem_groundReals (M : ZFSet.{u}) (A : Oracle) :
    realCode A ∈ groundReals M ↔ A ∈ modelReals M := by
  rw [mem_groundReals]
  exact and_iff_left (realCode_subset A)

theorem ground_real_in_relativeL (M : ZFSet.{u}) (A : Oracle)
    (hA : A ∈ modelReals M) : InRelativeL (groundReals M) (realCode A) :=
  relativeL_transitive _ (parameter_in_relativeL _) ((realCode_mem_groundReals M A).mpr hA)

theorem ground_seed_subset (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    seed (groundReals M) ⊆ M :=
  seed_minimal _ M hM (groundReals_mem M hM hT)

theorem omega_in_ground_relativeL (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    InRelativeL (groundReals M) ZFSet.omega := by
  apply relativeL_transitive _ (parameter_in_relativeL _)
  exact (mem_groundReals M _).mpr ⟨sourceT_omega_mem M hM hT,fun _ h => h⟩

theorem ground_relativeL_infinity (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ a : ZFSet.{u}, InRelativeL (groundReals M) a ∧ (∅ : ZFSet.{u}) ∈ a ∧
      ∀ x ∈ a, insert x x ∈ a := by
  refine ⟨ZFSet.omega,omega_in_ground_relativeL M hM hT,ZFSet.omega_zero,?_⟩
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨n+1,rfl⟩

end TuringRigidity.RelativeConstructible

end OAI
