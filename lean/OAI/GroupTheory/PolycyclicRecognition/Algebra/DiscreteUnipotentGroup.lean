import OAI.GroupTheory.PolycyclicRecognition.Algebra.DiscreteUnipotentAbelian
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentGroupNilpotent
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentAbelianFiniteness

namespace OAI

/-! # Polycyclicity of discrete upper-unipotent groups

An inducing representation turns the polynomial logarithm of every abelian
subgroup into a discrete integral submodule. Matrix nilpotence and the
abelian-subgroup criterion then supply a finite cyclic series.
-/

namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]

/-- Every discrete faithfully represented upper-unipotent real matrix group
is polycyclic. No finite-generation assumption is needed. -/
theorem isPolycyclic_of_discrete_strictUpper_representation
    {n : ℕ} (ρ : H →* (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hρ : Topology.IsInducing (fun h => (ρ h : Matrix (Fin n) (Fin n) ℝ)))
    (hinj : Function.Injective ρ)
    (hu : ∀ h, StrictUpper ((ρ h : Matrix (Fin n) (Fin n) ℝ) - 1)) :
    IsPolycyclic H := by
  let := nilpotent_of_faithful_strictUpper_representation ρ hinj hu
  apply isPolycyclic_of_nilpotent_abelian_subgroups_fg
  intro A hA
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := hA.is_comm.comm }
  let σ := ρ.comp A.subtype
  apply finitelyGenerated_of_discrete_unipotent_representation σ
    (hρ.comp Topology.IsInducing.subtypeVal)
  intro a
  exact ⟨n, (hu a).pow_eq_zero⟩

end PolycyclicRecognition

end OAI
