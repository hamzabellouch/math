import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungFinite
import OAI.Probability.BinarySweep.Representations.CharacterComplete

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

theorem partitionRep_complete {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    ∃ p : n.Partition, Nonempty (Representation.Equiv ρ (partitionRep p)) := by
  refine Irrep.complete_of_card_ge (G := Equiv.Perm (Fin n))
    (V := fun p : n.Partition => PartitionSpace p)
    (fun p : n.Partition => partitionRep p) ?_ ?_ ρ
  · intro p q ⟨f⟩
    exact partitionRep_equiv_injective p q f
  · let : Fintype (ConjClasses (Equiv.Perm (Fin n))) := Fintype.ofFinite _
    have h := Fintype.card_le_of_injective (conjPartition (X := Fin n)) conjPartition_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h

theorem specht_complete {X V : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm X) V) [ρ.IsIrreducible] :
    ∃ (μ : YoungDiagram) (e : Cell μ ≃ X), Nonempty (Representation.Equiv ρ
      ((spechtRep μ).comp e.symm.permCongrHom.toMonoidHom)) := by
  let a : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let ρ' : Representation ℂ (Equiv.Perm (Fin (Fintype.card X))) V :=
    ρ.comp a.symm.permCongrHom.toMonoidHom
  have : ρ'.IsIrreducible := Irrep.irreducible_comp_equiv _ _
  obtain ⟨p, ⟨f⟩⟩ := partitionRep_complete ρ'
  let e : Cell (diagram p) ≃ X := (cellsEquivFin p).trans a.symm
  refine ⟨diagram p, e, ⟨Representation.Equiv.mk f.toLinearEquiv ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  have h := Representation.IntertwiningMap.isIntertwining ρ' (partitionRep p)
    f.toIntertwiningMap (a.permCongr g) v
  change f.toLinearEquiv (ρ (a.symm.permCongr (a.permCongr g)) v) =
    spechtRep (diagram p) ((cellsEquivFin p).symm.permCongr (a.permCongr g)) (f.toLinearEquiv v) at h
  rw [show a.symm.permCongr (a.permCongr g) = g from
    a.permCongr.symm_apply_apply g] at h
  exact h

end BinaryCoordinateSweeps.Young

end

end OAI
