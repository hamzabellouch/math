import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungDominance
import OAI.Probability.BinarySweep.YoungTheory.YoungPartition
import OAI.Probability.BinarySweep.Representations.IrrepTransport

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

abbrev PartitionSpace {n : ℕ} (p : n.Partition) := SpechtSpace (diagram p)

def partitionRep {n : ℕ} (p : n.Partition) :
    Representation ℂ (Equiv.Perm (Fin n)) (PartitionSpace p) :=
  (spechtRep (diagram p)).comp ((cellsEquivFin p).symm.permCongrHom.toMonoidHom)

instance {n : ℕ} (p : n.Partition) :
    Representation.IsIrreducible (k := ℂ) (G := Equiv.Perm (Fin n))
      (V := PartitionSpace p) (partitionRep p) :=
  Irrep.irreducible_comp_equiv _ _

lemma partitionRep_apply {n : ℕ} (p : n.Partition) (g : Equiv.Perm (Fin n))
    (v : PartitionSpace p) : partitionRep p g v =
      spechtRep (diagram p) ((cellsEquivFin p).symm.permCongr g) v := rfl

lemma partitionRep_equiv_injective {n : ℕ} (p q : n.Partition)
    (f : Representation.Equiv (partitionRep p) (partitionRep q)) : p = q := by
  apply diagram_injective
  let e := (cellsEquivFin p).trans (cellsEquivFin q).symm
  apply equivalence_implies_diagram_eq e f.toLinearEquiv
  intro g v
  have h := Representation.IntertwiningMap.isIntertwining
    (partitionRep p) (partitionRep q) f.toIntertwiningMap ((cellsEquivFin p).permCongr g) v
  simp only [partitionRep_apply] at h
  change f.toLinearEquiv _ = _ at h
  have hep : ((cellsEquivFin p).symm.permCongr ((cellsEquivFin p).permCongr g)) = g :=
    (cellsEquivFin p).permCongr.symm_apply_apply g
  rw [hep] at h
  rw [h]
  congr 2

end BinaryCoordinateSweeps.Young

end

end OAI
