import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GroupedLogBounds
import OAI.Probability.BinarySweep.YoungTheory.HookWord

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
open Representation Irrep Signed

variable {N p : ℕ} (α : N.Partition) (h : InHook (diagram α) p)

def hookHilbertMap : IntertwiningMap (partitionHilbertRep α)
    (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N) where
  toLinearMap := (coeffEquiv (Bool × Fin p) N).symm.toLinearMap.comp
    ((hookMap h (cellsEquivFin α)).toLinearMap.comp (spechtHilbertEquiv (diagram α)).symm.toLinearMap)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply (coeffEquiv (Bool × Fin p) N).injective
    change hookMap h (cellsEquivFin α)
      ((spechtHilbertEquiv (diagram α)).symm (partitionHilbertRep α g v)) =
        tensorRep Prod.fst N g (hookMap h (cellsEquivFin α) ((spechtHilbertEquiv (diagram α)).symm v))
    have he := LinearMap.congr_fun ((hookMap h (cellsEquivFin α)).isIntertwining'
      ((cellsEquivFin α).symm.permCongr g)) ((spechtHilbertEquiv (diagram α)).symm v)
    have hg : (cellsEquivFin α).permCongr ((cellsEquivFin α).symm.permCongr g)=g := by
      ext t; simp [Equiv.permCongr_apply]
    change hookMap h (cellsEquivFin α)
      ((spechtHilbertEquiv (diagram α)).symm ((spechtHilbertEquiv (diagram α))
        (spechtRep (diagram α) ((cellsEquivFin α).symm.permCongr g)
          ((spechtHilbertEquiv (diagram α)).symm v)))) = _
    rw [LinearEquiv.symm_apply_apply]
    change hookMap h (cellsEquivFin α)
      (spechtRep (diagram α) ((cellsEquivFin α).symm.permCongr g)
        ((spechtHilbertEquiv (diagram α)).symm v)) =
      tensorRep Prod.fst N ((cellsEquivFin α).permCongr ((cellsEquivFin α).symm.permCongr g))
        (hookMap h (cellsEquivFin α) ((spechtHilbertEquiv (diagram α)).symm v)) at he
    rw [hg] at he
    exact he

lemma hookHilbertMap_injective : Function.Injective (hookHilbertMap α h) :=
  (coeffEquiv (Bool × Fin p) N).symm.injective.comp
    ((hookMap_injective h (cellsEquivFin α)).comp (spechtHilbertEquiv (diagram α)).symm.injective)

include h in
lemma hookHilbert_occurs :
    0<Module.finrank ℂ (IntertwiningMap (partitionHilbertRep α)
      (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N)) := by
  have : Nontrivial (PartitionHilbert α) := by
    exact Module.nontrivial_of_finrank_pos (irreducible_finrank_pos (partitionHilbertRep α))
  have hn : hookHilbertMap α h≠0 := by
    intro he
    obtain ⟨v,hv⟩ := exists_ne (0 : PartitionHilbert α)
    apply hv
    apply hookHilbertMap_injective α h
    rw [he]
    rfl
  have : Nontrivial (IntertwiningMap (partitionHilbertRep α)
      (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N)) := ⟨⟨_,_,hn⟩⟩
  exact Module.finrank_pos

variable (μ : YoungDiagram) (hμ : InHook μ p) (e : Cell μ ≃ Fin N)
def hookHilbertMapAt : IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
    (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N) where
  toLinearMap := (coeffEquiv (Bool × Fin p) N).symm.toLinearMap.comp
    ((hookMap hμ e).toLinearMap.comp (spechtHilbertEquiv μ).symm.toLinearMap)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply (coeffEquiv (Bool × Fin p) N).injective
    change hookMap hμ e
      ((spechtHilbertEquiv μ).symm (((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) g v)) =
        tensorRep Prod.fst N g (hookMap hμ e ((spechtHilbertEquiv μ).symm v))
    have he := LinearMap.congr_fun ((hookMap hμ e).isIntertwining'
      (e.symm.permCongr g)) ((spechtHilbertEquiv μ).symm v)
    have hg : e.permCongr (e.symm.permCongr g)=g := by
      ext t; simp [Equiv.permCongr_apply]
    change hookMap hμ e
      ((spechtHilbertEquiv μ).symm ((spechtHilbertEquiv μ)
        (spechtRep μ (e.symm.permCongr g)
          ((spechtHilbertEquiv μ).symm v)))) = _
    rw [LinearEquiv.symm_apply_apply]
    change hookMap hμ e
      (spechtRep μ (e.symm.permCongr g)
        ((spechtHilbertEquiv μ).symm v)) =
      tensorRep Prod.fst N (e.permCongr (e.symm.permCongr g))
        (hookMap hμ e ((spechtHilbertEquiv μ).symm v)) at he
    rw [hg] at he
    exact he

lemma hookHilbertMapAt_injective : Function.Injective (hookHilbertMapAt μ hμ e) :=
  (coeffEquiv (Bool × Fin p) N).symm.injective.comp
    ((hookMap_injective hμ e).comp (spechtHilbertEquiv μ).symm.injective)

include hμ in
lemma hookHilbert_occursAt :
    0<Module.finrank ℂ (IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N)) := by
  have : Nontrivial (SpechtHilbert μ) := by
    exact Module.nontrivial_of_finrank_pos (irreducible_finrank_pos (hilbertSpecht μ))
  have hn : hookHilbertMapAt μ hμ e≠0 := by
    intro he
    obtain ⟨v,hv⟩ := exists_ne (0 : SpechtHilbert μ)
    apply hv
    apply hookHilbertMapAt_injective μ hμ e
    rw [he]
    rfl
  have : Nontrivial (IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N)) := ⟨⟨_,_,hn⟩⟩
  exact Module.finrank_pos

end BinaryCoordinateSweeps.Young

end

end OAI
