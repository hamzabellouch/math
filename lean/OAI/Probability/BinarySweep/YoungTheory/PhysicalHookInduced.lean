import Mathlib
import OAI.Probability.BinarySweep.Representations.IrrepTransport
import OAI.Probability.BinarySweep.Conditional.PlacementCycleMoment

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Representation

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (μ : YoungDiagram) (p : ℕ) (e : Cell μ ≃ FreeSlot H 0)

def hookPlacementBasis : Cell (hookPart μ p) ⊕ Fin (Fintype.card (Cell (southeast μ p))) ≃ FreeSlot H 0 :=
  ((Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Cell (southeast μ p))).symm).trans
    (cutEquiv μ p)).trans e

lemma hookPlacement_restriction :
    ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom).comp
      (blockPerm (hookPlacementBasis H μ p e)) = (hilbertSpecht μ).comp (hookPerm μ p) := by
  apply MonoidHom.ext
  intro g
  change hilbertSpecht μ
    (e.symm.permCongr (blockPerm (hookPlacementBasis H μ p e) g)) =
    hilbertSpecht μ (hookPerm μ p g)
  apply congrArg (hilbertSpecht μ)
  rw [hookPerm_block]
  apply Equiv.ext
  intro a
  obtain ⟨a,rfl⟩ := (cutEquiv μ p).surjective a
  cases a with
  | inl a => simp [hookPlacementBasis,blockPerm,Equiv.permCongr_apply]
  | inr a => simp [hookPlacementBasis,blockPerm,Equiv.permCongr_apply]

lemma hook_hilbert_restriction_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤ Module.finrank ℂ
      (IntertwiningMap ((hilbertSpecht μ).comp (hookPerm μ p)) (hilbertSpecht (hookPart μ p))) := by
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  let : Module.Finite ℂ (SpechtSpace (hookPart μ p)) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace (hookPart μ p)))
  have hs := multiplicity_symm (spechtRep (hookPart μ p)) (hookRestriction μ p)
  have he := multiplicity_congr
    (repEquiv_comp (conjugateEquiv (spechtRep μ) (spechtHilbertEquiv μ)) (hookPerm μ p))
    (conjugateEquiv (spechtRep (hookPart μ p)) (spechtHilbertEquiv (hookPart μ p)))
  exact (hook_removal_multiplicity μ p).trans (Nat.le_of_eq (hs.trans he))

lemma hook_placement_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤ Module.finrank ℂ
      (IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (coindHilbertRep (blockPerm (hookPlacementBasis H μ p e)) (hilbertSpecht (hookPart μ p))
          (fun x => (placementSection (hookPlacementBasis H μ p e) x)⁻¹)
          (placement_cosets_bijective (hookPlacementBasis H μ p e)))) := by
  let ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (SpechtHilbert μ) :=
    (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom
  let f := hookPlacementBasis H μ p e
  let σ := hilbertSpecht (hookPart μ p)
  have hr := (coindHomEquiv (blockPerm f) ρ σ).finrank_eq
  have hd := multiplicity_congr (Representation.Equiv.refl ρ)
    (conjugateEquiv (coind (blockPerm f) σ)
      (coindHilbertEquiv (blockPerm f) σ (fun x => (placementSection f x)⁻¹)
        (placement_cosets_bijective f)))
  have he : ρ.comp (blockPerm f)=(hilbertSpecht μ).comp (hookPerm μ p) :=
    hookPlacement_restriction H μ p e
  rw [he] at hr
  exact (hook_hilbert_restriction_multiplicity μ p).trans (Nat.le_of_eq (hr.trans hd))

theorem conditional_hook_induced_moment_le (z : ℝ) (q : ℕ) :
    (Module.finrank ℂ (SpechtSpace (southeast μ p)):ℝ)*
      evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (fun a => (conditionalGroupLaw H z a:ℂ))) ≤
      evenMoment q (inducedPlacementAverage H (hookPlacementBasis H μ p e)
        (hilbertSpecht (hookPart μ p)) z) := by
  let ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (SpechtHilbert μ) :=
    (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom
  let : ρ.IsIrreducible := irreducible_comp_equiv e.symm.permCongrHom (hilbertSpecht μ)
  let f := hookPlacementBasis H μ p e
  let σ := coindHilbertRep (blockPerm f) (hilbertSpecht (hookPart μ p))
    (fun x => (placementSection f x)⁻¹) (placement_cosets_bijective f)
  have hσ (a) (v) : ‖σ a v‖=‖v‖ :=
    ((σ a).isometryOfInner (coindHilbert_unitary _ _ _ _
      (hilbertSpecht_inner (hookPart μ p)) a)).norm_map v
  have hm := multiplicity_moment_le ρ σ (fun a => (conditionalGroupLaw H z a:ℂ))
    (fun a v => hilbertSpecht_unitary μ _ v) hσ q
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hook_placement_multiplicity H μ p e)
    (evenMoment_nonneg q _)).trans hm

end BinaryCoordinateSweeps.Young

end

end OAI
