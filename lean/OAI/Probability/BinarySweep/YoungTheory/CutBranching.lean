import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.CoinductionTools
import OAI.Probability.BinarySweep.YoungTheory.CutTensor

namespace OAI

noncomputable section

namespace BinaryCoordinateSweeps.Young

local instance (ν : YoungDiagram) : Module.Finite ℂ (SpechtSpace ν) :=
  inferInstanceAs (FiniteDimensional ℂ (SpechtSpace ν))

local instance (ν : YoungDiagram) :
    @Module.IsTorsionFree ℂ (SpechtSpace ν) _
      (SpechtSpace.instAddCommGroup ν).toAddCommMonoid inferInstance :=
  DivisionSemiring.to_moduleIsTorsionFree

local instance {G V W : Type*} [Monoid G] [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Module.Finite ℂ (Representation.IntertwiningMap ρ σ) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  exact Module.Finite.of_injective (Representation.IntertwiningMap.toLinearMapl (ρ := ρ) (σ := σ))
    (Representation.IntertwiningMap.toLinearMap_injective ρ σ)

section

open scoped BigOperators Classical TensorProduct

open Representation

variable (μ : YoungDiagram) (p : ℕ)

abbrev CutGroup := G (hookPart μ p) × G (southeast μ p)

def cutSpechtRep : Representation ℂ (CutGroup μ p) (CutTensor μ p) :=
  Representation.tprod ((spechtRep (hookPart μ p)).comp (MonoidHom.fst _ _))
    ((spechtRep (southeast μ p)).comp (MonoidHom.snd _ _))

lemma cutSpechtRep_tmul (g : CutGroup μ p) (v : SpechtSpace (hookPart μ p))
    (w : SpechtSpace (southeast μ p)) :
    cutSpechtRep μ p g (v ⊗ₜ[ℂ] w) =
      spechtRep (hookPart μ p) g.1 v ⊗ₜ[ℂ] spechtRep (southeast μ p) g.2 w := rfl

def cutTabloidRep : Representation ℂ (CutGroup μ p) (CutTabloids μ p → ℂ) where
  toFun g := {
    toFun := fun v t => v (g.1⁻¹ • t.1, g.2⁻¹ • t.2)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext v t; simp
  map_mul' g d := by ext v t; simp [mul_smul]

lemma cutRestriction_rep (g : CutGroup μ p) (v : SpechtSpace μ) :
    cutRestriction μ p (spechtRep μ (cutPerm μ p g) v) =
      cutTabloidRep μ p g (cutRestriction μ p v) := by
  ext t
  change spechtInclude μ (spechtRep μ (cutPerm μ p g) v) (glueTabloid μ p t) =
    spechtInclude μ v (glueTabloid μ p (g.1⁻¹ • t.1,g.2⁻¹ • t.2))
  rw [spechtInclude_rep,tabloidRepresentation_apply,← map_inv,← glueTabloid_smul]
  rfl

lemma cutTensorInclude_rep (g : CutGroup μ p) (v : CutTensor μ p) :
    cutTensorInclude μ p (cutSpechtRep μ p g v) =
      cutTabloidRep μ p g (cutTensorInclude μ p v) := by
  induction v using TensorProduct.inductionOn with
  | tmul v w =>
    ext t
    rw [cutSpechtRep_tmul,cutTensorInclude_tmul,spechtInclude_rep,spechtInclude_rep]
    rfl
  | add u v hu hv => simp only [map_add,hu,hv]

def cutRestrictionIntertwiner : IntertwiningMap
    ((spechtRep μ).comp (cutPerm μ p)) (cutTabloidRep μ p) where
  toLinearMap := cutRestriction μ p
  isIntertwining' g := LinearMap.ext (cutRestriction_rep μ p g)

def cutTensorIntertwiner : IntertwiningMap (cutSpechtRep μ p) (cutTabloidRep μ p) where
  toLinearMap := cutTensorInclude μ p
  isIntertwining' g := LinearMap.ext (cutTensorInclude_rep μ p g)

theorem hook_removal_embedding :
    ∃ l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p)),
      Function.Injective l := by
  obtain ⟨l,hl⟩ := Irrep.lift_intertwiner _ _ _
    (cutRestrictionIntertwiner μ p) (cutTensorIntertwiner μ p) (cutTensor_range_le μ p)
  refine ⟨l,?_⟩
  intro v w h
  apply cutTensorInclude_injective μ p
  exact (hl v).symm.trans ((congrArg (cutRestrictionIntertwiner μ p) h).trans (hl w))

def hookPerm : G (hookPart μ p) →* G μ :=
  (cutPerm μ p).comp (MonoidHom.inl _ _)

def hookRestriction : Representation ℂ (G (hookPart μ p)) (SpechtSpace μ) :=
  (spechtRep μ).comp (hookPerm μ p)

def cutSlice (l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p)))
    (w : SpechtSpace (southeast μ p)) :
    IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p) where
  toLinearMap := {
    toFun := fun v => l (v ⊗ₜ[ℂ] w)
    map_add' := by intro a b; rw [TensorProduct.add_tmul,map_add]
    map_smul' := by intro c a; rw [← TensorProduct.smul_tmul',map_smul]; rfl }
  isIntertwining' g := by
    ext v
    have hh := IntertwiningMap.isIntertwining _ _ l (g,1) (v ⊗ₜ[ℂ] w)
    rw [cutSpechtRep_tmul,map_one,Module.End.one_apply] at hh
    exact hh

def cutSliceMap (l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p))) :
    SpechtSpace (southeast μ p) →ₗ[ℂ]
      IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p) where
  toFun := cutSlice μ p l
  map_add' a b := by ext v; exact (congrArg l (TensorProduct.tmul_add _ _ _)).trans (map_add l _ _)
  map_smul' c a := by ext v; exact (congrArg l (TensorProduct.tmul_smul c v a)).trans (map_smul l _ _)

lemma cutSliceMap_injective
    (l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p)))
    (hl : Function.Injective l) : Function.Injective (cutSliceMap μ p l) := by
  intro w z h
  have hh := DFunLike.congr_fun h (spechtPoly (hookPart μ p))
  change l (_ ⊗ₜ[ℂ] w) = l (_ ⊗ₜ[ℂ] z) at hh
  have he := congrArg (cutTensorInclude μ p) (hl hh)
  apply spechtInclude_injective (southeast μ p)
  ext t
  have ht := congrFun he (tabloidOfPerm (hookPart μ p) 1,t)
  simpa only [cutTensorInclude_tmul,spechtInclude_poly,polytabloid_base,one_mul] using ht

theorem hook_removal_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤
      Module.finrank ℂ (IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p)) := by
  obtain ⟨l,hl⟩ := hook_removal_embedding μ p
  exact LinearMap.finrank_le_finrank_of_injective (cutSliceMap_injective μ p l hl)

end

open scoped BigOperators Classical

open Representation

variable (μ : YoungDiagram) (p : ℕ)

abbrev HookInducedSpace := coindV (hookPerm μ p) (spechtRep (hookPart μ p))

def hookInducedRep : Representation ℂ (G μ) (HookInducedSpace μ p) :=
  coind (hookPerm μ p) (spechtRep (hookPart μ p))

lemma hookPerm_block : hookPerm μ p = Irrep.blockPerm (cutEquiv μ p) := rfl

theorem hook_induced_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤
      Module.finrank ℂ (IntertwiningMap (spechtRep μ) (hookInducedRep μ p)) := by
  have he := (Irrep.coindHomEquiv (hookPerm μ p) (spechtRep μ)
    (spechtRep (hookPart μ p))).finrank_eq
  have hs := Irrep.multiplicity_symm (spechtRep (hookPart μ p)) (hookRestriction μ p)
  change Module.finrank ℂ (IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p)) =
    Module.finrank ℂ (IntertwiningMap (hookRestriction μ p) (spechtRep (hookPart μ p))) at hs
  exact (hook_removal_multiplicity μ p).trans (by rw [hs]; exact Nat.le_of_eq he)

lemma hook_induced_dimension :
    Module.finrank ℂ (SpechtSpace μ) ≤ Module.finrank ℂ (HookInducedSpace μ p) := by
  have hp : 0 < Module.finrank ℂ (SpechtSpace (southeast μ p)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨spechtPoly _,spechtPoly_ne_zero _⟩
  let : AddCommGroup (HookInducedSpace μ p) := Module.addCommMonoidToAddCommGroup ℂ
  have hi := lt_of_lt_of_le hp (hook_induced_multiplicity μ p)
  obtain ⟨f,hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hi
  exact LinearMap.finrank_le_finrank_of_injective
    ((IsIrreducible.injective_or_eq_zero f).resolve_right hf)

theorem hook_removal_dimension_upper :
    Module.finrank ℂ (SpechtSpace μ) ≤
      (Fintype.card (Cell μ))^(Fintype.card (Cell (southeast μ p))) *
        Module.finrank ℂ (SpechtSpace (hookPart μ p)) := by
  apply (hook_induced_dimension μ p).trans
  change Module.finrank ℂ (coindV (hookPerm μ p) _) ≤ _
  exact Irrep.placement_coind_finrank_pow (cutEquiv μ p) (spechtRep (hookPart μ p))

end BinaryCoordinateSweeps.Young

end

end OAI
