import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungAnti

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

def polyModule : (tabloidRepresentation μ).asModule :=
  (tabloidRepresentation μ).asModuleEquiv.symm (polytabloid μ)

def antiModule : Module.End ℂ (tabloidRepresentation μ).asModule :=
  (tabloidRepresentation μ).asModuleEquiv.symm.toLinearMap.comp
    ((columnAnti μ).comp (tabloidRepresentation μ).asModuleEquiv.toLinearMap)

lemma antiModule_apply (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v = (tabloidRepresentation μ).asModuleEquiv.symm
      (columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v)) := rfl

lemma antiModule_rank_one (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v =
      columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) • polyModule μ := by
  rw [antiModule_apply, columnAnti_rank_one, map_smul]
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one]
  rfl

lemma antiModule_poly : antiModule μ (polyModule μ) =
    (Fintype.card (C μ) : ℂ) • polyModule μ := by
  rw [antiModule_apply, polyModule, LinearEquiv.apply_symm_apply, columnAnti_polytabloid, map_smul]

def Specht : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule :=
  Submodule.span _ {polyModule μ}

lemma polyModule_mem_Specht : polyModule μ ∈ Specht μ :=
  Submodule.subset_span (Set.mem_singleton _)

lemma polyModule_ne_zero : polyModule μ ≠ 0 := by
  intro h
  apply polytabloid_ne_zero μ
  have he := congrArg (tabloidRepresentation μ).asModuleEquiv h
  simpa only [polyModule, LinearEquiv.apply_symm_apply, map_zero] using he

lemma Specht_ne_bot : Specht μ ≠ ⊥ := by
  intro h
  have hm := polyModule_mem_Specht μ
  rw [h] at hm
  exact polyModule_ne_zero μ hm

lemma antiModule_mem (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    (v : (tabloidRepresentation μ).asModule) (hv : v ∈ U) : antiModule μ v ∈ U := by
  rw [antiModule_apply, columnAnti_apply, map_sum]
  apply U.sum_mem
  intro c hc
  have h := U.smul_mem (MonoidAlgebra.single c.val (signC μ c.val)) hv
  have he : (tabloidRepresentation μ).asModuleEquiv.symm
      (signC μ c.val • tabloidRepresentation μ c.val ((tabloidRepresentation μ).asModuleEquiv v)) =
      MonoidAlgebra.single c.val (signC μ c.val) • v := by
    apply (tabloidRepresentation μ).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
  rw [he]
  exact h

lemma scalar_polyModule_mem_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    {a : ℂ} (ha : a ≠ 0) : a • polyModule μ ∈ U ↔ polyModule μ ∈ U := by
  exact (U.restrictScalars ℂ).smul_mem_iff ha

lemma Specht_le_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule) :
    Specht μ ≤ U ↔ polyModule μ ∈ U := by
  rw [Specht, Submodule.span_le, Set.singleton_subset_iff]
  rfl

theorem Specht_isAtom : IsAtom (Specht μ) := by
  refine ⟨Specht_ne_bot μ, ?_⟩
  intro U hU
  obtain ⟨V, hUV⟩ := exists_isCompl U
  have ht : polyModule μ ∈ U ⊔ V := by
    rw [hUV.sup_eq_top]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ht
  have hau := antiModule_mem μ U u hu
  have hav := antiModule_mem μ V v hv
  rw [antiModule_rank_one] at hau hav
  by_cases hc : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv u) (tabloidOfPerm μ 1) = 0
  · have he : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) =
          (Fintype.card (C μ) : ℂ) := by
      have hh := congrArg (fun w : (tabloidRepresentation μ).asModule =>
        columnAnti μ ((tabloidRepresentation μ).asModuleEquiv w) (tabloidOfPerm μ 1)) huv
      simp only [map_add, Pi.add_apply, hc, zero_add, polyModule,
        LinearEquiv.apply_symm_apply, columnAnti_polytabloid,
        Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at hh
      exact hh
    have hne : (Fintype.card (C μ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hSV : Specht μ ≤ V := (Specht_le_iff μ V).mpr
      ((scalar_polyModule_mem_iff μ V (he.trans_ne hne)).mp hav)
    apply le_antisymm _ bot_le
    calc U ≤ U ⊓ V := le_inf le_rfl (hU.le.trans hSV)
         _ = ⊥ := hUV.inf_eq_bot
  · have hSU : Specht μ ≤ U := (Specht_le_iff μ U).mpr
      ((scalar_polyModule_mem_iff μ U hc).mp hau)
    exact (hU.not_ge hSU).elim

instance Specht_isSimpleModule : IsSimpleModule ℂ[G μ] (Specht μ) :=
  isSimpleModule_iff_isAtom.mpr (Specht_isAtom μ)

end BinaryCoordinateSweeps.Young

end

open scoped MonoidAlgebra BigOperators

namespace BinaryCoordinateSweeps.Young

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V] [IsScalarTower ℂ A V]

def restrictLinearEquiv : RestrictScalars ℂ A V ≃ₗ[ℂ] V where
  __ := RestrictScalars.addEquiv ℂ A V
  map_smul' a v := by
    change RestrictScalars.addEquiv ℂ A V (a • v) = a • RestrictScalars.addEquiv ℂ A V v
    rw [RestrictScalars.addEquiv_map_smul, algebraMap_smul]

variable (μ : YoungDiagram)
abbrev SpechtSpace := RestrictScalars ℂ ℂ[G μ] (Specht μ)

-- Use the same additive monoid for the restricted module and its additive group.
instance SpechtSpace.instAddCommGroup : AddCommGroup (SpechtSpace μ) :=
  Module.addCommMonoidToAddCommGroup ℂ

instance : @Module ℂ (SpechtSpace μ) _ (SpechtSpace.instAddCommGroup μ).toAddCommMonoid :=
  RestrictScalars.module ℂ ℂ[G μ] (Specht μ)

def spechtRep : Representation ℂ (G μ) (SpechtSpace μ) := Representation.ofModule (Specht μ)

instance : Representation.IsIrreducible (k := ℂ) (G := G μ) (V := SpechtSpace μ) (spechtRep μ) :=
  (Representation.isSimpleModule_iff_irreducible_ofModule (Specht μ)).mp inferInstance

instance : FiniteDimensional ℂ (Specht μ) :=
  Module.Finite.of_injective ((Specht μ).subtype.restrictScalars ℂ) Subtype.val_injective

instance : FiniteDimensional ℂ (SpechtSpace μ) :=
  Module.Finite.equiv (restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm

def spechtInclude : SpechtSpace μ →ₗ[ℂ] (Tabloid μ → ℂ) :=
  (tabloidRepresentation μ).asModuleEquiv.toLinearMap.comp
    (((Specht μ).subtype.restrictScalars ℂ).comp
      (restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).toLinearMap)

lemma spechtInclude_injective : Function.Injective (spechtInclude μ) :=
  (tabloidRepresentation μ).asModuleEquiv.injective.comp
    (Subtype.val_injective.comp restrictLinearEquiv.injective)

lemma spechtInclude_rep (g : G μ) (v : SpechtSpace μ) :
    spechtInclude μ (spechtRep μ g v) = tabloidRepresentation μ g (spechtInclude μ v) := by
  change (tabloidRepresentation μ).asModuleEquiv
    ((RestrictScalars.addEquiv ℂ ℂ[G μ] (Specht μ) (Representation.ofModule (Specht μ) g v)).val) = _
  simp only [Representation.ofModule, MonoidAlgebra.lift_symm_apply,
    RestrictScalars.lsmul_apply_apply, AddEquiv.apply_symm_apply, Submodule.coe_smul_of_tower,
    Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul]
  rfl

def spechtPoly : SpechtSpace μ :=
  (restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm
    ⟨polyModule μ, polyModule_mem_Specht μ⟩

lemma spechtInclude_poly : spechtInclude μ (spechtPoly μ) = polytabloid μ := by
  change (tabloidRepresentation μ).asModuleEquiv
    ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)
      ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm
        (⟨polyModule μ, polyModule_mem_Specht μ⟩ : Specht μ))).val) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (tabloidRepresentation μ).asModuleEquiv.apply_symm_apply _

lemma spechtPoly_ne_zero : spechtPoly μ ≠ 0 := by
  intro h
  have he := congrArg (spechtInclude μ) h
  rw [map_zero, spechtInclude_poly] at he
  exact polytabloid_ne_zero μ he

end BinaryCoordinateSweeps.Young

end

end OAI
