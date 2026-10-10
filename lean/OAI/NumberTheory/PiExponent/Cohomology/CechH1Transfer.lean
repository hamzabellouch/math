import OAI.NumberTheory.PiExponent.Cohomology.CechOneConverse

namespace OAI

namespace PiExponent.GeometrySupport.CechH1Transfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X Y : Scheme.{u}} {J : Type u}

private abbrev schemeFreeOpen (Z : Scheme.{u}) (U : Z.Opens) : Z.Modules :=
  freeOpen Z.ringCatSheaf U

private abbrev schemeUnit (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

@[instance_reducible] private def freeOpenHomAddCommGroup
    (Z : Scheme.{u}) (U : Z.Opens) (M : Z.Modules) :
    AddCommGroup (freeOpen Z.ringCatSheaf U ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen Z U ⟶ M))

@[instance_reducible] private def higherCochainAddCommGroup
    (Z : Scheme.{u}) (U : J → Z.Opens) (M : Z.Modules) (q : ℕ) :
    AddCommGroup (CechHigher.Cochain Z.ringCatSheaf U M q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen Z (intersection U t) ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup
  PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

structure SectionComparison (U : J → X.Opens) (V : J → Y.Opens)
    (M : X.Modules) (N : Y.Modules) where
  vertex : ∀ t : Fin 1 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) ≃+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  pair : ∀ t : Fin 2 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) →+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  triple : ∀ t : Fin 3 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) →+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  pair_injective : ∀ t, Function.Injective (pair t)
  pair_restrict : ∀ (t : Fin 2 → J) (k : Fin 2) b,
    pair t (restrictHom X.ringCatSheaf (faceLE U t k) b) =
      restrictHom Y.ringCatSheaf (faceLE V t k) (vertex (t ∘ k.succAbove) b)
  triple_restrict : ∀ (t : Fin 3 → J) (k : Fin 3) b,
    triple t (restrictHom X.ringCatSheaf (faceLE U t k) b) =
      restrictHom Y.ringCatSheaf (faceLE V t k) (pair (t ∘ k.succAbove) b)

namespace SectionComparison
variable {U : J → X.Opens} {V : J → Y.Opens} {M : X.Modules} {N : Y.Modules}
    (P : SectionComparison U V M N)

def cochainZero : CechHigher.Cochain X.ringCatSheaf U M 0 ≃+
    CechHigher.Cochain Y.ringCatSheaf V N 0 where
  toFun b t := P.vertex t (b t)
  invFun b t := (P.vertex t).symm (b t)
  left_inv b := by funext t; exact (P.vertex t).symm_apply_apply _
  right_inv b := by funext t; exact (P.vertex t).apply_symm_apply _
  map_add' b c := by funext t; exact map_add (P.vertex t) _ _

def cochainOne : CechHigher.Cochain X.ringCatSheaf U M 1 →+
    CechHigher.Cochain Y.ringCatSheaf V N 1 where
  toFun b t := P.pair t (b t)
  map_zero' := by funext t; exact map_zero (P.pair t)
  map_add' b c := by funext t; exact map_add (P.pair t) _ _

def cochainTwo : CechHigher.Cochain X.ringCatSheaf U M 2 →+
    CechHigher.Cochain Y.ringCatSheaf V N 2 where
  toFun b t := P.triple t (b t)
  map_zero' := by funext t; exact map_zero (P.triple t)
  map_add' b c := by funext t; exact map_add (P.triple t) _ _

theorem cochainOne_injective : Function.Injective P.cochainOne := by
  intro a b h
  funext t
  exact P.pair_injective t (congrFun h t)

theorem map_differential_zero (b : CechHigher.Cochain X.ringCatSheaf U M 0) :
    P.cochainOne (differential X.ringCatSheaf U M b) =
      differential Y.ringCatSheaf V N (P.cochainZero b) := by
  funext t
  change P.pair t (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
    restrictHom X.ringCatSheaf (faceLE U t k) (b (t ∘ k.succAbove))) = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.pair_restrict]
  rfl

theorem map_differential_one (b : CechHigher.Cochain X.ringCatSheaf U M 1) :
    P.cochainTwo (differential X.ringCatSheaf U M b) =
      differential Y.ringCatSheaf V N (P.cochainOne b) := by
  funext t
  change P.triple t (∑ k : Fin 3, (-1 : ℤ) ^ k.val •
    restrictHom X.ringCatSheaf (faceLE U t k) (b (t ∘ k.succAbove))) = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.triple_restrict]
  rfl

include P

theorem hasPrimitives (h : CechHigher.HasPrimitives Y.ringCatSheaf V N 0) :
    CechHigher.HasPrimitives X.ringCatSheaf U M 0 := by
  intro c hc
  have hclosed : differential Y.ringCatSheaf V N (P.cochainOne c) = 0 := by
    rw [← P.map_differential_one, hc]
    exact P.cochainTwo.map_zero
  obtain ⟨b, hb⟩ := h (P.cochainOne c) hclosed
  refine ⟨P.cochainZero.symm b, ?_⟩
  apply P.cochainOne_injective
  rw [P.map_differential_zero, AddEquiv.apply_symm_apply, hb]

theorem cohomology_one_zero [IsNoetherian X] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (hcoverU : (⨆ i, U i) = ⊤)
    (hcoverV : (⨆ i, V i) = ⊤)
    (hN : ∀ z : Ext.{u+1} (C := Y.Modules) (schemeUnit Y) N 1, z = 0)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M 1) : x = 0 := by
  have hprimitive := P.hasPrimitives
    (CechOneConverse.hasPrimitives_of_cohomology_one_zero V N hcoverV hN)
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X ⊤) M 1, z = 0 := by
    apply CechHigher.ext_one_eq_zero X.ringCatSheaf U M ⊤ (fun _ => le_top)
      (by rw [hcoverU]) _ hprimitive
    intro t z
    have he : intersection U t = U (t 0) := by
      apply le_antisymm (iInf_le _ 0)
      apply le_iInf
      intro i
      exact le_of_eq (congrArg (fun j => U (t j)) (Subsingleton.elim 0 i))
    have ha : IsAffineOpen (intersection U t) := he.symm ▸ hU (t 0)
    exact PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
      (intersection U t) ha M 0 z
  let e : schemeFreeOpen X ⊤ ≅ schemeUnit X :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf
  have h := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add 1))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add 1)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end SectionComparison
end
end PiExponent.GeometrySupport.CechH1Transfer

end OAI
