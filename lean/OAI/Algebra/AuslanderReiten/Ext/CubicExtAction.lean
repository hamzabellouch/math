import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionExtAction
import OAI.Algebra.AuslanderReiten.Ext.NatCubicExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

def closedCochain {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    Cocycle P.cochainComplex ((CochainComplex.singleFunctor (ModuleCat R) 0).obj Y) (n : ℤ) :=
  Cocycle.toSingleMk ((P.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f) (by omega)
    (-((n+1 : ℕ) : ℤ)) (by omega) (by
      rw [P.cochainComplex_d _ _ (n+1) n rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hf, CategoryTheory.Limits.comp_zero])

omit [HasDerivedCategory (ModuleCat.{u} R)] in
@[simp] theorem extOf_closedCochain {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    extOfCocycle P (closedCochain P f hf) = P.extMk f (n+1) rfl hf := rfl

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
include hp

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem cubicPrecomp_closed {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    P.complex.d (n+4) (n+3) ≫ (p n ≫ f)=0 := by
  rw [← Category.assoc, ← hp n, Category.assoc, hf, CategoryTheory.Limits.comp_zero]

include k in
omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem cubicPrecomp_cochain {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    (closedCochain P (p n ≫ f) (cubicPrecomp_closed P p hp f hf)).val =
      (natCubicCocycle (k := k) P p hp).val.comp (closedCochain P f hf).val
        (by omega : (3 : ℤ)+(n : ℤ)=((n+3 : ℕ) : ℤ)) := by
  apply (Cochain.toSingleEquiv (show -((n+3 : ℕ) : ℤ)+((n+3 : ℕ) : ℤ)=0 by omega)).injective
  change (Cochain.toSingleMk ((P.cochainComplexXIso (-((n+3 : ℕ) : ℤ)) (n+3) rfl).hom ≫ p n ≫ f)
    (by omega)).v (-((n+3 : ℕ) : ℤ)) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom =
    (((natCubicCocycle (k := k) P p hp).val.comp (closedCochain P f hf).val (by omega)).v
      (-((n+3 : ℕ) : ℤ)) 0 (by omega)) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom
  rw [Cochain.toSingleMk_v]
  erw [Cochain.comp_v _ _ _ _ (-(n : ℤ)) 0 (by omega) (by omega)]
  change _ = ((natCubicCochain P p).v (-((n+3 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) ≫
    (Cochain.toSingleMk ((P.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f)
      (by omega)).v (-(n : ℤ)) 0 (by omega)) ≫ _
  rw [Cochain.toSingleMk_v]
  have h := natCubicCochain_v P p n
  rw [h]
  let e := P.cochainComplexXIso (-(n : ℤ)) n rfl
  let e₃ := P.cochainComplexXIso (-((n+3 : ℕ) : ℤ)) (n+3) rfl
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y
  exact (congrArg (fun z => ((e₃.hom ≫ p n ≫ z ≫ f) ≫ s.inv) ≫ s.hom)
    e.inv_hom_id).symm

include k in

theorem cubic_endExt_comp_extMk {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    (endExt P (natCubicCocycle (k := k) P p hp)).comp (P.extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
      P.extMk (p n ≫ f) (n+4) rfl (cubicPrecomp_closed P p hp f hf) := by
  exact endExt_comp_extOfCocycle P (n := 3) (m := n) (r := n+3) (natCubicCocycle (k := k) P p hp)
    (closedCochain P f hf)
    (closedCochain P (p n ≫ f) (cubicPrecomp_closed P p hp f hf)) (by omega)
    (cubicPrecomp_cochain (k := k) P p hp f hf)

end ArExplicit.ResolutionProducts

end

end OAI
