import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftTotal
import OAI.Algebra.Finitistic.Localization.SignedCochainShift

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
local instance signedShift (a : ℤ) :
    (shiftFunctor (CochainComplex (ModuleCat.{u} B) ℤ) a).CommShift ℤ :=
  signedShiftComm (ModuleCat.{u} B) a

instance columnCommShift (P : BiComplex k B) (a : ℤ) :
    (columnFunctor k B P a).CommShift ℤ := by unfold columnFunctor; infer_instance

variable (P : BiComplex k B)

theorem column_commShiftIso_eq (Z : CochainComplex (ModuleCat.{u} B) ℤ) (s a : ℤ) :
    ((columnFunctor k B P a).commShiftIso s).app Z = shiftColumnIso k B P Z s a := by
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext n
  rw [shiftColumn_hom_f]
  simp only [Iso.app_hom,columnFunctor,Functor.commShiftIso_comp_hom_app,
    HomologicalComplex.comp_f,CochainComplex.shiftFunctor_map_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  change ((signedShiftIso (ModuleCat.{u} B) (-a) s).hom.app
    (((inputFunctor k B (P.X a)).mapHomologicalComplex (.up ℤ)).obj Z)).f n = _
  rw [signedShiftIso_hom_f]
  simp [shiftReindex,HomologicalComplex.XIsoOfEq,mul_comm]
  rfl

variable {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}

theorem fullColumn_map (f : Z ⟶ Z') (a n : ℤ) (x : Term k B P Z a (n + -a)) :
    (((columnFunctor k B P a).map f).f n).hom x =
      ComplexTensor.inputMap k B (right k B P) f a (n + -a) x := by
  induction x using BalancedTensor.induction_on with
  | hz => exact (map_zero _).trans (map_zero _).symm
  | ht m y => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem functor_map_component (f : Z ⟶ Z') (n : ℤ)
    (x : TotalTerm k B P p Z n) (i : Fin l) :
    (((functor k B P p hp).map f).f n).hom x i =
      (((columnFunctor k B P (p i)).map f).f n).hom (x i) := by
  change ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom x i = _
  erw [ComplexTensor.finiteTotalMap_apply]
  exact (fullColumn_map k B P f (p i) n (x i)).symm

@[simp] theorem shiftTotal_hom_apply (Z : CochainComplex (ModuleCat.{u} B) ℤ) (s n : ℤ)
    (x : TotalTerm k B P p (Z⟦s⟧) n) (i : Fin l) :
    (((shiftTotalIso k B P p hp Z s).hom).f n).hom x i =
      (((shiftColumnIso k B P Z s (p i)).hom).f n).hom (x i) := rfl

/-- Naturality of the full tensor shift, in every input complex and chain map. -/
def shiftIso (s : ℤ) : shiftFunctor _ s ⋙ functor k B P p hp ≅
    functor k B P p hp ⋙ shiftFunctor _ s :=
  NatIso.ofComponents (fun Z => shiftTotalIso k B P p hp Z s) (by
    intro Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    have h := congrArg (fun g => (g.f n).hom (x i))
      (((columnFunctor k B P (p i)).commShiftIso s).hom.naturality f)
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    change (((shiftColumnIso k B P Z' s (p i)).hom).f n).hom
        ((((functor k B P p hp).map ((shiftFunctor _ s).map f)).f n).hom x i) =
      (((functor k B P p hp).map f).f (n+s)).hom
        (((shiftTotalIso k B P p hp Z s).hom.f n).hom x) i
    erw [functor_map_component,functor_map_component,shiftTotal_hom_apply]
    simp only [Functor.comp_map,Functor.comp_obj,HomologicalComplex.comp_f,ModuleCat.hom_comp,
      CochainComplex.shiftFunctor_map_f'] at h
    convert h using 1 <;> rfl)

theorem total_transport_apply (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    (n m : ℤ) (h : n = m) (x : TotalTerm k B P p Z n) (i : Fin l) :
    ((eqToHom (congrArg (fun q => (total k B P p hp Z).X q) h)).hom x) i =
      (eqToHom (congrArg (fun q => ((columnFunctor k B P (p i)).obj Z).X q) h)).hom (x i) := by
  subst m
  rfl

@[simp] theorem shiftIso_apply (Z : CochainComplex (ModuleCat.{u} B) ℤ) (s n : ℤ)
    (x : TotalTerm k B P p (Z⟦s⟧) n) (i : Fin l) :
    (((shiftIso k B P p hp s).hom.app Z).f n).hom x i =
      (((shiftColumnIso k B P Z s (p i)).hom).f n).hom (x i) := rfl

theorem shiftZero_inv_component (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    (n : ℤ) (x : TotalTerm k B P p Z n) (i : Fin l) :
    (((shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ).inv.app
      ((functor k B P p hp).obj Z)).f n).hom x i =
    (((shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ).inv.app
      ((columnFunctor k B P (p i)).obj Z)).f n).hom (x i) := by
  convert total_transport_apply k B P p hp Z n (n+0) (by omega) x i using 1
  rfl

theorem shiftAdd_inv_component (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    (s t n : ℤ) (x : TotalTerm k B P p Z (n+t+s)) (i : Fin l) :
    (((shiftFunctorAdd (CochainComplex (ModuleCat.{u} B) ℤ) s t).inv.app
      ((functor k B P p hp).obj Z)).f n).hom x i =
    (((shiftFunctorAdd (CochainComplex (ModuleCat.{u} B) ℤ) s t).inv.app
      ((columnFunctor k B P (p i)).obj Z)).f n).hom (x i) := by
  convert total_transport_apply k B P p hp Z (n+t+s) (n+(s+t)) (by omega) x i using 1
  rfl

/-- All integer shifts satisfy zero and addition coherence for the actual tensor endofunctor. -/
instance commShift : (functor k B P p hp).CommShift ℤ where
  commShiftIso := shiftIso k B P p hp
  commShiftIso_zero := by
    ext Z n x
    funext i
    have h := congrArg (fun e => ((e.hom.app Z).f n).hom (x i))
      ((columnFunctor k B P (p i)).commShiftIso_zero ℤ)
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    simp only [Iso.app_hom,Functor.CommShift.isoZero_hom_app, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, LinearMap.comp_apply] at h ⊢
    have hc := shiftZero_inv_component k B P p hp Z n
      ((((functor k B P p hp).map ((shiftFunctorZero _ ℤ).hom.app Z)).f n).hom x) i
    have hf := functor_map_component k B P p hp ((shiftFunctorZero _ ℤ).hom.app Z) n x i
    have he := hc.trans (congrArg (fun y =>
      (((shiftFunctorZero (CochainComplex (ModuleCat.{u} B) ℤ) ℤ).inv.app
        ((columnFunctor k B P (p i)).obj Z)).f n).hom y) hf)
    exact h.trans he.symm
  commShiftIso_add s t := by
    ext Z n x
    funext i
    have h := congrArg (fun e => ((e.hom.app Z).f n).hom (x i))
      ((columnFunctor k B P (p i)).commShiftIso_add s t)
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    simp only [Iso.app_hom,Functor.CommShift.isoAdd_hom_app, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, LinearMap.comp_apply,CochainComplex.shiftFunctor_map_f'] at h ⊢
    simp only [← Iso.app_hom,column_commShiftIso_eq] at h
    let y := ((((functor k B P p hp).map ((shiftFunctorAdd _ s t).hom.app Z)).f n).hom x)
    let z := (((shiftIso k B P p hp t).hom.app (Z⟦s⟧)).f n).hom y
    have hf := functor_map_component k B P p hp ((shiftFunctorAdd _ s t).hom.app Z) n x i
    have ht := shiftIso_apply k B P p hp (Z⟦s⟧) t n y i
    have hs := shiftIso_apply k B P p hp Z s (n+t) z i
    have ht' := ht.trans (congrArg (fun w => ((shiftColumnIso k B P (Z⟦s⟧) t (p i)).hom.f n).hom w) hf)
    have hs' := hs.trans (congrArg (fun w => ((shiftColumnIso k B P Z s (p i)).hom.f (n+t)).hom w) ht')
    have hc := shiftAdd_inv_component k B P p hp Z s t n
      ((((shiftIso k B P p hp s).hom.app Z).f (n+t)).hom z) i
    have he := hc.trans (congrArg (fun w =>
      (((shiftFunctorAdd (CochainComplex (ModuleCat.{u} B) ℤ) s t).inv.app
        ((columnFunctor k B P (p i)).obj Z)).f n).hom w) hs')
    exact h.trans he.symm
end LittleFinitistic.BimoduleTotal

end

end OAI
