import OAI.CategoryTheory.ThickClosure.CyclicStructure

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.Unroll
universe u
variable (R : Type u) [Ring R] (D : ℕ)
abbrev PC := ChainComplex (ModuleCat.{u} R) (ZMod D)

def obj (P : PC R D) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun n : ℤ => P.X (-(n : ZMod D)))
    (fun n => P.d (-(n : ZMod D)) (-((n + 1 : ℤ) : ZMod D)))
    (fun _ => P.d_comp_d _ _ _)

def map {P Q : PC R D} (f : P ⟶ Q) : obj R D P ⟶ obj R D Q :=
  CochainComplex.ofHom (fun n => f.f (-(n : ZMod D))) (by
    intro n
    simpa only [obj, CochainComplex.of_d] using
      (f.comm (-(n : ZMod D)) (-((n + 1 : ℤ) : ZMod D))))

def functor : PC R D ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj := obj R D
  map := map R D
  map_id P := by ext n; rfl
  map_comp f g := by ext n; rfl

def scIso (n : ℤ) : functor R D ⋙
    shortComplexFunctor' (ModuleCat.{u} R) (.up ℤ) (n-1) n (n+1) ≅
    shortComplexFunctor' (ModuleCat.{u} R) (.down (ZMod D))
      (-((n-1 : ℤ) : ZMod D)) (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D)) := by
  refine NatIso.ofComponents (fun P => ?_) ?_
  · refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simp [shortComplexFunctor', functor, obj, CochainComplex.of.d]
    · simp [shortComplexFunctor', functor, obj, CochainComplex.of.d]
  · intro P Q f
    apply ShortComplex.hom_ext <;> simp [functor, map, ShortComplex.isoMk, shortComplexFunctor', obj]

def homologyIso (n : ℤ) :
    functor R D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n ≅
     HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) (-(n : ZMod D)) :=
  Functor.isoWhiskerLeft (functor R D)
    (homologyFunctorIso' (ModuleCat.{u} R) (.up ℤ) (n-1) n (n+1) (by simp) (by simp)) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (scIso R D n) _ ≪≫
  (homologyFunctorIso' (ModuleCat.{u} R) (.down (ZMod D))
    (-((n-1 : ℤ) : ZMod D)) (-(n : ZMod D)) (-((n+1 : ℤ) : ZMod D))
    (by simp; abel) (by simp; abel)).symm

theorem homology_iso (n : ℤ) : Nonempty
    (functor R D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n ≅
     HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) (-(n : ZMod D))) :=
  ⟨homologyIso R D n⟩

theorem map_quasiIso {P Q : PC R D} (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso ((functor R D).map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let e := homologyIso R D n
  let F := functor R D ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n
  let G := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) (-(n : ZMod D))
  change IsIso (F.map f)
  have h : F.map f ≫ (e.app Q).hom = (e.app P).hom ≫ G.map f := e.hom.naturality f
  have : IsIso (G.map f) := inferInstanceAs (IsIso (homologyMap f (-(n : ZMod D))))
  have : IsIso (F.map f ≫ (e.app Q).hom) := h.symm ▸ inferInstance
  exact (isIso_comp_right_iff (F.map f) (e.app Q).hom).mp inferInstance

end HahnWilson.Unroll

end

end OAI
