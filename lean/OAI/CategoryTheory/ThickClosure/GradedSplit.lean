import OAI.CategoryTheory.ThickClosure.CyclicTriangle
import OAI.CategoryTheory.ThickClosure.PeriodicDual

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.GradedSplit
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived
open HahnWilson.Unroll
universe u v w
variable (R : Type u) [Ring R] (D : ℕ)

instance : (Unroll.functor R D).Additive where
  map_add := by intros; rfl

abbrev dg (V : ZMod D → ModuleCat.{u} R) := diagonalComplex V
abbrev dgProd (V L : ZMod D → ModuleCat.{u} R) :=
  dg R D (fun i => ModuleCat.of R (V i × L i))

def pV (V L : ZMod D → ModuleCat.{u} R) : dgProd R D V L ⟶ dg R D V where
  f i := ModuleCat.ofHom (LinearMap.fst R (V i) (L i))
  comm' := by intros; simp [dgProd, dg, diagonalComplex, ChainComplex.of.d]
def pL (V L : ZMod D → ModuleCat.{u} R) : dgProd R D V L ⟶ dg R D L where
  f i := ModuleCat.ofHom (LinearMap.snd R (V i) (L i))
  comm' := by intros; simp [dgProd, dg, diagonalComplex, ChainComplex.of.d]
def iV (V L : ZMod D → ModuleCat.{u} R) : dg R D V ⟶ dgProd R D V L where
  f i := ModuleCat.ofHom (LinearMap.inl R (V i) (L i))
  comm' := by intros; simp [dgProd, dg, diagonalComplex, ChainComplex.of.d]
def iL (V L : ZMod D → ModuleCat.{u} R) : dg R D L ⟶ dgProd R D V L where
  f i := ModuleCat.ofHom (LinearMap.inr R (V i) (L i))
  comm' := by intros; simp [dgProd, dg, diagonalComplex, ChainComplex.of.d]

@[simp] lemma iV_pV (V L : ZMod D → ModuleCat.{u} R) : iV R D V L ≫ pV R D V L = 𝟙 _ := by ext; rfl
@[simp] lemma iL_pL (V L : ZMod D → ModuleCat.{u} R) : iL R D V L ≫ pL R D V L = 𝟙 _ := by ext; rfl
@[simp] lemma iV_pL (V L : ZMod D → ModuleCat.{u} R) : iV R D V L ≫ pL R D V L = 0 := by ext; rfl
@[simp] lemma iL_pV (V L : ZMod D → ModuleCat.{u} R) : iL R D V L ≫ pV R D V L = 0 := by ext; rfl
lemma decomp (V L : ZMod D → ModuleCat.{u} R) :
    pL R D V L ≫ iL R D V L + pV R D V L ≫ iV R D V L = 𝟙 _ := by
  apply Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨v,l⟩
  change (0,l) + (v,0) = (v,l)
  simp

def diagonalHomologyIso (V : ZMod D → ModuleCat.{u} R) (i : ZMod D) :
    (diagonalComplex V).homology i ≅ V i :=
  (ShortComplex.LeftHomologyData.ofZeros ((diagonalComplex V).sc i)
    (diagonalComplex_d V _ _) (diagonalComplex_d V _ _)).homologyIso

variable [HasDerivedCategory.{v} (ModuleCat.{u} R)]

abbrev F₀ := Unroll.functor R D ⋙ DerivedCategory.Q

noncomputable def splitIso (V L : ZMod D → ModuleCat.{u} R) :
    (F₀ R D).obj (dgProd R D V L) ≅
      (F₀ R D).obj (dg R D L) ⊞ (F₀ R D).obj (dg R D V) where
  hom := biprod.lift ((F₀ R D).map (pL R D V L)) ((F₀ R D).map (pV R D V L))
  inv := biprod.desc ((F₀ R D).map (iL R D V L)) ((F₀ R D).map (iV R D V L))
  hom_inv_id := by
    rw [biprod.lift_desc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add,
      decomp]
    exact (F₀ R D).map_id _
  inv_hom_id := by
    ext <;> simp [← Functor.map_comp]

@[reassoc] lemma iL_splitIso (V L : ZMod D → ModuleCat.{u} R) :
    (F₀ R D).map (iL R D V L) ≫ (splitIso R D V L).hom = biprod.inl := by
  ext <;> simp [splitIso, ← Functor.map_comp]
@[reassoc] lemma splitIso_pV (V L : ZMod D → ModuleCat.{u} R) :
    (splitIso R D V L).hom ≫ biprod.snd = (F₀ R D).map (pV R D V L) := by
  exact biprod.lift_snd _ _

lemma splitTriangle (V L : ZMod D → ModuleCat.{u} R) :
    Triangle.mk ((F₀ R D).map (iL R D V L)) ((F₀ R D).map (pV R D V L)) 0 ∈
      distTriang (DerivedCategory (ModuleCat.{u} R)) := by
  apply isomorphic_distinguished _ (binaryBiproductTriangle_distinguished _ _)
  exact Triangle.isoMk _ _ (Iso.refl _) (splitIso R D V L) (Iso.refl _)
    (by
      change (F₀ R D).map (iL R D V L) ≫ (splitIso R D V L).hom = 𝟙 _ ≫ biprod.inl
      exact (iL_splitIso R D V L).trans (Category.id_comp _).symm)
    (by
      change (F₀ R D).map (pV R D V L) ≫ 𝟙 _ = (splitIso R D V L).hom ≫ biprod.snd
      exact (Category.comp_id _).trans (splitIso_pV R D V L).symm)
    (by
      change (0 : (F₀ R D).obj (dg R D V) ⟶ ((F₀ R D).obj (dg R D L))⟦(1:ℤ)⟧) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1:ℤ)).map (𝟙 ((F₀ R D).obj (dg R D L))) =
        (𝟙 ((F₀ R D).obj (dg R D V))) ≫ 0
      exact (CategoryTheory.Limits.zero_comp).trans (CategoryTheory.Limits.comp_zero).symm)

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

def derivedDiagonalHomologyIso (V : ZMod D → ModuleCat.{u} R) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      ((derivedFunctor R D).obj ((Q R D).obj (diagonalComplex V))) ≅ V (-(n : ZMod D)) :=
  (derivedHomologyIso R D n).app _ ≪≫
    (HomologicalComplexUpToQuasiIso.homologyFunctorFactors (ModuleCat.{u} R)
      (.down (ZMod D)) (-(n : ZMod D))).app _ ≪≫
    diagonalHomologyIso R D V _

def F₀DiagonalHomologyIso (V : ZMod D → ModuleCat.{u} R) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      ((F₀ R D).obj (diagonalComplex V)) ≅ V (-(n : ZMod D)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso ((derivedFactors R D).symm.app _) ≪≫
    derivedDiagonalHomologyIso R D V n

end HahnWilson.GradedSplit

end

end OAI
