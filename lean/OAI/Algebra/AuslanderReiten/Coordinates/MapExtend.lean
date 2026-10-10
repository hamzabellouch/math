import OAI.Algebra.AuslanderReiten.Resolutions.ProjectiveResolutionFunctor

namespace OAI

noncomputable section
open CategoryTheory Category Limits ZeroObject HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

def mapExtendXIso (K : HomologicalComplex C c) : ∀ i : Option ι,
    extend.X ((F.mapHomologicalComplex c).obj K) i ≅ F.obj (extend.X K i)
  | some _ => Iso.refl _
  | none => (F.mapZeroObject).symm

theorem mapExtendXIso_d (K : HomologicalComplex C c) (i j : Option ι) :
    (mapExtendXIso F K i).hom ≫ F.map (extend.d K i j) =
      extend.d ((F.mapHomologicalComplex c).obj K) i j ≫
        (mapExtendXIso F K j).hom := by
  cases i with
  | none => exact (isZero_zero D).eq_of_src _ _
  | some i =>
    cases j with
    | none =>
      change (𝟙 (F.obj (K.X i))) ≫ F.map (0 : K.X i ⟶ (0 : C)) =
        (0 : F.obj (K.X i) ⟶ (0 : D)) ≫ (F.mapZeroObject).inv
      simp
    | some j =>
      change (𝟙 (F.obj (K.X i))) ≫ F.map (K.d i j) =
        F.map (K.d i j) ≫ (𝟙 (F.obj (K.X j)))
      simp

def mapExtendIso (K : HomologicalComplex C c) (e : c.Embedding c') :
    ((F.mapHomologicalComplex c).obj K).extend e ≅
      (F.mapHomologicalComplex c').obj (K.extend e) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => mapExtendXIso F K (e.r i))
    (fun i j _ => mapExtendXIso_d F K (e.r i) (e.r j))

theorem mapExtendXIso_hom_XIso (K : HomologicalComplex C c) {i : Option ι} {j : ι}
    (h : i = some j) :
    (mapExtendXIso F K i).hom ≫ F.map (extend.XIso K h).hom =
      (extend.XIso ((F.mapHomologicalComplex c).obj K) h).hom := by
  subst i
  change 𝟙 (F.obj (K.X j)) ≫ F.map (𝟙 (K.X j)) = 𝟙 (F.obj (K.X j))
  simp

theorem mapExtendXIso_natural {K L : HomologicalComplex C c} (f : K ⟶ L) (i : Option ι) :
    extend.mapX ((F.mapHomologicalComplex c).map f) i ≫ (mapExtendXIso F L i).hom =
      (mapExtendXIso F K i).hom ≫ F.map (extend.mapX f i) := by
  cases i with
  | none => exact (isZero_zero D).eq_of_src _ _
  | some i =>
    change F.map (f.f i) ≫ (𝟙 (F.obj (L.X i))) =
      (𝟙 (F.obj (K.X i))) ≫ F.map (f.f i)
    simp

theorem mapExtendIso_natural {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') :
    extendMap ((F.mapHomologicalComplex c).map f) e ≫ (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫ (F.mapHomologicalComplex c').map (extendMap f e) := by
  ext i
  exact mapExtendXIso_natural F f (e.r i)

end ArExplicit.ResolutionProducts

end

end OAI
