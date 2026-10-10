import OAI.Algebra.Finitistic.Localization.TwoDegreeSplitting
import OAI.Algebra.Finitistic.Localization.DiagramEvaluationSquares

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding DerivedTruncation DerivedCategory
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (X Y : D.{u,v} P) (hX : TwoDegrees X) (hY : TwoDegrees Y) (f : X ⟶ Y)

lemma upperIso_naturality :
    (DerivedTruncation.t.truncGE 0).map f ≫ (upperIso P Y hY).hom =
      (upperIso P X hX).hom ≫ (singleFunctor (C P) 0).map ((homologyFunctor (C P) 0).map f) := by
  have := upper_isLE X hX
  have := upper_isLE Y hY
  let px := upperHomologyIso X 0 (by omega)
  let py := upperHomologyIso Y 0 (by omega)
  have hp : (homologyFunctor (C P) 0).map f ≫ py.hom =
      px.hom ≫ (homologyFunctor (C P) 0).map ((DerivedTruncation.t.truncGE 0).map f) := by
    have h₀ : f ≫ DerivedTruncation.projection Y = DerivedTruncation.projection X ≫
        (DerivedTruncation.t.truncGE 0).map f := (DerivedTruncation.t.truncGEπ 0).naturality f
    have h := congrArg (homologyFunctor (C P) 0).map h₀
    dsimp only [px,py,upperHomologyIso,asIso]
    simpa only [Functor.map_comp] using h
  have hn : (homologyFunctor (C P) 0).map ((DerivedTruncation.t.truncGE 0).map f) ≫ py.inv =
      px.inv ≫ (homologyFunctor (C P) 0).map f := by
    apply (cancel_epi px.hom).mp
    rw [← Category.assoc,← hp,Category.assoc,Iso.hom_inv_id,Category.comp_id,Iso.hom_inv_id_assoc]
  have hs := congrArg (singleFunctor (C P) 0).map hn
  simp only [Functor.map_comp] at hs
  exact DiagramEvaluationSquares.compose _ _ _
    (canonicalIso 0 (upper X)) (canonicalIso 0 (upper Y))
    ((singleFunctor (C P) 0).mapIso px.symm) ((singleFunctor (C P) 0).mapIso py.symm)
    (canonicalIso_naturality 0 _) hs

lemma lowerIso_naturality :
    (DerivedTruncation.t.truncLT 0).map f ≫ (lowerIso P Y hY).hom =
      (lowerIso P X hX).hom ≫
        ((singleFunctor (C P) 0).map ((homologyFunctor (C P) (-3)).map f))⟦(3 : ℤ)⟧' := by
  have := lower_isLE X hX
  have := lower_isGE X hX
  have := lower_isLE Y hY
  have := lower_isGE Y hY
  let ix := lowerHomologyIso X (-3) (by omega)
  let iy := lowerHomologyIso Y (-3) (by omega)
  have hn : (homologyFunctor (C P) (-3)).map ((DerivedTruncation.t.truncLT 0).map f) ≫ iy.hom =
      ix.hom ≫ (homologyFunctor (C P) (-3)).map f := by
    have h₀ : (DerivedTruncation.t.truncLT 0).map f ≫ DerivedTruncation.inclusion Y =
        DerivedTruncation.inclusion X ≫ f := (DerivedTruncation.t.truncLTι 0).naturality f
    have h := congrArg (homologyFunctor (C P) (-3)).map h₀
    dsimp only [ix,iy,lowerHomologyIso,asIso]
    simpa only [Functor.map_comp] using h
  have hs := congrArg (singleFunctor (C P) (-3)).map hn
  simp only [Functor.map_comp] at hs
  let sh := ((singleFunctors (C P)).shiftIso 3 (-3) 0 (by omega)).symm
  have ht : (singleFunctor (C P) (-3)).map ((homologyFunctor (C P) (-3)).map f) ≫
      (sh.app (H P (-3) Y)).hom = (sh.app (H P (-3) X)).hom ≫
        ((singleFunctor (C P) 0).map ((homologyFunctor (C P) (-3)).map f))⟦(3 : ℤ)⟧' :=
    sh.hom.naturality _
  have hm := DiagramEvaluationSquares.compose _ _ _
    (canonicalIso (-3) (lower X)) (canonicalIso (-3) (lower Y))
    ((singleFunctor (C P) (-3)).mapIso ix) ((singleFunctor (C P) (-3)).mapIso iy)
    (canonicalIso_naturality (-3) ((DerivedTruncation.t.truncLT 0).map f)) hs
  have hh := DiagramEvaluationSquares.compose _ _ _
    (canonicalIso (-3) (lower X) ≪≫ (singleFunctor (C P) (-3)).mapIso ix)
    (canonicalIso (-3) (lower Y) ≪≫ (singleFunctor (C P) (-3)).mapIso iy)
    (sh.app (H P (-3) X)) (sh.app (H P (-3) Y)) hm ht
  dsimp only [Iso.trans] at hh
  dsimp only [lowerIso,Iso.trans]
  simpa only [ix,iy,sh,Category.assoc] using hh
end LittleFinitistic.TwoDegreeFormality

end

end OAI
