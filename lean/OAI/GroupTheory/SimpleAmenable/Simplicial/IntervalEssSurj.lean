import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PolygonPositionalMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalExtension
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalFunctor

namespace OAI

section

section

open CategoryTheory MonoidalCategory
universe u v u' v'
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]

noncomputable instance mapEssSurj (F : C ⥤ D) [F.Monoidal] [F.EssSurj] (n : ℕ) :
    (map (I:=Fin (n+1)) F).EssSurj where
  mem_essImage X := by
    let Y : Fin n → C := fun i => F.objPreimage ((eval n).obj X i)
    let A := (eval (C:=C) n).objPreimage Y
    let e := (eval (C:=C) n).objObjPreimageIso Y
    let f : (eval n).obj ((map F).obj A) ⟶ (eval n).obj X := fun i =>
      F.map (e.hom i) ≫ (F.objObjPreimageIso ((eval n).obj X i)).hom
    exact ⟨A,⟨asIso (extend f)⟩⟩

noncomputable instance map₃EssSurj (F : C ⥤ D) [F.Braided] [F.EssSurj] (l m n : ℕ) :
    (map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F))).EssSurj :=
  inferInstance

end IntervalBar.Diagram

end

section

open CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject

noncomputable instance positional_isIso {a : ℕ} {U V : PositionalCategory a} (f : U ⟶ V) : IsIso f := by
  refine ⟨⟨⟨CategoryTheory.inv f.hom,positional_inv f.property⟩,?_,?_⟩⟩
  · apply WideSubcategory.hom_ext
    exact IsIso.hom_inv_id f.hom
  · apply WideSubcategory.hom_ext
    exact IsIso.inv_hom_id f.hom

noncomputable instance positional_groupoid (a : ℕ) : Groupoid (PositionalCategory a) :=
  Groupoid.ofIsIso (fun _ => inferInstance)

noncomputable abbrev positionalInclusion (a : ℕ) := wideSubcategoryInclusion (positionalProperty a)

noncomputable instance positionalInclusionMonoidal (a : ℕ) : (positionalInclusion a).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; simp
    μIso_hom_natural_right := by intros; simp
    associativity := by intros; simp
    left_unitality := by intros; simp
    right_unitality := by intros; simp }

noncomputable instance positionalInclusionBraided (a : ℕ) : (positionalInclusion a).Braided where
  braided _ _ := by simp; rfl

instance positionalInclusionEssSurj (a : ℕ) : (positionalInclusion a).EssSurj where
  mem_essImage U := ⟨⟨U⟩,⟨Iso.refl U⟩⟩

open IntervalBar IntervalBar.Diagram

abbrev TripleBars (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
    (l m n : ℕ) := Diagram (Diagram (Diagram C (Fin (n+1))) (Fin (m+1))) (Fin (l+1))

noncomputable def positionalOneBarMap (a n : ℕ) :
    Diagram (PositionalCategory a) (Fin (n+1)) ⥤ Diagram (PolygonObject a) (Fin (n+1)) :=
  Diagram.map (positionalInclusion a)

noncomputable instance positionalOneBarBraided (a n : ℕ) : (positionalOneBarMap a n).Braided :=
  Diagram.mapBraided (positionalInclusion a)

noncomputable instance positionalOneBarEssSurj (a n : ℕ) : (positionalOneBarMap a n).EssSurj :=
  Diagram.mapEssSurj (positionalInclusion a) n

noncomputable def positionalTwoBarMap (a m n : ℕ) :
    Diagram (Diagram (PositionalCategory a) (Fin (n+1))) (Fin (m+1)) ⥤
      Diagram (Diagram (PolygonObject a) (Fin (n+1))) (Fin (m+1)) :=
  Diagram.map (positionalOneBarMap a n)

noncomputable instance positionalTwoBarBraided (a m n : ℕ) : (positionalTwoBarMap a m n).Braided :=
  Diagram.mapBraided (positionalOneBarMap a n)

noncomputable instance positionalTwoBarEssSurj (a m n : ℕ) : (positionalTwoBarMap a m n).EssSurj :=
  Diagram.mapEssSurj (positionalOneBarMap a n) m

noncomputable def positionalBarMap (a l m n : ℕ) :
    TripleBars (PositionalCategory a) l m n ⥤ TripleBars (PolygonObject a) l m n :=
  Diagram.map (positionalTwoBarMap a m n)

noncomputable instance positionalBarMapEssSurj (a l m n : ℕ) :
    (positionalBarMap a l m n).EssSurj := Diagram.mapEssSurj (positionalTwoBarMap a m n) l

abbrev PositionalBars (a l m n : ℕ) :=
  InducedCategory (TripleBars (PolygonObject a) l m n) (positionalBarMap a l m n).obj

noncomputable def positionalBarInclusion (a l m n : ℕ) :
    PositionalBars a l m n ⥤ TripleBars (PolygonObject a) l m n :=
  inducedFunctor (positionalBarMap a l m n).obj

noncomputable instance positionalBarInclusionEssSurj (a l m n : ℕ) :
    (positionalBarInclusion a l m n).EssSurj where
  mem_essImage X := ⟨(positionalBarMap a l m n).objPreimage X,
    ⟨(positionalBarMap a l m n).objObjPreimageIso X⟩⟩

noncomputable instance positionalBarInclusionEquivalence (a l m n : ℕ) :
    (positionalBarInclusion a l m n).IsEquivalence where
  full := inferInstanceAs (inducedFunctor _).Full
  faithful := inferInstanceAs (inducedFunctor _).Faithful

end SimpleAmenable.PolygonObject

end

end

end OAI
