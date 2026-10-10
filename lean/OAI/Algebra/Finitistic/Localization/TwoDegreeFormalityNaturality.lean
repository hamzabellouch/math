import OAI.Algebra.Finitistic.Localization.TruncationSplitNaturality
import OAI.Algebra.Finitistic.Localization.TruncationStalkNaturality

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding DerivedTruncation DerivedCategory
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {X Y : D.{u,v} P}

abbrev modelMap (f : X ⟶ Y) :=
  biprod.map ((singleFunctor (C P) 0).map ((homologyFunctor (C P) 0).map f))
    (((singleFunctor (C P) 0).map ((homologyFunctor (C P) (-3)).map f))⟦(3 : ℤ)⟧')

lemma braiding_square {A B A' B' : D.{u,v} P} (f : A ⟶ A') (g : B ⟶ B') :
    biprod.map f g ≫ (biprod.braiding A' B').hom =
      (biprod.braiding A B).hom ≫ biprod.map g f := by
  apply biprod.hom_ext <;> simp [biprod.braiding,Category.assoc]

variable (X Y) (hX : TwoDegrees X) (hY : TwoDegrees Y) (f : X ⟶ Y)

lemma stalk_diagonal_square :
    biprod.map ((DerivedTruncation.t.truncLT 0).map f) ((DerivedTruncation.t.truncGE 0).map f) ≫
      (biprod.mapIso (lowerIso P Y hY) (upperIso P Y hY)).hom =
    (biprod.mapIso (lowerIso P X hX) (upperIso P X hX)).hom ≫
      biprod.map (((singleFunctor (C P) 0).map ((homologyFunctor (C P) (-3)).map f))⟦(3 : ℤ)⟧')
        ((singleFunctor (C P) 0).map ((homologyFunctor (C P) 0).map f)) := by
  apply biprod.hom_ext
  · simp only [biprod.mapIso_hom,Category.assoc,biprod.map_fst,biprod.map_fst_assoc,
      lowerIso_naturality P X Y hX hY f]
  · simp only [biprod.mapIso_hom,Category.assoc,biprod.map_snd,biprod.map_snd_assoc,
      upperIso_naturality P X Y hX hY f]

/-- The actual two-degree formality isomorphism is natural for all derived B-morphisms. -/
theorem splitIso_naturality :
    f ≫ (splitIso P Y hY).hom = (splitIso P X hX).hom ≫ modelMap P f := by
  have hm := DiagramEvaluationSquares.compose _ _ _
    (truncationSplit P X hX).iso (truncationSplit P Y hY).iso
    (biprod.mapIso (lowerIso P X hX) (upperIso P X hX))
    (biprod.mapIso (lowerIso P Y hY) (upperIso P Y hY))
    (truncationSplit_naturality P X Y hX hY f) (stalk_diagonal_square P X Y hX hY f)
  have hh := DiagramEvaluationSquares.compose _ _ _
      ((truncationSplit P X hX).iso ≪≫ biprod.mapIso (lowerIso P X hX) (upperIso P X hX))
      ((truncationSplit P Y hY).iso ≪≫ biprod.mapIso (lowerIso P Y hY) (upperIso P Y hY))
      (biprod.braiding _ _) (biprod.braiding _ _) hm (braiding_square P _ _)
  dsimp only [Iso.trans] at hh
  dsimp only [splitIso,Iso.trans]
  simp only [Category.assoc] at hh ⊢
  exact hh

/-- In particular every endomorphism acts diagonally by its two actual cohomology maps. -/
theorem splitIso_endomorphism (a : End X) :
    a ≫ (splitIso P X hX).hom = (splitIso P X hX).hom ≫ modelMap P a :=
  splitIso_naturality P X X hX hX a

/-- The splitting retains any specified action by derived B-linear endomorphisms. -/
theorem splitIso_action (S : Type w) [Monoid S] (rho : S →* End X) (r : S) :
    rho r ≫ (splitIso P X hX).hom = (splitIso P X hX).hom ≫ modelMap P (rho r) :=
  splitIso_endomorphism P X hX (rho r)

/-- Substitute actual B-module identifications of the two cohomology modules. -/
def splitIsoWithModels (M N : C.{u,v} P) (e0 : H P 0 X ≅ M) (em : H P (-3) X ≅ N) :
    X ≅ stalk P M ⊞ (stalk P N)⟦(3 : ℤ)⟧ :=
  splitIso P X hX ≪≫ biprod.mapIso ((singleFunctor (C P) 0).mapIso e0)
    ((shiftFunctor (D P) (3 : ℤ)).mapIso ((singleFunctor (C P) 0).mapIso em))
end LittleFinitistic.TwoDegreeFormality

end

end OAI
