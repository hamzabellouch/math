import OAI.Algebra.Finitistic.Localization.ModuleActionCompatibility
import Mathlib.CategoryTheory.Idempotents.FunctorExtension

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
namespace LittleFinitistic.QuadraticEncoding
universe u v w
section General
variable {C : Type u} [Category.{v} C]

/-- An actual splitting realizes the corresponding formal Karoubi object. -/
def splitKaroubiIso {A I : C} (p : A ⟶ A) (hp : p ≫ p = p)
    (π : A ⟶ I) (ι : I ⟶ A) (hπι : π ≫ ι = p) (hιπ : ι ≫ π = 𝟙 I) :
    (⟨A,p,hp⟩ : Karoubi C) ≅ (toKaroubi C).obj I where
  hom := ⟨π, by simp only [toKaroubi_obj_p]; rw [← hπι]; simp [Category.assoc,hιπ]⟩
  inv := ⟨ι, by simp only [toKaroubi_obj_p]; rw [← hπι]; simp [← Category.assoc,hιπ]⟩
  hom_inv_id := by ext; exact hπι
  inv_hom_id := by ext; exact hιπ

/-- An isomorphism commuting with idempotents identifies their formal summands. -/
def transportKaroubiIso (A B : Karoubi C) (e : A.X ≅ B.X)
    (h : A.p ≫ e.hom = e.hom ≫ B.p) : A ≅ B where
  hom := ⟨A.p ≫ e.hom, by
    simp only [← Category.assoc, A.idem]
    rw [h, Category.assoc, B.idem]⟩
  inv := ⟨e.inv ≫ A.p, by
    have hi : B.p ≫ e.inv = e.inv ≫ A.p := by
      apply (cancel_mono e.hom).mp
      simpa [Category.assoc] using congrArg (fun f => e.inv ≫ f) h.symm
    simp [← hi, Category.assoc]⟩
  hom_inv_id := by ext; simp [Category.assoc]
  inv_hom_id := by
    ext
    simp only [Karoubi.comp_f, Karoubi.id_f, Category.assoc]
    rw [← Category.assoc A.p A.p, A.idem, h]
    simp
end General

variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

def karoubiEvaluation : Karoubi (BoundedQ P) ⥤
    Karoubi (HomotopyCategory (ModuleCat.{max u v} k) (.up ℤ)) :=
  (functorExtension₂ _ _).obj (boundedQuotientEvaluation X)

def quotientSummand (r : PresentedAlgebra P) (hr : r*r=r) : Karoubi (BoundedQ P) :=
  ⟨vertexQ P 0, quotientAction P r, by
    change (quotientAction P r) * (quotientAction P r) = quotientAction P r
    rw [← map_mul, hr]⟩

def stalkSummand (r : PresentedAlgebra P) (hr : r*r=r) :
    Karoubi (HomotopyCategory (ModuleCat.{max u v} k) (.up ℤ)) :=
  ⟨(vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)),
    givenStalkAction X r, by
      change (givenStalkAction X r) * (givenStalkAction X r) = givenStalkAction X r
      rw [← map_mul, hr]⟩

/-- The evaluated formal summand has precisely the idempotent induced by r on Y. -/
def evaluatedSummandIso (r : PresentedAlgebra P) (hr : r*r=r) :
    (karoubiEvaluation X).obj (quotientSummand r hr) ≅ stalkSummand X r hr :=
  transportKaroubiIso _ _ (quotientVertexIso X 0) (by
    change (boundedQuotientEvaluation X).map (quotientAction P r) ≫
      (quotientVertexIso X 0).hom = (quotientVertexIso X 0).hom ≫
        (𝟙 _ ≫ (vectorStalk (k := k)).map (liftedEndHom (givenAction X r)) ≫ 𝟙 _)
    simpa using quotientAction_square X r)
end LittleFinitistic.QuadraticEncoding

end

end OAI
