import OAI.Algebra.Finitistic.Localization.EvaluationLinear

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.QuadraticEncoding
universe u v w z

section LinearFunctor
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable {D : Type z} [Category D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] [F.Linear k] (L : C) {T : D} (e : F.obj L ≅ T)

/-- Evaluation of endomorphisms, expressed in a specified identification of the target. -/
def identifiedEndHom : End L →ₐ[k] End T where
  toFun a := e.inv ≫ F.map a ≫ e.hom
  map_zero' := by simp
  map_add' a b := by
    change e.inv ≫ F.map ((a : L ⟶ L) + b) ≫ e.hom =
      (e.inv ≫ F.map a ≫ e.hom) + (e.inv ≫ F.map b ≫ e.hom)
    rw [F.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_one' := by simp
  map_mul' a b := by simp [End.mul_def, Functor.map_comp, Category.assoc]
  commutes' c := by
    change e.inv ≫ F.map (c • 𝟙 L) ≫ e.hom = c • 𝟙 T
    simp [Linear.comp_smul, Linear.smul_comp]
end LinearFunctor

variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

/-- Canonical transport of every endomorphism of Y to its universe lift. -/
def liftedEndHom : Module.End k Y →ₐ[k] End (ModuleCat.of k (ULift.{u} Y)) where
  toFun a := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    (a.comp ULift.moduleEquiv.toLinearMap))
  map_zero' := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  map_add' a b := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  map_one' := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  map_mul' a b := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl
  commutes' c := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro y; rfl

/-- The presented algebra acts on Y by precisely its specified generator endomorphisms. -/
def givenAction : PresentedAlgebra P →ₐ[k] Module.End k Y :=
  presentationLift P X.generator X.relation

def givenStalkAction : PresentedAlgebra P →ₐ[k]
    End ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  (identifiedEndHom (vectorStalk (k := k)) _ (Iso.refl _)).comp
    ((liftedEndHom (k := k) (Y := Y)).comp (givenAction X))

/-- The quotient action, evaluated and identified with the stalk of Y. -/
def evaluatedAction : PresentedAlgebra P →ₐ[k]
    End ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  (identifiedEndHom (boundedQuotientEvaluation X) (vertexQ P 0) (quotientVertexIso X 0)).comp
    (quotientAction P)

lemma evaluatedAction_generator (h : Fin d) :
    evaluatedAction X (presentedGenerator P h) =
      givenStalkAction X (presentedGenerator P h) := by
  change (quotientVertexIso X 0).inv ≫
    (boundedQuotientEvaluation X).map (quotientAction P (presentedGenerator P h)) ≫
      (quotientVertexIso X 0).hom = _
  rw [quotientAction_generator, normalizedGenerator_evaluates]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change (vectorStalk (k := k)).map ((liftedEndHom (k := k) (Y := Y)) (X.generator h)) =
    𝟙 _ ≫ (vectorStalk (k := k)).map ((liftedEndHom (k := k) (Y := Y))
      (givenAction X (presentedGenerator P h))) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  rw [show givenAction X (presentedGenerator P h) = X.generator h from
    presentationLift_generator P X.generator X.relation h]

/-- Section 3, lines 167–168: the entire quotient action evaluates to the given action. -/
theorem quotientAction_evaluates : evaluatedAction X = givenStalkAction X := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext h
  exact evaluatedAction_generator X h
end LittleFinitistic.QuadraticEncoding

end

end OAI
