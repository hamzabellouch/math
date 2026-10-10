import OAI.Algebra.Finitistic.Localization.SourceModelBridge
import OAI.Algebra.Finitistic.Localization.VerdierEvaluationExact

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SourceEvaluation
open QuadraticEncoding FiniteProjectiveHomotopy
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] (X : Representation P Y)

def evaluation : SourceVerdier.K P ⥤ HomotopyCategory (ModuleCat.{max u v} k) (.up ℤ) :=
  SourceModelBridge.toBounded P ⋙ boundedEvaluation X
instance : (evaluation X).Additive := by unfold evaluation; infer_instance
instance : (evaluation X).Linear k := by unfold evaluation; infer_instance
instance : (evaluation X).CommShift ℤ := by unfold evaluation; infer_instance
instance : (evaluation X).IsTriangulated := by unfold evaluation; infer_instance

def vertexIso (i : Fin 3) :
    (evaluation X).obj ((SourceVerdier.stalk P).obj (SourceVerdier.E P i)) ≅
      (vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)) :=
  (boundedEvaluation X).mapIso (SourceModelBridge.vertexIso P i) ≪≫ homotopyVertexIso X i

lemma arrow01_square (a : Fin (d+1)) :
    (evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) ≫
      (vertexIso X 1).hom = (vertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X a) := by
  have h := congrArg (fun f => (boundedEvaluation X).map f) (SourceModelBridge.vertex_arrow01 P a)
  simp only [Functor.map_comp] at h
  dsimp only [vertexIso,Iso.trans_hom,Functor.mapIso_hom,evaluation,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc,homotopy_arrow01_square,← Category.assoc]

lemma arrow12_square (a : Fin (d+1)) :
    (evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P a)) ≫
      (vertexIso X 2).hom = (vertexIso X 1).hom ≫ (vectorStalk (k := k)).map (actionArrow X a) := by
  have h := congrArg (fun f => (boundedEvaluation X).map f) (SourceModelBridge.vertex_arrow12 P a)
  simp only [Functor.map_comp] at h
  dsimp only [vertexIso,Iso.trans_hom,Functor.mapIso_hom,evaluation,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc,homotopy_arrow12_square,← Category.assoc]

lemma actionArrow_zero : actionArrow X 0 = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext y
  rfl

instance first_inverted : IsIso ((evaluation X).map (SourceVerdier.cones P).first.mor₁) := by
  change IsIso ((evaluation X).map (SourceVerdier.s P))
  have : IsIso ((evaluation X).map (SourceVerdier.s P) ≫ (vertexIso X 1).hom) := by
    change IsIso ((evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P 0)) ≫ _)
    rw [arrow01_square,actionArrow_zero,CategoryTheory.Functor.map_id,Category.comp_id]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (vertexIso X 1).hom
instance second_inverted : IsIso ((evaluation X).map (SourceVerdier.cones P).second.mor₁) := by
  change IsIso ((evaluation X).map (SourceVerdier.s' P))
  have : IsIso ((evaluation X).map (SourceVerdier.s' P) ≫ (vertexIso X 2).hom) := by
    change IsIso ((evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P 0)) ≫ _)
    rw [arrow12_square,actionArrow_zero,CategoryTheory.Functor.map_id,Category.comp_id]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (vertexIso X 2).hom

variable [FiniteDimensional k Y]
def finite : SourceVerdier.K P ⥤ FiniteVectorHomotopy.{u,v} (k := k) :=
  SourceModelBridge.toBounded P ⋙ finiteEvaluation X
instance : (finite X).Additive := by unfold finite; infer_instance
instance : (finite X).CommShift ℤ := by unfold finite; infer_instance
instance : (finite X).IsTriangulated := by unfold finite; infer_instance
instance finite_first : IsIso ((finite X).map (SourceVerdier.cones P).first.mor₁) := by
  have : IsIso ((inclusion k).map ((finite X).map (SourceVerdier.cones P).first.mor₁)) :=
    inferInstanceAs (IsIso ((evaluation X).map (SourceVerdier.cones P).first.mor₁))
  exact isIso_of_reflects_iso _ (inclusion k)
instance finite_second : IsIso ((finite X).map (SourceVerdier.cones P).second.mor₁) := by
  have : IsIso ((inclusion k).map ((finite X).map (SourceVerdier.cones P).second.mor₁)) :=
    inferInstanceAs (IsIso ((evaluation X).map (SourceVerdier.cones P).second.mor₁))
  exact isIso_of_reflects_iso _ (inclusion k)

def quotientFinite : SourceVerdier.Q P ⥤ FiniteVectorHomotopy.{u,v} (k := k) :=
  (SourceVerdier.cones P).evaluation (finite X)
def finiteFactors : SourceVerdier.q P ⋙ quotientFinite X ≅ finite X :=
  (SourceVerdier.cones P).evaluation_fac (finite X)
instance : (quotientFinite X).Additive := by
  rw [Localization.functor_additive_iff (SourceVerdier.q P) (SourceVerdier.Sigma P)]
  exact Functor.additive_of_iso (finiteFactors X).symm
instance : (quotientFinite X).CommShift ℤ := by unfold quotientFinite; infer_instance
instance : (quotientFinite X).IsTriangulated := by unfold quotientFinite; infer_instance

def quotientHomotopy : SourceVerdier.Q P ⥤ HomotopyCategory (ModuleCat.{max u v} k) (.up ℤ) :=
  quotientFinite X ⋙ inclusion k
instance : (quotientHomotopy X).Additive := by unfold quotientHomotopy; infer_instance

def homotopyFactors : SourceVerdier.q P ⋙ quotientHomotopy X ≅ evaluation X :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (finiteFactors X) (inclusion k)
instance : Localization.Lifting (SourceVerdier.q P) (SourceVerdier.Sigma P)
    (evaluation X) (quotientHomotopy X) := ⟨homotopyFactors X⟩
instance : (quotientHomotopy X).Linear k :=
  (Localization.functor_linear_iff (SourceVerdier.q P) (SourceVerdier.Sigma P) k
    (evaluation X) (quotientHomotopy X)).mp inferInstance

def quotientVertexIso (i : Fin 3) :
    (quotientHomotopy X).obj (SourceQuotientAction.vertex P i) ≅
      (vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y)) :=
  (homotopyFactors X).app ((SourceVerdier.stalk P).obj (SourceVerdier.E P i)) ≪≫ vertexIso X i

lemma quotient_arrow01_square (a : Fin (d+1)) :
    (quotientHomotopy X).map (SourceQuotientAction.a01 P a) ≫ (quotientVertexIso X 1).hom =
      (quotientVertexIso X 0).hom ≫ (vectorStalk (k := k)).map (actionArrow X a) := by
  have h := (homotopyFactors X).hom.naturality ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a))
  have h' : (quotientHomotopy X).map (SourceQuotientAction.a01 P a) ≫
      ((homotopyFactors X).app ((SourceVerdier.stalk P).obj (SourceVerdier.E P 1))).hom =
    ((homotopyFactors X).app ((SourceVerdier.stalk P).obj (SourceVerdier.E P 0))).hom ≫
      (evaluation X).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) := h
  dsimp only [quotientVertexIso,Iso.trans_hom]
  rw [← Category.assoc,h',Category.assoc,arrow01_square,← Category.assoc]

def derived : SourceVerdier.Q P ⥤ FiniteVectorDerived.{u,v} (k := k) :=
  quotientFinite X ⋙ (derivedEmbedding k).toEssImage
instance : (derived X).Additive := by unfold derived; infer_instance
instance : (derived X).CommShift ℤ := by unfold derived; infer_instance
instance : (derived X).IsTriangulated := by unfold derived; infer_instance

def derivedVertexIso (i : Fin 3) :
    (derived X ⋙ derivedTargetInclusion (k := k)).obj (SourceQuotientAction.vertex P i) ≅
      DerivedCategory.Qh.obj ((vectorStalk (k := k)).obj (ModuleCat.of k (ULift.{u} Y))) :=
  DerivedCategory.Qh.mapIso (quotientVertexIso X i)
end LittleFinitistic.SourceEvaluation

end

end OAI
