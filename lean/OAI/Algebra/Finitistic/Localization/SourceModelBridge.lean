import OAI.Algebra.Finitistic.Localization.SourceQuotientAction
import OAI.Algebra.Finitistic.Localization.CompletedOddDoubleEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SourceModelBridge
open QuadraticEncoding FiniteProjectiveHomotopy
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

abbrev forgetProj := (ProjectiveComplexes.finiteProjective (B P)).ι
abbrev ambient : SourceVerdier.K P ⥤ HomotopyCategory (ModuleCat.{u} (B P)ᵐᵒᵖ) (.up ℤ) :=
  (BoundedHomotopy.bounded (SourceVerdier.Proj P)).ι ⋙ (forgetProj P).mapHomotopyCategory (.up ℤ)

lemma ambient_property (T : SourceVerdier.K P) : objects (B P)ᵐᵒᵖ ((ambient P).obj T) := by
  obtain ⟨a,b,ha,hb⟩ := (BoundedHomotopy.bounded_quotient_obj_iff _ _).mp T.property
  change ComplexProperty (B P)ᵐᵒᵖ (((forgetProj P).mapHomologicalComplex (.up ℤ)).obj T.obj.as)
  constructor
  · refine ⟨a,b,fun i hi => ?_⟩
    apply (forgetProj P).map_isZero
    rcases hi with hi | hi
    · exact CochainComplex.isZero_of_isStrictlyGE T.obj.as a i hi
    · exact CochainComplex.isZero_of_isStrictlyLE T.obj.as b i hi
  · intro i
    change Module.Finite (B P)ᵐᵒᵖ (T.obj.as.X i).obj ∧ Projective (T.obj.as.X i).obj
    have := (T.obj.as.X i).property.2
    exact ⟨(T.obj.as.X i).property.1,ModuleCat.projective_of_categoryTheory_projective _⟩

/-- Forgetting the projective subcategory gives actual bounded projective module complexes. -/
def toBounded : SourceVerdier.K P ⥤ BoundedK P :=
  (objects (B P)ᵐᵒᵖ).lift (ambient P) (ambient_property P)
instance : (toBounded P).Additive := by unfold toBounded; infer_instance
instance : (toBounded P).Linear k where
  map_smul := by
    intro X Y f a
    apply ObjectProperty.hom_ext
    exact (ambient P).map_smul a f
instance : (toBounded P).CommShift ℤ := by unfold toBounded; infer_instance
instance : (toBounded P).IsTriangulated := by unfold toBounded; infer_instance

abbrev rightStalk := HomotopyCategory.singleFunctor (ModuleCat.{u} (B P)ᵐᵒᵖ) 0

def stalkUnderlyingIso (M : SourceVerdier.Proj P) :
    (ambient P).obj ((SourceVerdier.stalk P).obj M) ≅ (rightStalk P).obj M.obj :=
  (HomotopyCategory.quotient _ _).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex (forgetProj P) (.up ℤ) (0 : ℤ)).app M)

lemma stalkUnderlying_square {M N : SourceVerdier.Proj P} (f : M ⟶ N) :
    (ambient P).map ((SourceVerdier.stalk P).map f) ≫ (stalkUnderlyingIso P N).hom =
      (stalkUnderlyingIso P M).hom ≫ (rightStalk P).map f.hom := by
  have h := (HomologicalComplex.singleMapHomologicalComplex
    (forgetProj P) (.up ℤ) (0 : ℤ)).hom.naturality f
  have h' := congrArg (fun g => (HomotopyCategory.quotient _ _).map g) h
  change ((forgetProj P).mapHomotopyCategory (.up ℤ)).map
    ((HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ)).map f)) ≫ _ = _
  rw [Functor.mapHomotopyCategory_map]
  simp only [Functor.map_comp, Functor.comp_map] at h'
  exact h'


def vertexIso (i : Fin 3) :
    (toBounded P).obj ((SourceVerdier.stalk P).obj (SourceVerdier.E P i)) ≅ vertexK P i :=
  (inclusion (B P)ᵐᵒᵖ).preimageIso
    (stalkUnderlyingIso P (SourceVerdier.E P i) ≪≫
      (rightStalk P).mapIso (SourceQuotientAction.vertexIso P i))

lemma vertex_arrow01 (a : Fin (d+1)) :
    (toBounded P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) ≫
      (vertexIso P 1).hom = (vertexIso P 0).hom ≫ arrowK01 P a := by
  apply (inclusion (B P)ᵐᵒᵖ).map_injective
  simp only [Functor.map_comp,vertexIso,Functor.preimageIso,Functor.map_preimage]
  change (ambient P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow01 P a)) ≫
    ((stalkUnderlyingIso P (SourceVerdier.E P 1)).hom ≫
      (rightStalk P).map (SourceQuotientAction.vertexIso P 1).hom) = _
  rw [← Category.assoc,stalkUnderlying_square,Category.assoc,← Functor.map_comp]
  have h := congrArg (fun f => f.hom ≫ (SourceQuotientAction.vertexIso P 1).hom)
    (SourceQuotientAction.nativeHom_arrow01 P a)
  dsimp [SourceQuotientAction.nativeHom] at h
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at h
  rw [← h,Functor.map_comp]
  unfold arrowK01
  erw [Functor.map_preimage]
  exact (Category.assoc _ _ _).symm

lemma vertex_arrow12 (a : Fin (d+1)) :
    (toBounded P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P a)) ≫
      (vertexIso P 2).hom = (vertexIso P 1).hom ≫ arrowK12 P a := by
  apply (inclusion (B P)ᵐᵒᵖ).map_injective
  simp only [Functor.map_comp,vertexIso,Functor.preimageIso,Functor.map_preimage]
  change (ambient P).map ((SourceVerdier.stalk P).map (SourceVerdier.arrow12 P a)) ≫
    ((stalkUnderlyingIso P (SourceVerdier.E P 2)).hom ≫
      (rightStalk P).map (SourceQuotientAction.vertexIso P 2).hom) = _
  rw [← Category.assoc,stalkUnderlying_square,Category.assoc,← Functor.map_comp]
  have h := congrArg (fun f => f.hom ≫ (SourceQuotientAction.vertexIso P 2).hom)
    (SourceQuotientAction.nativeHom_arrow12 P a)
  dsimp [SourceQuotientAction.nativeHom] at h
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id] at h
  rw [← h,Functor.map_comp]
  unfold arrowK12
  erw [Functor.map_preimage]
  exact (Category.assoc _ _ _).symm
end LittleFinitistic.SourceModelBridge

end

end OAI
