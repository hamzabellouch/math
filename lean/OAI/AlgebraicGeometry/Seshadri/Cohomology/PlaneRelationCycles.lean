import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.TripleComplex
import OAI.AlgebraicGeometry.Seshadri.Cohomology.PlanePairToric
import OAI.AlgebraicGeometry.Seshadri.Cohomology.TripleEvaluation

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance planeRelationCyclesLinear : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) :=
  sheafLinear X
attribute [local instance] baseHomModule

def basePrecomp (k : K →+* Γ(X,⊤)) {A B : X.Modules} (M : X.Modules) (f : A ⟶ B) :
    BaseHom k B M →ₗ[K] BaseHom k A M where
  toFun g := f ≫ g
  map_add' := Preadditive.comp_add (C := X.Modules) _ _ _ f
  map_smul' r g := Linear.comp_smul _ _ _ f (k r) g

abbrev planeRelations {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) : X.Modules :=
  tripleRelations X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
abbrev planeVertices {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) : X.Modules :=
  tripleVertices X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
abbrev planeRelIota {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) :
    planeRelations s ⟶ planeVertices s :=
  kernel.ι (tripleG X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2)))
abbrev planeRelPi {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) :
    (show X.Modules from triplePairs X.ringCatSheaf (SectionOpens.isoOpen (s 0))
      (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))) ⟶ planeRelations s :=
  tripleToRelations X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))

def relationA (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 0 1 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 0) (planeTriple_le s 1))).comp
    (basePrecomp k L.sheaf (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)
def relationB (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 0 2 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 0) (planeTriple_le s 2))).comp
    (basePrecomp k L.sheaf (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
      biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)
def relationC (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 1 2 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 1) (planeTriple_le s 2))).comp
    (basePrecomp k L.sheaf (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
      biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)

def relationCycles (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K]
      cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2) :=
  ((relationA k s L).prod ((relationB k s L).prod (relationC k s L))).codRestrict _ (by
    intro f
    let morphism : planeRelations s ⟶ L.sheaf := f
    have h := tripleToRelations_cycle X.ringCatSheaf (planeTriple_le s 0) (planeTriple_le s 1) (planeTriple_le s 2)
    let post : (freeOpen X.ringCatSheaf (planeTriple s) ⟶ planeRelations s) →+
        BaseHom k (freeOpen X.ringCatSheaf (planeTriple s)) L.sheaf :=
      { toFun := fun arrow => arrow ≫ morphism
        map_zero' := Limits.zero_comp
        map_add' := fun first second => Preadditive.add_comp _ _ _ first second morphism }
    let evaluate := (homChart k L.sheaf (le_rfl : planeTriple s ≤ planeTriple s)).toAddMonoidHom.comp post
    have evaluate_map {chart : X.Opens} (restriction : planeTriple s ≤ chart)
        (arrow : freeOpen X.ringCatSheaf chart ⟶ planeRelations s) :
        evaluate (freeOpenMap X.ringCatSheaf (homOfLE restriction) ≫ arrow) =
          homChart k L.sheaf restriction (arrow ≫ morphism) :=
      (congrArg (homChart k L.sheaf (le_rfl : planeTriple s ≤ planeTriple s))
        (Category.assoc _ _ _)).trans (homChart_natural k L.sheaf le_rfl restriction _)
    have he := congrArg evaluate h
    simp only [map_add, map_zero, evaluate_map] at he
    exact he)

lemma relationCycles_injective [IsIntegral X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) [Nonempty (planeTriple s)] (L : LineBundle X) :
    Function.Injective (relationCycles k s L) := by
  intro f g h
  let : Epi (planeRelPi s) := tripleToRelations_epi X.ringCatSheaf
    (SectionOpens.isoOpen (s 0)) (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
  apply (cancel_epi (planeRelPi s)).mp
  apply biprod.hom_ext' (C := SheafOfModules X.ringCatSheaf)
  · have component : (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ f =
        (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ g :=
      homChart_injective k L (le_inf (planeTriple_le s 0) (planeTriple_le s 1))
        (congrArg (fun z => z.val.1.val) h)
    exact (Category.assoc _ _ _).symm.trans (component.trans (Category.assoc _ _ _))
  · apply biprod.hom_ext' (C := SheafOfModules X.ringCatSheaf)
    · have component : (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
          biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ f =
          (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
            biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ g :=
        homChart_injective k L (le_inf (planeTriple_le s 0) (planeTriple_le s 2))
          (congrArg (fun z => z.val.2.1.val) h)
      exact ((Category.assoc _ _ _).trans
        (congrArg (fun arrow => biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
          (Category.assoc _ _ _))).symm.trans (component.trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun arrow => biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
                (Category.assoc _ _ _))))
    · have component : (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
          biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ f =
          (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
            biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ g :=
        homChart_injective k L (le_inf (planeTriple_le s 1) (planeTriple_le s 2))
          (congrArg (fun z => z.val.2.2.val) h)
      exact ((Category.assoc _ _ _).trans
        (congrArg (fun arrow => biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
          (Category.assoc _ _ _))).symm.trans (component.trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun arrow => biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
                (Category.assoc _ _ _))))

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
