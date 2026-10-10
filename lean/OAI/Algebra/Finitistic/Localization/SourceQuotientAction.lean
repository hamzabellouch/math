import OAI.Algebra.Finitistic.Localization.SourceShiftLinear
import OAI.Algebra.Finitistic.Localization.ConcreteTensorEvaluation
import OAI.Algebra.Finitistic.Localization.QuotientRelations
import OAI.Algebra.Finitistic.Localization.QuotientAction
import OAI.Algebra.Finitistic.Selection.SelectionEncoding

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.SourceQuotientAction
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The two concrete presentations of the same right ideal e_i B. -/
def vertexIso (i : Fin 3) : (SourceVerdier.E P i).obj ≅ vertexModule P i :=
  (ConcreteTensorEvaluation.idealEquiv (SourceVerdier.vertex P i)
    (SourceVerdier.vertex_idem P i)).toModuleIso

def nativeHom (i j : Fin 3) :
    (vertexModule P i ⟶ vertexModule P j) →ₗ[k]
      (SourceVerdier.E P i ⟶ SourceVerdier.E P j) where
  toFun f := ObjectProperty.homMk ((vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv)
  map_add' f g := by
    apply ObjectProperty.hom_ext
    change (vertexIso P i).hom ≫ (f+g) ≫ (vertexIso P j).inv =
      (vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv +
      (vertexIso P i).hom ≫ g ≫ (vertexIso P j).inv
    simp [Preadditive.comp_add,Preadditive.add_comp]
  map_smul' a f := by
    apply ObjectProperty.hom_ext
    change (vertexIso P i).hom ≫ (a • f) ≫ (vertexIso P j).inv =
      a • ((vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv)
    simp

lemma nativeHom_comp {i j l : Fin 3}
    (f : vertexModule P i ⟶ vertexModule P j) (g : vertexModule P j ⟶ vertexModule P l) :
    nativeHom P i l (f ≫ g) = nativeHom P i j f ≫ nativeHom P j l g := by
  apply ObjectProperty.hom_ext
  change _ = ((vertexIso P i).hom ≫ f ≫ (vertexIso P j).inv) ≫
    ((vertexIso P j).hom ≫ g ≫ (vertexIso P l).inv)
  simp [nativeHom]

lemma nativeHom_arrow01 (a : Fin (d+1)) :
    nativeHom P 0 1 (arrowModule01 P a) = SourceVerdier.arrow01 P a := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl
lemma nativeHom_arrow12 (a : Fin (d+1)) :
    nativeHom P 1 2 (arrowModule12 P a) = SourceVerdier.arrow12 P a := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  rfl

instance singleAdditive : (HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ)).Additive :=
  inferInstanceAs ((CochainComplex.singleFunctor (SourceVerdier.Proj P) 0).Additive)
instance singleLinear : (HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ)).Linear k :=
  inferInstanceAs ((CochainComplex.singleFunctor (SourceVerdier.Proj P) 0).Linear k)
instance stalkAdditive : (SourceVerdier.stalk P).Additive := by
  unfold SourceVerdier.stalk
  infer_instance
instance stalkLinear : (SourceVerdier.stalk P).Linear k where
  map_smul := by
    intro X Y f a
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.single (SourceVerdier.Proj P) (.up ℤ) (0 : ℤ) ⋙
      HomotopyCategory.quotient _ _).map_smul a f

abbrev vertex (i : Fin 3) : SourceVerdier.Q P :=
  (SourceVerdier.q P).obj ((SourceVerdier.stalk P).obj (SourceVerdier.E P i))
abbrev a01 (a : Fin (d+1)) : vertex P 0 ⟶ vertex P 1 :=
  (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map (SourceVerdier.arrow01 P a)
abbrev a12 (a : Fin (d+1)) : vertex P 1 ⟶ vertex P 2 :=
  (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map (SourceVerdier.arrow12 P a)
instance : IsIso (a01 P 0) := SourceVerdier.s_inverted P
instance : IsIso (a12 P 0) := SourceVerdier.s'_inverted P

def path : Paths k d →ₗ[k] (vertex P 0 ⟶ vertex P 2) :=
  ((SourceVerdier.stalk P ⋙ SourceVerdier.q P).mapLinearMap k).comp
    ((nativeHom P 0 2).comp (pathModuleMap P))

lemma path_basis (h l : Fin (d+1)) :
    path P (basis h ⊗ₜ[k] basis l) = a01 P l ≫ a12 P h := by
  change (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map
    (nativeHom P 0 2 (pathModuleMap P (basis h ⊗ₜ[k] basis l))) = _
  rw [pathModuleMap_basis,nativeHom_comp,nativeHom_arrow01,nativeHom_arrow12,Functor.map_comp]

lemma path_kills (z : Paths k d) (hz : z ∈ relationSpace P) : path P z = 0 := by
  change (SourceVerdier.stalk P ⋙ SourceVerdier.q P).map
    (nativeHom P 0 2 (pathModuleMap P z)) = 0
  rw [pathModuleMap_kills P z hz,map_zero,Functor.map_zero]

lemma commutation (h : Fin d) : a01 P 0 ≫ a12 P h.succ = a01 P h.succ ≫ a12 P 0 := by
  have hz := path_kills P (QuadraticEncoding.commutation h)
    (Submodule.subset_span (Or.inl ⟨h,rfl⟩))
  simpa only [QuadraticEncoding.commutation,map_sub,path_basis,sub_eq_zero] using hz

lemma homogenized (j : Fin t) :
    (∑ h, ∑ l, P.quadratic j h l • (a01 P l.succ ≫ a12 P h.succ)) +
    (∑ h, P.linear j h • (a01 P h.succ ≫ a12 P 0)) +
    P.constant j • (a01 P 0 ≫ a12 P 0) = 0 := by
  have hz := path_kills P (QuadraticEncoding.homogenized P j)
    (Submodule.subset_span (Or.inr ⟨j,rfl⟩))
  simpa only [QuadraticEncoding.homogenized,map_add,map_sum,map_smul,path_basis] using hz

/-- The actual theta on E0 in the primary's source Verdier quotient. -/
def theta {R : Type*} [Ring R] [Algebra k R] (E : SelectionEncoding.Encoding k R) :
    R →ₐ[k] End (vertex E.relations 0) :=
  QuotientAction.presentedAction E.relations (a01 E.relations 0) (a12 E.relations 0)
    (fun h => a01 E.relations h.succ) (fun h => a12 E.relations h.succ)
    (commutation E.relations) (homogenized E.relations) E.equiv
end LittleFinitistic.SourceQuotientAction

end

end OAI
