import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.HomologyCycle
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340.SingularCover

variable {X : Type} [TopologicalSpace X]

def supported (U : Set X) : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex where
  obj n := {s | ∀ p, TopCat.toSSetObjEquiv (TopCat.of X) n s p ∈ U}
  map {n m} f s hs p := by
    exact hs (Convexity.StdSimplex.map f.unop p)

@[simp] theorem mem_supported (U : Set X) (n : SimplexCategoryᵒᵖ)
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    s ∈ (supported U).obj n ↔
      ∀ p, TopCat.toSSetObjEquiv (TopCat.of X) n s p ∈ U := Iff.rfl

theorem supported_mono {U V : Set X} (h : U ⊆ V) : supported U ≤ supported V :=
  fun _ _ hs p => h (hs p)

@[simp] theorem supported_inter (U V : Set X) :
    supported (U ∩ V) = supported U ⊓ supported V := by
  ext n s
  exact forall_and

@[simp] theorem supported_univ : supported (Set.univ : Set X) = ⊤ := by
  ext n s
  simp

instance chainFunctor_preservesColimitsOfShape (J : Type) [Category J] :
    PreservesColimitsOfShape J
      ((SSet.chainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    ((evaluation SimplexCategoryᵒᵖ (Type _)).obj (op ⦋n⦌) ⋙
      sigmaConst.obj (ModuleCat.of ℝ ℝ))
  infer_instance

theorem union_isPushout {K : SSet} (A B : K.Subcomplex) :
    IsPushout
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) := by
  apply SSet.Subcomplex.BicartSq.isPushout
  exact ⟨rfl, rfl⟩

theorem chainUnion_isPushout {K : SSet} (A B : K.Subcomplex) :
    IsPushout
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) (ModuleCat.of ℝ ℝ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) (ModuleCat.of ℝ ℝ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) (ModuleCat.of ℝ ℝ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) (ModuleCat.of ℝ ℝ)) :=
  (union_isPushout A B).map
    ((SSet.chainComplexFunctor (ModuleCat ℝ)).obj (ModuleCat.of ℝ ℝ))

def unionShortComplex {K : SSet} (A B : K.Subcomplex) :
    ShortComplex (ChainComplex (ModuleCat ℝ) ℕ) :=
  (chainUnion_isPushout A B).shortComplex

theorem unionShortComplex_exact {K : SSet} (A B : K.Subcomplex) :
    (unionShortComplex A B).Exact :=
  (chainUnion_isPushout A B).exact_shortComplex

theorem chainMap_mono {K L : SSet} (f : K ⟶ L) [Mono f] :
    Mono (SSet.chainComplexMap f (ModuleCat.of ℝ ℝ)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj (ModuleCat.of ℝ ℝ)).map (f.app (op ⦋n⦌)))
  infer_instance

theorem unionShortComplex_shortExact {K : SSet} (A B : K.Subcomplex) :
    (unionShortComplex A B).ShortExact := by
  have : Epi (unionShortComplex A B).g :=
    (chainUnion_isPushout A B).epi_shortComplex_g
  have : Mono (unionShortComplex A B).f := by
    change Mono (biprod.lift _ _)
    exact @biprod.mono_lift_of_mono_left _ _ _ _ _ _ _ _ _ (chainMap_mono _)
  exact { exact := unionShortComplex_exact A B }

end Problem340.SingularCover

end

end OAI
