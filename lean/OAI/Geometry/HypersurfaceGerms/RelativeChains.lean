import Mathlib

namespace OAI

/-! Relative singular chains and naturality of the oriented prism. -/

namespace AmbientMultiplicity.RelativeSingular
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

abbrev integralChains : TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)

variable {X : Type} [TopologicalSpace X] (D : Set X)

 
def inclusion : TopCat.of D ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

instance inclusion_mono : Mono (inclusion D) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

 
abbrev relativeChains : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (integralChains.map (inclusion D))

 
abbrev RelativeHomology (n : ℕ) : ModuleCat ℤ := (relativeChains D).homology n

 
def pairSequence : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (integralChains.map (inclusion D))
    (cokernel.π (integralChains.map (inclusion D))) (cokernel.condition _)

lemma pairSequence_shortExact : (pairSequence D).ShortExact := by
  dsimp [pairSequence]
  exact { exact := ShortComplex.exact_cokernel _ }

 
def toRelativeHomology (n : ℕ) :
    ((integralChains.obj (TopCat.of X)).homology n) ⟶ RelativeHomology D n :=
  HomologicalComplex.homologyMap (cokernel.π (integralChains.map (inclusion D))) n

 
def boundary (n : ℕ) :
    RelativeHomology D (n+1) ⟶ (integralChains.obj (TopCat.of D)).homology n :=
  (pairSequence_shortExact D).δ (n+1) n (by simp)

lemma boundary_comp_inclusion (n : ℕ) :
    boundary D n ≫ HomologicalComplex.homologyMap (integralChains.map (inclusion D)) n = 0 :=
  (pairSequence_shortExact D).δ_comp (n+1) n (by simp)

lemma relative_comp_boundary (n : ℕ) :
    toRelativeHomology D (n+1) ≫ boundary D n = 0 :=
  (pairSequence_shortExact D).comp_δ (n+1) n (by simp)

 

lemma exact_at_subspace (n : ℕ) :
    (ShortComplex.mk (boundary D n)
      (HomologicalComplex.homologyMap (integralChains.map (inclusion D)) n)
      (boundary_comp_inclusion D n)).Exact :=
  (pairSequence_shortExact D).homology_exact₁ (n+1) n (by simp)

 
lemma exact_at_space (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (integralChains.map (inclusion D)) n)
      (toRelativeHomology D n) (by
        unfold toRelativeHomology
        rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (pairSequence_shortExact D).homology_exact₂ n

 
lemma exact_at_relative (n : ℕ) :
    (ShortComplex.mk (toRelativeHomology D (n+1)) (boundary D n)
      (relative_comp_boundary D n)).Exact :=
  (pairSequence_shortExact D).homology_exact₃ (n+1) n (by simp)

 
def relativeDegreeDesc (n : ℕ) {M : ModuleCat ℤ}
    (f : (integralChains.obj (TopCat.of X)).X n ⟶ M)
    (hf : (integralChains.map (inclusion D)).f n ≫ f = 0) :
    (relativeChains D).X n ⟶ M :=
  (PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
    (integralChains.map (inclusion D))).hom ≫ cokernel.desc _ f hf

@[reassoc]
lemma quotient_comp_relativeDegreeDesc (n : ℕ) {M : ModuleCat ℤ}
    (f : (integralChains.obj (TopCat.of X)).X n ⟶ M)
    (hf : (integralChains.map (inclusion D)).f n ≫ f = 0) :
    (cokernel.π (integralChains.map (inclusion D))).f n ≫
      relativeDegreeDesc D n f hf = f := by
  unfold relativeDegreeDesc
  change (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
    (cokernel.π (integralChains.map (inclusion D))) ≫ _ = _
  erw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

end
end AmbientMultiplicity.RelativeSingular

 

namespace AmbientMultiplicity.PrismNaturality
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

lemma simplicial_components {X Y X' Y' : SSet} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (i : X' ⟶ X) (j : Y' ⟶ Y) (sq : (i ▷ _) ≫ H.h = H'.h ≫ j)
    {n : ℕ} (k : Fin (n+1)) :
    i.app _ ≫ H.toSimplicialObjectHomotopy.h k =
      H'.toSimplicialObjectHomotopy.h k ≫ j.app _ := by
  ext x
  change ((SSet.yonedaEquiv.symm (i.app _ x) ▷ _) ≫ H.h).app _ _ =
    j.app _ (((SSet.yonedaEquiv.symm x ▷ _) ≫ H'.h).app _ _)
  rw [← SSet.yonedaEquiv_symm_comp, MonoidalCategory.comp_whiskerRight,
    Category.assoc, sq, ← Category.assoc]
  rfl

lemma simplicial_prism {X Y X' Y' : SSet} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (i : X' ⟶ X) (j : Y' ⟶ Y) (sq : (i ▷ _) ≫ H.h = H'.h ≫ j)
    (n : ℕ) :
    (SSet.chainComplexMap i (ModuleCat.of ℤ ℤ)).f n ≫
      (H.chainComplexMap (ModuleCat.of ℤ ℤ)).hom n (n+1) =
    (H'.chainComplexMap (ModuleCat.of ℤ ℤ)).hom n (n+1) ≫
      (SSet.chainComplexMap j (ModuleCat.of ℤ ℤ)).f (n+1) := by
  change (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (i.app (Opposite.op ⦋n⦌)) ≫
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
      (H.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj (ModuleCat.of ℤ ℤ))) n (n+1) =
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
      (H'.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj (ModuleCat.of ℤ ℤ))) n (n+1) ≫
        (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map (j.app (Opposite.op ⦋n+1⦌))
  simp only [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  erw [Preadditive.comp_neg, Preadditive.neg_comp]
  congr 1
  erw [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  erw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  change _ ≫ (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map
    (H.toSimplicialObjectHomotopy.h k) =
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map
      (H'.toSimplicialObjectHomotopy.h k) ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp, simplicial_components H H' i j sq]

lemma topological_square {X Y X' Y' : TopCat} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (i : X' ⟶ X) (j : Y' ⟶ Y) (sq : (i ▷ TopCat.I) ≫ H.h = H'.h ≫ j) :
    (TopCat.toSSet.map i ▷ _) ≫ H.toSSet.h = H'.toSSet.h ≫ TopCat.toSSet.map j := by
  dsimp only [TopCat.Homotopy.toSSet]
  rw [← Category.assoc, ← Category.assoc, ← whisker_exchange]
  simp only [Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [← Functor.map_comp, sq, Functor.map_comp]

lemma topological_prism {X Y X' Y' : TopCat} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (i : X' ⟶ X) (j : Y' ⟶ Y) (sq : (i ▷ TopCat.I) ≫ H.h = H'.h ≫ j)
    (n : ℕ) :
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map i).f n ≫
      (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom n (n+1) =
    (H'.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom n (n+1) ≫
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map j).f (n+1) :=
  simplicial_prism H.toSSet H'.toSSet _ _ (topological_square H H' i j sq) n

lemma topological_prism_all {X Y X' Y' : TopCat} {f g : X ⟶ Y}
    {f' g' : X' ⟶ Y'} (H : TopCat.Homotopy f g) (H' : TopCat.Homotopy f' g')
    (i : X' ⟶ X) (j : Y' ⟶ Y) (sq : (i ▷ TopCat.I) ≫ H.h = H'.h ≫ j)
    (n m : ℕ) :
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map i).f n ≫
      (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom n m =
    (H'.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom n m ≫
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map j).f m := by
  by_cases h : n + 1 = m
  · subst m
    exact topological_prism H H' i j sq n
  · rw [(H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).zero n m h,
      (H'.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).zero n m h,
      comp_zero, zero_comp]

end
end AmbientMultiplicity.PrismNaturality

end OAI
