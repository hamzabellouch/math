import OAI.CategoryTheory.Thomason.Simplicial.HomotopyFiberPathEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import OAI.CategoryTheory.Thomason.Transfer.KanQuillenLiftingReduction

namespace OAI

section

/-! # Evaluation of genuine simplicial internal path objects -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

abbrev internalPathObject (X : SSet.{0}) : SSet.{0} := (ihom (Δ[1] : SSet.{0})).obj X

/-- Evaluation, with the interval written as the second cylinder factor. -/
def internalPathCylinder {K X : SSet.{0}} (a : K ⟶ internalPathObject X) :
    K ⊗ Δ[1] ⟶ X := (β_ K Δ[1]).hom ≫ uncurry a

theorem internalPathCylinder_naturality {A K X : SSet.{0}} (i : A ⟶ K)
    (a : K ⟶ internalPathObject X) :
    internalPathCylinder (i ≫ a) = i ▷ Δ[1] ≫ internalPathCylinder a := by
  unfold internalPathObject at a
  change (β_ A (Δ[1] : SSet.{0})).hom ≫ uncurry (A := (Δ[1] : SSet.{0})) (i ≫ a) =
    i ▷ (Δ[1] : SSet.{0}) ≫ ((β_ K (Δ[1] : SSet.{0})).hom ≫
      uncurry (A := (Δ[1] : SSet.{0})) a)
  rw [uncurry_natural_left, ← Category.assoc,
    ← BraidedCategory.braiding_naturality_left i (Δ[1] : SSet.{0}), Category.assoc]

def internalPathStart (X : SSet.{0}) : internalPathObject X ⟶ X :=
  SSet.ι₀ ≫ internalPathCylinder (𝟙 (internalPathObject X))

theorem internalPathCylinder_start {K X : SSet.{0}} (a : K ⟶ internalPathObject X) :
    SSet.ι₀ ≫ internalPathCylinder a = a ≫ internalPathStart X := by
  have he := internalPathCylinder_naturality a (𝟙 (internalPathObject X))
  rw [Category.comp_id] at he
  rw [he, ← Category.assoc]
  have hn : SSet.ι₀ ≫ a ▷ Δ[1] = a ≫ SSet.ι₀ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [hn, Category.assoc]
  rfl

/-- Currying a cylinder in this order reverses evaluation exactly. -/
def internalPathTranspose {K X : SSet.{0}} (h : K ⊗ Δ[1] ⟶ X) :
    K ⟶ internalPathObject X := curry ((β_ K Δ[1]).inv ≫ h)

theorem internalPathCylinder_transpose {K X : SSet.{0}} (h : K ⊗ Δ[1] ⟶ X) :
    internalPathCylinder (internalPathTranspose h) = h := by
  unfold internalPathCylinder internalPathTranspose
  rw [uncurry_curry, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem internalPathCylinder_injective (K X : SSet.{0}) :
    Function.Injective (@internalPathCylinder K X) := by
  intro a b h
  apply ((ihom.adjunction Δ[1]).homEquiv K X).symm.injective
  apply (cancel_epi (β_ K (Δ[1] : SSet.{0})).hom).mp
  exact h

/-- Initial evaluation lifts against every monomorphism when the target is
Kan. This is proved directly by relative cylinder extension. -/
theorem internalPathStart_mono_lifting (X : SSet.{0}) [SSet.KanComplex X]
    {A B : SSet.{0}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (internalPathStart X) := by
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨h, h₀, hi⟩ := exists_kan_homotopy_extension i b (internalPathCylinder a)
    ((internalPathCylinder_start a).trans sq.w)
  let l := internalPathTranspose h
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply internalPathCylinder_injective A X
    rw [internalPathCylinder_naturality, internalPathCylinder_transpose, hi]
  · rw [← internalPathCylinder_start, internalPathCylinder_transpose, h₀]

/-- The internal path start map satisfies the actual boundary lifting class,
not merely the Kan fibration class. -/
theorem internalPathStart_boundary_rlp (X : SSet.{0}) [SSet.KanComplex X] :
    I.rlp (internalPathStart X) := by
  rw [← SSet.rlp_monomorphisms]
  intro A B i hi
  have : Mono i := hi
  exact internalPathStart_mono_lifting X i

theorem internalPathStart_weak (X : SSet.{0}) [SSet.KanComplex X] :
    realizationWeakEquivalences (internalPathStart X) :=
  boundary_rlp_weak _ (internalPathStart_boundary_rlp X)


theorem internalPathCylinder_postcomp {K X Y : SSet.{0}}
    (a : K ⟶ internalPathObject X) (f : X ⟶ Y) :
    internalPathCylinder (a ≫ (ihom (Δ[1] : SSet.{0})).map f) =
      internalPathCylinder a ≫ f := by
  unfold internalPathObject at a
  change (β_ K (Δ[1] : SSet.{0})).hom ≫
      uncurry (A := (Δ[1] : SSet.{0})) (a ≫ (ihom (Δ[1] : SSet.{0})).map f) =
    ((β_ K (Δ[1] : SSet.{0})).hom ≫ uncurry (A := (Δ[1] : SSet.{0})) a) ≫ f
  rw [uncurry_natural_right, Category.assoc]

theorem internalPathStart_naturality {X Y : SSet.{0}} (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{0})).map f ≫ internalPathStart Y = internalPathStart X ≫ f := by
  rw [← internalPathCylinder_start]
  have he := internalPathCylinder_postcomp (𝟙 (internalPathObject X)) f
  rw [Category.id_comp] at he
  rw [he, ← Category.assoc]
  rfl

/-- Internal paths preserve and reflect the actual realization weak class
between Kan targets. Both evaluation maps have already been proved to lift
against every boundary. -/
theorem internalPathMap_weak_iff {X Y : SSet.{0}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) :
    realizationWeakEquivalences ((ihom (Δ[1] : SSet.{0})).map f) ↔
      realizationWeakEquivalences f := by
  have hx := internalPathStart_weak X
  have hy := internalPathStart_weak Y
  constructor
  · intro hf
    apply realizationWeakEquivalences.of_precomp (internalPathStart X) f hx
    rw [← internalPathStart_naturality]
    exact realizationWeakEquivalences.comp_mem _ _ hf hy
  · intro hf
    apply realizationWeakEquivalences.of_postcomp _ (internalPathStart Y) hy
    rw [internalPathStart_naturality]
    exact realizationWeakEquivalences.comp_mem _ _ hx hf

end

end Thomason.Construction

end

section

/-! # The actual realization comparison for simplicial internal paths -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial

noncomputable section

def internalPathEnd (X : SSet.{0}) : internalPathObject X ⟶ X :=
  SSet.ι₁ ≫ internalPathCylinder (𝟙 (internalPathObject X))


theorem internalPathCylinder_end {K X : SSet.{0}} (a : K ⟶ internalPathObject X) :
    SSet.ι₁ ≫ internalPathCylinder a = a ≫ internalPathEnd X := by
  have he := internalPathCylinder_naturality a (𝟙 (internalPathObject X))
  rw [Category.comp_id] at he
  rw [he, ← Category.assoc]
  have hn : SSet.ι₁ ≫ a ▷ Δ[1] = a ≫ SSet.ι₁ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [hn, Category.assoc]
  rfl

/-- The internal evaluation cylinder is an actual simplicial homotopy
between its two evaluation maps. -/
def internalPathEvaluationHomotopy (X : SSet.{0}) :
    SSet.Homotopy (internalPathStart X) (internalPathEnd X) where
  h := internalPathCylinder (𝟙 (internalPathObject X))
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Realizing the evaluation cylinder and currying gives the genuine
compact-open path of every realized internal path. -/
def realizedInternalPathComparison (X : SSet.{0}) :
    SSet.toTop.obj (internalPathObject X) ⟶ continuousPathSpace (SSet.toTop.obj X) :=
  (continuousPathFamilyEquiv (internalPathObject X) (SSet.toTop.obj X)).symm
    (RealizedCylinder.homotopy (internalPathEvaluationHomotopy X))

theorem realizedInternalPathComparison_start (X : SSet.{0}) :
    realizedInternalPathComparison X ≫ continuousPathStart (SSet.toTop.obj X) =
      SSet.toTop.map (internalPathStart X) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact (RealizedCylinder.homotopy (internalPathEvaluationHomotopy X)).apply_zero x

/-- For a Kan target this comparison is an actual weak homotopy equivalence.
The proof uses the constructed boundary-lifting property of start evaluation,
without the general acyclic-Kan implication. -/
theorem realizedInternalPathComparison_weak (X : SSet.{0}) [SSet.KanComplex X] :
    topologicalWeakEquivalences (realizedInternalPathComparison X) := by
  have hs : topologicalWeakEquivalences (continuousPathStart (SSet.toTop.obj X)) :=
    homotopyEquiv_isWeakHomotopyEquivalence (continuousPathStartEquiv _)
  apply topologicalWeakEquivalences.of_postcomp _ _ hs
  rw [realizedInternalPathComparison_start]
  exact internalPathStart_weak X


theorem realizedInternalPathComparison_apply (X : SSet.{0})
    (x : SSet.toTop.obj (internalPathObject X)) (t : unitInterval) :
    (show C(unitInterval, SSet.toTop.obj X) from (realizedInternalPathComparison X).hom x) t =
      (SSet.toTop.map (internalPathCylinder (𝟙 (internalPathObject X)))).hom
        ((RealizedCylinder.comparison (internalPathObject X)).hom (x, t)) :=
  realizedHomotopy_apply (internalPathEvaluationHomotopy X) t x

/-- The realization/path comparison commutes with every simplicial target
map, including the exact point and time coordinates. -/
theorem realizedInternalPathComparison_naturality {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.toTop.map ((ihom (Δ[1] : SSet.{0})).map f) ≫ realizedInternalPathComparison Y =
      realizedInternalPathComparison X ≫ continuousPathMap (SSet.toTop.map f) := by
  let a := (ihom (Δ[1] : SSet.{0})).map f
  have he : a ▷ Δ[1] ≫ internalPathCylinder (𝟙 (internalPathObject Y)) =
      internalPathCylinder (𝟙 (internalPathObject X)) ≫ f := by
    have h₁ := internalPathCylinder_naturality a (𝟙 (internalPathObject Y))
    have h₂ := internalPathCylinder_postcomp (𝟙 (internalPathObject X)) f
    rw [Category.comp_id] at h₁
    rw [Category.id_comp] at h₂
    exact h₁.symm.trans h₂
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change (show C(unitInterval, SSet.toTop.obj Y) from
    (realizedInternalPathComparison Y).hom ((SSet.toTop.map a).hom x)) t =
    (SSet.toTop.map f).hom ((show C(unitInterval, SSet.toTop.obj X) from (realizedInternalPathComparison X).hom x) t)
  rw [realizedInternalPathComparison_apply, realizedInternalPathComparison_apply]
  have hn := congrArg (fun g => g.hom (x, t)) (RealizedCylinder.comparison_naturality a)
  change (RealizedCylinder.comparison (internalPathObject Y)).hom
      ((SSet.toTop.map a).hom x, t) =
    (SSet.toTop.map (a ▷ Δ[1])).hom
      ((RealizedCylinder.comparison (internalPathObject X)).hom (x, t)) at hn
  rw [hn]
  change (SSet.toTop.map (a ▷ Δ[1]) ≫
      SSet.toTop.map (internalPathCylinder (𝟙 (internalPathObject Y)))).hom _ =
    (SSet.toTop.map (internalPathCylinder (𝟙 (internalPathObject X))) ≫ SSet.toTop.map f).hom _
  rw [← SSet.toTop.map_comp, he, SSet.toTop.map_comp]

end

end Thomason.Construction

end

section

/-! # Constant internal paths and both endpoint formulas -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open scoped Simplicial

noncomputable section

def internalPathConstant (X : SSet.{0}) : X ⟶ internalPathObject X :=
  internalPathTranspose (fst X (Δ[1] : SSet.{0}))

theorem internalPathConstant_start (X : SSet.{0}) :
    internalPathConstant X ≫ internalPathStart X = 𝟙 X := by
  rw [← internalPathCylinder_start, internalPathConstant, internalPathCylinder_transpose]
  rfl

theorem internalPathConstant_end (X : SSet.{0}) :
    internalPathConstant X ≫ internalPathEnd X = 𝟙 X := by
  rw [← internalPathCylinder_end, internalPathConstant, internalPathCylinder_transpose]
  rfl

theorem internalPathEnd_naturality {X Y : SSet.{0}} (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{0})).map f ≫ internalPathEnd Y = internalPathEnd X ≫ f := by
  rw [← internalPathCylinder_end]
  have he := internalPathCylinder_postcomp (𝟙 (internalPathObject X)) f
  rw [Category.id_comp] at he
  rw [he, ← Category.assoc]
  rfl

theorem internalPathConstant_naturality {X Y : SSet.{0}} (f : X ⟶ Y) :
    internalPathConstant X ≫ (ihom (Δ[1] : SSet.{0})).map f =
      f ≫ internalPathConstant Y := by
  apply internalPathCylinder_injective
  rw [internalPathCylinder_postcomp, internalPathCylinder_naturality]
  change internalPathCylinder (internalPathTranspose _) ≫ f =
    f ▷ Δ[1] ≫ internalPathCylinder (internalPathTranspose _)
  rw [internalPathCylinder_transpose, internalPathCylinder_transpose]
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem realizedInternalPathComparison_end (X : SSet.{0})
    (x : SSet.toTop.obj (internalPathObject X)) :
    (show C(unitInterval, SSet.toTop.obj X) from (realizedInternalPathComparison X).hom x) 1 =
      (SSet.toTop.map (internalPathEnd X)).hom x :=
  (RealizedCylinder.homotopy (internalPathEvaluationHomotopy X)).apply_one x

end

end Thomason.Construction

end

section

/-! # A direct contraction of internal paths, without a Kan hypothesis -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Evaluate a path at the minimum of its parameter and the contraction time. -/
def internalPathMinMap (P : SSet.{0}) :
    (P ⊗ (Δ[1] : SSet.{0})) ⊗ Δ[1] ⟶ P ⊗ Δ[1] where
  app d := ↾fun z => (z.1.1, SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk {
    toFun j := min ((SSet.stdSimplex.objEquiv z.1.2).toOrderHom j)
      ((SSet.stdSimplex.objEquiv z.2).toOrderHom j)
    monotone' := fun a b hab => min_le_min
      ((SSet.stdSimplex.objEquiv z.1.2).toOrderHom.monotone hab)
      ((SSet.stdSimplex.objEquiv z.2).toOrderHom.monotone hab) }))
  naturality d e f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · rfl
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl

/-- Internal path shrinking is obtained by transposing the actual min map. -/
def internalPathShrinkingMap (X : SSet.{0}) :
    internalPathObject X ⊗ Δ[1] ⟶ internalPathObject X :=
  internalPathTranspose (internalPathMinMap (internalPathObject X) ≫
    internalPathCylinder (𝟙 (internalPathObject X)))

private theorem internalPathMinMap_zero (P : SSet.{0}) :
    (SSet.ι₀ (X := P)) ▷ (Δ[1] : SSet.{0}) ≫ internalPathMinMap P =
      fst P Δ[1] ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  exact min_eq_left (Fin.zero_le _)

private theorem internalPathMinMap_one (P : SSet.{0}) :
    (SSet.ι₁ (X := P)) ▷ (Δ[1] : SSet.{0}) ≫ internalPathMinMap P = 𝟙 _ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  exact min_eq_right (Fin.le_last _)

/-- The internal path object contracts to its starting constant path in
all simplicial sets. This fact requires no horn fillers. -/
def internalPathContraction (X : SSet.{0}) :
    SSet.Homotopy (internalPathStart X ≫ internalPathConstant X)
      (𝟙 (internalPathObject X)) where
  h := internalPathShrinkingMap X
  h₀ := by
    change SSet.ι₀ ≫ internalPathShrinkingMap X = internalPathStart X ≫ internalPathConstant X
    apply internalPathCylinder_injective
    rw [internalPathCylinder_naturality, internalPathShrinkingMap,
      internalPathCylinder_transpose, ← Category.assoc, internalPathMinMap_zero]
    rw [internalPathCylinder_naturality, internalPathConstant, internalPathCylinder_transpose]
    rw [Category.assoc]
    change fst (internalPathObject X) Δ[1] ≫ internalPathStart X = _
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  h₁ := by
    change SSet.ι₁ ≫ internalPathShrinkingMap X = 𝟙 (internalPathObject X)
    apply internalPathCylinder_injective
    rw [internalPathCylinder_naturality, internalPathShrinkingMap,
      internalPathCylinder_transpose, ← Category.assoc, internalPathMinMap_one,
      Category.id_comp]
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- The contraction fixes the initial evaluation exactly throughout time. -/
theorem internalPathShrinkingMap_start (X : SSet.{0}) :
    internalPathShrinkingMap X ≫ internalPathStart X =
      fst (internalPathObject X) Δ[1] ≫ internalPathStart X := by
  rw [← internalPathCylinder_start, internalPathShrinkingMap, internalPathCylinder_transpose]
  rw [← Category.assoc]
  have he : SSet.ι₀ ≫ internalPathMinMap (internalPathObject X) =
      fst (internalPathObject X) Δ[1] ≫ SSet.ι₀ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · rfl
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    exact min_eq_right (Fin.zero_le _)
  rw [he, Category.assoc]
  rfl

/-- Starting evaluation is a realization weak equivalence for every
simplicial set, independently of the stronger Kan boundary-lifting claim. -/
theorem internalPathStart_weak_unconditional (X : SSet.{0}) :
    realizationWeakEquivalences (internalPathStart X) := by
  have hc := simplicial_retraction_weak_of_zigzag
    (internalPathConstant X) (internalPathStart X)
    (internalPathStart X ≫ internalPathConstant X) (internalPathConstant_start X)
    (internalPathContraction X) (SSet.RelativeMorphism.Homotopy.refl _)
  apply realizationWeakEquivalences.of_precomp (internalPathConstant X) _ hc
  rw [internalPathConstant_start]
  exact realizationWeakEquivalences.id_mem _

/-- The continuous free-path comparison is weak for arbitrary simplicial
bases, including the non-Kan bases in the main construction. -/
theorem realizedInternalPathComparison_weak_unconditional (X : SSet.{0}) :
    topologicalWeakEquivalences (realizedInternalPathComparison X) := by
  have hs : topologicalWeakEquivalences (continuousPathStart (SSet.toTop.obj X)) :=
    homotopyEquiv_isWeakHomotopyEquivalence (continuousPathStartEquiv _)
  apply topologicalWeakEquivalences.of_postcomp _ _ hs
  rw [realizedInternalPathComparison_start]
  exact internalPathStart_weak_unconditional X

end

end Thomason.Construction

end

section

/-! # Constant paths are anodyne over arbitrary simplicial sets -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Minimum reparametrization commutes strictly with the parameter object. -/
theorem internalPathMinMap_naturality {P Q : SSet.{0}} (f : P ⟶ Q) :
    (f ▷ (Δ[1] : SSet.{0})) ▷ Δ[1] ≫ internalPathMinMap Q =
      internalPathMinMap P ≫ f ▷ Δ[1] := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- The whole contraction fixes every constant internal path, with an
arbitrary simplicial parameter. -/
theorem internalPathShrinkingMap_constant (X : SSet.{0}) :
    internalPathConstant X ▷ (Δ[1] : SSet.{0}) ≫ internalPathShrinkingMap X =
      fst X Δ[1] ≫ internalPathConstant X := by
  apply internalPathCylinder_injective
  rw [internalPathCylinder_naturality, internalPathShrinkingMap,
    internalPathCylinder_transpose, ← Category.assoc, internalPathMinMap_naturality]
  rw [Category.assoc]
  have hc : internalPathConstant X ▷ (Δ[1] : SSet.{0}) ≫
      internalPathCylinder (𝟙 (internalPathObject X)) = fst X Δ[1] := by
    rw [← internalPathCylinder_naturality, Category.comp_id,
      internalPathConstant, internalPathCylinder_transpose]
  rw [hc, internalPathCylinder_naturality, internalPathConstant,
    internalPathCylinder_transpose]
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- Constant paths form an anodyne subobject without any Kan condition on
`X`; the proof is the stationary simplicial contraction itself. -/
theorem internalPathConstant_anodyne (X : SSet.{0}) :
    SSet.anodyneExtensions (internalPathConstant X) := by
  have : Mono (internalPathConstant X) := mono_of_mono_fac (internalPathConstant_start X)
  exact anodyne_of_simplicial_deformation (internalPathConstant X) (internalPathStart X)
    (internalPathConstant_start X) (internalPathContraction X)
    (internalPathShrinkingMap_constant X)

end

end Thomason.Construction

end

section

/-! # Genuine simplicial mapping-path factorizations -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

abbrev simplicialMappingPath {X Y : SSet.{0}} (p : X ⟶ Y) : SSet.{0} :=
  pullback p (internalPathStart Y)

abbrev simplicialMappingPathRetraction {X Y : SSet.{0}} (p : X ⟶ Y) :
    simplicialMappingPath p ⟶ X := pullback.fst _ _

def simplicialMappingPathInclusion {X Y : SSet.{0}} (p : X ⟶ Y) :
    X ⟶ simplicialMappingPath p :=
  pullback.lift (𝟙 X) (p ≫ internalPathConstant Y) (by
    rw [Category.id_comp, Category.assoc, internalPathConstant_start, Category.comp_id])

def simplicialMappingPathProjection {X Y : SSet.{0}} (p : X ⟶ Y) :
    simplicialMappingPath p ⟶ Y := pullback.snd _ _ ≫ internalPathEnd Y

@[reassoc]
theorem simplicialMappingPath_inclusion_retraction {X Y : SSet.{0}} (p : X ⟶ Y) :
    simplicialMappingPathInclusion p ≫ simplicialMappingPathRetraction p = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem simplicialMappingPath_factorization {X Y : SSet.{0}} (p : X ⟶ Y) :
    simplicialMappingPathInclusion p ≫ simplicialMappingPathProjection p = p := by
  dsimp only [simplicialMappingPathInclusion, simplicialMappingPathProjection]
  rw [← Category.assoc, pullback.lift_snd, Category.assoc, internalPathConstant_end,
    Category.comp_id]

/-- The retraction lifts against every mono: it is a base change of the
constructed acyclic initial-evaluation map. -/
theorem simplicialMappingPath_retraction_lifting {X Y A B : SSet.{0}}
    (p : X ⟶ Y) [SSet.KanComplex Y] (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (simplicialMappingPathRetraction p) := by
  have : HasLiftingProperty i (internalPathStart Y) := internalPathStart_mono_lifting Y i
  refine ⟨fun {a b} sq => ?_⟩
  let s : CommSq (a ≫ pullback.snd p (internalPathStart Y)) i (internalPathStart Y)
      (b ≫ p) := ⟨by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (fun f => f ≫ p) sq.w⟩
  refine ⟨⟨{ l := pullback.lift b s.lift s.fac_right.symm, fac_left := ?_,
             fac_right := pullback.lift_fst _ _ _ }⟩⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using sq.w.symm
  · simp only [Category.assoc, pullback.lift_snd, s.fac_left]

theorem simplicialMappingPath_retraction_boundary_rlp {X Y : SSet.{0}}
    (p : X ⟶ Y) [SSet.KanComplex Y] : I.rlp (simplicialMappingPathRetraction p) := by
  rw [← SSet.rlp_monomorphisms]
  intro A B i hi
  have : Mono i := hi
  exact simplicialMappingPath_retraction_lifting p i

theorem simplicialMappingPath_retraction_weak {X Y : SSet.{0}}
    (p : X ⟶ Y) [SSet.KanComplex Y] :
    realizationWeakEquivalences (simplicialMappingPathRetraction p) :=
  boundary_rlp_weak _ (simplicialMappingPath_retraction_boundary_rlp p)

theorem simplicialMappingPath_inclusion_weak {X Y : SSet.{0}}
    (p : X ⟶ Y) [SSet.KanComplex Y] :
    realizationWeakEquivalences (simplicialMappingPathInclusion p) := by
  apply realizationWeakEquivalences.of_postcomp _ _ (simplicialMappingPath_retraction_weak p)
  rw [simplicialMappingPath_inclusion_retraction]
  exact realizationWeakEquivalences.id_mem _

theorem simplicialMappingPath_projection_weak_iff {X Y : SSet.{0}}
    (p : X ⟶ Y) [SSet.KanComplex Y] :
    realizationWeakEquivalences (simplicialMappingPathProjection p) ↔
      realizationWeakEquivalences p := by
  have hi := simplicialMappingPath_inclusion_weak p
  constructor
  · intro h
    simpa only [simplicialMappingPath_factorization] using
      realizationWeakEquivalences.comp_mem _ _ hi h
  · intro h
    apply realizationWeakEquivalences.of_precomp _ _ hi
    simpa only [simplicialMappingPath_factorization] using h

/-- A parameter anodyne extension lifts the endpoint projection whenever
its map into the first factor extends. Both path ends are fixed exactly. -/
theorem simplicialMappingPath_projection_lifting {X Y A B : SSet.{0}}
    (p : X ⟶ Y) [SSet.KanComplex Y] (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
    [HasLiftingProperty i (terminal.from X)] :
    HasLiftingProperty i (simplicialMappingPathProjection p) := by
  refine ⟨fun {a b} sq => ?_⟩
  let s : CommSq (a ≫ simplicialMappingPathRetraction p) i (terminal.from X)
      (terminal.from B) := ⟨terminal.hom_ext _ _⟩
  let c := intervalBoundaryFamily (s.lift ≫ p) b
  let h := internalPathCylinder (a ≫ pullback.snd p (internalPathStart Y))
  have h₀ : SSet.ι₀ ≫ h = i ≫ s.lift ≫ p := by
    dsimp only [h]
    rw [internalPathCylinder_start, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using (congrArg (fun f => f ≫ p) s.fac_left).symm
  have h₁ : SSet.ι₁ ≫ h = i ≫ b := by
    dsimp only [h]
    rw [internalPathCylinder_end, Category.assoc]
    exact sq.w
  have hc : i ▷ (SSet.boundary 1 : SSet.{0}) ≫ c =
      A ◁ (SSet.boundary 1).ι ≫ h := by
    dsimp only [c]
    rw [intervalBoundaryFamily_naturality, intervalBoundaryFamily_restriction, h₀, h₁]
  obtain ⟨e, hei, hec, _⟩ := exists_kan_boundary_cylinder_lift i hi (terminal.from Y)
    h c (terminal.from _) hc (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  obtain ⟨he₀, he₁⟩ := intervalBoundaryFamily_endpoints e (s.lift ≫ p) b hec
  let q := internalPathTranspose e
  have hq : q ≫ internalPathStart Y = s.lift ≫ p := by
    rw [← internalPathCylinder_start, internalPathCylinder_transpose, he₀]
  refine ⟨⟨{ l := pullback.lift s.lift q hq.symm, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using s.fac_left
    · simp only [Category.assoc, pullback.lift_snd]
      apply internalPathCylinder_injective
      rw [internalPathCylinder_naturality, internalPathCylinder_transpose]
      exact hei
  · simp only [simplicialMappingPathProjection, ← Category.assoc, pullback.lift_snd]
    rw [← internalPathCylinder_end, internalPathCylinder_transpose, he₁]

/-- With Kan source and target, this is an actual Kan fibration. -/
theorem simplicialMappingPath_projection_fibration {X Y : SSet.{0}}
    (p : X ⟶ Y) [SSet.KanComplex X] [SSet.KanComplex Y] :
    HomotopicalAlgebra.Fibration (simplicialMappingPathProjection p) := by
  rw [fibration_iff]
  intro A B i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨j⟩⟩ := hi
  exact simplicialMappingPath_projection_lifting p _ (SSet.anodyneExtensions.horn_ι j)

end

end Thomason.Construction

end

section

/-! # Comparison with the genuine continuous mapping-path space -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The continuous path attached to a point in the realized simplicial
mapping-path object starts at the image of its first coordinate. -/
theorem realizedMappingPath_start {X Y : SSet.{0}} (p : X ⟶ Y) :
    SSet.toTop.map (pullback.snd p (internalPathStart Y)) ≫
        realizedInternalPathComparison Y ≫ continuousPathStart (SSet.toTop.obj Y) =
      SSet.toTop.map (simplicialMappingPathRetraction p) ≫ SSet.toTop.map p := by
  rw [realizedInternalPathComparison_start, ← SSet.toTop.map_comp,
    ← pullback.condition, SSet.toTop.map_comp]

/-- Realization of the actual simplicial pullback maps to the actual
continuous mapping-path pullback, without asserting preservation of pullbacks. -/
def realizedMappingPathComparison {X Y : SSet.{0}} (p : X ⟶ Y) :
    SSet.toTop.obj (simplicialMappingPath p) ⟶ mappingPathSpace (SSet.toTop.map p) :=
  TopCat.ofHom {
    toFun z := ⟨((SSet.toTop.map (simplicialMappingPathRetraction p)).hom z,
      (show C(unitInterval, SSet.toTop.obj Y) from
        (realizedInternalPathComparison Y).hom
          ((SSet.toTop.map (pullback.snd p (internalPathStart Y))).hom z))),
      congrArg (fun f => f.hom z) (realizedMappingPath_start p)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · exact (SSet.toTop.map (simplicialMappingPathRetraction p)).hom.continuous
      · exact (realizedInternalPathComparison Y).hom.continuous.comp
          (SSet.toTop.map (pullback.snd p (internalPathStart Y))).hom.continuous }

@[reassoc]
theorem realizedMappingPathComparison_retraction {X Y : SSet.{0}} (p : X ⟶ Y) :
    realizedMappingPathComparison p ≫ mappingPathRetraction (SSet.toTop.map p) =
      SSet.toTop.map (simplicialMappingPathRetraction p) := rfl

@[reassoc]
theorem realizedMappingPathComparison_projection {X Y : SSet.{0}} (p : X ⟶ Y) :
    realizedMappingPathComparison p ≫ mappingPathProjection (SSet.toTop.map p) =
      SSet.toTop.map (simplicialMappingPathProjection p) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  simp only [simplicialMappingPathProjection, SSet.toTop.map_comp]
  exact realizedInternalPathComparison_end Y
    ((SSet.toTop.map (pullback.snd p (internalPathStart Y))).hom z)

/-- The comparison is an actual weak homotopy equivalence for every map
into a Kan complex. Both retractions to the source have been proved weak,
so no general realization/pullback or singular-counit theorem is required. -/
theorem realizedMappingPathComparison_weak {X Y : SSet.{0}} (p : X ⟶ Y)
    [SSet.KanComplex Y] : topologicalWeakEquivalences (realizedMappingPathComparison p) := by
  have hr : topologicalWeakEquivalences (mappingPathRetraction (SSet.toTop.map p)) :=
    homotopyEquiv_isWeakHomotopyEquivalence (mappingPathEquiv (SSet.toTop.map p)).symm
  apply topologicalWeakEquivalences.of_postcomp _ _ hr
  rw [realizedMappingPathComparison_retraction]
  exact simplicialMappingPath_retraction_weak p

end

end Thomason.Construction

end

section

/-! # Mapping-path comparisons over arbitrary simplicial bases -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Shrinking the path preserves its start, so it restricts to every
mapping-path pullback, even when the base is not Kan. -/
def simplicialMappingPathShrinkingMap {X Y : SSet.{0}} (p : X ⟶ Y) :
    simplicialMappingPath p ⊗ Δ[1] ⟶ simplicialMappingPath p :=
  pullback.lift
    (fst (simplicialMappingPath p) Δ[1] ≫ simplicialMappingPathRetraction p)
    ((pullback.snd p (internalPathStart Y)) ▷ Δ[1] ≫ internalPathShrinkingMap Y) (by
      calc
        _ = fst (simplicialMappingPath p) Δ[1] ≫
            (pullback.snd p (internalPathStart Y) ≫ internalPathStart Y) := by
          rw [Category.assoc, ← pullback.condition]
        _ = _ := by
          simp only [Category.assoc, internalPathShrinkingMap_start]
          rw [← Category.assoc (pullback.snd p (internalPathStart Y) ▷ Δ[1]),
            whiskerRight_fst, Category.assoc])

@[reassoc]
theorem simplicialMappingPathShrinkingMap_fst {X Y : SSet.{0}} (p : X ⟶ Y) :
    simplicialMappingPathShrinkingMap p ≫ simplicialMappingPathRetraction p =
      fst (simplicialMappingPath p) Δ[1] ≫ simplicialMappingPathRetraction p :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem simplicialMappingPathShrinkingMap_snd {X Y : SSet.{0}} (p : X ⟶ Y) :
    simplicialMappingPathShrinkingMap p ≫ pullback.snd p (internalPathStart Y) =
      (pullback.snd p (internalPathStart Y)) ▷ Δ[1] ≫ internalPathShrinkingMap Y :=
  pullback.lift_snd _ _ _

private theorem path_iota_zero_naturality {A B : SSet.{0}} (f : A ⟶ B) :
    SSet.ι₀ ≫ f ▷ (Δ[1] : SSet.{0}) = f ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

private theorem path_iota_one_naturality {A B : SSet.{0}} (f : A ⟶ B) :
    SSet.ι₁ ≫ f ▷ (Δ[1] : SSet.{0}) = f ≫ SSet.ι₁ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- The pullback contraction is an actual simplicial homotopy from the
inclusion followed by retraction to the identity, over the source. -/
def simplicialMappingPathContraction {X Y : SSet.{0}} (p : X ⟶ Y) :
    SSet.Homotopy (simplicialMappingPathRetraction p ≫ simplicialMappingPathInclusion p)
      (𝟙 (simplicialMappingPath p)) where
  h := simplicialMappingPathShrinkingMap p
  h₀ := by
    change SSet.ι₀ ≫ simplicialMappingPathShrinkingMap p =
      simplicialMappingPathRetraction p ≫ simplicialMappingPathInclusion p
    have hzero : SSet.ι₀ ≫ internalPathShrinkingMap Y =
        internalPathStart Y ≫ internalPathConstant Y := (internalPathContraction Y).h₀
    apply pullback.hom_ext
    · rw [Category.assoc, simplicialMappingPathShrinkingMap_fst,
        ← Category.assoc, SSet.ι₀_fst, Category.id_comp,
        Category.assoc, simplicialMappingPath_inclusion_retraction, Category.comp_id]
    · rw [Category.assoc, simplicialMappingPathShrinkingMap_snd, ← Category.assoc,
        path_iota_zero_naturality, Category.assoc, hzero]
      change pullback.snd p (internalPathStart Y) ≫
        (internalPathStart Y ≫ internalPathConstant Y) =
          simplicialMappingPathRetraction p ≫
            (simplicialMappingPathInclusion p ≫ pullback.snd p (internalPathStart Y))
      rw [simplicialMappingPathInclusion, pullback.lift_snd,
        ← Category.assoc, ← pullback.condition, Category.assoc]
  h₁ := by
    change SSet.ι₁ ≫ simplicialMappingPathShrinkingMap p = 𝟙 _
    have hone : SSet.ι₁ ≫ internalPathShrinkingMap Y = 𝟙 _ := (internalPathContraction Y).h₁
    apply pullback.hom_ext
    · simp only [Category.assoc, simplicialMappingPathShrinkingMap_fst,
        SSet.ι₁_fst_assoc, Category.id_comp]
    · rw [Category.assoc, simplicialMappingPathShrinkingMap_snd, ← Category.assoc,
        path_iota_one_naturality, Category.assoc, hone,
        Category.comp_id, Category.id_comp]
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- The retraction is weak for every map, without requiring a Kan base. -/
theorem simplicialMappingPath_retraction_weak_unconditional {X Y : SSet.{0}} (p : X ⟶ Y) :
    realizationWeakEquivalences (simplicialMappingPathRetraction p) := by
  have hi := simplicial_retraction_weak_of_zigzag (simplicialMappingPathInclusion p)
    (simplicialMappingPathRetraction p)
    (simplicialMappingPathRetraction p ≫ simplicialMappingPathInclusion p)
    (simplicialMappingPath_inclusion_retraction p) (simplicialMappingPathContraction p)
    (SSet.RelativeMorphism.Homotopy.refl _)
  apply realizationWeakEquivalences.of_precomp (simplicialMappingPathInclusion p) _ hi
  rw [simplicialMappingPath_inclusion_retraction]
  exact realizationWeakEquivalences.id_mem _

/-- The actual comparison with continuous mapping paths is weak over every
simplicial base, and still commutes exactly with the original projection. -/
theorem realizedMappingPathComparison_weak_unconditional {X Y : SSet.{0}} (p : X ⟶ Y) :
    topologicalWeakEquivalences (realizedMappingPathComparison p) := by
  have hr : topologicalWeakEquivalences (mappingPathRetraction (SSet.toTop.map p)) :=
    homotopyEquiv_isWeakHomotopyEquivalence (mappingPathEquiv (SSet.toTop.map p)).symm
  apply topologicalWeakEquivalences.of_postcomp _ _ hr
  rw [realizedMappingPathComparison_retraction]
  exact simplicialMappingPath_retraction_weak_unconditional p

end

end Thomason.Construction

end

section

/-! # The actual mapping-path inclusion is anodyne over every base -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Shrinking paths in a mapping-path object fixes the original source
as an entire simplicial subobject, in every parameter degree. -/
theorem simplicialMappingPathShrinkingMap_stationary {X Y : SSet.{0}} (p : X ⟶ Y) :
    (simplicialMappingPathInclusion p) ▷ (Δ[1] : SSet.{0}) ≫
        simplicialMappingPathShrinkingMap p =
      fst X Δ[1] ≫ simplicialMappingPathInclusion p := by
  apply pullback.hom_ext
  · rw [Category.assoc, simplicialMappingPathShrinkingMap_fst,
      ← Category.assoc, whiskerRight_fst, Category.assoc]
  · rw [Category.assoc, simplicialMappingPathShrinkingMap_snd,
      ← Category.assoc, ← comp_whiskerRight]
    have hi : simplicialMappingPathInclusion p ≫ pullback.snd p (internalPathStart Y) =
        p ≫ internalPathConstant Y := pullback.lift_snd _ _ _
    rw [hi, comp_whiskerRight, Category.assoc, internalPathShrinkingMap_constant,
      ← Category.assoc, whiskerRight_fst, Category.assoc, ← hi, Category.assoc]

/-- The first map in the actual mapping-path factorization is always
anodyne, not merely a realization weak equivalence. -/
theorem simplicialMappingPathInclusion_anodyne {X Y : SSet.{0}} (p : X ⟶ Y) :
    SSet.anodyneExtensions (simplicialMappingPathInclusion p) := by
  have : Mono (simplicialMappingPathInclusion p) :=
    mono_of_mono_fac (simplicialMappingPath_inclusion_retraction p)
  exact anodyne_of_simplicial_deformation (simplicialMappingPathInclusion p)
    (simplicialMappingPathRetraction p) (simplicialMappingPath_inclusion_retraction p)
    (simplicialMappingPathContraction p) (simplicialMappingPathShrinkingMap_stationary p)

/-- The endpoint projection has exactly the weak-equivalence status of the
original map over arbitrary simplicial bases. -/
theorem simplicialMappingPath_projection_weak_iff_unconditional {X Y : SSet.{0}}
    (p : X ⟶ Y) :
    realizationWeakEquivalences (simplicialMappingPathProjection p) ↔
      realizationWeakEquivalences p := by
  have hi := anodyne_realization_weak _ (simplicialMappingPathInclusion_anodyne p)
  constructor
  · intro h
    simpa only [simplicialMappingPath_factorization] using
      realizationWeakEquivalences.comp_mem _ _ hi h
  · intro h
    apply realizationWeakEquivalences.of_precomp _ _ hi
    simpa only [simplicialMappingPath_factorization] using h

end

end Thomason.Construction

end

section

/-! # Naturality of finite cubical singular lifts along faces -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory

noncomputable section

/-- The continuous insertion of one endpoint coordinate. -/
def insertEndpoint (n : ℕ) (i : Fin (n+1)) (e : Bool) :
    C((Fin n → unitInterval), Fin (n+1) → unitInterval) :=
  ⟨fun p => (Fin.insertNth i (endpoint e) p : Fin (n+1) → unitInterval), by
    apply continuous_pi
    intro j
    rcases eq_or_ne j i with rfl | h
    · simpa only [Fin.insertNth_apply_same] using
        (continuous_const : Continuous (fun _ : Fin n → unitInterval => endpoint e))
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
      simpa only [Fin.insertNth_apply_succAbove] using (continuous_apply k)⟩

/-- Restriction of a singular cube agrees with the singular cube of the restricted map. -/
theorem singularMap_face_naturality {X : TopCat.{0}} (n : ℕ)
    (p : C((Fin (n+1) → unitInterval), X)) (i : Fin (n+1)) (e : Bool) :
    face n i e ≫ singularMap (n+1) p = singularMap n (p.comp (insertEndpoint n i e)) := by
  change face n i e ≫ sSetTopAdj.homEquiv _ _
    (TopCat.ofHom (p.comp (coordinates (n+1)))) = sSetTopAdj.homEquiv _ _ _
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  exact congrArg p (coordinates_face n i e z)

/-- The realized cubical lift of a continuous map. -/
def liftMap {X : TopCat.{0}} (n : ℕ) (p : C((Fin n → unitInterval), X)) :
    C((Fin n → unitInterval), SSet.toTop.obj (TopCat.toSSet.obj X)) :=
  (SSet.toTop.map (singularMap n p)).hom.comp (sectionMap n)

/-- The continuous lift also commutes exactly with every cubical face. -/
theorem liftMap_face {X : TopCat.{0}} (n : ℕ)
    (p : C((Fin (n+1) → unitInterval), X)) (i : Fin (n+1)) (e : Bool)
    (t : Fin n → unitInterval) :
    liftMap (n+1) p (Fin.insertNth i (endpoint e) t) =
      liftMap n (p.comp (insertEndpoint n i e)) t := by
  change (SSet.toTop.map (singularMap (n+1) p)).hom
    (sectionMap (n+1) (Fin.insertNth i (endpoint e) t)) = _
  rw [section_face]
  have h := SSet.toTop.congr_map (singularMap_face_naturality n p i e)
  rw [SSet.toTop.map_comp] at h
  exact congrArg (fun f => f.hom (sectionMap n t)) h

/-- A constant topological cube has the constant lift at its singular vertex. -/
theorem liftMap_const (X : TopCat.{0}) (n : ℕ) (x : X) (t : Fin n → unitInterval) :
    liftMap n (ContinuousMap.const _ x) t = singularVertex X x := by
  have h : singularMap n (ContinuousMap.const _ x) =
      SSet.const (TopCat.toSSetObj₀Equiv.symm x) := singular_adjoint_const _ X x
  change (SSet.toTop.map (singularMap n (ContinuousMap.const _ x))).hom (sectionMap n t) = _
  rw [h]
  exact realized_singular_const _ X x _

end

end Thomason.Construction.RealizedCube

end

end OAI
