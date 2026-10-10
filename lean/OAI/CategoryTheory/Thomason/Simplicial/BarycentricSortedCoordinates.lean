import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.FiniteSingularRelativeLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.SingularCubeNaturality
import OAI.CategoryTheory.Thomason.Transfer.NonsingularFaceGluing
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

namespace OAI

section

/-! # Relative weak Kan lifting inside a finite-base Kan subfibration -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- A finite simplicial lifting problem for an actual weak Kan fibration
has a continuous relative lift inside a Kan subfibration over a finite
base. Both original boundary maps are kept simplicial and exact, and the
entire projection homotopy stays inside that finite base. -/
theorem finite_weak_kan_relative_lift {E Y A K : SSet.{0}} [K.Finite]
    (p : E ⟶ Y) [HomotopicalAlgebra.Fibration p]
    (hp : realizationWeakEquivalences p) (i : A ⟶ K) [Mono i]
    (a : A ⟶ E) (b : K ⟶ Y) (h : a ≫ p = i ≫ b) :
    ∃ (T : Y.Subcomplex) (_ : SSet.Finite T.toSSet)
      (U : E.Subcomplex) (q : U.toSSet ⟶ T.toSSet)
      (_ : HomotopicalAlgebra.Fibration q)
      (aU : A ⟶ U.toSSet) (bT : K ⟶ T.toSSet)
      (c : SSet.toTop.obj K ⟶ SSet.toTop.obj U.toSSet),
      q ≫ T.ι = U.ι ≫ p ∧ aU ≫ U.ι = a ∧ bT ≫ T.ι = b ∧
      aU ≫ q = i ≫ bT ∧ SSet.toTop.map i ≫ c = SSet.toTop.map aU ∧
      Nonempty ((c ≫ SSet.toTop.map q).hom.HomotopyRel
        (SSet.toTop.map bT).hom (Set.range (SSet.toTop.map i).hom)) := by
  have ht : SSet.toTop.map a ≫ SSet.toTop.map p =
      SSet.toTop.map i ≫ SSet.toTop.map b := by
    rw [← SSet.toTop.map_comp, h, SSet.toTop.map_comp]
  obtain ⟨S, V, hS, hV, r, aS, cS, bV, hr, haS, hcS, hbV, ⟨H⟩⟩ :=
    finite_relative_lift_with_homotopy_support i p hp a (SSet.toTop.map b) ht
  have : SSet.Finite S.toSSet := hS
  have : SSet.Finite V.toSSet := hV
  let T : Y.Subcomplex := V ⊔ SSet.Subcomplex.range b
  have hT : SSet.Finite T.toSSet := by
    let W : Bool → Y.Subcomplex := fun t => if t then V else SSet.Subcomplex.range b
    have he : T = iSup W := by
      apply le_antisymm
      · exact sup_le (le_iSup W true) (le_iSup W false)
      · apply iSup_le
        intro t
        cases t
        · exact le_sup_right
        · exact le_sup_left
    rw [he]
    apply (SSet.finite_iSup_iff W).mpr
    intro t
    cases t <;> dsimp [W] <;> infer_instance
  have : SSet.Finite T.toSSet := hT
  let j : V.toSSet ⟶ T.toSSet := SSet.Subcomplex.homOfLE le_sup_left
  let bT : K ⟶ T.toSSet := T.lift b le_sup_right
  have hj : j ≫ T.ι = V.ι := rfl
  have hbT : bT ≫ T.ι = b := rfl
  have hST : S ≤ T.preimage p := by
    intro d x hx
    have he := congrArg (fun f => f.app d ⟨x, hx⟩) hr
    change V.ι.app d (r.app d ⟨x, hx⟩) = p.app d x at he
    change p.app d x ∈ T.obj d
    rw [← he]
    exact (show V ≤ T from le_sup_left) _ (r.app d ⟨x, hx⟩).property
  obtain ⟨U, q, hSU, _, hq, hqKan, _⟩ :=
    exists_finite_exhausted_kan_subfibration p T S hST
  let k : S.toSSet ⟶ U.toSSet := SSet.Subcomplex.homOfLE hSU
  have hk : k ≫ U.ι = S.ι := rfl
  have hkq : k ≫ q = r ≫ j := by
    apply (cancel_mono T.ι).mp
    rw [Category.assoc, hq, ← Category.assoc, hk,
      Category.assoc, hj, hr]
  let aU := aS ≫ k
  let c := cS ≫ SSet.toTop.map k
  have haU : aU ≫ U.ι = a := by
    dsimp only [aU]
    rw [Category.assoc, hk, haS]
  have hsquare : aU ≫ q = i ≫ bT := by
    apply (cancel_mono T.ι).mp
    rw [Category.assoc, hq, ← Category.assoc, haU,
      Category.assoc, hbT, h]
  have hc : SSet.toTop.map i ≫ c = SSet.toTop.map aU := by
    dsimp only [c, aU]
    rw [← Category.assoc, hcS, ← SSet.toTop.map_comp]
  have hzero : (SSet.toTop.map j).hom.comp (cS ≫ SSet.toTop.map r).hom =
      (c ≫ SSet.toTop.map q).hom := by
    apply ContinuousMap.ext
    intro x
    have he := congrArg (fun f => f.hom (cS.hom x)) (SSet.toTop.congr_map hkq)
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at he
    exact he.symm
  have hone : (SSet.toTop.map j).hom.comp bV.hom = (SSet.toTop.map bT).hom := by
    apply ContinuousMap.ext
    intro x
    apply RealizationPrism.inclusion_injective Y T
    have he := congrArg (fun f => f.hom (bV.hom x)) (SSet.toTop.congr_map hj)
    rw [SSet.toTop.map_comp] at he
    have he' := congrArg (fun f => f.hom x) hbV
    have hb' := congrArg (fun f => f.hom x) (SSet.toTop.congr_map hbT)
    rw [SSet.toTop.map_comp] at hb'
    exact (he.trans he').trans hb'.symm
  exact ⟨T, hT, U, q, hqKan, aU, bT, c, hq, haU, hbT, hsquare, hc,
    ⟨(H.compContinuousMap (SSet.toTop.map j).hom).cast hzero hone⟩⟩

end

end Thomason.Construction

end

section

/-! # Finite approximation through iterated actual subdivision -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- The iterates used in finite simplicial approximation, with zero iterate
included so that exact factorization can be proved by induction. -/
def iteratedSubdivision : ℕ → SSet.{0} ⥤ SSet.{0}
  | 0 => 𝟭 _
  | n+1 => iteratedSubdivision n ⋙ SSet.sd

theorem iteratedSubdivision_finite (n : ℕ) (K : SSet.{0}) [K.Finite] :
    ((iteratedSubdivision n).obj K).Finite := by
  induction n with
  | zero => exact inferInstanceAs K.Finite
  | succ n ih =>
    let := ih
    exact subdivision_finite _

theorem iteratedSubdivision_mono (n : ℕ) {K L : SSet.{0}} (f : K ⟶ L) [Mono f] :
    Mono ((iteratedSubdivision n).map f) := by
  induction n with
  | zero => exact inferInstanceAs (Mono f)
  | succ n ih =>
    let := ih
    exact subdivision_map_mono _

/-- Iteration preserves and reflects the actual realization weak equivalences. -/
theorem iteratedSubdivision_weak_iff (n : ℕ) {K L : SSet.{0}} (f : K ⟶ L) :
    realizationWeakEquivalences ((iteratedSubdivision n).map f) ↔
      realizationWeakEquivalences f := by
  induction n with
  | zero => rfl
  | succ n ih => exact (subdivision_weak_iff _).trans ih

/-- A finite family of simplices in an arbitrary iterate is supported over a
single finite subcomplex of the original simplicial set. -/
theorem finite_map_iteratedSubdivision_factors (n : ℕ) {T K : SSet.{0}} [T.Finite]
    (f : T ⟶ (iteratedSubdivision n).obj K) :
    ∃ A : K.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : T ⟶ (iteratedSubdivision n).obj A.toSSet,
        g ≫ (iteratedSubdivision n).map A.ι = f := by
  induction n generalizing T with
  | zero =>
    change T ⟶ K at f
    exact ⟨SSet.Subcomplex.range f, inferInstance, SSet.Subcomplex.toRange f, rfl⟩
  | succ n ih =>
    obtain ⟨A, hA, g, hg⟩ := finite_map_subdivision_factors f
    let := hA
    obtain ⟨B, hB, b, hb⟩ := ih A.ι
    refine ⟨B, hB, g ≫ SSet.sd.map b, ?_⟩
    change (g ≫ SSet.sd.map b) ≫ SSet.sd.map ((iteratedSubdivision n).map B.ι) = f
    rw [Category.assoc, ← SSet.sd.map_comp, hb]
    exact hg

end

end Thomason.Construction

end

section

/-! # Exact compact and relative support over finite subdivision carriers -/

namespace Thomason.Construction

open CategoryTheory Topology

noncomputable section

/-- The actual realization of a subdivided subcomplex inclusion is injective. -/
theorem iteratedSubdivisionInclusion_injective (n : ℕ) {K : SSet.{0}}
    (A : K.Subcomplex) : Function.Injective
      (SSet.toTop.map ((iteratedSubdivision n).map A.ι)).hom := by
  let f := (iteratedSubdivision n).map A.ι
  have : Mono f := iteratedSubdivision_mono n A.ι
  let q := SSet.Subcomplex.toRange f
  have : IsIso q := inferInstance
  intro x y h
  apply (TopCat.mono_iff_injective (SSet.toTop.map q)).mp inferInstance
  apply RealizationPrism.inclusion_injective ((iteratedSubdivision n).obj K)
    (SSet.Subcomplex.range f)
  change (SSet.toTop.map q ≫ SSet.toTop.map (SSet.Subcomplex.range f).ι).hom x =
    (SSet.toTop.map q ≫ SSet.toTop.map (SSet.Subcomplex.range f).ι).hom y
  rw [← SSet.toTop.map_comp]
  exact h

/-- Compact maps into any subdivision iterate are supported over the iterate
of a finite subcomplex of the original simplicial set. -/
theorem compact_map_iteratedSubdivision_factors {X : Type}
    [TopologicalSpace X] [CompactSpace X] (n : ℕ) (K : SSet.{0})
    (f : C(X, SSet.toTop.obj ((iteratedSubdivision n).obj K))) :
    ∃ A : K.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ g : C(X, SSet.toTop.obj ((iteratedSubdivision n).obj A.toSSet)),
        (SSet.toTop.map ((iteratedSubdivision n).map A.ι)).hom.comp g = f := by
  obtain ⟨T, hT, u, hu⟩ := RealizationPrism.compact_map_factors _ f
  let := hT
  obtain ⟨A, hA, b, hb⟩ := finite_map_iteratedSubdivision_factors n T.ι
  refine ⟨A, hA, (SSet.toTop.map b).hom.comp u, ?_⟩
  calc
    _ = (SSet.toTop.map (b ≫ (iteratedSubdivision n).map A.ι)).hom.comp u := by
      rw [SSet.toTop.map_comp]
      rfl
    _ = f := by rw [hb]; exact hu

/-- A relative homotopy has a single finite support before subdivision,
including both endpoint maps and every point of the fixed locus. -/
theorem compact_homotopy_iteratedSubdivision_factors {X : Type}
    [TopologicalSpace X] [CompactSpace X] (n : ℕ) (K : SSet.{0}) (S : Set X)
    {f g : C(X, SSet.toTop.obj ((iteratedSubdivision n).obj K))}
    (H : f.HomotopyRel g S) :
    ∃ A : K.Subcomplex, SSet.Finite A.toSSet ∧
      ∃ (f' g' : C(X, SSet.toTop.obj ((iteratedSubdivision n).obj A.toSSet)))
        (H' : f'.HomotopyRel g' S),
        (∀ x, (SSet.toTop.map ((iteratedSubdivision n).map A.ι)).hom (f' x) = f x) ∧
        (∀ x, (SSet.toTop.map ((iteratedSubdivision n).map A.ι)).hom (g' x) = g x) ∧
        (∀ z, (SSet.toTop.map ((iteratedSubdivision n).map A.ι)).hom (H' z) = H z) := by
  let F : C(unitInterval × X, SSet.toTop.obj ((iteratedSubdivision n).obj K)) :=
    ⟨H, H.continuous⟩
  obtain ⟨A, hA, u, hu⟩ := compact_map_iteratedSubdivision_factors n K F
  have he (z) : (SSet.toTop.map ((iteratedSubdivision n).map A.ι)).hom (u z) = H z :=
    congrArg (fun v : C(_, _) => v z) hu
  let f' : C(X, SSet.toTop.obj ((iteratedSubdivision n).obj A.toSSet)) :=
    ⟨fun x => u (0, x), u.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let g' : C(X, SSet.toTop.obj ((iteratedSubdivision n).obj A.toSSet)) :=
    ⟨fun x => u (1, x), u.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H' : f'.HomotopyRel g' S := {
    toFun := u
    continuous_toFun := u.continuous
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl
    prop' := by
      intro t x hx
      apply iteratedSubdivisionInclusion_injective n A
      exact (he (t,x)).trans ((H.eq_fst t hx).trans
        ((H.apply_zero x).symm.trans (he (0,x)).symm)) }
  exact ⟨A, hA, f', g', H',
    fun x => (he (0,x)).trans (H.apply_zero x),
    fun x => (he (1,x)).trans (H.apply_one x), he⟩

end

end Thomason.Construction

end

section

/-! # Filtered colimits and the simplicial Kan classes

Extension commutes with filtered colimits because each subdivided simplex
is finite. Finite lifting squares also appear at a common stage, with
their equation valid at a later stage. No stage maps need be monic.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Evaluation of extension is represented by the actual subdivided simplex. -/
def extensionEvaluationIso (d : SimplexCategoryᵒᵖ) :
    SSet.ex.{0} ⋙ SSet.evaluation.obj d ≅
      coyoneda.obj (Opposite.op (SimplexCategory.sd.{0}.obj d.unop)) :=
  NatIso.ofComponents (fun _ => Equiv.ulift.toIso) (by
    intro X Y f
    ext x
    rfl)

instance extension_preservesFilteredColimitsOfShape {J : Type} [Category.{0} J]
    [IsFiltered J] : PreservesColimitsOfShape J SSet.ex.{0} := by
  apply preservesColimitsOfShape_of_evaluation
  intro d
  have : ((SSet.stdSimplex.{0} ⋙ SSet.sd).obj d.unop).Finite :=
    subdivision_standard_finite d.unop
  have : (SimplexCategory.sd.{0}.obj d.unop).Finite :=
    SSet.finite_of_iso (SSet.stdSimplex.sdIso.app d.unop)
  exact preservesColimitsOfShape_of_natIso (extensionEvaluationIso d).symm

instance extension_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{0,0} SSet.ex.{0} where
  preserves_filtered_colimits _J := inferInstance

section FiniteLifting

variable {K : Type} [Category.{0} K] [IsFiltered K]
    {D E : K ⥤ SSet.{0}} {c : Cocone D} {d : Cocone E}

/-- A finite lifting square in a filtered colimit becomes an exact square
at one stage, and hence inherits a lift from the stagewise right maps. -/
theorem filtered_colimit_hasLiftingProperty (hc : IsColimit c) (hd : IsColimit d)
    (η : D ⟶ E) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.ι.app j ≫ p = η.app j ≫ d.ι.app j)
    {A B : SSet.{0}} [A.Finite] [B.Finite] (i : A ⟶ B)
    (hi : ∀ j, HasLiftingProperty i (η.app j)) : HasLiftingProperty i p := by
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨j, a₀, ha₀⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc a
  obtain ⟨k, b₀, hb₀⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hd b
  let l := IsFiltered.max j k
  let a₁ := a₀ ≫ D.map (IsFiltered.leftToMax j k)
  let b₁ := b₀ ≫ E.map (IsFiltered.rightToMax j k)
  have ha₁ : a₁ ≫ c.ι.app l = a := by
    dsimp only [a₁, l]
    rw [Category.assoc, c.w, ha₀]
  have hb₁ : b₁ ≫ d.ι.app l = b := by
    dsimp only [b₁, l]
    rw [Category.assoc, d.w, hb₀]
  have he : (a₁ ≫ η.app l) ≫ d.ι.app l = (i ≫ b₁) ≫ d.ι.app l := by
    rw [Category.assoc, ← hp, ← Category.assoc, ha₁, Category.assoc, hb₁]
    exact sq.w
  obtain ⟨m, u, hu⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (coyoneda.obj (Opposite.op A)) hd)
    (a₁ ≫ η.app l) (i ≫ b₁)).mp he
  have hh : (a₁ ≫ D.map u) ≫ η.app m = i ≫ (b₁ ≫ E.map u) := by
    rw [Category.assoc, η.naturality, ← Category.assoc]
    exact hu
  let : HasLiftingProperty i (η.app m) := hi m
  let t : CommSq (a₁ ≫ D.map u) i (η.app m) (b₁ ≫ E.map u) := ⟨hh⟩
  refine ⟨⟨{ l := t.lift ≫ c.ι.app m, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, t.fac_left, Category.assoc, c.w, ha₁]
  · rw [Category.assoc, hp, ← Category.assoc, t.fac_right,
      Category.assoc, d.w, hb₁]

theorem filtered_colimit_fibration (hc : IsColimit c) (hd : IsColimit d)
    (η : D ⟶ E) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.ι.app j ≫ p = η.app j ≫ d.ι.app j)
    (hη : ∀ j, J.rlp (η.app j)) : J.rlp p := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  apply filtered_colimit_hasLiftingProperty hc hd η p hp
  intro j
  exact hη j _ (horn_ι_mem_J (n + 1) k)

theorem filtered_colimit_boundary_rlp (hc : IsColimit c) (hd : IsColimit d)
    (η : D ⟶ E) (p : c.pt ⟶ d.pt)
    (hp : ∀ j, c.ι.app j ≫ p = η.app j ≫ d.ι.app j)
    (hη : ∀ j, I.rlp (η.app j)) : I.rlp p := by
  intro A B i hi
  obtain ⟨n⟩ := hi
  apply filtered_colimit_hasLiftingProperty hc hd η p hp
  intro j
  exact hη j _ (boundary_ι_mem_I n)

theorem filtered_colimit_kan (hc : IsColimit c) (hD : ∀ j, SSet.KanComplex (D.obj j)) :
    SSet.KanComplex c.pt := by
  apply (HomotopicalAlgebra.isFibrant_iff c.pt).mpr
  apply (fibration_iff _).mpr
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  refine ⟨fun {a _} _ => ?_⟩
  obtain ⟨j, a₀, ha₀⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc a
  let : SSet.KanComplex (D.obj j) := hD j
  obtain ⟨b₀, hb₀⟩ := SSet.KanComplex.hornFilling a₀
  refine ⟨⟨{ l := b₀ ≫ c.ι.app j, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, ← hb₀, ha₀]
  · exact terminalIsTerminal.hom_ext _ _

end FiniteLifting

end

end Thomason.Construction

end

section

/-! # Internal paths commute with filtered colimits

The simplices of the internal path object are represented by products of
two finite standard simplices. This gives preservation for arbitrary
filtered diagrams, without restrictions on their transition maps.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped Simplicial

noncomputable section

abbrev internalPathFunctor : SSet.{0} ⥤ SSet.{0} := ihom (Δ[1] : SSet.{0})

def simplexEvaluationCoyonedaIso (d : SimplexCategoryᵒᵖ) :
    SSet.evaluation.obj d ≅ coyoneda.obj (Opposite.op (SSet.stdSimplex.obj d.unop)) :=
  NatIso.ofComponents (fun _ => SSet.yonedaEquiv.symm.toIso) (by
    intro X Y f
    ext x
    exact (SSet.yonedaEquiv_symm_comp x f).symm)

def internalPathEvaluationIso (d : SimplexCategoryᵒᵖ) :
    internalPathFunctor ⋙ SSet.evaluation.obj d ≅
      coyoneda.obj (Opposite.op ((Δ[1] : SSet.{0}) ⊗ SSet.stdSimplex.obj d.unop)) :=
  Functor.isoWhiskerLeft internalPathFunctor (simplexEvaluationCoyonedaIso d) ≪≫
    ((Adjunction.compCoyonedaIso (ihom.adjunction (Δ[1] : SSet.{0}))).app
      (Opposite.op (SSet.stdSimplex.obj d.unop))).symm

instance internalPath_preservesFilteredColimitsOfShape {J : Type} [Category.{0} J]
    [IsFiltered J] : PreservesColimitsOfShape J internalPathFunctor := by
  apply preservesColimitsOfShape_of_evaluation
  intro d
  exact preservesColimitsOfShape_of_natIso (internalPathEvaluationIso d).symm

instance internalPath_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{0,0} internalPathFunctor where
  preserves_filtered_colimits _J := inferInstance

def internalPathStartNat : internalPathFunctor ⟶ 𝟭 SSet.{0} where
  app := internalPathStart
  naturality _ _ f := internalPathStart_naturality f

def internalPathEndNat : internalPathFunctor ⟶ 𝟭 SSet.{0} where
  app := internalPathEnd
  naturality _ _ f := internalPathEnd_naturality f

instance simplicialFilteredColimit_preservesFiniteLimits {J : Type} [Category.{0} J]
    [IsFiltered J] : PreservesFiniteLimits (colim : (J ⥤ SSet.{0}) ⥤ SSet.{0}) := by
  apply preservesFiniteLimits_of_evaluation
  intro d
  exact preservesFiniteLimits_of_natIso
    (preservesColimitNatIso (SSet.evaluation.obj d)).symm

end

end Thomason.Construction

end

section

/-! # Filtered colimits of the actual simplicial mapping-path construction -/

namespace Thomason.Construction.SimplicialMappingPathDiagram

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {K : Type} [Category.{0} K] {D E : K ⥤ SSet.{0}} (η : D ⟶ E)

def diagram : K ⥤ SSet.{0} where
  obj j := simplicialMappingPath (η.app j)
  map {j k} u := pullback.lift
    (pullback.fst _ _ ≫ D.map u)
    (pullback.snd _ _ ≫ internalPathFunctor.map (E.map u)) (by
      rw [Category.assoc, η.naturality, ← Category.assoc, pullback.condition]
      simp only [Category.assoc, internalPathStart_naturality])
  map_id _ := by
    apply pullback.hom_ext
    · simp
    · simp
  map_comp u v := by
    apply pullback.hom_ext
    · simp only [Functor.map_comp, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [Functor.map_comp, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]

def first : diagram η ⟶ D where
  app _ := pullback.fst _ _
  naturality _ _ _ := pullback.lift_fst _ _ _

def path : diagram η ⟶ E ⋙ internalPathFunctor where
  app _ := pullback.snd _ _
  naturality _ _ _ := pullback.lift_snd _ _ _

def start : E ⋙ internalPathFunctor ⟶ E := Functor.whiskerLeft E internalPathStartNat

def endpoint : diagram η ⟶ E := path η ≫ Functor.whiskerLeft E internalPathEndNat

theorem square : first η ≫ η = path η ≫ start (E := E) := by
  ext j : 2
  change pullback.fst (η.app j) (internalPathStart (E.obj j)) ≫ η.app j =
    pullback.snd (η.app j) (internalPathStart (E.obj j)) ≫ internalPathStart (E.obj j)
  exact pullback.condition

theorem isPullback : IsPullback (first η) (path η) η (start (E := E)) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ (square η))
  apply evaluationJointlyReflectsLimits
  intro j
  apply (isLimitMapConePullbackConeEquiv ((evaluation K SSet.{0}).obj j)
    (square η)).symm.toFun
  exact pullbackIsPullback (η.app j) (internalPathStart (E.obj j))

variable [IsFiltered K]

abbrev pathColimitIso : colimit (E ⋙ internalPathFunctor) ≅
    internalPathObject (colimit E) := (preservesColimitIso internalPathFunctor E).symm

theorem colimit_start : colimMap (start (E := E)) =
    (pathColimitIso (E := E)).hom ≫ internalPathStart (colimit E) := by
  apply colimit.hom_ext
  intro j
  rw [ι_colimMap]
  change internalPathStart (E.obj j) ≫ colimit.ι E j =
    colimit.ι (E ⋙ internalPathFunctor) j ≫
      (preservesColimitIso internalPathFunctor E).inv ≫ internalPathStart (colimit E)
  rw [ι_preservesColimitIso_inv_assoc]
  exact (internalPathStart_naturality (colimit.ι E j)).symm

theorem colimit_end : colimMap (Functor.whiskerLeft E internalPathEndNat) =
    (pathColimitIso (E := E)).hom ≫ internalPathEnd (colimit E) := by
  apply colimit.hom_ext
  intro j
  rw [ι_colimMap]
  change internalPathEnd (E.obj j) ≫ colimit.ι E j =
    colimit.ι (E ⋙ internalPathFunctor) j ≫
      (preservesColimitIso internalPathFunctor E).inv ≫ internalPathEnd (colimit E)
  rw [ι_preservesColimitIso_inv_assoc]
  exact (internalPathEnd_naturality (colimit.ι E j)).symm

theorem colimit_isPullback : IsPullback (colimMap (first η))
    (colimMap (path η) ≫ (pathColimitIso (E := E)).hom)
    (colimMap η) (internalPathStart (colimit E)) := by
  apply (Functor.map_isPullback (colim : (K ⥤ SSet.{0}) ⥤ SSet.{0})
    (isPullback η)).of_iso (Iso.refl _) (Iso.refl _)
    (pathColimitIso (E := E)) (Iso.refl _)
  · simp
  · simp
  · simp
  · simpa using colimit_start (E := E)

def comparison : colimit (diagram η) ≅ simplicialMappingPath (colimMap η) :=
  (colimit_isPullback η).isoPullback

theorem comparison_projection : (comparison η).hom ≫
    simplicialMappingPathProjection (colimMap η) = colimMap (endpoint η) := by
  dsimp only [comparison]
  rw [simplicialMappingPathProjection, ← Category.assoc,
    IsPullback.isoPullback_hom_snd, Category.assoc, ← colimit_end]
  exact (Functor.map_comp (colim : (K ⥤ SSet.{0}) ⥤ SSet.{0}) _ _).symm

end

end Thomason.Construction.SimplicialMappingPathDiagram

end

section

/-! # Actual barycentric coordinates on a subdivided standard simplex

These are the affine coordinates needed to control the mesh of repeated
subdivisions in the finite relative approximation argument.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder

noncomputable section

abbrev Faces (n : ℕ) := NonemptyFiniteChains (ULift.{0} (Fin (n+1)))

instance (n : ℕ) : Finite (Faces n) := finite_nonemptyFiniteChains _

/-- A face vertex is sent to the uniform barycenter of its original vertices. -/
def face (n : ℕ) (A : Faces n) : StdSimplex ℝ (Fin (n+1)) where
  weights := ∑ a ∈ A.finset, Finsupp.single a.down (1 / (A.finset.card : ℝ))
  nonneg := by
    classical
    apply Finset.sum_nonneg
    intro a ha
    exact Finsupp.single_nonneg.mpr (by positivity)
  total := by
    classical
    rw [← Finsupp.sum_finsetSum_index (by intro; rfl) (by intros; rfl)]
    have he (a : ULift.{0} (Fin (n+1))) :
        (Finsupp.single a.down (1 / (A.finset.card : ℝ))).sum (fun _ r => r) =
          1 / (A.finset.card : ℝ) := Finsupp.sum_single_index rfl
    simp_rw [he]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc : (A.finset.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr A.nonempty).ne'
    exact mul_one_div_cancel hc

theorem face_weight (n : ℕ) (A : Faces n) (i : Fin (n+1)) :
    (face n A).weights i =
      if ULift.up i ∈ A.finset then 1 / (A.finset.card : ℝ) else 0 := by
  classical
  change (∑ a ∈ A.finset, Finsupp.single a.down (1 / (A.finset.card : ℝ))) i = _
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  have he (a : ULift.{0} (Fin (n+1))) : a.down = i ↔ a = ULift.up i :=
    ⟨fun h => ULift.ext _ _ h, fun h => congrArg ULift.down h⟩
  simp_rw [he]
  simp

theorem face_weight_pos_iff (n : ℕ) (A : Faces n) (i : Fin (n+1)) :
    0 < (face n A).weights i ↔ ULift.up i ∈ A.finset := by
  rw [face_weight]
  split_ifs with h
  · simp only [h, iff_true]
    have hc : (0 : ℝ) < A.finset.card := by
      exact_mod_cast Finset.card_pos.mpr A.nonempty
    exact one_div_pos.mpr hc
  · simp only [lt_self_iff_false, h]

/-- Every vertex occurring in a face receives a uniform positive amount
of mass, bounded using the dimension of the original simplex. -/
theorem face_weight_lower (n : ℕ) (A : Faces n) (i : Fin (n+1))
    (hi : ULift.up i ∈ A.finset) :
    1 / ((n : ℝ)+1) ≤ (face n A).weights i := by
  rw [face_weight, ite_eq_left hi]
  have hc : (0 : ℝ) < A.finset.card := by
    exact_mod_cast Finset.card_pos.mpr A.nonempty
  have hb : (A.finset.card : ℝ) ≤ (n : ℝ)+1 := by
    have h := Finset.card_le_univ A.finset
    simpa using (show (A.finset.card : ℝ) ≤
      (Fintype.card (ULift.{0} (Fin (n+1))) : ℝ) by exact_mod_cast h)
  exact one_div_le_one_div_of_le hc hb

/-- All vertices of a subdivided characteristic simplex share one
uniformly positive original vertex. This is the common-mass estimate
used in the mesh contraction argument. -/
theorem simplex_common_vertex (n m : ℕ)
    (s : Fin (m+1) ⥤ Faces n) :
    ∃ v : Fin (n+1), ∀ i : Fin (m+1),
      1 / ((n : ℝ)+1) ≤ (face n (s.obj i)).weights v := by
  obtain ⟨v, hv⟩ := (s.obj 0).nonempty
  refine ⟨v.down, fun i => face_weight_lower n (s.obj i) v.down ?_⟩
  have hi : s.obj 0 ≤ s.obj i := leOfHom (s.map (homOfLE (Fin.zero_le i)))
  exact hi hv

/-- Injective ordinal maps act on faces by taking their actual vertex image. -/
def liftEmbedding {m n : ℕ} (f : Fin (m+1) ↪o Fin (n+1)) :
    ULift.{0} (Fin (m+1)) →o ULift.{0} (Fin (n+1)) where
  toFun a := ULift.up (f a.down)
  monotone' _ _ h := f.monotone h

def faceMap {m n : ℕ} (f : Fin (m+1) ↪o Fin (n+1)) : Faces m →o Faces n :=
  NonemptyFiniteChains.orderHomMap (liftEmbedding f)

/-- Barycenters respect face inclusions; no compatibility with collapsing
ordinal maps is asserted. -/
theorem face_map {m n : ℕ} (f : Fin (m+1) ↪o Fin (n+1)) (A : Faces m) :
    StdSimplex.map f (face m A) = face n (faceMap f A) := by
  classical
  have hu : Function.Injective (liftEmbedding f) := by
    intro a b h
    exact ULift.ext _ _ (f.injective (congrArg ULift.down h))
  apply StdSimplex.ext
  have hface : (faceMap f A).finset = A.finset.image (liftEmbedding f) := by
    ext a
    simp [faceMap, NonemptyFiniteChains.orderHomMap, NonemptyFiniteChains.map]
  rw [StdSimplex.weights_map]
  simp only [face, hface]
  change (∑ a ∈ A.finset, Finsupp.single a.down (1 / (A.finset.card : ℝ))).mapDomain f =
    ∑ a ∈ A.finset.image (liftEmbedding f),
      Finsupp.single a.down (1 / ((A.finset.image (liftEmbedding f)).card : ℝ))
  rw [Finsupp.mapDomain_finsetSum, Finset.card_image_of_injective _ hu,
    Finset.sum_image (fun a _ b _ h => hu h)]
  simp only [Finsupp.mapDomain_single]
  rfl

/-- Affine extension of the face barycenters across the actual face nerve. -/
def point (n : ℕ) (z : SSet.toTop.obj (nerve (Faces n))) :
    StdSimplex ℝ (Fin (n+1)) :=
  (StdSimplex.map (face n) (PosetGeometry.coordinates (Faces n) z)).sConvexComb

theorem point_weights (n : ℕ) (z : SSet.toTop.obj (nerve (Faces n))) :
    (point n z).weights =
      (PosetGeometry.coordinates (Faces n) z).weights.sum
        (fun A r => r • (face n A).weights) := by
  classical
  simp [point, StdSimplex.weights_sConvexComb, Finsupp.sum_mapDomain_index, add_smul]

/-- On each characteristic simplex this is precisely the affine combination
of its face barycenters, including repeated face vertices. -/
theorem point_simplex (n m : ℕ) (s : Fin (m+1) ⥤ Faces n)
    (p : StdSimplex ℝ (Fin (m+1))) :
    point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p) =
      (StdSimplex.map (fun i => face n (s.obj i)) p).sConvexComb := by
  unfold point
  calc
    _ = (StdSimplex.map (face n) (StdSimplex.map s.obj p)).sConvexComb :=
      congrArg (fun q : StdSimplex ℝ (Faces n) => (StdSimplex.map (face n) q).sConvexComb)
        (PosetGeometry.coordinates_simplexPoint (Faces n) s p)
    _ = _ := by rw [← StdSimplex.map_comp]; rfl

theorem point_weight (n : ℕ) [Fintype (Faces n)]
    (z : SSet.toTop.obj (nerve (Faces n))) (j : Fin (n+1)) :
    (point n z).weights j = ∑ A : Faces n,
      (PosetGeometry.coordinates (Faces n) z).weights A * (face n A).weights j := by
  rw [point_weights, Finsupp.sum_apply]
  change (PosetGeometry.coordinates (Faces n) z).weights.sum
    (fun A r => r * (face n A).weights j) = _
  exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)

theorem point_simplex_weight (n m : ℕ)
    (s : Fin (m+1) ⥤ Faces n)
    (p : StdSimplex ℝ (Fin (m+1))) (j : Fin (n+1)) :
    (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p)).weights j =
      ∑ i, p.weights i * (face n (s.obj i)).weights j := by
  classical
  rw [point_simplex, StdSimplex.weights_sConvexComb]
  change ((p.weights.mapDomain (fun i => face n (s.obj i))).sum
    (fun A r => r • A.weights)) j = _
  rw [Finsupp.sum_mapDomain_index
    (h := fun (A : StdSimplex ℝ (Fin (n+1))) (r : ℝ) => r • A.weights)
    (fun _ => zero_smul ℝ _) (fun _ _ _ => add_smul _ _ _), Finsupp.sum_apply]
  change p.weights.sum (fun i r => r * (face n (s.obj i)).weights j) = _
  exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)

/-- A whole subdivided simplex, including its boundary, retains at least
`1/(n+1)` of one common original vertex. -/
theorem simplex_common_mass (n m : ℕ)
    (s : Fin (m+1) ⥤ Faces n) :
    ∃ v : Fin (n+1), ∀ p : StdSimplex ℝ (Fin (m+1)),
      1 / ((n : ℝ)+1) ≤
        (point n (RealizationPrism.simplexPoint (nerve (Faces n)) s p)).weights v := by
  obtain ⟨v, hv⟩ := simplex_common_vertex n m s
  refine ⟨v, fun p => ?_⟩
  rw [point_simplex_weight]
  calc
    _ = ∑ i, p.weights i * (1 / ((n : ℝ)+1)) := by
      rw [← Finset.sum_mul, p.total_of_fintype, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hv i) (p.nonneg i))

/-- The affine barycentric map is continuous on the actual realization. -/
def map (n : ℕ) : C(SSet.toTop.obj (nerve (Faces n)), StdSimplex ℝ (Fin (n+1))) where
  toFun := point n
  continuous_toFun := by
    classical
    let := Fintype.ofFinite (Faces n)
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
    apply continuous_pi
    intro j
    simp only [Function.comp_def, point_weight]
    apply continuous_finsetSum
    intro A _
    exact ((StdSimplex.continuous_weights_apply ℝ A).comp
      (PosetGeometry.coordinates (Faces n)).continuous).mul continuous_const

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Exact barycentric coordinates on an ordered flag chamber

Differences of successive ordered coordinates give nonnegative flag
weights. The weighted telescoping formula is the finite algebra behind
the barycentric subdivision homeomorphism.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity

noncomputable section

theorem weighted_differences_sum (a : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, ((i : ℝ)+1) * (a i-a (i+1))) =
      (∑ i ∈ Finset.range N, a i) - (N : ℝ) * a N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- The k-th face of the full flag contains precisely the first k+1 vertices. -/
def prefixFace (n : ℕ) (k : Fin (n+1)) : Faces n where
  finset := (Finset.Iic k).image ULift.up
  nonempty := ⟨ULift.up 0, Finset.mem_image.mpr ⟨0, Finset.mem_Iic.mpr (Fin.zero_le k), rfl⟩⟩
  comparable _ _ := le_total _ _

theorem prefixFace_card (n : ℕ) (k : Fin (n+1)) :
    (prefixFace n k).finset.card = k.val+1 := by
  classical
  change ((Finset.Iic k).image ULift.up).card = _
  rw [Finset.card_image_of_injective _ ULift.up_injective, Fin.card_Iic]

theorem prefixFace_weight (n : ℕ) (k i : Fin (n+1)) :
    (face n (prefixFace n k)).weights i =
      if i ≤ k then 1 / ((k.val : ℝ)+1) else 0 := by
  classical
  rw [face_weight, prefixFace_card]
  have he : ULift.up i ∈ (prefixFace n k).finset ↔ i ≤ k := by
    simp [prefixFace]
  simp only [he, Nat.cast_add, Nat.cast_one]

/-- The full ascending flag, regarded as a simplex of the face-poset nerve. -/
def prefixSimplex (n : ℕ) : Fin (n+1) ⥤ Faces n :=
  (show Fin (n+1) →o Faces n from
    { toFun := prefixFace n
      monotone' := by
        intro i j hij
        change (Finset.Iic i).image ULift.up ⊆ (Finset.Iic j).image ULift.up
        apply Finset.image_subset_image
        intro a ha
        exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp ha).trans hij) }).monotone.functor

/-- Flag weights associated to a nonincreasing finite list of coordinates. -/
def flagWeights (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i < n+1, a (i+1) ≤ a i)
    (hz : a (n+1) = 0) (ht : (∑ i ∈ Finset.range (n+1), a i) = 1) :
    StdSimplex ℝ (Fin (n+1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun i => ((i.val : ℝ)+1) * (a i.val-a (i.val+1)))
  nonneg i := mul_nonneg (by positivity) (sub_nonneg.mpr (ha i.val i.isLt))
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change (∑ i : Fin (n+1), ((i.val : ℝ)+1) * (a i.val-a (i.val+1))) = 1
    rw [Fin.sum_univ_eq_sum_range (fun k => ((k : ℝ)+1) * (a k-a (k+1))) (n+1),
      weighted_differences_sum, hz, mul_zero, sub_zero, ht]

theorem flagWeights_weight (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i < n+1, a (i+1) ≤ a i)
    (hz : a (n+1) = 0) (ht : (∑ i ∈ Finset.range (n+1), a i) = 1)
    (i : Fin (n+1)) :
    (flagWeights n a ha hz ht).weights i = ((i.val : ℝ)+1) * (a i.val-a (i.val+1)) := rfl

/-- The actual affine subdivision map reconstructs every point in this
ordered chamber, including coincident adjacent coordinates. -/
theorem point_prefix_weight (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i < n+1, a (i+1) ≤ a i)
    (hz : a (n+1) = 0) (ht : (∑ i ∈ Finset.range (n+1), a i) = 1)
    (j : Fin (n+1)) :
    (point n (RealizationPrism.simplexPoint (nerve (Faces n)) (prefixSimplex n)
      (flagWeights n a ha hz ht))).weights j = a j.val := by
  rw [point_simplex_weight]
  change (∑ i : Fin (n+1), (flagWeights n a ha hz ht).weights i *
    (face n (prefixFace n i)).weights j) = _
  simp_rw [flagWeights_weight, prefixFace_weight]
  have hterm (i : Fin (n+1)) :
      (((i.val : ℝ)+1) * (a i.val-a (i.val+1))) *
        (if j ≤ i then 1 / ((i.val : ℝ)+1) else 0) =
      if j.val ≤ i.val then a i.val-a (i.val+1) else 0 := by
    change _ = if j ≤ i then a i.val-a (i.val+1) else 0
    by_cases h : j ≤ i
    · simp only [ite_eq_left h]
      have hden : ((i.val : ℝ)+1) ≠ 0 := by positivity
      field_simp [hden]
    · simp only [ite_eq_right h, mul_zero]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun k => if j.val ≤ k then a k-a (k+1) else 0) (n+1),
    ← Finset.sum_filter]
  have hfilter : (Finset.range (n+1)).filter (j.val ≤ ·) = Finset.Ico j.val (n+1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [hfilter]
  have h := Finset.sum_Ico_sub (fun i => -a i) (Nat.le_of_lt j.isLt)
  simpa only [neg_sub_neg, hz, neg_zero, zero_sub, neg_neg] using h

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Sorting simplex coordinates for the flag decomposition -/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity

noncomputable section

/-- Every finite list of coordinates has a decreasing enumeration, with
an actual permutation retaining repeated coordinate values. -/
theorem exists_antitone_permutation (n : ℕ) (x : Fin (n+1) → ℝ) :
    ∃ σ : Equiv.Perm (Fin (n+1)), Antitone (fun i => x (σ i)) := by
  classical
  let key : ULift.{0} (Fin (n+1)) → ℝ ×ₗ Fin (n+1) :=
    fun i => toLex (-x i.down, i.down)
  have hinj : Function.Injective key := by
    intro i j h
    exact ULift.ext _ _ (congrArg (fun z : ℝ ×ₗ Fin (n+1) => (ofLex z).2) h)
  let : LinearOrder (ULift.{0} (Fin (n+1))) := LinearOrder.lift' key hinj
  let e := monoEquivOfFin (ULift.{0} (Fin (n+1))) (k := n+1)
    (by simp only [Fintype.card_ulift, Fintype.card_fin])
  refine ⟨e.toEquiv.trans Equiv.ulift, ?_⟩
  intro i j hij
  have h : key (e i) ≤ key (e j) := e.map_rel_iff'.mpr hij
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · change x (e j).down ≤ x (e i).down
    dsimp [key] at h
    linarith
  · change x (e j).down ≤ x (e i).down
    dsimp [key] at h
    linarith

/-- Append the terminal zero used in the telescoping flag formula. -/
def sortedSequence (n : ℕ) (p : StdSimplex ℝ (Fin (n+1)))
    (σ : Equiv.Perm (Fin (n+1))) (i : ℕ) : ℝ :=
  if h : i < n+1 then p.weights (σ ⟨i, h⟩) else 0

theorem sortedSequence_zero (n : ℕ) (p : StdSimplex ℝ (Fin (n+1)))
    (σ : Equiv.Perm (Fin (n+1))) : sortedSequence n p σ (n+1) = 0 := by
  simp [sortedSequence]

theorem sortedSequence_antitone (n : ℕ) (p : StdSimplex ℝ (Fin (n+1)))
    (σ : Equiv.Perm (Fin (n+1))) (hσ : Antitone (fun i => p.weights (σ i))) :
    ∀ i < n+1, sortedSequence n p σ (i+1) ≤ sortedSequence n p σ i := by
  intro i hi
  unfold sortedSequence
  rw [dite_eq_left hi]
  split_ifs with hj
  · exact hσ (by change i ≤ i+1; omega)
  · exact p.nonneg _

theorem sortedSequence_total (n : ℕ) (p : StdSimplex ℝ (Fin (n+1)))
    (σ : Equiv.Perm (Fin (n+1))) :
    (∑ i ∈ Finset.range (n+1), sortedSequence n p σ i) = 1 := by
  have h : (∑ i : Fin (n+1), sortedSequence n p σ i.val) =
      ∑ i : Fin (n+1), p.weights (σ i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [sortedSequence, i.isLt]
  rw [Fin.sum_univ_eq_sum_range (sortedSequence n p σ) (n+1)] at h
  rw [h, Equiv.sum_comp σ, p.total_of_fintype]

end

end Thomason.Construction.SubdivisionBarycentric

end

end OAI
