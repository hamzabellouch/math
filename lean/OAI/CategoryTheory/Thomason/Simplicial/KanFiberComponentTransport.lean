import OAI.CategoryTheory.Thomason.Simplicial.KanRealizedEdgeComposition
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.SingularCounitSurjectivity
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

namespace OAI

section

/-! # Naturality of the realized homotopy-category comparison -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- Naturality on an edge includes the actual equalities of its realized
endpoints; no basepoint transport is left implicit. -/
theorem edgePath_class_naturality {X Y : SSet.{0}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    eqToHom (congrArg FundamentalGroupoid.mk (map_vertexPoint f x).symm) ≫
      (FundamentalGroupoid.map (SSet.toTop.map f).hom).map
        (Path.Homotopic.Quotient.mk (edgePath e)) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (map_vertexPoint f y)) =
        Path.Homotopic.Quotient.mk (edgePath (e.map f)) := by
  change eqToHom (congrArg FundamentalGroupoid.mk (map_vertexPoint f x).symm) ≫
    Path.Homotopic.Quotient.mk ((edgePath e).map (SSet.toTop.map f).hom.continuous) ≫
    eqToHom (congrArg FundamentalGroupoid.mk (map_vertexPoint f y)) = _
  rw [FundamentalGroupoid.conj_eqToHom (map_vertexPoint f x).symm
    (map_vertexPoint f y).symm]
  exact congrArg Path.Homotopic.Quotient.mk (edgePath_map f e)

/-- The comparison with the actual fundamental groupoid is natural in
simplicial maps, with the canonical endpoint identifications. -/
def homotopyCategoryToFundamentalGroupoid_naturality {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.mapHomotopyCategory f ⋙ homotopyCategoryToFundamentalGroupoid Y ≅
      homotopyCategoryToFundamentalGroupoid X ⋙
        FundamentalGroupoid.map (SSet.toTop.map f).hom :=
  SSet.Truncated.HomotopyCategory.mkNatIso (V := (SSet.truncation 2).obj X)
    (fun x => eqToIso (congrArg FundamentalGroupoid.mk (map_vertexPoint f x).symm))
    (fun {x y} e => by
      change X _⦋0⦌ at x y
      change SSet.Edge x y at e
      change (homotopyCategoryToFundamentalGroupoid Y).map
          (SSet.HomotopyCategory.homMk ((SSet.Edge.ofTruncated e).map f)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk (map_vertexPoint f _).symm) =
        eqToHom (congrArg FundamentalGroupoid.mk (map_vertexPoint f _).symm) ≫
          (FundamentalGroupoid.map (SSet.toTop.map f).hom).map
            ((homotopyCategoryToFundamentalGroupoid X).map
              (SSet.HomotopyCategory.homMk (SSet.Edge.ofTruncated e)))
      rw [homotopyCategoryToFundamentalGroupoid_map, homotopyCategoryToFundamentalGroupoid_map]
      apply (Iso.eq_comp_inv
        (eqToIso (congrArg FundamentalGroupoid.mk (map_vertexPoint f y).symm))).mp
      exact (edgePath_class_naturality f (SSet.Edge.ofTruncated e)).symm.trans
        (Category.assoc _ _ _).symm)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Relative mapping spaces and exact simplicial lifting

The mapping-space fibration is constructed from the ordinary internal hom.
Surjectivity on its actual path components supplies exact lifts. This lemma
is used as a geometric bridge; no new published input is added to the main
statement, and no weak-equivalence assertion for these mapping spaces is
assumed in the construction.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem zeroFaceSection_naturality {A B : SSet.{0}} (i : A ⟶ B) :
    i ≫ zeroFaceSection B = zeroFaceSection A ≫ i ▷ (Δ[0] : SSet.{0}) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- Vertex-surjectivity is lifting against the initial map into the point. -/
theorem initial_point_lifting_of_vertices {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : Function.Surjective (p.app (.op (.mk 0)))) :
    HasLiftingProperty (initial.to (Δ[0] : SSet.{0})) p := by
  refine ⟨fun {a b} _ => ?_⟩
  obtain ⟨x, hx⟩ := hp (SSet.yonedaEquiv b)
  refine ⟨⟨{ l := SSet.const x, fac_left := ?_, fac_right := ?_ }⟩⟩
  · exact (initialIsInitial (C := SSet.{0})).hom_ext _ _
  · apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const] using hx

/-- Exact lifting of `i` follows from actual component-surjectivity of its
relative mapping-space fibration. Its Kan property is supplied by the proved
pushout-product theorem, independently of Kan–Quillen weak factorization. -/
theorem lifting_of_relativeMapping_components {A B X Y : SSet.{0}}
    (i : A ⟶ B) [Mono i] (p : X ⟶ Y) [HomotopicalAlgebra.Fibration p]
    (q : MonoidalClosed.internalHom.PullbackObjObj i p)
    (hq : Function.Surjective (HomotopyMaps.componentsMap (SSet.toTop.map q.π).hom)) :
    HasLiftingProperty i p := by
  have : HomotopicalAlgebra.Fibration q.π := SSet.fibration_pullbackObjObjπ q
  have hz := initial_point_lifting_of_vertices q.π (kan_fibration_vertices_surjective q.π hq)
  let t := Functor.PushoutObjObj.ofIsInitialRight (curriedTensor SSet) i
    (initial.to (Δ[0] : SSet.{0})) (initialIsInitial (C := SSet.{0}))
  have ht : HasLiftingProperty t.ι p :=
    (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff t q).mpr hz
  have : HasLiftingProperty (i ▷ (Δ[0] : SSet.{0})) p := ht
  refine ⟨fun {a b} sq => ?_⟩
  have hc : (fst A (Δ[0] : SSet.{0}) ≫ a) ≫ p =
      (i ▷ (Δ[0] : SSet.{0})) ≫ (fst B (Δ[0] : SSet.{0}) ≫ b) := by
    rw [Category.assoc, sq.w]
    have hn : i ▷ (Δ[0] : SSet.{0}) ≫ fst B (Δ[0] : SSet.{0}) =
        fst A (Δ[0] : SSet.{0}) ≫ i := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc (i ▷ (Δ[0] : SSet.{0})), hn, Category.assoc]
  let c : CommSq (fst A (Δ[0] : SSet.{0}) ≫ a)
      (i ▷ (Δ[0] : SSet.{0})) p (fst B (Δ[0] : SSet.{0}) ≫ b) := ⟨hc⟩
  refine ⟨⟨{ l := zeroFaceSection B ≫ c.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, zeroFaceSection_naturality, Category.assoc, c.fac_left,
      ← Category.assoc, zeroFaceSection_fst, Category.id_comp]
  · rw [Category.assoc, c.fac_right, ← Category.assoc, zeroFaceSection_fst, Category.id_comp]

end

end Thomason.Construction

end

section

/-! # The local fibre theorem over every standard simplex -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

def finalSimplexVertex (n : ℕ) : (Δ[n] : SSet.{0}) _⦋0⦌ :=
  SSet.stdSimplex.objEquiv.symm (RealizationPrism.vertexOperator (Fin.last n))

/-- The explicit monotone contraction from a simplex to its final vertex. -/
def simplexFinalContraction (n : ℕ) :
    SSet.Homotopy (𝟙 (Δ[n] : SSet.{0})) (SSet.const (finalSimplexVertex n)) where
  h := {
    app m := ↾fun x => SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
      (orderInterpolate OrderHom.id (OrderHom.const _ (Fin.last n))
        (fun j => Fin.le_last j) (SSet.stdSimplex.objEquiv x.1).toOrderHom
        (SSet.stdSimplex.objEquiv x.2).toOrderHom))
    naturality m k a := by
      apply ConcreteCategory.hom_ext
      intro x
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Every constant family at the final vertex is fixed throughout the
contraction, with an arbitrary simplicial parameter. -/
theorem simplexFinalContraction_stationary (n : ℕ) (K : SSet.{0}) :
    (SSet.const (X := K) (finalSimplexVertex n)) ▷ Δ[1] ≫
        (simplexFinalContraction n).h =
      fst K Δ[1] ≫ SSet.const (finalSimplexVertex n) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  change (if (SSet.stdSimplex.objEquiv z.2).toOrderHom j = 0 then Fin.last n
    else Fin.last n) = Fin.last n
  split <;> rfl

/-- A Kan fibration over a simplex has an actual stationary simplicial
retraction onto its final-vertex fibre. This is the local fibre comparison
needed before passing through a base's simplices. -/
theorem kan_simplex_fiber_deformation {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    ∃ r : E ⟶ (simplicialPointFiber p (finalSimplexVertex n)).toSSet,
      (simplicialPointFiber p (finalSimplexVertex n)).ι ≫ r = 𝟙 _ ∧
      ∃ T : SSet.Homotopy (𝟙 E) (r ≫ (simplicialPointFiber p (finalSimplexVertex n)).ι),
        (simplicialPointFiber p (finalSimplexVertex n)).ι ▷ Δ[1] ≫ T.h =
          fst (simplicialPointFiber p (finalSimplexVertex n)).toSSet Δ[1] ≫
            (simplicialPointFiber p (finalSimplexVertex n)).ι ∧
        T.h ≫ p = p ▷ Δ[1] ≫ (simplexFinalContraction n).h := by
  apply kan_fiber_deformation p _ (simplexFinalContraction n)
  rw [simplicialPointFiber_ι_comp]
  exact simplexFinalContraction_stationary n _

/-- Inclusion of the literal final-vertex fibre is an actual realization
weak equivalence. The base simplex itself need not be a Kan complex. -/
theorem kan_simplex_fiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    realizationWeakEquivalences (simplicialPointFiber p (finalSimplexVertex n)).ι := by
  obtain ⟨r, hr, T, _, _⟩ := kan_simplex_fiber_deformation n p
  exact simplicial_retraction_weak _ r hr T

end

end Thomason.Construction

end

section

/-! # A stationary contraction of a horn through its distinguished vertex -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

/-- Changing simplex vertices only to the distinguished horn vertex stays
inside the horn, since an omitted different vertex is still omitted. -/
theorem horn_supported {n : ℕ} (i : Fin (n+2)) {m : SimplexCategoryᵒᵖ}
    (s : (Λ[n+1, i] : SSet.{0}).obj m)
    (f : Fin (m.unop.len+1) →o Fin (n+2))
    (hf : ∀ k, f k = (SSet.stdSimplex.objEquiv s.val).toOrderHom k ∨ f k = i) :
    SSet.stdSimplex.objMk f ∈ (Λ[n+1, i] : (Δ[n+1] : SSet.{0}).Subcomplex).obj m := by
  change Set.range f ∪ {i} ≠ Set.univ
  intro he
  apply s.property
  apply Set.eq_univ_iff_forall.mpr
  intro j
  have hj : j ∈ Set.range f ∪ {i} := by rw [he]; trivial
  rcases hj with ⟨k, rfl⟩ | hj
  · rcases hf k with hk | hk
    · exact Or.inl ⟨k, hk.symm⟩
    · exact Or.inr hk
  · exact Or.inr hj

/-- The distinguished vertex belongs to its horn in every positive dimension. -/
def hornVertex (n : ℕ) (i : Fin (n+2)) : (Λ[n+1, i] : SSet.{0}) _⦋0⦌ :=
  ⟨SSet.stdSimplex.objEquiv.symm (RealizationPrism.vertexOperator i), by
    apply (SSet.mem_horn_iff_notMem_range _ i).mpr
    obtain ⟨j, hj⟩ := exists_ne i
    refine ⟨j, hj, ?_⟩
    rintro ⟨k, hk⟩
    exact hj hk.symm⟩

def hornClamp (n : ℕ) (i : Fin (n+2)) :
    (Λ[n+1, i] : SSet.{0}) ⟶ Λ[n+1, i] where
  app m := ↾fun s => ⟨SSet.stdSimplex.objMk
      ((SSet.stdSimplex.objEquiv s.val).toOrderHom ⊓ OrderHom.const _ i),
    horn_supported i s _ (fun k => by
      change min _ i = _ ∨ min _ i = i
      exact min_choice _ _)⟩
  naturality m k a := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl

/-- The clamp is below the identity, with no change of an omitted vertex. -/
def hornClampToId (n : ℕ) (i : Fin (n+2)) :
    SSet.Homotopy (hornClamp n i) (𝟙 (Λ[n+1, i] : SSet.{0})) where
  h := {
    app m := ↾fun x => ⟨SSet.stdSimplex.objMk
      (orderInterpolate (OrderHom.id ⊓ OrderHom.const _ i) OrderHom.id
        (fun _ => min_le_left _ _)
        (SSet.stdSimplex.objEquiv x.1.val).toOrderHom
        (SSet.stdSimplex.objEquiv x.2).toOrderHom),
      horn_supported i x.1 _ (fun k => by
        change (if _ then min _ i else _) = _ ∨ (if _ then min _ i else _) = i
        split
        · exact min_choice _ _
        · exact Or.inl rfl)⟩
    naturality m k a := by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- The same clamp is below the constant distinguished vertex. -/
def hornClampToVertex (n : ℕ) (i : Fin (n+2)) :
    SSet.Homotopy (hornClamp n i) (SSet.const (hornVertex n i)) where
  h := {
    app m := ↾fun x => ⟨SSet.stdSimplex.objMk
      (orderInterpolate (OrderHom.id ⊓ OrderHom.const _ i) (OrderHom.const _ i)
        (fun _ => min_le_right _ _)
        (SSet.stdSimplex.objEquiv x.1.val).toOrderHom
        (SSet.stdSimplex.objEquiv x.2).toOrderHom),
      horn_supported i x.1 _ (fun k => by
        change (if _ then min _ i else i) = _ ∨ (if _ then min _ i else i) = i
        split
        · exact min_choice _ _
        · exact Or.inr rfl)⟩
    naturality m k a := by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    rfl
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

theorem hornClampToId_stationary (n : ℕ) (i : Fin (n+2)) (K : SSet.{0}) :
    (SSet.const (X := K) (hornVertex n i)) ▷ Δ[1] ≫ (hornClampToId n i).h =
      fst K Δ[1] ≫ SSet.const (hornVertex n i) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  change (if _ then min i i else i) = i
  simp

theorem hornClampToVertex_stationary (n : ℕ) (i : Fin (n+2)) (K : SSet.{0}) :
    (SSet.const (X := K) (hornVertex n i)) ▷ Δ[1] ≫ (hornClampToVertex n i).h =
      fst K Δ[1] ≫ SSet.const (hornVertex n i) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  change (if _ then min i i else i) = i
  simp

end

end Thomason.Construction

end

section

/-! # The initial vertex is an anodyne subcomplex of the standard simplex -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

def initialVertexInclusion (n : ℕ) : (Δ[0] : SSet.{0}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (RealizationPrism.vertexOperator (0 : Fin (n+1)))

theorem initialVertexInclusion_mono (n : ℕ) : Mono (initialVertexInclusion n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro a b _
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro k
  exact @Subsingleton.elim (Fin 1) inferInstance _ _

/-- The explicit simplex contraction fixes the initial vertex in every
simplicial degree and at every cylinder time. -/
theorem simplexInitialContraction_stationary (n : ℕ) :
    initialVertexInclusion n ▷ Δ[1] ≫ (simplexInitialContraction n).h =
      fst (Δ[0] : SSet.{0}) Δ[1] ≫ initialVertexInclusion n := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro k
  change (if (SSet.stdSimplex.objEquiv x.2).toOrderHom k = 0 then 0 else 0) = 0
  split <;> rfl

/-- The actual vertex inclusion is anodyne without using the Kan–Quillen
weak-equivalence characterization of anodyne maps. -/
theorem initialVertexInclusion_anodyne (n : ℕ) :
    SSet.anodyneExtensions (initialVertexInclusion n) := by
  let i := initialVertexInclusion n
  have : Mono i := initialVertexInclusion_mono n
  let r : (Δ[n] : SSet.{0}) ⟶ Δ[0] := SSet.stdSimplex.isTerminalObj₀.from _
  have hir : i ≫ r = 𝟙 _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have he : r ≫ i = SSet.const (initialSimplexVertex n) := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro k
    rfl
  let H : SSet.Homotopy (r ≫ i) (𝟙 (Δ[n] : SSet.{0})) := by
    rw [he]
    exact simplexInitialContraction n
  apply anodyne_of_simplicial_deformation i r hir H
  exact simplexInitialContraction_stationary n

/-- A simplex lift can preserve the originally specified initial vertex
exactly, in addition to commuting with the fibration. -/
theorem kan_fibration_simplex_lift_vertex {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] (n : ℕ) (b : Δ[n] ⟶ Y) (x : X _⦋0⦌)
    (hx : p.app _ x = b.app _ (initialSimplexVertex n)) :
    ∃ a : Δ[n] ⟶ X, initialVertexInclusion n ≫ a = SSet.const x ∧ a ≫ p = b := by
  have : HasLiftingProperty (initialVertexInclusion n) p :=
    initialVertexInclusion_anodyne n p (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  have hc : SSet.const x ≫ p = initialVertexInclusion n ≫ b := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const, SSet.yonedaEquiv_comp,
      initialVertexInclusion, SSet.yonedaEquiv_map]
    exact hx
  let sq : CommSq (SSet.const x) (initialVertexInclusion n) p b := ⟨hc⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end

end Thomason.Construction

end

section

/-! # Exact boundary fillers from simplicial nullhomotopies in every dimension -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- A boundary homotopy over a fixed base map corrects any preliminary
simplicial lift to an exact lift. This works for every monomorphism. -/
theorem kan_lift_of_boundary_homotopy {A K E B : SSet.{0}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (d : K ⟶ E) (b : K ⟶ B) (hd : d ≫ p = b) (a : A ⟶ E)
    (H : SSet.Homotopy (i ≫ d) a)
    (hH : H.h ≫ p = fst A Δ[1] ≫ i ≫ b) :
    ∃ l : K ⟶ E, i ≫ l = a ∧ l ≫ p = b := by
  have hzero : d ≫ p = SSet.ι₀ ≫ (fst K Δ[1] ≫ b) := by
    simpa only [← Category.assoc, SSet.ι₀_fst, Category.id_comp] using hd
  have hp : H.h ≫ p = i ▷ Δ[1] ≫ (fst K Δ[1] ≫ b) := by
    rw [hH]
    rfl
  obtain ⟨e, _, hei, hep⟩ := exists_kan_cylinder_lift i p d H.h
    (fst K Δ[1] ≫ b) H.h₀ hp hzero
  refine ⟨SSet.ι₁ ≫ e, ?_, ?_⟩
  · have hn : i ≫ SSet.ι₁ = SSet.ι₁ ≫ i ▷ (Δ[1] : SSet.{0}) := by
      apply NatTrans.ext
      funext k
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, hei, H.h₁]
  · rw [Category.assoc, hep]
    simp only [← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- A simplicial nullhomotopy extends across any monomorphic inclusion
into a Kan complex. The extension keeps the given map exactly. -/
theorem kan_extension_of_nullhomotopy {A K X : SSet.{0}} [SSet.KanComplex X]
    (i : A ⟶ K) [Mono i] (a : A ⟶ X) (x : X _⦋0⦌)
    (H : SSet.Homotopy (SSet.const x) a) :
    ∃ l : K ⟶ X, i ≫ l = a := by
  let d : K ⟶ X := SSet.const x
  have H' : SSet.Homotopy (i ≫ d) a := by
    simpa only [d, SSet.comp_const] using H
  obtain ⟨l, hl, _⟩ := kan_lift_of_boundary_homotopy i (terminal.from X)
    d (terminal.from K) (terminal.hom_ext _ _) a H' (terminal.hom_ext _ _)
  exact ⟨l, hl⟩

/-- Any extension over a standard simplex supplies an explicit simplicial
nullhomotopy, by the actual initial-vertex contraction. -/
def boundaryNullhomotopyOfExtension {X : SSet.{0}} (n : ℕ)
    (a : (SSet.boundary n : SSet.{0}) ⟶ X) (d : (Δ[n] : SSet.{0}) ⟶ X)
    (hd : (SSet.boundary n).ι ≫ d = a) :
    SSet.Homotopy (SSet.const (d.app _ (initialSimplexVertex n))) a where
  h := (SSet.boundary n).ι ▷ Δ[1] ≫ (simplexInitialContraction n).h ≫ d
  h₀ := by
    have hn : SSet.ι₀ ≫ (SSet.boundary n).ι ▷ (Δ[1] : SSet.{0}) =
        (SSet.boundary n).ι ≫ SSet.ι₀ := by
      apply NatTrans.ext
      funext k
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, ← Category.assoc SSet.ι₀,
      (simplexInitialContraction n).h₀, SSet.const_comp, SSet.comp_const]
    rfl
  h₁ := by
    have hn : SSet.ι₁ ≫ (SSet.boundary n).ι ▷ (Δ[1] : SSet.{0}) =
        (SSet.boundary n).ι ≫ SSet.ι₁ := by
      apply NatTrans.ext
      funext k
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, ← Category.assoc SSet.ι₁,
      (simplexInitialContraction n).h₁, Category.id_comp, hd]
    rfl
  rel := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- In every dimension, the exact boundary extension problem in a Kan
complex is equivalent to an actual simplicial nullhomotopy. This is a
reduction, not an assumption about continuous nullhomotopies. -/
theorem kan_boundary_extension_iff_nullhomotopy {X : SSet.{0}} [SSet.KanComplex X]
    (n : ℕ) (a : (SSet.boundary n : SSet.{0}) ⟶ X) :
    (∃ l : (Δ[n] : SSet.{0}) ⟶ X, (SSet.boundary n).ι ≫ l = a) ↔
      ∃ x : X _⦋0⦌, Nonempty (SSet.Homotopy (SSet.const x) a) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d.app _ (initialSimplexVertex n), ⟨boundaryNullhomotopyOfExtension n a d hd⟩⟩
  · rintro ⟨x, ⟨H⟩⟩
    exact kan_extension_of_nullhomotopy (SSet.boundary n).ι a x H

end

end Thomason.Construction

end

section

/-! # Exact point fibres and local simplex base change -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- Horn lifting is stable under actual simplicial pullback. -/
theorem kan_pullback_snd_fibration {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B)
    [HomotopicalAlgebra.Fibration p] :
    HomotopicalAlgebra.Fibration (pullback.snd p g) := by
  rw [fibration_iff]
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback p g)
    ((fibration_iff p).mp inferInstance)

/-- The original point fibre maps canonically into every pullback containing
that point. -/
def pointFiberToPullback {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B)
    (c : C.obj (.op (.mk 0))) :
    (simplicialPointFiber p (g.app _ c)).toSSet ⟶ pullback p g :=
  pullback.lift (simplicialPointFiber p (g.app _ c)).ι (SSet.const c)
    (by rw [simplicialPointFiber_ι_comp, SSet.const_comp])

@[reassoc]
theorem pointFiberToPullback_fst {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B)
    (c : C.obj (.op (.mk 0))) :
    pointFiberToPullback p g c ≫ pullback.fst p g =
      (simplicialPointFiber p (g.app _ c)).ι := pullback.lift_fst _ _ _

@[reassoc]
theorem pointFiberToPullback_snd {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B)
    (c : C.obj (.op (.mk 0))) :
    pointFiberToPullback p g c ≫ pullback.snd p g = SSet.const c :=
  pullback.lift_snd _ _ _

/-- Fibres of the actual simplicial pullback identify exactly with the
original point fibres. -/
def simplicialPointFiberBaseChangeIso {E B C : SSet.{0}} (p : E ⟶ B) (g : C ⟶ B)
    (c : C.obj (.op (.mk 0))) :
    (simplicialPointFiber p (g.app _ c)).toSSet ≅
      (simplicialPointFiber (pullback.snd p g) c).toSSet where
  hom := simplicialPointFiberLift (pullback.snd p g) c (pointFiberToPullback p g c)
    (pointFiberToPullback_snd p g c)
  inv := simplicialPointFiberLift p (g.app _ c)
    ((simplicialPointFiber (pullback.snd p g) c).ι ≫ pullback.fst p g) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        simplicialPointFiber_ι_comp, SSet.const_comp])
  hom_inv_id := by
    apply (cancel_mono (simplicialPointFiber p (g.app _ c)).ι).mp
    rw [Category.assoc, simplicialPointFiberLift_ι, ← Category.assoc,
      simplicialPointFiberLift_ι, pointFiberToPullback_fst, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (simplicialPointFiber (pullback.snd p g) c).ι).mp
    rw [Category.assoc, simplicialPointFiberLift_ι, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pointFiberToPullback_fst, simplicialPointFiberLift_ι]
    · rw [Category.assoc, pointFiberToPullback_snd, SSet.comp_const,
        simplicialPointFiber_ι_comp]

@[reassoc]
theorem simplicialPointFiberBaseChangeIso_hom_ι {E B C : SSet.{0}}
    (p : E ⟶ B) (g : C ⟶ B) (c : C.obj (.op (.mk 0))) :
    (simplicialPointFiberBaseChangeIso p g c).hom ≫
      (simplicialPointFiber (pullback.snd p g) c).ι = pointFiberToPullback p g c := rfl

/-- In a Kan fibration, the canonical map from the fibre over the final
vertex of any base simplex into that simplex pullback is an actual W.
This local result does not assume right properness or acyclic Kan lifting. -/
theorem kan_simplex_baseChange_fiber_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (n : ℕ) (g : SSet.stdSimplex.obj (.mk n) ⟶ B) :
    realizationWeakEquivalences (pointFiberToPullback p g (finalSimplexVertex n)) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p g) := kan_pullback_snd_fibration p g
  rw [← simplicialPointFiberBaseChangeIso_hom_ι]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) (kan_simplex_fiber_weak n (pullback.snd p g))

end

end Thomason.Construction

end

section

/-! # Fibre comparisons across simplex restrictions of a Kan fibration -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

theorem simplexInitialContraction_const (n : ℕ) (K : SSet.{0}) :
    (SSet.const (X := K) (initialSimplexVertex n)) ▷ Δ[1] ≫
        (simplexInitialContraction n).h =
      fst K Δ[1] ≫ SSet.const (initialSimplexVertex n) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro z
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  change (if (SSet.stdSimplex.objEquiv z.2).toOrderHom j = 0 then 0 else 0) = (0 : Fin (n+1))
  split <;> rfl

/-- The initial fibre inclusion is even anodyne, by the reverse lifted
stationary simplex contraction. -/
theorem kan_simplex_initialFiber_anodyne {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    SSet.anodyneExtensions (simplicialPointFiber p (initialSimplexVertex n)).ι := by
  have hs : ((simplicialPointFiber p (initialSimplexVertex n)).ι ≫ p) ▷ Δ[1] ≫
      (simplexInitialContraction n).h =
      fst (simplicialPointFiber p (initialSimplexVertex n)).toSSet Δ[1] ≫
        (simplicialPointFiber p (initialSimplexVertex n)).ι ≫ p := by
    rw [simplicialPointFiber_ι_comp]
    exact simplexInitialContraction_const n _
  obtain ⟨r, hr, T, hT, _⟩ := kan_fiber_deformation_reverse p _ (simplexInitialContraction n) hs
  exact anodyne_of_simplicial_deformation _ r hr T hT

theorem kan_simplex_initialFiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    realizationWeakEquivalences (simplicialPointFiber p (initialSimplexVertex n)).ι :=
  anodyne_realization_weak _ (kan_simplex_initialFiber_anodyne n p)

theorem kan_simplex_baseChange_initialFiber_weak {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (n : ℕ) (g : (Δ[n] : SSet.{0}) ⟶ B) :
    realizationWeakEquivalences (pointFiberToPullback p g (initialSimplexVertex n)) := by
  have : HomotopicalAlgebra.Fibration (pullback.snd p g) := kan_pullback_snd_fibration p g
  rw [← simplicialPointFiberBaseChangeIso_hom_ι]
  exact realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso _) (kan_simplex_initialFiber_weak n (pullback.snd p g))

/-- A restriction preserving the final vertex induces a weak equivalence
on the total pullback of any Kan fibration over a simplex. -/
theorem kan_simplex_baseChange_weak_of_final {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (g : (Δ[m] : SSet.{0}) ⟶ Δ[n])
    (hg : g.app _ (finalSimplexVertex m) = finalSimplexVertex n) :
    realizationWeakEquivalences (pullback.fst p g) := by
  have hi := kan_simplex_baseChange_fiber_weak p m g
  apply realizationWeakEquivalences.of_precomp (pointFiberToPullback p g (finalSimplexVertex m)) _ hi
  rw [pointFiberToPullback_fst, hg]
  exact kan_simplex_fiber_weak n p

/-- The ordinal edge from any vertex to the final one. -/
def finalVertexEdgeOperator {n : ℕ} (j : Fin (n+1)) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk {
    toFun k := if k = 0 then j else Fin.last n
    monotone' := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
      exact Fin.le_last j }

theorem finalVertexEdgeOperator_final {n : ℕ} (j : Fin (n+1)) :
    (SSet.stdSimplex.map (finalVertexEdgeOperator j)).app _ (finalSimplexVertex 1) =
      finalSimplexVertex n := by
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro k
  fin_cases k
  rfl

theorem finalVertexEdgeOperator_initial {n : ℕ} (j : Fin (n+1)) :
    (SSet.stdSimplex.map (finalVertexEdgeOperator j)).app _ (initialSimplexVertex 1) =
      SSet.stdSimplex.objEquiv.symm (RealizationPrism.vertexOperator j) := by
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro k
  fin_cases k
  rfl

/-- Every vertex fibre, not only an endpoint fibre, includes weakly in the
total space of a Kan fibration over a standard simplex. -/
theorem kan_simplex_vertexFiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (j : Fin (n+1)) :
    realizationWeakEquivalences
      (simplicialPointFiber p (SSet.stdSimplex.objEquiv.symm (RealizationPrism.vertexOperator j))).ι := by
  let g := SSet.stdSimplex.map (finalVertexEdgeOperator j)
  have hg : g.app _ (finalSimplexVertex 1) = finalSimplexVertex n :=
    finalVertexEdgeOperator_final j
  have hpull := kan_simplex_baseChange_weak_of_final n 1 p g hg
  have hfib := kan_simplex_baseChange_initialFiber_weak p 1 g
  have hw := realizationWeakEquivalences.comp_mem _ _ hfib hpull
  rw [pointFiberToPullback_fst, finalVertexEdgeOperator_initial] at hw
  exact hw

/-- A vertex of a standard simplex is exactly one of its ordinal vertices. -/
theorem standard_vertex_eq (n : ℕ) (v : (Δ[n] : SSet.{0}) _⦋0⦌) :
    v = SSet.stdSimplex.objEquiv.symm
      (RealizationPrism.vertexOperator ((SSet.stdSimplex.objEquiv v).toOrderHom 0)) := by
  apply SSet.stdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro k
  fin_cases k
  rfl

theorem kan_simplex_anyFiber_weak {E : SSet.{0}} (n : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (v : (Δ[n] : SSet.{0}) _⦋0⦌) :
    realizationWeakEquivalences (simplicialPointFiber p v).ι := by
  rw [standard_vertex_eq n v]
  exact kan_simplex_vertexFiber_weak n p _

/-- Every map of standard simplices induces an actual weak equivalence on
pullback total spaces of a Kan fibration over the target simplex. This is
proved from the endpoint deformations, without global acyclic Kan lifting. -/
theorem kan_simplex_baseChange_weak {E : SSet.{0}} (n m : ℕ)
    (p : E ⟶ (Δ[n] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (g : (Δ[m] : SSet.{0}) ⟶ Δ[n]) :
    realizationWeakEquivalences (pullback.fst p g) := by
  have hi := kan_simplex_baseChange_fiber_weak p m g
  apply realizationWeakEquivalences.of_precomp (pointFiberToPullback p g (finalSimplexVertex m)) _ hi
  rw [pointFiberToPullback_fst]
  exact kan_simplex_anyFiber_weak n p _

end

end Thomason.Construction

end

section

/-! # Transporting actual fibre weak equivalences along base paths -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- In a Kan fibration, whether a vertex fibre includes by an actual weak
 equivalence is unchanged along a simplicial edge. This uses the proved
 simplex fibre theorem, rather than a global homotopy-fibre assumption. -/
theorem kan_fiber_weak_iff_of_edge {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {x y : B _⦋0⦌} (e : SSet.Edge x y) :
    realizationWeakEquivalences (simplicialPointFiber p x).ι ↔
      realizationWeakEquivalences (simplicialPointFiber p y).ι := by
  let g : (Δ[1] : SSet.{0}) ⟶ B := SSet.yonedaEquiv.symm e.edge
  have hq : HomotopicalAlgebra.Fibration (pullback.snd p g) :=
    kan_pullback_snd_fibration p g
  have hf (v : (Δ[1] : SSet.{0}) _⦋0⦌) :
      realizationWeakEquivalences (pointFiberToPullback p g v) := by
    rw [← simplicialPointFiberBaseChangeIso_hom_ι]
    exact realizationWeakEquivalences.comp_mem _ _
      (realizationWeakEquivalences.of_isIso _) (kan_simplex_anyFiber_weak 1 _ v)
  have hi : g.app _ (initialSimplexVertex 1) = x := by
    dsimp only [g, initialSimplexVertex]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    have hv : RealizationPrism.vertexOperator (0 : Fin 2) = SimplexCategory.δ (1 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl
    rw [hv]
    exact e.src_eq
  have ht : g.app _ (finalSimplexVertex 1) = y := by
    dsimp only [g, finalSimplexVertex]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    have hv : RealizationPrism.vertexOperator (Fin.last 1) = SimplexCategory.δ (0 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl
    rw [hv]
    exact e.tgt_eq
  have heq (v : (Δ[1] : SSet.{0}) _⦋0⦌) :
      realizationWeakEquivalences (simplicialPointFiber p (g.app _ v)).ι ↔
        realizationWeakEquivalences (pullback.fst p g) := by
    rw [← pointFiberToPullback_fst p g v]
    exact realizationWeakEquivalences.precomp_iff _ _ (hf v)
  rw [← hi, heq, ← heq (finalSimplexVertex 1), ht]

/-- The same exact test is constant on an entire simplicial edge component. -/
theorem kan_fiber_weak_iff_of_zigzag {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {x y : B _⦋0⦌}
    (h : Relation.EqvGen SSet.π₀Rel x y) :
    realizationWeakEquivalences (simplicialPointFiber p x).ι ↔
      realizationWeakEquivalences (simplicialPointFiber p y).ι := by
  induction h with
  | rel a b h => exact kan_fiber_weak_iff_of_edge p (Classical.choice h)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Actual continuous paths between realized vertices transport the fibre
weak-equivalence test. No simplicial approximation of the path is assumed:
the already proved component comparison supplies the finite edge zigzag. -/
theorem kan_fiber_weak_iff_of_realization_path {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {x y : B _⦋0⦌}
    (h : Path (RealizationPrism.vertexPoint B x) (RealizationPrism.vertexPoint B y)) :
    realizationWeakEquivalences (simplicialPointFiber p x).ι ↔
      realizationWeakEquivalences (simplicialPointFiber p y).ι :=
  kan_fiber_weak_iff_of_zigzag p (RealizationPrism.edge_zigzag_of_realization_path h)

end

end Thomason.Construction

end

end OAI
