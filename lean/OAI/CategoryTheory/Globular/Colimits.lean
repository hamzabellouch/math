import OAI.CategoryTheory.Globular.Reflection

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

theorem source_bijective_of_coskeletal (X : GlobularSet.{u}) (q n : ℕ)
    (hX : ∀ j, q < j → Function.Bijective (X.boundary j)) (hn : q < n) :
    Function.Bijective (X.source n) := by
  have ht (z : X.Cell (n+1)) : X.source n z = X.target n z :=
    (hX n hn).1 ((X.parallel_iff_boundary_eq n _ _).1 (Joined.parallel ⟨z, rfl, rfl⟩))
  constructor
  · intro x y h
    apply (hX (n+1) (by omega)).1
    exact Subtype.ext (Prod.ext h ((ht x).symm.trans (h.trans (ht y))))
  · intro x
    have hp : X.Parallel n x x := by cases n <;> simp [Parallel]
    obtain ⟨z, hz⟩ := (hX (n+1) (by omega)).2 ⟨(x, x), hp⟩
    exact ⟨z, congrArg (fun b => b.1.1) hz⟩

end GlobularSet

namespace GlobularTheory.Model

@[simp] theorem cellEquiv_comp {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (a : disk C n ⟶ X) (f : X ⟶ Y) :
    cellEquiv Y n (a ≫ f) = (underlyingMap f).app n (cellEquiv X n a) := rfl

@[simp] theorem cellEquiv_J {C : GlobularTheory.{v}} {X : C.Model}
    (n : ℕ) (a : disk C (n+1) ⟶ X) :
    cellEquiv X n (J C n ≫ a) = X.underlying.source n (cellEquiv X (n+1) a) := by
  exact (yonedaEquiv_naturality a
    (show (⟨Shape.globe n⟩ : C.Obj) ⟶ ⟨Shape.globe (n+1)⟩ from
      C.base (Shape.source n))).symm

theorem J_coskeletalLocalMap (C : GlobularTheory.{v}) (k n : ℕ) (hkn : k < n) :
    CoskeletalLocalMap k (J C n) := by
  intro Z hZ g
  obtain ⟨z, hz, unique⟩ := (Z.underlying.source_bijective_of_coskeletal k n hZ hkn).existsUnique
    (cellEquiv Z n g)
  refine ⟨(cellEquiv Z (n+1)).symm z, ?_, ?_⟩
  · apply (cellEquiv Z n).injective
    simpa only [cellEquiv_J, Equiv.apply_symm_apply] using hz
  · intro a ha
    apply (cellEquiv Z (n+1)).injective
    rw [Equiv.apply_symm_apply]
    apply unique
    exact (cellEquiv_J n a).symm.trans (congrArg (cellEquiv Z n) ha)

theorem CoskeletalLocalMap.pushout {C : GlobularTheory.{v}} (q : ℕ)
    {A B X Y : C.Model} (f : A ⟶ B) (a : A ⟶ X) (i : X ⟶ Y) (b : B ⟶ Y)
    (sq : IsPushout a f i b) (hf : CoskeletalLocalMap q f) :
    CoskeletalLocalMap q i := by
  intro Z hZ x
  obtain ⟨z, hz, unique⟩ := hf Z hZ (a ≫ x)
  refine ⟨sq.desc x z hz.symm, sq.inl_desc _ _ _, ?_⟩
  intro y hy
  apply sq.hom_ext
  · exact hy.trans (sq.inl_desc _ _ _).symm
  · have hz' : b ≫ y = z := unique (b ≫ y)
      ((Category.assoc f b y).symm.trans
        ((congrArg (· ≫ y) sq.w.symm).trans ((Category.assoc a i y).trans (congrArg (a ≫ ·) hy))))
    exact hz'.trans (sq.inr_desc _ _ _).symm

theorem elementary_pushout_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y)
    (b : disk C (n+1) ⟶ Y) (sq : IsPushout a (J C n) i b)
    (k : ℕ) (hkn : k < n) :
    Function.Bijective ((underlyingMap i).app k) :=
  (coskeletalLocalMap_iff hC k i).1
    ((J_coskeletalLocalMap C k n hkn).pushout k (J C n) a i b sq) k le_rfl

theorem low_bijections_eq_local (C : GlobularTheory.{v}) (hC : C.IsCoherator) (q : ℕ) :
    (fun {X Y : C.Model} (f : X ⟶ Y) =>
      ∀ k, k ≤ q → Function.Bijective ((underlyingMap f).app k) : MorphismProperty C.Model) =
    ObjectProperty.isLocal (fun X : C.Model => X.IsCoskeletal q) := by
  ext X Y f
  rw [← coskeletalLocalMap_iff hC q f]
  exact forall_congr' (fun Z => imp_congr_right (fun _ =>
    (Function.bijective_iff_existsUnique (fun g : Y ⟶ Z => f ≫ g)).symm))

theorem low_bijective_transfinite {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {X Y : C.Model} (f : X ⟶ Y)
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    (H : TransfiniteCompositionOfShape J f)
    (hH : ∀ j, ¬ IsMax j → ∀ k, k ≤ q → Function.Bijective
      ((underlyingMap (H.F.map (homOfLE (Order.le_succ j)))).app k)) :
    ∀ k, k ≤ q → Function.Bijective ((underlyingMap f).app k) := by
  let P : ObjectProperty C.Model := fun X => X.IsCoskeletal q
  have hf : P.isLocal f := P.isLocal.transfiniteCompositionsOfShape_le J f
    ⟨{ toTransfiniteCompositionOfShape := H
       map_mem j hj := by
         change ObjectProperty.isLocal (fun X : C.Model => X.IsCoskeletal q) _
         rw [← low_bijections_eq_local C hC q]
         exact hH j hj }⟩
  change ObjectProperty.isLocal (fun X : C.Model => X.IsCoskeletal q) f at hf
  rwa [← low_bijections_eq_local C hC q] at hf

end GlobularTheory.Model

namespace GlobularSet

theorem exactBoundaryTest_split_into_coskeletal {X Y : GlobularSet.{u}}
    (i : Hom X Y) (r : Hom Y X) (hr : i.comp r = Hom.id X) (q : ℕ)
    (hlo : ∀ k, k < q → Function.Surjective (i.app k))
    (hhi : ∀ j, q < j → Function.Surjective (Y.boundary j))
    (hrefl : ∀ j x, Y.Joined j x x) : ExactBoundaryTest i := by
  intro d b y hy
  have hb : X.boundary d (r.app d y) = b := by
    rw [← r.boundary_app, hy, ← Hom.boundaryMap_comp]
    have hh := congrArg (fun f : Hom X X => f.boundaryMap d b) hr
    cases d with
    | zero => exact PUnit.ext _ _
    | succ d => exact hh
  refine ⟨r.app d y, hb, ?_⟩
  by_cases hd : d < q
  · obtain ⟨x, rfl⟩ := hlo d hd y
    have hx : r.app d (i.app d x) = x := congrArg (fun f : Hom X X => f.app d x) hr
    rw [hx]
    exact hrefl d _
  · have hp : Y.Parallel d (i.app d (r.app d y)) y := by
      apply (Y.parallel_iff_boundary_eq d _ _).2
      rw [← i.boundary_app, hb, hy]
    obtain ⟨z, hz⟩ := hhi (d+1) (by omega) ⟨(_, _), hp⟩
    exact ⟨z, congrArg (fun z => z.1.1) hz, congrArg (fun z => z.1.2) hz⟩

end GlobularSet

namespace GlobularTheory.Model

theorem elementary_pushout_to_coskeletal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y)
    (b : disk C (n+1) ⟶ Y) (sq : IsPushout a (J C n) i b)
    (hY : Y.IsCoskeletal n) : WeakEquivalence hC i := by
  obtain ⟨r, hr⟩ := elementary_pushout_retraction hC n a i b sq
  apply weakEquivalence_of_exactBoundaryTest hC
  apply GlobularSet.exactBoundaryTest_split_into_coskeletal (underlyingMap i) (underlyingMap r)
    (show (underlyingMap i).comp (underlyingMap r) = GlobularSet.Hom.id X.underlying from
      congrArg (fun f : X ⟶ X => underlyingMap f) hr) n
  · exact fun k hk => (elementary_pushout_low_bijective hC n a i b sq k hk).2
  · exact fun j hj => (hY j hj).2
  · exact Y.joined_refl hC

end GlobularTheory.Model

namespace GlobularTheory

structure SumIndex where
  S : Shape
  b : ℕ
  h : ℕ
  left : b < S.1
  right : b < h

noncomputable def sumDiagram (C : GlobularTheory.{v}) (t : SumIndex) :
    WalkingCospan ⥤ C.Objᵒᵖ :=
  cospan (C.toTheoryData.arity.map (t.S.seam t.left)).op
    (C.toTheoryData.arity.map (Shape.face t.right false)).op

noncomputable def sumCone (C : GlobularTheory.{v}) (t : SumIndex) : Cone (C.sumDiagram t) :=
  PullbackCone.mk (C.toTheoryData.arity.map (t.S.inl t.b t.h t.left t.right)).op
    (C.toTheoryData.arity.map (t.S.inr t.b t.h t.left t.right)).op
    (by simpa only [← op_comp] using congrArg Quiver.Hom.op (C.sums t.S t.b t.h t.left t.right).w)

noncomputable def sumConeIsLimit (C : GlobularTheory.{v}) (t : SumIndex) :
    IsLimit (C.sumCone t) :=
  (C.sums t.S t.b t.h t.left t.right).op.flip.isLimit

noncomputable def sumComparison (C : GlobularTheory.{v}) (t : SumIndex) :=
  Presheaf.coconePtToShrinkYoneda (C.sumCone t)
    (colimit.isColimit ((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v}))

noncomputable def sumComparisons (C : GlobularTheory.{v}) :
    MorphismProperty (C.Objᵒᵖ ⥤ Type v) :=
  MorphismProperty.ofHoms C.sumComparison

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance shrinkYoneda_cardinalPresentable (C : GlobularTheory.{v})
    (S : C.Obj) : IsCardinalPresentable (shrinkYoneda.{v}.obj S) Cardinal.aleph0.{v} where
  preservesColimitOfShape J _ _ := by
    let e : coyoneda.obj (op (shrinkYoneda.{v}.obj S)) ≅
        (evaluation C.Objᵒᵖ (Type v)).obj (op S) :=
      NatIso.ofComponents (fun P => Equiv.toIso shrinkYonedaEquiv)
    exact preservesColimitsOfShape_of_natIso e.symm

instance sumComparison_source_presentable (C : GlobularTheory.{v}) (t : SumIndex) :
    IsCardinalPresentable (colimit ((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v}))
      Cardinal.aleph0.{v} := by
  let (k : WalkingCospanᵒᵖ) : IsCardinalPresentable
      (((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v}).obj k) Cardinal.aleph0.{v} :=
    C.shrinkYoneda_cardinalPresentable (((C.sumDiagram t).obj k.unop).unop)
  apply isCardinalPresentable_of_isColimit _ (colimit.isColimit _) Cardinal.aleph0.{v}
  exact hasCardinalLT_of_finite _ _ le_rfl

theorem sumComparisons_rightAdjoint (C : GlobularTheory.{v}) :
    C.sumComparisons.isLocal.ι.IsRightAdjoint := by
  let : MorphismProperty.IsSmall.{v} (MorphismProperty.ofHoms C.sumComparison) :=
    MorphismProperty.isSmall_ofHoms.{v} (ι := SumIndex) C.sumComparison
  change (MorphismProperty.ofHoms C.sumComparison).isLocal.ι.IsRightAdjoint
  apply MorphismProperty.isRightAdjoint_ι_isLocal _ Cardinal.aleph0.{v}
  rintro X Y f ⟨t⟩
  exact ⟨C.sumComparison_source_presentable t,
    C.shrinkYoneda_cardinalPresentable (C.sumCone t).pt.unop⟩


theorem sumComparison_local_iff (C : GlobularTheory.{v})
    (P : C.Objᵒᵖ ⥤ Type v) (t : SumIndex) :
    (MorphismProperty.single (C.sumComparison t)).isLocal P ↔
      IsPullback
        (P.map (C.toTheoryData.arity.map (t.S.inl t.b t.h t.left t.right)).op)
        (P.map (C.toTheoryData.arity.map (t.S.inr t.b t.h t.left t.right)).op)
        (P.map (C.toTheoryData.arity.map (t.S.seam t.left)).op)
        (P.map (C.toTheoryData.arity.map (Shape.face t.right false)).op) := by
  unfold sumComparison
  rw [← Presheaf.nonempty_isLimit_mapCone_iff.{v} (C.sumCone t)
    (colimit.isColimit ((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v})) P]
  constructor
  · rintro ⟨h⟩
    exact IsPullback.of_isLimit_cone h
  · intro h
    exact ⟨(PullbackCone.isLimitMapConeEquiv _ P).symm h.isLimit⟩

namespace Model

theorem sums_local {C : GlobularTheory.{v}} (M : C.Model) :
    C.sumComparisons.isLocal M.presheaf := by
  rintro A B f ⟨t⟩
  exact (MorphismProperty.isLocal_single_iff_bijective _ _).1
    ((C.sumComparison_local_iff M.presheaf t).2 (M.sums t.S t.b t.h t.left t.right))

noncomputable def toLocal (C : GlobularTheory.{v}) :
    C.Model ⥤ C.sumComparisons.isLocal.FullSubcategory where
  obj X := ⟨X.presheaf, X.sums_local⟩
  map f := ObjectProperty.homMk f

theorem local_sums (C : GlobularTheory.{v})
    (P : C.sumComparisons.isLocal.FullSubcategory) (t : SumIndex) :
    IsPullback
      (P.obj.map (C.toTheoryData.arity.map (t.S.inl t.b t.h t.left t.right)).op)
      (P.obj.map (C.toTheoryData.arity.map (t.S.inr t.b t.h t.left t.right)).op)
      (P.obj.map (C.toTheoryData.arity.map (t.S.seam t.left)).op)
      (P.obj.map (C.toTheoryData.arity.map (Shape.face t.right false)).op) := by
  apply (C.sumComparison_local_iff P.obj t).mp
  apply (MorphismProperty.isLocal_single_iff_bijective (C.sumComparison t) P.obj).mpr
  exact P.property (C.sumComparison t) (MorphismProperty.ofHoms.mk t)

noncomputable def fromLocal (C : GlobularTheory.{v}) :
    C.sumComparisons.isLocal.FullSubcategory ⥤ C.Model where
  obj P :=
    { presheaf := P.obj
      sums := fun S b h hl hr => local_sums C P ⟨S,b,h,hl,hr⟩ }
  map f := f.hom

noncomputable def localEquivalence (C : GlobularTheory.{v}) :
    C.Model ≌ C.sumComparisons.isLocal.FullSubcategory where
  functor := toLocal C
  inverse := fromLocal C
  unitIso := NatIso.ofComponents (fun X => Iso.refl X)
  counitIso := NatIso.ofComponents (fun X => Iso.refl X)

noncomputable instance hasColimits (C : GlobularTheory.{v}) : HasColimitsOfSize.{v,v} C.Model := by
  let := C.sumComparisons_rightAdjoint
  let : Reflective C.sumComparisons.isLocal.ι :=
    ⟨_, Adjunction.ofIsRightAdjoint C.sumComparisons.isLocal.ι⟩
  let : HasColimitsOfSize.{v,v} C.sumComparisons.isLocal.FullSubcategory :=
    hasColimits_of_reflective C.sumComparisons.isLocal.ι
  exact Adjunction.has_colimits_of_equivalence (localEquivalence C).functor

end Model
end GlobularTheory

namespace GlobularTheory.Model

abbrev CutoffModels (C : GlobularTheory.{v}) (q : ℕ) :=
  ObjectProperty.FullSubcategory (fun X : C.Model => X.IsCoskeletal q)

noncomputable def chosenCutoff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : C.Model :=
  (exists_cutoff_reflection hC X q).choose

noncomputable def cutoffUnit {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : X ⟶ chosenCutoff hC q X :=
  (exists_cutoff_reflection hC X q).choose_spec.choose

theorem cutoffUnit_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (k : ℕ) (hk : k ≤ q) :
    Function.Bijective ((underlyingMap (cutoffUnit hC q X)).app k) :=
  (exists_cutoff_reflection hC X q).choose_spec.choose_spec.1 k hk

theorem chosenCutoff_coskeletal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : (chosenCutoff hC q X).IsCoskeletal q :=
  (exists_cutoff_reflection hC X q).choose_spec.choose_spec.2.1

theorem cutoffUnit_universal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (Y : CutoffModels C q) (f : X ⟶ Y.obj) :
    ∃! l : chosenCutoff hC q X ⟶ Y.obj, cutoffUnit hC q X ≫ l = f :=
  (exists_cutoff_reflection hC X q).choose_spec.choose_spec.2.2 Y.obj Y.property f

noncomputable def cutoffObject {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : CutoffModels C q :=
  ⟨chosenCutoff hC q X, chosenCutoff_coskeletal hC q X⟩

noncomputable def cutoffEquiv {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (Y : CutoffModels C q) :
    (cutoffObject hC q X ⟶ Y) ≃ (X ⟶ Y.obj) :=
  Equiv.ofBijective (fun f => cutoffUnit hC q X ≫ f.hom) (by
    constructor
    · intro f g h
      apply ObjectProperty.hom_ext
      obtain ⟨_, _, hu⟩ := cutoffUnit_universal hC q X Y (cutoffUnit hC q X ≫ f.hom)
      exact (hu f.hom rfl).trans (hu g.hom h.symm).symm
    · intro f
      obtain ⟨l, hl, _⟩ := cutoffUnit_universal hC q X Y f
      exact ⟨ObjectProperty.homMk l, hl⟩)

theorem cutoffEquiv_natural {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (Y Y' : CutoffModels C q) (g : Y ⟶ Y')
    (h : cutoffObject hC q X ⟶ Y) :
    cutoffEquiv hC q X Y' (h ≫ g) = cutoffEquiv hC q X Y h ≫ g.hom := by
  change cutoffUnit hC q X ≫ (h.hom ≫ g.hom) = (cutoffUnit hC q X ≫ h.hom) ≫ g.hom
  exact (Category.assoc _ _ _).symm

noncomputable def cutoffFunctor {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : C.Model ⥤ CutoffModels C q :=
  Adjunction.leftAdjointOfEquiv (G := (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)))
    (cutoffEquiv hC q) (cutoffEquiv_natural hC q)

noncomputable def cutoffAdjunction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : cutoffFunctor hC q ⊣ (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)) :=
  Adjunction.adjunctionOfEquivLeft _ _

@[instance_reducible] noncomputable def cutoffReflective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : Reflective (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)) :=
  ⟨cutoffFunctor hC q, cutoffAdjunction hC q⟩

theorem cutoff_hasColimits {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : HasColimitsOfSize.{v,v} (CutoffModels C q) := by
  let := cutoffReflective hC q
  exact hasColimits_of_reflective (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q))

end GlobularTheory.Model

end Grothendieck

end OAI
