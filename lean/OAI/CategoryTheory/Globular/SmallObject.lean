import OAI.CategoryTheory.Globular.Boundary

namespace OAI

universe u v w

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0

instance presheafFunctor_finitelyAccessible (C : GlobularTheory.{v}) :
    (presheafFunctor C).IsCardinalAccessible Cardinal.aleph0.{v} := by
  let : C.sumComparisons.isLocal.ι.IsCardinalAccessible Cardinal.aleph0.{v} := by
    apply MorphismProperty.isCardinalAccessible_ι_isLocal _ Cardinal.aleph0.{v}
    rintro X Y f ⟨t⟩
    exact ⟨C.sumComparison_source_presentable t,
      C.shrinkYoneda_cardinalPresentable (C.sumCone t).pt.unop⟩
  let : (toLocal C).IsEquivalence := (localEquivalence C).isEquivalence_functor
  change ((toLocal C) ⋙ C.sumComparisons.isLocal.ι).IsCardinalAccessible Cardinal.aleph0.{v}
  infer_instance

instance freeShape_finitelyPresentable (C : GlobularTheory.{v}) (S : Shape) :
    IsCardinalPresentable (freeShape C S) Cardinal.aleph0.{v} := by
  let e : coyoneda.obj (op (freeShape C S)) ≅
      presheafFunctor C ⋙ (evaluation C.Objᵒᵖ (Type v)).obj (op (⟨S⟩ : C.Obj)) :=
    NatIso.ofComponents (fun X => Equiv.toIso yonedaEquiv)
  exact Functor.isCardinalAccessible_of_natIso e.symm Cardinal.aleph0.{v}

instance disk_finitelyPresentable (C : GlobularTheory.{v}) (n : ℕ) :
    IsCardinalPresentable (disk C n) Cardinal.aleph0.{v} :=
  freeShape_finitelyPresentable C (Shape.globe n)

instance boundaryDisk_finitelyPresentable (C : GlobularTheory.{v}) (n : ℕ) :
    IsCardinalPresentable (boundaryDisk C n) Cardinal.aleph0.{v} := by
  induction n with
  | zero =>
    change IsCardinalPresentable (⊥_ C.Model) Cardinal.aleph0.{v}
    let (k : Discrete PEmpty) : IsCardinalPresentable
        ((Functor.empty C.Model).obj k) Cardinal.aleph0.{v} := by cases k.as
    apply isCardinalPresentable_of_isColimit _ (initialIsInitial) Cardinal.aleph0.{v}
    exact hasCardinalLT_of_finite _ _ le_rfl
  | succ n ih =>
    let := ih
    change IsCardinalPresentable (pushout (I C n) (I C n)) Cardinal.aleph0.{v}
    let (k : WalkingSpan) : IsCardinalPresentable
        ((span (I C n) (I C n)).obj k) Cardinal.aleph0.{v} := by
      cases k with
      | none => exact ih
      | some k => cases k <;> exact disk_finitelyPresentable C n
    apply isCardinalPresentable_of_isColimit _ (colimit.isColimit _) Cardinal.aleph0.{v}
    exact hasCardinalLT_of_finite _ _ le_rfl

open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0

noncomputable def highBoundaries (C : GlobularTheory.{v}) (q : ℕ) :
    MorphismProperty C.Model :=
  MorphismProperty.ofHoms (fun n : {n : ℕ // q < n} => I C n.1)

theorem isCoskeletal_iff_local {C : GlobularTheory.{v}} (M : C.Model) (q : ℕ) :
    M.IsCoskeletal q ↔ (highBoundaries C q).isLocal M := by
  constructor
  · intro h A B i hi
    rcases hi with ⟨⟨n, hn⟩⟩
    let R := boundaryRepresentation C n
    constructor
    · intro f g hfg
      apply (cellEquiv M n).injective
      apply (h n hn).1
      rw [← R.inclusion_boundary, ← R.inclusion_boundary]
      exact congrArg (R.equiv M) hfg
    · intro f
      obtain ⟨x, hx⟩ := (h n hn).2 (R.equiv M f)
      refine ⟨(cellEquiv M n).symm x, ?_⟩
      apply (R.equiv M).injective
      rw [R.inclusion_boundary, Equiv.apply_symm_apply]
      exact hx
  · intro h n hn
    have hb := h (I C n) (MorphismProperty.ofHoms.mk (⟨n, hn⟩ : {n : ℕ // q < n}))
    let R := boundaryRepresentation C n
    change Function.Bijective (fun f : disk C n ⟶ M => R.inclusion ≫ f) at hb
    constructor
    · intro x y hxy
      apply (cellEquiv M n).symm.injective
      apply hb.1
      apply (R.equiv M).injective
      simpa only [R.inclusion_boundary, Equiv.apply_symm_apply] using hxy
    · intro b
      obtain ⟨f, hf⟩ := hb.2 ((R.equiv M).symm b)
      change R.inclusion ≫ f = (R.equiv M).symm b at hf
      refine ⟨cellEquiv M n f, ?_⟩
      rw [← R.inclusion_boundary, hf]
      exact (R.equiv M).apply_symm_apply b

theorem highBoundaries_local (C : GlobularTheory.{v}) (q : ℕ) :
    (highBoundaries C q).isLocal = (fun X : C.Model => X.IsCoskeletal q) := by
  funext X
  exact propext (isCoskeletal_iff_local X q).symm

instance cutoffInclusion_finitelyAccessible (C : GlobularTheory.{v}) (q : ℕ) :
    (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)).IsCardinalAccessible
      Cardinal.aleph0.{v} := by
  rw [← highBoundaries_local]
  apply MorphismProperty.isCardinalAccessible_ι_isLocal _ Cardinal.aleph0.{v}
  rintro A B i ⟨⟨n, hn⟩⟩
  exact ⟨boundaryDisk_finitelyPresentable C n, disk_finitelyPresentable C n⟩

theorem cutoff_finitelyPresentable {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) [IsCardinalPresentable X Cardinal.aleph0.{v}] :
    IsCardinalPresentable ((cutoffFunctor hC q).obj X) Cardinal.aleph0.{v} :=
  (cutoffAdjunction hC q).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0.{v} X

open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0

noncomputable instance hasLimits (C : GlobularTheory.{v}) : HasLimitsOfSize.{v,v} C.Model := by
  let := presheafReflection C
  let : HasLimitsOfSize.{v,v} C.sumComparisons.isLocal.FullSubcategory :=
    hasLimits_of_reflective C.sumComparisons.isLocal.ι
  exact Adjunction.has_limits_of_equivalence (localEquivalence C).functor

theorem hasFillers_iff {C : GlobularTheory.{v}} (X : C.Model) :
    X.underlying.HasFillers ↔ ∀ n (f : boundaryDisk C n ⟶ X),
      ∃ g : disk C n ⟶ X, I C n ≫ g = f := by
  constructor
  · intro h n f
    let R := boundaryRepresentation C n
    obtain ⟨x, hx⟩ := h n (R.equiv X f)
    refine ⟨(cellEquiv X n).symm x, (R.equiv X).injective ?_⟩
    change R.equiv X (R.inclusion ≫ (cellEquiv X n).symm x) = R.equiv X f
    simpa only [R.inclusion_boundary, Equiv.apply_symm_apply] using hx
  · intro h n b
    let R := boundaryRepresentation C n
    obtain ⟨g, hg⟩ := h n ((R.equiv X).symm b)
    refine ⟨cellEquiv X n g, ?_⟩
    change R.inclusion ≫ g = (R.equiv X).symm b at hg
    rw [← R.inclusion_boundary, hg, Equiv.apply_symm_apply]

theorem hasFillers_of_filteredColimit {C : GlobularTheory.{v}}
    {K : Type v} [SmallCategory K] [IsFiltered K]
    {F : K ⥤ C.Model} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ k, (F.obj k).underlying.HasFillers) : c.pt.underlying.HasFillers := by
  rw [hasFillers_iff]
  intro n f
  obtain ⟨k, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc f
  obtain ⟨a, ha⟩ := (hasFillers_iff (F.obj k)).1 (hF k) n g
  exact ⟨a ≫ c.ι.app k, by rw [← Category.assoc, ha, hg]⟩

theorem hasFillers_of_cutoffFilteredColimit {C : GlobularTheory.{v}}
    (q : ℕ)
    {K : Type v} [SmallCategory K] [IsFiltered K]
    {F : K ⥤ CutoffModels C q} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ k, (F.obj k).obj.underlying.HasFillers) : c.pt.obj.underlying.HasFillers := by
  let ι := ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)
  have : PreservesFilteredColimitsOfSize.{v,v} ι :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mp inferInstance
  exact hasFillers_of_filteredColimit (isColimitOfPreserves ι hc) hF

end Grothendieck.GlobularTheory.Model

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

theorem smallObjectArgument_of_finiteDomains {A : Type u} [Category.{v} A]
    [HasColimitsOfSize.{v,v} A] {ι : Type w} [Small.{v} ι]
    {U V : ι → A} (f : ∀ i, U i ⟶ V i)
    [∀ i, IsCardinalPresentable (U i) Cardinal.aleph0.{v}] :
    (MorphismProperty.ofHoms f).HasSmallObjectArgument.{v} := by
  refine ⟨Cardinal.aleph0.{v}, inferInstance, inferInstance, ?_⟩
  refine { preservesColimit := ?_ }
  rintro _ _ _ _ _ ⟨i⟩ g hg
  infer_instance

namespace GlobularTheory.Model

noncomputable abbrev cutoffDisk {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : CutoffModels C q := (cutoffFunctor hC q).obj (disk C n)

noncomputable abbrev cutoffBoundary {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : CutoffModels C q := (cutoffFunctor hC q).obj (boundaryDisk C n)

noncomputable abbrev cutoffI {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : cutoffBoundary hC q n ⟶ cutoffDisk hC q n :=
  (cutoffFunctor hC q).map (I C n)

noncomputable abbrev cutoffJ {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : cutoffDisk hC q n ⟶ cutoffDisk hC q (n+1) :=
  (cutoffFunctor hC q).map (J C n)

noncomputable def boundaryClass {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : MorphismProperty (CutoffModels C q) :=
  MorphismProperty.ofHoms (fun n : {n : ℕ // r ≤ n} => cutoffI hC q n.1)

noncomputable def sourceClass {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : MorphismProperty (CutoffModels C q) :=
  MorphismProperty.ofHoms (fun n : {n : ℕ // r ≤ n} => cutoffJ hC q n.1)

theorem boundaryClass_rlp_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (p : X ⟶ Y) :
    (boundaryClass hC q r).rlp p ↔
      ∀ n, r ≤ n → HasLiftingProperty (I C n) p.hom := by
  constructor
  · intro hp n hn
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).1
      (hp _ (MorphismProperty.ofHoms.mk (⟨n, hn⟩ : {n : ℕ // r ≤ n})))
  · intro hp _ _ i hi
    rcases hi with ⟨⟨n, hn⟩⟩
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).2 (hp n hn)

theorem sourceClass_rlp_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (p : X ⟶ Y) :
    (sourceClass hC q r).rlp p ↔
      ∀ n, r ≤ n → HasLiftingProperty (J C n) p.hom := by
  constructor
  · intro hp n hn
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).1
      (hp _ (MorphismProperty.ofHoms.mk (⟨n, hn⟩ : {n : ℕ // r ≤ n})))
  · intro hp _ _ i hi
    rcases hi with ⟨⟨n, hn⟩⟩
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).2 (hp n hn)

theorem boundaryClass_smallObject {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : (boundaryClass hC q r).HasSmallObjectArgument.{v} := by
  let := cutoff_hasColimits hC q
  let (n : {n : ℕ // r ≤ n}) : IsCardinalPresentable
      (cutoffBoundary hC q n.1) Cardinal.aleph0.{v} :=
    cutoff_finitelyPresentable hC q (boundaryDisk C n.1)
  exact smallObjectArgument_of_finiteDomains _

theorem sourceClass_smallObject {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : (sourceClass hC q r).HasSmallObjectArgument.{v} := by
  let := cutoff_hasColimits hC q
  let (n : {n : ℕ // r ≤ n}) : IsCardinalPresentable
      (cutoffDisk hC q n.1) Cardinal.aleph0.{v} :=
    cutoff_finitelyPresentable hC q (disk C n.1)
  exact smallObjectArgument_of_finiteDomains _

def Cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ)
    (X : CutoffModels C q) : Prop :=
  ∀ {P Q : CutoffModels C q} (p : P ⟶ Q), (boundaryClass hC q 0).rlp p →
    ∀ f : X ⟶ Q, ∃ g : X ⟶ P, g ≫ p = f

theorem Cofibrant.of_cofibration {C : GlobularTheory.{v}} {hC : C.IsCoherator}
    {q : ℕ} {X Y : CutoffModels C q} (hX : Cofibrant hC q X) (i : X ⟶ Y)
    (hi : (boundaryClass hC q 0).rlp.llp i) : Cofibrant hC q Y := by
  intro P Q p hp f
  obtain ⟨g, hg⟩ := hX p hp (i ≫ f)
  let := hi p hp
  have sq : CommSq g i p f := ⟨hg⟩
  exact ⟨sq.lift, sq.fac_right⟩

theorem Cofibrant.retract {C : GlobularTheory.{v}} {hC : C.IsCoherator}
    {q : ℕ} {X Y : CutoffModels C q} (hY : Cofibrant hC q Y)
    (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) : Cofibrant hC q X := by
  intro P Q p hp f
  obtain ⟨g, hg⟩ := hY p hp (r ≫ f)
  exact ⟨i ≫ g, by rw [Category.assoc, hg, ← Category.assoc, hir, Category.id_comp]⟩

theorem hasLiftingProperty_J_of_I {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (p : X ⟶ Y) (hn : HasLiftingProperty (I C n) p)
    (hn₁ : HasLiftingProperty (I C (n+1)) p) : HasLiftingProperty (J C n) p := by
  rw [hasLiftingProperty_J_iff]
  intro x y hy
  have hb : Y.underlying.boundary n (Y.underlying.target n y) =
      (underlyingMap p).boundaryMap n (X.underlying.boundary n x) := by
    rw [(underlyingMap p).boundary_app]
    have hp := (GlobularSet.parallel_iff_boundary_eq Y.underlying n
      (Y.underlying.source n y) (Y.underlying.target n y)).1
        (GlobularSet.Joined.parallel ⟨y, rfl, rfl⟩)
    rw [hy] at hp
    exact hp.symm
  obtain ⟨z, hz, hpz⟩ := (hasLiftingProperty_I_iff n p).1 hn
    (X.underlying.boundary n x) (Y.underlying.target n y) hb
  let b : X.underlying.Boundary (n+1) := ⟨(x,z),
    (GlobularSet.parallel_iff_boundary_eq _ _ _ _).2 hz.symm⟩
  have hby : Y.underlying.boundary (n+1) y = (underlyingMap p).boundaryMap (n+1) b := by
    apply Subtype.ext
    exact Prod.ext hy hpz.symm
  obtain ⟨a, ha, hpa⟩ := (hasLiftingProperty_I_iff (n+1) p).1 hn₁ b y hby
  exact ⟨a, congrArg (fun v => v.1.1) ha, hpa⟩

theorem sourceClass_cofibration_le {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : (sourceClass hC q r).rlp.llp ≤ (boundaryClass hC q r).rlp.llp := by
  apply MorphismProperty.antitone_llp
  intro X Y p hp
  rw [sourceClass_rlp_iff]
  have h := (boundaryClass_rlp_iff hC q r p).1 hp
  intro n hn
  exact hasLiftingProperty_J_of_I n p.hom (h n hn) (h (n+1) (by omega))

theorem boundaryClass_cofibration_le {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r s : ℕ) (hrs : r ≤ s) :
    (boundaryClass hC q s).rlp.llp ≤ (boundaryClass hC q r).rlp.llp := by
  apply MorphismProperty.antitone_llp
  intro X Y p hp
  rw [boundaryClass_rlp_iff] at hp ⊢
  exact fun n hn => hp n (hrs.trans hn)

end GlobularTheory.Model
end Grothendieck

end OAI
