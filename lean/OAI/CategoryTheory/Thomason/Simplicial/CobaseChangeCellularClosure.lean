import OAI.CategoryTheory.Thomason.Transfer.StreetLocalizationFromModel
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

namespace OAI

section

/-! # The universal weak-preserving attachment class

For left properness the relevant attaching maps preserve weak maps after
any cobase change. We keep this universal condition explicit; it is
stronger than testing only weak maps from the original source.
-/

namespace Thomason.Construction.CobaseChangeCellularClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

variable {C : Type u} [Category.{0} C] [HasColimitsOfSize.{0,0} C]

noncomputable section

/-- A single attaching map preserves weak maps under pushout. -/
def weakPreserving (W : MorphismProperty C) : MorphismProperty C :=
  fun _ _ i => W.IsStableUnderCobaseChangeAlong i

/-- Every cobase change of the attaching map preserves weak maps. -/
abbrev universalWeakPreserving (W : MorphismProperty C) : MorphismProperty C :=
  (weakPreserving W).op.universally.unop

omit [HasColimitsOfSize.{0,0} C] in
theorem universalWeakPreserving_iff (W : MorphismProperty C) {A B : C} (i : A ⟶ B) :
    universalWeakPreserving W i ↔
      ∀ {X P : C} (a : A ⟶ X) (b : B ⟶ P) (j : X ⟶ P),
        IsPushout i a b j → W.IsStableUnderCobaseChangeAlong j :=
  FiniteSubsetAttachments.cobaseWeak_iff (weakPreserving W) i

omit [HasColimitsOfSize.{0,0} C] in
theorem universalWeakPreserving_along (W : MorphismProperty C) {A B : C} {i : A ⟶ B}
    (hi : universalWeakPreserving W i) : W.IsStableUnderCobaseChangeAlong i :=
  SimultaneousAttachments.cobaseWeak_le (weakPreserving W) i hi

instance universalWeakPreserving_respectsIso (W : MorphismProperty C) :
    (universalWeakPreserving W).RespectsIso := by
  unfold universalWeakPreserving
  infer_instance

instance universalWeakPreserving_cobaseChange (W : MorphismProperty C) :
    (universalWeakPreserving W).IsStableUnderCobaseChange := by
  unfold universalWeakPreserving
  infer_instance

omit [HasColimitsOfSize.{0,0} C] in
theorem weakPreserving_of_isIso (W : MorphismProperty C) [W.RespectsIso]
    {A B : C} (i : A ⟶ B) [IsIso i] : weakPreserving W i := by
  constructor
  intro X P j b a sq ha
  have : IsIso j := sq.isIso_inr_of_isIso
  rw [← W.cancel_left_of_respectsIso i, sq.w, W.cancel_right_of_respectsIso]
  exact ha

instance weakPreserving_composition (W : MorphismProperty C) :
    (weakPreserving W).IsStableUnderComposition where
  comp_mem f g hf hg := by
    let : W.IsStableUnderCobaseChangeAlong f := hf
    let : W.IsStableUnderCobaseChangeAlong g := hg
    change W.IsStableUnderCobaseChangeAlong (f ≫ g)
    infer_instance

instance universalWeakPreserving_multiplicative (W : MorphismProperty C) [W.RespectsIso] :
    (universalWeakPreserving W).IsMultiplicative where
  id_mem A := by
    rw [universalWeakPreserving_iff]
    intro X P a b j sq
    have : IsIso j := sq.isIso_inr_of_isIso
    exact weakPreserving_of_isIso W j
  comp_mem := (inferInstance : (universalWeakPreserving W).IsStableUnderComposition).comp_mem

section CanonicalComparison

variable {A B X Y : C} (i : A ⟶ B) (a : A ⟶ X) (w : X ⟶ Y)

/-- The map between the two pushouts induced by a map of attaching targets. -/
abbrev comparison : pushout i a ⟶ pushout i (a ≫ w) :=
  pushout.desc (pushout.inl i (a ≫ w)) (w ≫ pushout.inr i (a ≫ w))
    (by rw [pushout.condition, Category.assoc])

@[reassoc, simp] theorem inl_comparison :
    pushout.inl i a ≫ comparison i a w = pushout.inl i (a ≫ w) :=
  pushout.inl_desc _ _ _

@[reassoc, simp] theorem inr_comparison :
    pushout.inr i a ≫ comparison i a w = w ≫ pushout.inr i (a ≫ w) :=
  pushout.inr_desc _ _ _

theorem comparison_isPushout :
    IsPushout w (pushout.inr i a) (pushout.inr i (a ≫ w)) (comparison i a w) := by
  have outer : IsPushout (a ≫ w) i (pushout.inr i (a ≫ w))
      (pushout.inl i a ≫ comparison i a w) := by
    rw [inl_comparison]
    exact (IsPushout.of_hasPushout i (a ≫ w)).flip
  exact outer.of_left (inr_comparison i a w).symm (IsPushout.of_hasPushout i a).flip

theorem comparison_weak (W : MorphismProperty C) (hi : universalWeakPreserving W i)
    (hw : W w) : W (comparison i a w) := by
  let := (universalWeakPreserving_iff W i).mp hi a _ _ (IsPushout.of_hasPushout i a)
  exact IsStableUnderCobaseChangeAlong.of_isPushout (comparison_isPushout i a w).flip hw

end CanonicalComparison

/-- Canonical pushouts suffice to test all the universal squares. -/
theorem of_comparison_weak (W : MorphismProperty C) [W.RespectsIso]
    {A B : C} (i : A ⟶ B)
    (h : ∀ {X Y : C} (a : A ⟶ X) (w : X ⟶ Y),
      W w → W (comparison i a w)) : universalWeakPreserving W i := by
  rw [universalWeakPreserving_iff]
  intro X P a b j sq
  constructor
  intro Y Q l k w sq' hw
  let e₀ := (IsPushout.of_hasPushout i a).isoIsPushout _ _ sq
  let e₁ := (IsPushout.of_hasPushout i (a ≫ w)).isoIsPushout
    _ _ (sq.paste_vert sq')
  have he : comparison i a w ≫ e₁.hom = e₀.hom ≫ k := by
    apply pushout.hom_ext
    · dsimp only [e₀, e₁]
      simp only [inl_comparison_assoc,
        IsPushout.inl_isoIsPushout_hom, IsPushout.inl_isoIsPushout_hom_assoc]
    · dsimp only [e₀, e₁]
      simp only [inr_comparison_assoc,
        IsPushout.inr_isoIsPushout_hom, IsPushout.inr_isoIsPushout_hom_assoc]
      exact sq'.w.symm
  rw [← W.cancel_left_of_respectsIso e₀.hom, ← he,
    W.cancel_right_of_respectsIso]
  exact h a w hw

section Filtered

attribute [local instance] IsFiltered.isConnected

variable {J : Type} [Category.{0} J] [IsFiltered J]

noncomputable def constColimitIso (X : C) : colimit ((Functor.const J).obj X) ≅ X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J X)

omit [HasColimitsOfSize.{0,0} C] in
@[reassoc, simp] theorem constColimitIso_ι (X : C) (j : J) :
    colimit.ι ((Functor.const J).obj X) j ≫ (constColimitIso (J := J) X).hom = 𝟙 X :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j

@[reassoc] theorem constColimitIso_map {X Y : C} (w : X ⟶ Y) :
    colim.map ((Functor.const J).map w) ≫ (constColimitIso (J := J) Y).hom =
      (constColimitIso (J := J) X).hom ≫ w := by
  apply colimit.hom_ext
  intro j
  simp only [colimit.ι_map_assoc, Functor.const_map_app, constColimitIso_ι,
    constColimitIso_ι_assoc]
  change w ≫ 𝟙 Y = 𝟙 X ≫ w
  simp only [Category.comp_id, Category.id_comp]

/-- A map from a diagram to a constant target, induced by its colimit. -/
def toConstant {D : J ⥤ C} {X : C} (a : colimit D ⟶ X) :
    D ⟶ (Functor.const J).obj X :=
  (colimit.cocone D).ι ≫ (Functor.const J).map a

@[reassoc] theorem toConstant_colimMap {D : J ⥤ C} {X : C} (a : colimit D ⟶ X) :
    colim.map (toConstant a) ≫ (constColimitIso (J := J) X).hom = a := by
  apply colimit.hom_ext
  intro j
  simp only [colimit.ι_map_assoc, toConstant, NatTrans.comp_app,
    Functor.const_map_app, Category.assoc, constColimitIso_ι]
  change colimit.ι D j ≫ a ≫ 𝟙 X = colimit.ι D j ≫ a
  rw [Category.comp_id]

@[reassoc] theorem constColimitIso_inv_map {X Y : C} (w : X ⟶ Y) :
    (constColimitIso (J := J) X).inv ≫ colim.map ((Functor.const J).map w) =
      w ≫ (constColimitIso (J := J) Y).inv := by
  apply (cancel_mono (constColimitIso (J := J) Y).hom).mp
  simp only [Category.assoc, constColimitIso_map, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Commuting colimits with a pushout having a constant right leg. -/
theorem colimit_constant_pushout {D E : J ⥤ C} (η : D ⟶ E) {X : C}
    (β : D ⟶ (Functor.const J).obj X) (b : colimit D ⟶ X)
    (hb : colim.map β ≫ (constColimitIso (J := J) X).hom = b) :
    IsPushout (colim.map η) b (colim.map (pushout.inl η β))
      ((constColimitIso (J := J) X).inv ≫ colim.map (pushout.inr η β)) := by
  apply ((colim : (J ⥤ C) ⥤ C).map_isPushout (IsPushout.of_hasPushout η β)).of_iso
    (Iso.refl _) (Iso.refl _) (constColimitIso (J := J) X) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.id_comp] using hb
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Universal weak preservation is stable under a filtered colimit of
attaching maps, with no monomorphism assumption on the diagram. -/
theorem universalWeakPreserving_colimMap (W : MorphismProperty C) [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}] {D E : J ⥤ C} (η : D ⟶ E)
    (hη : ∀ j, universalWeakPreserving W (η.app j)) :
    universalWeakPreserving W (colim.map η) := by
  apply of_comparison_weak W
  intro X Y a w hw
  let β := toConstant (J := J) a
  let γ := (Functor.const J).map w
  let v := comparison η β γ
  have hv : ∀ j, W (v.app j) := by
    intro j
    let ev := (evaluation J C).obj j
    have hs := ev.map_isPushout (IsPushout.of_hasPushout η β)
    let : W.IsStableUnderCobaseChangeAlong (ev.map (pushout.inr η β)) := by
      change W.IsStableUnderCobaseChangeAlong ((pushout.inr η β).app j)
      exact (universalWeakPreserving_iff W (η.app j)).mp (hη j)
        (β.app j) ((pushout.inl η β).app j) ((pushout.inr η β).app j) hs
    exact IsStableUnderCobaseChangeAlong.of_isPushout
      (ev.map_isPushout (comparison_isPushout η β γ)).flip hw
  have hcv : W (colim.map v) := MorphismProperty.colimMap (W := W) v hv
  have hβ : colim.map β ≫ (constColimitIso (J := J) X).hom = a :=
    toConstant_colimMap a
  have hβγ : colim.map (β ≫ γ) ≫ (constColimitIso (J := J) Y).hom = a ≫ w := by
    rw [Functor.map_comp, Category.assoc, constColimitIso_map, ← Category.assoc, hβ]
  have sx := colimit_constant_pushout η β a hβ
  have sy := colimit_constant_pushout η (β ≫ γ) (a ≫ w) hβγ
  let e₀ := (IsPushout.of_hasPushout (colim.map η) a).isoIsPushout _ _ sx
  let e₁ := (IsPushout.of_hasPushout (colim.map η) (a ≫ w)).isoIsPushout _ _ sy
  have hl : colim.map (pushout.inl η β) ≫ colim.map v =
      colim.map (pushout.inl η (β ≫ γ)) := by
    simpa only [Functor.map_comp] using
      congrArg ((colim : (J ⥤ C) ⥤ C).map) (inl_comparison η β γ)
  have hr : colim.map (pushout.inr η β) ≫ colim.map v =
      colim.map γ ≫ colim.map (pushout.inr η (β ≫ γ)) := by
    simpa only [Functor.map_comp] using
      congrArg ((colim : (J ⥤ C) ⥤ C).map) (inr_comparison η β γ)
  have he : comparison (colim.map η) a w ≫ e₁.hom = e₀.hom ≫ colim.map v := by
    apply pushout.hom_ext
    · dsimp only [e₀, e₁]
      rw [inl_comparison_assoc, IsPushout.inl_isoIsPushout_hom,
        ← Category.assoc, IsPushout.inl_isoIsPushout_hom, hl]
    · dsimp only [e₀, e₁]
      simp only [inr_comparison_assoc, IsPushout.inr_isoIsPushout_hom,
        IsPushout.inr_isoIsPushout_hom_assoc]
      simp only [Category.assoc, hr]
      simpa only [γ] using (constColimitIso_inv_map_assoc (J := J) w
        (colim.map (pushout.inr η (β ≫ γ)))).symm
  rw [← W.cancel_right_of_respectsIso _ e₁.hom, he, W.cancel_left_of_respectsIso]
  exact hcv

instance universalWeakPreserving_filtered (W : MorphismProperty C) [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}] :
    (universalWeakPreserving W).IsStableUnderColimitsOfShape J where
  condition D E c d hc hd η hη f hf := by
    let e₀ := (colimit.isColimit D).coconePointUniqueUpToIso hc
    let e₁ := (colimit.isColimit E).coconePointUniqueUpToIso hd
    have he : e₀.hom ≫ f = colim.map η ≫ e₁.hom := by
      apply colimit.hom_ext
      intro j
      have h₀ : colimit.ι D j ≫ e₀.hom = c.ι.app j :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      have h₁ : colimit.ι E j ≫ e₁.hom = d.ι.app j :=
        IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
      rw [← Category.assoc, h₀, colimit.ι_map_assoc, h₁]
      exact hf j
    exact ((universalWeakPreserving W).arrow_mk_iso_iff (Arrow.isoMk e₀ e₁ he)).mp
      (universalWeakPreserving_colimMap W η hη)

end Filtered

instance universalWeakPreserving_filteredColimits (W : MorphismProperty C) [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}] :
    (universalWeakPreserving W).IsStableUnderFilteredColimits.{0,0} where
  isStableUnderColimitsOfShape _J := inferInstance

instance universalWeakPreserving_transfinite (W : MorphismProperty C) [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}] :
    (universalWeakPreserving W).IsStableUnderTransfiniteComposition.{0} := inferInstance



section Retracts

variable {A B A' B' X Y : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (r : RetractArrow f g) (a : A ⟶ X)

abbrev pushoutEmbedding : pushout f a ⟶ pushout g (r.r.left ≫ a) :=
  pushout.map f a g (r.r.left ≫ a) r.i.right (𝟙 X) r.i.left r.i_w.symm
    (by rw [Category.comp_id, ← Category.assoc, r.retract_left, Category.id_comp])

abbrev pushoutProjection : pushout g (r.r.left ≫ a) ⟶ pushout f a :=
  pushout.map g (r.r.left ≫ a) f a r.r.right (𝟙 X) r.r.left r.r_w.symm
    (Category.comp_id _)

@[simp] theorem pushoutEmbedding_projection :
    pushoutEmbedding r a ≫ pushoutProjection r a = 𝟙 _ := by
  apply pushout.hom_ext <;>
    simp [pushoutEmbedding, pushoutProjection, pushout.map, pushout.inl_desc,
      pushout.inr_desc, pushout.inl_desc_assoc, pushout.inr_desc_assoc, Category.assoc]

variable (w : X ⟶ Y)

/-- The larger comparison written with a fixed association of its target. -/
abbrev liftedComparison : pushout g (r.r.left ≫ a) ⟶ pushout g (r.r.left ≫ (a ≫ w)) :=
  pushout.desc (pushout.inl _ _) (w ≫ pushout.inr _ _)
    (by simp only [pushout.condition, Category.assoc])

theorem liftedComparison_isPushout :
    IsPushout w (pushout.inr g (r.r.left ≫ a))
      (pushout.inr g (r.r.left ≫ (a ≫ w))) (liftedComparison r a w) := by
  have outer : IsPushout ((r.r.left ≫ a) ≫ w) g
      (pushout.inr g (r.r.left ≫ (a ≫ w)))
      (pushout.inl g (r.r.left ≫ a) ≫ liftedComparison r a w) := by
    rw [show pushout.inl g (r.r.left ≫ a) ≫ liftedComparison r a w =
      pushout.inl g (r.r.left ≫ (a ≫ w)) from pushout.inl_desc _ _ _, Category.assoc]
    exact (IsPushout.of_hasPushout g (r.r.left ≫ (a ≫ w))).flip
  exact outer.of_left (pushout.inr_desc _ _ _).symm
    (IsPushout.of_hasPushout g (r.r.left ≫ a)).flip

theorem pushoutEmbedding_comparison :
    pushoutEmbedding r a ≫ liftedComparison r a w =
      comparison f a w ≫ pushoutEmbedding r (a ≫ w) := by
  apply pushout.hom_ext <;>
    simp [pushoutEmbedding, liftedComparison, comparison, pushout.map, pushout.inl_desc,
      pushout.inr_desc, pushout.inl_desc_assoc, pushout.inr_desc_assoc, Category.assoc]

theorem pushoutProjection_comparison :
    pushoutProjection r a ≫ comparison f a w =
      liftedComparison r a w ≫ pushoutProjection r (a ≫ w) := by
  apply pushout.hom_ext <;>
    simp [pushoutProjection, liftedComparison, comparison, pushout.map, pushout.inl_desc,
      pushout.inr_desc, pushout.inl_desc_assoc, pushout.inr_desc_assoc, Category.assoc]

def comparisonRetract : RetractArrow (comparison f a w) (liftedComparison r a w) where
  i := Arrow.homMk (pushoutEmbedding r a) (pushoutEmbedding r (a ≫ w))
    (pushoutEmbedding_comparison r a w)
  r := Arrow.homMk (pushoutProjection r a) (pushoutProjection r (a ≫ w))
    (pushoutProjection_comparison r a w)
  retract := by
    apply Arrow.hom_ext <;> exact pushoutEmbedding_projection r _

end Retracts

instance universalWeakPreserving_retracts (W : MorphismProperty C) [W.RespectsIso]
    [W.IsStableUnderRetracts] : (universalWeakPreserving W).IsStableUnderRetracts where
  of_retract {A B A' B' f g} r hg := by
    apply of_comparison_weak W
    intro X Y a w hw
    have hbig : W (liftedComparison r a w) := by
      let : W.IsStableUnderCobaseChangeAlong (pushout.inr g (r.r.left ≫ a)) :=
        (universalWeakPreserving_iff W g).mp hg (r.r.left ≫ a) _ _
          (IsPushout.of_hasPushout g (r.r.left ≫ a))
      exact IsStableUnderCobaseChangeAlong.of_isPushout
        (liftedComparison_isPushout r a w).flip hw
    exact W.of_retract (comparisonRetract r a w) hbig

instance universalWeakPreserving_coproducts (W : MorphismProperty C) [W.RespectsIso]
    [W.IsStableUnderFilteredColimits.{0,0}] :
    (universalWeakPreserving W).IsStableUnderCoproducts.{0} where
  isStableUnderCoproductsOfShape _α := IsStableUnderCoproductsOfShape.mk _ _ (by
    intro A B _ _ i hi
    apply SimultaneousAttachments.cobaseWeak_le (universalWeakPreserving W)
    apply SimultaneousAttachments.cobaseWeak_sigmaMap (universalWeakPreserving W) i
    intro j
    rw [FiniteSubsetAttachments.cobaseWeak_iff]
    intro X P a b k sq
    exact MorphismProperty.of_isPushout sq.flip (hi j))

/-- Universal weak preservation by the generators propagates to every
map in their generated left lifting class. -/
theorem generated_left_preserves_weak (I W : MorphismProperty C)
    [I.HasSmallObjectArgument.{0}] [W.RespectsIso] [W.IsStableUnderRetracts]
    [W.IsStableUnderFilteredColimits.{0,0}]
    (hI : I ≤ universalWeakPreserving W) :
    W.IsStableUnderCobaseChangeAgainst I.rlp.llp := by
  have hleft : I.rlp.llp ≤ universalWeakPreserving W := by
    rw [I.llp_rlp_of_hasSmallObjectArgument, retracts_le_iff]
    apply (transfiniteCompositions_monotone.{0} ?_).trans
      (universalWeakPreserving W).transfiniteCompositions_le
    exact pushouts_le_iff.mpr (coproducts_le_iff.mpr hI)
  refine ⟨?_⟩
  intro A B i hi
  exact universalWeakPreserving_along W (hleft i hi)

end

end Thomason.Construction.CobaseChangeCellularClosure

end

end OAI
