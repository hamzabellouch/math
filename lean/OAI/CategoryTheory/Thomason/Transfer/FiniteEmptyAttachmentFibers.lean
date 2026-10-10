import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SieveFiberPresentation
import OAI.CategoryTheory.Thomason.Strict.OrientalFiniteCells
import OAI.CategoryTheory.Thomason.Strict.StrictPosetWeakEquivalences
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.PastingGlobeCylinderPushout
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge

namespace OAI

section

/-! # Unconditional full endpoint-fibre compatibility for actual attaching pushouts at either endpoint -/

namespace Thomason.Construction.EndpointFiber

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

/-- The fibre square is a pushout for the original unlabelled attachment,
once its four strict labels commute. -/
theorem omega_pushout_fibers (e : Fin 2)
    {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pA : A ⟶ StrictPoset.category (Fin 2)) (pB : B ⟶ StrictPoset.category (Fin 2))
    (pX : X ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hi : i ≫ pB = pA) (ha : a ≫ pX = pA)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = pX) :
    IsPushout (labelFiberMap pA pB e i hi) (labelFiberMap pA pX e a ha)
      (labelFiberMap pB pY e b hb) (labelFiberMap pX pY e j hj) := by
  have := constructedLabelFiberInput.omega e
  exact (isPushout_over hp pA pB pX pY hi ha hb hj).map (labelFiberFunctor (Fin 2) e)

/-- The same compatibility theorem uses the finite-category pushout itself. -/
theorem finite_pushout_fibers (n : ℕ) (e : Fin 2)
    {A B X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pA : A ⟶ finiteInterval n) (pB : B ⟶ finiteInterval n)
    (pX : X ⟶ finiteInterval n) (pY : Y ⟶ finiteInterval n)
    (hi : i ≫ pB = pA) (ha : a ≫ pX = pA)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = pX) :
    IsPushout
      ((finiteLabelFiberFunctor n e).map (Over.homMk i hi : Over.mk pA ⟶ Over.mk pB))
      ((finiteLabelFiberFunctor n e).map (Over.homMk a ha : Over.mk pA ⟶ Over.mk pX))
      ((finiteLabelFiberFunctor n e).map (Over.homMk b hb : Over.mk pB ⟶ Over.mk pY))
      ((finiteLabelFiberFunctor n e).map (Over.homMk j hj : Over.mk pX ⟶ Over.mk pY)) := by
  have := constructedLabelFiberInput.finite n e
  exact (isPushout_over hp pA pB pX pY hi ha hb hj).map (finiteLabelFiberFunctor n e)

end Thomason.Construction.EndpointFiber

end

section

/-! # A full fibre disjoint from the old part is unchanged by attachment -/

namespace Thomason.Construction.EndpointFiber

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

/-- If both old labels are constant at the other endpoint, the new fibre
maps isomorphically onto the fibre of the actual pushout. -/
theorem omega_attachment_complement_iso (e d : Fin 2) (hed : d ≠ e)
    {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pB : B ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hi : i ≫ pB = constantLabel A d)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = constantLabel X d) :
    IsIso (labelFiberMap pB pY e b hb) := by
  have ha : a ≫ constantLabel X d = constantLabel A d := by apply Hom.ext; rfl
  have hpF := omega_pushout_fibers e hp (constantLabel A d) pB
    (constantLabel X d) pY hi ha hb hj
  let : IsEmpty (labelFiber (constantLabel A d) e) := constantFiber_empty A d e hed
  let : IsEmpty (labelFiber (constantLabel X d) e) := constantFiber_empty X d e hed
  let ei := isoOfBijective (labelFiberMap (constantLabel A d) (constantLabel X d) e a ha)
    ⟨by intro x; exact isEmptyElim x, by intro x; exact isEmptyElim x⟩
  have : IsIso (labelFiberMap (constantLabel A d) (constantLabel X d) e a ha) := ei.isIso_hom
  exact hpF.isIso_inl_of_isIso

end Thomason.Construction.EndpointFiber

end

section

/-! # Full labelled pieces after an arbitrary attachment

If a labelled piece `U` of the attaching category contains the attaching
source, its full fibre after attachment is the pushout of `U` with the old
target. The assertion uses the original attaching map, without injectivity
or freeness assumptions on that map.
-/

namespace Thomason.Construction.EndpointFiber

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

/-- The labelled fibre is precisely a pushout with the chosen full piece. -/
theorem omega_attachment_piece (e : Fin 2)
    {A B U X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {iU : A ⟶ U} {u : U ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (hiU : iU ≫ u = i)
    (pB : B ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hi : i ≫ pB = constantLabel A e)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = constantLabel X e)
    (eU : U ≅ labelFiber pB e) (hu : eU.hom ≫ labelFiberInclusion pB e = u) :
    IsPushout iU a
      (eU.hom ≫ labelFiberMap pB pY e b hb)
      ((constantFiberIso X e).inv ≫ labelFiberMap (constantLabel X e) pY e j hj) := by
  have ha : a ≫ constantLabel X e = constantLabel A e := by apply Hom.ext; rfl
  have hpF := EndpointFiber.omega_pushout_fibers e hp (constantLabel A e) pB
    (constantLabel X e) pY hi ha hb hj
  apply hpF.of_iso (constantFiberIso A e) eU.symm (constantFiberIso X e) (Iso.refl _)
  · apply (cancel_mono eU.hom).mp
    apply (cancel_mono (labelFiberInclusion pB e)).mp
    simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_assoc]
    rw [hu, hiU]
    apply Hom.ext
    rfl
  · apply Hom.ext
    rfl
  · simp
  · simp

/-- The inclusion of the constructed piece into the original pushout is
exactly its original structure map. -/
theorem omega_attachment_piece_inclusion (e : Fin 2)
    {B U X Y : StrictOmegaCategory.{0}} {u : U ⟶ B}
    {b : B ⟶ Y} {j : X ⟶ Y}
    (pB : B ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hb : b ≫ pY = pB) (hj : j ≫ pY = constantLabel X e)
    (eU : U ≅ labelFiber pB e) (hu : eU.hom ≫ labelFiberInclusion pB e = u) :
    (eU.hom ≫ labelFiberMap pB pY e b hb) ≫ labelFiberInclusion pY e = u ≫ b ∧
      ((constantFiberIso X e).inv ≫ labelFiberMap (constantLabel X e) pY e j hj) ≫
        labelFiberInclusion pY e = j := by
  constructor
  · rw [Category.assoc, ← hu, Category.assoc]
    congr 1
  · apply Hom.ext
    rfl

end Thomason.Construction.EndpointFiber

end

section

/-! # Unconditional full zero-fibre compatibility for actual attaching pushouts -/

namespace Thomason.Construction.ZeroFiber

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

/-- The fibre square is a pushout for the original unlabelled attachment,
once its four strict labels commute. -/
theorem omega_pushout_fibers
    {A B X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pA : A ⟶ StrictPoset.category (Fin 2)) (pB : B ⟶ StrictPoset.category (Fin 2))
    (pX : X ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hi : i ≫ pB = pA) (ha : a ≫ pX = pA)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = pX) :
    IsPushout (labelFiberMap pA pB 0 i hi) (labelFiberMap pA pX 0 a ha)
      (labelFiberMap pB pY 0 b hb) (labelFiberMap pX pY 0 j hj) := by
  have := TerminalCone.zeroFiber_preservesColimits
  exact (isPushout_over hp pA pB pX pY hi ha hb hj).map (labelFiberFunctor (Fin 2) 0)

/-- The same compatibility theorem uses the finite-category pushout itself. -/
theorem finite_pushout_fibers (n : ℕ)
    {A B X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j)
    (pA : A ⟶ finiteInterval n) (pB : B ⟶ finiteInterval n)
    (pX : X ⟶ finiteInterval n) (pY : Y ⟶ finiteInterval n)
    (hi : i ≫ pB = pA) (ha : a ≫ pX = pA)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = pX) :
    IsPushout
      ((finiteLabelFiberFunctor n 0).map (Over.homMk i hi : Over.mk pA ⟶ Over.mk pB))
      ((finiteLabelFiberFunctor n 0).map (Over.homMk a ha : Over.mk pA ⟶ Over.mk pX))
      ((finiteLabelFiberFunctor n 0).map (Over.homMk b hb : Over.mk pB ⟶ Over.mk pY))
      ((finiteLabelFiberFunctor n 0).map (Over.homMk j hj : Over.mk pX ⟶ Over.mk pY)) := by
  have := TerminalCone.finiteZeroFiber_preservesColimits n
  exact (isPushout_over hp pA pB pX pY hi ha hb hj).map (finiteLabelFiberFunctor n 0)

end Thomason.Construction.ZeroFiber

end

section

/-! # Full labelled pieces after an arbitrary attachment

If a labelled piece `U` of the attaching category contains the attaching
source, its full fibre after attachment is the pushout of `U` with the old
target. The assertion uses the original attaching map, without injectivity
or freeness assumptions on that map.
-/

namespace Thomason.Construction.ZeroFiber

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

/-- The labelled fibre is precisely a pushout with the chosen full piece. -/
theorem omega_attachment_piece
    {A B U X Y : StrictOmegaCategory.{0}}
    {i : A ⟶ B} {iU : A ⟶ U} {u : U ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (hiU : iU ≫ u = i)
    (pB : B ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hi : i ≫ pB = constantLabel A 0)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = constantLabel X 0)
    (eU : U ≅ labelFiber pB 0) (hu : eU.hom ≫ labelFiberInclusion pB 0 = u) :
    IsPushout iU a
      (eU.hom ≫ labelFiberMap pB pY 0 b hb)
      ((constantFiberIso X 0).inv ≫ labelFiberMap (constantLabel X 0) pY 0 j hj) := by
  have ha : a ≫ constantLabel X 0 = constantLabel A 0 := by apply Hom.ext; rfl
  have hpF := ZeroFiber.omega_pushout_fibers hp (constantLabel A 0) pB
    (constantLabel X 0) pY hi ha hb hj
  apply hpF.of_iso (constantFiberIso A 0) eU.symm (constantFiberIso X 0) (Iso.refl _)
  · apply (cancel_mono eU.hom).mp
    apply (cancel_mono (labelFiberInclusion pB 0)).mp
    simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_assoc]
    rw [hu, hiU]
    apply Hom.ext
    rfl
  · apply Hom.ext
    rfl
  · simp
  · simp

/-- The inclusion of the constructed piece into the original pushout is
exactly its original structure map. -/
theorem omega_attachment_piece_inclusion
    {B U X Y : StrictOmegaCategory.{0}} {u : U ⟶ B}
    {b : B ⟶ Y} {j : X ⟶ Y}
    (pB : B ⟶ StrictPoset.category (Fin 2)) (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hb : b ≫ pY = pB) (hj : j ≫ pY = constantLabel X 0)
    (eU : U ≅ labelFiber pB 0) (hu : eU.hom ≫ labelFiberInclusion pB 0 = u) :
    (eU.hom ≫ labelFiberMap pB pY 0 b hb) ≫ labelFiberInclusion pY 0 = u ≫ b ∧
      ((constantFiberIso X 0).inv ≫ labelFiberMap (constantLabel X 0) pY 0 j hj) ≫
        labelFiberInclusion pY 0 = j := by
  constructor
  · rw [Category.assoc, ← hu, Category.assoc]
    congr 1
  · apply Hom.ext
    rfl

end Thomason.Construction.ZeroFiber

end

section

/-! # The published finite-poset sieve input

Ara--Maltsiniotis (2014), Proposition 5.5 and its proof, combined with
Lemma 5.12 and Proposition 5.13(c), identify the image of a poset sieve
with the full zero-fibre of its characteristic label. Section 5 fixes
`0 < n ≤ ∞`. Finite posets suffice for the transfer criterion by Remark 4.13.
The comparison maps use the actual categorification, and their
invertibility is the hypothesis of this interface.

Original source: https://arxiv.org/pdf/1305.5086v3, pp.27--29, 31--32.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

/-- The finite-poset specialization of published sieve preservation. -/
structure PublishedPosetSieveInput (h : NormalizedSimplexIdentities) [StrictColimitsInput] : Prop where
  omega {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A) :
    IsIso (h.posetFiberMap A hA)
  finite (n : ℕ) (r : FiniteReflectionInput n)
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A) :
    IsIso (C := StrictOmegaCategory.Truncated (n + 1)) (r.posetFiberMap h A hA)

namespace PublishedPosetSieveInput

variable {h : NormalizedSimplexIdentities} [StrictColimitsInput]
  (s : PublishedPosetSieveInput h)

include s

/-- The original categorified sieve map is monic. -/
theorem omega_mono {P : Type} [PartialOrder P] [Finite P]
    (A : Set P) (hA : IsLowerSet A) : Mono (h.posetMap (subposetInclusion A)) := by
  have := s.omega A hA
  rw [← h.posetFiberMap_inclusion A hA]
  infer_instance

/-- Its actual Street nerve is a simplicial monomorphism. -/
theorem omega_nerve_mono {P : Type} [PartialOrder P] [Finite P]
    (A : Set P) (hA : IsLowerSet A) :
    Mono (h.streetNerve.map (h.posetMap (subposetInclusion A))) := by
  have := s.omega A hA
  rw [← h.posetFiberMap_inclusion A hA, h.streetNerve.map_comp]
  infer_instance

/-- Relating the canonical fibre map to the map obtained by taking fibres
of the original inclusion with its constant source label. -/
theorem omega_source_fiber_iso {P : Type} [PartialOrder P] [Finite P]
    (A : Set P) (hA : IsLowerSet A)
    (hi : h.posetMap (subposetInclusion A) ≫ h.membershipLabel A hA =
      constantLabel (h.categorification.obj (nerve A)) 0) :
    IsIso (labelFiberMap (constantLabel (h.categorification.obj (nerve A)) 0)
      (h.membershipLabel A hA) 0 (h.posetMap (subposetInclusion A)) hi) := by
  have := s.omega A hA
  have he : labelFiberMap (constantLabel (h.categorification.obj (nerve A)) 0)
      (h.membershipLabel A hA) 0 (h.posetMap (subposetInclusion A)) hi =
      (constantFiberIso (h.categorification.obj (nerve A)) 0).hom ≫ h.posetFiberMap A hA := by
    apply Hom.ext
    rfl
  rw [he]
  infer_instance

/-- For every attaching functor, the old target is the actual full zero-fibre
of a label on the pushout. The isomorphism commutes with the original map. -/
theorem omega_attachment_full_fiber {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    ∃ (pY : Y ⟶ StrictPoset.category (Fin 2)) (e : X ≅ labelFiber pY 0),
      e.hom ≫ labelFiberInclusion pY 0 = j ∧
      b ≫ pY = h.membershipLabel A hA ∧ j ≫ pY = constantLabel X 0 := by
  let pB := h.membershipLabel A hA
  have hi : h.posetMap (subposetInclusion A) ≫ pB =
      constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact h.posetMap_membership_zero A hA _ (fun z => z.property) x
  have ha : a ≫ constantLabel X 0 = constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    rfl
  obtain ⟨pY, hb, hj⟩ := hp.exists_desc pB (constantLabel X 0) (hi.trans ha.symm)
  have := s.omega_source_fiber_iso A hA hi
  have hpF := ZeroFiber.omega_pushout_fibers hp
    (constantLabel (h.categorification.obj (nerve A)) 0) pB (constantLabel X 0) pY hi ha hb hj
  have : IsIso (labelFiberMap (constantLabel X 0) pY 0 j hj) := hpF.isIso_inr_of_isIso
  let k : X ⟶ labelFiber pY 0 := (constantFiberIso X 0).inv ≫
    labelFiberMap (constantLabel X 0) pY 0 j hj
  have : IsIso k := by dsimp [k]; infer_instance
  refine ⟨pY, asIso k, ?_, hb, hj⟩
  apply Hom.ext
  rfl

/-- Arbitrary attachments along these finite-poset sieves remain monic. -/
theorem omega_attachment_mono {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) : Mono j := by
  obtain ⟨pY, e, he, _, _⟩ := s.omega_attachment_full_fiber A hA hp
  rw [← he]
  infer_instance

end PublishedPosetSieveInput
end Thomason.Construction

end

section

/-! # Canonical sieve pieces of poset attachments

The abstract labelled piece-pushout calculation is here applied to the
original categorified poset inclusions. These are the smaller attachments
used by the finite couniversality induction.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

/-- The inclusion between two full subposets with nested object sets. -/
def subposetInclusionWithin {P : Type} [PartialOrder P]
    (A U : Set P) (hAU : A ⊆ U) : A →o U where
  toFun x := ⟨x.val, hAU x.property⟩
  monotone' := fun _ _ h => h

/-- Restricting the ambient poset retains a canonically isomorphic old part. -/
def restrictedOldIso {P : Type} [PartialOrder P]
    (A U : Set P) (hAU : A ⊆ U) : A ≃o {x : U | x.val ∈ A} where
  toFun x := ⟨⟨x.val, hAU x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Categorification carries an order isomorphism to an actual strict isomorphism. -/
noncomputable def posetMapIso {E F : Type} [PartialOrder E] [PartialOrder F]
    (e : E ≃o F) : h.categorification.obj (nerve E) ≅ h.categorification.obj (nerve F) where
  hom := h.posetMap e.toOrderEmbedding.toOrderHom
  inv := h.posetMap e.symm.toOrderEmbedding.toOrderHom
  hom_inv_id := by
    rw [← h.posetMap_comp]
    have he : e.symm.toOrderEmbedding.toOrderHom.comp e.toOrderEmbedding.toOrderHom = OrderHom.id := by
      ext x
      exact e.symm_apply_apply x
    rw [he, h.posetMap_id]
  inv_hom_id := by
    rw [← h.posetMap_comp]
    have he : e.toOrderEmbedding.toOrderHom.comp e.symm.toOrderEmbedding.toOrderHom = OrderHom.id := by
      ext x
      exact e.apply_symm_apply x
    rw [he, h.posetMap_id]

/-- The original nested inclusions commute after categorification. -/
theorem subposetInclusionWithin_fac {P : Type} [PartialOrder P]
    (A U : Set P) (hAU : A ⊆ U) :
    h.posetMap (subposetInclusionWithin A U hAU) ≫ h.posetMap (subposetInclusion U) =
      h.posetMap (subposetInclusion A) := by
  rw [← h.posetMap_comp]
  rfl

end NormalizedSimplexIdentities

namespace PublishedPosetSieveInput

variable {h : NormalizedSimplexIdentities} [StrictColimitsInput]
  (s : PublishedPosetSieveInput h) include s

/-- A containing sieve gives the corresponding smaller attachment as the
actual full fibre in the original pushout. -/
theorem omega_piece_pushout {P : Type} [PartialOrder P] [Finite P]
    (A U : Set P) (hU : IsLowerSet U) (hAU : A ⊆ U)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j)
    (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hb : b ≫ pY = h.membershipLabel U hU) (hj : j ≫ pY = constantLabel X 0) :
    IsPushout (h.posetMap (subposetInclusionWithin A U hAU)) a
      ((h.posetFiberMap U hU) ≫ labelFiberMap (h.membershipLabel U hU) pY 0 b hb)
      ((constantFiberIso X 0).inv ≫ labelFiberMap (constantLabel X 0) pY 0 j hj) := by
  have := s.omega U hU
  have hi : h.posetMap (subposetInclusion A) ≫ h.membershipLabel U hU =
      constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact h.posetMap_membership_zero U hU _ (fun z => hAU z.property) x
  exact ZeroFiber.omega_attachment_piece hp (h.subposetInclusionWithin_fac A U hAU)
    (h.membershipLabel U hU) pY hi hb hj (asIso (h.posetFiberMap U hU))
    (h.posetFiberMap_inclusion U hU)

omit s in
/-- The required compatible label exists for every containing sieve. -/
theorem omega_piece_label {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsLowerSet U) (hAU : A ⊆ U)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    ∃ pY : Y ⟶ StrictPoset.category (Fin 2),
      b ≫ pY = h.membershipLabel U hU ∧ j ≫ pY = constantLabel X 0 := by
  have hi : h.posetMap (subposetInclusion A) ≫ h.membershipLabel U hU =
      constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact h.posetMap_membership_zero U hU _ (fun z => hAU z.property) x
  have ha : a ≫ constantLabel X 0 = constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    rfl
  exact hp.exists_desc (h.membershipLabel U hU) (constantLabel X 0) (hi.trans ha.symm)

end PublishedPosetSieveInput
end Thomason.Construction

end

section

/-! # The two-sieve induction step for couniversal Street equivalences

All three smaller attachments have the same old target and arbitrary
attaching map. Joint labels identify their intersection in the original
pushout. The actual Street-cover theorem then glues their equivalences.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

/-- Every cobase change of a strict map is a Street weak equivalence. -/
def CouniversalStreetWeakEquivalence {A B : StrictOmegaCategory.{0}} (i : A ⟶ B) : Prop :=
  ∀ {X Y : StrictOmegaCategory.{0}} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y},
    IsPushout i a b j → h.streetWeakEquivalences j

variable [StrictColimitsInput]

/-- Stationary Gray prisms supply the greatest-new case. -/
theorem greatestNew_couniversal {P : Type} [PartialOrder P] {A : Set P}
    (R : SieveRetraction A) {x : P} (hx : SieveRetraction.GreatestNew (A := A) x)
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (kq : KanQuillenPublishedInput.{0}) :
    h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusion A)) :=
  fun hp => R.greatest_new_pushout_weakEquivalence hx h G aw kq hp

/-- Couniversality glues over two containing sieves and their intersection. -/
theorem couniversal_of_two_sieve_cover
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P]
    (A U V : Set P) (hU : IsLowerSet U) (hV : IsLowerSet V)
    (hAU : A ⊆ U) (hAV : A ⊆ V) (cover : ∀ x, x ∈ U ∨ x ∈ V)
    (wU : h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusionWithin A U hAU)))
    (wV : h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusionWithin A V hAV)))
    (wI : h.CouniversalStreetWeakEquivalence (h.posetMap
      (subposetInclusionWithin A (U ∩ V) (fun _x hx => ⟨hAU hx, hAV hx⟩)))) :
    h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusion A)) := by
  intro X Y a b j hp
  obtain ⟨p, hbp, hjp⟩ := PublishedPosetSieveInput.omega_piece_label (h := h) A U hU hAU hp
  obtain ⟨q, hbq, hjq⟩ := PublishedPosetSieveInput.omega_piece_label (h := h) A V hV hAV hp
  let z := maxLabel p q
  have hbz : b ≫ z = h.membershipLabel (U ∩ V) (hU.inter hV) := by
    change b ≫ maxLabel p q = _
    rw [maxLabel_precomp, hbp, hbq, h.membershipLabel_inter]
  have hjz : j ≫ z = constantLabel X 0 := by
    change j ≫ maxLabel p q = _
    rw [maxLabel_precomp, hjp, hjq]
    apply Hom.ext
    rfl
  let jU := (constantFiberIso X 0).inv ≫ labelFiberMap (constantLabel X 0) p 0 j hjp
  let jV := (constantFiberIso X 0).inv ≫ labelFiberMap (constantLabel X 0) q 0 j hjq
  let jZ := (constantFiberIso X 0).inv ≫ labelFiberMap (constantLabel X 0) z 0 j hjz
  have wjU : h.streetWeakEquivalences jU :=
    wU (s.omega_piece_pushout A U hU hAU hp p hbp hjp)
  have wjV : h.streetWeakEquivalences jV :=
    wV (s.omega_piece_pushout A V hV hAV hp q hbq hjq)
  have wjZ : h.streetWeakEquivalences jZ :=
    wI (s.omega_piece_pushout A (U ∩ V) (hU.inter hV)
      (fun x hx => ⟨hAU hx, hAV hx⟩) hp z hbz hjz)
  let jI := jZ ≫ (maxLabelFiberIso p q).hom
  have := kq.weakEquivalences_retracts
  have wjI : h.streetWeakEquivalences jI := by
    change realizationWeakEquivalences (h.streetNerve.map (jZ ≫ (maxLabelFiberIso p q).hom))
    rw [h.streetNerve.map_comp]
    exact realizationWeakEquivalences.comp_mem _ _ wjZ (realizationWeakEquivalences.of_isIso _)
  have hcover : ∀ y : Objects Y, p.toFun y.val = StrictPoset.identity 0 ∨
      q.toFun y.val = StrictPoset.identity 0 := by
    apply pushout_label_cover hp p q 0
    · intro x
      rcases cover (h.posetObjectsEquiv P x) with hx | hx
      · left
        exact (congrArg (fun f => f.toFun x.val) hbp).trans
          ((h.membershipLabel_object_zero_iff U hU x).mpr hx)
      · right
        exact (congrArg (fun f => f.toFun x.val) hbq).trans
          ((h.membershipLabel_object_zero_iff V hV x).mpr hx)
    · intro x
      left
      exact congrArg (fun f => f.toFun x.val) hjp
  apply h.weakEquivalence_of_sieveStreet_cover g kq p q hcover j jU jV jI
  · apply Hom.ext
    rfl
  · apply Hom.ext
    rfl
  · change (jZ ≫ (maxLabelFiberIso p q).hom) ≫ _ = j
    rw [Category.assoc, maxLabelFiberIso_inclusion]
    apply Hom.ext
    rfl
  · exact wjU
  · exact wjV
  · exact wjI

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Source isomorphisms in couniversal Street equivalences -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

/-- Renaming the attaching source does not change couniversality. -/
theorem couniversal_precompose_iso {A A' B : StrictOmegaCategory.{0}}
    (e : A' ≅ A) (i : A ⟶ B) (hi : h.CouniversalStreetWeakEquivalence i) :
    h.CouniversalStreetWeakEquivalence (e.hom ≫ i) := by
  intro X Y a b j hp
  have hp' : IsPushout i (e.inv ≫ a) b j := hp.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
  exact hi hp'

/-- Isomorphisms remain weak equivalences under arbitrary cobase change. -/
theorem couniversal_of_isIso (kq : KanQuillenPublishedInput.{0})
    {A B : StrictOmegaCategory.{0}} (i : A ⟶ B) [IsIso i] :
    h.CouniversalStreetWeakEquivalence i := by
  intro X Y a b j hp
  have := hp.isIso_inr_of_isIso
  have := kq.weakEquivalences_retracts
  exact realizationWeakEquivalences.of_isIso (h.streetNerve.map j)

variable [StrictColimitsInput]

/-- A sieve containing every object induces an isomorphism. -/
theorem posetMap_isIso_of_all {P : Type} [PartialOrder P]
    (A : Set P) (hA : ∀ x, x ∈ A) : IsIso (h.posetMap (subposetInclusion A)) := by
  let e : A ≃o P :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hA x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (h.posetMapIso e).isIso_hom

/-- Compatibility of the canonical old-source renaming with the actual inclusion. -/
theorem restrictedOldIso_fac {P : Type} [PartialOrder P]
    (A U : Set P) (hAU : A ⊆ U) :
    (h.posetMapIso (restrictedOldIso A U hAU)).hom ≫
      h.posetMap (subposetInclusion {x : U | x.val ∈ A}) =
      h.posetMap (subposetInclusionWithin A U hAU) := by
  change h.posetMap (restrictedOldIso A U hAU).toOrderEmbedding.toOrderHom ≫
    h.posetMap (subposetInclusion {x : U | x.val ∈ A}) = _
  rw [← h.posetMap_comp]
  rfl

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Full pieces of actual finite-dimensional attachments

The pushouts are in `Truncated (n + 1)`. The inclusion into
omega-categories is used only to read the cells of their full fibres.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

namespace StrictOmegaCategory

variable {n : ℕ}

/-- The truncation inclusion does not identify strict functors. -/
instance inclusion_faithful (k : ℕ) : (StrictOmegaCategory.inclusion k).Faithful where
  map_injective h := h

/-- Every ambient strict functor between truncated objects is a finite functor. -/
instance inclusion_full (k : ℕ) : (StrictOmegaCategory.inclusion k).Full where
  map_surjective f := ⟨f, rfl⟩

/-- A full endpoint fibre as an object of the original finite category. -/
def finiteLabelFiber {C : Truncated (n + 1)} (p : C ⟶ finiteInterval n) (e : Fin 2) :
    Truncated (n + 1) := (finiteLabelFiberFunctor n e).obj (Over.mk p)

/-- Restriction of a finite-dimensional strict functor to its full fibres. -/
def finiteLabelFiberMap {C D : Truncated (n + 1)}
    (p : C ⟶ finiteInterval n) (q : D ⟶ finiteInterval n) (e : Fin 2)
    (f : C ⟶ D) (hf : f ≫ q = p) : finiteLabelFiber p e ⟶ finiteLabelFiber q e :=
  labelFiberMap p q e f hf

/-- A constant label in the finite category, on all cells. -/
def finiteConstantLabel (C : Truncated (n + 1)) (e : Fin 2) : C ⟶ finiteInterval n :=
  constantLabel C.val e

/-- The constant-label fibre retains the original finite-dimensional object. -/
def finiteConstantFiberIso (C : Truncated (n + 1)) (e : Fin 2) :
    finiteLabelFiber (finiteConstantLabel C e) e ≅ C where
  hom := (constantFiberIso C.val e).hom
  inv := (constantFiberIso C.val e).inv
  hom_inv_id := (constantFiberIso C.val e).hom_inv_id
  inv_hom_id := (constantFiberIso C.val e).inv_hom_id

end StrictOmegaCategory

namespace ZeroFiber

/-- A full finite-dimensional piece containing the attaching source has
exactly the expected pushout, without assuming that inclusion preserves it. -/
theorem finite_attachment_piece {n : ℕ}
    {A B U X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {iU : A ⟶ U} {u : U ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (hiU : iU ≫ u = i)
    (pB : B ⟶ finiteInterval n) (pY : Y ⟶ finiteInterval n)
    (hi : i ≫ pB = finiteConstantLabel A 0)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = finiteConstantLabel X 0)
    (eU : U ≅ finiteLabelFiber pB 0) (hu : eU.hom ≫ labelFiberInclusion pB 0 = u) :
    IsPushout iU a
      (eU.hom ≫ finiteLabelFiberMap pB pY 0 b hb)
      ((finiteConstantFiberIso X 0).inv ≫
        finiteLabelFiberMap (finiteConstantLabel X 0) pY 0 j hj) := by
  have ha : a ≫ finiteConstantLabel X 0 = finiteConstantLabel A 0 := by apply Hom.ext; rfl
  have hpF := ZeroFiber.finite_pushout_fibers n hp (finiteConstantLabel A 0) pB
    (finiteConstantLabel X 0) pY hi ha hb hj
  apply hpF.of_iso (finiteConstantFiberIso A 0) eU.symm
    (finiteConstantFiberIso X 0) (Iso.refl _)
  · apply (cancel_mono (C := Truncated (n + 1)) eU.hom).mp
    apply Hom.ext
    funext x
    let v := (finiteLabelFiberMap (finiteConstantLabel A 0) pB 0 i hi).toFun x
    have hc : eU.hom.toFun (eU.inv.toFun v) = v :=
      congrArg (fun f => f.toFun v) eU.inv_hom_id
    apply hc.trans
    apply Subtype.ext
    change i.toFun x.val = (eU.hom.toFun (iU.toFun x.val)).val
    exact (congrArg (fun f => f.toFun x.val) hiU).symm.trans
      (congrArg (fun f => f.toFun (iU.toFun x.val)) hu).symm
  · apply Hom.ext
    rfl
  · change finiteLabelFiberMap pB pY 0 b hb = eU.inv ≫ eU.hom ≫ _
    simp
  · change finiteLabelFiberMap (finiteConstantLabel X 0) pY 0 j hj =
      (finiteConstantFiberIso X 0).hom ≫ (finiteConstantFiberIso X 0).inv ≫ _
    simp

end ZeroFiber

namespace PublishedPosetSieveInput

variable {h : NormalizedSimplexIdentities} [StrictColimitsInput]
  (s : PublishedPosetSieveInput h) {n : ℕ} (r : FiniteReflectionInput n)

include s

/-- The smaller categorified poset attachment is the actual full finite fibre. -/
theorem finite_piece_pushout {P : Type} [PartialOrder P] [Finite P]
    (A U : Set P) (hU : IsLowerSet U) (hAU : A ⊆ U)
    {X Y : Truncated.{0} (n + 1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j)
    (pY : Y ⟶ finiteInterval n)
    (hb : b ≫ pY = r.membershipLabel h U hU) (hj : j ≫ pY = finiteConstantLabel X 0) :
    IsPushout (r.reflect.map (h.posetMap (subposetInclusionWithin A U hAU))) a
      ((r.posetFiberMap h U hU) ≫ finiteLabelFiberMap (r.membershipLabel h U hU) pY 0 b hb)
      ((finiteConstantFiberIso X 0).inv ≫
        finiteLabelFiberMap (finiteConstantLabel X 0) pY 0 j hj) := by
  let eU : (r.categorification h).obj (nerve U) ≅
      finiteLabelFiber (r.membershipLabel h U hU) 0 :=
    @asIso (Truncated (n + 1)) _ _ _ (r.posetFiberMap h U hU) (s.finite n r U hU)
  have hi : r.reflect.map (h.posetMap (subposetInclusion A)) ≫ r.membershipLabel h U hU =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact r.posetMap_membership_zero h U hU _ (fun z => hAU z.property) x
  have hiU : r.reflect.map (h.posetMap (subposetInclusionWithin A U hAU)) ≫
      r.reflect.map (h.posetMap (subposetInclusion U)) =
      r.reflect.map (h.posetMap (subposetInclusion A)) := by
    rw [← r.reflect.map_comp, h.subposetInclusionWithin_fac]
  have hu : r.posetFiberMap h U hU ≫ labelFiberInclusion (r.membershipLabel h U hU) 0 =
      r.reflect.map (h.posetMap (subposetInclusion U)) := by apply Hom.ext; rfl
  exact ZeroFiber.finite_attachment_piece hp hiU (r.membershipLabel h U hU) pY hi hb hj
    eU hu

omit s in
/-- Construct the compatible label using the original finite pushout. -/
theorem finite_piece_label {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsLowerSet U) (hAU : A ⊆ U)
    {X Y : Truncated.{0} (n + 1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    ∃ pY : Y ⟶ finiteInterval n,
      b ≫ pY = r.membershipLabel h U hU ∧ j ≫ pY = finiteConstantLabel X 0 := by
  have hi : r.reflect.map (h.posetMap (subposetInclusion A)) ≫ r.membershipLabel h U hU =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact r.posetMap_membership_zero h U hU _ (fun z => hAU z.property) x
  have ha : a ≫ finiteConstantLabel X 0 =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 0 := by apply Hom.ext; rfl
  exact hp.exists_desc (r.membershipLabel h U hU) (finiteConstantLabel X 0) (hi.trans ha.symm)

end PublishedPosetSieveInput
end Thomason.Construction

end

section

/-! # Couniversality gluing in every positive finite dimension -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

namespace NormalizedSimplexIdentities

/-- Cobase changes in the actual finite category are Street weak equivalences. -/
def FiniteCouniversalStreetWeakEquivalence (h : NormalizedSimplexIdentities) (n : ℕ)
    {A B : Truncated.{0} (n + 1)} (i : A ⟶ B) : Prop :=
  ∀ {X Y : Truncated.{0} (n + 1)} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y},
    IsPushout i a b j → h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map j)

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The finite stationary Gray prisms give the greatest-new base case. -/
theorem greatestNew_couniversal {P : Type} [PartialOrder P] {A : Set P}
    (R : SieveRetraction A) {x : P} (hx : SieveRetraction.GreatestNew (A := A) x)
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (aw : SimplexComplex.AlexanderWhitneyInput h) (kq : KanQuillenPublishedInput.{0}) :
    h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusion A))) :=
  fun hp => R.finite_greatest_new_pushout_weakEquivalence hx h G t r aw kq hp

/-- The two-sieve induction step uses finite pushouts and ambient Street covers. -/
theorem couniversal_of_two_sieve_cover
    (s : PublishedPosetSieveInput h)
    (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P]
    (A U V : Set P) (hU : IsLowerSet U) (hV : IsLowerSet V)
    (hAU : A ⊆ U) (hAV : A ⊆ V) (cover : ∀ x, x ∈ U ∨ x ∈ V)
    (wU : h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusionWithin A U hAU))))
    (wV : h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusionWithin A V hAV))))
    (wI : h.FiniteCouniversalStreetWeakEquivalence n (r.reflect.map (h.posetMap
      (subposetInclusionWithin A (U ∩ V) (fun _x hx => ⟨hAU hx, hAV hx⟩))))) :
    h.FiniteCouniversalStreetWeakEquivalence n
      (r.reflect.map (h.posetMap (subposetInclusion A))) := by
  intro X Y a b j hp
  obtain ⟨p, hbp, hjp⟩ := PublishedPosetSieveInput.finite_piece_label r A U hU hAU hp
  obtain ⟨q, hbq, hjq⟩ := PublishedPosetSieveInput.finite_piece_label r A V hV hAV hp
  let z : Y ⟶ finiteInterval n := maxLabel p q
  let b' : ((r.categorification h).obj (nerve P)).val ⟶ Y.val := b
  let j' : X.val ⟶ Y.val := j
  let p' : Y.val ⟶ StrictPoset.category (Fin 2) := p
  let q' : Y.val ⟶ StrictPoset.category (Fin 2) := q
  have hbz : b ≫ z = r.membershipLabel h (U ∩ V) (hU.inter hV) :=
    (maxLabel_precomp p' q' b').trans
      ((congrArg₂ (fun u v => maxLabel u v) hbp hbq).trans
        (r.membershipLabel_inter h U V hU hV))
  have hjz : j ≫ z = finiteConstantLabel X 0 := by
    have he := (maxLabel_precomp p' q' j').trans
      (congrArg₂ (fun u v => maxLabel u v) hjp hjq)
    exact he.trans (by apply Hom.ext; rfl)
  let jU := (finiteConstantFiberIso X 0).inv ≫
    finiteLabelFiberMap (finiteConstantLabel X 0) p 0 j hjp
  let jV := (finiteConstantFiberIso X 0).inv ≫
    finiteLabelFiberMap (finiteConstantLabel X 0) q 0 j hjq
  let jZ := (finiteConstantFiberIso X 0).inv ≫
    finiteLabelFiberMap (finiteConstantLabel X 0) z 0 j hjz
  have wjU : h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map jU) :=
    wU (s.finite_piece_pushout r A U hU hAU hp p hbp hjp)
  have wjV : h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map jV) :=
    wV (s.finite_piece_pushout r A V hV hAV hp q hbq hjq)
  have wjZ : h.streetWeakEquivalences ((StrictOmegaCategory.inclusion (n + 1)).map jZ) :=
    wI (s.finite_piece_pushout r A (U ∩ V) (hU.inter hV)
      (fun x hx => ⟨hAU hx, hAV hx⟩) hp z hbz hjz)
  let jZ' : X.val ⟶ labelFiber z 0 := jZ
  let jI := jZ' ≫ (maxLabelFiberIso p' q').hom
  have := kq.weakEquivalences_retracts
  have wjI : h.streetWeakEquivalences jI := by
    have hwz : realizationWeakEquivalences (h.streetNerve.map jZ') := wjZ
    have hw := realizationWeakEquivalences.comp_mem _ _ hwz
      (realizationWeakEquivalences.of_isIso (h.streetNerve.map (maxLabelFiberIso p' q').hom))
    exact (congrArg (fun f => realizationWeakEquivalences.{0} f)
      (h.streetNerve.map_comp jZ' (maxLabelFiberIso p' q').hom)).mpr hw
  have hcover : ∀ y : Objects Y.val, p.toFun y.val = StrictPoset.identity 0 ∨
      q.toFun y.val = StrictPoset.identity 0 := by
    apply finite_pushout_label_cover hp p q 0
    · intro x
      rcases cover (r.posetObjectsEquiv h P x) with hx | hx
      · left
        exact (congrArg (fun f => f.toFun x.val) hbp).trans
          ((r.membershipLabel_object_zero_iff h U hU x).mpr hx)
      · right
        exact (congrArg (fun f => f.toFun x.val) hbq).trans
          ((r.membershipLabel_object_zero_iff h V hV x).mpr hx)
    · intro x
      left
      exact congrArg (fun f => f.toFun x.val) hjp
  apply h.weakEquivalence_of_sieveStreet_cover g kq p q hcover
    ((StrictOmegaCategory.inclusion (n + 1)).map j) ((StrictOmegaCategory.inclusion (n + 1)).map jU)
    ((StrictOmegaCategory.inclusion (n + 1)).map jV) jI
  · apply Hom.ext
    rfl
  · apply Hom.ext
    rfl
  · apply Hom.ext
    rfl
  · exact wjU
  · exact wjV
  · exact wjI

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # Full pieces of finite attachments at either endpoint -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

namespace EndpointFiber

/-- A full finite-dimensional piece containing the attaching source has
exactly the expected pushout, without assuming that inclusion preserves it. -/
theorem finite_attachment_piece (e : Fin 2) {n : ℕ}
    {A B U X Y : Truncated.{0} (n + 1)}
    {i : A ⟶ B} {iU : A ⟶ U} {u : U ⟶ B}
    {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (hiU : iU ≫ u = i)
    (pB : B ⟶ finiteInterval n) (pY : Y ⟶ finiteInterval n)
    (hi : i ≫ pB = finiteConstantLabel A e)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = finiteConstantLabel X e)
    (eU : U ≅ finiteLabelFiber pB e) (hu : eU.hom ≫ labelFiberInclusion pB e = u) :
    IsPushout iU a
      (eU.hom ≫ finiteLabelFiberMap pB pY e b hb)
      ((finiteConstantFiberIso X e).inv ≫
        finiteLabelFiberMap (finiteConstantLabel X e) pY e j hj) := by
  have ha : a ≫ finiteConstantLabel X e = finiteConstantLabel A e := by apply Hom.ext; rfl
  have hpF := EndpointFiber.finite_pushout_fibers n e hp (finiteConstantLabel A e) pB
    (finiteConstantLabel X e) pY hi ha hb hj
  apply hpF.of_iso (finiteConstantFiberIso A e) eU.symm
    (finiteConstantFiberIso X e) (Iso.refl _)
  · apply (cancel_mono (C := Truncated (n + 1)) eU.hom).mp
    apply Hom.ext
    funext x
    let v := (finiteLabelFiberMap (finiteConstantLabel A e) pB e i hi).toFun x
    have hc : eU.hom.toFun (eU.inv.toFun v) = v :=
      congrArg (fun f => f.toFun v) eU.inv_hom_id
    apply hc.trans
    apply Subtype.ext
    change i.toFun x.val = (eU.hom.toFun (iU.toFun x.val)).val
    exact (congrArg (fun f => f.toFun x.val) hiU).symm.trans
      (congrArg (fun f => f.toFun (iU.toFun x.val)) hu).symm
  · apply Hom.ext
    rfl
  · change finiteLabelFiberMap pB pY e b hb = eU.inv ≫ eU.hom ≫ _
    simp
  · change finiteLabelFiberMap (finiteConstantLabel X e) pY e j hj =
      (finiteConstantFiberIso X e).hom ≫ (finiteConstantFiberIso X e).inv ≫ _
    simp

end EndpointFiber
end Thomason.Construction

end

section

/-! # Disjoint full fibres of finite-dimensional attachments -/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

def finiteLabelFiberInclusion {n : ℕ} {C : Truncated.{0} (n+1)}
    (p : C ⟶ finiteInterval n) (e : Fin 2) : finiteLabelFiber p e ⟶ C :=
  labelFiberInclusion p e

theorem finiteLabelFiberMap_inclusion {n : ℕ} {C D : Truncated.{0} (n+1)}
    (p : C ⟶ finiteInterval n) (q : D ⟶ finiteInterval n) (e : Fin 2)
    (f : C ⟶ D) (hf : f ≫ q = p) :
    finiteLabelFiberMap p q e f hf ≫ finiteLabelFiberInclusion q e =
      finiteLabelFiberInclusion p e ≫ f := by apply Hom.ext; rfl

end Thomason.Construction.StrictOmegaCategory

namespace Thomason.Construction.EndpointFiber

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

theorem finite_piece_inclusion {n : ℕ} {B U Y : Truncated.{0} (n+1)}
    (e : Fin 2) (pB : B ⟶ finiteInterval n) (pY : Y ⟶ finiteInterval n)
    (b : B ⟶ Y) (hb : b ≫ pY = pB) (u : U ⟶ B)
    (eU : U ≅ finiteLabelFiber pB e) (hu : eU.hom ≫ finiteLabelFiberInclusion pB e = u) :
    (eU.hom ≫ finiteLabelFiberMap pB pY e b hb) ≫ finiteLabelFiberInclusion pY e = u ≫ b :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => eU.hom ≫ k) (finiteLabelFiberMap_inclusion pB pY e b hb)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ b) hu)))

/-- The full fibre away from the old constant label is unchanged by the
actual finite-dimensional pushout. -/
theorem finite_attachment_complement_iso {n : ℕ} (e d : Fin 2) (hed : d ≠ e)
    {A B X Y : Truncated.{0} (n+1)}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout i a b j) (pB : B ⟶ finiteInterval n) (pY : Y ⟶ finiteInterval n)
    (hi : i ≫ pB = finiteConstantLabel A d)
    (hb : b ≫ pY = pB) (hj : j ≫ pY = finiteConstantLabel X d) :
    IsIso (finiteLabelFiberMap pB pY e b hb) := by
  have ha : a ≫ finiteConstantLabel X d = finiteConstantLabel A d := by apply Hom.ext; rfl
  have hpF := finite_pushout_fibers n e hp (finiteConstantLabel A d) pB
    (finiteConstantLabel X d) pY hi ha hb hj
  let : IsEmpty (finiteLabelFiber (finiteConstantLabel A d) e).val :=
    constantFiber_empty A.val d e hed
  let : IsEmpty (finiteLabelFiber (finiteConstantLabel X d) e).val :=
    constantFiber_empty X.val d e hed
  let f : finiteLabelFiber (finiteConstantLabel A d) e ⟶
      finiteLabelFiber (finiteConstantLabel X d) e :=
    finiteLabelFiberMap (finiteConstantLabel A d) (finiteConstantLabel X d) e a ha
  let g : finiteLabelFiber (finiteConstantLabel X d) e ⟶
      finiteLabelFiber (finiteConstantLabel A d) e :=
    { toFun := fun x => isEmptyElim x
      map_face := by intro a n x; exact isEmptyElim x
      map_comp := by intro n x y h h'; exact False.elim (isEmptyElim x) }
  have : IsIso f := ⟨⟨g,
    by apply Hom.ext; funext x; exact isEmptyElim x,
    by apply Hom.ext; funext x; exact isEmptyElim x⟩⟩
  let : IsIso ((finiteLabelFiberFunctor n e).map
      (Over.homMk a ha : Over.mk (finiteConstantLabel A d) ⟶ Over.mk (finiteConstantLabel X d))) :=
    inferInstanceAs (IsIso f)
  exact hpF.isIso_inl_of_isIso

end Thomason.Construction.EndpointFiber

end

end OAI
