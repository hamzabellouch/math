import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.SieveFiberPresentation
import OAI.CategoryTheory.Thomason.Strict.StrictPosetWeakEquivalences
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Transfer.FiniteEmptyAttachmentFibers
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import Mathlib.CategoryTheory.Limits.Types.Pushouts

namespace OAI

section

/-! # Monic pushout comparisons from exact image intersections -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

/-- A map out of a simplicial pushout is monic when the two monic image
pieces intersect in precisely the image of the common source. -/
theorem simplicial_pushout_comparison_mono
    {A B C D X : SSet.{0}} {i : A ⟶ B} {j : A ⟶ C}
    {u : B ⟶ D} {v : C ⟶ D} (hp : IsPushout i j u v)
    (k : D ⟶ X) (b : B ⟶ X) (c : C ⟶ X)
    [Mono b] [Mono c] [Mono (i ≫ b)]
    (hb : u ≫ k = b) (hc : v ≫ k = c)
    (hinter : SSet.Subcomplex.range (i ≫ b) =
      SSet.Subcomplex.range b ⊓ SSet.Subcomplex.range c) : Mono k := by
  have hw : i ≫ b = j ≫ c := by rw [← hb, ← hc, ← Category.assoc, hp.w, Category.assoc]
  rw [NatTrans.mono_iff_mono_app]
  intro d
  have hi : Function.Injective ((i ≫ b).app d) :=
    (CategoryTheory.mono_iff_injective _).mp (inferInstance : Mono ((i ≫ b).app d))
  have hbi : Function.Injective (b.app d) :=
    (CategoryTheory.mono_iff_injective _).mp (inferInstance : Mono (b.app d))
  have hci : Function.Injective (c.app d) :=
    (CategoryTheory.mono_iff_injective _).mp (inferInstance : Mono (c.app d))
  have hpb : IsPullback (i.app d) (j.app d) (b.app d) (c.app d) := by
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨NatTrans.congr_app hw d, ?_, ?_⟩
    · intro x y h
      apply hi
      change b.app d (i.app d x) = b.app d (i.app d y)
      rw [h.1]
    · intro x y h
      have hx : b.app d x ∈ (SSet.Subcomplex.range (i ≫ b)).obj d := by
        rw [hinter]
        exact ⟨⟨x, rfl⟩, ⟨y, h.symm⟩⟩
      obtain ⟨a, ha⟩ := hx
      refine ⟨a, hbi ha, hci ?_⟩
      have he := congrArg (fun f => f.app d a) hw
      exact he.symm.trans (ha.trans h)
  apply Types.mono_of_isPushout_of_isPullback
    (hp.map (SSet.evaluation.obj d)) hpb (NatTrans.congr_app hb d) (NatTrans.congr_app hc d)
  intro x y _ _ h
  exact hci h

/-- The actual image of any pushout comparison is the union of its two
pieces, with no injectivity assumption. -/
theorem simplicial_pushout_comparison_range
    {A B C D X : SSet.{0}} {i : A ⟶ B} {j : A ⟶ C}
    {u : B ⟶ D} {v : C ⟶ D} (hp : IsPushout i j u v)
    (k : D ⟶ X) (b : B ⟶ X) (c : C ⟶ X)
    (hb : u ≫ k = b) (hc : v ≫ k = c) :
    SSet.Subcomplex.range k = SSet.Subcomplex.range b ⊔ SSet.Subcomplex.range c := by
  ext d x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ :=
      Types.eq_or_eq_of_isPushout (hp.map (SSet.evaluation.obj d)) z
    · exact Or.inl ⟨y, (congrArg (fun f => f.app d y) hb).symm⟩
    · exact Or.inr ⟨y, (congrArg (fun f => f.app d y) hc).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨u.app d y, congrArg (fun f => f.app d y) hb⟩
    · exact ⟨v.app d y, congrArg (fun f => f.app d y) hc⟩

end Thomason.Construction

end

section

/-! # Street nerves of two-cosieve decompositions of finite posets

The constructed cosieve comparison identifies each actual categorified inclusion
with a full labelled fibre. The explicit Street cover theorem and the
range criterion then give the required simplicial pushout, without any
assumption that the Street nerve preserves arbitrary colimits.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

theorem street_endpoint_factor_mono {X C : StrictOmegaCategory.{0}}
    (e : Fin 2) (p : C ⟶ StrictPoset.category (Fin 2)) (f : X ⟶ labelFiber p e) [IsIso f] :
    Mono (h.streetNerve.map (f ≫ labelFiberInclusion p e)) := by
  rw [h.streetNerve.map_comp]
  infer_instance

theorem street_endpoint_factor_range {X C : StrictOmegaCategory.{0}}
    (e : Fin 2) (p : C ⟶ StrictPoset.category (Fin 2)) (f : X ⟶ labelFiber p e) [IsIso f] :
    SSet.Subcomplex.range (h.streetNerve.map (f ≫ labelFiberInclusion p e)) =
      h.fiberStreetSubcomplex p e := by
  rw [h.streetNerve.map_comp, SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]
  exact (h.fullStreetSubcomplex_eq_range _ _).symm

theorem fiberStreetSubcomplex_min {C : StrictOmegaCategory.{0}}
    (p q : C ⟶ StrictPoset.category (Fin 2)) :
    h.fiberStreetSubcomplex (minLabel p q) 1 =
      h.fiberStreetSubcomplex p 1 ⊓ h.fiberStreetSubcomplex q 1 := by
  ext m f
  change (∀ x, C.FullCell {y | (minLabel p q).toFun y = StrictPoset.identity 1} (f.toFun x)) ↔
    (∀ x, C.FullCell {y | p.toFun y = StrictPoset.identity 1} (f.toFun x)) ∧
    (∀ x, C.FullCell {y | q.toFun y = StrictPoset.identity 1} (f.toFun x))
  simp only [FullCell, Set.mem_ofPred_eq, minLabel_one_iff]
  constructor
  · intro hf
    exact ⟨fun x => ⟨(hf x).1.1, (hf x).2.1⟩, fun x => ⟨(hf x).1.2, (hf x).2.2⟩⟩
  · rintro ⟨hp, hq⟩ x
    exact ⟨⟨(hp x).1, (hq x).1⟩, ⟨(hp x).2, (hq x).2⟩⟩

variable [StrictColimitsInput]

/-- The image of the original Street map is exactly its full labelled fibre. -/
theorem posetCosieveStreet_range {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A) :
    SSet.Subcomplex.range (h.streetNerve.map (h.posetMap (subposetInclusion A))) =
      h.fiberStreetSubcomplex (h.membershipLabel Aᶜ hA.compl) 1 := by
  have : IsIso (h.cosievePosetFiberMap A hA) := (h.posetCosieveIso A hA).isIso_hom
  rw [← h.cosievePosetFiberMap_inclusion A hA, h.streetNerve.map_comp,
    SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]
  exact (h.fullStreetSubcomplex_eq_range _ _).symm

/-- Full cosieve inclusions have monomorphic actual Street nerves. -/
theorem posetCosieve_nerve_mono
    {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A) :
    Mono (h.streetNerve.map (h.posetMap (subposetInclusion A))) := by
  have : IsIso (h.cosievePosetFiberMap A hA) := (h.posetCosieveIso A hA).isIso_hom
  rw [← h.cosievePosetFiberMap_inclusion A hA]
  exact h.street_endpoint_factor_mono 1 _ _

/-- The actual composite N c takes this two-cosieve square to a pushout. -/
theorem street_cosieve_maps_isPushout
    {P : Type} [PartialOrder P]
    (A B : Set P) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hcover : ∀ x, x ∈ A ∨ x ∈ B) :
    IsPushout ((h.categorification ⋙ h.streetNerve).map
        (nerveMap (interLeft A B).monotone.functor))
      ((h.categorification ⋙ h.streetNerve).map
        (nerveMap (interRight A B).monotone.functor))
      (h.streetNerve.map (h.posetMap (subposetInclusion A)))
      (h.streetNerve.map (h.posetMap (subposetInclusion B))) := by
  let F := h.categorification ⋙ h.streetNerve
  have hi : F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have hj : F.map (nerveMap (interRight A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion B).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have : Mono (F.map (nerveMap (subposetInclusion A).monotone.functor)) :=
    h.posetCosieve_nerve_mono A hA
  have : Mono (F.map (nerveMap (subposetInclusion B).monotone.functor)) :=
    h.posetCosieve_nerve_mono B hB
  have : Mono (F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor)) :=
    h.posetCosieve_nerve_mono (A ∩ B) (hA.inter hB)
  have : Mono (F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor)) := by rwa [hi]
  have hrange (S : Set P) (hS : IsUpperSet S) :
      SSet.Subcomplex.range (F.map (nerveMap (subposetInclusion S).monotone.functor)) =
        h.fiberStreetSubcomplex (h.membershipLabel Sᶜ hS.compl) 1 := h.posetCosieveStreet_range S hS
  apply simplicial_isPushout_of_ranges _ _ _ _ (hi.trans hj.symm)
  · rw [hrange A hA, hrange B hB]
    apply h.cosieve_street_cover
    intro x
    exact (hcover (h.posetObjectsEquiv P x)).imp
      ((h.cosieveMembershipLabel_object A hA x).mpr)
      ((h.cosieveMembershipLabel_object B hB x).mpr)
  · rw [hi, hrange (A ∩ B) (hA.inter hB), hrange A hA, hrange B hB,
      ← h.cosieveMembershipLabel_inter A B hA hB, h.fiberStreetSubcomplex_min]

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # The actual full cosieve pieces of a poset attachment -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- A containing sieve gives the corresponding smaller attachment as the
actual full fibre in the original pushout. -/
theorem cosieve_piece_pushout {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : A ⊆ U)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j)
    (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hb : b ≫ pY = h.membershipLabel Uᶜ hU.compl) (hj : j ≫ pY = constantLabel X 1) :
    IsPushout (h.posetMap (subposetInclusionWithin A U hAU)) a
      ((h.cosievePosetFiberMap U hU) ≫ labelFiberMap (h.membershipLabel Uᶜ hU.compl) pY 1 b hb)
      ((constantFiberIso X 1).inv ≫ labelFiberMap (constantLabel X 1) pY 1 j hj) := by
  have hi : h.posetMap (subposetInclusion A) ≫ h.membershipLabel Uᶜ hU.compl =
      constantLabel (h.categorification.obj (nerve A)) 1 := by
    apply Hom.ext
    funext x
    exact h.posetMap_cosieveMembership_one U hU _ (fun z => hAU z.property) x
  exact EndpointFiber.omega_attachment_piece 1 hp (h.subposetInclusionWithin_fac A U hAU)
    (h.membershipLabel Uᶜ hU.compl) pY hi hb hj (h.posetCosieveIso U hU)
    (h.cosievePosetFiberMap_inclusion U hU)

/-- The required compatible label exists for every containing sieve. -/
theorem cosieve_piece_label {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : A ⊆ U)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    ∃ pY : Y ⟶ StrictPoset.category (Fin 2),
      b ≫ pY = h.membershipLabel Uᶜ hU.compl ∧ j ≫ pY = constantLabel X 1 := by
  have hi : h.posetMap (subposetInclusion A) ≫ h.membershipLabel Uᶜ hU.compl =
      constantLabel (h.categorification.obj (nerve A)) 1 := by
    apply Hom.ext
    funext x
    exact h.posetMap_cosieveMembership_one U hU _ (fun z => hAU z.property) x
  have ha : a ≫ constantLabel X 1 = constantLabel (h.categorification.obj (nerve A)) 1 := by
    apply Hom.ext
    rfl
  exact hp.exists_desc (h.membershipLabel Uᶜ hU.compl) (constantLabel X 1) (hi.trans ha.symm)

/-- A cosieve disjoint from the old part extends by the constant zero label. -/
theorem disjoint_cosieve_piece_label {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : ∀ x ∈ A, x ∉ U)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    ∃ pY : Y ⟶ StrictPoset.category (Fin 2),
      b ≫ pY = h.membershipLabel Uᶜ hU.compl ∧ j ≫ pY = constantLabel X 0 := by
  have hi : h.posetMap (subposetInclusion A) ≫ h.membershipLabel Uᶜ hU.compl =
      constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact h.posetMap_membership_zero Uᶜ hU.compl _ (fun z => hAU z.val z.property) x
  have ha : a ≫ constantLabel X 0 = constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    rfl
  exact hp.exists_desc (h.membershipLabel Uᶜ hU.compl) (constantLabel X 0) (hi.trans ha.symm)

/-- The original categorified disjoint cosieve is exactly the post-attachment
full one fibre; this retains the original map into the pushout. -/
theorem disjoint_cosieve_piece_iso {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : ∀ x ∈ A, x ∉ U)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j)
    (pY : Y ⟶ StrictPoset.category (Fin 2))
    (hb : b ≫ pY = h.membershipLabel Uᶜ hU.compl) (hj : j ≫ pY = constantLabel X 0) :
    IsIso (h.cosievePosetFiberMap U hU ≫
      labelFiberMap (h.membershipLabel Uᶜ hU.compl) pY 1 b hb) := by
  have hi : h.posetMap (subposetInclusion A) ≫ h.membershipLabel Uᶜ hU.compl =
      constantLabel (h.categorification.obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact h.posetMap_membership_zero Uᶜ hU.compl _ (fun z => hAU z.val z.property) x
  have := EndpointFiber.omega_attachment_complement_iso 1 0 (by decide) hp
    (h.membershipLabel Uᶜ hU.compl) pY hi hb hj
  have : IsIso (h.cosievePosetFiberMap U hU) := (h.posetCosieveIso U hU).isIso_hom
  infer_instance

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # Street pushouts from full cosieve fibres after attachment -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

/-- Identify a square with a cover by two full cosieves and their full
intersection. No preservation of arbitrary pushouts by Street is assumed. -/
theorem street_cosieve_fiber_pushout
    {I B C D : StrictOmegaCategory.{0}}
    {i : I ⟶ B} {j : I ⟶ C} {b : B ⟶ D} {c : C ⟶ D}
    (p q : D ⟶ StrictPoset.category (Fin 2))
    (cover : ∀ x : Objects D, p.toFun x.val = StrictPoset.identity 1 ∨
      q.toFun x.val = StrictPoset.identity 1)
    (eB : B ≅ labelFiber p 1) (eC : C ≅ labelFiber q 1)
    (eI : I ≅ labelFiber (minLabel p q) 1)
    (hb : eB.hom ≫ labelFiberInclusion p 1 = b)
    (hc : eC.hom ≫ labelFiberInclusion q 1 = c)
    (hi : i ≫ b = eI.hom ≫ labelFiberInclusion (minLabel p q) 1)
    (hw : i ≫ b = j ≫ c) :
    IsPushout (h.streetNerve.map i) (h.streetNerve.map j)
      (h.streetNerve.map b) (h.streetNerve.map c) := by
  have : Mono (h.streetNerve.map b) := by
    rw [← hb]
    exact h.street_endpoint_factor_mono 1 p eB.hom
  have : Mono (h.streetNerve.map c) := by
    rw [← hc]
    exact h.street_endpoint_factor_mono 1 q eC.hom
  have : Mono (h.streetNerve.map i ≫ h.streetNerve.map b) := by
    rw [← h.streetNerve.map_comp, hi]
    exact h.street_endpoint_factor_mono 1 (minLabel p q) eI.hom
  apply simplicial_isPushout_of_ranges _ _ _ _
    ((h.streetNerve.map_comp i b).symm.trans
      ((congrArg h.streetNerve.map hw).trans (h.streetNerve.map_comp j c)))
  · rw [← hb, ← hc, h.street_endpoint_factor_range 1 p eB.hom,
      h.street_endpoint_factor_range 1 q eC.hom]
    exact h.cosieve_street_cover p q cover
  · rw [← h.streetNerve.map_comp, hi, ← hb, ← hc,
      h.street_endpoint_factor_range 1 (minLabel p q) eI.hom,
      h.street_endpoint_factor_range 1 p eB.hom,
      h.street_endpoint_factor_range 1 q eC.hom, h.fiberStreetSubcomplex_min]

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # The Street cover of the actual attaching pushout

The two cosieves are a containing cosieve and one disjoint from the old
part. Their intersection remains the original categorified intersection.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The actual post-attachment cover is a simplicial pushout. In particular,
the attaching functor is allowed to identify arbitrary old cells. -/
theorem cosieve_attachment_street_pushout
    {P : Type} [PartialOrder P] (A Z C : Set P)
    (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hAC : ∀ x ∈ A, x ∉ C) (cover : ∀ x, x ∈ Z ∨ x ∈ C)
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j)
    (p q : Y ⟶ StrictPoset.category (Fin 2))
    (hbp : b ≫ p = h.membershipLabel Zᶜ hZ.compl)
    (hjp : j ≫ p = constantLabel X 1)
    (hbq : b ≫ q = h.membershipLabel Cᶜ hC.compl)
    (hjq : j ≫ q = constantLabel X 0) :
    IsPushout
      (h.streetNerve.map (h.posetMap (interLeft Z C) ≫
        (h.cosievePosetFiberMap Z hZ ≫
          labelFiberMap (h.membershipLabel Zᶜ hZ.compl) p 1 b hbp)))
      (h.streetNerve.map (h.posetMap (interRight Z C)))
      (h.streetNerve.map (labelFiberInclusion p 1))
      (h.streetNerve.map (h.posetMap (subposetInclusion C) ≫ b)) := by
  let z := minLabel p q
  have hbz : b ≫ z = h.membershipLabel (Z ∩ C)ᶜ (hZ.inter hC).compl := by
    change b ≫ minLabel p q = _
    rw [minLabel_precomp, hbp, hbq, h.cosieveMembershipLabel_inter Z C hZ hC]
  have hjz : j ≫ z = constantLabel X 0 := by
    change j ≫ minLabel p q = _
    rw [minLabel_precomp, hjp, hjq]
    apply Hom.ext
    rfl
  let fC := h.cosievePosetFiberMap C hC ≫
    labelFiberMap (h.membershipLabel Cᶜ hC.compl) q 1 b hbq
  let fI := h.cosievePosetFiberMap (Z ∩ C) (hZ.inter hC) ≫
    labelFiberMap (h.membershipLabel (Z ∩ C)ᶜ (hZ.inter hC).compl) z 1 b hbz
  have : IsIso fC := h.disjoint_cosieve_piece_iso A C hC hAC hp q hbq hjq
  have : IsIso fI := h.disjoint_cosieve_piece_iso A (Z ∩ C) (hZ.inter hC)
    (fun x hx hxc => hAC x hx hxc.2) hp z hbz hjz
  have hfC : fC ≫ labelFiberInclusion q 1 = h.posetMap (subposetInclusion C) ≫ b := by
    apply Hom.ext
    rfl
  have hfI : fI ≫ labelFiberInclusion z 1 = h.posetMap (subposetInclusion (Z ∩ C)) ≫ b := by
    apply Hom.ext
    rfl
  let bZ := h.cosievePosetFiberMap Z hZ ≫
    labelFiberMap (h.membershipLabel Zᶜ hZ.compl) p 1 b hbp
  have hbZ : bZ ≫ labelFiberInclusion p 1 = h.posetMap (subposetInclusion Z) ≫ b := by
    apply Hom.ext
    rfl
  have hi : (h.posetMap (interLeft Z C) ≫ bZ) ≫ labelFiberInclusion p 1 =
      fI ≫ labelFiberInclusion z 1 := by
    rw [Category.assoc, hbZ, ← Category.assoc, ← h.posetMap_comp, hfI]
    rfl
  have hw : (h.posetMap (interLeft Z C) ≫ bZ) ≫ labelFiberInclusion p 1 =
      h.posetMap (interRight Z C) ≫ (h.posetMap (subposetInclusion C) ≫ b) := by
    rw [hi, hfI, ← Category.assoc, ← h.posetMap_comp]
    rfl
  have hcover : ∀ y : Objects Y, p.toFun y.val = StrictPoset.identity 1 ∨
      q.toFun y.val = StrictPoset.identity 1 := by
    apply pushout_label_cover hp p q 1
    · intro x
      rcases cover (h.posetObjectsEquiv P x) with hx | hx
      · left
        exact (congrArg (fun f => f.toFun x.val) hbp).trans
          ((h.cosieveMembershipLabel_object Z hZ x).mpr hx)
      · right
        exact (congrArg (fun f => f.toFun x.val) hbq).trans
          ((h.cosieveMembershipLabel_object C hC x).mpr hx)
    · intro x
      left
      exact congrArg (fun f => f.toFun x.val) hjp
  exact h.street_cosieve_fiber_pushout p q hcover (Iso.refl _) (asIso fC) (asIso fI)
    (by simp) hfC hi hw

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # The actual comparison for a sieve retracting on a containing cosieve -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Extend couniversality on a containing cosieve to the nerve-pushout
comparison on the original ambient poset. -/
theorem containing_cosieve_attachment_comparison
    (g : PublishedSimplicialGluingInput) (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] (A Z C : Set P)
    (hZ : IsUpperSet Z) (hC : IsUpperSet C) (hAZ : A ⊆ Z)
    (hAC : ∀ x ∈ A, x ∉ C) (cover : ∀ x, x ∈ Z ∨ x ∈ C)
    (wZ : h.CouniversalStreetWeakEquivalence (h.posetMap (subposetInclusionWithin A Z hAZ)))
    [Mono (h.streetNerve.map (h.posetMap (subposetInclusionWithin A Z hAZ)))]
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    realizationWeakEquivalences (nervePushoutComparison h.streetNerve hp) := by
  obtain ⟨p, hbp, hjp⟩ := h.cosieve_piece_label A Z hZ hAZ hp
  obtain ⟨q, hbq, hjq⟩ := h.disjoint_cosieve_piece_label A C hC hAC hp
  let d := h.cosievePosetFiberMap Z hZ ≫
    labelFiberMap (h.membershipLabel Zᶜ hZ.compl) p 1 b hbp
  let e := (constantFiberIso X 1).inv ≫ labelFiberMap (constantLabel X 1) p 1 j hjp
  have hz : IsPushout (h.posetMap (subposetInclusionWithin A Z hAZ)) a d e :=
    h.cosieve_piece_pushout A Z hZ hAZ hp p hbp hjp
  have hi : IsPushout (h.posetMap (subposetInclusionWithin A Z hAZ))
      (𝟙 _) (𝟙 _) (h.posetMap (subposetInclusionWithin A Z hAZ)) := IsPushout.of_id_snd
  have wz := nervePushoutComparison_weakEquivalence h.streetNerve kq hz (wZ hi) (wZ hz)
  have hk : d ≫ labelFiberInclusion p 1 = h.posetMap (subposetInclusion Z) ≫ b := by
    apply Hom.ext
    rfl
  have he : e ≫ labelFiberInclusion p 1 = j := by
    apply Hom.ext
    rfl
  have : Mono (h.streetNerve.map (h.posetMap (interRight Z C)) ≫
      h.streetNerve.map (h.posetMap (subposetInclusion C))) := by
    rw [← h.streetNerve.map_comp, ← h.posetMap_comp]
    exact h.posetCosieve_nerve_mono (Z ∩ C) (hZ.inter hC)
  have : Mono (h.streetNerve.map (h.posetMap (interRight Z C))) :=
    mono_of_mono _ (h.streetNerve.map (h.posetMap (subposetInclusion C)))
  have : Mono ((h.categorification ⋙ h.streetNerve).map
      (nerveMap (interRight Z C).monotone.functor)) := by
    change Mono (h.streetNerve.map (h.posetMap (interRight Z C)))
    infer_instance
  have hp' : IsPushout (h.posetMap (subposetInclusionWithin A Z hAZ) ≫
      h.posetMap (subposetInclusion Z)) a b j := by
    rw [h.subposetInclusionWithin_fac]
    exact hp
  have hw := nervePushoutComparison_weak_of_cosieve_cover h.streetNerve g
    (v := h.posetMap (interRight Z C)) hp' hz hk he
    (h.street_cosieve_maps_isPushout Z C hZ hC cover)
    (h.cosieve_attachment_street_pushout A Z C hZ hC hAC cover hp p q hbp hjp hbq hjq) wz
  exact (nervePushoutComparison_weak_iff h.streetNerve
    (h.subposetInclusionWithin_fac A Z hAZ) hp' hp).mp hw

/-- The right adjoint is required only on the containing cosieve, rather
than on the ambient poset. This covers the actual subdivided horn pairs. -/
theorem finite_dwyer_attachment_comparison
    (G : RightGrayInput h) (aw : SimplexComplex.AlexanderWhitneyInput h)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0})
    {P : Type} [PartialOrder P] [Finite P] (A Z : Set P)
    (hA : IsLowerSet A) (hZ : IsUpperSet Z) (hAZ : A ⊆ Z)
    (R : SieveRetraction {z : Z | z.val ∈ A})
    {X Y : StrictOmegaCategory.{0}}
    {a : h.categorification.obj (nerve A) ⟶ X}
    {b : h.categorification.obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (h.posetMap (subposetInclusion A)) a b j) :
    realizationWeakEquivalences (nervePushoutComparison h.streetNerve hp) := by
  have wZ : h.CouniversalStreetWeakEquivalence
      (h.posetMap (subposetInclusionWithin A Z hAZ)) := by
    rw [← h.restrictedOldIso_fac A Z hAZ]
    exact h.couniversal_precompose_iso (h.posetMapIso (restrictedOldIso A Z hAZ)) _
      (h.finite_poset_couniversal G aw s g kq _ R)
  have : Mono (h.streetNerve.map (h.posetMap (subposetInclusionWithin A Z hAZ))) := by
    have := s.omega_nerve_mono {z : Z | z.val ∈ A} R.lower
    rw [← h.restrictedOldIso_fac A Z hAZ, h.streetNerve.map_comp]
    infer_instance
  apply h.containing_cosieve_attachment_comparison g kq A Z Aᶜ hZ hA.compl hAZ
    (fun _ hx hxc => hxc hx) ?_ wZ hp
  intro x
  by_cases hx : x ∈ A
  · exact Or.inl (hAZ hx)
  · exact Or.inr hx

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Street nerves of two-sieve decompositions of finite posets

The published sieve input identifies each actual categorified inclusion
with a full labelled fibre. The explicit Street cover theorem and the
range criterion then give the required simplicial pushout, without any
assumption that the Street nerve preserves arbitrary colimits.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable (h : NormalizedSimplexIdentities)

theorem street_factor_mono {X C : StrictOmegaCategory.{0}}
    (p : C ⟶ StrictPoset.category (Fin 2)) (f : X ⟶ labelFiber p 0) [IsIso f] :
    Mono (h.streetNerve.map (f ≫ labelFiberInclusion p 0)) := by
  rw [h.streetNerve.map_comp]
  infer_instance

theorem street_factor_range {X C : StrictOmegaCategory.{0}}
    (p : C ⟶ StrictPoset.category (Fin 2)) (f : X ⟶ labelFiber p 0) [IsIso f] :
    SSet.Subcomplex.range (h.streetNerve.map (f ≫ labelFiberInclusion p 0)) =
      h.fiberStreetSubcomplex p 0 := by
  rw [h.streetNerve.map_comp, SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]
  exact (h.fullStreetSubcomplex_eq_range _ _).symm

theorem fiberStreetSubcomplex_max {C : StrictOmegaCategory.{0}}
    (p q : C ⟶ StrictPoset.category (Fin 2)) :
    h.fiberStreetSubcomplex (maxLabel p q) 0 =
      h.fiberStreetSubcomplex p 0 ⊓ h.fiberStreetSubcomplex q 0 := by
  ext m f
  change (∀ x, C.FullCell {y | (maxLabel p q).toFun y = StrictPoset.identity 0} (f.toFun x)) ↔
    (∀ x, C.FullCell {y | p.toFun y = StrictPoset.identity 0} (f.toFun x)) ∧
    (∀ x, C.FullCell {y | q.toFun y = StrictPoset.identity 0} (f.toFun x))
  simp only [FullCell, Set.mem_ofPred_eq, maxLabel_zero_iff]
  constructor
  · intro hf
    exact ⟨fun x => ⟨(hf x).1.1, (hf x).2.1⟩, fun x => ⟨(hf x).1.2, (hf x).2.2⟩⟩
  · rintro ⟨hp, hq⟩ x
    exact ⟨⟨(hp x).1, (hq x).1⟩, ⟨(hp x).2, (hq x).2⟩⟩

variable [StrictColimitsInput]

/-- The image of the original Street map is exactly its full labelled fibre. -/
theorem posetStreet_range (s : PublishedPosetSieveInput h)
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A) :
    SSet.Subcomplex.range (h.streetNerve.map (h.posetMap (subposetInclusion A))) =
      h.fiberStreetSubcomplex (h.membershipLabel A hA) 0 := by
  have := s.omega A hA
  rw [← h.posetFiberMap_inclusion A hA, h.streetNerve.map_comp,
    SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top, SSet.Subcomplex.image_top]
  exact (h.fullStreetSubcomplex_eq_range _ _).symm

/-- The actual composite N c takes this two-sieve square to a pushout. -/
theorem street_sieve_maps_isPushout
    (s : PublishedPosetSieveInput h)
    {P : Type} [PartialOrder P] [Finite P]
    (A B : Set P) (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hcover : ∀ x, x ∈ A ∨ x ∈ B) :
    IsPushout ((h.categorification ⋙ h.streetNerve).map
        (nerveMap (interLeft A B).monotone.functor))
      ((h.categorification ⋙ h.streetNerve).map
        (nerveMap (interRight A B).monotone.functor))
      (h.streetNerve.map (h.posetMap (subposetInclusion A)))
      (h.streetNerve.map (h.posetMap (subposetInclusion B))) := by
  let F := h.categorification ⋙ h.streetNerve
  have hi : F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have hj : F.map (nerveMap (interRight A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion B).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have : Mono (F.map (nerveMap (subposetInclusion A).monotone.functor)) :=
    s.omega_nerve_mono A hA
  have : Mono (F.map (nerveMap (subposetInclusion B).monotone.functor)) :=
    s.omega_nerve_mono B hB
  have : Mono (F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor)) :=
    s.omega_nerve_mono (A ∩ B) (hA.inter hB)
  have : Mono (F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor)) := by rwa [hi]
  have hrange (S : Set P) (hS : IsLowerSet S) :
      SSet.Subcomplex.range (F.map (nerveMap (subposetInclusion S).monotone.functor)) =
        h.fiberStreetSubcomplex (h.membershipLabel S hS) 0 := h.posetStreet_range s S hS
  apply simplicial_isPushout_of_ranges _ _ _ _ (hi.trans hj.symm)
  · rw [hrange A hA, hrange B hB]
    apply h.sieve_street_cover
    intro x
    exact (hcover (h.posetObjectsEquiv P x)).imp
      ((h.membershipLabel_object_zero_iff A hA x).mpr)
      ((h.membershipLabel_object_zero_iff B hB x).mpr)
  · rw [hi, hrange (A ∩ B) (hA.inter hB), hrange A hA, hrange B hB,
      ← h.membershipLabel_inter A B hA hB, h.fiberStreetSubcomplex_max]

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Two-sieve Street pushouts after finite reflection

Only the published full-fibre identification is transported through the
fully faithful inclusion. All four categories remain in the original
finite dimension before taking their Street nerves.
-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem posetFiberMap_inclusion {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) :
    (StrictOmegaCategory.inclusion (n + 1)).map (r.posetFiberMap h A hA) ≫
      labelFiberInclusion (r.membershipLabel h A hA) 0 =
    (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map (h.posetMap (subposetInclusion A))) := by
  apply Hom.ext
  rfl

theorem posetStreet_mono (s : PublishedPosetSieveInput h)
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A) :
    Mono ((h.finiteStreetNerve (n + 1)).map
      (r.reflect.map (h.posetMap (subposetInclusion A)))) := by
  have : IsIso (C := Truncated (n + 1)) (r.posetFiberMap h A hA) := s.finite n r A hA
  let X : StrictOmegaCategory := ((r.categorification h).obj (nerve A)).val
  let C : StrictOmegaCategory := ((r.categorification h).obj (nerve P)).val
  let p : C ⟶ StrictPoset.category (Fin 2) := r.membershipLabel h A hA
  let f : X ⟶ labelFiber p 0 := (StrictOmegaCategory.inclusion (n + 1)).map (r.posetFiberMap h A hA)
  have : IsIso f := inferInstanceAs (IsIso ((StrictOmegaCategory.inclusion (n + 1)).map (r.posetFiberMap h A hA)))
  have hf : f ≫ labelFiberInclusion p 0 =
      (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map (h.posetMap (subposetInclusion A))) :=
    r.posetFiberMap_inclusion h A hA
  exact (congrArg (fun k : X ⟶ C => Mono (h.streetNerve.map k)) hf).mp
    (h.street_factor_mono p f)

theorem posetStreet_range (s : PublishedPosetSieveInput h)
    {P : Type} [PartialOrder P] [Finite P] (A : Set P) (hA : IsLowerSet A) :
    SSet.Subcomplex.range ((h.finiteStreetNerve (n + 1)).map
      (r.reflect.map (h.posetMap (subposetInclusion A)))) =
      h.fiberStreetSubcomplex (r.membershipLabel h A hA) 0 := by
  have : IsIso (C := Truncated (n + 1)) (r.posetFiberMap h A hA) := s.finite n r A hA
  let X : StrictOmegaCategory := ((r.categorification h).obj (nerve A)).val
  let C : StrictOmegaCategory := ((r.categorification h).obj (nerve P)).val
  let p : C ⟶ StrictPoset.category (Fin 2) := r.membershipLabel h A hA
  let f : X ⟶ labelFiber p 0 := (StrictOmegaCategory.inclusion (n + 1)).map (r.posetFiberMap h A hA)
  have : IsIso f := inferInstanceAs (IsIso ((StrictOmegaCategory.inclusion (n + 1)).map (r.posetFiberMap h A hA)))
  have hf : f ≫ labelFiberInclusion p 0 =
      (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map (h.posetMap (subposetInclusion A))) :=
    r.posetFiberMap_inclusion h A hA
  exact (congrArg (fun k : X ⟶ C => SSet.Subcomplex.range (h.streetNerve.map k)) hf).symm.trans
    (h.street_factor_range p f)

theorem street_sieve_maps_isPushout
    (s : PublishedPosetSieveInput h)
    {P : Type} [PartialOrder P] [Finite P]
    (A B : Set P) (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hcover : ∀ x, x ∈ A ∨ x ∈ B) :
    IsPushout (((r.categorification h) ⋙ h.finiteStreetNerve (n + 1)).map
        (nerveMap (interLeft A B).monotone.functor))
      (((r.categorification h) ⋙ h.finiteStreetNerve (n + 1)).map
        (nerveMap (interRight A B).monotone.functor))
      (((r.categorification h) ⋙ h.finiteStreetNerve (n + 1)).map
        (nerveMap (subposetInclusion A).monotone.functor))
      (((r.categorification h) ⋙ h.finiteStreetNerve (n + 1)).map
        (nerveMap (subposetInclusion B).monotone.functor)) := by
  let F := r.categorification h ⋙ h.finiteStreetNerve (n + 1)
  have hi : F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have hj : F.map (nerveMap (interRight A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion B).monotone.functor) =
      F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor) := by
    rw [← F.map_comp, ← orderNerveMap_comp]
    rfl
  have : Mono (F.map (nerveMap (subposetInclusion A).monotone.functor)) :=
    r.posetStreet_mono h s A hA
  have : Mono (F.map (nerveMap (subposetInclusion B).monotone.functor)) :=
    r.posetStreet_mono h s B hB
  have : Mono (F.map (nerveMap (subposetInclusion (A ∩ B)).monotone.functor)) :=
    r.posetStreet_mono h s (A ∩ B) (hA.inter hB)
  have : Mono (F.map (nerveMap (interLeft A B).monotone.functor) ≫
      F.map (nerveMap (subposetInclusion A).monotone.functor)) := by rwa [hi]
  have hrange (S : Set P) (hS : IsLowerSet S) :
      SSet.Subcomplex.range (F.map (nerveMap (subposetInclusion S).monotone.functor)) =
        h.fiberStreetSubcomplex (r.membershipLabel h S hS) 0 := r.posetStreet_range h s S hS
  apply simplicial_isPushout_of_ranges _ _ _ _ (hi.trans hj.symm)
  · rw [hrange A hA, hrange B hB]
    apply h.sieve_street_cover
    intro x
    exact (hcover (r.posetObjectsEquiv h P x)).imp
      ((r.membershipLabel_object_zero_iff h A hA x).mpr)
      ((r.membershipLabel_object_zero_iff h B hB x).mpr)
  · rw [hi, hrange (A ∩ B) (hA.inter hB), hrange A hA, hrange B hB,
      ← r.membershipLabel_inter h A B hA hB, h.fiberStreetSubcomplex_max]
    rfl

end Thomason.Construction.FiniteReflectionInput

end

end OAI
