import OAI.CategoryTheory.Thomason.Strict.FiniteCosieveMembership
import OAI.CategoryTheory.Thomason.Transfer.FiniteEmptyAttachmentFibers
import OAI.CategoryTheory.Thomason.Transfer.FiniteStreetSievePushouts

namespace OAI

section

/-! # Full cosieve pieces in the original finite attaching pushout -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The smaller categorified poset attachment is the actual full finite fibre. -/
theorem cosieve_piece_pushout {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : A ⊆ U)
    {X Y : Truncated.{0} (n + 1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j)
    (pY : Y ⟶ finiteInterval n)
    (hb : b ≫ pY = r.membershipLabel h Uᶜ hU.compl) (hj : j ≫ pY = finiteConstantLabel X 1) :
    IsPushout (r.reflect.map (h.posetMap (subposetInclusionWithin A U hAU))) a
      (((r.posetCosieveIso h U hU).hom) ≫ finiteLabelFiberMap (r.membershipLabel h Uᶜ hU.compl) pY 1 b hb)
      ((finiteConstantFiberIso X 1).inv ≫
        finiteLabelFiberMap (finiteConstantLabel X 1) pY 1 j hj) := by
  let eU : (r.categorification h).obj (nerve U) ≅
      finiteLabelFiber (r.membershipLabel h Uᶜ hU.compl) 1 :=
    r.posetCosieveIso h U hU
  have hi : r.reflect.map (h.posetMap (subposetInclusion A)) ≫ r.membershipLabel h Uᶜ hU.compl =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 1 := by
    apply Hom.ext
    funext x
    exact r.posetMap_cosieveMembership_one h U hU _ (fun z => hAU z.property) x
  have hiU : r.reflect.map (h.posetMap (subposetInclusionWithin A U hAU)) ≫
      r.reflect.map (h.posetMap (subposetInclusion U)) =
      r.reflect.map (h.posetMap (subposetInclusion A)) := by
    rw [← r.reflect.map_comp, h.subposetInclusionWithin_fac]
  have hu : (r.posetCosieveIso h U hU).hom ≫ labelFiberInclusion (r.membershipLabel h Uᶜ hU.compl) 1 =
      r.reflect.map (h.posetMap (subposetInclusion U)) := r.posetCosieveIso_inclusion h U hU
  exact EndpointFiber.finite_attachment_piece 1 hp hiU (r.membershipLabel h Uᶜ hU.compl) pY hi hb hj
    eU hu

/-- Construct the compatible label using the original finite pushout. -/
theorem cosieve_piece_label {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : A ⊆ U)
    {X Y : Truncated.{0} (n + 1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    ∃ pY : Y ⟶ finiteInterval n,
      b ≫ pY = r.membershipLabel h Uᶜ hU.compl ∧ j ≫ pY = finiteConstantLabel X 1 := by
  have hi : r.reflect.map (h.posetMap (subposetInclusion A)) ≫ r.membershipLabel h Uᶜ hU.compl =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 1 := by
    apply Hom.ext
    funext x
    exact r.posetMap_cosieveMembership_one h U hU _ (fun z => hAU z.property) x
  have ha : a ≫ finiteConstantLabel X 1 =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 1 := by apply Hom.ext; rfl
  exact hp.exists_desc (r.membershipLabel h Uᶜ hU.compl) (finiteConstantLabel X 1) (hi.trans ha.symm)


/-- A disjoint cosieve extends across the old target by the constant zero label. -/
theorem disjoint_cosieve_piece_label {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : ∀ x ∈ A, x ∉ U)
    {X Y : Truncated.{0} (n+1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j) :
    ∃ pY : Y ⟶ finiteInterval n,
      b ≫ pY = r.membershipLabel h Uᶜ hU.compl ∧ j ≫ pY = finiteConstantLabel X 0 := by
  have hi : r.reflect.map (h.posetMap (subposetInclusion A)) ≫ r.membershipLabel h Uᶜ hU.compl =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact r.posetMap_membership_zero h Uᶜ hU.compl _ (fun z => hAU z.val z.property) x
  have ha : a ≫ finiteConstantLabel X 0 =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 0 := by apply Hom.ext; rfl
  exact hp.exists_desc (r.membershipLabel h Uᶜ hU.compl) (finiteConstantLabel X 0) (hi.trans ha.symm)

/-- The disjoint finite cosieve is isomorphic to the post-attachment fibre. -/
theorem disjoint_cosieve_piece_iso {P : Type} [PartialOrder P]
    (A U : Set P) (hU : IsUpperSet U) (hAU : ∀ x ∈ A, x ∉ U)
    {X Y : Truncated.{0} (n+1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j)
    (pY : Y ⟶ finiteInterval n)
    (hb : b ≫ pY = r.membershipLabel h Uᶜ hU.compl) (hj : j ≫ pY = finiteConstantLabel X 0) :
    IsIso ((r.posetCosieveIso h U hU).hom ≫
      finiteLabelFiberMap (r.membershipLabel h Uᶜ hU.compl) pY 1 b hb) := by
  have hi : r.reflect.map (h.posetMap (subposetInclusion A)) ≫ r.membershipLabel h Uᶜ hU.compl =
      finiteConstantLabel ((r.categorification h).obj (nerve A)) 0 := by
    apply Hom.ext
    funext x
    exact r.posetMap_membership_zero h Uᶜ hU.compl _ (fun z => hAU z.val z.property) x
  have : IsIso (C := Truncated (n+1))
      (finiteLabelFiberMap (r.membershipLabel h Uᶜ hU.compl) pY 1 b hb) :=
    EndpointFiber.finite_attachment_complement_iso 1 0 (by decide) hp
      (r.membershipLabel h Uᶜ hU.compl) pY hi hb hj
  let eU : (r.categorification h).obj (nerve U) ≅
      finiteLabelFiber (r.membershipLabel h Uᶜ hU.compl) 1 := r.posetCosieveIso h U hU
  change IsIso (C := Truncated (n+1))
    (eU.hom ≫ finiteLabelFiberMap (r.membershipLabel h Uᶜ hU.compl) pY 1 b hb)
  infer_instance

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # Full cosieve covers of actual finite-dimensional attachments -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

theorem cosieve_attachment_street_pushout
    {P : Type} [PartialOrder P] (A Z C : Set P)
    (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hAC : ∀ x ∈ A, x ∉ C) (cover : ∀ x, x ∈ Z ∨ x ∈ C)
    {X Y : Truncated.{0} (n+1)}
    {a : (r.categorification h).obj (nerve A) ⟶ X}
    {b : (r.categorification h).obj (nerve P) ⟶ Y} {j : X ⟶ Y}
    (hp : IsPushout (r.reflect.map (h.posetMap (subposetInclusion A))) a b j)
    (p q : Y ⟶ finiteInterval n)
    (hbp : b ≫ p = r.membershipLabel h Zᶜ hZ.compl)
    (hjp : j ≫ p = finiteConstantLabel X 1)
    (hbq : b ≫ q = r.membershipLabel h Cᶜ hC.compl)
    (hjq : j ≫ q = finiteConstantLabel X 0) :
    IsPushout
      ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (interLeft Z C)) ≫
        ((r.posetCosieveIso h Z hZ).hom ≫
          finiteLabelFiberMap (r.membershipLabel h Zᶜ hZ.compl) p 1 b hbp)))
      ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (interRight Z C))))
      ((h.finiteStreetNerve (n+1)).map (finiteLabelFiberInclusion p 1))
      ((h.finiteStreetNerve (n+1)).map (r.reflect.map (h.posetMap (subposetInclusion C)) ≫ b)) := by
  let z : Y ⟶ finiteInterval n := minLabel p q
  have hbz : b ≫ z = r.membershipLabel h (Z ∩ C)ᶜ (hZ.inter hC).compl := by
    exact (minLabel_precomp p q b).trans
      ((congrArg₂ minLabel hbp hbq).trans (r.cosieveMembershipLabel_inter h Z C hZ hC))
  have hjz : j ≫ z = finiteConstantLabel X 0 := by
    apply (minLabel_precomp p q j).trans
    apply (congrArg₂ minLabel hjp hjq).trans
    apply Hom.ext
    rfl
  let fC : (r.categorification h).obj (nerve C) ⟶ finiteLabelFiber q 1 :=
    (r.posetCosieveIso h C hC).hom ≫
      finiteLabelFiberMap (r.membershipLabel h Cᶜ hC.compl) q 1 b hbq
  let fI : (r.categorification h).obj (nerve ↥(Z ∩ C)) ⟶ finiteLabelFiber z 1 :=
    (r.posetCosieveIso h (Z ∩ C) (hZ.inter hC)).hom ≫
      finiteLabelFiberMap (r.membershipLabel h (Z ∩ C)ᶜ (hZ.inter hC).compl) z 1 b hbz
  have : IsIso (C := Truncated (n+1)) fC := r.disjoint_cosieve_piece_iso h A C hC hAC hp q hbq hjq
  have : IsIso (C := Truncated (n+1)) fI := r.disjoint_cosieve_piece_iso h A (Z ∩ C) (hZ.inter hC)
    (fun x hx hxc => hAC x hx hxc.2) hp z hbz hjz
  have hfC : fC ≫ finiteLabelFiberInclusion q 1 =
      r.reflect.map (h.posetMap (subposetInclusion C)) ≫ b :=
    EndpointFiber.finite_piece_inclusion 1 _ _ b hbq _ (r.posetCosieveIso h C hC)
      (r.posetCosieveIso_inclusion h C hC)
  have hfI : fI ≫ finiteLabelFiberInclusion z 1 =
      r.reflect.map (h.posetMap (subposetInclusion (Z ∩ C))) ≫ b :=
    EndpointFiber.finite_piece_inclusion 1 _ _ b hbz _ (r.posetCosieveIso h (Z ∩ C) (hZ.inter hC))
      (r.posetCosieveIso_inclusion h (Z ∩ C) (hZ.inter hC))
  let bZ : (r.categorification h).obj (nerve Z) ⟶ finiteLabelFiber p 1 :=
    (r.posetCosieveIso h Z hZ).hom ≫
      finiteLabelFiberMap (r.membershipLabel h Zᶜ hZ.compl) p 1 b hbp
  have hbZ : bZ ≫ finiteLabelFiberInclusion p 1 =
      r.reflect.map (h.posetMap (subposetInclusion Z)) ≫ b :=
    EndpointFiber.finite_piece_inclusion 1 _ _ b hbp _ (r.posetCosieveIso h Z hZ)
      (r.posetCosieveIso_inclusion h Z hZ)
  have hleft : r.reflect.map (h.posetMap (interLeft Z C)) ≫
      r.reflect.map (h.posetMap (subposetInclusion Z)) =
      r.reflect.map (h.posetMap (subposetInclusion (Z ∩ C))) :=
    (r.reflect.map_comp _ _).symm.trans
      (congrArg r.reflect.map (h.posetMap_comp (interLeft Z C) (subposetInclusion Z)).symm)
  have hright : r.reflect.map (h.posetMap (interRight Z C)) ≫
      r.reflect.map (h.posetMap (subposetInclusion C)) =
      r.reflect.map (h.posetMap (subposetInclusion (Z ∩ C))) :=
    (r.reflect.map_comp _ _).symm.trans
      (congrArg r.reflect.map (h.posetMap_comp (interRight Z C) (subposetInclusion C)).symm)
  have hi : (r.reflect.map (h.posetMap (interLeft Z C)) ≫ bZ) ≫ finiteLabelFiberInclusion p 1 =
      fI ≫ finiteLabelFiberInclusion z 1 :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => r.reflect.map (h.posetMap (interLeft Z C)) ≫ k) hbZ).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ b) hleft).trans hfI.symm)))
  have hw : (r.reflect.map (h.posetMap (interLeft Z C)) ≫ bZ) ≫ finiteLabelFiberInclusion p 1 =
      r.reflect.map (h.posetMap (interRight Z C)) ≫
        (r.reflect.map (h.posetMap (subposetInclusion C)) ≫ b) :=
    hi.trans (hfI.trans
      (((congrArg (fun k => k ≫ b) hright).symm).trans (Category.assoc _ _ _)))
  have hcover : ∀ y : Objects Y.val, p.toFun y.val = StrictPoset.identity 1 ∨
      q.toFun y.val = StrictPoset.identity 1 := by
    apply finite_pushout_label_cover hp p q 1
    · intro x
      rcases cover (r.posetObjectsEquiv h P x) with hx | hx
      · left
        exact (congrArg (fun f => f.toFun x.val) hbp).trans
          ((r.cosieveMembershipLabel_object h Z hZ x).mpr hx)
      · right
        exact (congrArg (fun f => f.toFun x.val) hbq).trans
          ((r.cosieveMembershipLabel_object h C hC x).mpr hx)
    · intro x
      left
      exact congrArg (fun f => f.toFun x.val) hjp
  let eC : ((r.categorification h).obj (nerve C)).val ≅ labelFiber q 1 :=
    (StrictOmegaCategory.inclusion (n+1)).mapIso (asIso fC)
  let eI : ((r.categorification h).obj (nerve ↥(Z ∩ C))).val ≅ labelFiber z 1 :=
    (StrictOmegaCategory.inclusion (n+1)).mapIso (asIso fI)
  exact h.street_cosieve_fiber_pushout p q hcover (Iso.refl _) eC eI
    (by apply Hom.ext; rfl) hfC hi hw

end Thomason.Construction.FiniteReflectionInput

end

end OAI
