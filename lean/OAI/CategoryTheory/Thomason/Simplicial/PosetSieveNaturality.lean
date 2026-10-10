import OAI.CategoryTheory.Thomason.Simplicial.ConstructedPosetCosieves
import OAI.CategoryTheory.Thomason.Simplicial.SieveFiberPresentation
import OAI.CategoryTheory.Thomason.Simplicial.SimplexCubeRetract
import OAI.CategoryTheory.Thomason.Strict.StrictPosetStarSemantics

namespace OAI

section

/-! # The canonical categorified sieve is its actual full zero fibre

The inverse is descended from clamped simplex maps. Both inverse identities
follow from the actual simplex colimits, with empty pieces included.
-/

namespace Thomason.Construction.SieveSimplex

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory
open NormalizedSimplexIdentities

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Forgetting the descended inverse recovers the original fibre inclusion. -/
theorem inverse_inclusion :
    inverse A hA h ≫ h.posetMap (subposetInclusion A) =
      labelFiberInclusion (h.membershipLabel A hA) 0 := by
  apply (fiberCoconeIsColimit A hA h).hom_ext
  intro s
  let l : labelFiber (label A hA (simplexOrder (SSet.yonedaEquiv s.hom)) h) 0 ⟶
      labelFiber (h.membershipLabel A hA) 0 := (fiberCocone A hA h).ι.app s
  change l ≫ (inverse A hA h ≫ h.posetMap (subposetInclusion A)) =
    l ≫ labelFiberInclusion (h.membershipLabel A hA) 0
  have he := back_inclusion A hA h (simplexOrder (SSet.yonedaEquiv s.hom))
  rw [h.posetLeg_simplexOrder] at he
  exact (Category.assoc l _ _).symm.trans
    ((congrArg (fun k => k ≫ h.posetMap (subposetInclusion A))
      (inverse_fac A hA h s)).trans he)

/-- The descended inverse is a right inverse of the canonical sieve map. -/
theorem inverse_posetFiberMap :
    inverse A hA h ≫ h.posetFiberMap A hA = 𝟙 _ := by
  apply (cancel_mono (labelFiberInclusion (h.membershipLabel A hA) 0)).mp
  rw [Category.assoc, h.posetFiberMap_inclusion, inverse_inclusion, Category.id_comp]

/-- The whole sieve simplex maps to the original colimit leg after forgetting. -/
theorem whole_fiberLeg {m : ℕ} (s : Fin (m+1) →o A) :
    whole A hA h s ≫ (fiberCocone A hA h).ι.app
        (CostructuredArrow.mk (SSet.yonedaEquiv.symm
          (orderSimplex ((subposetInclusion A).comp s)))) =
      h.posetLeg s ≫ h.posetFiberMap A hA := by
  apply (cancel_mono (labelFiberInclusion (h.membershipLabel A hA) 0)).mp
  rw [Category.assoc, h.posetFiberMap_inclusion]
  exact (h.posetLeg_postcomp s (subposetInclusion A)).symm

/-- The inverse identity on an arbitrary simplex of the original sieve. -/
theorem posetFiberMap_inverse_on_leg {m : ℕ} (s : Fin (m+1) →o A) :
    h.posetLeg s ≫ (h.posetFiberMap A hA ≫ inverse A hA h) = h.posetLeg s := by
  let t := CostructuredArrow.mk (SSet.yonedaEquiv.symm
    (orderSimplex ((subposetInclusion A).comp s)))
  let l : labelFiber (label A hA ((subposetInclusion A).comp s) h) 0 ⟶
      labelFiber (h.membershipLabel A hA) 0 := (fiberCocone A hA h).ι.app t
  have hl : l ≫ inverse A hA h = back A hA h ((subposetInclusion A).comp s) := by
    have hv : simplexOrder (SSet.yonedaEquiv t.hom) = (subposetInclusion A).comp s := by
      change simplexOrder (SSet.yonedaEquiv (SSet.yonedaEquiv.symm
        (orderSimplex ((subposetInclusion A).comp s)))) = _
      rw [Equiv.apply_symm_apply, simplexOrder_orderSimplex]
    apply Hom.ext
    funext x
    let y : labelFiber (label A hA (simplexOrder (SSet.yonedaEquiv t.hom)) h) 0 :=
      ⟨x.val, by rw [hv]; exact x.property⟩
    have he := congrArg (fun f => f.toFun y) (inverse_fac A hA h t)
    exact he.trans (back_apply_congr A hA h hv y x rfl)
  have hw : whole A hA h s ≫ l = h.posetLeg s ≫ h.posetFiberMap A hA :=
    whole_fiberLeg A hA h s
  exact (Category.assoc (h.posetLeg s) _ _).symm.trans
    ((congrArg (fun k => k ≫ inverse A hA h) hw.symm).trans
      ((Category.assoc (whole A hA h s) l _).trans
        ((congrArg (fun k => whole A hA h s ≫ k) hl).trans (whole_back A hA h s))))

/-- The descended inverse is also a left inverse, on the original sieve colimit. -/
theorem posetFiberMap_inverse :
    h.posetFiberMap A hA ≫ inverse A hA h = 𝟙 _ := by
  apply (h.simplexCocone_isColimit (nerve A)).hom_ext
  intro t
  have he := posetFiberMap_inverse_on_leg A hA h (simplexOrder (SSet.yonedaEquiv t.hom))
  rw [h.posetLeg_simplexOrder] at he
  change h.simplexLeg t.hom ≫ (h.posetFiberMap A hA ≫ inverse A hA h) =
    h.simplexLeg t.hom ≫ 𝟙 _
  rw [Category.comp_id]
  exact he

end SieveSimplex

namespace NormalizedSimplexIdentities

open CategoryTheory StrictOmegaCategory

/-- A poset sieve categorifies to exactly the full zero fibre of membership. -/
noncomputable def posetSieveIso (h : NormalizedSimplexIdentities) [StrictColimitsInput]
    {P : Type} [PartialOrder P] (A : Set P) (hA : IsLowerSet A) :
    h.categorification.obj (nerve A) ≅ labelFiber (h.membershipLabel A hA) 0 where
  hom := h.posetFiberMap A hA
  inv := SieveSimplex.inverse A hA h
  hom_inv_id := SieveSimplex.posetFiberMap_inverse A hA h
  inv_hom_id := SieveSimplex.inverse_posetFiberMap A hA h

/-- The simplex construction gives the full-sieve comparison in omega dimension. -/
theorem constructedOmegaPosetSieveInput (h : NormalizedSimplexIdentities)
    [StrictColimitsInput] : PublishedOmegaPosetSieveInput h where
  omega A hA := (h.posetSieveIso A hA).isIso_hom

end NormalizedSimplexIdentities
end Thomason.Construction

end

section

/-! # Finite reflection retains the actual full cosieve inclusion -/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)

/-- The one-fibre comparison commutes with the original full inclusion. -/
theorem oneFiberComparison_inclusion {X : StrictOmegaCategory.{0}}
    (p : X ⟶ StrictPoset.category (Fin 2))
    (q : (r.reflect.obj X).val ⟶ StrictPoset.category (Fin 2))
    (hq : r.adjunction.unit.app X ≫ q = p) :
    r.oneFiberComparison p q hq ≫
      (show r.reflectedOneLabelFiber q ⟶ r.reflect.obj X from labelFiberInclusion q 1) =
      r.reflect.map (labelFiberInclusion p 1) := by
  let F := labelFiber p 1
  let Q := r.reflectedOneLabelFiber q
  let c : (r.reflect.obj F).val ⟶ Q.val := r.oneFiberComparison p q hq
  let k : Q.val ⟶ (r.reflect.obj X).val := labelFiberInclusion q 1
  let u : F ⟶ (r.reflect.obj F).val := r.adjunction.unit.app F
  have hc : u ≫ c = r.oneFiberUnit p q hq := r.oneFiberComparison_fac p q hq
  let f : (r.reflect.obj F).val ⟶ (r.reflect.obj X).val :=
    r.reflect.map (labelFiberInclusion p 1)
  let v : X ⟶ (r.reflect.obj X).val := r.adjunction.unit.app X
  have hn : labelFiberInclusion p 1 ≫ v = u ≫ f :=
    r.adjunction.unit.naturality (labelFiberInclusion p 1)
  apply r.unit_hom_ext F (r.reflect.obj X)
  change u ≫ (c ≫ k) = u ≫ f
  have hv : r.oneFiberUnit p q hq ≫ k = labelFiberInclusion p 1 ≫ v := by
    apply Hom.ext
    rfl
  exact (Category.assoc u c k).symm.trans
    ((congrArg (fun f : F ⟶ Q.val => f ≫ k) hc).trans (hv.trans hn))

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- A finite cosieve is its actual full one fibre, not merely an equivalent
replacement category. -/
noncomputable def posetCosieveIso {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) :
    (r.categorification h).obj (nerve A) ≅
      r.reflectedOneLabelFiber (r.membershipLabel h Aᶜ hA.compl) := by
  have := r.oneFiberComparison_isIso (h.membershipLabel Aᶜ hA.compl)
    (r.membershipLabel h Aᶜ hA.compl) (r.membershipLabel_unit h Aᶜ hA.compl)
  exact r.reflect.mapIso (h.posetCosieveIso A hA) ≪≫
    asIso (r.oneFiberComparison (h.membershipLabel Aᶜ hA.compl)
      (r.membershipLabel h Aᶜ hA.compl) (r.membershipLabel_unit h Aᶜ hA.compl))

/-- The isomorphism factors the literal reflected poset inclusion. -/
theorem posetCosieveIso_inclusion {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) :
    (r.posetCosieveIso h A hA).hom ≫
      (show r.reflectedOneLabelFiber (r.membershipLabel h Aᶜ hA.compl) ⟶
        (r.categorification h).obj (nerve P) from
          labelFiberInclusion (r.membershipLabel h Aᶜ hA.compl) 1) =
      r.reflect.map (h.posetMap (subposetInclusion A)) := by
  let p := h.membershipLabel Aᶜ hA.compl
  let q := r.membershipLabel h Aᶜ hA.compl
  let hq := r.membershipLabel_unit h Aᶜ hA.compl
  let f : r.reflect.obj (h.categorification.obj (nerve A)) ⟶
      r.reflect.obj (labelFiber p 1) := r.reflect.map (h.posetCosieveIso A hA).hom
  let c : r.reflect.obj (labelFiber p 1) ⟶ r.reflectedOneLabelFiber q :=
    r.oneFiberComparison p q hq
  let k : r.reflectedOneLabelFiber q ⟶ r.reflect.obj (h.categorification.obj (nerve P)) :=
    labelFiberInclusion q 1
  have hc : c ≫ k = r.reflect.map (labelFiberInclusion p 1) :=
    r.oneFiberComparison_inclusion p q hq
  change (f ≫ c) ≫ k = _
  calc
    _ = f ≫ (c ≫ k) := Category.assoc f c k
    _ = f ≫ r.reflect.map (labelFiberInclusion p 1) := congrArg (fun v => f ≫ v) hc
    _ = r.reflect.map ((h.posetCosieveIso A hA).hom ≫ labelFiberInclusion p 1) :=
      (r.reflect.map_comp _ _).symm
    _ = _ := congrArg r.reflect.map (h.cosievePosetFiberMap_inclusion A hA)

end Thomason.Construction.FiniteReflectionInput

end

section

/-! # Naturality of the constructed full sieve identification

A monotone map pulling a target sieve back to the source sieve respects the
actual membership labels. Its restriction on full zero fibres is the
categorification of its ordinary restriction, under the constructed isomorphisms.
-/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

namespace SieveMap

variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
  (A : Set P) (B : Set Q) (f : P →o Q) (hf : ∀ x, f x ∈ B ↔ x ∈ A)

/-- The ordinary restriction to the two sieves. -/
def restriction : A →o B where
  toFun x := ⟨f x.val, (hf x.val).mpr x.property⟩
  monotone' := fun _ _ hxy => f.monotone hxy

/-- Restriction commutes with the original full-subposet inclusions. -/
theorem restriction_inclusion :
    (subposetInclusion B).comp (restriction A B f hf) = f.comp (subposetInclusion A) := rfl

include hf

/-- Pullback equality of sieves is exactly equality of binary characteristic labels. -/
theorem characteristic (hA : IsLowerSet A) (hB : IsLowerSet B) :
    (sieveCharacteristic B hB).comp f = sieveCharacteristic A hA := by
  classical
  apply DFunLike.ext
  intro x
  change (if f x ∈ B then (0 : Fin 2) else 1) = (if x ∈ A then 0 else 1)
  rw [hf x]

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (hA : IsLowerSet A) (hB : IsLowerSet B)

/-- The actual categorified map respects the original membership labels. -/
theorem membership :
    h.posetMap f ≫ h.membershipLabel B hB = h.membershipLabel A hA := by
  apply Hom.ext
  funext x
  have hn := congrArg (fun k : h.categorification.obj (nerve P) ⟶ StrictPoset.category Q =>
    k.toFun x) (h.posetEvaluation_naturality f)
  change (h.posetEvaluation Q).toFun ((h.posetMap f).toFun x) =
    (StrictPoset.map f).toFun ((h.posetEvaluation P).toFun x) at hn
  change (StrictPoset.map (sieveCharacteristic B hB)).toFun
    ((h.posetEvaluation Q).toFun ((h.posetMap f).toFun x)) = _
  rw [hn]
  have hc := congrArg (fun k : P →o Fin 2 => (StrictPoset.map k).toFun
    ((h.posetEvaluation P).toFun x)) (characteristic A B f hf hA hB)
  exact hc

/-- The full-fibre map is the restriction of the original strict functor. -/
noncomputable def fiberMap :
    labelFiber (h.membershipLabel A hA) 0 ⟶ labelFiber (h.membershipLabel B hB) 0 :=
  labelFiberMap _ _ 0 (h.posetMap f) (membership A B f hf h hA hB)

/-- The constructed sieve isomorphisms commute with every pullback-preserving map. -/
theorem naturality :
    h.posetFiberMap A hA ≫ fiberMap A B f hf h hA hB =
      h.posetMap (restriction A B f hf) ≫ h.posetFiberMap B hB := by
  apply (cancel_mono (labelFiberInclusion (h.membershipLabel B hB) 0)).mp
  have he : h.posetMap (subposetInclusion A) ≫ h.posetMap f =
      h.posetMap (restriction A B f hf) ≫ h.posetMap (subposetInclusion B) := by
    rw [← h.posetMap_comp, ← h.posetMap_comp, restriction_inclusion]
  exact he

end SieveMap
end Thomason.Construction

end

end OAI
