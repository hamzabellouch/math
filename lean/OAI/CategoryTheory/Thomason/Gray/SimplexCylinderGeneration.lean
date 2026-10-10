import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Chains.SimplexChainHeight
import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping
import OAI.CategoryTheory.Thomason.Gray.PosetPrismEndpoints
import OAI.CategoryTheory.Thomason.Gray.StrictAbelianization
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import Mathlib.Data.List.Sort

namespace OAI

section

/-! # Relative cylinder lifting for genuine Kan fibrations -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

universe u

noncomputable section

/-- A Kan fibration lifts a cylinder with both its initial map and a prescribed
subobject cylinder fixed. This is the pushout-product lifting property. -/
theorem exists_kan_cylinder_lift {A K E B : SSet.{u}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (f : K ⟶ E) (h : A ⊗ Δ[1] ⟶ E) (b : K ⊗ Δ[1] ⟶ B)
    (h₀ : SSet.ι₀ ≫ h = i ≫ f)
    (hb : h ≫ p = i ▷ Δ[1] ≫ b) (hf : f ≫ p = SSet.ι₀ ≫ b) :
    ∃ e : K ⊗ Δ[1] ⟶ E,
      SSet.ι₀ ≫ e = f ∧ i ▷ Δ[1] ≫ e = h ∧ e ≫ p = b := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet)
    i (SSet.stdSimplex.δ (1 : Fin 2))
  have hc : i ▷ (Δ[0] : SSet.{u}) ≫ fst K (Δ[0] : SSet.{u}) ≫ f =
      A ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ h := by
    rw [whisker_zero_face, Category.assoc, h₀]
    have hp : i ▷ (Δ[0] : SSet.{u}) ≫ fst K (Δ[0] : SSet.{u}) =
        fst A (Δ[0] : SSet.{u}) ≫ i := by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hp, Category.assoc]
  let g : sq.pt ⟶ E := sq.isPushout.desc (fst K (Δ[0] : SSet.{u}) ≫ f) h hc
  have gl : sq.inl ≫ g = fst K (Δ[0] : SSet.{u}) ≫ f := sq.isPushout.inl_desc _ _ _
  have gr : sq.inr ≫ g = h := sq.isPushout.inr_desc _ _ _
  have il : sq.inl ≫ sq.ι = K ◁ SSet.stdSimplex.δ (1 : Fin 2) := sq.inl_ι
  have ir : sq.inr ≫ sq.ι = i ▷ Δ[1] := sq.inr_ι
  have hg : g ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, gl, Category.assoc, hf]
      rw [← Category.assoc sq.inl sq.ι b, il, whisker_zero_face, Category.assoc]
    · rw [← Category.assoc, gr, hb, ← Category.assoc, ir]
  have ha : SSet.anodyneExtensions sq.ι :=
    SSet.anodyneExtensions_pushoutObjObjι sq (anodyne_delta_one 1)
  let : HasLiftingProperty sq.ι p :=
    ha _ (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let c : CommSq g sq.ι p b := ⟨hg⟩
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · have he : K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ c.lift =
        fst K (Δ[0] : SSet.{u}) ≫ f := by
      rw [← il, Category.assoc, c.fac_left, gl]
    have hz := congrArg (fun k => zeroFaceSection K ≫ k) he
    simpa only [← Category.assoc, zeroFaceSection_face, zeroFaceSection_fst,
      Category.id_comp] using hz
  · rw [← ir, Category.assoc, c.fac_left, gr]

end

end Thomason.Construction

end

section

/-! # Kan lifts preserving both ends of an anodyne cylinder -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

universe u

noncomputable section

theorem whisker_one_face (K : SSet.{u}) :
    K ◁ SSet.stdSimplex.δ (0 : Fin 2) =
      fst K (Δ[0] : SSet.{u}) ≫ SSet.ι₁ := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.objEquiv.injective
    ext k
    change ↑((SimplexCategory.δ (0 : Fin 2)).toOrderHom
      ((SSet.stdSimplex.objEquiv x.2).toOrderHom k)) = (1 : ℕ)
    have he : (SSet.stdSimplex.objEquiv x.2).toOrderHom k = 0 :=
      @Subsingleton.elim (Fin 1) inferInstance _ _
    rw [he]
    rfl

theorem intervalBoundary_restriction {K X : SSet.{u}} (a : K ⊗ Δ[1] ⟶ X)
    (x₀ x₁ : X _⦋0⦌) (h₀ : SSet.ι₀ ≫ a = SSet.const x₀)
    (h₁ : SSet.ι₁ ≫ a = SSet.const x₁) :
    K ◁ (SSet.boundary 1).ι ≫ a =
      snd K (SSet.boundary 1 : SSet.{u}) ≫ intervalBoundaryMap x₀ x₁ := by
  apply interval_boundary_tensor_hom_ext
  · rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_zero_face, Category.assoc, h₀, SSet.comp_const]
    rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
      intervalBoundaryMap_zero, SSet.comp_const]
  · rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      whisker_one_face, Category.assoc, h₁, SSet.comp_const]
    rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
      intervalBoundaryMap_one, SSet.comp_const]

/-- An anodyne map times an interval can be lifted while prescribing the
whole interval boundary. This uses only the proved pushout-product theorem. -/
theorem exists_kan_boundary_cylinder_lift {A K E B : SSet.{u}}
    (i : A ⟶ K) (hi : SSet.anodyneExtensions i)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (a : A ⊗ Δ[1] ⟶ E) (c : K ⊗ (SSet.boundary 1 : SSet.{u}) ⟶ E)
    (b : K ⊗ Δ[1] ⟶ B)
    (hc : i ▷ (SSet.boundary 1 : SSet.{u}) ≫ c = A ◁ (SSet.boundary 1).ι ≫ a)
    (ha : a ≫ p = i ▷ Δ[1] ≫ b) (hb : c ≫ p = K ◁ (SSet.boundary 1).ι ≫ b) :
    ∃ e : K ⊗ Δ[1] ⟶ E,
      i ▷ Δ[1] ≫ e = a ∧ K ◁ (SSet.boundary 1).ι ≫ e = c ∧ e ≫ p = b := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i (SSet.boundary 1).ι
  let g := sq.isPushout.desc c a hc
  have gl : sq.inl ≫ g = c := sq.isPushout.inl_desc _ _ _
  have gr : sq.inr ≫ g = a := sq.isPushout.inr_desc _ _ _
  have il : sq.inl ≫ sq.ι = K ◁ (SSet.boundary 1).ι := sq.inl_ι
  have ir : sq.inr ≫ sq.ι = i ▷ Δ[1] := sq.inr_ι
  have hg : g ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, gl, hb, ← Category.assoc, il]
    · rw [← Category.assoc, gr, ha, ← Category.assoc, ir]
  have hsq : SSet.anodyneExtensions sq.ι :=
    SSet.anodyneExtensions_pushoutObjObjι' sq hi
  let : HasLiftingProperty sq.ι p :=
    hsq _ (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let s : CommSq g sq.ι p b := ⟨hg⟩
  refine ⟨s.lift, ?_, ?_, s.fac_right⟩
  · rw [← ir, Category.assoc, s.fac_left, gr]
  · rw [← il, Category.assoc, s.fac_left, gl]

end

end Thomason.Construction

end

section

/-! # Relative cylinder lifting from the final endpoint -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SSet.modelCategoryQuillen

universe u

noncomputable section

theorem zeroFaceSection_one_face (K : SSet.{u}) :
    zeroFaceSection K ≫ K ◁ SSet.stdSimplex.δ (0 : Fin 2) = SSet.ι₁ := by
  rw [whisker_one_face, zeroFaceSection_fst_assoc]

/-- Final-endpoint lifting, with the prescribed subobject fixed throughout. -/
theorem exists_kan_cylinder_lift_one {A K E B : SSet.{u}}
    (i : A ⟶ K) [Mono i] (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (f : K ⟶ E) (h : A ⊗ Δ[1] ⟶ E) (b : K ⊗ Δ[1] ⟶ B)
    (h₀ : SSet.ι₁ ≫ h = i ≫ f)
    (hb : h ≫ p = i ▷ Δ[1] ≫ b) (hf : f ≫ p = SSet.ι₁ ≫ b) :
    ∃ e : K ⊗ Δ[1] ⟶ E,
      SSet.ι₁ ≫ e = f ∧ i ▷ Δ[1] ≫ e = h ∧ e ≫ p = b := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet)
    i (SSet.stdSimplex.δ (0 : Fin 2))
  have hc : i ▷ (Δ[0] : SSet.{u}) ≫ fst K (Δ[0] : SSet.{u}) ≫ f =
      A ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ h := by
    rw [whisker_one_face, Category.assoc, h₀]
    have hp : i ▷ (Δ[0] : SSet.{u}) ≫ fst K (Δ[0] : SSet.{u}) =
        fst A (Δ[0] : SSet.{u}) ≫ i := by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hp, Category.assoc]
  let g : sq.pt ⟶ E := sq.isPushout.desc (fst K (Δ[0] : SSet.{u}) ≫ f) h hc
  have gl : sq.inl ≫ g = fst K (Δ[0] : SSet.{u}) ≫ f := sq.isPushout.inl_desc _ _ _
  have gr : sq.inr ≫ g = h := sq.isPushout.inr_desc _ _ _
  have il : sq.inl ≫ sq.ι = K ◁ SSet.stdSimplex.δ (0 : Fin 2) := sq.inl_ι
  have ir : sq.inr ≫ sq.ι = i ▷ Δ[1] := sq.inr_ι
  have hg : g ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, gl, Category.assoc, hf]
      rw [← Category.assoc sq.inl sq.ι b, il, whisker_one_face, Category.assoc]
    · rw [← Category.assoc, gr, hb, ← Category.assoc, ir]
  have ha : SSet.anodyneExtensions sq.ι :=
    SSet.anodyneExtensions_pushoutObjObjι sq (anodyne_delta_one 0)
  let : HasLiftingProperty sq.ι p :=
    ha _ (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let c : CommSq g sq.ι p b := ⟨hg⟩
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · have he : K ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ c.lift =
        fst K (Δ[0] : SSet.{u}) ≫ f := by
      rw [← il, Category.assoc, c.fac_left, gl]
    have hz := congrArg (fun k => zeroFaceSection K ≫ k) he
    simpa only [← Category.assoc, zeroFaceSection_one_face, zeroFaceSection_fst,
      Category.id_comp] using hz
  · rw [← ir, Category.assoc, c.fac_left, gr]

end

end Thomason.Construction

end

section

/-!
# Strict stationarity on the old subposet

The equation is proved on the whole old cylinder, including every lower
cell. This is what permits relative prisms to descend through arbitrary
attaching pushouts.
-/

namespace Thomason.Construction.RelativePrismData

open CategoryTheory CategoryTheory.Limits Opposite NormalizedSimplexIdentities

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput] (G : RightGrayInput h)

/-- A local piece lying entirely in the old subposet is strictly stationary. -/
theorem piece_stationary {m : ℕ} (s : Fin (m + 1) →o E) (hs : ∀ i, s i ∈ D.old) :
    D.piece h G s = G.projection.app (h.object m) ≫ h.posetLeg (D.first.comp s) := by
  let p : G.cylinder.obj (h.object m) ⟶ h.object (D.ordinal s).dim :=
    G.prism (D.old_preimage_lower s) (D.firstIndex s) (D.lastIndex s)
      (D.index_le s) (D.index_agree s) (D.index_constant s)
  let v : h.object (D.ordinal s).dim ⟶ h.categorification.obj (nerve E) :=
    h.posetLeg (D.evaluate s)
  have hp : G.cylinder.map (h.map (OrderHom.id : Fin (m + 1) →o Fin (m + 1))) ≫ p =
      G.projection.app (h.object m) ≫ h.map ((D.firstIndex s).comp OrderHom.id) :=
    G.prism_stationary (D.old_preimage_lower s) (D.firstIndex s) (D.lastIndex s)
      (D.index_le s) (D.index_agree s) (D.index_constant s) OrderHom.id hs
  have hid : G.cylinder.map (h.map (OrderHom.id : Fin (m + 1) →o Fin (m + 1))) =
      𝟙 (G.cylinder.obj (h.object m)) := by
    rw [h.map_id, G.cylinder.map_id]
  have he : (D.evaluate s).comp (D.firstIndex s) = D.first.comp s := by
    apply DFunLike.ext
    exact D.evaluate_firstIndex s
  have hp' : p = G.projection.app (h.object m) ≫ h.map (D.firstIndex s) := by
    simpa only [hid, Category.id_comp, OrderHom.comp_id] using hp
  have hv : h.map (D.firstIndex s) ≫ v = h.posetLeg (D.first.comp s) :=
    (h.posetLeg_precomp _ _).trans (congrArg h.posetLeg he)
  calc
    _ = p ≫ v := (Category.assoc _ _ _).symm
    _ = (G.projection.app (h.object m) ≫ h.map (D.firstIndex s)) ≫ v :=
      congrArg (fun k => k ≫ v) hp'
    _ = G.projection.app (h.object m) ≫ (h.map (D.firstIndex s) ≫ v) := Category.assoc _ _ _
    _ = _ := congrArg (fun k => G.projection.app (h.object m) ≫ k) hv

/-- The monotone inclusion of the old subposet. -/
def oldInclusion : D.old →o E where
  toFun := Subtype.val
  monotone' := fun _ _ hij => hij

/-- The whole assembled cylinder is stationary on the old subposet. -/
theorem prism_stationary :
    G.cylinder.map (h.categorification.map (nerveMap D.oldInclusion.monotone.functor)) ≫ D.prism h G =
      G.projection.app (h.categorification.obj (nerve D.old)) ≫
        h.categorification.map (nerveMap (D.first.comp D.oldInclusion).monotone.functor) := by
  apply G.assembled_stationary (h.simplexCocone_isColimit (nerve D.old))
  intro j
  let s := simplexOrder (SSet.yonedaEquiv j.hom)
  have hj : h.posetLeg s = h.simplexLeg j.hom := h.posetLeg_simplexOrder j.hom
  have hi : h.simplexLeg j.hom ≫ h.categorification.map (nerveMap D.oldInclusion.monotone.functor) =
      h.posetLeg (D.oldInclusion.comp s) := by
    calc
      _ = h.posetLeg s ≫ h.categorification.map (nerveMap D.oldInclusion.monotone.functor) :=
        congrArg (fun k => k ≫ _) hj.symm
      _ = _ := h.posetLeg_postcomp s D.oldInclusion
  have hv : h.simplexLeg j.hom ≫
      h.categorification.map (nerveMap (D.first.comp D.oldInclusion).monotone.functor) =
      h.posetLeg (D.first.comp (D.oldInclusion.comp s)) := by
    calc
      _ = h.posetLeg s ≫
          h.categorification.map (nerveMap (D.first.comp D.oldInclusion).monotone.functor) :=
        congrArg (fun k => k ≫ _) hj.symm
      _ = _ := h.posetLeg_postcomp s (D.first.comp D.oldInclusion)
  change G.cylinder.map (h.simplexLeg j.hom ≫ _) ≫ D.prism h G =
    G.projection.app (h.object j.left.len) ≫ (h.simplexLeg j.hom ≫ _)
  calc
    _ = G.cylinder.map (h.posetLeg (D.oldInclusion.comp s)) ≫ D.prism h G :=
      congrArg (fun k => G.cylinder.map k ≫ D.prism h G) hi
    _ = D.piece h G (D.oldInclusion.comp s) := D.prism_fac_poset h G _
    _ = G.projection.app (h.object j.left.len) ≫
        h.posetLeg (D.first.comp (D.oldInclusion.comp s)) :=
      D.piece_stationary h G _ (fun i => (s i).property)
    _ = _ := congrArg (fun k => G.projection.app (h.object j.left.len) ≫ k) hv.symm

end Thomason.Construction.RelativePrismData

end

section

/-!
# The assembled relative prism in every positive finite dimension

The construction uses the already stated published reflection adjunction
and preservation of target dimension by the right internal hom. Endpoints
and stationarity are transported by their universal properties.
-/

namespace Thomason.Construction

open CategoryTheory

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)

/-- Reflection units detect maps to every finite-dimensional target. -/
theorem unit_hom_ext (X : StrictOmegaCategory.{0})
    (Y : StrictOmegaCategory.Truncated.{0} (n + 1))
    {f g : (r.reflect.obj X).val ⟶ Y.val}
    (he : r.adjunction.unit.app X ≫ f = r.adjunction.unit.app X ≫ g) : f = g := by
  let e : ((r.reflect.obj X).val ⟶ Y.val) ≃ (X ⟶ Y.val) := r.adjunction.homEquiv X Y
  apply e.injective
  exact (r.adjunction.homEquiv_apply X Y f).trans
    (he.trans (r.adjunction.homEquiv_apply X Y g).symm)

end FiniteReflectionInput

namespace RightGrayInput

variable {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
  (t : GrayTruncationInput G) {n : ℕ} (r : FiniteReflectionInput n)

include t

/-- Descent preserves strict stationarity, as an equation on the whole
reflected cylinder. -/
theorem factor_cylinder_stationary (A X : StrictOmegaCategory.{0})
    (i v : A ⟶ X) (P : G.cylinder.obj X ⟶ X)
    (Q : G.cylinder.obj (r.reflect.obj X).val ⟶ (r.reflect.obj X).val)
    (hQ : G.cylinder.map (r.adjunction.unit.app X) ≫ Q = P ≫ r.adjunction.unit.app X)
    (hP : G.cylinder.map i ≫ P = G.projection.app A ≫ v) :
    G.cylinder.map ((StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map i)) ≫ Q =
      G.projection.app (r.reflect.obj A).val ≫
        (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map v) := by
  let qA : A ⟶ (r.reflect.obj A).val := r.adjunction.unit.app A
  let qX : X ⟶ (r.reflect.obj X).val := r.adjunction.unit.app X
  let ri : (r.reflect.obj A).val ⟶ (r.reflect.obj X).val :=
    (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map i)
  let rv : (r.reflect.obj A).val ⟶ (r.reflect.obj X).val :=
    (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map v)
  have hi : i ≫ qX = qA ≫ ri := r.adjunction.unit.naturality i
  have hv : v ≫ qX = qA ≫ rv := r.adjunction.unit.naturality v
  apply (G.cylinderRestrictionEquiv t r A (r.reflect.obj X)).injective
  exact (G.cylinderRestrictionEquiv_apply t r _ _ _).trans ((calc
    G.cylinder.map qA ≫ (G.cylinder.map ri ≫ Q)
        = G.cylinder.map (qA ≫ ri) ≫ Q := by rw [G.cylinder.map_comp, Category.assoc]
    _ = G.cylinder.map (i ≫ qX) ≫ Q := congrArg (fun f => G.cylinder.map f ≫ Q) hi.symm
    _ = G.cylinder.map i ≫ (G.cylinder.map qX ≫ Q) := by rw [G.cylinder.map_comp, Category.assoc]
    _ = G.cylinder.map i ≫ (P ≫ qX) := congrArg (fun f => G.cylinder.map i ≫ f) hQ
    _ = (G.cylinder.map i ≫ P) ≫ qX := (Category.assoc _ _ _).symm
    _ = (G.projection.app A ≫ v) ≫ qX := congrArg (fun f => f ≫ qX) hP
    _ = G.projection.app A ≫ (qA ≫ rv) := (Category.assoc _ _ _).trans
      (congrArg (fun f => G.projection.app A ≫ f) hv)
    _ = (G.cylinder.map qA ≫ G.projection.app (r.reflect.obj A).val) ≫ rv :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ rv) (G.projection.naturality qA).symm)
    _ = G.cylinder.map qA ≫ (G.projection.app (r.reflect.obj A).val ≫ rv) := Category.assoc _ _ _
    ).trans (G.cylinderRestrictionEquiv_apply t r _ _ _).symm)

end RightGrayInput

namespace RelativePrismData

variable {E : Type} [PartialOrder E] (D : RelativePrismData E)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]
  (G : RightGrayInput h) (t : GrayTruncationInput G) {n : ℕ} (r : FiniteReflectionInput n)

/-- Compose the omega prism with the finite reflection unit, then descend
its source cylinder by the published internal-hom truncation theorem. -/
noncomputable def finitePrism :
    G.cylinder.obj (r.reflect.obj (h.categorification.obj (nerve E))).val ⟶
      (r.reflect.obj (h.categorification.obj (nerve E))).val :=
  (G.cylinderRestrictionEquiv t r _ _).symm
    (D.prism h G ≫ r.adjunction.unit.app (h.categorification.obj (nerve E)))

theorem finitePrism_restrict :
    G.cylinder.map (r.adjunction.unit.app (h.categorification.obj (nerve E))) ≫
      D.finitePrism h G t r = D.prism h G ≫ r.adjunction.unit.app (h.categorification.obj (nerve E)) := by
  let e := G.cylinderRestrictionEquiv t r (h.categorification.obj (nerve E))
    (r.reflect.obj (h.categorification.obj (nerve E)))
  exact (G.cylinderRestrictionEquiv_apply t r _ _ _).symm.trans (e.apply_symm_apply _)

/-- The descended endpoints are the actual finite categorification maps. -/
theorem finitePrism_endpoint (a : Bool) :
    (G.endpoint a).app (r.reflect.obj (h.categorification.obj (nerve E))).val ≫
      D.finitePrism h G t r =
    (StrictOmegaCategory.inclusion (n + 1)).map
      (r.reflect.map (h.posetMap (if a then D.last else D.first))) := by
  apply r.unit_hom_ext (h.categorification.obj (nerve E))
  have hp := G.factor_cylinder_endpoint r (h.categorification.obj (nerve E))
    (r.reflect.obj (h.categorification.obj (nerve E)))
    (D.prism h G ≫ r.adjunction.unit.app (h.categorification.obj (nerve E)))
    (D.finitePrism h G t r) (D.finitePrism_restrict h G t r) a
  exact hp.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ r.adjunction.unit.app _) (D.prism_endpoint h G a)).trans
      (r.adjunction.unit.naturality (h.posetMap (if a then D.last else D.first)))))

/-- The finite relative prism is stationary on the entire reflected old cylinder. -/
theorem finitePrism_stationary :
    G.cylinder.map ((StrictOmegaCategory.inclusion (n + 1)).map
      (r.reflect.map (h.posetMap D.oldInclusion))) ≫ D.finitePrism h G t r =
    G.projection.app (r.reflect.obj (h.categorification.obj (nerve D.old))).val ≫
      (StrictOmegaCategory.inclusion (n + 1)).map
        (r.reflect.map (h.posetMap (D.first.comp D.oldInclusion))) :=
  G.factor_cylinder_stationary t r _ _ _ _ (D.prism h G) (D.finitePrism h G t r)
    (D.finitePrism_restrict h G t r) (D.prism_stationary h G)

end RelativePrismData
end Thomason.Construction

end

section

/-! # The two stationary cylinders for a greatest new element -/

namespace Thomason.Construction.SieveRetraction

open CategoryTheory

variable {E : Type} [PartialOrder E] {A : Set E} (R : SieveRetraction A)
  {x : E} (hx : GreatestNew (A := A) x)

noncomputable def upperPrismData : RelativePrismData E where
  old := A
  lower := R.lower
  first := OrderHom.id
  last := R.upperCollapse hx
  le := R.identity_le_upperCollapse hx
  agree := fun _ ha => (R.upperCollapse_old hx ha).symm
  constant := fun _ ha _ hb => (R.upperCollapse_new hx ha).trans (R.upperCollapse_new hx hb).symm

noncomputable def lowerPrismData : RelativePrismData E where
  old := A
  lower := R.lower
  first := R.oldCollapse hx
  last := R.upperCollapse hx
  le := R.oldCollapse_le_upperCollapse hx
  agree := fun _ ha => (R.oldCollapse_old hx ha).trans (R.upperCollapse_old hx ha).symm
  constant := fun _ ha _ hb => (R.upperCollapse_new hx ha).trans (R.upperCollapse_new hx hb).symm

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput] (G : RightGrayInput h)

/-- The common upper map gives two strict cylinders, both stationary on
all cells of the old part. Their endpoints are `id ≤ upper ≥ lower`. -/
theorem greatest_new_cylinders :
    ∃ P Q : G.cylinder.obj (h.categorification.obj (nerve E)) ⟶ h.categorification.obj (nerve E),
      (G.endpoint false).app _ ≫ P = 𝟙 _ ∧
      (G.endpoint true).app _ ≫ P = h.posetMap (R.upperCollapse hx) ∧
      (G.endpoint false).app _ ≫ Q = h.posetMap (R.oldCollapse hx) ∧
      (G.endpoint true).app _ ≫ Q = h.posetMap (R.upperCollapse hx) ∧
      G.cylinder.map (h.posetMap (subposetInclusion A)) ≫ P =
        G.projection.app _ ≫ h.posetMap (subposetInclusion A) ∧
      G.cylinder.map (h.posetMap (subposetInclusion A)) ≫ Q =
        G.projection.app _ ≫ h.posetMap (subposetInclusion A) := by
  let D := R.upperPrismData hx
  let D' := R.lowerPrismData hx
  refine ⟨D.prism h G, D'.prism h G, ?_, D.prism_endpoint h G true,
    D'.prism_endpoint h G false, D'.prism_endpoint h G true, ?_, ?_⟩
  · exact (D.prism_endpoint h G false).trans (h.posetMap_id E)
  · have hs := D.prism_stationary h G
    have he : D.first.comp D.oldInclusion = subposetInclusion A := by rfl
    exact hs.trans (congrArg (fun f => G.projection.app _ ≫ h.posetMap f) he)
  · have hs := D'.prism_stationary h G
    have he : D'.first.comp D'.oldInclusion = subposetInclusion A := by
      apply DFunLike.ext
      intro a
      exact R.oldCollapse_old hx a.property
    exact hs.trans (congrArg (fun f => G.projection.app _ ≫ h.posetMap f) he)

/-- The old-valued collapse is an actual retraction after categorification. -/
theorem oldCollapse_posetMap_retraction :
    h.posetMap (subposetInclusion A) ≫ h.posetMap (R.oldCollapseRetraction hx) = 𝟙 _ ∧
      h.posetMap (R.oldCollapseRetraction hx) ≫ h.posetMap (subposetInclusion A) =
        h.posetMap (R.oldCollapse hx) := by
  constructor
  · have he : (R.oldCollapseRetraction hx).comp (subposetInclusion A) = OrderHom.id := by
      apply DFunLike.ext
      exact R.oldCollapseRetraction_coe hx
    exact (h.posetMap_comp _ _).symm.trans
      ((congrArg h.posetMap he).trans (h.posetMap_id A))
  · exact (h.posetMap_comp _ _).symm

end Thomason.Construction.SieveRetraction

end

section

/-! # Constructed simplex atoms and composition generation

The recursive cone cells satisfy Steiner's entire signed-part table formula.
The composition-generation assertion is separated from these explicit formulas.
-/

namespace Thomason.Construction

namespace SimplexComplex

/-- The two parts of a boundary with distinct positive and negative basis terms. -/
theorem signedPart_single_sub {m p : ℕ} (a : Bool) (b c : Basis m p) (hbc : b ≠ c) :
    signedPart a (Finsupp.single b 1 - Finsupp.single c 1) =
      if a then Finsupp.single b 1 else Finsupp.single c 1 := by
  classical
  apply Finsupp.ext
  intro t
  cases a <;> by_cases hb : t = b <;> by_cases hc : t = c <;>
    simp_all [signedPart]

/-- The bottom chains of the constructed principal cells are their endpoint vertices. -/
theorem principalCell_bottom (h : NormalizedSimplexIdentities) (m : ℕ) (a : Bool) :
    (principalCell h m).table a 0 =
      if a then Finsupp.single (vertexBasis (Fin.last m)) 1
        else Finsupp.single (vertexBasis 0) 1 := by
  cases a with
  | false =>
    exact congrArg (fun x : h.object m => x.table false 0) (principalCell_source h m)
  | true =>
    exact congrArg (fun x : h.object m => x.table false 0) (principalCell_target h m)

/-- The zero-dimensional signed-boundary formula follows from the two distinct endpoints. -/
theorem principalCell_signedPart_zero (h : NormalizedSimplexIdentities) (m : ℕ) (a : Bool) :
    signedPart a (differential (m + 1) 0 ((principalCell h (m + 1)).table a 1)) =
      (principalCell h (m + 1)).table a 0 := by
  have hb : differential (m + 1) 0 ((principalCell h (m + 1)).table a 1) =
      (principalCell h (m + 1)).table true 0 - (principalCell h (m + 1)).table false 0 :=
    (principalCell h (m + 1)).boundary a 0
  have hne : vertexBasis (Fin.last (m + 1)) ≠ vertexBasis (0 : Fin (m + 2)) := by
    intro he
    have hv := congrArg (fun b : Basis (m + 1) 0 => (b 0).val) he
    change m + 1 = 0 at hv
    omega
  have ht : (principalCell h (m + 1)).table true 0 =
      Finsupp.single (vertexBasis (Fin.last (m + 1))) 1 := principalCell_bottom h _ true
  have hs : (principalCell h (m + 1)).table false 0 =
      Finsupp.single (vertexBasis 0) 1 := principalCell_bottom h _ false
  have hd := hb.trans (congrArg₂ (· - ·) ht hs)
  exact (congrArg (signedPart a) hd).trans
    ((signedPart_single_sub a _ _ hne).trans (principalCell_bottom h _ a).symm)

/-- The entire downward-recursive atom table is proved, not postulated. -/
theorem principalCell_isBasisAtom (h : NormalizedSimplexIdentities) (m : ℕ) :
    IsBasisAtom h (topBasis m) (principalCell h m) := by
  induction m with
  | zero =>
    refine ⟨principalCell_top h 0, ?_, ?_⟩
    · intro a n hn
      omega
    · intro a n hn
      exact NormalizedSimplexIdentities.chains_eq_zero_above hn _
  | succ m ih =>
    refine ⟨principalCell_top h (m + 1), ?_, ?_⟩
    · intro a n hn
      cases n with
      | zero => exact (principalCell_signedPart_zero h m a).symm
      | succ p =>
        exact (coneCell_signedPart h (principalCell h m) p
          (fun b => (ih.2.1 b p (by omega)).symm) a).symm
    · intro a n hn
      exact NormalizedSimplexIdentities.chains_eq_zero_above hn _

end SimplexComplex

/-- Steiner 2004, Theorem 5.6, restricted to generation by the simplex atoms
explicitly constructed here. Atom existence, tables and endpoints are proved. -/
structure PublishedSimplexGenerationInput (h : NormalizedSimplexIdentities) : Prop where
  generated (m : ℕ) (P : h.object m → Prop)
    (atoms : ∀ p (b : SimplexComplex.Basis m p),
      P ((h.map b.toOrderHom).toFun (SimplexComplex.principalCell h p)))
    (compositions : ∀ n x y hxy, P x → P y → P ((h.object m).comp n x y hxy)) :
    ∀ x, P x

/-- The signed-part formulas and composition generation give the simplex-atom data. -/
noncomputable def PublishedSimplexGenerationInput.toSimplexAtomsInput
    {h : NormalizedSimplexIdentities} (g : PublishedSimplexGenerationInput h) : SimplexAtomsInput h where
  principal := SimplexComplex.principalCell h
  principal_table := SimplexComplex.principalCell_isBasisAtom h
  principal_source := SimplexComplex.principalCell_source h
  principal_target := SimplexComplex.principalCell_target h
  generated := g.generated

end Thomason.Construction

end

section

/-! # The full table formula for every constructed simplex atom

An injective vertex map acts by an actual embedding of normalized bases.
It therefore commutes with signed parts. Applying it to a principal atom
constructs the required basis atom without a generation premise.
-/

namespace Thomason.Construction.SimplexComplex

/-- Postcomposition with an increasing tuple embeds every normalized basis. -/
def basisPostcompose {m p : ℕ} (b : Basis m p) (q : ℕ) : Basis p q ↪ Basis m q where
  toFun s := s.trans b
  inj' s t he := by
    apply DFunLike.ext
    intro i
    exact b.injective (congrArg (fun c : Basis m q => c i) he)

/-- An injective simplex operator has no degenerate or colliding images. -/
theorem mapChains_embedding {m p q : ℕ} (b : Basis m p) (x : Chains p q) :
    mapChains b.toOrderHom q x = Finsupp.embDomain (basisPostcompose b q) x := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add s z x _ _ ih =>
    have hs : mapBasis b.toOrderHom q s = Finsupp.single (s.trans b) 1 := by
      have hm : StrictMono (fun i => b.toOrderHom (s i)) := by
        intro i j hij
        exact b.strictMono (s.strictMono hij)
      rw [mapBasis, dite_eq_left hm]
      rfl
    simp only [map_add, mapChains_single, hs, ih, Finsupp.embDomain_add,
      Finsupp.embDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl

/-- Signed parts commute with these actual basis embeddings. -/
theorem mapChains_embedding_signedPart {m p q : ℕ} (b : Basis m p) (side : Bool)
    (x : Chains p q) :
    mapChains b.toOrderHom q (signedPart side x) =
      signedPart side (mapChains b.toOrderHom q x) := by
  rw [mapChains_embedding, mapChains_embedding]
  exact Finsupp.embDomain_mapRange (basisPostcompose b q)
    (fun z => max 0 (if side then z else -z)) x (by cases side <;> simp)

/-- Every face image of the principal atom satisfies the full recursive
signed-boundary table formula. -/
theorem basisAtom_embedding (h : NormalizedSimplexIdentities) {m p : ℕ}
    (b : Basis m p) (x : h.object p) (hx : IsBasisAtom h (topBasis p) x) :
    IsBasisAtom h b ((h.map b.toOrderHom).toFun x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro side
    change mapChains b.toOrderHom p (x.table side p) = _
    rw [hx.1 side, mapChains_embedding, Finsupp.embDomain_single]
    rfl
  · intro side n hn
    change mapChains b.toOrderHom n (x.table side n) =
      signedPart side (differential m n (mapChains b.toOrderHom (n+1) (x.table side (n+1))))
    rw [hx.2.1 side n hn, mapChains_embedding_signedPart]
    exact congrArg (signedPart side) ((h.naturality b.toOrderHom) n (x.table side (n+1)))
  · intro side n hn
    change mapChains b.toOrderHom n (x.table side n) = 0
    rw [hx.2.2 side n hn, map_zero]

/-- The concrete atom attached to any normalized basis element. -/
noncomputable def basisAtom (h : NormalizedSimplexIdentities) {m p : ℕ} (b : Basis m p) :
    h.object m := (h.map b.toOrderHom).toFun (principalCell h p)

theorem basisAtom_isBasisAtom (h : NormalizedSimplexIdentities) {m p : ℕ} (b : Basis m p) :
    IsBasisAtom h b (basisAtom h b) :=
  basisAtom_embedding h b (principalCell h p) (principalCell_isBasisAtom h p)

end Thomason.Construction.SimplexComplex

end

section

/-! # Positive residual chains below a simplex atom

Agreement above a degree identifies the differences of the two boundaries.
The disjoint signed supports of an atom then make the residual positive.
At degree zero its augmentation is zero, so the residual vanishes.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- A positive zero-chain of augmentation zero vanishes coefficientwise. -/
theorem positive_augmentation_zero {m : ℕ} (z : Chains m 0)
    (hz : z ∈ positive m 0) (he : augmentation m z = 0) : z = 0 := by
  classical
  have hs : ∑ b ∈ z.support, z b = 0 := by
    simpa [augmentation, Finsupp.linearCombination_apply, Finsupp.sum] using he
  apply Finsupp.ext
  intro b
  by_cases hb : b ∈ z.support
  · have hle := Finset.single_le_sum (fun c (_ : c ∈ z.support) => hz c) hb
    rw [hs] at hle
    exact le_antisymm hle (hz b)
  · exact Finsupp.notMem_support_iff.mp hb

/-- Equal next-degree chains give the same residual on both sides. -/
theorem atom_residual_sides {h : NormalizedSimplexIdentities} {m : ℕ}
    (X A : h.object m) (r : ℕ)
    (he : X.table false (r+1) = A.table false (r+1)) :
    X.table false r - A.table false r = X.table true r - A.table true r := by
  have hd := congrArg (differential m r) he
  change (directedComplex m (h.squared m)).differential r (X.table false (r+1)) =
    (directedComplex m (h.squared m)).differential r (A.table false (r+1)) at hd
  rw [X.boundary, A.boundary] at hd
  apply sub_eq_zero.mp
  calc
    _ = (A.table true r - A.table false r) -
        (X.table true r - X.table false r) := by abel
    _ = 0 := by rw [hd, sub_self]

/-- The extra chain below a common atom is positive; no generation input
is needed for this subtraction. -/
theorem atom_residual_positive {h : NormalizedSimplexIdentities} {m p : ℕ}
    {b : Basis m p} (X A : h.object m) (hA : IsBasisAtom h b A)
    (r : ℕ) (hr : r < p)
    (he : X.table false (r+1) = A.table false (r+1)) :
    X.table false r - A.table false r ∈ positive m r := by
  have hs := atom_residual_sides X A r he
  intro c
  have hdis := ordered_basisAtoms_disjoint hA hA hr hr le_rfl c
  rcases hdis with hneg | hpos
  · simpa only [Finsupp.sub_apply, hneg, sub_zero] using X.positive false r c
  · rw [hs]
    simpa only [Finsupp.sub_apply, hpos, sub_zero] using X.positive true r c

/-- There is no lower-dimensional freedom below the zero-chains of an
atom: augmentation one removes the positive residual. -/
theorem eq_atom_of_above_zero {h : NormalizedSimplexIdentities} {m p : ℕ}
    {b : Basis m p} (X A : h.object m) (hA : IsBasisAtom h b A) (hp : 0 < p)
    (he : ∀ n, 0 < n → ∀ side, X.table side n = A.table side n) : X = A := by
  have hr := atom_residual_positive X A hA 0 hp (he 1 (by omega) false)
  have haug : augmentation m (X.table false 0 - A.table false 0) = 0 := by
    change (directedComplex m (h.squared m)).augmentation
      (X.table false 0 - A.table false 0) = 0
    rw [map_sub, X.augmentation, A.augmentation, sub_self]
  have hzero := positive_augmentation_zero _ hr haug
  have hfalse : X.table false 0 = A.table false 0 := sub_eq_zero.mp hzero
  have htrue : X.table true 0 = A.table true 0 := by
    apply sub_eq_zero.mp
    rw [← atom_residual_sides X A 0 (he 1 (by omega) false), hzero]
  apply DirectedComplex.Cell.ext
  funext side n
  cases n with
  | zero => cases side <;> assumption
  | succ n => exact he (n+1) (by omega) side

end Thomason.Construction.SimplexComplex

end

section

/-! # Positive chains as finite lists of actual simplex atoms

Coefficients give literal repeated atoms. Sorting those lists by the
signed-boundary height supplies the disjointness used by cell splitting.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators
open _root_.OAI.Thomason.Construction.DirectedComplex

/-- An atom retains both its degree and its increasing vertex tuple. -/
abbrev AtomIndex (m : ℕ) := Σ p, Basis m p

noncomputable def atomCell (h : NormalizedSimplexIdentities) {m : ℕ}
    (a : AtomIndex m) : Cell (directedComplex m (h.squared m)) := basisAtom h a.2

def atomHeight {m : ℕ} (a : AtomIndex m) : ℤ := basisHeight a.2

theorem atomCell_isBasisAtom (h : NormalizedSimplexIdentities) {m : ℕ}
    (a : AtomIndex m) : IsBasisAtom h a.2 (atomCell h a) := basisAtom_isBasisAtom h a.2

/-- A finite integral positive chain specifies a finite list of atoms. -/
noncomputable def chainAtomIndices {m p : ℕ} (z : Chains m p) : List (AtomIndex m) :=
  z.support.toList.flatMap (fun b => List.replicate (z b).toNat ⟨p, b⟩)

theorem chainAtomIndices_degree {m p : ℕ} (z : Chains m p)
    (a : AtomIndex m) (ha : a ∈ chainAtomIndices z) : a.1 = p := by
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp ha
  obtain ⟨_, he⟩ := List.mem_replicate.mp hb
  subst a
  rfl

private theorem sum_map_flatMap {α β M : Type*} [AddMonoid M]
    (as : List α) (f : α → List β) (g : β → M) :
    ((as.flatMap f).map g).sum = (as.map (fun a => ((f a).map g).sum)).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

/-- The top chains of the listed atoms sum to precisely the original chain. -/
theorem chainAtomIndices_table (h : NormalizedSimplexIdentities) {m p : ℕ}
    (z : Chains m p) (hz : z ∈ positive m p) (side : Bool) :
    (Cell.PositiveTable.ofCells ((chainAtomIndices z).map (atomCell h))).table side p = z := by
  classical
  rw [Cell.PositiveTable.ofCells_table]
  rw [List.map_map]
  unfold chainAtomIndices
  rw [sum_map_flatMap]
  simp only [List.map_replicate, List.sum_replicate]
  change (z.support.toList.map (fun b =>
    (z b).toNat • (atomCell h ⟨p,b⟩).table side p)).sum = z
  have ht (b : Basis m p) : (atomCell h ⟨p,b⟩).table side p = Finsupp.single b 1 :=
    (atomCell_isBasisAtom h ⟨p,b⟩).1 side
  simp_rw [ht]
  rw [Finset.sum_map_toList]
  calc
    ∑ b ∈ z.support, (z b).toNat • Finsupp.single b (1 : ℤ) =
        ∑ b ∈ z.support, Finsupp.single b (z b) := by
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finsupp.smul_single, nsmul_eq_mul, mul_one, Int.toNat_of_nonneg (hz b)]
    _ = z := Finsupp.sum_single z

/-- No listed atom contributes above the degree of the chain. -/
theorem chainAtomIndices_above (h : NormalizedSimplexIdentities) {m p : ℕ}
    (z : Chains m p) (n : ℕ) (hn : p < n) (side : Bool) :
    (Cell.PositiveTable.ofCells ((chainAtomIndices z).map (atomCell h))).table side n = 0 := by
  rw [Cell.PositiveTable.ofCells_table]
  rw [List.map_map]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
  exact (atomCell_isBasisAtom h a).2.2 side n
    (by rw [chainAtomIndices_degree z a ha]; exact hn)

/-- Height sorting is a permutation, so it retains every positive table. -/
noncomputable def sortAtoms {m : ℕ} (as : List (AtomIndex m)) : List (AtomIndex m) :=
  as.mergeSort (fun a b => decide (atomHeight a ≤ atomHeight b))

theorem sortAtoms_perm {m : ℕ} (as : List (AtomIndex m)) : (sortAtoms as).Perm as :=
  List.mergeSort_perm _ _

theorem sortAtoms_pairwise {m : ℕ} (as : List (AtomIndex m)) :
    (sortAtoms as).Pairwise (fun a b => atomHeight a ≤ atomHeight b) := by
  simpa only [sortAtoms, decide_eq_true_eq] using
    (List.pairwise_mergeSort
      (le := fun a b : AtomIndex m => decide (atomHeight a ≤ atomHeight b))
      (fun a b c hab hbc => by
        simpa only [decide_eq_true_eq] using le_trans
          (of_decide_eq_true hab) (of_decide_eq_true hbc))
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) as)

theorem sortAtoms_table (h : NormalizedSimplexIdentities) {m : ℕ}
    (as : List (AtomIndex m)) (side : Bool) (n : ℕ) :
    (Cell.PositiveTable.ofCells ((sortAtoms as).map (atomCell h))).table side n =
      (Cell.PositiveTable.ofCells (as.map (atomCell h))).table side n := by
  simp only [Cell.PositiveTable.ofCells_table]
  simp only [List.map_map]
  exact ((sortAtoms_perm as).map (fun a => (atomCell h a).table side n)).sum_eq

end Thomason.Construction.SimplexComplex

end

section

/-! # The concrete ordered basis of every normalized simplex complex -/

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

/-- Every field is the corresponding literal normalized-chain construction.
No generation assertion is required by this interface. -/
noncomputable def orderedAtomBasis (h : NormalizedSimplexIdentities) (m : ℕ) :
    OrderedAtomBasis (directedComplex m (h.squared m)) where
  Index p := Basis m p
  coordinates _ := AddEquiv.refl _
  positive_iff _ _ := Iff.rfl
  augmentation x := by
    simp [directedComplex, augmentation, Finsupp.linearCombination_apply, Finsupp.sum]
  atom _ b := basisAtom h b
  atom_top _ b side := (basisAtom_isBasisAtom h b).1 side
  atom_above _ b n hn side := (basisAtom_isBasisAtom h b).2.2 side n hn
  height _ b := basisHeight b
  disjoint b c hrp hrq hbc e :=
    ordered_basisAtoms_disjoint (basisAtom_isBasisAtom h b) (basisAtom_isBasisAtom h c)
      hrp hrq hbc e

end Thomason.Construction.SimplexComplex

end

section

/-! # Generation of the actual simplex-chain cylinders

The atoms are the two endpoint copies of the simplex atoms and their
actual mixed prisms. Their signed heights instantiate the proved ordered
generation theorem, without a freeness or tensor-preservation premise.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

noncomputable def cylinderOrderedAtomBasis (hs : B.SideHeight) :
    OrderedAtomBasis (rightCylinder K) where
  Index p := B.CylinderIndex p
  coordinates := B.cylinderCoordinates
  positive_iff := B.cylinder_positive_iff
  augmentation := B.cylinder_augmentation
  atom _ := B.cylinderAtom
  atom_top _ := B.cylinderAtom_top
  atom_above _ := B.cylinderAtom_above
  height _ := RightCylinderBasis.height B.height
  disjoint b c hrp hrq hbc e := B.cylinder_atoms_disjoint hs b c hrp hrq hbc e

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

namespace Thomason.Construction.SimplexComplex

open _root_.OAI.Thomason.Construction.DirectedComplex

theorem orderedAtomBasis_sideHeight (h : NormalizedSimplexIdentities) (m : ℕ) :
    (orderedAtomBasis h m).SideHeight := by
  intro p b q hqp side c hc
  exact basisAtom_side_height (basisAtom_isBasisAtom h b) side q hqp c
    (Finsupp.mem_support_iff.mpr hc)

/-- The concrete right interval tensor on each normalized simplex has
an actual ordered atom basis, including all mixed prisms. -/
noncomputable def cylinderOrderedAtomBasis (h : NormalizedSimplexIdentities) (m : ℕ) :
    OrderedAtomBasis (rightCylinder (directedComplex m (h.squared m))) :=
  (orderedAtomBasis h m).cylinderOrderedAtomBasis (orderedAtomBasis_sideHeight h m)

/-- Every strict cell of the actual simplex-chain cylinder is generated
by its explicit endpoint atoms and mixed prism atoms. -/
theorem cylinder_generated (h : NormalizedSimplexIdentities) (m : ℕ)
    (P : Cell (rightCylinder (directedComplex m (h.squared m))) → Prop)
    (hatom : ∀ p b, P ((cylinderOrderedAtomBasis h m).atom p b))
    (hcomp : ∀ n x y hxy, P x → P y → P (Cell.comp x y n hxy)) : ∀ X, P X :=
  (cylinderOrderedAtomBasis h m).generated P hatom hcomp

end Thomason.Construction.SimplexComplex

end

end OAI
