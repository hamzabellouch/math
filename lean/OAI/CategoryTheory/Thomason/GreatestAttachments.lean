import Mathlib
import OAI.CategoryTheory.Thomason.DimensionOne
import OAI.CategoryTheory.Thomason.FiniteChains
import OAI.CategoryTheory.Thomason.IntervalExtension

namespace OAI

/-! Greatest Attachments. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits DirectedComplex NormalizedChains OmegaCategory

namespace FiniteVertexChain
variable {E P : Type u} [PartialOrder E] [PartialOrder P]

lemma map_lift (S : FiniteVertexChain E) (σ : P →o S.vertices) :
    posetCategorificationTableMap P ≫ (complexMap σ).nu ≫ S.lift =
      categorification.map (nerveMap (S.inclusion.comp σ).monotone.functor) := by
  rw [← Category.assoc, ← posetCategorificationTableMap_natural, lift, Category.assoc,
    IsIso.hom_inv_id_assoc, ← categorification.map_comp]
  rfl

end FiniteVertexChain
namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalExtension.{u})
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

def prismLeg (σ : P →o E) :
    T.tensor.obj (categorification.obj (nerve P)) ⟶ categorification.obj (nerve E) :=
  T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P).hom ≫
    (d.finiteCylinderChainMap σ).nu ≫ (d.finiteImage σ).lift

lemma prismLeg_natural (σ : Q →o E) (α : P →o Q) :
    T.tensor.map (categorification.map (nerveMap α.monotone.functor)) ≫ d.prismLeg T σ =
      d.prismLeg T (σ.comp α) := by
  unfold prismLeg
  rw [← Category.assoc, ← T.tensor.map_comp, posetCategorificationTableMap_natural,
    T.tensor.map_comp, Category.assoc, ← Category.assoc (T.tensor.map (complexMap α).nu),
    T.simplex_natural, Category.assoc]
  have hc := congrArg Hom.nu (d.finiteCylinderChainMap_natural σ α)
  change (show (complex P).cylinder.nu ⟶ _ from (d.finiteCylinderChainMap (σ.comp α)).nu) ≫
      (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
        (d.finiteImage_mono σ α))).nu =
      (complexMap α).cylinder.nu ≫ (d.finiteCylinderChainMap σ).nu at hc
  have hcc := congrArg (fun z : (complex P).cylinder.nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P).hom ≫ z ≫
      (d.finiteImage σ).lift) hc
  simp only [Category.assoc, FiniteVertexChain.lift_natural] at hcc
  exact hcc.symm

lemma prismLeg_endpoint_false (σ : P →o E) :
    (T.endpoint false).app (categorification.obj (nerve P)) ≫ d.prismLeg T σ =
      categorification.map (nerveMap (d.f.comp σ).monotone.functor) := by
  unfold prismLeg
  rw [← Category.assoc, ← (T.endpoint false).naturality, Category.assoc,
    ← Category.assoc ((T.endpoint false).app (complex P).nu), T.simplex_endpoint, CategoryTheory.Functor.id_map]
  have hc := congrArg Hom.nu (d.finiteAntihomotopy σ).cylinderHom_endpoint_false
  change (show (complex P).nu ⟶ (complex P).cylinder.nu from ((complex P).cylinderEndpoint false).nu) ≫ (d.finiteCylinderChainMap σ).nu =
    (complexMap (d.finiteImageLeft σ)).nu at hc
  have hcc := congrArg (fun z : (complex P).nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    posetCategorificationTableMap P ≫ z ≫ (d.finiteImage σ).lift) hc
  simp only [Category.assoc] at hcc
  exact hcc.trans ((d.finiteImage σ).map_lift (d.finiteImageLeft σ))

lemma prismLeg_endpoint_true (σ : P →o E) :
    (T.endpoint true).app (categorification.obj (nerve P)) ≫ d.prismLeg T σ =
      categorification.map (nerveMap (d.g.comp σ).monotone.functor) := by
  unfold prismLeg
  rw [← Category.assoc, ← (T.endpoint true).naturality, Category.assoc,
    ← Category.assoc ((T.endpoint true).app (complex P).nu), T.simplex_endpoint, CategoryTheory.Functor.id_map]
  have hc := congrArg Hom.nu (d.finiteAntihomotopy σ).cylinderHom_endpoint_true
  change (show (complex P).nu ⟶ (complex P).cylinder.nu from ((complex P).cylinderEndpoint true).nu) ≫ (d.finiteCylinderChainMap σ).nu =
    (complexMap (d.finiteImageRight σ)).nu at hc
  have hcc := congrArg (fun z : (complex P).nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    posetCategorificationTableMap P ≫ z ≫ (d.finiteImage σ).lift) hc
  simp only [Category.assoc] at hcc
  exact hcc.trans ((d.finiteImage σ).map_lift (d.finiteImageRight σ))

lemma prismLeg_stationary (σ : P →o E) (hs : ∀ p, σ p ∈ A) :
    d.prismLeg T σ = T.projection.app (categorification.obj (nerve P)) ≫
      categorification.map (nerveMap (d.f.comp σ).monotone.functor) := by
  unfold prismLeg
  rw [d.finiteCylinderChainMap_stationary σ hs]
  change T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P).hom ≫
    (complex P).cylinderProjection.nu ≫ (complexMap (d.finiteImageLeft σ)).nu ≫
      (d.finiteImage σ).lift = _
  rw [← Category.assoc (T.simplex P).hom, T.simplex_projection,
    ← Category.assoc (T.tensor.map (posetCategorificationTableMap P)),
    T.projection.naturality, Category.assoc, CategoryTheory.Functor.id_map, FiniteVertexChain.map_lift]
  rfl

def prismCocone : Cocone (posetSimplexDiagram E ⋙ T.tensor) where
  pt := categorification.obj (nerve E)
  ι.app s := d.prismLeg T (simplexVertexOrder s)
  ι.naturality s t α := by
    change T.tensor.map (categorification.map (nerveMap (simplexVertexMap α).monotone.functor)) ≫
      d.prismLeg T (simplexVertexOrder t) = d.prismLeg T (simplexVertexOrder s) ≫ 𝟙 _
    rw [d.prismLeg_natural, simplexVertexOrder_natural, Category.comp_id]

def prism : T.tensor.obj (categorification.obj (nerve E)) ⟶ categorification.obj (nerve E) := by
  letI := T.cocontinuous
  letI : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  exact (isColimitOfPreserves T.tensor (posetSimplexIsColimit E)).desc (d.prismCocone T)

lemma prism_leg (s : SimplexIndex E) :
    T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      d.prism T = d.prismLeg T (simplexVertexOrder s) := by
  let := T.cocontinuous
  let : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  exact (isColimitOfPreserves T.tensor (posetSimplexIsColimit E)).fac (d.prismCocone T) s

lemma prism_endpoint_false :
    (T.endpoint false).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap d.f.monotone.functor) := by
  apply (posetSimplexIsColimit E).hom_ext
  intro s
  change categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (T.endpoint false).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
        categorification.map (nerveMap d.f.monotone.functor)
  have hn := (T.endpoint false).naturality
    (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor))
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc,
    d.prism_leg, d.prismLeg_endpoint_false]
  rw [← categorification.map_comp]
  congr 1

lemma prism_endpoint_true :
    (T.endpoint true).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap d.g.monotone.functor) := by
  apply (posetSimplexIsColimit E).hom_ext
  intro s
  change categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (T.endpoint true).app (categorification.obj (nerve E)) ≫ d.prism T =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
        categorification.map (nerveMap d.g.monotone.functor)
  have hn := (T.endpoint true).naturality
    (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor))
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc,
    d.prism_leg, d.prismLeg_endpoint_true]
  rw [← categorification.map_comp]
  congr 1

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits DirectedComplex NormalizedChains OmegaCategory

def SimplexIndex.postcompose {P E : Type u} [PartialOrder P] [PartialOrder E]
    (v : P →o E) (s : SimplexIndex P) : SimplexIndex E :=
  CostructuredArrow.mk (s.hom ≫ nerveMap v.monotone.functor)

lemma simplexVertexOrder_postcompose {P E : Type u} [PartialOrder P] [PartialOrder E]
    (v : P →o E) (s : SimplexIndex P) :
    simplexVertexOrder (s.postcompose v) = v.comp (simplexVertexOrder s) := by
  ext k
  rfl

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalExtension.{u})

lemma grayPrism_stationary {P : Type u} [PartialOrder P] (v : P →o E) (hv : ∀ p, v p ∈ A) :
    T.tensor.map (categorification.map (nerveMap v.monotone.functor)) ≫ d.prism T =
      T.projection.app (categorification.obj (nerve P)) ≫
        categorification.map (nerveMap (d.f.comp v).monotone.functor) := by
  let := T.cocontinuous
  let : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  apply (isColimitOfPreserves T.tensor (posetSimplexIsColimit P)).hom_ext
  intro s
  change T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      T.tensor.map (categorification.map (nerveMap v.monotone.functor)) ≫ d.prism T =
    T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      T.projection.app (categorification.obj (nerve P)) ≫
        categorification.map (nerveMap (d.f.comp v).monotone.functor)
  rw [← Category.assoc, ← T.tensor.map_comp, ← categorification.map_comp]
  have hvn : nerveMap (simplexVertexOrder s).monotone.functor ≫ nerveMap v.monotone.functor =
      nerveMap (simplexVertexOrder (s.postcompose v)).monotone.functor := by
    rw [simplexVertexOrder_postcompose]
    rfl
  erw [hvn, d.prism_leg, d.prismLeg_stationary T _ (fun p => hv _),
    ← Category.assoc, T.projection.naturality, CategoryTheory.Functor.id_map,
    Category.assoc, ← categorification.map_comp]
  congr 1

lemma grayPrism_stationary_inclusion :
    T.tensor.map (categorification.map (nerveMap (OrderHom.Subtype.val (fun element : E => element ∈ A)).monotone.functor)) ≫
      d.prism T = T.projection.app (categorification.obj (nerve A)) ≫
        categorification.map (nerveMap (d.f.comp (OrderHom.Subtype.val (fun element : E => element ∈ A))).monotone.functor) :=
  d.grayPrism_stationary T (OrderHom.Subtype.val (fun element : E => element ∈ A)) (fun p => p.property)

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits OmegaCategory

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalExtension.{u}) (R : OmegaCategory.{u} ⥤ OmegaCategory.{u})
variable (adj : T.tensor ⊣ R) (n : ℕ)

def finitePrism :
    T.tensor.obj ((categorificationFinite n).obj (nerve E)).val ⟶
      ((categorificationFinite n).obj (nerve E)).val :=
  (T.truncatedCylinderEquiv R adj n (categorification.obj (nerve E))
    ((categorificationFinite n).obj (nerve E)).val
    ((categorificationFinite n).obj (nerve E)).property).symm
      (d.prism T ≫ truncationUnit n (categorification.obj (nerve E)))

lemma finitePrism_unit :
    T.tensor.map (truncationUnit n (categorification.obj (nerve E))) ≫
      d.finitePrism T R adj n = d.prism T ≫ truncationUnit n (categorification.obj (nerve E)) := by
  erw [← T.truncatedCylinderEquiv_apply R adj n _ _
    ((categorificationFinite n).obj (nerve E)).property]
  exact Equiv.apply_symm_apply _ _

lemma finitePrism_endpoint_false :
    (T.endpoint false).app ((categorificationFinite n).obj (nerve E)).val ≫
      d.finitePrism T R adj n = (categorificationFinite n).map (nerveMap d.f.monotone.functor) := by
  apply truncation_functor_ext (n := n)
  have hn := (T.endpoint false).naturality
    (truncationUnit n (categorification.obj (nerve E)))
  exact (congrArg (fun h : categorification.obj (nerve E) ⟶
      T.tensor.obj ((categorificationFinite n).obj (nerve E)).val =>
    h ≫ d.finitePrism T R adj n) hn).trans
      ((congrArg (fun h => (T.endpoint false).app (categorification.obj (nerve E)) ≫ h)
        (d.finitePrism_unit T R adj n)).trans
        (congrArg (fun h : categorification.obj (nerve E) ⟶ categorification.obj (nerve E) =>
          h ≫ truncationUnit n (categorification.obj (nerve E)))
          (d.prism_endpoint_false T)))

lemma finitePrism_endpoint_true :
    (T.endpoint true).app ((categorificationFinite n).obj (nerve E)).val ≫
      d.finitePrism T R adj n = (categorificationFinite n).map (nerveMap d.g.monotone.functor) := by
  apply truncation_functor_ext (n := n)
  have hn := (T.endpoint true).naturality
    (truncationUnit n (categorification.obj (nerve E)))
  exact (congrArg (fun h : categorification.obj (nerve E) ⟶
      T.tensor.obj ((categorificationFinite n).obj (nerve E)).val =>
    h ≫ d.finitePrism T R adj n) hn).trans
      ((congrArg (fun h => (T.endpoint true).app (categorification.obj (nerve E)) ≫ h)
        (d.finitePrism_unit T R adj n)).trans
        (congrArg (fun h : categorification.obj (nerve E) ⟶ categorification.obj (nerve E) =>
          h ≫ truncationUnit n (categorification.obj (nerve E)))
          (d.prism_endpoint_true T)))

lemma finitePrism_stationary {P : Type u} [PartialOrder P] (v : P →o E) (hv : ∀ p, v p ∈ A) :
    T.tensor.map ((categorificationFinite n).map (nerveMap v.monotone.functor)) ≫
      d.finitePrism T R adj n =
      T.projection.app ((categorificationFinite n).obj (nerve P)).val ≫
        (categorificationFinite n).map (nerveMap (d.f.comp v).monotone.functor) := by
  apply (T.truncatedCylinderEquiv R adj n (categorification.obj (nerve P))
    ((categorificationFinite n).obj (nerve E)).val
    ((categorificationFinite n).obj (nerve E)).property).injective
  erw [T.truncatedCylinderEquiv_apply, T.truncatedCylinderEquiv_apply]
  erw [← Category.assoc, ← T.tensor.map_comp]
  have hn : truncationUnit n (categorification.obj (nerve P)) ≫
      (show ((categorificationFinite n).obj (nerve P)).val ⟶
          ((categorificationFinite n).obj (nerve E)).val from
      (categorificationFinite n).map (nerveMap v.monotone.functor)) =
      categorification.map (nerveMap v.monotone.functor) ≫
        truncationUnit n (categorification.obj (nerve E)) := rfl
  erw [hn, T.tensor.map_comp, Category.assoc, d.finitePrism_unit,
    ← Category.assoc, d.grayPrism_stationary T v hv,
    Category.assoc]
  exact congrArg (fun h : T.tensor.obj (categorification.obj (nerve P)) ⟶
      ((categorificationFinite n).obj (nerve P)).val =>
    h ≫ (categorificationFinite n).map (nerveMap (d.f.comp v).monotone.functor))
      (T.projection.naturality (truncationUnit n (categorification.obj (nerve P)))).symm

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory AttachmentComparison Classical

variable {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
variable (r : E →o A) (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
variable (x : E) (hx : IsGreatest Aᶜ x)

def retract : E →o A where
  toFun e := if he : e ∈ A then ⟨e, he⟩ else r x
  monotone' := by
    intro b c hbc
    dsimp
    split_ifs with hb hc hc
    · exact hbc
    · exact (hadj ⟨b,hb⟩ x).mp (hbc.trans (hx.2 hc))
    · exact False.elim (hb (hA hbc hc))
    · exact le_rfl

def upper : E →o E where
  toFun e := if e ∈ A then e else x
  monotone' := by
    intro b c hbc
    dsimp
    split_ifs with hb hc hc
    · exact hbc
    · exact hbc.trans (hx.2 hc)
    · exact False.elim (hb (hA hbc hc))
    · exact le_rfl

@[simp] lemma retract_old (a : A) : retract A hA r hadj x hx a.val = a := by
  change (if membership : a.val ∈ A then ⟨a.val, membership⟩ else r x) = a
  simp [a.property]

@[simp] lemma upper_old (a : A) : upper A hA x hx a.val = a.val := by
  change (if a.val ∈ A then a.val else x) = a.val
  simp [a.property]

lemma retract_comp_inc : (retract A hA r hadj x hx).comp
    (OrderEmbedding.subtype A).toOrderHom = OrderHom.id := by
  ext a
  exact congrArg Subtype.val (retract_old A hA r hadj x hx a)

lemma id_le_upper (e : E) : e ≤ upper A hA x hx e := by
  change e ≤ if e ∈ A then e else x
  split_ifs with he
  · exact le_rfl
  · exact hx.2 he

lemma retract_le_upper (e : E) :
    (retract A hA r hadj x hx e).val ≤ upper A hA x hx e := by
  change (if membership : e ∈ A then (⟨e, membership⟩ : A) else r x).val ≤
    if e ∈ A then e else x
  split_ifs
  · exact le_rfl
  · exact (hadj (r x) x).mpr le_rfl

lemma upper_constant (a : E) (ha : a ∉ A) (b : E) (hb : b ∉ A) :
    upper A hA x hx a = upper A hA x hx b := by
  change (if a ∈ A then a else x) = if b ∈ A then b else x
  simp [ha, hb]

def idPrismData : RelativePrismData E A where
  lowerSet := hA
  f := OrderHom.id
  g := upper A hA x hx
  below := id_le_upper A hA x hx
  agree e he := (upper_old A hA x hx ⟨e,he⟩).symm
  constant := upper_constant A hA x hx

def retractPrismData : RelativePrismData E A where
  lowerSet := hA
  f := (OrderHom.Subtype.val (fun element : E => element ∈ A)).comp (retract A hA r hadj x hx)
  g := upper A hA x hx
  below := retract_le_upper A hA r hadj x hx
  agree e he := by
    change (retract A hA r hadj x hx e).val = upper A hA x hx e
    rw [retract_old A hA r hadj x hx ⟨e,he⟩, upper_old A hA x hx ⟨e,he⟩]
  constant := upper_constant A hA x hx

end Thomason.GreatestNew

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)

include R adj in

theorem finite_pushout_zigzag
    {n : ℕ} {A B X Y : NCategory.{u} n}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i a b j)
    (r : B ⟶ A) (hi : i ≫ r = 𝟙 A) (G : B ⟶ B)
    (P₀ P₁ : T.tensor.obj B.val ⟶ B.val)
    (h₀ : (T.endpoint false).app B.val ≫ P₀ = 𝟙 B.val)
    (h₁ : (T.endpoint true).app B.val ≫ P₀ = G)
    (h₂ : (T.endpoint false).app B.val ≫ P₁ = r ≫ i)
    (h₃ : (T.endpoint true).app B.val ≫ P₁ = G)
    (hs₀ : T.tensor.map i ≫ P₀ = T.projection.app A.val ≫ i)
    (hs₁ : T.tensor.map i ≫ P₁ = T.projection.app A.val ≫ i) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y))
        ((streetNerveFinite n).map H)) ∧
      Nonempty (SSet.Homotopy ((streetNerveFinite n).map (p ≫ j))
        ((streetNerveFinite n).map H)) := by
  let p : Y ⟶ X := sq.desc (r ≫ a) (𝟙 X) (by
    rw [← Category.assoc, hi, Category.id_comp, Category.comp_id])
  have hpB : b ≫ p = r ≫ a := sq.inl_desc _ _ _
  have hpX : j ≫ p = 𝟙 X := sq.inr_desc _ _ _
  obtain ⟨Q₀, _, _, hB₀, hX₀, _⟩ := T.finite_stationary_gluing R adj sq P₀
    (fun ε => if ε then G else 𝟙 B) (by intro ε; cases ε; exact h₀; exact h₁) hs₀
  obtain ⟨Q₁, _, _, hB₁, hX₁, _⟩ := T.finite_stationary_gluing R adj sq P₁
    (fun ε => if ε then G else r ≫ i) (by intro ε; cases ε; exact h₂; exact h₃) hs₁
  let e₀ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y.val) Q₀
  let e₁ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y.val) Q₁
  have he₀ : e₀ false = 𝟙 Y := by
    apply sq.hom_ext
    · exact hB₀ false
    · exact hX₀ false
  have he₁ : e₁ false = p ≫ j := by
    apply sq.hom_ext
    · rw [← Category.assoc, hpB, Category.assoc, ← sq.w, ← Category.assoc]
      exact hB₁ false
    · rw [← Category.assoc, hpX, Category.id_comp]
      exact hX₁ false
  have he : e₁ true = e₀ true := by
    apply sq.hom_ext
    · exact (hB₁ true).trans (hB₀ true).symm
    · exact (hX₁ true).trans (hX₀ true).symm
  refine ⟨p, e₀ true, hpX, ?_, ?_⟩
  · have h : SSet.Homotopy ((streetNerveFinite n).map (e₀ false))
        ((streetNerveFinite n).map (e₀ true)) := T.nerveHomotopy Q₀
    rw [he₀, (streetNerveFinite n).map_id] at h
    exact ⟨h⟩
  · have h : SSet.Homotopy ((streetNerveFinite n).map (e₁ false))
        ((streetNerveFinite n).map (e₁ true)) := T.nerveHomotopy Q₁
    rw [he₁, he] at h
    exact ⟨h⟩

lemma finite_nerve_weak_of_zigzag {n : ℕ} {X Y : NCategory.{u} n}
    (j : X ⟶ Y) (p : Y ⟶ X) (H : Y ⟶ Y) (hp : j ≫ p = 𝟙 X)
    (h₀ : SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y)) ((streetNerveFinite n).map H))
    (h₁ : SSet.Homotopy ((streetNerveFinite n).map (p ≫ j)) ((streetNerveFinite n).map H)) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  have hH : simplicialWeakEquivalences ((streetNerveFinite n).map H) :=
    (simplicialWeakEquivalences_homotopy h₀).mp (simplicialWeakEquivalences.id_mem _)
  have hw : simplicialWeakEquivalences ((streetNerveFinite n).map (p ≫ j)) :=
    (simplicialWeakEquivalences_homotopy h₁).mpr hH
  have rt : RetractArrow j (p ≫ j) :=
    { i := Arrow.homMk j (𝟙 Y) (by simp [← Category.assoc,hp])
      r := Arrow.homMk p (𝟙 Y) (by simp)
      retract := by ext <;> simp [hp] }
  exact simplicialWeakEquivalences.of_retract (rt.map (streetNerveFinite n)) hw

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory AttachmentComparison

lemma finitePosetMap_id (n : ℕ) (E : Type u) [PartialOrder E] :
    posetMap n (OrderHom.id : E →o E) = 𝟙 (posetObj n E) :=
  (categorificationFinite n).map_id (nerve E)

lemma finitePosetMap_comp (n : ℕ) {P Q R : Type u} [PartialOrder P]
    [PartialOrder Q] [PartialOrder R] (f : P →o Q) (g : Q →o R) :
    posetMap n (g.comp f) = posetMap n f ≫ posetMap n g :=
  (categorificationFinite n).map_comp (nerveMap f.toFunctor) (nerveMap g.toFunctor)

variable (T : RightIntervalExtension.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
variable {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
variable (r : E →o A) (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
variable (x : E) (hx : IsGreatest Aᶜ x)

include T R adj hA r hadj x hx in

theorem finite_pushout_deformation (n : ℕ)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X} {j : X ⟶ Y}
    {b : posetObj n E ⟶ Y} (sq : IsPushout (inc n A) a b j) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y))
        ((streetNerveFinite n).map H)) ∧
      Nonempty (SSet.Homotopy ((streetNerveFinite n).map (p ≫ j))
        ((streetNerveFinite n).map H)) := by
  let d₀ := idPrismData A hA x hx
  let d₁ := retractPrismData A hA r hadj x hx
  let i : A →o E := (OrderEmbedding.subtype A).toOrderHom
  let r' := retract A hA r hadj x hx
  have hr' : r'.comp i = OrderHom.id := retract_comp_inc A hA r hadj x hx
  have hri : inc n A ≫ posetMap n r' = 𝟙 (posetObj n A) := by
    rw [← finitePosetMap_comp]
    change posetMap n (r'.comp i) = _
    rw [hr', finitePosetMap_id]
  have h₀ : d₀.f.comp i = i := rfl
  have h₁ : d₁.f.comp i = i := by
    ext e
    exact congrArg Subtype.val (retract_old A hA r hadj x hx e)
  have hs₀ := d₀.finitePrism_stationary T R adj n i (fun e => e.property)
  have hs₁ := d₁.finitePrism_stationary T R adj n i (fun e => e.property)
  rw [h₀] at hs₀
  rw [h₁] at hs₁
  exact T.finite_pushout_zigzag R adj sq (posetMap n r') hri
    (posetMap n (upper A hA x hx))
    (d₀.finitePrism T R adj n) (d₁.finitePrism T R adj n)
    ((d₀.finitePrism_endpoint_false T R adj n).trans (finitePosetMap_id n E))
    (d₀.finitePrism_endpoint_true T R adj n)
    ((d₁.finitePrism_endpoint_false T R adj n).trans (finitePosetMap_comp n r' i))
    (d₁.finitePrism_endpoint_true T R adj n) hs₀ hs₁

include T R adj hA r hadj x hx in

theorem finite_pushout_nerve_weak (n : ℕ)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X} {j : X ⟶ Y}
    {b : posetObj n E ⟶ Y} (sq : IsPushout (inc n A) a b j) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  obtain ⟨p,H,hp,⟨H₀⟩,⟨H₁⟩⟩ := finite_pushout_deformation T R adj A hA r hadj x hx n sq
  exact RightIntervalExtension.finite_nerve_weak_of_zigzag j p H hp H₀ H₁

end Thomason.GreatestNew

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})
variable {A B X Y Z : OmegaCategory.{u}}
variable {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
variable (sq : IsPushout i a b j)

include sq in

lemma omegaCylinder_pushout : IsPushout (T.tensor.map i) (T.tensor.map a)
    (T.tensor.map b) (T.tensor.map j) := by
  let := T.cocontinuous
  exact sq.map T.tensor

def omegaGlue (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) : T.tensor.obj Y ⟶ Z :=
  (T.omegaCylinder_pushout sq).desc PB PX h

lemma omegaGlue_left (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map b ≫ T.omegaGlue sq PB PX h = PB :=
  (T.omegaCylinder_pushout sq).inl_desc PB PX h

lemma omegaGlue_right (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) :
    T.tensor.map j ≫ T.omegaGlue sq PB PX h = PX :=
  (T.omegaCylinder_pushout sq).inr_desc PB PX h

include sq in
lemma omegaCylinder_hom_ext {P Q : T.tensor.obj Y ⟶ Z}
    (hb : T.tensor.map b ≫ P = T.tensor.map b ≫ Q)
    (hj : T.tensor.map j ≫ P = T.tensor.map j ≫ Q) : P = Q :=
  (T.omegaCylinder_pushout sq).hom_ext hb hj

lemma omegaGlue_endpoint_left
    (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    b ≫ (T.endpoint ε).app Y ≫ T.omegaGlue sq PB PX h =
      (T.endpoint ε).app B ≫ PB := by
  exact (congrArg (fun f : B ⟶ T.tensor.obj Y =>
    f ≫ T.omegaGlue sq PB PX h) ((T.endpoint ε).naturality b)).trans
    (congrArg (fun f => (T.endpoint ε).app B ≫ f) (T.omegaGlue_left sq PB PX h))

lemma omegaGlue_endpoint_right
    (PB : T.tensor.obj B ⟶ Z) (PX : T.tensor.obj X ⟶ Z)
    (h : T.tensor.map i ≫ PB = T.tensor.map a ≫ PX) (ε : Bool) :
    j ≫ (T.endpoint ε).app Y ≫ T.omegaGlue sq PB PX h =
      (T.endpoint ε).app X ≫ PX := by
  exact (congrArg (fun f : X ⟶ T.tensor.obj Y =>
    f ≫ T.omegaGlue sq PB PX h) ((T.endpoint ε).naturality j)).trans
    (congrArg (fun f => (T.endpoint ε).app X ≫ f) (T.omegaGlue_right sq PB PX h))

include sq in

theorem omega_stationary_gluing
    (P : T.tensor.obj B ⟶ B) (F : Bool → (B ⟶ B))
    (he : ∀ ε, (T.endpoint ε).app B ≫ P = F ε)
    (hs : T.tensor.map i ≫ P = T.projection.app A ≫ i) :
    ∃ Q : T.tensor.obj Y ⟶ Y,
      T.tensor.map b ≫ Q = P ≫ b ∧
      T.tensor.map j ≫ Q = T.projection.app X ≫ j ∧
      (∀ ε, b ≫ (T.endpoint ε).app Y ≫ Q = F ε ≫ b) ∧
      (∀ ε, j ≫ (T.endpoint ε).app Y ≫ Q = j) ∧
      (∀ Q' : T.tensor.obj Y ⟶ Y,
        T.tensor.map b ≫ Q' = P ≫ b →
        T.tensor.map j ≫ Q' = T.projection.app X ≫ j → Q' = Q) := by
  have hc : T.tensor.map i ≫ (P ≫ b) =
      T.tensor.map a ≫ (T.projection.app X ≫ j) := by
    calc
      _ = T.projection.app A ≫ (i ≫ b) := by rw [← Category.assoc, hs, Category.assoc]
      _ = T.projection.app A ≫ (a ≫ j) := congrArg (fun f => T.projection.app A ≫ f) sq.w
      _ = _ := (congrArg (fun f : T.tensor.obj A ⟶ X => f ≫ j)
        (T.projection.naturality a)).symm
  let Q := T.omegaGlue sq (P ≫ b) (T.projection.app X ≫ j) hc
  refine ⟨Q, T.omegaGlue_left sq _ _ hc, T.omegaGlue_right sq _ _ hc, ?_, ?_, ?_⟩
  · intro ε
    rw [T.omegaGlue_endpoint_left, ← Category.assoc, he ε]
  · intro ε
    rw [T.omegaGlue_endpoint_right, ← Category.assoc]
    have hε := congrArg (fun α => α.app X) (T.endpoint_projection ε)
    change (T.endpoint ε).app X ≫ T.projection.app X = 𝟙 X at hε
    rw [hε]; rfl
  · intro Q' hb hj
    apply T.omegaCylinder_hom_ext sq
    · exact hb.trans (T.omegaGlue_left sq _ _ hc).symm
    · exact hj.trans (T.omegaGlue_right sq _ _ hc).symm

include sq in

lemma omega_stationary_gluing_natural
    {X' Y' : OmegaCategory.{u}} {j' : X' ⟶ Y'} {b' : B ⟶ Y'}
    (w : X ⟶ X') (v : Y ⟶ Y') (hvB : b ≫ v = b') (hvX : j ≫ v = w ≫ j')
    (P : T.tensor.obj B ⟶ B)
    (Q : T.tensor.obj Y ⟶ Y) (Q' : T.tensor.obj Y' ⟶ Y')
    (hB : T.tensor.map b ≫ Q = P ≫ b)
    (hX : T.tensor.map j ≫ Q = T.projection.app X ≫ j)
    (hB' : T.tensor.map b' ≫ Q' = P ≫ b')
    (hX' : T.tensor.map j' ≫ Q' = T.projection.app X' ≫ j') :
    T.tensor.map v ≫ Q' = Q ≫ v := by
  apply T.omegaCylinder_hom_ext sq
  · rw [← Category.assoc, ← T.tensor.map_comp, hvB, hB', ← hvB,
      ← Category.assoc, ← hB, Category.assoc]
  · calc
      _ = T.tensor.map (j ≫ v) ≫ Q' := by rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map (w ≫ j') ≫ Q' := by rw [hvX]
      _ = T.tensor.map w ≫ (T.tensor.map j' ≫ Q') := by rw [T.tensor.map_comp, Category.assoc]
      _ = T.tensor.map w ≫ (T.projection.app X' ≫ j') := by rw [hX']
      _ = T.projection.app X ≫ (w ≫ j') :=
        congrArg (fun f : T.tensor.obj X ⟶ X' => f ≫ j') (T.projection.naturality w)
      _ = (T.projection.app X ≫ j) ≫ v :=
        congrArg (fun f : X ⟶ Y' => T.projection.app X ≫ f) hvX.symm
      _ = _ := by rw [← hX, Category.assoc]

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalExtension
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalExtension.{u})

include T in

theorem omega_pushout_zigzag
    {A B X Y : OmegaCategory.{u}}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i a b j)
    (r : B ⟶ A) (hi : i ≫ r = 𝟙 A) (G : B ⟶ B)
    (P₀ P₁ : T.tensor.obj B ⟶ B)
    (h₀ : (T.endpoint false).app B ≫ P₀ = 𝟙 B)
    (h₁ : (T.endpoint true).app B ≫ P₀ = G)
    (h₂ : (T.endpoint false).app B ≫ P₁ = r ≫ i)
    (h₃ : (T.endpoint true).app B ≫ P₁ = G)
    (hs₀ : T.tensor.map i ≫ P₀ = T.projection.app A ≫ i)
    (hs₁ : T.tensor.map i ≫ P₁ = T.projection.app A ≫ i) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 (streetNerveFunctor.obj Y))
        (streetNerveFunctor.map H)) ∧
      Nonempty (SSet.Homotopy (streetNerveFunctor.map (p ≫ j))
        (streetNerveFunctor.map H)) := by
  let p : Y ⟶ X := sq.desc (r ≫ a) (𝟙 X) (by
    rw [← Category.assoc, hi, Category.id_comp, Category.comp_id])
  have hpB : b ≫ p = r ≫ a := sq.inl_desc _ _ _
  have hpX : j ≫ p = 𝟙 X := sq.inr_desc _ _ _
  obtain ⟨Q₀, _, _, hB₀, hX₀, _⟩ := T.omega_stationary_gluing sq P₀
    (fun ε => if ε then G else 𝟙 B) (by intro ε; cases ε; exact h₀; exact h₁) hs₀
  obtain ⟨Q₁, _, _, hB₁, hX₁, _⟩ := T.omega_stationary_gluing sq P₁
    (fun ε => if ε then G else r ≫ i) (by intro ε; cases ε; exact h₂; exact h₃) hs₁
  let e₀ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y) Q₀
  let e₁ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y) Q₁
  have he₀ : e₀ false = 𝟙 Y := by
    apply sq.hom_ext
    · exact hB₀ false
    · exact hX₀ false
  have he₁ : e₁ false = p ≫ j := by
    apply sq.hom_ext
    · rw [← Category.assoc, hpB, Category.assoc, ← sq.w, ← Category.assoc]
      exact hB₁ false
    · rw [← Category.assoc, hpX, Category.id_comp]
      exact hX₁ false
  have he : e₁ true = e₀ true := by
    apply sq.hom_ext
    · exact (hB₁ true).trans (hB₀ true).symm
    · exact (hX₁ true).trans (hX₀ true).symm
  refine ⟨p, e₀ true, hpX, ?_, ?_⟩
  · have h : SSet.Homotopy (streetNerveFunctor.map (e₀ false))
        (streetNerveFunctor.map (e₀ true)) := T.nerveHomotopy Q₀
    rw [he₀, streetNerveFunctor.map_id] at h
    exact ⟨h⟩
  · have h : SSet.Homotopy (streetNerveFunctor.map (e₁ false))
        (streetNerveFunctor.map (e₁ true)) := T.nerveHomotopy Q₁
    rw [he₁, he] at h
    exact ⟨h⟩

lemma omega_nerve_weak_of_zigzag {X Y : OmegaCategory.{u}}
    (j : X ⟶ Y) (p : Y ⟶ X) (H : Y ⟶ Y) (hp : j ≫ p = 𝟙 X)
    (h₀ : SSet.Homotopy (𝟙 (streetNerveFunctor.obj Y)) (streetNerveFunctor.map H))
    (h₁ : SSet.Homotopy (streetNerveFunctor.map (p ≫ j)) (streetNerveFunctor.map H)) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  have hH : simplicialWeakEquivalences (streetNerveFunctor.map H) :=
    (simplicialWeakEquivalences_homotopy h₀).mp (simplicialWeakEquivalences.id_mem _)
  have hw : simplicialWeakEquivalences (streetNerveFunctor.map (p ≫ j)) :=
    (simplicialWeakEquivalences_homotopy h₁).mpr hH
  have rt : RetractArrow j (p ≫ j) :=
    { i := Arrow.homMk j (𝟙 Y) (by simp [← Category.assoc,hp])
      r := Arrow.homMk p (𝟙 Y) (by simp)
      retract := by ext <;> simp [hp] }
  exact simplicialWeakEquivalences.of_retract (rt.map streetNerveFunctor) hw

end Thomason.RightIntervalExtension

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory

abbrev omegaPosetObj (P : Type u) [PartialOrder P] : OmegaCategory.{u} :=
  categorification.obj (nerve P)

abbrev omegaPosetMap {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) : omegaPosetObj P ⟶ omegaPosetObj Q :=
  categorification.map (nerveMap f.toFunctor)

abbrev omegaInc {P : Type u} [PartialOrder P] (A : Set P) :=
  omegaPosetMap (P := A) (Q := P) (OrderEmbedding.subtype A).toOrderHom

lemma omegaPosetMap_id (E : Type u) [PartialOrder E] :
    omegaPosetMap (OrderHom.id : E →o E) = 𝟙 (omegaPosetObj E) :=
  categorification.map_id (nerve E)

lemma omegaPosetMap_comp {P Q R : Type u} [PartialOrder P]
    [PartialOrder Q] [PartialOrder R] (f : P →o Q) (g : Q →o R) :
    omegaPosetMap (g.comp f) = omegaPosetMap f ≫ omegaPosetMap g :=
  categorification.map_comp (nerveMap f.toFunctor) (nerveMap g.toFunctor)

variable (T : RightIntervalExtension.{u})
variable {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
variable (r : E →o A) (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
variable (x : E) (hx : IsGreatest Aᶜ x)

include T hA r hadj x hx in

theorem omega_pushout_deformation
    {X Y : OmegaCategory.{u}} {a : omegaPosetObj A ⟶ X} {j : X ⟶ Y}
    {b : omegaPosetObj E ⟶ Y} (sq : IsPushout (omegaInc A) a b j) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 (streetNerveFunctor.obj Y))
        (streetNerveFunctor.map H)) ∧
      Nonempty (SSet.Homotopy (streetNerveFunctor.map (p ≫ j))
        (streetNerveFunctor.map H)) := by
  let d₀ := idPrismData A hA x hx
  let d₁ := retractPrismData A hA r hadj x hx
  let i : A →o E := (OrderEmbedding.subtype A).toOrderHom
  let r' := retract A hA r hadj x hx
  have hr' : r'.comp i = OrderHom.id := retract_comp_inc A hA r hadj x hx
  have hri : omegaInc A ≫ omegaPosetMap r' = 𝟙 (omegaPosetObj A) := by
    rw [← omegaPosetMap_comp]
    change omegaPosetMap (r'.comp i) = _
    rw [hr', omegaPosetMap_id]
  have h₀ : d₀.f.comp i = i := rfl
  have h₁ : d₁.f.comp i = i := by
    ext e
    exact congrArg Subtype.val (retract_old A hA r hadj x hx e)
  have hs₀ := d₀.grayPrism_stationary T i (fun e => e.property)
  have hs₁ := d₁.grayPrism_stationary T i (fun e => e.property)
  rw [h₀] at hs₀
  rw [h₁] at hs₁
  exact T.omega_pushout_zigzag sq (omegaPosetMap r') hri
    (omegaPosetMap (upper A hA x hx))
    (d₀.prism T) (d₁.prism T)
    ((d₀.prism_endpoint_false T).trans (omegaPosetMap_id E))
    (d₀.prism_endpoint_true T)
    ((d₁.prism_endpoint_false T).trans (omegaPosetMap_comp r' i))
    (d₁.prism_endpoint_true T) hs₀ hs₁

include T hA r hadj x hx in

theorem omega_pushout_nerve_weak
    {X Y : OmegaCategory.{u}} {a : omegaPosetObj A ⟶ X} {j : X ⟶ Y}
    {b : omegaPosetObj E ⟶ Y} (sq : IsPushout (omegaInc A) a b j) :
    simplicialWeakEquivalences (streetNerveFunctor.map j) := by
  obtain ⟨p,H,hp,⟨H₀⟩,⟨H₁⟩⟩ := omega_pushout_deformation T A hA r hadj x hx sq
  exact RightIntervalExtension.omega_nerve_weak_of_zigzag j p H hp H₀ H₁

end Thomason.GreatestNew

end

end OAI
