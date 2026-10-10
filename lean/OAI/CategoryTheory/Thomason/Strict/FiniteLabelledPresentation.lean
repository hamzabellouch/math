import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.TerminalConeUniversal
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor

namespace OAI

section

/-!
# Ordered labels after finite reflection

Strict poset targets are already one-dimensional. Their labels therefore
descend uniquely through the actual reflection unit, and their object
values agree with the proved finite object equivalence.
-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)

/-- A strict poset is an object of every positive finite dimension. -/
def truncatedPoset (E : Type) [Preorder E] : Truncated (n + 1) :=
  ⟨StrictPoset.category E, fun x => (StrictPoset.category E).dimensionLE_mono (by omega)
    (StrictPoset.category_isTruncated E x)⟩

/-- Descend an actual strict ordered label through finite reflection. -/
noncomputable def descendPosetLabel {X : StrictOmegaCategory.{0}} {E : Type} [Preorder E]
    (p : X ⟶ StrictPoset.category E) : (r.reflect.obj X).val ⟶ StrictPoset.category E :=
  (r.adjunction.homEquiv X (truncatedPoset E)).symm p

/-- The descended label agrees with the original label on all cells. -/
theorem descendPosetLabel_fac {X : StrictOmegaCategory.{0}} {E : Type} [Preorder E]
    (p : X ⟶ StrictPoset.category E) :
    r.adjunction.unit.app X ≫ r.descendPosetLabel p = p := by
  let Y : Truncated (n + 1) := truncatedPoset E
  let e := r.adjunction.homEquiv X Y
  exact (r.adjunction.homEquiv_apply X Y (e.symm p)).symm.trans (e.apply_symm_apply p)

/-- Any two finite labels agreeing on the original category coincide. -/
theorem descendPosetLabel_unique {X : StrictOmegaCategory.{0}} {E : Type} [Preorder E]
    (p : X ⟶ StrictPoset.category E) (q : (r.reflect.obj X).val ⟶ StrictPoset.category E)
    (hq : r.adjunction.unit.app X ≫ q = p) : q = r.descendPosetLabel p :=
  r.unit_hom_ext X (truncatedPoset E) (hq.trans (r.descendPosetLabel_fac p).symm)

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Poset objects retain their canonical names after finite categorification. -/
noncomputable def posetObjectsEquiv (E : Type) [PartialOrder E] :
    Objects ((r.categorification h).obj (nerve E)).val ≃ E :=
  (r.unitObjectsEquiv (h.categorification.obj (nerve E))).symm.trans (h.posetObjectsEquiv E)

/-- The actual finite-dimensional strict evaluation into ordered labels. -/
noncomputable def posetEvaluation (E : Type) [PartialOrder E] :
    ((r.categorification h).obj (nerve E)).val ⟶ StrictPoset.category E :=
  r.descendPosetLabel (h.posetEvaluation E)

/-- This evaluation has the required object values after finite reflection. -/
theorem posetEvaluation_object {E : Type} [PartialOrder E]
    (x : Objects ((r.categorification h).obj (nerve E)).val) :
    (r.posetEvaluation h E).toFun x.val = StrictPoset.identity (r.posetObjectsEquiv h E x) := by
  obtain ⟨y, rfl⟩ := (r.unit_objects_bijective (h.categorification.obj (nerve E))).2 x
  have he := congrArg (fun f : h.categorification.obj (nerve E) ⟶ StrictPoset.category E =>
    f.toFun y.val) (r.descendPosetLabel_fac (h.posetEvaluation E))
  have hi : r.posetObjectsEquiv h E
      ((r.adjunction.unit.app (h.categorification.obj (nerve E))).toOneFunctor.obj y) =
      h.posetObjectsEquiv E y :=
    congrArg (h.posetObjectsEquiv E)
      ((r.unitObjectsEquiv (h.categorification.obj (nerve E))).symm_apply_apply y)
  rw [hi]
  exact he.trans (h.posetEvaluation_object y)

/-- Evaluation of finite-dimensional poset cells is natural under monotone maps. -/
theorem posetEvaluation_naturality {E F : Type} [PartialOrder E] [PartialOrder F]
    (f : E →o F) :
    (StrictOmegaCategory.inclusion (n + 1)).map (r.reflect.map (h.posetMap f)) ≫
      r.posetEvaluation h F = r.posetEvaluation h E ≫ StrictPoset.map f := by
  apply r.unit_hom_ext (h.categorification.obj (nerve E)) (truncatedPoset F)
  let X := h.categorification.obj (nerve E)
  let Y := h.categorification.obj (nerve F)
  let qX := r.adjunction.unit.app X
  let qY := r.adjunction.unit.app Y
  let rf : (r.reflect.obj X).val ⟶ (r.reflect.obj Y).val := r.reflect.map (h.posetMap f)
  have hn : qX ≫ rf = h.posetMap f ≫ qY := (r.adjunction.unit.naturality (h.posetMap f)).symm
  let eX : (r.reflect.obj X).val ⟶ StrictPoset.category E :=
    r.descendPosetLabel (h.posetEvaluation E)
  let eY : (r.reflect.obj Y).val ⟶ StrictPoset.category F :=
    r.descendPosetLabel (h.posetEvaluation F)
  have hfX : qX ≫ eX = h.posetEvaluation E := r.descendPosetLabel_fac _
  have hfY : qY ≫ eY = h.posetEvaluation F := r.descendPosetLabel_fac _
  change qX ≫ (rf ≫ eY) = qX ≫ (eX ≫ StrictPoset.map f)
  calc
    _ = (qX ≫ rf) ≫ eY := (Category.assoc _ _ _).symm
    _ = (h.posetMap f ≫ qY) ≫ eY := congrArg (fun k => k ≫ eY) hn
    _ = h.posetMap f ≫ (qY ≫ eY) := Category.assoc _ _ _
    _ = h.posetMap f ≫ h.posetEvaluation F := congrArg (fun k => h.posetMap f ≫ k) hfY
    _ = h.posetEvaluation E ≫ StrictPoset.map f := h.posetEvaluation_naturality f
    _ = (qX ≫ eX) ≫ StrictPoset.map f := congrArg (fun k => k ≫ StrictPoset.map f) hfX.symm
    _ = _ := Category.assoc _ _ _

/-- The sieve membership label in every positive finite dimension. -/
noncomputable def membershipLabel {E : Type} [PartialOrder E] (A : Set E) (hA : IsLowerSet A) :
    ((r.categorification h).obj (nerve E)).val ⟶ StrictPoset.category (Fin 2) :=
  r.posetEvaluation h E ≫ StrictPoset.map (sieveCharacteristic A hA)

/-- Finite membership labels retain the original poset's object criterion. -/
theorem membershipLabel_object_zero_iff {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (x : Objects ((r.categorification h).obj (nerve E)).val) :
    (r.membershipLabel h A hA).toFun x.val = StrictPoset.identity 0 ↔
      r.posetObjectsEquiv h E x ∈ A := by
  change (StrictPoset.map (sieveCharacteristic A hA)).toFun
    ((r.posetEvaluation h E).toFun x.val) = _ ↔ _
  rw [r.posetEvaluation_object h x, StrictPoset.map_identity]
  constructor
  · intro he
    exact (sieveCharacteristic_zero_iff A hA _).mp
      (congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) he)
  · intro hx
    exact congrArg StrictPoset.identity ((sieveCharacteristic_zero_iff A hA _).mpr hx)

end Thomason.Construction.FiniteReflectionInput

end

section

/-!
# Labelled simplex colimits in finite dimensions

Reflection and preservation of finite endpoint-fibre colimits give
colimits in the finite-category slice.
-/

namespace Thomason.Construction.FiniteReflectionInput

open CategoryTheory CategoryTheory.Limits StrictOmegaCategory

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Reflect the actual oriental presentation into the chosen finite dimension. -/
noncomputable def simplexCocone (K : SSet.{0}) :
    Cocone (CostructuredArrow.proj SSet.stdSimplex K ⋙ h.cosimplicial ⋙ r.reflect) :=
  r.reflect.mapCocone (h.simplexCocone K)

/-- Its colimit property is preserved by the reflection adjunction. -/
noncomputable def simplexCocone_isColimit (K : SSet.{0}) :
    IsColimit (r.simplexCocone h K) := by
  have := r.adjunction.leftAdjoint_preservesColimits
  exact isColimitOfPreserves r.reflect (h.simplexCocone_isColimit K)

/-- The simplex diagram with a fixed finite-dimensional binary label. -/
noncomputable def labelledSimplexDiagram {K : SSet.{0}}
    (p : (r.categorification h).obj K ⟶ finiteInterval n) :
    CostructuredArrow SSet.stdSimplex K ⥤ Over (finiteInterval n) :=
  Over.lift (CostructuredArrow.proj SSet.stdSimplex K ⋙ h.cosimplicial ⋙ r.reflect)
    ((r.simplexCocone h K).ι ≫ (Functor.const _).map p)

/-- This presentation lives in the finite-dimensional slice itself. -/
noncomputable def labelledSimplexCocone {K : SSet.{0}}
    (p : (r.categorification h).obj K ⟶ finiteInterval n) :
    Cocone (r.labelledSimplexDiagram h p) := Over.liftCocone (r.simplexCocone h K) p

noncomputable def labelledSimplexCocone_isColimit {K : SSet.{0}}
    (p : (r.categorification h).obj K ⟶ finiteInterval n) :
    IsColimit (r.labelledSimplexCocone h p) :=
  Over.isColimitLiftCocone (r.simplexCocone h K) p (r.simplexCocone_isColimit h K)

/-- Take actual finite-dimensional full endpoint fibres of the pieces. -/
noncomputable def simplexFiberCocone {K : SSet.{0}}
    (p : (r.categorification h).obj K ⟶ finiteInterval n) (e : Fin 2) :
    Cocone (r.labelledSimplexDiagram h p ⋙ finiteLabelFiberFunctor n e) :=
  (finiteLabelFiberFunctor n e).mapCocone (r.labelledSimplexCocone h p)

/-- Their colimit is the finite full fibre. -/
noncomputable def simplexFiberCocone_isColimit (f : PublishedLabelFiberInput) {K : SSet.{0}}
    (p : (r.categorification h).obj K ⟶ finiteInterval n) (e : Fin 2) :
    IsColimit (r.simplexFiberCocone h p e) := by
  have := f.finite n e
  exact isColimitOfPreserves (finiteLabelFiberFunctor n e)
    (r.labelledSimplexCocone_isColimit h p)

end Thomason.Construction.FiniteReflectionInput

end

end OAI
