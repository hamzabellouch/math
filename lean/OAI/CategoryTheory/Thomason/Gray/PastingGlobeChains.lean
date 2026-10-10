import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.GlobePastingDensity
import OAI.CategoryTheory.Thomason.Gray.RightCylinderPrism
import OAI.CategoryTheory.Thomason.Gray.StrictAbelianization
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Dense
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

namespace OAI

section

/-! # Extending the actual globe-and-pasting presentation

The proved cellwise presentation is dense. Consequently a cocontinuous
functor and its natural transformations are recovered from these small
parameters. The extension below is a genuine small colimit, with its
restriction and universal comparison maps explicitly retained.
-/

namespace Thomason.Construction.StrictOmegaCategory.GlobePasting

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

instance : inclusion.Full where
  map_surjective f := ⟨f, rfl⟩

instance : inclusion.Faithful where
  map_injective h := h

instance : inclusion.IsDense where
  isDenseAt C := ⟨by
    change IsColimit (cocone C)
    exact isColimit C⟩

/-- The original strict category is recovered by the small presentation. -/
def presentationIso : inclusion.leftKanExtension inclusion ≅ 𝟭 StrictOmegaCategory.{0} :=
  Functor.IsDense.leftKanExtensionIso inclusion

/-- Extend actual data on the finite parameters by its small colimit. -/
def extend (F : Shape ⥤ StrictOmegaCategory.{0}) :
    StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0} :=
  inclusion.leftKanExtension F

/-- Every parameter is recovered, since the parameter inclusion is full
and faithful. This statement assumes no global preservation by the extension. -/
def restrictionIso (F : Shape ⥤ StrictOmegaCategory.{0}) :
    F ≅ inclusion ⋙ extend F := by
  letI : IsIso (inclusion.leftKanExtensionUnit F) :=
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit inclusion F).isIso_hom
  exact (asIso (inclusion.leftKanExtensionUnit F) :
    F ≅ inclusion ⋙ inclusion.leftKanExtension F)

/-- The extension is computed on the actual category of parameters over C. -/
def extensionObjIso (F : Shape ⥤ StrictOmegaCategory.{0}) (C : StrictOmegaCategory.{0}) :
    (extend F).obj C ≅ colimit (CostructuredArrow.proj inclusion C ⋙ F) :=
  inclusion.leftKanExtensionObjIsoColimit F C

/-- The explicit global comparison determined by a parameter-level map. -/
def compare (F : Shape ⥤ StrictOmegaCategory.{0})
    (T : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}) (a : F ⟶ inclusion ⋙ T) :
    extend F ⟶ T :=
  Functor.descOfIsLeftKanExtension _ (inclusion.leftKanExtensionUnit F) T a

@[reassoc (attr := simp)]
theorem restriction_compare (F : Shape ⥤ StrictOmegaCategory.{0})
    (T : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0})
    (a : F ⟶ inclusion ⋙ T) :
    (restrictionIso F).hom ≫ whiskerLeft inclusion (compare F T a) = a := by
  exact Functor.descOfIsLeftKanExtension_fac (inclusion.leftKanExtension F)
    (inclusion.leftKanExtensionUnit F) T a

/-- Global maps from the extension are determined by their finite-parameter values. -/
theorem compare_ext (F : Shape ⥤ StrictOmegaCategory.{0})
    {T : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}}
    {a b : extend F ⟶ T}
    (he : (restrictionIso F).hom ≫ whiskerLeft inclusion a =
      (restrictionIso F).hom ≫ whiskerLeft inclusion b) : a = b :=
  Functor.hom_ext_of_isLeftKanExtension _ (inclusion.leftKanExtensionUnit F) a b he

end

end Thomason.Construction.StrictOmegaCategory.GlobePasting

end

section

/-! # Restriction of the dense presentation to the free globes -/

namespace Thomason.Construction.StrictOmegaCategory.GlobePasting

open CategoryTheory

noncomputable section

/-- Keep the globe objects and all of their strict maps in the dense presentation. -/
def globes : Globe.Shapes ⥤ Shape where
  obj n := .globe n.dim
  map f := f

/-- The restricted inclusion is exactly the original globe inclusion. -/
def globesInclusionIso : globes ⋙ inclusion ≅ Globe.inclusion :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end

end Thomason.Construction.StrictOmegaCategory.GlobePasting

end

section

/-! # A global extension of the actual right chain cylinders

This constructs the small-colimit extension of the chain cylinders on
free globes and composable pairs. Its endpoints and comparison to chain
realization are natural on all strict categories. No claim of global
cocontinuity, adjointness, or preservation of colimits by nu is used.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory CategoryTheory.Functor _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

namespace GrayChainExtension

/-- The chain-cylinder model before extension from the finite parameters. -/
def model : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0} :=
  Abelianization.functor ⋙ rightCylinderFunctor ⋙ realizationFunctor

/-- The actual endpoint into the chain model, using the constructed unit. -/
def modelEndpoint (a : Bool) : 𝟭 StrictOmegaCategory.{0} ⟶ model where
  app C := Abelianization.unit C ≫ (RightCylinder.endpoint (Abelianization.complex C) a).realization
  naturality C D f := by
    let uC : C ⟶ (Abelianization.complex C).realization := Abelianization.unit C
    let uD : D ⟶ (Abelianization.complex D).realization := Abelianization.unit D
    let v : (Abelianization.complex C).realization ⟶ (Abelianization.complex D).realization :=
      (Abelianization.map f).realization
    let eC : (Abelianization.complex C).realization ⟶ model.obj C :=
      (RightCylinder.endpoint (Abelianization.complex C) a).realization
    let eD : (Abelianization.complex D).realization ⟶ model.obj D :=
      (RightCylinder.endpoint (Abelianization.complex D) a).realization
    let w : model.obj C ⟶ model.obj D :=
      (RightCylinder.map (Abelianization.map f)).realization
    have hu : f ≫ uD = uC ≫ v := Abelianization.adjunction.unit.naturality f
    have he : v ≫ eD = eC ≫ w := by
      apply StrictOmegaCategory.Hom.ext
      funext x
      apply Cell.ext
      funext b p
      exact (RightCylinder.map_endpoint (Abelianization.map f) a p (x.table b p)).symm
    change f ≫ (uD ≫ eD) = (uC ≫ eC) ≫ w
    calc
      _ = (f ≫ uD) ≫ eD := (Category.assoc _ _ _).symm
      _ = (uC ≫ v) ≫ eD := congrArg (fun q => q ≫ eD) hu
      _ = uC ≫ (v ≫ eD) := Category.assoc _ _ _
      _ = uC ≫ (eC ≫ w) := congrArg (fun q => uC ≫ q) he
      _ = _ := (Category.assoc _ _ _).symm

/-- The concrete diagram being extended. -/
def parameters : GlobePasting.Shape ⥤ StrictOmegaCategory.{0} :=
  GlobePasting.inclusion ⋙ model

/-- Small-colimit extension of the explicit cylinders. -/
def cylinder : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0} :=
  GlobePasting.extend parameters

/-- Exact agreement with the actual chain model on every chosen parameter. -/
def parameterIso : parameters ≅ GlobePasting.inclusion ⋙ cylinder :=
  GlobePasting.restrictionIso parameters

/-- The canonical comparison to the chain model on arbitrary strict categories. -/
def comparison : cylinder ⟶ model :=
  GlobePasting.compare parameters model (𝟙 parameters)

@[reassoc (attr := simp)]
theorem parameter_comparison :
    parameterIso.hom ≫ whiskerLeft GlobePasting.inclusion comparison = 𝟙 parameters :=
  GlobePasting.restriction_compare parameters model (𝟙 parameters)

/-- Density extends the literal endpoint maps to every strict category. -/
def endpoint (a : Bool) : 𝟭 StrictOmegaCategory.{0} ⟶ cylinder :=
  Functor.descOfIsLeftKanExtension _ GlobePasting.inclusion.rightUnitor.inv cylinder
    (whiskerLeft GlobePasting.inclusion (modelEndpoint a) ≫ parameterIso.hom)

@[reassoc (attr := simp)]
theorem endpoint_parameters (a : Bool) :
    GlobePasting.inclusion.rightUnitor.inv ≫
      whiskerLeft GlobePasting.inclusion (endpoint a) =
      whiskerLeft GlobePasting.inclusion (modelEndpoint a) ≫ parameterIso.hom :=
  Functor.descOfIsLeftKanExtension_fac _ _ _ _

/-- The globally defined endpoints agree with the original chain endpoints
under the canonical comparison. -/
theorem endpoint_comparison (a : Bool) : endpoint a ≫ comparison = modelEndpoint a := by
  apply Functor.hom_ext_of_isLeftKanExtension _ GlobePasting.inclusion.rightUnitor.inv
  apply NatTrans.ext
  funext i
  let e : model.obj (GlobePasting.object i) ≅ cylinder.obj (GlobePasting.object i) :=
    parameterIso.app i
  have he : (endpoint a).app (GlobePasting.object i) =
      (modelEndpoint a).app (GlobePasting.object i) ≫ e.hom := by
    have hh := congrArg (fun q => q.app i) (endpoint_parameters a)
    exact hh
  have hc : e.hom ≫ comparison.app (GlobePasting.object i) = 𝟙 _ :=
    congrArg (fun q => q.app i) parameter_comparison
  change (endpoint a).app (GlobePasting.object i) ≫
    comparison.app (GlobePasting.object i) = (modelEndpoint a).app (GlobePasting.object i)
  calc
    _ = ((modelEndpoint a).app (GlobePasting.object i) ≫ e.hom) ≫
        comparison.app (GlobePasting.object i) := congrArg (fun q => q ≫ _) he
    _ = (modelEndpoint a).app (GlobePasting.object i) ≫
        (e.hom ≫ comparison.app (GlobePasting.object i)) := Category.assoc _ _ _
    _ = _ := by rw [hc, Category.comp_id]

/-- Restricting the global comparison to the generating parameters is an
isomorphism, although no global isomorphism is asserted. -/
theorem comparison_parameter_isIso (i : GlobePasting.Shape) :
    IsIso (comparison.app (GlobePasting.object i)) := by
  let e : model.obj (GlobePasting.object i) ≅ cylinder.obj (GlobePasting.object i) :=
    parameterIso.app i
  have he : e.hom ≫ comparison.app (GlobePasting.object i) = 𝟙 _ :=
    congrArg (fun q => q.app i) parameter_comparison
  have hc : comparison.app (GlobePasting.object i) = e.inv := by
    apply (cancel_epi e.hom).mp
    exact he.trans e.hom_inv_id.symm
  rw [hc]
  infer_instance

end GrayChainExtension

end

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # The pointwise parameter presentation of the actual extended cylinder

This retains its colimit universal property together with the concrete
parameter legs. These are the source-side universal maps for the global
right-adjunction construction.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayChainExtension

open CategoryTheory CategoryTheory.Limits

noncomputable section

def presentationDiagram (C : StrictOmegaCategory.{0}) :
    CostructuredArrow GlobePasting.inclusion C ⥤ StrictOmegaCategory.{0} :=
  CostructuredArrow.proj GlobePasting.inclusion C ⋙ parameters

def presentationIso (C : StrictOmegaCategory.{0}) :
    cylinder.obj C ≅ colimit (presentationDiagram C) :=
  GlobePasting.extensionObjIso parameters C

def presentationCocone (C : StrictOmegaCategory.{0}) : Cocone (presentationDiagram C) where
  pt := cylinder.obj C
  ι := {
    app j := colimit.ι (presentationDiagram C) j ≫ (presentationIso C).inv
    naturality i j f := by
      change (presentationDiagram C).map f ≫
        (colimit.ι (presentationDiagram C) j ≫ (presentationIso C).inv) =
          (colimit.ι (presentationDiagram C) i ≫ (presentationIso C).inv) ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, colimit.w] }

def presentationIsColimit (C : StrictOmegaCategory.{0}) : IsColimit (presentationCocone C) where
  desc s := (presentationIso C).hom ≫ colimit.desc (presentationDiagram C) s
  fac s j := by
    change (colimit.ι (presentationDiagram C) j ≫ (presentationIso C).inv) ≫
      ((presentationIso C).hom ≫ colimit.desc (presentationDiagram C) s) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, colimit.ι_desc]
  uniq s f hf := by
    apply (cancel_epi (presentationIso C).inv).mp
    apply colimit.hom_ext
    intro j
    calc
      _ = (presentationCocone C).ι.app j ≫ f := (Category.assoc _ _ _).symm
      _ = s.ι.app j := hf j
      _ = _ := by
        change s.ι.app j = colimit.ι (presentationDiagram C) j ≫
          ((presentationIso C).inv ≫ ((presentationIso C).hom ≫ colimit.desc (presentationDiagram C) s))
        simp only [Iso.inv_hom_id_assoc, colimit.ι_desc]

/-- The colimit leg is the actual parameter comparison followed by the
extended cylinder of the corresponding strict map. -/
theorem presentation_leg (C : StrictOmegaCategory.{0})
    (j : CostructuredArrow GlobePasting.inclusion C) :
    (presentationCocone C).ι.app j = parameterIso.hom.app j.left ≫ cylinder.map j.hom := by
  exact Functor.ι_leftKanExtensionObjIsoColimit_inv GlobePasting.inclusion parameters C j

/-- Naturality of parameter legs in the category being presented. -/
theorem presentation_leg_map {C D : StrictOmegaCategory.{0}} (f : C ⟶ D)
    (j : CostructuredArrow GlobePasting.inclusion C) :
    (presentationCocone C).ι.app j ≫ cylinder.map f =
      (presentationCocone D).ι.app (CostructuredArrow.mk (Y := j.left) (j.hom ≫ f)) := by
  exact (congrArg (fun q => q ≫ cylinder.map f) (presentation_leg C j)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => parameterIso.hom.app j.left ≫ q)
        (cylinder.map_comp j.hom f).symm).trans
          (presentation_leg D (CostructuredArrow.mk (Y := j.left) (j.hom ≫ f))).symm))

end
end Thomason.Construction.StrictOmegaCategory.GrayChainExtension

end

section

/-! # The ordered pasted basis is the actual strict abelianization

The comparison uses the two matching top cells and the literal strict
pushout. It makes no assertion that positive-table realization preserves
that pushout, and uses no simplex atom-generation hypothesis.
-/

namespace Thomason.Construction.PastingGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

/-- The canonical positive top cell of either half. -/
def top {n k : ℕ} (hkn : k < n) (s : Bool) : (complex n k hkn).realization :=
  (inclusion hkn s).realization.toFun (DirectedGlobeComplex.topCell n)

/-- Both top cells have dimension at most n. -/
theorem top_dimension {n k : ℕ} (hkn : k < n) (s : Bool) :
    (complex n k hkn).realization.DimensionLE n (top hkn s) :=
  (inclusion hkn s).realization.dimensionLE (DirectedGlobeComplex.topCell_dimension n)

/-- The two top cells share their specified target and source k-faces. -/
theorem top_matching {n k : ℕ} (hkn : k < n) :
    (top hkn false).face true k = (top hkn true).face false k := by
  apply Cell.ext
  funext a p
  change Cell.cutTable (top hkn false) true k a p =
    Cell.cutTable (top hkn true) false k a p
  by_cases hp : p < k
  · have hpn : p < n := hp.trans hkn
    simp only [Cell.cutTable, hp, ite_true]
    change embedApp hkn false p (DirectedGlobeComplex.topTable n a p) =
      embedApp hkn true p (DirectedGlobeComplex.topTable n a p)
    simp [DirectedGlobeComplex.topTable, hpn, embed, right, hp]
  · by_cases he : p = k
    · subst p
      simp only [Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]
      change embedApp hkn false k (DirectedGlobeComplex.topTable n true k) =
        embedApp hkn true k (DirectedGlobeComplex.topTable n false k)
      simp [DirectedGlobeComplex.topTable, hkn, embed, right]
    · simp only [Cell.cutTable, hp, he, ite_false]

/-- The actual strict map from the pasted globes to its ordered chain model. -/
def fromPasting {n k : ℕ} (hkn : k < n) :
    StrictOmegaCategory.PastingGlobe.category n n k ⟶ (complex n k hkn).realization :=
  StrictOmegaCategory.PastingGlobe.desc _ (top hkn false) (top hkn true)
    (top_dimension hkn false) (top_dimension hkn true) (top_matching hkn)

/-- Evaluating strict abelianization on the actual ordered chain model. -/
def abelianizationToBasis {n k : ℕ} (hkn : k < n) :
    Hom (StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.PastingGlobe.category n n k)) (complex n k hkn) :=
  StrictOmegaCategory.Abelianization.evaluateHom (fromPasting hkn)

/-- The unit of strict abelianization carries the two pasted cells to
matching positive tables. -/
theorem unit_matching {n k : ℕ} :
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.PastingGlobe.leftCell n n k)).face true k =
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.PastingGlobe.rightCell n n k)).face false k := by
  rw [← StrictOmegaCategory.Abelianization.unitCell_face,
    ← StrictOmegaCategory.Abelianization.unitCell_face]
  exact congrArg (StrictOmegaCategory.Abelianization.unitCell _)
    (StrictOmegaCategory.PastingGlobe.matching n n k)

/-- Read the unit's actual cell tables on each basis. -/
def basisToAbelianization {n k : ℕ} (hkn : k < n) :
    Hom (complex n k hkn) (StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.PastingGlobe.category n n k)) :=
  desc hkn
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.PastingGlobe.leftCell n n k))
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.PastingGlobe.rightCell n n k)) unit_matching

/-- The universal map evaluates the canonical top cell on either side. -/
theorem desc_top {n k : ℕ} {L : DirectedComplex.{0}} (hkn : k < n)
    (x y : Cell L) (hxy : x.face true k = y.face false k) (s : Bool)
    (hb : L.realization.DimensionLE n (if s then y else x)) :
    (desc hkn x y hxy).realization.toFun (top hkn s) = if s then y else x := by
  have h := congrArg (fun f : Hom (DirectedGlobeComplex.complex n) L =>
    f.realization.toFun (DirectedGlobeComplex.topCell n)) (inclusion_desc hkn x y hxy s)
  exact h.trans (DirectedGlobeComplex.cellMap_top_of_bounded n _ hb)

/-- Evaluation of the abelianization unit is the strict comparison itself. -/
theorem abelianizationToBasis_unit {n k : ℕ} (hkn : k < n)
    (x : StrictOmegaCategory.PastingGlobe.category n n k) :
    (abelianizationToBasis hkn).realization.toFun
      (StrictOmegaCategory.Abelianization.unitCell _ x) = (fromPasting hkn).toFun x := by
  exact congrArg (fun f => f.toFun x)
    (StrictOmegaCategory.Abelianization.unit_evaluate (fromPasting hkn))

theorem basisToAbelianization_top {n k : ℕ} (hkn : k < n) (s : Bool) :
    (basisToAbelianization hkn).realization.toFun (top hkn s) =
      StrictOmegaCategory.Abelianization.unitCell _
        (if s then StrictOmegaCategory.PastingGlobe.rightCell n n k
         else StrictOmegaCategory.PastingGlobe.leftCell n n k) := by
  have hb := (StrictOmegaCategory.Abelianization.unit
    (StrictOmegaCategory.PastingGlobe.category n n k)).dimensionLE
      ((if s then StrictOmegaCategory.PastingGlobe.right n n k
        else StrictOmegaCategory.PastingGlobe.left n n k).dimensionLE
          (StrictOmegaCategory.Globe.category_truncated n StrictOmegaCategory.Globe.Cell.top))
  cases s <;> exact desc_top hkn _ _ unit_matching _ hb

/-- The two maps are inverse on strict abelianization, by the actual
universal property of the pasted pair. -/
theorem abelianizationToBasis_inverse {n k : ℕ} (hkn : k < n) :
    Hom.comp (abelianizationToBasis hkn) (basisToAbelianization hkn) = Hom.id _ := by
  apply (StrictOmegaCategory.Abelianization.homEquiv
    (StrictOmegaCategory.PastingGlobe.category n n k) _).injective
  apply StrictOmegaCategory.PastingGlobe.hom_ext
  · change (basisToAbelianization hkn).realization.toFun
      ((abelianizationToBasis hkn).realization.toFun
        (StrictOmegaCategory.Abelianization.unitCell _
          (StrictOmegaCategory.PastingGlobe.leftCell n n k))) = _
    rw [abelianizationToBasis_unit]
    have hl : (fromPasting hkn).toFun
        (StrictOmegaCategory.PastingGlobe.leftCell n n k) = top hkn false :=
      StrictOmegaCategory.PastingGlobe.desc_left _ _ _ _ _ _
    rw [hl]
    exact basisToAbelianization_top hkn false
  · change (basisToAbelianization hkn).realization.toFun
      ((abelianizationToBasis hkn).realization.toFun
        (StrictOmegaCategory.Abelianization.unitCell _
          (StrictOmegaCategory.PastingGlobe.rightCell n n k))) = _
    rw [abelianizationToBasis_unit]
    have hr : (fromPasting hkn).toFun
        (StrictOmegaCategory.PastingGlobe.rightCell n n k) = top hkn true :=
      StrictOmegaCategory.PastingGlobe.desc_right _ _ _ _ _ _
    rw [hr]
    exact basisToAbelianization_top hkn true

/-- The two maps are inverse on the explicit chain basis. -/
theorem basisToAbelianization_inverse {n k : ℕ} (hkn : k < n) :
    Hom.comp (basisToAbelianization hkn) (abelianizationToBasis hkn) = Hom.id _ := by
  apply hom_ext hkn
  all_goals
    apply (DirectedGlobeComplex.homEquiv n (complex n k hkn)).injective
    apply Subtype.ext
  · change (abelianizationToBasis hkn).realization.toFun
      ((basisToAbelianization hkn).realization.toFun (top hkn false)) = top hkn false
    rw [basisToAbelianization_top, abelianizationToBasis_unit]
    exact StrictOmegaCategory.PastingGlobe.desc_left _ _ _ _ _ _
  · change (abelianizationToBasis hkn).realization.toFun
      ((basisToAbelianization hkn).realization.toFun (top hkn true)) = top hkn true
    rw [basisToAbelianization_top, abelianizationToBasis_unit]
    exact StrictOmegaCategory.PastingGlobe.desc_right _ _ _ _ _ _

/-- The ordered finite complex is the actual abelianization of the pasted
pair, with its specified two globe inclusions. -/
def abelianizationIso {n k : ℕ} (hkn : k < n) :
    StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.PastingGlobe.category n n k) ≅ complex n k hkn where
  hom := abelianizationToBasis hkn
  inv := basisToAbelianization hkn
  hom_inv_id := abelianizationToBasis_inverse hkn
  inv_hom_id := basisToAbelianization_inverse hkn

end

end Thomason.Construction.PastingGlobeBasis

end

section

/-! # Actual atoms of the finite pasted-globe basis

Every basis element is the top chain of an explicit bounded positive cell.
Its lower rows are literal singleton faces. Applying the proved prism
construction gives the mixed generator of the right cylinder.
-/

namespace Thomason.Construction.PastingGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Canonical representatives are unchanged by their chosen globe inclusion. -/
theorem embed_self {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    embed hkn b.val.1 ⟨b.val.2, b.property.1⟩ = b := by
  rcases b with ⟨⟨s, a⟩, hv, hs⟩
  cases s with
  | false => rfl
  | true =>
    rcases hs with h | hp | ⟨he, ha⟩
    · cases h
    · simp [embed, right, Nat.not_lt.mpr hp.le, Nat.ne_of_gt hp]
    · have ha' : a = true := ha
      subst p
      subst a
      simp [embed, right]

/-- The atom is the appropriate face of the corresponding globe's top cell. -/
def atom {n k p : ℕ} (hkn : k < n) (b : Basis n k p) : Cell (complex n k hkn) :=
  (inclusion hkn b.val.1).realization.toFun
    ((DirectedGlobeComplex.topCell n).face b.val.2 p)

/-- Its top chain is exactly the chosen basis, on both sides. -/
theorem atom_top {n k p : ℕ} (hkn : k < n) (b : Basis n k p) (a : Bool) :
    (atom hkn b).table a p = Finsupp.single b 1 := by
  change embedApp hkn b.val.1 p
    (Cell.cutTable (DirectedGlobeComplex.topCell n) b.val.2 p a p) = _
  simp only [Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]
  change embedApp hkn b.val.1 p (DirectedGlobeComplex.topTable n b.val.2 p) = _
  rw [DirectedGlobeComplex.topTable_eq_single n p ⟨b.val.2, b.property.1⟩,
    embedApp_single, embed_self]

/-- Every atom is bounded by its basis degree. -/
theorem atom_dimension {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    (complex n k hkn).realization.DimensionLE p (atom hkn b) :=
  (inclusion hkn b.val.1).realization.dimensionLE
    ((DirectedGlobeComplex.complex n).realization.face_dimensionLE b.val.2 p
      (DirectedGlobeComplex.topCell n))

/-- All chains strictly above the basis degree vanish. -/
theorem atom_above {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hpq : p < q) (a : Bool) : (atom hkn b).table a q = 0 :=
  Cell.table_zero_of_dimensionLE (atom_dimension hkn b) hpq a

/-- Every lower row is the corresponding singleton face of that globe. -/
theorem atom_below {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hqp : q < p) (a : Bool) :
    (atom hkn b).table a q = Finsupp.single
      (embed hkn b.val.1 ⟨a, Or.inl (hqp.trans_le (degree_le b))⟩) 1 := by
  have hqn : q < n := hqp.trans_le (degree_le b)
  change embedApp hkn b.val.1 q
    (Cell.cutTable (DirectedGlobeComplex.topCell n) b.val.2 p a q) = _
  simp only [Cell.cutTable, hqp, ite_true]
  change embedApp hkn b.val.1 q (DirectedGlobeComplex.topTable n a q) = _
  simp [DirectedGlobeComplex.topTable, hqn]

/-- Source and target representatives below the top dimension are distinct. -/
theorem embed_polarities_ne {n k q : ℕ} (hkn : k < n) (s : Bool) (hqn : q < n) :
    embed hkn s (⟨false, Or.inl hqn⟩ : DirectedGlobeComplex.Basis n q) ≠
      embed hkn s (⟨true, Or.inl hqn⟩ : DirectedGlobeComplex.Basis n q) := by
  cases s with
  | false => simp [embed, left]
  | true =>
    by_cases hq : q < k
    · simp [embed, right, hq, left]
    · by_cases he : q = k
      · simp [embed, right, he, left]
      · simp [embed, right, hq, he]

/-- The two lower atom rows have disjoint basis supports. -/
theorem atom_lower_disjoint {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (hqp : q < p) (c : Basis n k q) :
    DFunLike.coe (F := Chains n k q) ((atom hkn b).table false q) c = 0 ∨
      DFunLike.coe (F := Chains n k q) ((atom hkn b).table true q) c = 0 := by
  classical
  rw [atom_below hkn b hqp false, atom_below hkn b hqp true]
  have he := embed_polarities_ne hkn b.val.1 (hqp.trans_le (degree_le b))
  by_cases hf : embed hkn b.val.1
      (⟨false, Or.inl (hqp.trans_le (degree_le b))⟩ : DirectedGlobeComplex.Basis n q) = c
  · right
    have ht : embed hkn b.val.1
        (⟨true, Or.inl (hqp.trans_le (degree_le b))⟩ : DirectedGlobeComplex.Basis n q) ≠ c := by
      intro ht
      exact he (hf.trans ht.symm)
    simp [ht]
  · left
    simp [hf]

/-- The mixed tensor generator is the top chain of the explicit prism atom. -/
def mixedAtom {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    Cell (rightCylinder (complex n k hkn)) := RightCylinder.prism (atom hkn b)

theorem mixedAtom_top {n k p : ℕ} (hkn : k < n) (b : Basis n k p) (a : Bool) :
    (mixedAtom hkn b).table a (p+1) = (0, 0, Finsupp.single b 1) := by
  rw [mixedAtom, RightCylinder.prism_top _ (atom_dimension hkn b), atom_top]
  rfl

theorem mixedAtom_dimension {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    (rightCylinder (complex n k hkn)).realization.DimensionLE (p+1) (mixedAtom hkn b) :=
  RightCylinder.prism_dimension _ (atom_dimension hkn b)

/-- Endpoint tensor generators are also actual bounded positive cells. -/
def endpointAtom {n k p : ℕ} (hkn : k < n) (s : Bool) (b : Basis n k p) :
    Cell (rightCylinder (complex n k hkn)) :=
  (RightCylinder.endpoint (complex n k hkn) s).realization.toFun (atom hkn b)

theorem endpointAtom_top {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : Basis n k p) (a : Bool) :
    (endpointAtom hkn s b).table a p =
      (RightCylinder.endpoint (complex n k hkn) s).app p (Finsupp.single b 1) := by
  change (RightCylinder.endpoint _ s).app p ((atom hkn b).table a p) = _
  rw [atom_top]

theorem endpointAtom_dimension {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : Basis n k p) :
    (rightCylinder (complex n k hkn)).realization.DimensionLE p (endpointAtom hkn s b) :=
  (RightCylinder.endpoint (complex n k hkn) s).realization.dimensionLE (atom_dimension hkn b)

end

end Thomason.Construction.PastingGlobeBasis

end

section

/-! # The two actual positive row inclusions in the grid complex -/

namespace Thomason.Construction.GridGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

def embedApp {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) (p : ℕ) :
    PastingGlobeBasis.Chains n k p →ₗ[ℤ] Chains n k l p :=
  Finsupp.linearCombination ℤ (fun b => Finsupp.single (embed hkl hln s b) 1)

@[simp] theorem embedApp_single {n k l p : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (b : PastingGlobeBasis.Basis n k p) (z : ℤ) :
    embedApp hkl hln s p (Finsupp.single b z) = Finsupp.single (embed hkl hln s b) z := by
  simp [embedApp]

theorem embedApp_differential {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) (p : ℕ)
    (u : PastingGlobeBasis.Chains n k (p+1)) :
    embedApp hkl hln s p (PastingGlobeBasis.differential (hkl.trans hln) p u) =
      differential hkl hln p (embedApp hkl hln s (p+1) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    simp only [PastingGlobeBasis.differential_single, map_smul,
      PastingGlobeBasis.boundary, map_sub, embedApp_single,
      differential_single, boundary, face_embed]

theorem embedApp_augmentation {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (u : PastingGlobeBasis.Chains n k 0) :
    weight n k l 0 (embedApp hkl hln s 0 u) = PastingGlobeBasis.weight n k 0 u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z => simp

theorem embedApp_positive {n k l p : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (u : PastingGlobeBasis.Chains n k p) (hu : u ∈ PastingGlobeBasis.positive n k p) :
    embedApp hkl hln s p u ∈ positive n k l p := by
  classical
  change (u.sum fun b z => z • Finsupp.single (embed hkl hln s b) 1) ∈ positive n k l p
  apply (positive n k l p).sum_mem
  intro b hb
  change u b • Finsupp.single (embed hkl hln s b) 1 ∈ positive n k l p
  rw [← Int.toNat_of_nonneg (hu b), natCast_zsmul]
  apply (positive n k l p).nsmul_mem
  intro c
  simp only [Finsupp.single_apply]
  split_ifs <;> norm_num

def inclusion {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) :
    Hom (PastingGlobeBasis.complex n k (hkl.trans hln)) (complex hkl hln) where
  app p := (embedApp hkl hln s p).toAddMonoidHom
  differential := embedApp_differential hkl hln s
  augmentation := embedApp_augmentation hkl hln s
  positive _ _ hu := embedApp_positive hkl hln s _ hu

end
end Thomason.Construction.GridGlobeBasis

end

section

/-! # The positive chain map specified by four matching cell tables -/

namespace Thomason.Construction.GridGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

variable {L : DirectedComplex.{0}}

def value {n k l p : ℕ} (x : Bool → Bool → Cell L) (b : Basis n k l p) : L.group p :=
  (x b.val.1 b.val.2.val.1).table b.val.2.val.2 p

theorem value_embed {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (x : Bool → Bool → Cell L)
    (hv : ∀ a, (x false a).face true l = (x true a).face false l)
    (s : Bool) (b : PastingGlobeBasis.Basis n k p) :
    value x (embed hkl hln s b) =
      PastingGlobeBasis.value (x s false) (x s true) b := by
  cases s with
  | false => cases hb : b.val.1 <;> simp [embed, left, value, PastingGlobeBasis.value, hb]
  | true =>
    by_cases hp : p < l
    · have he := Cell.matching_below (hv b.val.1) b.val.2 hp
      cases hb : b.val.1 <;>
        simpa [embed, hp, left, value, PastingGlobeBasis.value, hb] using he
    · by_cases he : p = l
      · subst p
        by_cases hb : b.val.2 = false
        · have ht := Cell.matching_top (hv b.val.1)
          cases ha : b.val.1 <;>
            simpa [embed, hb, targetBasis, left, value, PastingGlobeBasis.value, ha] using ht
        · cases ha : b.val.1 <;>
            simp [embed, hb, value, PastingGlobeBasis.value, ha]
      · cases ha : b.val.1 <;> simp [embed, hp, he, value, PastingGlobeBasis.value, ha]

def descApp {n k l : ℕ} (x : Bool → Bool → Cell L) (p : ℕ) :
    Chains n k l p →ₗ[ℤ] L.group p :=
  Finsupp.linearCombination ℤ (value x)

@[simp] theorem descApp_single {n k l p : ℕ} (x : Bool → Bool → Cell L)
    (b : Basis n k l p) (z : ℤ) :
    descApp x p (Finsupp.single b z) = z • value x b := by simp [descApp]

theorem descApp_embedApp {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (x : Bool → Bool → Cell L)
    (hv : ∀ a, (x false a).face true l = (x true a).face false l)
    (s : Bool) (p : ℕ) (u : PastingGlobeBasis.Chains n k p) :
    descApp x p (embedApp hkl hln s p u) =
      PastingGlobeBasis.descApp (x s false) (x s true) p u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hw => simp [hu, hw]
  | single b z => simp [value_embed hkl hln x hv]

theorem descApp_differential {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (x : Bool → Bool → Cell L)
    (hh : ∀ b, (x b false).face true k = (x b true).face false k)
    (hv : ∀ a, (x false a).face true l = (x true a).face false l)
    (p : ℕ) (u : Chains n k l (p+1)) :
    descApp x p (differential hkl hln p u) =
      L.differential p (descApp x (p+1) u) := by
  have hs (s : Bool) (b : PastingGlobeBasis.Basis n k (p+1)) (z : ℤ) :
      descApp x p (differential hkl hln p (Finsupp.single (embed hkl hln s b) z)) =
        L.differential p (descApp x (p+1) (Finsupp.single (embed hkl hln s b) z)) := by
    rw [← embedApp_single hkl hln s b z, ← embedApp_differential,
      descApp_embedApp hkl hln x hv, descApp_embedApp hkl hln x hv]
    exact PastingGlobeBasis.descApp_differential (hkl.trans hln)
      (x s false) (x s true) (hh s) p _
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hw => simp [hu, hw]
  | single b z => simpa only [embed_self] using hs b.val.1 b.val.2 z

theorem descApp_augmentation {n k l : ℕ} (x : Bool → Bool → Cell L)
    (u : Chains n k l 0) : L.augmentation (descApp x 0 u) = weight n k l 0 u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hw => simp [hu, hw]
  | single b z => simp [value, Cell.augmentation]

theorem descApp_positive {n k l p : ℕ} (x : Bool → Bool → Cell L)
    (u : Chains n k l p) (hu : u ∈ positive n k l p) :
    descApp x p u ∈ L.positive p := by
  classical
  change (u.sum fun b z => z • value x b) ∈ L.positive p
  apply (L.positive p).sum_mem
  intro b hb
  change u b • value x b ∈ L.positive p
  rw [← Int.toNat_of_nonneg (hu b), natCast_zsmul]
  exact (L.positive p).nsmul_mem ((x b.val.1 b.val.2.val.1).positive b.val.2.val.2 p) _

def desc {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (x : Bool → Bool → Cell L)
    (hh : ∀ b, (x b false).face true k = (x b true).face false k)
    (hv : ∀ a, (x false a).face true l = (x true a).face false l) :
    Hom (complex hkl hln) L where
  app p := (descApp x p).toAddMonoidHom
  differential := descApp_differential hkl hln x hh hv
  augmentation := descApp_augmentation x
  positive _ _ hu := descApp_positive x _ hu

theorem inclusion_desc {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (x : Bool → Bool → Cell L)
    (hh : ∀ b, (x b false).face true k = (x b true).face false k)
    (hv : ∀ a, (x false a).face true l = (x true a).face false l)
    (s : Bool) : Hom.comp (inclusion hkl hln s) (desc hkl hln x hh hv) =
      PastingGlobeBasis.desc (hkl.trans hln) (x s false) (x s true) (hh s) := by
  apply Hom.ext_app
  intro p u
  exact descApp_embedApp hkl hln x hv s p u

theorem hom_ext {n k l : ℕ} (hkl : k < l) (hln : l < n)
    {f g : Hom (complex hkl hln) L}
    (h : ∀ s, Hom.comp (inclusion hkl hln s) f = Hom.comp (inclusion hkl hln s) g) :
    f = g := by
  apply Hom.ext_app
  intro p u
  have hs (s : Bool) (b : PastingGlobeBasis.Basis n k p) (z : ℤ) :
      f.app p (Finsupp.single (embed hkl hln s b) z) =
        g.app p (Finsupp.single (embed hkl hln s b) z) := by
    have he := congrArg (fun q : Hom (PastingGlobeBasis.complex n k (hkl.trans hln)) L =>
      q.app p (Finsupp.single b z)) (h s)
    change f.app p (embedApp hkl hln s p (Finsupp.single b z)) =
      g.app p (embedApp hkl hln s p (Finsupp.single b z)) at he
    simpa only [embedApp_single] using he
  let fp : Chains n k l p →+ L.group p := f.app p
  let gp : Chains n k l p →+ L.group p := g.app p
  change fp u = gp u
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hw => simp [hu, hw]
  | single b z =>
    change f.app p (Finsupp.single b z) = g.app p (Finsupp.single b z)
    simpa only [embed_self] using hs b.val.1 b.val.2 z

end
end Thomason.Construction.GridGlobeBasis

end

section

/-! # Strict pasting and right-cylinder chain compatibility

The constructed lambda adjunction carries the actual pasted-globe square
to a pushout of positive complexes. The universal composite is the sum of
the two cell generators, including after right interval tensoring. No Gray
comparison or preservation property of nu is assumed here.
-/

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe

open CategoryTheory CategoryTheory.Limits _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Lambda sends the universal composable pair to a pushout of actual
positive chain maps. -/
theorem abelianization_isPushout (n m k : ℕ) :
    IsPushout (C := DirectedComplex.{0}) (Abelianization.map (Globe.faceMap true k n))
      (Abelianization.map (Globe.faceMap false k m))
      (Abelianization.map (left n m k)) (Abelianization.map (right n m k)) := by
  have := Abelianization.preservesColimits
  exact Abelianization.functor.map_isPushout
    (IsPushout.of_hasPushout (Globe.faceMap true k n) (Globe.faceMap false k m))

def leftBounded (n m k : ℕ) : Abelianization.Bounded (category n m k) (max n m) :=
  ⟨leftCell n m k, (category n m k).dimensionLE_mono (Nat.le_max_left n m)
    ((left n m k).dimensionLE (Globe.category_truncated n Globe.Cell.top))⟩

def rightBounded (n m k : ℕ) : Abelianization.Bounded (category n m k) (max n m) :=
  ⟨rightCell n m k, (category n m k).dimensionLE_mono (Nat.le_max_right n m)
    ((right n m k).dimensionLE (Globe.category_truncated m Globe.Cell.top))⟩

/-- The chain of the universal composite is exactly the sum of its factors. -/
theorem composite_generator (n m k : ℕ) (hk : k < max n m) :
    Abelianization.generator (category n m k) (max n m)
      ⟨composite n m k, composite_dimension n m k hk⟩ =
    Abelianization.generator (category n m k) (max n m) (leftBounded n m k) +
      Abelianization.generator (category n m k) (max n m) (rightBounded n m k) :=
  Abelianization.generator_composite (category n m k) k hk
    (leftBounded n m k) (rightBounded n m k) (matching n m k)

/-- The chain map of the strict composition parameter has the prescribed sum. -/
theorem compositionMap_generator (n m k : ℕ) (hk : k < max n m) :
    (Abelianization.map (compositionMap n m k hk)).app (max n m)
      (Abelianization.generator (Globe.category (max n m)) (max n m)
        ⟨Globe.Cell.top, Globe.category_truncated (max n m) Globe.Cell.top⟩) =
    Abelianization.generator (category n m k) (max n m) (leftBounded n m k) +
      Abelianization.generator (category n m k) (max n m) (rightBounded n m k) := by
  exact (Abelianization.map_generator (compositionMap n m k hk) (max n m) _).trans
    (composite_generator n m k hk)

/-- The concrete signed chain prism of the universal composition map. -/
def cylinderComposition (n m k : ℕ) (hk : k < max n m) :
    DirectedComplex.Hom
      (rightCylinder (Abelianization.complex (Globe.category (max n m))))
      (rightCylinder (Abelianization.complex (category n m k))) :=
  RightCylinder.map (Abelianization.map (compositionMap n m k hk))

/-- At either endpoint the prism realizes the actual universal composite. -/
theorem cylinderComposition_endpoint (n m k : ℕ) (hk : k < max n m)
    (a : Bool) (j : ℕ)
    (x : (Abelianization.complex (Globe.category (max n m))).group j) :
    (cylinderComposition n m k hk).app j
      ((RightCylinder.endpoint _ a).app j x) =
    (RightCylinder.endpoint _ a).app j
      ((Abelianization.map (compositionMap n m k hk)).app j x) :=
  RightCylinder.map_endpoint (Abelianization.map (compositionMap n m k hk)) a j x

/-- The shifted top component of the right prism retains the sum relation. -/
theorem cylinderComposition_shifted (n m k : ℕ) (hk : k < max n m) :
    (cylinderComposition n m k hk).app (max n m + 1)
      (0, 0, Abelianization.generator (Globe.category (max n m)) (max n m)
        ⟨Globe.Cell.top, Globe.category_truncated (max n m) Globe.Cell.top⟩) =
    (0, 0,
      Abelianization.generator (category n m k) (max n m) (leftBounded n m k) +
        Abelianization.generator (category n m k) (max n m) (rightBounded n m k)) := by
  change ((Abelianization.map (compositionMap n m k hk)).app (max n m + 1) 0,
      (Abelianization.map (compositionMap n m k hk)).app (max n m + 1) 0,
      (Abelianization.map (compositionMap n m k hk)).app (max n m)
        (Abelianization.generator _ _ _)) = _
  rw [map_zero, compositionMap_generator]
  rfl

end

end Thomason.Construction.StrictOmegaCategory.PastingGlobe

end

end OAI
