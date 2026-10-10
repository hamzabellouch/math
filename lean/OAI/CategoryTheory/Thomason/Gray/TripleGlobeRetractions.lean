import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.GlobePastingDensity
import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.GrayMappingEndpointEvaluation
import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.GridGlobeCylinderComparison
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderRetractions
import OAI.CategoryTheory.Thomason.Transfer.GridGlobeCylinderPushout

namespace OAI

section

/-! # Unrestricted interchange for the actual mapping-cell operation

The actual grid-cylinder pushout glues four boundary-compatible maps.
Evaluation of the strict grid diagram proves interchange, first at a
common finite level and then on the filtered-union carrier.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

variable {D : StrictOmegaCategory.{0}} {n k l : ℕ}

def gridGlue (hkl : k < l) (hln : l < n)
    (f : Bool → Bool → (model.obj (Globe.category n) ⟶ D))
    (hh : ∀ b, model.map (Globe.faceMap true k n) ≫ f b false =
      model.map (Globe.faceMap false k n) ≫ f b true)
    (hv : ∀ a, model.map (Globe.faceMap true l n) ≫ f false a =
      model.map (Globe.faceMap false l n) ≫ f true a) :
    model.obj (GridGlobe.category n k l hkl) ⟶ D :=
  (GridGlobeCylinder.isPushout hkl hln).desc
    (glue (hkl.trans hln) (f false false) (f false true) (hh false))
    (glue (hkl.trans hln) (f true false) (f true true) (hh true))
    (grid_row_matching hkl hln _ _ _ _ (hh false) (hh true) (hv false) (hv true))

theorem gridGlue_row (hkl : k < l) (hln : l < n)
    (f : Bool → Bool → (model.obj (Globe.category n) ⟶ D))
    (hh : ∀ b, model.map (Globe.faceMap true k n) ≫ f b false =
      model.map (Globe.faceMap false k n) ≫ f b true)
    (hv : ∀ a, model.map (Globe.faceMap true l n) ≫ f false a =
      model.map (Globe.faceMap false l n) ≫ f true a) (b : Bool) :
    model.map (GridGlobe.row n k l hkl b) ≫ gridGlue hkl hln f hh hv =
      glue (hkl.trans hln) (f b false) (f b true) (hh b) := by
  cases b
  · exact (GridGlobeCylinder.isPushout hkl hln).inl_desc _ _ _
  · exact (GridGlobeCylinder.isPushout hkl hln).inr_desc _ _ _

theorem gridGlue_evaluation (hkl : k < l) (hln : l < n)
    (f : Bool → Bool → (model.obj (Globe.category n) ⟶ D))
    (hh : ∀ b, model.map (Globe.faceMap true k n) ≫ f b false =
      model.map (Globe.faceMap false k n) ≫ f b true)
    (hv : ∀ a, model.map (Globe.faceMap true l n) ≫ f false a =
      model.map (Globe.faceMap false l n) ≫ f true a) (b a : Bool) :
    gridEvaluation (gridGlue hkl hln f hh hv) b a = f b a := by
  change model.map ((if a then PastingGlobe.right n n k else PastingGlobe.left n n k) ≫
    GridGlobe.row n k l hkl b) ≫ _ = _
  rw [model.map_comp, Category.assoc, gridGlue_row]
  cases a
  · exact glue_left _ _ _ _
  · exact glue_right _ _ _ _

/-- Interchange at every common finite mapping level. -/
theorem composite_interchange (hkl : k < l) (hln : l < n)
    (f : Bool → Bool → (model.obj (Globe.category n) ⟶ D))
    (hh : ∀ b, model.map (Globe.faceMap true k n) ≫ f b false =
      model.map (Globe.faceMap false k n) ≫ f b true)
    (hv : ∀ a, model.map (Globe.faceMap true l n) ≫ f false a =
      model.map (Globe.faceMap false l n) ≫ f true a)
    (hV : model.map (Globe.faceMap true l n) ≫
        composite (hkl.trans hln) (f false false) (f false true) (hh false) =
      model.map (Globe.faceMap false l n) ≫
        composite (hkl.trans hln) (f true false) (f true true) (hh true))
    (hH : model.map (Globe.faceMap true k n) ≫
        composite hln (f false false) (f true false) (hv false) =
      model.map (Globe.faceMap false k n) ≫
        composite hln (f false true) (f true true) (hv true)) :
    composite hln
        (composite (hkl.trans hln) (f false false) (f false true) (hh false))
        (composite (hkl.trans hln) (f true false) (f true true) (hh true)) hV =
      composite (hkl.trans hln)
        (composite hln (f false false) (f true false) (hv false))
        (composite hln (f false true) (f true true) (hv true)) hH := by
  let u := gridGlue hkl hln f hh hv
  have he (b a) : gridEvaluation u b a = f b a := gridGlue_evaluation hkl hln f hh hv b a
  have ht : model.map (Globe.faceMap true k n) ≫ gridEvaluation u false false =
      model.map (Globe.faceMap false k n) ≫ gridEvaluation u false true := by
    simpa only [he] using hh false
  have hb : model.map (Globe.faceMap true k n) ≫ gridEvaluation u true false =
      model.map (Globe.faceMap false k n) ≫ gridEvaluation u true true := by
    simpa only [he] using hh true
  have hl : model.map (Globe.faceMap true l n) ≫ gridEvaluation u false false =
      model.map (Globe.faceMap false l n) ≫ gridEvaluation u true false := by
    simpa only [he] using hv false
  have hr : model.map (Globe.faceMap true l n) ≫ gridEvaluation u false true =
      model.map (Globe.faceMap false l n) ≫ gridEvaluation u true true := by
    simpa only [he] using hv true
  have hV' : model.map (Globe.faceMap true l n) ≫
        composite (hkl.trans hln) (gridEvaluation u false false) (gridEvaluation u false true) ht =
      model.map (Globe.faceMap false l n) ≫
        composite (hkl.trans hln) (gridEvaluation u true false) (gridEvaluation u true true) hb := by
    simpa only [he] using hV
  have hH' : model.map (Globe.faceMap true k n) ≫
        composite hln (gridEvaluation u false false) (gridEvaluation u true false) hl =
      model.map (Globe.faceMap false k n) ≫
        composite hln (gridEvaluation u false true) (gridEvaluation u true true) hr := by
    simpa only [he] using hH
  simpa only [he] using grid_interchange hln u ht hb hl hr hV' hH'

/-- Interchange on the images of four finite representatives. -/
theorem interchange_ι (hkl : k < l) (hln : l < n)
    (f : Bool → Bool → (model.obj (Globe.category n) ⟶ D))
    (hh : ∀ b, GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n (f b false)) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n (f b true)))
    (hv : ∀ a, GlobeMappingCells.face model D true l (GlobeMappingCells.ι model D n (f false a)) =
      GlobeMappingCells.face model D false l (GlobeMappingCells.ι model D n (f true a)))
    (hV : GlobeMappingCells.face model D true l
        (comp k (GlobeMappingCells.ι model D n (f false false))
          (GlobeMappingCells.ι model D n (f false true)) (hh false)) =
      GlobeMappingCells.face model D false l
        (comp k (GlobeMappingCells.ι model D n (f true false))
          (GlobeMappingCells.ι model D n (f true true)) (hh true)))
    (hH : GlobeMappingCells.face model D true k
        (comp l (GlobeMappingCells.ι model D n (f false false))
          (GlobeMappingCells.ι model D n (f true false)) (hv false)) =
      GlobeMappingCells.face model D false k
        (comp l (GlobeMappingCells.ι model D n (f false true))
          (GlobeMappingCells.ι model D n (f true true)) (hv true))) :
    comp l
        (comp k (GlobeMappingCells.ι model D n (f false false))
          (GlobeMappingCells.ι model D n (f false true)) (hh false))
        (comp k (GlobeMappingCells.ι model D n (f true false))
          (GlobeMappingCells.ι model D n (f true true)) (hh true)) hV =
      comp k
        (comp l (GlobeMappingCells.ι model D n (f false false))
          (GlobeMappingCells.ι model D n (f true false)) (hv false))
        (comp l (GlobeMappingCells.ι model D n (f false true))
          (GlobeMappingCells.ι model D n (f true true)) (hv true)) hH := by
  have hhF (b) := (GlobeMappingCells.faces_eq_iff model D true false k n n
    (f b false) (f b true)).mp (hh b)
  have hvF (a) := (GlobeMappingCells.faces_eq_iff model D true false l n n
    (f false a) (f true a)).mp (hv a)
  have heH (b) := comp_ι (hkl.trans hln) (f b false) (f b true) (hhF b) (hh b)
  have heV (a) := comp_ι hln (f false a) (f true a) (hvF a) (hv a)
  have hV' : GlobeMappingCells.face model D true l
        (GlobeMappingCells.ι model D n
          (composite (hkl.trans hln) (f false false) (f false true) (hhF false))) =
      GlobeMappingCells.face model D false l
        (GlobeMappingCells.ι model D n
          (composite (hkl.trans hln) (f true false) (f true true) (hhF true))) :=
    (congrArg (GlobeMappingCells.face model D true l) (heH false)).symm.trans
      (hV.trans (congrArg (GlobeMappingCells.face model D false l) (heH true)))
  have hH' : GlobeMappingCells.face model D true k
        (GlobeMappingCells.ι model D n
          (composite hln (f false false) (f true false) (hvF false))) =
      GlobeMappingCells.face model D false k
        (GlobeMappingCells.ι model D n
          (composite hln (f false true) (f true true) (hvF true))) :=
    (congrArg (GlobeMappingCells.face model D true k) (heV false)).symm.trans
      (hH.trans (congrArg (GlobeMappingCells.face model D false k) (heV true)))
  have hVF := (GlobeMappingCells.faces_eq_iff model D true false l n n _ _).mp hV'
  have hHF := (GlobeMappingCells.faces_eq_iff model D true false k n n _ _).mp hH'
  exact (comp_congr (heH false) (heH true) hV hV').trans
    ((comp_ι hln _ _ hVF hV').trans
      ((congrArg (GlobeMappingCells.ι model D n)
        (composite_interchange hkl hln f hhF hvF hVF hHF)).trans
          ((comp_ι (hkl.trans hln) _ _ hHF hH').symm.trans
            (comp_congr (heV false) (heV true) hH hH').symm)))

/-- Interchange for any four matching cells of the actual mapping carrier. -/
theorem interchange_family (k l : ℕ) (hkl : k < l) (x : Bool → Bool → Cell D)
    (hh : ∀ b, GlobeMappingCells.face model D true k (x b false) =
      GlobeMappingCells.face model D false k (x b true))
    (hv : ∀ a, GlobeMappingCells.face model D true l (x false a) =
      GlobeMappingCells.face model D false l (x true a))
    (hV : GlobeMappingCells.face model D true l (comp k (x false false) (x false true) (hh false)) =
      GlobeMappingCells.face model D false l (comp k (x true false) (x true true) (hh true)))
    (hH : GlobeMappingCells.face model D true k (comp l (x false false) (x true false) (hv false)) =
      GlobeMappingCells.face model D false k (comp l (x false true) (x true true) (hv true))) :
    comp l (comp k (x false false) (x false true) (hh false))
        (comp k (x true false) (x true true) (hh true)) hV =
      comp k (comp l (x false false) (x true false) (hv false))
        (comp l (x false true) (x true true) (hv true)) hH := by
  obtain ⟨n, hn, f, hf⟩ := GlobeMappingCells.exists_representatives_finite_above model D
    (fun i : Bool × Bool => x i.1 i.2) (l+1)
  have hln : l < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self l) hn
  let F (b a) := f (b, a)
  have he (b a) : GlobeMappingCells.ι model D n (F b a) = x b a := hf (b, a)
  have hh' (b) : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n (F b false)) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n (F b true)) := by
    simpa only [he] using hh b
  have hv' (a) : GlobeMappingCells.face model D true l (GlobeMappingCells.ι model D n (F false a)) =
      GlobeMappingCells.face model D false l (GlobeMappingCells.ι model D n (F true a)) := by
    simpa only [he] using hv a
  have hV' : GlobeMappingCells.face model D true l
        (comp k (GlobeMappingCells.ι model D n (F false false))
          (GlobeMappingCells.ι model D n (F false true)) (hh' false)) =
      GlobeMappingCells.face model D false l
        (comp k (GlobeMappingCells.ι model D n (F true false))
          (GlobeMappingCells.ι model D n (F true true)) (hh' true)) := by
    simpa only [he] using hV
  have hH' : GlobeMappingCells.face model D true k
        (comp l (GlobeMappingCells.ι model D n (F false false))
          (GlobeMappingCells.ι model D n (F true false)) (hv' false)) =
      GlobeMappingCells.face model D false k
        (comp l (GlobeMappingCells.ι model D n (F false true))
          (GlobeMappingCells.ι model D n (F true true)) (hv' true)) := by
    simpa only [he] using hH
  simpa only [he] using interchange_ι hkl hln F hh' hv' hV' hH'

/-- The strict interchange law in the usual four-cell notation. -/
theorem interchange (k l : ℕ) (hkl : k < l) (a b c d : Cell D)
    (hab : GlobeMappingCells.face model D true k a = GlobeMappingCells.face model D false k b)
    (hcd : GlobeMappingCells.face model D true k c = GlobeMappingCells.face model D false k d)
    (hac : GlobeMappingCells.face model D true l a = GlobeMappingCells.face model D false l c)
    (hbd : GlobeMappingCells.face model D true l b = GlobeMappingCells.face model D false l d)
    (hl : GlobeMappingCells.face model D true l (comp k a b hab) =
      GlobeMappingCells.face model D false l (comp k c d hcd))
    (hr : GlobeMappingCells.face model D true k (comp l a c hac) =
      GlobeMappingCells.face model D false k (comp l b d hbd)) :
    comp l (comp k a b hab) (comp k c d hcd) hl =
      comp k (comp l a c hac) (comp l b d hbd) hr := by
  let x (r s : Bool) : Cell D := if r then (if s then d else c) else (if s then b else a)
  have hh (r) : GlobeMappingCells.face model D true k (x r false) =
      GlobeMappingCells.face model D false k (x r true) := by
    cases r
    · exact hab
    · exact hcd
  have hv (s) : GlobeMappingCells.face model D true l (x false s) =
      GlobeMappingCells.face model D false l (x true s) := by
    cases s
    · exact hac
    · exact hbd
  exact interchange_family k l hkl x hh hv hl hr

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # Currying an actual chain-cylinder map on cells

For any strict category C, a map from its concrete chain model evaluates
all finite globe representatives. The resulting mapping cells are
independent of the chosen bounds and preserve faces and composition.
This supplies naturality on all finite parameters for the right adjunction.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

variable {C D E : StrictOmegaCategory.{0}}

private theorem curry_rep_lower (u : model.obj C ⟶ D) (x : C) {n m : ℕ}
    (hx : C.DimensionLE n x) (hm : C.DimensionLE m x) (hnm : n ≤ m) :
    GlobeMappingCells.ι model D m (model.map (Globe.lift C x hm) ≫ u) =
      GlobeMappingCells.ι model D n (model.map (Globe.lift C x hx) ≫ u) := by
  have he : Globe.lift C x hm = Globe.lower m n hnm ≫ Globe.lift C x hx := by
    apply Globe.hom_ext
    rfl
  rw [he, model.map_comp, Category.assoc, GlobeMappingCells.ι_lower]

def cellCurry (u : model.obj C ⟶ D) (x : C) : Cell D :=
  GlobeMappingCells.ι model D (Classical.choose (C.finite_dimension x))
    (model.map (Globe.lift C x (Classical.choose_spec (C.finite_dimension x))) ≫ u)

/-- Every dimension bound computes the same curried cell. -/
theorem cellCurry_eq (u : model.obj C ⟶ D) (x : C) {n : ℕ} (hx : C.DimensionLE n x) :
    cellCurry u x = GlobeMappingCells.ι model D n (model.map (Globe.lift C x hx) ≫ u) := by
  let r := Classical.choose (C.finite_dimension x)
  have hr : C.DimensionLE r x := Classical.choose_spec (C.finite_dimension x)
  let m := max r n
  have hm : C.DimensionLE m x := C.dimensionLE_mono (Nat.le_max_left _ _) hr
  exact (curry_rep_lower u x hr hm (Nat.le_max_left _ _)).symm.trans
    (curry_rep_lower u x hx hm (Nat.le_max_right _ _))

/-- Restriction to any bounded cell is exactly its globe representative. -/
theorem cellCurry_globe (u : model.obj C ⟶ D) {n : ℕ} (s : Globe.category n ⟶ C) :
    cellCurry u (s.toFun Globe.Cell.top) = GlobeMappingCells.ι model D n (model.map s ≫ u) := by
  have hx := s.dimensionLE (Globe.category_truncated n Globe.Cell.top)
  have hs : Globe.lift C (s.toFun Globe.Cell.top) hx = s := by
    apply Globe.hom_ext
    rfl
  rw [cellCurry_eq u _ hx, hs]

theorem cellCurry_face (u : model.obj C ⟶ D) (a : Bool) (r : ℕ) (x : C) :
    cellCurry u (C.face a r x) = GlobeMappingCells.face model D a r (cellCurry u x) := by
  obtain ⟨n, hn⟩ := C.finite_dimension x
  have hx : C.DimensionLE n x := hn
  rw [cellCurry_eq u _ (C.face_dimensionLE a r x), cellCurry_eq u x hx,
    GlobeMappingCells.face_ι, ← Category.assoc, ← model.map_comp]
  exact congrArg (fun q => GlobeMappingCells.ι model D r (model.map q ≫ u))
    (Globe.faceMap_lift C x hx a r).symm

/-- Cellwise currying respects each defined composition. -/
theorem cellCurry_comp (u : model.obj C ⟶ D) (k : ℕ) (x y : C)
    (h : C.target k x = C.source k y)
    (h' : GlobeMappingCells.face model D true k (cellCurry u x) =
      GlobeMappingCells.face model D false k (cellCurry u y)) :
    cellCurry u (C.comp k x y h) = comp k (cellCurry u x) (cellCurry u y) h' := by
  obtain ⟨nx, hx⟩ := C.finite_dimension x
  obtain ⟨ny, hy⟩ := C.finite_dimension y
  let n := max (k+1) (max nx ny)
  have hk : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_left _ _)
  have hxn : C.DimensionLE n x := C.dimensionLE_mono
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) hx
  have hyn : C.DimensionLE n y := C.dimensionLE_mono
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)) hy
  let f := model.map (Globe.lift C x hxn) ≫ u
  let g := model.map (Globe.lift C y hyn) ≫ u
  have hf : GlobeMappingCells.ι model D n f = cellCurry u x := (cellCurry_eq u x hxn).symm
  have hg : GlobeMappingCells.ι model D n g = cellCurry u y := (cellCurry_eq u y hyn).symm
  have hm := GlobeMappingCells.matching_representatives model D _ _ h' f g hf hg
  have hm' := (GlobeMappingCells.faces_eq_iff model D true false k n n f g).mpr hm
  let p := PastingGlobe.desc C x y hxn hyn h
  have hpL : PastingGlobe.left n n k ≫ p = Globe.lift C x hxn := by
    apply Globe.hom_ext
    exact PastingGlobe.desc_left _ _ _ _ _ _
  have hpR : PastingGlobe.right n n k ≫ p = Globe.lift C y hyn := by
    apply Globe.hom_ext
    exact PastingGlobe.desc_right _ _ _ _ _ _
  have hcomp := C.dimensionLE_comp hk hxn hyn h
  have hpC : compositionGlobe n k hk ≫ p = Globe.lift C (C.comp k x y h) hcomp := by
    apply Globe.hom_ext
    exact PastingGlobe.desc_composite _ _ _ _ _ _
  have hc := composite_evaluation_of_legs hk p u f g
    (congrArg (fun q => model.map q ≫ u) hpL)
    (congrArg (fun q => model.map q ≫ u) hpR) hm
  rw [hpC] at hc
  exact (cellCurry_eq u _ hcomp).trans
    ((congrArg (GlobeMappingCells.ι model D n) hc).symm.trans
      ((comp_ι hk f g hm hm').symm.trans (comp_congr hf hg hm' h')))

/-- Currying commutes with an arbitrary strict map of source categories. -/
theorem cellCurry_precomp {B : StrictOmegaCategory.{0}} (s : B ⟶ C)
    (u : model.obj C ⟶ D) (x : B) :
    cellCurry (model.map s ≫ u) x = cellCurry u (s.toFun x) := by
  obtain ⟨n, hx⟩ := B.finite_dimension x
  rw [cellCurry_eq _ x hx, cellCurry_eq u _ (s.dimensionLE hx)]
  have he : Globe.lift B x hx ≫ s = Globe.lift C (s.toFun x) (s.dimensionLE hx) := by
    apply Globe.hom_ext
    rfl
  rw [← Category.assoc, ← model.map_comp, he]

/-- Currying commutes with postcomposition in the target. -/
theorem cellCurry_postcomp (u : model.obj C ⟶ D) (v : D ⟶ E) (x : C) :
    cellCurry (u ≫ v) x = GlobeMappingCells.map model v (cellCurry u x) := by
  obtain ⟨n, hx⟩ := C.finite_dimension x
  rw [cellCurry_eq _ x hx, cellCurry_eq u x hx, GlobeMappingCells.map_ι, Category.assoc]

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # The three-globe basis is the actual strict abelianization -/

namespace Thomason.Construction.TripleGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

def top {n k : ℕ} (hkn : k < n) (i : Fin 3) : (complex n k hkn).realization :=
  (inclusion hkn i).realization.toFun (DirectedGlobeComplex.topCell n)

theorem top_dimension {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    (complex n k hkn).realization.DimensionLE n (top hkn i) :=
  (inclusion hkn i).realization.dimensionLE (DirectedGlobeComplex.topCell_dimension n)

theorem top_matching {n k : ℕ} (hkn : k < n) (i : Fin 2) :
    (top hkn i.castSucc).face true k = (top hkn i.succ).face false k := by
  apply Cell.ext
  funext a p
  change Cell.cutTable (top hkn i.castSucc) true k a p =
    Cell.cutTable (top hkn i.succ) false k a p
  by_cases hp : p < k
  · have hpn : p < n := hp.trans hkn
    simp only [Cell.cutTable, hp, ite_true]
    change embedApp hkn i.castSucc p (DirectedGlobeComplex.topTable n a p) =
      embedApp hkn i.succ p (DirectedGlobeComplex.topTable n a p)
    simp [DirectedGlobeComplex.topTable, hpn, embed, hp]
  · by_cases he : p = k
    · subst p
      simp only [Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]
      change embedApp hkn i.castSucc k (DirectedGlobeComplex.topTable n true k) =
        embedApp hkn i.succ k (DirectedGlobeComplex.topTable n false k)
      fin_cases i <;> simp [DirectedGlobeComplex.topTable, hkn, embed, predecessor]
    · simp only [Cell.cutTable, hp, he, ite_false]

def fromTriple {n k : ℕ} (hkn : k < n) :
    StrictOmegaCategory.TripleGlobe.category n k ⟶ (complex n k hkn).realization :=
  StrictOmegaCategory.TripleGlobe.desc _ (top hkn) (top_dimension hkn) (top_matching hkn)

@[simp] theorem fromTriple_cell {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    (fromTriple hkn).toFun (StrictOmegaCategory.TripleGlobe.cell n k i) = top hkn i :=
  StrictOmegaCategory.TripleGlobe.desc_cell _ _ _ _ i

def abelianizationToBasis {n k : ℕ} (hkn : k < n) :
    Hom (StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.TripleGlobe.category n k)) (complex n k hkn) :=
  StrictOmegaCategory.Abelianization.evaluateHom (fromTriple hkn)

theorem unit_matching {n k : ℕ} (i : Fin 2) :
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.TripleGlobe.cell n k i.castSucc)).face true k =
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.TripleGlobe.cell n k i.succ)).face false k := by
  rw [← StrictOmegaCategory.Abelianization.unitCell_face,
    ← StrictOmegaCategory.Abelianization.unitCell_face]
  exact congrArg (StrictOmegaCategory.Abelianization.unitCell _)
    (StrictOmegaCategory.TripleGlobe.adjacent_matching n k i)

def basisToAbelianization {n k : ℕ} (hkn : k < n) :
    Hom (complex n k hkn) (StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.TripleGlobe.category n k)) :=
  desc hkn (fun i => StrictOmegaCategory.Abelianization.unitCell _
    (StrictOmegaCategory.TripleGlobe.cell n k i)) unit_matching

theorem desc_top {n k : ℕ} {L : DirectedComplex.{0}} (hkn : k < n)
    (x : Fin 3 → Cell L)
    (hm : ∀ i : Fin 2, (x i.castSucc).face true k = (x i.succ).face false k)
    (i : Fin 3) (hb : L.realization.DimensionLE n (x i)) :
    (desc hkn x hm).realization.toFun (top hkn i) = x i := by
  have h := congrArg (fun f : Hom (DirectedGlobeComplex.complex n) L =>
    f.realization.toFun (DirectedGlobeComplex.topCell n)) (inclusion_desc hkn x hm i)
  exact h.trans (DirectedGlobeComplex.cellMap_top_of_bounded n _ hb)

theorem abelianizationToBasis_unit {n k : ℕ} (hkn : k < n)
    (x : StrictOmegaCategory.TripleGlobe.category n k) :
    (abelianizationToBasis hkn).realization.toFun
      (StrictOmegaCategory.Abelianization.unitCell _ x) = (fromTriple hkn).toFun x :=
  congrArg (fun f => f.toFun x)
    (StrictOmegaCategory.Abelianization.unit_evaluate (fromTriple hkn))

theorem basisToAbelianization_top {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    (basisToAbelianization hkn).realization.toFun (top hkn i) =
      StrictOmegaCategory.Abelianization.unitCell _
        (StrictOmegaCategory.TripleGlobe.cell n k i) := by
  exact desc_top hkn _ unit_matching i
    ((StrictOmegaCategory.Abelianization.unit _).dimensionLE
      (StrictOmegaCategory.TripleGlobe.cell_dimension n k i))

theorem abelianizationToBasis_inverse {n k : ℕ} (hkn : k < n) :
    Hom.comp (abelianizationToBasis hkn) (basisToAbelianization hkn) = Hom.id _ := by
  apply (StrictOmegaCategory.Abelianization.homEquiv
    (StrictOmegaCategory.TripleGlobe.category n k) _).injective
  apply StrictOmegaCategory.TripleGlobe.hom_ext
  intro i
  change (basisToAbelianization hkn).realization.toFun
    ((abelianizationToBasis hkn).realization.toFun
      (StrictOmegaCategory.Abelianization.unitCell _
        (StrictOmegaCategory.TripleGlobe.cell n k i))) = _
  rw [abelianizationToBasis_unit, fromTriple_cell]
  exact basisToAbelianization_top hkn i

theorem basisToAbelianization_inverse {n k : ℕ} (hkn : k < n) :
    Hom.comp (basisToAbelianization hkn) (abelianizationToBasis hkn) = Hom.id _ := by
  apply hom_ext hkn
  intro i
  apply (DirectedGlobeComplex.homEquiv n (complex n k hkn)).injective
  apply Subtype.ext
  change (abelianizationToBasis hkn).realization.toFun
    ((basisToAbelianization hkn).realization.toFun (top hkn i)) = top hkn i
  rw [basisToAbelianization_top, abelianizationToBasis_unit, fromTriple_cell]

def abelianizationIso {n k : ℕ} (hkn : k < n) :
    StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.TripleGlobe.category n k) ≅ complex n k hkn where
  hom := abelianizationToBasis hkn
  inv := basisToAbelianization hkn
  hom_inv_id := abelianizationToBasis_inverse hkn
  inv_hom_id := basisToAbelianization_inverse hkn

end
end Thomason.Construction.TripleGlobeBasis

end

section

/-! # Atomic images of the pair and final globe in the triple -/

namespace Thomason.Construction.TripleGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

theorem embed_lower {n k p q : ℕ} (hkn : k < n) (i : Fin 3)
    (b : DirectedGlobeComplex.Basis n p) (c : DirectedGlobeComplex.Basis n q)
    (hqp : q < p) : embed hkn i c = embed hkn (embed hkn i b).val.1 c := by
  by_cases hp : p < k
  · simp [embed, show q < k by omega]
  · by_cases he : p = k
    · simp [embed, show q < k by omega]
    · simp [embed, hp, he]

theorem inclusion_basisAtom {n k p : ℕ} (hkn : k < n) (i : Fin 3)
    (b : DirectedGlobeComplex.Basis n p) :
    (inclusion hkn i).realization.toFun (DirectedGlobeComplex.basisAtom n p b) =
      atom hkn (embed hkn i b) := by
  apply Cell.ext
  funext side q
  change embedApp hkn i q ((DirectedGlobeComplex.basisAtom n p b).table side q) = _
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · rw [DirectedGlobeComplex.basisAtom_below n p b q hqp side,
      embedApp_single, atom_below hkn (embed hkn i b) hqp side]
    congr 1
    exact embed_lower hkn i b _ hqp
  · rw [DirectedGlobeComplex.basisAtom_top, embedApp_single, atom_top]
  · rw [DirectedGlobeComplex.basisAtom_above n p b q hpq side]
    change embedApp hkn i q (0 : DirectedGlobeComplex.Chains n q) = _
    rw [map_zero, atom_above hkn (embed hkn i b) hpq side]
    rfl

def pairCopy (s : Bool) : Fin 3 := if s then 1 else 0

def pairEmbed {n k p : ℕ} (hkn : k < n) (b : PastingGlobeBasis.Basis n k p) :
    Basis n k p :=
  embed hkn (pairCopy b.val.1) ⟨b.val.2, b.property.1⟩

def pairInclusion {n k : ℕ} (hkn : k < n) :
    Hom (PastingGlobeBasis.complex n k hkn) (complex n k hkn) :=
  PastingGlobeBasis.desc hkn (top hkn 0) (top hkn 1) (top_matching hkn 0)

theorem inclusion_pairInclusion {n k : ℕ} (hkn : k < n) (s : Bool) :
    Hom.comp (PastingGlobeBasis.inclusion hkn s) (pairInclusion hkn) =
      inclusion hkn (pairCopy s) := by
  apply (DirectedGlobeComplex.homEquiv n (complex n k hkn)).injective
  apply Subtype.ext
  change (pairInclusion hkn).realization.toFun (PastingGlobeBasis.top hkn s) =
    top hkn (pairCopy s)
  cases s <;> exact PastingGlobeBasis.desc_top hkn _ _ (top_matching hkn 0) _
    (top_dimension hkn _)

theorem pairInclusion_atom {n k p : ℕ} (hkn : k < n)
    (b : PastingGlobeBasis.Basis n k p) :
    (pairInclusion hkn).realization.toFun (PastingGlobeBasis.atom hkn b) =
      atom hkn (pairEmbed hkn b) := by
  have he := congrArg (fun f : Hom (DirectedGlobeComplex.complex n) (complex n k hkn) =>
    f.realization.toFun (DirectedGlobeComplex.basisAtom n p ⟨b.val.2, b.property.1⟩))
    (inclusion_pairInclusion hkn b.val.1)
  exact he.trans (inclusion_basisAtom hkn (pairCopy b.val.1) _)

def globeCylinderIndex {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    {p : ℕ} → (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p →
      (cylinderOrderedAtomBasis hkn).Index p
  | _, .endpoint a b => .endpoint a (embed hkn i b)
  | _, .mixed b => .mixed (embed hkn i b)

def pairCylinderIndex {n k : ℕ} (hkn : k < n) :
    {p : ℕ} → PastingGlobeCylinderBasis.Basis n k p →
      (cylinderOrderedAtomBasis hkn).Index p
  | _, .endpoint a b => .endpoint a (pairEmbed hkn b)
  | _, .mixed b => .mixed (pairEmbed hkn b)

theorem globeCylinder_atom {n k p : ℕ} (hkn : k < n) (i : Fin 3)
    (b : (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p) :
    (RightCylinder.map (inclusion hkn i)).realization.toFun
      ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b) =
        (cylinderOrderedAtomBasis hkn).atom p (globeCylinderIndex hkn i b) := by
  cases b with
  | endpoint a b =>
    have he : Cell.map (RightCylinder.map (inclusion hkn i))
        (Cell.map (RightCylinder.endpoint _ a) (DirectedGlobeComplex.basisAtom n p b)) =
        Cell.map (RightCylinder.endpoint _ a)
          (Cell.map (inclusion hkn i) (DirectedGlobeComplex.basisAtom n p b)) := by
      apply Cell.ext
      funext c q
      exact RightCylinder.map_endpoint (inclusion hkn i) a q _
    exact he.trans (congrArg (Cell.map (RightCylinder.endpoint _ a))
      (inclusion_basisAtom hkn i b))
  | @mixed r b =>
    exact (RightCylinder.prism_naturality (inclusion hkn i)
      (DirectedGlobeComplex.basisAtom n r b)).trans
      (congrArg RightCylinder.prism (inclusion_basisAtom hkn i b))

theorem pairCylinder_atom {n k p : ℕ} (hkn : k < n)
    (b : PastingGlobeCylinderBasis.Basis n k p) :
    (RightCylinder.map (pairInclusion hkn)).realization.toFun
      (PastingGlobeCylinderBasis.atom hkn b) =
        (cylinderOrderedAtomBasis hkn).atom p (pairCylinderIndex hkn b) := by
  cases b with
  | endpoint a b =>
    have he : Cell.map (RightCylinder.map (pairInclusion hkn))
        (Cell.map (RightCylinder.endpoint _ a) (PastingGlobeBasis.atom hkn b)) =
        Cell.map (RightCylinder.endpoint _ a)
          (Cell.map (pairInclusion hkn) (PastingGlobeBasis.atom hkn b)) := by
      apply Cell.ext
      funext c q
      exact RightCylinder.map_endpoint (pairInclusion hkn) a q _
    exact he.trans (congrArg (Cell.map (RightCylinder.endpoint _ a))
      (pairInclusion_atom hkn b))
  | @mixed r b =>
    exact (RightCylinder.prism_naturality (pairInclusion hkn)
      (PastingGlobeBasis.atom hkn b)).trans
      (congrArg RightCylinder.prism (pairInclusion_atom hkn b))

end
end Thomason.Construction.TripleGlobeBasis

end

section

/-! # Exact comparison of the triple's chain-model cylinder -/

namespace Thomason.Construction.TripleGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory StrictOmegaCategory

noncomputable section

theorem abelianization_globe {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    Abelianization.functor.map (TripleGlobe.inclusion n k i) ≫ (abelianizationIso hkn).hom =
      (DirectedGlobeComplex.abelianizationIso n).hom ≫ inclusion hkn i := by
  let a : Abelianization.functor.obj (Globe.category n) ⟶ complex n k hkn :=
    (DirectedGlobeComplex.abelianizationIso n).hom ≫ inclusion hkn i
  let b : Abelianization.functor.obj (TripleGlobe.category n k) ⟶ complex n k hkn :=
    (abelianizationIso hkn).hom
  change Abelianization.functor.map (TripleGlobe.inclusion n k i) ≫ b = a
  apply (Abelianization.adjunction.homEquiv _ _).injective
  rw [Abelianization.adjunction.homEquiv_naturality_left]
  change TripleGlobe.inclusion n k i ≫ (Abelianization.unit _ ≫
      (Abelianization.evaluateHom (fromTriple hkn)).realization) =
    (Abelianization.unit _ ≫
      (Abelianization.evaluateHom (DirectedGlobeComplex.fromGlobe n)).realization) ≫
      (inclusion hkn i).realization
  have ht : Abelianization.unit (TripleGlobe.category n k) ≫
      (Abelianization.evaluateHom (fromTriple hkn)).realization = fromTriple hkn :=
    Abelianization.unit_evaluate _
  have hg : Abelianization.unit (Globe.category n) ≫
      (Abelianization.evaluateHom (DirectedGlobeComplex.fromGlobe n)).realization =
        DirectedGlobeComplex.fromGlobe n := Abelianization.unit_evaluate _
  rw [ht, hg]
  apply Globe.hom_ext
  exact fromTriple_cell hkn i

theorem abelianization_pair {n k : ℕ} (hkn : k < n) :
    Abelianization.functor.map (TripleGlobe.pair n k) ≫ (abelianizationIso hkn).hom =
      (PastingGlobeBasis.abelianizationIso hkn).hom ≫ pairInclusion hkn := by
  let a : Abelianization.functor.obj (PastingGlobe.category n n k) ⟶ complex n k hkn :=
    (PastingGlobeBasis.abelianizationIso hkn).hom ≫ pairInclusion hkn
  let b : Abelianization.functor.obj (TripleGlobe.category n k) ⟶ complex n k hkn :=
    (abelianizationIso hkn).hom
  change Abelianization.functor.map (TripleGlobe.pair n k) ≫ b = a
  apply (Abelianization.adjunction.homEquiv _ _).injective
  rw [Abelianization.adjunction.homEquiv_naturality_left]
  change TripleGlobe.pair n k ≫ (Abelianization.unit _ ≫
      (Abelianization.evaluateHom (fromTriple hkn)).realization) =
    (Abelianization.unit _ ≫
      (Abelianization.evaluateHom (PastingGlobeBasis.fromPasting hkn)).realization) ≫
      (pairInclusion hkn).realization
  have ht : Abelianization.unit (TripleGlobe.category n k) ≫
      (Abelianization.evaluateHom (fromTriple hkn)).realization = fromTriple hkn :=
    Abelianization.unit_evaluate _
  have hp : Abelianization.unit (PastingGlobe.category n n k) ≫
      (Abelianization.evaluateHom (PastingGlobeBasis.fromPasting hkn)).realization =
        PastingGlobeBasis.fromPasting hkn := Abelianization.unit_evaluate _
  rw [ht, hp]
  apply PastingGlobe.hom_ext
  · change (fromTriple hkn).toFun (TripleGlobe.cell n k 0) =
      (pairInclusion hkn).realization.toFun
        ((PastingGlobeBasis.fromPasting hkn).toFun (PastingGlobe.leftCell n n k))
    have hl : (PastingGlobeBasis.fromPasting hkn).toFun (PastingGlobe.leftCell n n k) =
        PastingGlobeBasis.top hkn false := PastingGlobe.desc_left _ _ _ _ _ _
    rw [fromTriple_cell, hl]
    exact (PastingGlobeBasis.desc_top hkn _ _ (top_matching hkn 0) false
      (top_dimension hkn 0)).symm
  · change (fromTriple hkn).toFun (TripleGlobe.cell n k 1) =
      (pairInclusion hkn).realization.toFun
        ((PastingGlobeBasis.fromPasting hkn).toFun (PastingGlobe.rightCell n n k))
    have hr : (PastingGlobeBasis.fromPasting hkn).toFun (PastingGlobe.rightCell n n k) =
        PastingGlobeBasis.top hkn true := PastingGlobe.desc_right _ _ _ _ _ _
    rw [fromTriple_cell, hr]
    exact (PastingGlobeBasis.desc_top hkn _ _ (top_matching hkn 0) true
      (top_dimension hkn 1)).symm

def modelIso {n k : ℕ} (hkn : k < n) :
    GrayChainExtension.model.obj (TripleGlobe.category n k) ≅
      (rightCylinder (complex n k hkn)).realization :=
  (rightCylinderFunctor ⋙ realizationFunctor).mapIso (abelianizationIso hkn)

def globeModelIso (n : ℕ) : GrayChainExtension.model.obj (Globe.category n) ≅
    (rightCylinder (DirectedGlobeComplex.complex n)).realization :=
  (rightCylinderFunctor ⋙ realizationFunctor).mapIso (DirectedGlobeComplex.abelianizationIso n)

theorem model_globe {n k : ℕ} (hkn : k < n) (i : Fin 3) :
    GrayChainExtension.model.map (TripleGlobe.inclusion n k i) ≫ (modelIso hkn).hom =
      (globeModelIso n).hom ≫ (RightCylinder.map (inclusion hkn i)).realization := by
  let T := rightCylinderFunctor ⋙ realizationFunctor
  exact (T.map_comp (Abelianization.functor.map (TripleGlobe.inclusion n k i))
    (abelianizationIso hkn).hom).symm.trans
      ((congrArg T.map (abelianization_globe hkn i)).trans
        (T.map_comp (DirectedGlobeComplex.abelianizationIso n).hom (inclusion hkn i)))

theorem model_pair {n k : ℕ} (hkn : k < n) :
    GrayChainExtension.model.map (TripleGlobe.pair n k) ≫ (modelIso hkn).hom =
      (PastingGlobeCylinderBasis.modelIso hkn).hom ≫
        (RightCylinder.map (pairInclusion hkn)).realization := by
  let T := rightCylinderFunctor ⋙ realizationFunctor
  exact (T.map_comp (Abelianization.functor.map (TripleGlobe.pair n k))
    (abelianizationIso hkn).hom).symm.trans
      ((congrArg T.map (abelianization_pair hkn)).trans
        (T.map_comp (PastingGlobeBasis.abelianizationIso hkn).hom (pairInclusion hkn)))

end
end Thomason.Construction.TripleGlobeBasis

end

section

/-! # Split intersections for the pair and final globe of a triple

The retractions are strict maps of the original parameters. Consequently
their identities remain valid after every functor, including the chain
cylinder model.
-/

namespace Thomason.Construction.StrictOmegaCategory.TripleGlobe

open CategoryTheory CategoryTheory.Limits

noncomputable section

def collapsePair (n k : ℕ) (hkn : k ≤ n) :
    PastingGlobe.category n n k ⟶ Globe.category k :=
  PastingGlobe.retractCommon n n k hkn hkn

@[reassoc (attr := simp)] theorem bridge_collapsePair (n k : ℕ) (hkn : k ≤ n) :
    bridge n k ≫ collapsePair n k hkn = 𝟙 _ := by
  change (Globe.faceMap true k n ≫ PastingGlobe.right n n k) ≫
    PastingGlobe.retractCommon n n k hkn hkn = _
  rw [Category.assoc, PastingGlobe.right_retractCommon, PastingGlobe.collapseTo_face]

def retractPair (n k : ℕ) (hkn : k ≤ n) : category n k ⟶ PastingGlobe.category n n k :=
  pushout.desc (𝟙 _) (PastingGlobe.collapseTo n k hkn ≫ bridge n k) (by
    rw [Category.comp_id, ← Category.assoc, PastingGlobe.collapseTo_face, Category.id_comp])

def retractLast (n k : ℕ) (hkn : k ≤ n) : category n k ⟶ Globe.category n :=
  pushout.desc (collapsePair n k hkn ≫ Globe.faceMap false k n) (𝟙 _) (by
    rw [← Category.assoc, bridge_collapsePair, Category.id_comp, Category.comp_id])

@[reassoc (attr := simp)] theorem pair_retractPair (n k : ℕ) (hkn : k ≤ n) :
    pair n k ≫ retractPair n k hkn = 𝟙 _ := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem last_retractPair (n k : ℕ) (hkn : k ≤ n) :
    inclusion n k 2 ≫ retractPair n k hkn =
      PastingGlobe.collapseTo n k hkn ≫ bridge n k := pushout.inr_desc _ _ _

@[reassoc (attr := simp)] theorem pair_retractLast (n k : ℕ) (hkn : k ≤ n) :
    pair n k ≫ retractLast n k hkn = collapsePair n k hkn ≫ Globe.faceMap false k n :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem last_retractLast (n k : ℕ) (hkn : k ≤ n) :
    inclusion n k 2 ≫ retractLast n k hkn = 𝟙 _ := pushout.inr_desc _ _ _

variable (F : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0})

abbrev ImageSource (n k : ℕ) : StrictOmegaCategory.{0} :=
  pushout (F.map (bridge n k)) (F.map (Globe.faceMap false k n))

def imageCell (n k : ℕ) :
    (F.obj (PastingGlobe.category n n k) ⊕ F.obj (Globe.category n)) → ImageSource F n k
  | .inl x => (pushout.inl (F.map (bridge n k)) (F.map (Globe.faceMap false k n))).toFun x
  | .inr x => (pushout.inr (F.map (bridge n k)) (F.map (Globe.faceMap false k n))).toFun x

def targetCell (n k : ℕ) :
    (F.obj (PastingGlobe.category n n k) ⊕ F.obj (Globe.category n)) →
      F.obj (category n k)
  | .inl x => (F.map (pair n k)).toFun x
  | .inr x => (F.map (inclusion n k 2)).toFun x

theorem cross_image_eq (n k : ℕ) (hkn : k ≤ n)
    (x : F.obj (PastingGlobe.category n n k)) (y : F.obj (Globe.category n))
    (he : (F.map (pair n k)).toFun x = (F.map (inclusion n k 2)).toFun y) :
    (pushout.inl (F.map (bridge n k)) (F.map (Globe.faceMap false k n))).toFun x =
      (pushout.inr (F.map (bridge n k)) (F.map (Globe.faceMap false k n))).toFun y := by
  let z := (F.map (PastingGlobe.collapseTo n k hkn)).toFun y
  have hx : x = (F.map (bridge n k)).toFun z := by
    have hh := congrArg (F.map (retractPair n k hkn)).toFun he
    have hl := congrArg (fun u => u.toFun x)
      (show F.map (pair n k) ≫ F.map (retractPair n k hkn) = 𝟙 _ by
        rw [← F.map_comp, pair_retractPair, F.map_id])
    have hr := congrArg (fun u => u.toFun y)
      (show F.map (inclusion n k 2) ≫ F.map (retractPair n k hkn) =
        F.map (PastingGlobe.collapseTo n k hkn) ≫ F.map (bridge n k) by
        rw [← F.map_comp, last_retractPair, F.map_comp])
    exact hl.symm.trans (hh.trans hr)
  have hc : (F.map (collapsePair n k hkn)).toFun x = z := by
    rw [hx]
    exact congrArg (fun u => u.toFun z)
      (show F.map (bridge n k) ≫ F.map (collapsePair n k hkn) = 𝟙 _ by
        rw [← F.map_comp, bridge_collapsePair, F.map_id])
  have hy : (F.map (Globe.faceMap false k n)).toFun z = y := by
    have hh := congrArg (F.map (retractLast n k hkn)).toFun he
    have hl := congrArg (fun u => u.toFun x)
      (show F.map (pair n k) ≫ F.map (retractLast n k hkn) =
        F.map (collapsePair n k hkn) ≫ F.map (Globe.faceMap false k n) by
        rw [← F.map_comp, pair_retractLast, F.map_comp])
    have hr := congrArg (fun u => u.toFun y)
      (show F.map (inclusion n k 2) ≫ F.map (retractLast n k hkn) = 𝟙 _ by
        rw [← F.map_comp, last_retractLast, F.map_id])
    exact (congrArg (F.map (Globe.faceMap false k n)).toFun hc).symm.trans
      (hl.symm.trans (hh.trans hr))
  rw [hx, ← hy]
  exact congrArg (fun u : F.obj (Globe.category k) ⟶ ImageSource F n k => u.toFun z)
    (pushout.condition (f := F.map (bridge n k)) (g := F.map (Globe.faceMap false k n)))

/-- Equal target piece cells are already equal in the source pushout. -/
theorem imageCell_eq (n k : ℕ) (hkn : k ≤ n)
    (x y : F.obj (PastingGlobe.category n n k) ⊕ F.obj (Globe.category n))
    (he : targetCell F n k x = targetCell F n k y) :
    imageCell F n k x = imageCell F n k y := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hh := congrArg (F.map (retractPair n k hkn)).toFun he
      have hl := congrArg (fun u : F.obj (PastingGlobe.category n n k) ⟶
          F.obj (PastingGlobe.category n n k) => u.toFun)
        (show F.map (pair n k) ≫ F.map (retractPair n k hkn) = 𝟙 _ by
          rw [← F.map_comp, pair_retractPair, F.map_id])
      apply congrArg (pushout.inl (F.map (bridge n k)) (F.map (Globe.faceMap false k n))).toFun
      exact (congrFun hl x).symm.trans (hh.trans (congrFun hl y))
    | inr y => exact cross_image_eq F n k hkn x y he
  | inr x =>
    cases y with
    | inl y => exact (cross_image_eq F n k hkn y x he.symm).symm
    | inr y =>
      have hh := congrArg (F.map (retractLast n k hkn)).toFun he
      have hr := congrArg (fun u : F.obj (Globe.category n) ⟶ F.obj (Globe.category n) => u.toFun)
        (show F.map (inclusion n k 2) ≫ F.map (retractLast n k hkn) = 𝟙 _ by
          rw [← F.map_comp, last_retractLast, F.map_id])
      apply congrArg (pushout.inr (F.map (bridge n k)) (F.map (Globe.faceMap false k n))).toFun
      exact (congrFun hr x).symm.trans (hh.trans (congrFun hr y))

end
end Thomason.Construction.StrictOmegaCategory.TripleGlobe

end

end OAI
