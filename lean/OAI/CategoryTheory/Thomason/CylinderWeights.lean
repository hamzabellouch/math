import Mathlib
import OAI.CategoryTheory.Thomason.IntervalCategories

namespace OAI

/-! Cylinder Weights. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {Y Z W : OmegaCategory.{u}}

lemma face_false (n : ℕ) (x : Cell Y) : face n false x = ofMap (eval n x) := by
  unfold face
  rw [eval_eq_restrict (bounded_bound x) n]

lemma bounded_iff_fixed (n : ℕ) (x : Cell Y) : Bounded n x ↔ (omegaCategory Y).source n x = x := by
  change ofMap (eval n x) = x ↔ face n false x = x
  rw [face_false]

lemma restrictCylinder_post {n m : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y)
    (P : OmegaCategory.Functor Y Z) (b : Bool) :
    restrictCylinder m b (OmegaCategory.Functor.comp F P) =
      OmegaCategory.Functor.comp (restrictCylinder m b F) P := rfl

def mapCell (P : OmegaCategory.Functor Y Z) (x : Cell Y) : Cell Z :=
  ⟨fun n => OmegaCategory.Functor.comp (eval n x) P, bound x, fun n => by
    change OmegaCategory.Functor.comp (eval n x) P =
      restrictCylinder n false (OmegaCategory.Functor.comp (eval (bound x) x) P)
    rw [eval_eq_restrict (bounded_bound x) n, restrictCylinder_post]⟩

@[simp] lemma eval_mapCell (P : OmegaCategory.Functor Y Z) (x : Cell Y) (n : ℕ) :
    eval n (mapCell P x) = OmegaCategory.Functor.comp (eval n x) P := rfl

@[simp] lemma mapCell_ofMap (P : OmegaCategory.Functor Y Z) {n : ℕ}
    (F : OmegaCategory.Functor (K.{u} n).nu Y) :
    mapCell P (ofMap F) = ofMap (OmegaCategory.Functor.comp F P) := rfl

lemma mapCell_face (P : OmegaCategory.Functor Y Z) (x : Cell Y) (k : ℕ) (b : Bool) :
    mapCell P (face k b x) = face k b (mapCell P x) := by
  obtain ⟨n,hn⟩ := bounded_exists x
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} n).nu Y, ofMap F = x := ⟨_,hn⟩
  simp only [face_ofMap, mapCell_ofMap, restrictCylinder_post]

lemma mapCell_comp (P : OmegaCategory.Functor Y Z) (x y : Cell Y) (k : ℕ)
    (h : face k true x = face k false y) (h' : face k true (mapCell P x) = face k false (mapCell P y)) :
    mapCell P (comp k x y h) = comp k (mapCell P x) (mapCell P y) h' := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  simp only [mapCell_ofMap, comp_ofMap hk]
  congr 1
  exact pasteCylinder_natural N k hk _ _ _ P

def mapFunctor (P : OmegaCategory.Functor Y Z) : OmegaCategory.Functor (omegaCategory Y) (omegaCategory Z) where
  map := mapCell P
  map_source k x := mapCell_face P x k false
  map_target k x := mapCell_face P x k true
  map_comp k x y h h' := mapCell_comp P x y k h h'

def functor : OmegaCategory.{u} ⥤ OmegaCategory.{u} where
  obj := omegaCategory
  map := mapFunctor
  map_id _ := rfl
  map_comp _ _ := rfl

def cellsEquiv (n : ℕ) (Y : OmegaCategory.{u}) :
    OmegaCategory.Functor (K.{u} n).nu Y ≃ (omegaCategory Y).Cells n where
  toFun F := ⟨ofMap F, (bounded_iff_fixed n _).mp (ofMap_bounded F)⟩
  invFun x := eval n x.val
  left_inv F := eval_ofMap_self F
  right_inv x := Subtype.ext ((bounded_iff_fixed n x.val).mpr x.property)
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

lemma presentation_separates (P : OmegaCategory.Presentation.{u})
    {x y : Cell P.category}
    (h : ∀ (Y : OmegaCategory.{u}) (I : P.Interpretation Y),
      mapCell (P.lift Y I) x = mapCell (P.lift Y I) y) : x = y := by
  let N := max (bound x) (bound y)
  apply cell_ext ((bounded_bound x).mono (le_max_left _ _)) ((bounded_bound y).mono (le_max_right _ _))
  apply OmegaCategory.Functor.ext
  funext z
  apply P.cells_ext
  intro Y I
  exact congrArg (fun c => (eval N c).map z) (h Y I)

def TensorGenerator (X : OmegaCategory.{u}) := Σ n : ℕ, X.Cells n × (K.{u} n).nu.Cell

def tensorPresentation (X : OmegaCategory.{u}) : OmegaCategory.Presentation.{u} where
  Generator := TensorGenerator X
  dimension g := ((K g.1).nu.finite_dimension g.2.2).choose
  relations Y f := ∃ F : OmegaCategory.Functor X (omegaCategory Y),
    ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), f ⟨n,x,z⟩ = (eval n (F.map x.val)).map z

variable {X Y : OmegaCategory.{u}}

lemma functor_cell_bounded (F : OmegaCategory.Functor X (omegaCategory Y)) {n : ℕ} (x : X.Cells n) :
    Bounded n (F.map x.val) := by
  apply (bounded_iff_fixed n _).mpr
  rw [← F.map_source, x.property]

def tensorInterpretation (F : OmegaCategory.Functor X (omegaCategory Y)) :
    (tensorPresentation X).Interpretation Y where
  map g := (eval g.1 (F.map g.2.1.val)).map g.2.2
  bounded g := by
    change TensorGenerator X at g
    change Y.source ((K g.1).nu.finite_dimension g.2.2).choose ((eval g.1 (F.map g.2.1.val)).map g.2.2) = _
    rw [← OmegaCategory.Functor.map_source, ((K g.1).nu.finite_dimension g.2.2).choose_spec]
  satisfies := ⟨F, fun _ _ _ => rfl⟩

def generatorCylinder (n : ℕ) (x : X.Cells n) :
    OmegaCategory.Functor (K.{u} n).nu (tensorPresentation X).category where
  map z := (tensorPresentation X).generator ⟨n,x,z⟩
  map_source k z := by
    apply (tensorPresentation X).cells_ext
    intro Y I
    obtain ⟨F,hF⟩ := I.satisfies
    simp only [Presentation.evaluate_source]
    erw [Presentation.evaluate_generator, Presentation.evaluate_generator, hF, hF]
    exact (eval n (F.map x.val)).map_source k z
  map_target k z := by
    apply (tensorPresentation X).cells_ext
    intro Y I
    obtain ⟨F,hF⟩ := I.satisfies
    simp only [Presentation.evaluate_target]
    erw [Presentation.evaluate_generator, Presentation.evaluate_generator, hF, hF]
    exact (eval n (F.map x.val)).map_target k z
  map_comp k z w h h' := by
    apply (tensorPresentation X).cells_ext
    intro Y I
    obtain ⟨F,hF⟩ := I.satisfies
    simp only [Presentation.evaluate_comp]
    change I.map ⟨n,x,(K n).nu.comp k z w h⟩ =
      Y.comp k (I.map ⟨n,x,z⟩) (I.map ⟨n,x,w⟩) _
    simp only [hF n x]
    apply (eval n (F.map x.val)).map_comp

lemma generatorCylinder_interpretation (I : (tensorPresentation X).Interpretation Y)
    (F : OmegaCategory.Functor X (omegaCategory Y))
    (hF : ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), I.map ⟨n,x,z⟩ = (eval n (F.map x.val)).map z)
    (n : ℕ) (x : X.Cells n) :
    OmegaCategory.Functor.comp (generatorCylinder n x) ((tensorPresentation X).lift Y I) =
      eval n (F.map x.val) := OmegaCategory.Functor.ext (funext (hF n x))

lemma ofMap_generator_image (I : (tensorPresentation X).Interpretation Y)
    (F : OmegaCategory.Functor X (omegaCategory Y))
    (hF : ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), I.map ⟨n,x,z⟩ = (eval n (F.map x.val)).map z)
    (n : ℕ) (x : X.Cells n) :
    mapCell ((tensorPresentation X).lift Y I) (ofMap (generatorCylinder n x)) = F.map x.val := by
  rw [mapCell_ofMap, generatorCylinder_interpretation I F hF n x]
  exact functor_cell_bounded F x

def tensorUnitCell (x : X.Cell) : Cell (tensorPresentation X).category :=
  ofMap (generatorCylinder (X.finite_dimension x).choose ⟨x,(X.finite_dimension x).choose_spec⟩)

lemma tensorUnitCell_image (I : (tensorPresentation X).Interpretation Y)
    (F : OmegaCategory.Functor X (omegaCategory Y))
    (hF : ∀ n (x : X.Cells n) (z : (K.{u} n).nu.Cell), I.map ⟨n,x,z⟩ = (eval n (F.map x.val)).map z)
    (x : X.Cell) :
    mapCell ((tensorPresentation X).lift Y I) (tensorUnitCell x) = F.map x :=
  ofMap_generator_image I F hF _ _

lemma tensorUnitCell_of_bounded (n : ℕ) (x : X.Cells n) :
    tensorUnitCell x.val = ofMap (generatorCylinder n x) := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF, ofMap_generator_image I F hF]

lemma tensorUnitCell_source (k : ℕ) (x : X.Cell) :
    tensorUnitCell (X.source k x) = (omegaCategory (tensorPresentation X).category).source k (tensorUnitCell x) := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF]
  change F.map (X.source k x) = mapCell ((tensorPresentation X).lift Y I) (face k false (tensorUnitCell x))
  rw [mapCell_face, tensorUnitCell_image I F hF]
  exact F.map_source k x

lemma tensorUnitCell_target (k : ℕ) (x : X.Cell) :
    tensorUnitCell (X.target k x) = (omegaCategory (tensorPresentation X).category).target k (tensorUnitCell x) := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF]
  change F.map (X.target k x) = mapCell ((tensorPresentation X).lift Y I) (face k true (tensorUnitCell x))
  rw [mapCell_face, tensorUnitCell_image I F hF]
  exact F.map_target k x

lemma tensorUnitCell_comp (k : ℕ) (x y : X.Cell) (h : X.target k x = X.source k y)
    (h' : (omegaCategory (tensorPresentation X).category).target k (tensorUnitCell x) =
      (omegaCategory (tensorPresentation X).category).source k (tensorUnitCell y)) :
    tensorUnitCell (X.comp k x y h) = (omegaCategory (tensorPresentation X).category).comp k
      (tensorUnitCell x) (tensorUnitCell y) h' := by
  apply presentation_separates
  intro Y I
  obtain ⟨F,hF⟩ := I.satisfies
  rw [tensorUnitCell_image I F hF]
  change F.map (X.comp k x y h) =
    (mapFunctor ((tensorPresentation X).lift Y I)).map
      ((omegaCategory (tensorPresentation X).category).comp k (tensorUnitCell x) (tensorUnitCell y) h')
  rw [(mapFunctor ((tensorPresentation X).lift Y I)).map_comp k _ _ h'
    ((mapFunctor ((tensorPresentation X).lift Y I)).map_composable h')]
  change F.map (X.comp k x y h) = (omegaCategory Y).comp k
    (mapCell ((tensorPresentation X).lift Y I) (tensorUnitCell x))
    (mapCell ((tensorPresentation X).lift Y I) (tensorUnitCell y)) _
  simp only [tensorUnitCell_image I F hF]
  apply F.map_comp

def tensorUnit (X : OmegaCategory.{u}) :
    OmegaCategory.Functor X (omegaCategory (tensorPresentation X).category) where
  map := tensorUnitCell
  map_source := tensorUnitCell_source
  map_target := tensorUnitCell_target
  map_comp := tensorUnitCell_comp
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y Z : OmegaCategory.{u}}

def uncurry (F : OmegaCategory.Functor X (omegaCategory Y)) :
    OmegaCategory.Functor (tensorPresentation X).category Y :=
  (tensorPresentation X).lift Y (tensorInterpretation F)

def curry (F : OmegaCategory.Functor (tensorPresentation X).category Y) :
    OmegaCategory.Functor X (omegaCategory Y) :=
  OmegaCategory.Functor.comp (tensorUnit X) (mapFunctor F)

lemma curry_uncurry (F : OmegaCategory.Functor X (omegaCategory Y)) : curry (uncurry F) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  exact tensorUnitCell_image (tensorInterpretation F) F (fun _ _ _ => rfl) x

lemma curry_eval (F : OmegaCategory.Functor (tensorPresentation X).category Y)
    (n : ℕ) (x : X.Cells n) (z : (K.{u} n).nu.Cell) :
    (eval n ((curry F).map x.val)).map z = F.map ((tensorPresentation X).generator ⟨n,x,z⟩) := by
  change (eval n (mapCell F (tensorUnitCell x.val))).map z = _
  rw [tensorUnitCell_of_bounded n x, mapCell_ofMap, eval_ofMap_self]
  rfl

lemma uncurry_curry (F : OmegaCategory.Functor (tensorPresentation X).category Y) : uncurry (curry F) = F := by
  apply (tensorPresentation X).functor_ext
  intro ⟨n,x,z⟩
  exact curry_eval F n x z

def homEquiv (X Y : OmegaCategory.{u}) :
    ((tensorPresentation X).category ⟶ Y) ≃ (X ⟶ functor.obj Y) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

lemma homEquiv_natural (X Y Z : OmegaCategory.{u}) (P : Y ⟶ Z) (F : (tensorPresentation X).category ⟶ Y) :
    homEquiv X Z (F ≫ P) = homEquiv X Y F ≫ functor.map P := rfl

def tensorFunctor : OmegaCategory.{u} ⥤ OmegaCategory.{u} :=
  Adjunction.leftAdjointOfEquiv homEquiv homEquiv_natural

def tensorAdjunction : tensorFunctor.{u} ⊣ functor :=
  Adjunction.adjunctionOfEquivLeft homEquiv homEquiv_natural

instance tensorFunctor_isLeftAdjoint : tensorFunctor.{u}.IsLeftAdjoint := ⟨functor, ⟨tensorAdjunction⟩⟩
instance tensorFunctor_preservesColimits : Limits.PreservesColimitsOfSize.{u,u} tensorFunctor.{u} :=
  tensorAdjunction.leftAdjoint_preservesColimits

lemma tensorFunctor_obj (X : OmegaCategory.{u}) : tensorFunctor.obj X = (tensorPresentation X).category := rfl

lemma tensorFunctor_map_generator (P : X ⟶ Y) (n : ℕ) (x : X.Cells n) (z : (K.{u} n).nu.Cell) :
    (tensorFunctor.map P).map ((tensorPresentation X).generator ⟨n,x,z⟩) =
      (tensorPresentation Y).generator ⟨n,⟨P.map x.val, by rw [← P.map_source, x.property]⟩,z⟩ := by
  change (eval n (tensorUnitCell (P.map x.val))).map z = _
  rw [tensorUnitCell_of_bounded n ⟨P.map x.val, by rw [← P.map_source, x.property]⟩, eval_ofMap_self]
  rfl
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y Z : OmegaCategory.{u}}

lemma endpointTop_bounded {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) :
    Y.source n (F.map (atEnd a (topTable n))) = F.map (atEnd a (topTable n)) := by
  erw [← F.map_source]
  congr 1
  exact (atEnd_truncate a false (topTable n) n).trans (congrArg (atEnd a) (topTable_bounded n))

def endpointCell (a : Bool) (x : Cell Y) : Y.Cell :=
  (eval (bound x) x).map (atEnd a (topTable (bound x)))

lemma endpointCell_of_bounded {n : ℕ} {x : Cell Y} (hx : Bounded n x) (a : Bool) :
    endpointCell a x = (eval n x).map (atEnd a (topTable n)) := by
  let N := max n (bound x)
  have he (m : ℕ) (hm : Bounded m x) (hmN : m ≤ N) :
      (eval N x).map (atEnd a (topTable N)) = (eval m x).map (atEnd a (topTable m)) := by
    rw [eval_eq_restrict hm N, restrictCylinder_endpoint_top]
    exact Y.source_fixed_upwards hmN (endpointTop_bounded (eval m x) a)
  exact (he (bound x) (bounded_bound x) (le_max_right _ _)).symm.trans (he n hx (le_max_left _ _))

@[simp] lemma endpointCell_ofMap {n : ℕ} (F : OmegaCategory.Functor (K.{u} n).nu Y) (a : Bool) :
    endpointCell a (ofMap F) = F.map (atEnd a (topTable n)) := by
  rw [endpointCell_of_bounded (ofMap_bounded F), eval_ofMap_self]

lemma endpointCell_face (a : Bool) (x : Cell Y) (k : ℕ) (b : Bool) :
    endpointCell a (face k b x) = Y.face k b (endpointCell a x) := by
  obtain ⟨n,hn⟩ := bounded_exists x
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} n).nu Y, ofMap F = x := ⟨_,hn⟩
  rw [face_ofMap, endpointCell_ofMap, endpointCell_ofMap, restrictCylinder_endpoint_top]

lemma endpointCell_comp (a : Bool) (x y : Cell Y) (k : ℕ) (h : face k true x = face k false y)
    (h' : Y.target k (endpointCell a x) = Y.source k (endpointCell a y)) :
    endpointCell a (comp k x y h) = Y.comp k (endpointCell a x) (endpointCell a y) h' := by
  let N := max (k+1) (max (bound x) (bound y))
  have hk : k < N := by omega
  have hx : Bounded N x := (bounded_bound x).mono (by omega)
  have hy : Bounded N y := (bounded_bound y).mono (by omega)
  clear_value N
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} N).nu Y, ofMap F = x := ⟨_,hx⟩
  obtain ⟨G,rfl⟩ : ∃ G : OmegaCategory.Functor (K.{u} N).nu Y, ofMap G = y := ⟨_,hy⟩
  simp only [comp_ofMap hk, endpointCell_ofMap] at h' ⊢
  rw [pasteCylinder_endpoint_top, Y.join_eq k _ _ h']

def endpointFunctor (a : Bool) (Y : OmegaCategory.{u}) : OmegaCategory.Functor (omegaCategory Y) Y where
  map := endpointCell a
  map_source k x := endpointCell_face a x k false
  map_target k x := endpointCell_face a x k true
  map_comp k x y h h' := endpointCell_comp a x y k h h'

lemma endpointCell_map (a : Bool) (P : OmegaCategory.Functor Y Z) (x : Cell Y) :
    endpointCell a (mapCell P x) = P.map (endpointCell a x) := by
  obtain ⟨n,hn⟩ := bounded_exists x
  obtain ⟨F,rfl⟩ : ∃ F : OmegaCategory.Functor (K.{u} n).nu Y, ofMap F = x := ⟨_,hn⟩
  rw [mapCell_ofMap, endpointCell_ofMap, endpointCell_ofMap]
  rfl

def endpointTransformation (a : Bool) : functor.{u} ⟶ 𝟭 OmegaCategory.{u} where
  app Y := endpointFunctor a Y
  naturality _ _ P := OmegaCategory.Functor.ext (funext (endpointCell_map a P))

def tensorEndpoint (a : Bool) : 𝟭 OmegaCategory.{u} ⟶ tensorFunctor.{u} where
  app X := OmegaCategory.Functor.comp (tensorUnit X) (endpointFunctor a (tensorFunctor.obj X))
  naturality X Y P := by
    apply OmegaCategory.Functor.ext
    funext x
    obtain ⟨n,hn⟩ := X.finite_dimension x
    change endpointCell a (tensorUnitCell (P.map x)) = (tensorFunctor.map P).map (endpointCell a (tensorUnitCell x))
    erw [tensorUnitCell_of_bounded n ⟨x,hn⟩, tensorUnitCell_of_bounded n ⟨P.map x, by rw [← P.map_source,hn]⟩,
      endpointCell_ofMap, endpointCell_ofMap]
    exact (tensorFunctor_map_generator P n ⟨x,hn⟩ (atEnd a (topTable n))).symm

lemma tensorEndpoint_bounded (a : Bool) (X : OmegaCategory.{u}) (n : ℕ) (x : X.Cells n) :
    ((tensorEndpoint a).app X).map x.val = (tensorPresentation X).generator ⟨n,x,atEnd a (topTable n)⟩ := by
  change endpointCell a (tensorUnitCell x.val) = _
  rw [tensorUnitCell_of_bounded n x, endpointCell_ofMap]
  rfl
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory
variable {X Y Z : OmegaCategory.{u}}

lemma constantInterval_restrict {n k : ℕ} (F : OmegaCategory.Functor (complex.{u} n).nu Y) (b : Bool) :
    restrictCylinder k b (constantInterval F) =
      constantInterval (OmegaCategory.Functor.comp (faceMap n k b).nu F) := by
  apply OmegaCategory.Functor.ext
  funext z
  exact congrArg F.map (congrArg (fun P => P.nu.map z) (faceMap.{u} n k b).cylinder_projection)

lemma lift_face (x : Y.Cell) {n : ℕ} (hx : Y.source n x = x) (k : ℕ) (b : Bool) :
    OmegaCategory.Functor.comp (faceMap.{u} n k b).nu (lift x hx) =
      lift (Y.face k b x) (by cases b <;> simp [OmegaCategory.face]) := by
  apply GlobeComplex.functor_ext
  change (lift x hx).map ((faceMap n k b).nu.map (topTable k)) = _
  rw [faceMap_top, lift_top]
  exact evaluate_face x hx k b

lemma constant_bound_mono (x : Y.Cell) {n m : ℕ} (hn : Y.source n x = x) (hm : Y.source m x = x)
    (hnm : n ≤ m) :
    ofMap (constantInterval (lift.{u,u} x hn)) = ofMap (constantInterval (lift x hm)) := by
  rw [← ofMap_raise hnm (constantInterval (lift x hn)), constantInterval_restrict]
  apply congrArg (fun F : OmegaCategory.Functor (complex.{u} m).nu Y => ofMap (constantInterval F))
  apply GlobeComplex.functor_ext
  change (lift x hn).map ((faceMap n m false).nu.map (topTable m)) = _
  rw [faceMap_top, lift_top]
  exact (evaluate_face x hn m false).trans hm

lemma constant_bound_independent (x : Y.Cell) {n m : ℕ} (hn : Y.source n x = x) (hm : Y.source m x = x) :
    ofMap (constantInterval (lift.{u,u} x hn)) = ofMap (constantInterval (lift x hm)) := by
  have hnm := Y.source_fixed_upwards (le_max_left n m) hn
  rw [constant_bound_mono x hn hnm (le_max_left n m), constant_bound_mono x hm hnm (le_max_right n m)]

def constantCell (x : Y.Cell) : Cell Y :=
  ofMap (constantInterval (lift x (Y.finite_dimension x).choose_spec))

lemma constantCell_of_bounded (n : ℕ) (x : Y.Cell) (hx : Y.source n x = x) :
    constantCell x = ofMap (constantInterval (lift.{u,u} x hx)) :=
  constant_bound_independent x _ hx

lemma constantCell_face (x : Y.Cell) (k : ℕ) (b : Bool) :
    constantCell (Y.face k b x) = face k b (constantCell x) := by
  obtain ⟨n,hn⟩ := Y.finite_dimension x
  have hface : Y.source k (Y.face k b x) = Y.face k b x := by cases b <;> simp [OmegaCategory.face]
  rw [constantCell_of_bounded n x hn, face_ofMap, constantInterval_restrict, lift_face,
    constantCell_of_bounded k (Y.face k b x) hface]

lemma constantCell_comp (x y : Y.Cell) (k : ℕ) (h : Y.target k x = Y.source k y)
    (h' : face k true (constantCell x) = face k false (constantCell y)) :
    constantCell (Y.comp k x y h) = comp k (constantCell x) (constantCell y) h' := by
  obtain ⟨m,hm⟩ := Y.finite_dimension x
  obtain ⟨l,hl⟩ := Y.finite_dimension y
  let N := max (k+1) (max m l)
  have hk : k < N := by omega
  have hx : Y.source N x = x := Y.source_fixed_upwards (by omega : m ≤ N) hm
  have hy : Y.source N y = y := Y.source_fixed_upwards (by omega : l ≤ N) hl
  have hxy : Y.source N (Y.comp k x y h) = Y.comp k x y h := by
    rw [Y.source_comp_gt N k hk x y h (Y.source_composable hk h)]
    simp only [hx,hy]
  simp only [constantCell_of_bounded N x hx, constantCell_of_bounded N y hy] at h' ⊢
  rw [constantCell_of_bounded N (Y.comp k x y h) hxy, comp_ofMap hk]
  have hw : Y.target k ((lift.{u,u} x hx).map (topTable N)) =
      Y.source k ((lift.{u,u} y hy).map (topTable N)) := by simpa only [lift_top] using h
  rw [pasteCylinder_constant N k hk _ _ hw]
  congr 2
  apply GlobeComplex.functor_ext
  rw [lift_top, globeComposite_top, lift_top, lift_top, Y.join_eq k x y h]

def constantFunctor (Y : OmegaCategory.{u}) : OmegaCategory.Functor Y (omegaCategory Y) where
  map := constantCell
  map_source k x := constantCell_face x k false
  map_target k x := constantCell_face x k true
  map_comp k x y h h' := constantCell_comp x y k h h'

lemma constantCell_map (P : OmegaCategory.Functor Y Z) (x : Y.Cell) :
    constantCell (P.map x) = mapCell P (constantCell x) := by
  obtain ⟨n,hn⟩ := Y.finite_dimension x
  have hp : Z.source n (P.map x) = P.map x := by rw [← P.map_source,hn]
  rw [constantCell_of_bounded n x hn, constantCell_of_bounded n (P.map x) hp, mapCell_ofMap]
  apply congrArg ofMap
  have he : lift.{u,u} (P.map x) hp = OmegaCategory.Functor.comp (lift x hn) P := by
    apply GlobeComplex.functor_ext
    change _ = P.map ((lift x hn).map (topTable n))
    rw [lift_top,lift_top]
  rw [he]
  rfl

def constantTransformation : 𝟭 OmegaCategory.{u} ⟶ functor.{u} where
  app Y := constantFunctor Y
  naturality _ _ P := OmegaCategory.Functor.ext (funext (constantCell_map P))

lemma endpointCell_constant (a : Bool) (x : Y.Cell) : endpointCell a (constantCell x) = x := by
  obtain ⟨n,hn⟩ := Y.finite_dimension x
  rw [constantCell_of_bounded n x hn, endpointCell_ofMap, constantInterval_endpoint, lift_top]

def tensorProjection : tensorFunctor.{u} ⟶ 𝟭 OmegaCategory.{u} where
  app X := uncurry (constantFunctor X)
  naturality X Y P := by
    apply (tensorPresentation X).functor_ext
    intro ⟨n,x,z⟩
    change ((uncurry (constantFunctor Y)).map ((tensorFunctor.map P).map
      ((tensorPresentation X).generator ⟨n,x,z⟩))) =
      P.map ((uncurry (constantFunctor X)).map ((tensorPresentation X).generator ⟨n,x,z⟩))
    rw [tensorFunctor_map_generator]
    change (eval n (constantCell (P.map x.val))).map z = P.map ((eval n (constantCell x.val)).map z)
    rw [constantCell_map,eval_mapCell]
    rfl

lemma tensorProjection_generator (X : OmegaCategory.{u}) (n : ℕ) (x : X.Cells n) (z : (K.{u} n).nu.Cell) :
    (tensorProjection.app X).map ((tensorPresentation X).generator ⟨n,x,z⟩) =
      (lift.{u,u} x.val x.property).map (project z) := by
  change (eval n (constantCell x.val)).map z = _
  rw [constantCell_of_bounded n x.val x.property, eval_ofMap_self]
  rfl

lemma tensorEndpoint_projection (a : Bool) : tensorEndpoint.{u} a ≫ tensorProjection = 𝟙 (𝟭 OmegaCategory.{u}) := by
  ext X
  apply OmegaCategory.Functor.ext
  funext x
  obtain ⟨n,hn⟩ := X.finite_dimension x
  change (tensorProjection.app X).map (((tensorEndpoint a).app X).map x) = x
  erw [tensorEndpoint_bounded a X n ⟨x,hn⟩,tensorProjection_generator, project_end, lift_top]
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

def globeDiagram (n : ℕ) : OmegaCategory.Functor (complex.{u} n).nu (omegaCategory (K.{u} n).nu) :=
  lift (ofMap (OmegaCategory.Functor.id (K.{u} n).nu))
    ((bounded_iff_fixed n _).mp (ofMap_bounded _))

lemma globeDiagram_top (n : ℕ) :
    (globeDiagram.{u} n).map (topTable n) = ofMap (OmegaCategory.Functor.id (K.{u} n).nu) :=
  lift_top _ _

lemma globeDiagram_face (m p : ℕ) (b : Bool) :
    (globeDiagram.{u} m).map (truncate p b (topTable m)) = ofMap (faceMap m p b).cylinder.nu := by
  erw [← face_nu, (globeDiagram m).map_face, globeDiagram_top]
  cases b <;> exact face_ofMap _ _ _

lemma globeDiagram_map (n m : ℕ) (a : Hom (complex.{u} n) (complex.{u} m)) :
    (globeDiagram m).map (a.nu.map (topTable n)) = ofMap a.cylinder.nu := by
  let t := a.nu.map (topTable n)
  have ht : truncate n false t = t := by
    exact (a.nu.map_source n (topTable n)).symm.trans (congrArg a.nu.map (topTable_bounded n))
  have hb : Bounded n ((globeDiagram m).map t) := by
    apply (bounded_iff_fixed n _).mpr
    exact ((globeDiagram m).map_source n t).symm.trans (congrArg (globeDiagram m).map ht)
  rw [← hb]
  apply congrArg ofMap
  obtain ⟨p,b,_,he⟩ := table_classification t
  have ha : a = Hom.comp (faceMap.{u} p n false) (faceMap m p b) := by
    apply GlobeComplex.hom_ext
    change t = (faceMap m p b).nu.map ((faceMap p n false).nu.map (topTable n))
    rw [faceMap_top]
    change t = (faceMap m p b).table (truncate n false (topTable p))
    rw [Hom.table_truncate]
    change t = truncate n false ((faceMap m p b).nu.map (topTable p))
    rw [faceMap_top,← he,ht]
  rw [he,globeDiagram_face,eval_ofMap,ha,Hom.cylinder_comp]
  rfl

def globeTensorHom (n : ℕ) : tensorFunctor.obj (complex.{u} n).nu ⟶ (K.{u} n).nu :=
  uncurry (globeDiagram n)

def globeTensorInv (n : ℕ) : (K.{u} n).nu ⟶ tensorFunctor.obj (complex.{u} n).nu :=
  generatorCylinder n ⟨topTable n,topTable_bounded n⟩

lemma globeTensorHom_generator (n k : ℕ) (x : (complex.{u} n).nu.Cells k) (z : (K.{u} k).nu.Cell) :
    (globeTensorHom n).map ((tensorPresentation (complex.{u} n).nu).generator ⟨k,x,z⟩) =
      (eval k ((globeDiagram n).map x.val)).map z := rfl

lemma globeTensorHom_inv (n : ℕ) : globeTensorHom.{u} n ≫ globeTensorInv n = 𝟙 _ := by
  apply (homEquiv (complex.{u} n).nu (tensorFunctor.obj (complex n).nu)).injective
  erw [homEquiv_natural]
  change OmegaCategory.Functor.comp (curry (uncurry (globeDiagram n))) (mapFunctor (globeTensorInv n)) =
    curry (𝟙 (tensorFunctor.obj (complex n).nu))
  rw [curry_uncurry]
  apply GlobeComplex.functor_ext
  change mapCell (globeTensorInv n) ((globeDiagram n).map (topTable n)) = tensorUnitCell (topTable n)
  rw [globeDiagram_top,mapCell_ofMap]
  rw [tensorUnitCell_of_bounded (X := (complex n).nu) n ⟨topTable.{u} n,topTable_bounded n⟩]
  rfl

lemma globeTensorInv_hom (n : ℕ) : globeTensorInv.{u} n ≫ globeTensorHom n = 𝟙 _ := by
  apply OmegaCategory.Functor.ext
  funext z
  change (eval n ((globeDiagram n).map (topTable n))).map z = z
  rw [globeDiagram_top,eval_ofMap_self]
  rfl

def globeTensorIso (n : ℕ) : tensorFunctor.obj (complex.{u} n).nu ≅ (complex.{u} n).cylinder.nu where
  hom := globeTensorHom n
  inv := globeTensorInv n
  hom_inv_id := globeTensorHom_inv n
  inv_hom_id := globeTensorInv_hom n

lemma globeTensorIso_natural (n m : ℕ) (a : Hom (complex.{u} n) (complex.{u} m)) :
    tensorFunctor.map a.nu ≫ (globeTensorIso m).hom = (globeTensorIso n).hom ≫ a.cylinder.nu := by
  apply (homEquiv (complex.{u} n).nu (K.{u} m).nu).injective
  have hl : homEquiv (complex.{u} n).nu (K.{u} m).nu (tensorFunctor.map a.nu ≫ (globeTensorIso m).hom) =
      a.nu ≫ globeDiagram m := by
    change tensorAdjunction.homEquiv _ _ (tensorFunctor.map a.nu ≫ (globeTensorIso m).hom) = _
    rw [tensorAdjunction.homEquiv_naturality_left]
    change OmegaCategory.Functor.comp a.nu (curry (uncurry (globeDiagram m))) = _
    rw [curry_uncurry]
    rfl
  erw [hl,homEquiv_natural]
  change OmegaCategory.Functor.comp a.nu (globeDiagram m) =
    OmegaCategory.Functor.comp (curry (uncurry (globeDiagram n))) (mapFunctor a.cylinder.nu)
  rw [curry_uncurry]
  apply GlobeComplex.functor_ext
  change (globeDiagram m).map (a.nu.map (topTable n)) = mapCell a.cylinder.nu ((globeDiagram n).map (topTable n))
  rw [globeDiagram_map,globeDiagram_top,mapCell_ofMap]
  rfl

lemma globeTensorIso_endpoint (n : ℕ) (b : Bool) :
    (tensorEndpoint b).app (complex.{u} n).nu ≫ (globeTensorIso n).hom =
      ((complex n).cylinderEndpoint b).nu := by
  apply GlobeComplex.functor_ext
  change (globeTensorHom n).map (((tensorEndpoint b).app (complex n).nu).map (topTable n)) = _
  erw [tensorEndpoint_bounded b (complex n).nu n ⟨topTable n,topTable_bounded n⟩,
    globeTensorHom_generator,globeDiagram_top,eval_ofMap_self]
  rfl

lemma globeTensorIso_projection (n : ℕ) :
    (globeTensorIso.{u} n).hom ≫ (complex n).cylinderProjection.nu = tensorProjection.app (complex n).nu := by
  apply (homEquiv (complex.{u} n).nu (complex n).nu).injective
  erw [homEquiv_natural]
  change OmegaCategory.Functor.comp (curry (uncurry (globeDiagram n))) (mapFunctor (complex n).cylinderProjection.nu) =
    curry (uncurry (constantFunctor (complex n).nu))
  rw [curry_uncurry,curry_uncurry]
  apply GlobeComplex.functor_ext
  change mapCell (complex n).cylinderProjection.nu ((globeDiagram n).map (topTable n)) = constantCell (topTable n)
  rw [globeDiagram_top,mapCell_ofMap]
  rw [constantCell_of_bounded (Y := (complex n).nu) n (topTable.{u} n) (topTable_bounded n)]
  apply congrArg ofMap
  have he : lift.{u,u} (topTable n) (topTable_bounded n) = OmegaCategory.Functor.id (complex n).nu := by
    apply GlobeComplex.functor_ext
    exact lift_top _ _
  rw [he]
  rfl
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open CategoryTheory DirectedComplex DirectedComplex.Table GlobeComplex OmegaCategory

structure CellWeight (Y : OmegaCategory.{v}) (d : ℕ) (A : Type w) [AddCommMonoid A] where
  apply : Y.Cell → A
  add : ∀ k, k < d → ∀ x y, Y.target k x = Y.source k y →
    apply (Y.join k x y) = apply x + apply y
  vanish : ∀ k, k < d → ∀ x, Y.source k x = x → apply x = 0

namespace CellWeight
variable {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
instance {d : ℕ} : CoeFun (CellWeight Y d A) (fun _ => Y.Cell → A) := ⟨apply⟩

def hom {d : ℕ} (q : CellWeight Y (d+1) A) (a b : Y.Cell) :
    CellWeight (Y.homCategory a b) d A where
  apply x := q x.val
  add k hk x y h := by
    rw [hom_join_val k x y h]
    exact q.add (k+1) (by omega) x.val y.val (congrArg Subtype.val h)
  vanish k hk x h := q.vanish (k+1) (by omega) x.val (congrArg Subtype.val h)

def row (M : DirectedComplex.{v}) (d : ℕ) (b : Bool) : CellWeight M.nu d (M.Chain d) where
  apply x := x.row d b
  add k hk x y h := by
    rw [M.nu.join_eq k x y h]
    change (DirectedComplex.Table.comp k x y h).row d b = _
    erw [comp_row]
    simp only [show ¬d < k by omega, show d ≠ k by omega, ite_false]
  vanish k hk x h := row_above_fixed x h hk b
end CellWeight

lemma concatInterval_weight (n : ℕ) {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
    (q : CellWeight Y (n+1) A)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : IntervalMatching F G) :
    q ((concatInterval F G h).map (verticalTable (topTable n))) =
      q (F.map (verticalTable (topTable n))) + q (G.map (verticalTable (topTable n))) := by
  induction n generalizing Y with
  | zero =>
    rw [concatInterval_zero_vertical]
    exact q.add 0 (by omega) _ _ (zero_interval_seam F G h)
  | succ n ih =>
    rw [← suspendTable_top n, ← up_vertical, concatInterval_succ_up]
    let D := rectangleDiagramOfFunctor F
    let E := rectangleDiagramOfFunctor G
    let x := verticalTable (topTable.{u} n)
    have hw := ih (q.hom ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
      (D.concatDiagonalOne E h) (D.concatDiagonalTwo E h) (D.concatDiagonal_matching E h)
    change q _ = q _ + q _ at hw
    rw [hw]
    change q (Y.join 0 (D.edge false) (E.diagonal.map x).val) +
        q (Y.join 0 (D.diagonal.map x).val (E.edge true)) = _
    rw [q.add 0 (by omega) _ _ ((D.edge_target false).trans ((h _).trans (E.diagonal.map x).property.1.symm)),
      q.add 0 (by omega) _ _ ((D.diagonal.map x).property.2.trans ((h _).trans (E.edge_source true).symm)),
      q.vanish 1 (by omega) _ (D.edge_fixed false), q.vanish 1 (by omega) _ (E.edge_fixed true),
      zero_add, add_zero]
    exact add_comm _ _

lemma horizontalCylinder_weight {n : ℕ} {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
    (q : CellWeight Y (n+1+1) A)
    (F G : OmegaCategory.Functor (K.{u} (n+1)).nu Y)
    (h : F.map (verticalTable (vertex n true)) = G.map (verticalTable (vertex n false))) :
    q ((horizontalCylinder F G h).map (verticalTable (topTable (n+1)))) =
      q (F.map (verticalTable (topTable (n+1)))) + q (G.map (verticalTable (topTable (n+1)))) := by
  rw [← suspendTable_top n, ← up_vertical]
  change q (((rectangleDiagramOfFunctor F).horizontal (rectangleDiagramOfFunctor G) h).lift.map _) = _
  rw [RectangleDiagram.lift_up]
  let D := rectangleDiagramOfFunctor F
  let E := rectangleDiagramOfFunctor G
  let x := verticalTable (topTable.{u} n)
  have hw := concatInterval_weight n
    (q.hom ((D.ends false).map (vertex n false)) ((E.ends true).map (vertex n true)))
    (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h) (D.horizontalDiagonal_matching E h)
  change q _ = q _ + q _ at hw
  change q ((concatInterval (D.horizontalDiagonalOne E h) (D.horizontalDiagonalTwo E h)
    (D.horizontalDiagonal_matching E h)).map x).val = _
  rw [hw]
  change q (Y.join 0 (D.diagonal.map x).val ((E.ends true).map (suspendTable (project x)))) +
    q (Y.join 0 ((D.ends false).map (suspendTable (project x))) (E.diagonal.map x).val) = _
  have hb (a : Bool) (R : RectangleDiagram.{u,v} n Y) :
      Y.source (n+1) ((R.ends a).map (suspendTable (project x))) =
        (R.ends a).map (suspendTable (project x)) := by
    erw [← (R.ends a).map_source]
    exact congrArg (R.ends a).map (dimension_of_rows_above_zero _
      (fun p hp b => chain_zero hp _))
  rw [q.add 0 (by omega) _ _ ((D.diagonal.map x).property.2.trans (by
      erw [← (E.ends true).map_source]
      change _ = (E.ends true).map (truncate 0 false (suspendTable (project x)))
      rw [suspend_truncate_zero]
      exact D.horizontal_seam E h true)),
    q.add 0 (by omega) _ _ ((by
      erw [← (D.ends false).map_target]
      change (D.ends false).map (truncate 0 true (suspendTable (project x))) = _
      rw [suspend_truncate_zero]
      exact (D.horizontal_seam E h false).trans (E.diagonal.map x).property.1.symm)),
    q.vanish (n+1) (by omega) _ (hb true E), q.vanish (n+1) (by omega) _ (hb false D),
    add_zero, zero_add]
  rfl

lemma pasteCylinder_weight (n k : ℕ) (hk : k < n)
    {Y : OmegaCategory.{v}} {A : Type w} [AddCommMonoid A]
    (q : CellWeight Y (n+1) A)
    (F G : OmegaCategory.Functor (K.{u} n).nu Y) (h : FaceMatching k F G) :
    q ((pasteCylinder hk F G h).map (verticalTable (topTable n))) =
      q (F.map (verticalTable (topTable n))) + q (G.map (verticalTable (topTable n))) := by
  induction k generalizing n Y with
  | zero =>
    cases n with
    | zero => omega
    | succ n =>
      rw [pasteCylinder_zero]
      exact horizontalCylinder_weight q F G _
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hk' : k < n := by omega
      rw [← suspendTable_top n, ← up_vertical, pasteCylinder_succ_up hk']
      exact ih n hk' (q.hom _ _) (rectangleDiagramOfFunctor F).diagonal
        (CylinderComposition.secondDiagonal F G h) (CylinderComposition.diagonal_matching F G h)
end Thomason.GrayRecursive

end

end OAI
