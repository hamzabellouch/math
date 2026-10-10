import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.GrayMappingEndpointEvaluation
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeChains
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderRetractions

namespace OAI

section

/-! # Higher-face compatibility of the actual mapping composition -/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

private theorem face_matching (a : Bool) (r n k : ℕ) (hkr : k < r) :
    (PastingGlobe.category n n k).target k
        ((PastingGlobe.category n n k).face a r (PastingGlobe.leftCell n n k)) =
      (PastingGlobe.category n n k).source k
        ((PastingGlobe.category n n k).face a r (PastingGlobe.rightCell n n k)) := by
  simpa only [source, target, (PastingGlobe.category n n k).globular, hkr, ite_true] using
    PastingGlobe.matching n n k

def pastingFace (a : Bool) (r n k : ℕ) (hkr : k < r) :
    PastingGlobe.category r r k ⟶ PastingGlobe.category n n k :=
  PastingGlobe.desc _
    ((PastingGlobe.category n n k).face a r (PastingGlobe.leftCell n n k))
    ((PastingGlobe.category n n k).face a r (PastingGlobe.rightCell n n k))
    ((PastingGlobe.category n n k).face_dimensionLE a r _)
    ((PastingGlobe.category n n k).face_dimensionLE a r _)
    (face_matching a r n k hkr)

theorem pastingFace_left (a : Bool) (r n k : ℕ) (hkr : k < r) :
    PastingGlobe.left r r k ≫ pastingFace a r n k hkr =
      Globe.faceMap a r n ≫ PastingGlobe.left n n k := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_left _ _ _ _ _ _).trans
    ((PastingGlobe.left n n k).map_face a r Globe.Cell.top).symm

theorem pastingFace_right (a : Bool) (r n k : ℕ) (hkr : k < r) :
    PastingGlobe.right r r k ≫ pastingFace a r n k hkr =
      Globe.faceMap a r n ≫ PastingGlobe.right n n k := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_right _ _ _ _ _ _).trans
    ((PastingGlobe.right n n k).map_face a r Globe.Cell.top).symm

theorem compositionGlobe_face (a : Bool) (r n k : ℕ) (hkr : k < r) (hkn : k < n) :
    compositionGlobe r k hkr ≫ pastingFace a r n k hkr =
      Globe.faceMap a r n ≫ compositionGlobe n k hkn := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_composite _ _ _ _ _ _).trans
    (((PastingGlobe.category n n k).face_comp a r k hkr
      (PastingGlobe.leftCell n n k) (PastingGlobe.rightCell n n k)
      (PastingGlobe.matching n n k) (face_matching a r n k hkr)).symm.trans
        ((compositionGlobe n k hkn).map_face a r Globe.Cell.top).symm)

variable {D : StrictOmegaCategory.{0}} {n k : ℕ}

theorem glue_face (a : Bool) (r : ℕ) (hkr : k < r) (hkn : k < n)
    (f g : model.obj (Globe.category n) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ f =
      model.map (Globe.faceMap false k n) ≫ g)
    (hr : model.map (Globe.faceMap true k r) ≫ (model.map (Globe.faceMap a r n) ≫ f) =
      model.map (Globe.faceMap false k r) ≫ (model.map (Globe.faceMap a r n) ≫ g)) :
    glue hkr (model.map (Globe.faceMap a r n) ≫ f)
      (model.map (Globe.faceMap a r n) ≫ g) hr =
      model.map (pastingFace a r n k hkr) ≫ glue hkn f g h := by
  apply (PastingGlobe.CylinderSource.isPushout hkr).hom_ext
  · rw [glue_left, ← Category.assoc, ← model.map_comp, pastingFace_left,
      model.map_comp, Category.assoc, glue_left]
  · rw [glue_right, ← Category.assoc, ← model.map_comp, pastingFace_right,
      model.map_comp, Category.assoc, glue_right]

theorem composite_face (a : Bool) (r : ℕ) (hkr : k < r) (hkn : k < n)
    (f g : model.obj (Globe.category n) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ f =
      model.map (Globe.faceMap false k n) ≫ g)
    (hr : model.map (Globe.faceMap true k r) ≫ (model.map (Globe.faceMap a r n) ≫ f) =
      model.map (Globe.faceMap false k r) ≫ (model.map (Globe.faceMap a r n) ≫ g)) :
    composite hkr (model.map (Globe.faceMap a r n) ≫ f)
      (model.map (Globe.faceMap a r n) ≫ g) hr =
      model.map (Globe.faceMap a r n) ≫ composite hkn f g h := by
  change model.map (compositionGlobe r k hkr) ≫ glue _ _ _ hr = _
  rw [glue_face a r hkr hkn f g h hr, ← Category.assoc, ← model.map_comp,
    compositionGlobe_face, model.map_comp, Category.assoc]
  rfl

/-- The actual mapping-cell composition preserves every higher face. -/
theorem face_comp (a : Bool) (r k : ℕ) (hkr : k < r) (x y : Cell D)
    (h : GlobeMappingCells.face model D true k x = GlobeMappingCells.face model D false k y)
    (h' : GlobeMappingCells.face model D true k (GlobeMappingCells.face model D a r x) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.face model D a r y)) :
    GlobeMappingCells.face model D a r (comp k x y h) =
      comp k (GlobeMappingCells.face model D a r x) (GlobeMappingCells.face model D a r y) h' := by
  let R := Classical.choice (representative_exists k x y h)
  let f : model.obj (Globe.category r) ⟶ D := model.map (Globe.faceMap a r R.bound) ≫ R.first
  let g : model.obj (Globe.category r) ⟶ D := model.map (Globe.faceMap a r R.bound) ≫ R.last
  have hf : GlobeMappingCells.ι model D r f = GlobeMappingCells.face model D a r x :=
    (GlobeMappingCells.face_ι model D a r R.bound R.first).symm.trans
      (congrArg (GlobeMappingCells.face model D a r) R.first_eq)
  have hg : GlobeMappingCells.ι model D r g = GlobeMappingCells.face model D a r y :=
    (GlobeMappingCells.face_ι model D a r R.bound R.last).symm.trans
      (congrArg (GlobeMappingCells.face model D a r) R.last_eq)
  have hr : model.map (Globe.faceMap true k r) ≫ f =
      model.map (Globe.faceMap false k r) ≫ g :=
    GlobeMappingCells.matching_representatives model D _ _ h' f g hf hg
  have hm := (GlobeMappingCells.faces_eq_iff model D true false k r r f g).mpr hr
  calc
    _ = GlobeMappingCells.face model D a r R.value :=
      congrArg (GlobeMappingCells.face model D a r) (comp_eq k x y h R)
    _ = GlobeMappingCells.ι model D r
        (model.map (Globe.faceMap a r R.bound) ≫ composite R.lt_bound R.first R.last R.matching) :=
      GlobeMappingCells.face_ι model D a r R.bound _
    _ = GlobeMappingCells.ι model D r (composite hkr f g hr) :=
      congrArg (GlobeMappingCells.ι model D r)
        (composite_face a r hkr R.lt_bound R.first R.last R.matching hr).symm
    _ = comp k (GlobeMappingCells.ι model D r f) (GlobeMappingCells.ι model D r g) hm :=
      (comp_ι hkr f g hr hm).symm
    _ = _ := comp_congr hf hg hm h'

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # Unit laws for actual bounded mapping composition

The retractions of the two pasted globes implement composition with the
source or target identity. Functoriality of the concrete chain model and
the proved pushout universal property give the mapping-level unit laws.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

theorem compositionGlobe_retractRight (n k : ℕ) (hk : k < n) :
    compositionGlobe n k hk ≫ PastingGlobe.retractRight n n k hk.le = 𝟙 _ := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_composite _ _ _ _ _ _).trans
    ((Globe.category n).left_unit k Globe.Cell.top _)

theorem compositionGlobe_retractLeft (n k : ℕ) (hk : k < n) :
    compositionGlobe n k hk ≫ PastingGlobe.retractLeft n n k hk.le = 𝟙 _ := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_composite _ _ _ _ _ _).trans
    ((Globe.category n).right_unit k Globe.Cell.top _)

variable {D : StrictOmegaCategory.{0}} {n k : ℕ}

def paddedFace (a : Bool) (hk : k < n) (f : model.obj (Globe.category n) ⟶ D) :
    model.obj (Globe.category n) ⟶ D :=
  model.map (PastingGlobe.collapseTo n k hk.le ≫ Globe.faceMap a k n) ≫ f

theorem paddedFace_cell (a : Bool) (hk : k < n) (f : model.obj (Globe.category n) ⟶ D) :
    GlobeMappingCells.ι model D n (paddedFace a hk f) =
      GlobeMappingCells.face model D a k (GlobeMappingCells.ι model D n f) := by
  have he : PastingGlobe.collapseTo n k hk.le = Globe.lower n k hk.le := rfl
  change GlobeMappingCells.ι model D n
    (model.map (PastingGlobe.collapseTo n k hk.le ≫ Globe.faceMap a k n) ≫ f) = _
  rw [he, model.map_comp, Category.assoc, GlobeMappingCells.ι_lower,
    GlobeMappingCells.face_ι]

theorem glue_source_identity (hk : k < n) (f : model.obj (Globe.category n) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ paddedFace false hk f =
      model.map (Globe.faceMap false k n) ≫ f) :
    glue hk (paddedFace false hk f) f h =
      model.map (PastingGlobe.retractRight n n k hk.le) ≫ f := by
  apply (PastingGlobe.CylinderSource.isPushout hk).hom_ext
  · rw [glue_left, ← Category.assoc, ← model.map_comp, PastingGlobe.left_retractRight]
    rfl
  · rw [glue_right, ← Category.assoc, ← model.map_comp,
      PastingGlobe.right_retractRight, model.map_id, Category.id_comp]

theorem glue_target_identity (hk : k < n) (f : model.obj (Globe.category n) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ f =
      model.map (Globe.faceMap false k n) ≫ paddedFace true hk f) :
    glue hk f (paddedFace true hk f) h =
      model.map (PastingGlobe.retractLeft n n k hk.le) ≫ f := by
  apply (PastingGlobe.CylinderSource.isPushout hk).hom_ext
  · rw [glue_left, ← Category.assoc, ← model.map_comp,
      PastingGlobe.left_retractLeft, model.map_id, Category.id_comp]
  · rw [glue_right, ← Category.assoc, ← model.map_comp, PastingGlobe.right_retractLeft]
    rfl

theorem composite_source_identity (hk : k < n) (f : model.obj (Globe.category n) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ paddedFace false hk f =
      model.map (Globe.faceMap false k n) ≫ f) :
    composite hk (paddedFace false hk f) f h = f := by
  change model.map (compositionGlobe n k hk) ≫ glue hk (paddedFace false hk f) f h = f
  rw [glue_source_identity, ← Category.assoc, ← model.map_comp,
    compositionGlobe_retractRight, model.map_id, Category.id_comp]

theorem composite_target_identity (hk : k < n) (f : model.obj (Globe.category n) ⟶ D)
    (h : model.map (Globe.faceMap true k n) ≫ f =
      model.map (Globe.faceMap false k n) ≫ paddedFace true hk f) :
    composite hk f (paddedFace true hk f) h = f := by
  change model.map (compositionGlobe n k hk) ≫ glue hk f (paddedFace true hk f) h = f
  rw [glue_target_identity, ← Category.assoc, ← model.map_comp,
    compositionGlobe_retractLeft, model.map_id, Category.id_comp]

theorem left_unit (k : ℕ) (x : Cell D)
    (h : GlobeMappingCells.face model D true k (GlobeMappingCells.face model D false k x) =
      GlobeMappingCells.face model D false k x) :
    comp k (GlobeMappingCells.face model D false k x) x h = x := by
  obtain ⟨n, hn, f, hf⟩ := GlobeMappingCells.exists_representative_above model D x (k+1)
  have hk : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
  let sf := paddedFace false hk f
  have hs : GlobeMappingCells.ι model D n sf = GlobeMappingCells.face model D false k x :=
    (paddedFace_cell false hk f).trans (congrArg (GlobeMappingCells.face model D false k) hf)
  have hm : model.map (Globe.faceMap true k n) ≫ sf =
      model.map (Globe.faceMap false k n) ≫ f :=
    GlobeMappingCells.matching_representatives model D _ _ h sf f hs hf
  have hm' := (GlobeMappingCells.faces_eq_iff model D true false k n n sf f).mpr hm
  calc
    _ = comp k (GlobeMappingCells.ι model D n sf) (GlobeMappingCells.ι model D n f) hm' :=
      (comp_congr hs hf hm' h).symm
    _ = GlobeMappingCells.ι model D n (composite hk sf f hm) := comp_ι hk sf f hm hm'
    _ = GlobeMappingCells.ι model D n f :=
      congrArg (GlobeMappingCells.ι model D n) (composite_source_identity hk f hm)
    _ = x := hf

theorem right_unit (k : ℕ) (x : Cell D)
    (h : GlobeMappingCells.face model D true k x =
      GlobeMappingCells.face model D false k (GlobeMappingCells.face model D true k x)) :
    comp k x (GlobeMappingCells.face model D true k x) h = x := by
  obtain ⟨n, hn, f, hf⟩ := GlobeMappingCells.exists_representative_above model D x (k+1)
  have hk : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
  let tf := paddedFace true hk f
  have ht : GlobeMappingCells.ι model D n tf = GlobeMappingCells.face model D true k x :=
    (paddedFace_cell true hk f).trans (congrArg (GlobeMappingCells.face model D true k) hf)
  have hm : model.map (Globe.faceMap true k n) ≫ f =
      model.map (Globe.faceMap false k n) ≫ tf :=
    GlobeMappingCells.matching_representatives model D _ _ h f tf hf ht
  have hm' := (GlobeMappingCells.faces_eq_iff model D true false k n n f tf).mpr hm
  calc
    _ = comp k (GlobeMappingCells.ι model D n f) (GlobeMappingCells.ι model D n tf) hm' :=
      (comp_congr hf ht hm' h).symm
    _ = GlobeMappingCells.ι model D n (composite hk f tf hm) := comp_ι hk f tf hm hm'
    _ = GlobeMappingCells.ι model D n f :=
      congrArg (GlobeMappingCells.ι model D n) (composite_target_identity hk f hm)
    _ = x := hf

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # The finite strict parameter for interchange

Two horizontally pasted pairs are glued along their common higher face.
The four generating cells retain exactly the two horizontal and two
vertical matching conditions needed by strict interchange.
-/

namespace Thomason.Construction.StrictOmegaCategory.GridGlobe

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable (n k l : ℕ) (hkl : k < l)

abbrev category : StrictOmegaCategory.{0} :=
  pushout (GrayMapping.pastingFace true l n k hkl) (GrayMapping.pastingFace false l n k hkl)

abbrev row (b : Bool) : PastingGlobe.category n n k ⟶ category n k l hkl :=
  if b then pushout.inr _ _ else pushout.inl _ _

abbrev inclusion (b a : Bool) : Globe.category n ⟶ category n k l hkl :=
  (if a then PastingGlobe.right n n k else PastingGlobe.left n n k) ≫ row n k l hkl b

def cell (b a : Bool) : category n k l hkl := (inclusion n k l hkl b a).toFun Globe.Cell.top

theorem cell_dimension (b a : Bool) :
    (category n k l hkl).DimensionLE n (cell n k l hkl b a) :=
  (inclusion n k l hkl b a).dimensionLE (Globe.category_truncated n Globe.Cell.top)

theorem horizontal_matching (b : Bool) :
    (category n k l hkl).target k (cell n k l hkl b false) =
      (category n k l hkl).source k (cell n k l hkl b true) := by
  have h := congrArg (row n k l hkl b).toFun (PastingGlobe.matching n n k)
  exact ((row n k l hkl b).map_face true k (PastingGlobe.leftCell n n k)).symm.trans
    (h.trans ((row n k l hkl b).map_face false k (PastingGlobe.rightCell n n k)))

theorem vertical_boundary (a : Bool) :
    Globe.faceMap true l n ≫ inclusion n k l hkl false a =
      Globe.faceMap false l n ≫ inclusion n k l hkl true a := by
  cases a
  · change Globe.faceMap true l n ≫ (PastingGlobe.left n n k ≫ pushout.inl _ _) =
      Globe.faceMap false l n ≫ (PastingGlobe.left n n k ≫ pushout.inr _ _)
    rw [← Category.assoc, ← GrayMapping.pastingFace_left, Category.assoc,
      pushout.condition, ← Category.assoc, GrayMapping.pastingFace_left, Category.assoc]
  · change Globe.faceMap true l n ≫ (PastingGlobe.right n n k ≫ pushout.inl _ _) =
      Globe.faceMap false l n ≫ (PastingGlobe.right n n k ≫ pushout.inr _ _)
    rw [← Category.assoc, ← GrayMapping.pastingFace_right, Category.assoc,
      pushout.condition, ← Category.assoc, GrayMapping.pastingFace_right, Category.assoc]

theorem vertical_matching (a : Bool) :
    (category n k l hkl).target l (cell n k l hkl false a) =
      (category n k l hkl).source l (cell n k l hkl true a) := by
  have he := congrArg (fun f : Globe.category l ⟶ category n k l hkl =>
    f.toFun Globe.Cell.top) (vertical_boundary n k l hkl a)
  exact ((inclusion n k l hkl false a).map_face true l Globe.Cell.top).symm.trans
    (he.trans ((inclusion n k l hkl true a).map_face false l Globe.Cell.top))

theorem hom_ext {C : StrictOmegaCategory.{0}} (f g : category n k l hkl ⟶ C)
    (h : ∀ b a, f.toFun (cell n k l hkl b a) = g.toFun (cell n k l hkl b a)) : f = g := by
  apply pushout.hom_ext
  · exact PastingGlobe.hom_ext _ _ (h false false) (h false true)
  · exact PastingGlobe.hom_ext _ _ (h true false) (h true true)

end
end Thomason.Construction.StrictOmegaCategory.GridGlobe

end

section

/-! # Matching row maps on the common higher face

Four boundary-compatible globe-cylinder maps induce two binary gluing
maps which agree on the entire intervening pasted-globe cylinder.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

variable {D : StrictOmegaCategory.{0}} {n k l : ℕ}

theorem grid_row_matching (hkl : k < l) (hln : l < n)
    (a b c d : model.obj (Globe.category n) ⟶ D)
    (hab : model.map (Globe.faceMap true k n) ≫ a = model.map (Globe.faceMap false k n) ≫ b)
    (hcd : model.map (Globe.faceMap true k n) ≫ c = model.map (Globe.faceMap false k n) ≫ d)
    (hac : model.map (Globe.faceMap true l n) ≫ a = model.map (Globe.faceMap false l n) ≫ c)
    (hbd : model.map (Globe.faceMap true l n) ≫ b = model.map (Globe.faceMap false l n) ≫ d) :
    model.map (pastingFace true l n k hkl) ≫ glue (hkl.trans hln) a b hab =
      model.map (pastingFace false l n k hkl) ≫ glue (hkl.trans hln) c d hcd := by
  apply (PastingGlobe.CylinderSource.isPushout hkl).hom_ext
  · rw [← Category.assoc, ← model.map_comp, pastingFace_left,
      model.map_comp, Category.assoc, glue_left,
      ← Category.assoc, ← model.map_comp, pastingFace_left,
      model.map_comp, Category.assoc, glue_left]
    exact hac
  · rw [← Category.assoc, ← model.map_comp, pastingFace_right,
      model.map_comp, Category.assoc, glue_right,
      ← Category.assoc, ← model.map_comp, pastingFace_right,
      model.map_comp, Category.assoc, glue_right]
    exact hbd

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # The strict interchange diagram on the four-globe parameter -/

namespace Thomason.Construction.StrictOmegaCategory.GridGlobe

open CategoryTheory

noncomputable section

variable (n k l : ℕ) (hkl : k < l)

def horizontalComposite (b : Bool) : category n k l hkl :=
  (category n k l hkl).comp k (cell n k l hkl b false) (cell n k l hkl b true)
    (horizontal_matching n k l hkl b)

def verticalComposite (a : Bool) : category n k l hkl :=
  (category n k l hkl).comp l (cell n k l hkl false a) (cell n k l hkl true a)
    (vertical_matching n k l hkl a)

private theorem comp_congr (C : StrictOmegaCategory) {r : ℕ} {x y x' y' : C}
    (hx : x = x') (hy : y = y')
    (h : C.target r x = C.source r y) (h' : C.target r x' = C.source r y') :
    C.comp r x y h = C.comp r x' y' h' := by
  subst x'
  subst y'
  rfl

theorem face_horizontal_matching (a b : Bool) :
    (category n k l hkl).target k ((category n k l hkl).face a l (cell n k l hkl b false)) =
      (category n k l hkl).source k ((category n k l hkl).face a l (cell n k l hkl b true)) := by
  simpa only [source, target, (category n k l hkl).globular, hkl, ite_true] using
    horizontal_matching n k l hkl b

theorem horizontal_composites_matching :
    (category n k l hkl).target l (horizontalComposite n k l hkl false) =
      (category n k l hkl).source l (horizontalComposite n k l hkl true) := by
  change (category n k l hkl).face true l ((category n k l hkl).comp k _ _ _) =
    (category n k l hkl).face false l ((category n k l hkl).comp k _ _ _)
  rw [(category n k l hkl).face_comp true l k hkl _ _ _
      (face_horizontal_matching n k l hkl true false),
    (category n k l hkl).face_comp false l k hkl _ _ _
      (face_horizontal_matching n k l hkl false true)]
  exact comp_congr _ (vertical_matching n k l hkl false)
    (vertical_matching n k l hkl true) _ _

theorem verticalComposite_lower_face (a b : Bool) :
    (category n k l hkl).face a k (verticalComposite n k l hkl b) =
      (category n k l hkl).face a k (cell n k l hkl false b) := by
  have he := congrArg ((category n k l hkl).face a k)
    ((category n k l hkl).source_comp l (cell n k l hkl false b)
      (cell n k l hkl true b) (vertical_matching n k l hkl b))
  simpa only [verticalComposite, source, (category n k l hkl).globular, hkl, ite_true] using he

theorem vertical_composites_matching :
    (category n k l hkl).target k (verticalComposite n k l hkl false) =
      (category n k l hkl).source k (verticalComposite n k l hkl true) :=
  (verticalComposite_lower_face n k l hkl true false).trans
    ((horizontal_matching n k l hkl false).trans
      (verticalComposite_lower_face n k l hkl false true).symm)

variable (hln : l < n)

theorem horizontalComposite_dimension (hln : l < n) (b : Bool) :
    (category n k l hkl).DimensionLE n (horizontalComposite n k l hkl b) :=
  (category n k l hkl).dimensionLE_comp (hkl.trans hln)
    (cell_dimension n k l hkl b false) (cell_dimension n k l hkl b true) _

theorem verticalComposite_dimension (hln : l < n) (a : Bool) :
    (category n k l hkl).DimensionLE n (verticalComposite n k l hkl a) :=
  (category n k l hkl).dimensionLE_comp hln
    (cell_dimension n k l hkl false a) (cell_dimension n k l hkl true a) _

/-- The vertical pair of horizontal composites. -/
def verticalOuter : PastingGlobe.category n n l ⟶ category n k l hkl :=
  PastingGlobe.desc _ (horizontalComposite n k l hkl false)
    (horizontalComposite n k l hkl true)
    (horizontalComposite_dimension n k l hkl hln false)
    (horizontalComposite_dimension n k l hkl hln true)
    (horizontal_composites_matching n k l hkl)

/-- The horizontal pair of vertical composites. -/
def horizontalOuter : PastingGlobe.category n n k ⟶ category n k l hkl :=
  PastingGlobe.desc _ (verticalComposite n k l hkl false)
    (verticalComposite n k l hkl true)
    (verticalComposite_dimension n k l hkl hln false)
    (verticalComposite_dimension n k l hkl hln true)
    (vertical_composites_matching n k l hkl)

/-- The individual vertical column, including both its generating cells. -/
def column (a : Bool) : PastingGlobe.category n n l ⟶ category n k l hkl :=
  PastingGlobe.desc _ (cell n k l hkl false a) (cell n k l hkl true a)
    (cell_dimension n k l hkl false a) (cell_dimension n k l hkl true a)
    (vertical_matching n k l hkl a)

theorem column_left (a : Bool) :
    PastingGlobe.left n n l ≫ column n k l hkl a = inclusion n k l hkl false a := by
  apply Globe.hom_ext
  exact PastingGlobe.desc_left _ _ _ _ _ _

theorem column_right (a : Bool) :
    PastingGlobe.right n n l ≫ column n k l hkl a = inclusion n k l hkl true a := by
  apply Globe.hom_ext
  exact PastingGlobe.desc_right _ _ _ _ _ _

theorem row_composite (b : Bool) :
    (row n k l hkl b).toFun (PastingGlobe.composite n n k) = horizontalComposite n k l hkl b :=
  (row n k l hkl b).map_comp k _ _ _ (horizontal_matching n k l hkl b)

theorem column_composite (a : Bool) :
    (column n k l hkl a).toFun (PastingGlobe.composite n n l) = verticalComposite n k l hkl a :=
  PastingGlobe.desc_composite _ _ _ _ _ _

theorem verticalOuter_left :
    PastingGlobe.left n n l ≫ verticalOuter n k l hkl hln =
      GrayMapping.compositionGlobe n k (hkl.trans hln) ≫ row n k l hkl false := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_left _ _ _ _ _ _).trans (row_composite n k l hkl false).symm

theorem verticalOuter_right :
    PastingGlobe.right n n l ≫ verticalOuter n k l hkl hln =
      GrayMapping.compositionGlobe n k (hkl.trans hln) ≫ row n k l hkl true := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_right _ _ _ _ _ _).trans (row_composite n k l hkl true).symm

theorem horizontalOuter_left :
    PastingGlobe.left n n k ≫ horizontalOuter n k l hkl hln =
      GrayMapping.compositionGlobe n l hln ≫ column n k l hkl false := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_left _ _ _ _ _ _).trans (column_composite n k l hkl false).symm

theorem horizontalOuter_right :
    PastingGlobe.right n n k ≫ horizontalOuter n k l hkl hln =
      GrayMapping.compositionGlobe n l hln ≫ column n k l hkl true := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_right _ _ _ _ _ _).trans (column_composite n k l hkl true).symm

/-- Strict interchange is an equality of actual finite parameter maps. -/
theorem interchange_diagram :
    GrayMapping.compositionGlobe n l hln ≫ verticalOuter n k l hkl hln =
      GrayMapping.compositionGlobe n k (hkl.trans hln) ≫ horizontalOuter n k l hkl hln := by
  apply Globe.hom_ext
  exact (PastingGlobe.desc_composite _ _ _ _ _ _).trans
    (((category n k l hkl).interchange k l hkl
      (cell n k l hkl false false) (cell n k l hkl false true)
      (cell n k l hkl true false) (cell n k l hkl true true)
      (horizontal_matching n k l hkl false) (horizontal_matching n k l hkl true)
      (vertical_matching n k l hkl false) (vertical_matching n k l hkl true)
      (horizontal_composites_matching n k l hkl) (vertical_composites_matching n k l hkl)).trans
        (PastingGlobe.desc_composite _ _ _ _ _ _).symm)

end
end Thomason.Construction.StrictOmegaCategory.GridGlobe

end

section

/-! # Split row intersections in the interchange parameter

Both higher-face maps have the same strict retraction. The two row
retractions therefore detect duplicate row images after every functor.
-/

namespace Thomason.Construction.StrictOmegaCategory.GridGlobe

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {n k l : ℕ} (hkl : k < l) (hln : l ≤ n)

theorem face_lower_retraction (a : Bool) :
    GrayMapping.pastingFace a l n k hkl ≫ GrayMapping.pastingLower hln k = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [← Category.assoc, GrayMapping.pastingFace_left, Category.assoc,
      GrayMapping.pastingLower_left, ← Category.assoc, Globe.faceMap_lower_retraction,
      Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, GrayMapping.pastingFace_right, Category.assoc,
      GrayMapping.pastingLower_right, ← Category.assoc, Globe.faceMap_lower_retraction,
      Category.id_comp, Category.comp_id]

def retractTop : category n k l hkl ⟶ PastingGlobe.category n n k :=
  pushout.desc (𝟙 _) (GrayMapping.pastingLower hln k ≫ GrayMapping.pastingFace true l n k hkl) (by
    rw [Category.comp_id, ← Category.assoc, face_lower_retraction, Category.id_comp])

def retractBottom : category n k l hkl ⟶ PastingGlobe.category n n k :=
  pushout.desc (GrayMapping.pastingLower hln k ≫ GrayMapping.pastingFace false l n k hkl) (𝟙 _) (by
    rw [Category.comp_id, ← Category.assoc, face_lower_retraction, Category.id_comp])

@[reassoc (attr := simp)] theorem top_retractTop :
    row n k l hkl false ≫ retractTop hkl hln = 𝟙 _ := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem bottom_retractTop :
    row n k l hkl true ≫ retractTop hkl hln =
      GrayMapping.pastingLower hln k ≫ GrayMapping.pastingFace true l n k hkl :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)] theorem top_retractBottom :
    row n k l hkl false ≫ retractBottom hkl hln =
      GrayMapping.pastingLower hln k ≫ GrayMapping.pastingFace false l n k hkl :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)] theorem bottom_retractBottom :
    row n k l hkl true ≫ retractBottom hkl hln = 𝟙 _ := pushout.inr_desc _ _ _

def retractRow (b : Bool) : category n k l hkl ⟶ PastingGlobe.category n n k :=
  if b then retractBottom hkl hln else retractTop hkl hln

@[reassoc (attr := simp)] theorem row_retractRow (b : Bool) :
    row n k l hkl b ≫ retractRow hkl hln b = 𝟙 _ := by
  cases b
  · exact top_retractTop hkl hln
  · exact bottom_retractBottom hkl hln

variable (F : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0})

abbrev ImageSource : StrictOmegaCategory.{0} :=
  pushout (F.map (GrayMapping.pastingFace true l n k hkl))
    (F.map (GrayMapping.pastingFace false l n k hkl))

include hln in
theorem row_map_injective (b : Bool) :
    Function.Injective (F.map (row n k l hkl b)).toFun := by
  have he : F.map (row n k l hkl b) ≫ F.map (retractRow hkl hln b) = 𝟙 _ := by
    rw [← F.map_comp, row_retractRow, F.map_id]
  have hi : Function.LeftInverse (F.map (retractRow hkl hln b)).toFun
      (F.map (row n k l hkl b)).toFun := fun x =>
    congrArg (fun q => q.toFun x) he
  exact hi.injective

include hln in
/-- Equality of top and bottom images is already witnessed in the actual
pushout of their functor images. -/
theorem cross_image_eq (x y : F.obj (PastingGlobe.category n n k))
    (he : (F.map (row n k l hkl false)).toFun x = (F.map (row n k l hkl true)).toFun y) :
    (pushout.inl (F.map (GrayMapping.pastingFace true l n k hkl))
      (F.map (GrayMapping.pastingFace false l n k hkl))).toFun x =
    (pushout.inr (F.map (GrayMapping.pastingFace true l n k hkl))
      (F.map (GrayMapping.pastingFace false l n k hkl))).toFun y := by
  let z := (F.map (GrayMapping.pastingLower hln k)).toFun y
  have hx : x = (F.map (GrayMapping.pastingFace true l n k hkl)).toFun z := by
    have hh := congrArg (F.map (retractTop hkl hln)).toFun he
    have hl := congrArg (fun u => u.toFun x)
      (show F.map (row n k l hkl false) ≫ F.map (retractTop hkl hln) = 𝟙 _ by
        rw [← F.map_comp, top_retractTop, F.map_id])
    have hr := congrArg (fun u => u.toFun y)
      (show F.map (row n k l hkl true) ≫ F.map (retractTop hkl hln) =
        F.map (GrayMapping.pastingLower hln k) ≫ F.map (GrayMapping.pastingFace true l n k hkl) by
        rw [← F.map_comp, bottom_retractTop, F.map_comp])
    exact hl.symm.trans (hh.trans hr)
  have hz : (F.map (GrayMapping.pastingLower hln k)).toFun x = z := by
    rw [hx]
    exact congrArg (fun u => u.toFun z)
      (show F.map (GrayMapping.pastingFace true l n k hkl) ≫
          F.map (GrayMapping.pastingLower hln k) = 𝟙 _ by
        rw [← F.map_comp, face_lower_retraction, F.map_id])
  have hy : (F.map (GrayMapping.pastingFace false l n k hkl)).toFun z = y := by
    have hh := congrArg (F.map (retractBottom hkl hln)).toFun he
    have hl := congrArg (fun u => u.toFun x)
      (show F.map (row n k l hkl false) ≫ F.map (retractBottom hkl hln) =
        F.map (GrayMapping.pastingLower hln k) ≫ F.map (GrayMapping.pastingFace false l n k hkl) by
        rw [← F.map_comp, top_retractBottom, F.map_comp])
    have hr := congrArg (fun u => u.toFun y)
      (show F.map (row n k l hkl true) ≫ F.map (retractBottom hkl hln) = 𝟙 _ by
        rw [← F.map_comp, bottom_retractBottom, F.map_id])
    exact (congrArg (F.map (GrayMapping.pastingFace false l n k hkl)).toFun hz).symm.trans
      (hl.symm.trans (hh.trans hr))
  rw [hx, ← hy]
  exact congrArg (fun u : F.obj (PastingGlobe.category l l k) ⟶ ImageSource hkl F => u.toFun z)
    (pushout.condition (f := F.map (GrayMapping.pastingFace true l n k hkl))
      (g := F.map (GrayMapping.pastingFace false l n k hkl)))

end
end Thomason.Construction.StrictOmegaCategory.GridGlobe

end

section

/-! # The four-cell universal property of the interchange parameter -/

namespace Thomason.Construction.StrictOmegaCategory.GridGlobe

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {n k l : ℕ} (hkl : k < l) (C : StrictOmegaCategory.{0}) (x : Bool → Bool → C)
    (hd : ∀ b a, C.DimensionLE n (x b a))
    (hh : ∀ b, C.target k (x b false) = C.source k (x b true))
    (hv : ∀ a, C.target l (x false a) = C.source l (x true a))

abbrev rowDesc (b : Bool) : PastingGlobe.category n n k ⟶ C :=
  PastingGlobe.desc C (x b false) (x b true) (hd b false) (hd b true) (hh b)

include hv in
theorem desc_condition :
    GrayMapping.pastingFace true l n k hkl ≫ rowDesc C x hd hh false =
      GrayMapping.pastingFace false l n k hkl ≫ rowDesc C x hd hh true := by
  apply PastingGlobe.hom_ext
  · change (rowDesc C x hd hh false).toFun
        ((GrayMapping.pastingFace true l n k hkl).toFun (PastingGlobe.leftCell l l k)) =
      (rowDesc C x hd hh true).toFun
        ((GrayMapping.pastingFace false l n k hkl).toFun (PastingGlobe.leftCell l l k))
    rw [show (GrayMapping.pastingFace true l n k hkl).toFun (PastingGlobe.leftCell l l k) =
          (PastingGlobe.category n n k).face true l (PastingGlobe.leftCell n n k) from
        PastingGlobe.desc_left _ _ _ _ _ _,
      show (GrayMapping.pastingFace false l n k hkl).toFun (PastingGlobe.leftCell l l k) =
          (PastingGlobe.category n n k).face false l (PastingGlobe.leftCell n n k) from
        PastingGlobe.desc_left _ _ _ _ _ _,
      (rowDesc C x hd hh false).map_face, (rowDesc C x hd hh true).map_face]
    exact (congrArg (C.face true l) (PastingGlobe.desc_left C _ _ _ _ _)).trans
      ((hv false).trans (congrArg (C.face false l) (PastingGlobe.desc_left C _ _ _ _ _)).symm)
  · change (rowDesc C x hd hh false).toFun
        ((GrayMapping.pastingFace true l n k hkl).toFun (PastingGlobe.rightCell l l k)) =
      (rowDesc C x hd hh true).toFun
        ((GrayMapping.pastingFace false l n k hkl).toFun (PastingGlobe.rightCell l l k))
    rw [show (GrayMapping.pastingFace true l n k hkl).toFun (PastingGlobe.rightCell l l k) =
          (PastingGlobe.category n n k).face true l (PastingGlobe.rightCell n n k) from
        PastingGlobe.desc_right _ _ _ _ _ _,
      show (GrayMapping.pastingFace false l n k hkl).toFun (PastingGlobe.rightCell l l k) =
          (PastingGlobe.category n n k).face false l (PastingGlobe.rightCell n n k) from
        PastingGlobe.desc_right _ _ _ _ _ _,
      (rowDesc C x hd hh false).map_face, (rowDesc C x hd hh true).map_face]
    exact (congrArg (C.face true l) (PastingGlobe.desc_right C _ _ _ _ _)).trans
      ((hv true).trans (congrArg (C.face false l) (PastingGlobe.desc_right C _ _ _ _ _)).symm)

/-- Unique strict map with the prescribed four matching bounded cells. -/
def desc : category n k l hkl ⟶ C :=
  pushout.desc (rowDesc C x hd hh false) (rowDesc C x hd hh true)
    (desc_condition hkl C x hd hh hv)

@[simp] theorem desc_cell (b a : Bool) :
    (desc hkl C x hd hh hv).toFun (cell n k l hkl b a) = x b a := by
  have hrow : row n k l hkl b ≫ desc hkl C x hd hh hv = rowDesc C x hd hh b := by
    cases b
    · exact pushout.inl_desc _ _ _
    · exact pushout.inr_desc _ _ _
  cases a
  · exact (congrArg (fun f : PastingGlobe.category n n k ⟶ C =>
      f.toFun (PastingGlobe.leftCell n n k)) hrow).trans (PastingGlobe.desc_left C _ _ _ _ _)
  · exact (congrArg (fun f : PastingGlobe.category n n k ⟶ C =>
      f.toFun (PastingGlobe.rightCell n n k)) hrow).trans (PastingGlobe.desc_right C _ _ _ _ _)

end
end Thomason.Construction.StrictOmegaCategory.GridGlobe

end

section

/-! # The grid basis is the actual abelianization of four pasted globes -/

namespace Thomason.Construction.GridGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

def top {n k l : ℕ} (hkl : k < l) (hln : l < n) (s a : Bool) :
    (complex hkl hln).realization :=
  (inclusion hkl hln s).realization.toFun (PastingGlobeBasis.top (hkl.trans hln) a)

theorem top_dimension {n k l : ℕ} (hkl : k < l) (hln : l < n) (s a : Bool) :
    (complex hkl hln).realization.DimensionLE n (top hkl hln s a) :=
  (inclusion hkl hln s).realization.dimensionLE
    (PastingGlobeBasis.top_dimension (hkl.trans hln) a)

theorem top_horizontal {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) :
    (top hkl hln s false).face true k = (top hkl hln s true).face false k := by
  have he := congrArg (inclusion hkl hln s).realization.toFun
    (PastingGlobeBasis.top_matching (hkl.trans hln))
  exact ((inclusion hkl hln s).realization.map_face true k _).symm.trans
    (he.trans ((inclusion hkl hln s).realization.map_face false k _))

theorem top_table_below {n k l p : ℕ} (hkl : k < l) (hln : l < n)
    (s c a : Bool) (hp : p < n) :
    (top hkl hln s c).table a p = Finsupp.single
      (embed hkl hln s (PastingGlobeBasis.embed (hkl.trans hln) c ⟨a, Or.inl hp⟩)) 1 := by
  change embedApp hkl hln s p
    (PastingGlobeBasis.embedApp (hkl.trans hln) c p
      (DirectedGlobeComplex.topTable n a p)) = _
  simp [DirectedGlobeComplex.topTable, hp]

theorem top_vertical {n k l : ℕ} (hkl : k < l) (hln : l < n) (c : Bool) :
    (top hkl hln false c).face true l = (top hkl hln true c).face false l := by
  apply Cell.ext
  funext a p
  change Cell.cutTable (top hkl hln false c) true l a p =
    Cell.cutTable (top hkl hln true c) false l a p
  by_cases hp : p < l
  · simp only [Cell.cutTable, hp, ite_true]
    rw [top_table_below hkl hln _ _ _ (hp.trans hln),
      top_table_below hkl hln _ _ _ (hp.trans hln)]
    simp [embed, hp]
    rfl
  · by_cases he : p = l
    · subst p
      simp only [Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]
      rw [top_table_below hkl hln _ _ _ hln, top_table_below hkl hln _ _ _ hln]
      cases c <;> simp [embed, targetBasis, left, PastingGlobeBasis.embed,
        PastingGlobeBasis.left, PastingGlobeBasis.right, Nat.ne_of_gt hkl,
        Nat.not_lt.mpr hkl.le]
      all_goals rfl
    · simp only [Cell.cutTable, hp, he, ite_false]

def fromGrid {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    StrictOmegaCategory.GridGlobe.category n k l hkl ⟶ (complex hkl hln).realization :=
  StrictOmegaCategory.GridGlobe.desc hkl _ (top hkl hln)
    (top_dimension hkl hln) (top_horizontal hkl hln) (top_vertical hkl hln)

@[simp] theorem fromGrid_cell {n k l : ℕ} (hkl : k < l) (hln : l < n) (s a : Bool) :
    (fromGrid hkl hln).toFun (StrictOmegaCategory.GridGlobe.cell n k l hkl s a) =
      top hkl hln s a := StrictOmegaCategory.GridGlobe.desc_cell _ _ _ _ _ _ s a

def abelianizationToBasis {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    Hom (StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.GridGlobe.category n k l hkl)) (complex hkl hln) :=
  StrictOmegaCategory.Abelianization.evaluateHom (fromGrid hkl hln)

theorem unit_horizontal {n k l : ℕ} (hkl : k < l) (s : Bool) :
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.GridGlobe.cell n k l hkl s false)).face true k =
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.GridGlobe.cell n k l hkl s true)).face false k := by
  rw [← StrictOmegaCategory.Abelianization.unitCell_face,
    ← StrictOmegaCategory.Abelianization.unitCell_face]
  exact congrArg (StrictOmegaCategory.Abelianization.unitCell _)
    (StrictOmegaCategory.GridGlobe.horizontal_matching n k l hkl s)

theorem unit_vertical {n k l : ℕ} (hkl : k < l) (a : Bool) :
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.GridGlobe.cell n k l hkl false a)).face true l =
    (StrictOmegaCategory.Abelianization.unitCell _
      (StrictOmegaCategory.GridGlobe.cell n k l hkl true a)).face false l := by
  rw [← StrictOmegaCategory.Abelianization.unitCell_face,
    ← StrictOmegaCategory.Abelianization.unitCell_face]
  exact congrArg (StrictOmegaCategory.Abelianization.unitCell _)
    (StrictOmegaCategory.GridGlobe.vertical_matching n k l hkl a)

def basisToAbelianization {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    Hom (complex hkl hln) (StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.GridGlobe.category n k l hkl)) :=
  desc hkl hln (fun s a => StrictOmegaCategory.Abelianization.unitCell _
    (StrictOmegaCategory.GridGlobe.cell n k l hkl s a))
      (unit_horizontal hkl) (unit_vertical hkl)

theorem desc_top {n k l : ℕ} {L : DirectedComplex.{0}} (hkl : k < l) (hln : l < n)
    (x : Bool → Bool → Cell L)
    (hh : ∀ b, (x b false).face true k = (x b true).face false k)
    (hv : ∀ a, (x false a).face true l = (x true a).face false l)
    (s a : Bool) (hb : L.realization.DimensionLE n (x s a)) :
    (desc hkl hln x hh hv).realization.toFun (top hkl hln s a) = x s a := by
  have h := congrArg (fun f : Hom (PastingGlobeBasis.complex n k (hkl.trans hln)) L =>
    f.realization.toFun (PastingGlobeBasis.top (hkl.trans hln) a))
      (inclusion_desc hkl hln x hh hv s)
  cases a <;> exact h.trans (PastingGlobeBasis.desc_top (hkl.trans hln) _ _ (hh s) _ hb)

theorem abelianizationToBasis_unit {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (x : StrictOmegaCategory.GridGlobe.category n k l hkl) :
    (abelianizationToBasis hkl hln).realization.toFun
      (StrictOmegaCategory.Abelianization.unitCell _ x) = (fromGrid hkl hln).toFun x :=
  congrArg (fun f => f.toFun x)
    (StrictOmegaCategory.Abelianization.unit_evaluate (fromGrid hkl hln))

theorem basisToAbelianization_top {n k l : ℕ} (hkl : k < l) (hln : l < n) (s a : Bool) :
    (basisToAbelianization hkl hln).realization.toFun (top hkl hln s a) =
      StrictOmegaCategory.Abelianization.unitCell _
        (StrictOmegaCategory.GridGlobe.cell n k l hkl s a) := by
  exact desc_top hkl hln _ (unit_horizontal hkl) (unit_vertical hkl) s a
    ((StrictOmegaCategory.Abelianization.unit _).dimensionLE
      (StrictOmegaCategory.GridGlobe.cell_dimension n k l hkl s a))

theorem abelianizationToBasis_inverse {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    Hom.comp (abelianizationToBasis hkl hln) (basisToAbelianization hkl hln) = Hom.id _ := by
  apply (StrictOmegaCategory.Abelianization.homEquiv
    (StrictOmegaCategory.GridGlobe.category n k l hkl) _).injective
  apply StrictOmegaCategory.GridGlobe.hom_ext
  intro s a
  change (basisToAbelianization hkl hln).realization.toFun
    ((abelianizationToBasis hkl hln).realization.toFun
      (StrictOmegaCategory.Abelianization.unitCell _
        (StrictOmegaCategory.GridGlobe.cell n k l hkl s a))) = _
  rw [abelianizationToBasis_unit, fromGrid_cell]
  exact basisToAbelianization_top hkl hln s a

theorem basisToAbelianization_inverse {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    Hom.comp (basisToAbelianization hkl hln) (abelianizationToBasis hkl hln) = Hom.id _ := by
  apply hom_ext hkl hln
  intro s
  apply PastingGlobeBasis.hom_ext (hkl.trans hln)
  all_goals
    apply (DirectedGlobeComplex.homEquiv n (complex hkl hln)).injective
    apply Subtype.ext
  · change (abelianizationToBasis hkl hln).realization.toFun
      ((basisToAbelianization hkl hln).realization.toFun (top hkl hln s false)) = _
    rw [basisToAbelianization_top, abelianizationToBasis_unit, fromGrid_cell]
    rfl
  · change (abelianizationToBasis hkl hln).realization.toFun
      ((basisToAbelianization hkl hln).realization.toFun (top hkl hln s true)) = _
    rw [basisToAbelianization_top, abelianizationToBasis_unit, fromGrid_cell]
    rfl

def abelianizationIso {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    StrictOmegaCategory.Abelianization.complex
      (StrictOmegaCategory.GridGlobe.category n k l hkl) ≅ complex hkl hln where
  hom := abelianizationToBasis hkl hln
  inv := basisToAbelianization hkl hln
  hom_inv_id := abelianizationToBasis_inverse hkl hln
  inv_hom_id := basisToAbelianization_inverse hkl hln

end
end Thomason.Construction.GridGlobeBasis

end

section

/-! # The literal chain-cylinder comparison on both rows of the grid -/

namespace Thomason.Construction.GridGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory StrictOmegaCategory

noncomputable section

theorem abelianization_row {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) :
    Abelianization.functor.map (GridGlobe.row n k l hkl s) ≫
      (abelianizationIso hkl hln).hom =
        (PastingGlobeBasis.abelianizationIso (hkl.trans hln)).hom ≫ inclusion hkl hln s := by
  let a : Abelianization.functor.obj (PastingGlobe.category n n k) ⟶ complex hkl hln :=
    (PastingGlobeBasis.abelianizationIso (hkl.trans hln)).hom ≫ inclusion hkl hln s
  let b : Abelianization.functor.obj (GridGlobe.category n k l hkl) ⟶ complex hkl hln :=
    (abelianizationIso hkl hln).hom
  change Abelianization.functor.map (GridGlobe.row n k l hkl s) ≫ b = a
  apply (Abelianization.adjunction.homEquiv _ _).injective
  rw [Abelianization.adjunction.homEquiv_naturality_left]
  change GridGlobe.row n k l hkl s ≫ (Abelianization.unit _ ≫
      (Abelianization.evaluateHom (fromGrid hkl hln)).realization) =
    (Abelianization.unit _ ≫
      (Abelianization.evaluateHom (PastingGlobeBasis.fromPasting (hkl.trans hln))).realization) ≫
      (inclusion hkl hln s).realization
  have ht : Abelianization.unit (GridGlobe.category n k l hkl) ≫
      (Abelianization.evaluateHom (fromGrid hkl hln)).realization = fromGrid hkl hln :=
    Abelianization.unit_evaluate _
  have hp : Abelianization.unit (PastingGlobe.category n n k) ≫
      (Abelianization.evaluateHom (PastingGlobeBasis.fromPasting (hkl.trans hln))).realization =
        PastingGlobeBasis.fromPasting (hkl.trans hln) := Abelianization.unit_evaluate _
  rw [ht, hp]
  apply PastingGlobe.hom_ext
  · change (fromGrid hkl hln).toFun (GridGlobe.cell n k l hkl s false) =
      (inclusion hkl hln s).realization.toFun
        ((PastingGlobeBasis.fromPasting (hkl.trans hln)).toFun (PastingGlobe.leftCell n n k))
    have hl : (PastingGlobeBasis.fromPasting (hkl.trans hln)).toFun
        (PastingGlobe.leftCell n n k) = PastingGlobeBasis.top (hkl.trans hln) false :=
      PastingGlobe.desc_left _ _ _ _ _ _
    rw [fromGrid_cell, hl]
    rfl
  · change (fromGrid hkl hln).toFun (GridGlobe.cell n k l hkl s true) =
      (inclusion hkl hln s).realization.toFun
        ((PastingGlobeBasis.fromPasting (hkl.trans hln)).toFun (PastingGlobe.rightCell n n k))
    have hr : (PastingGlobeBasis.fromPasting (hkl.trans hln)).toFun
        (PastingGlobe.rightCell n n k) = PastingGlobeBasis.top (hkl.trans hln) true :=
      PastingGlobe.desc_right _ _ _ _ _ _
    rw [fromGrid_cell, hr]
    rfl

def modelIso {n k l : ℕ} (hkl : k < l) (hln : l < n) :
    GrayChainExtension.model.obj (GridGlobe.category n k l hkl) ≅
      (rightCylinder (complex hkl hln)).realization :=
  (rightCylinderFunctor ⋙ realizationFunctor).mapIso (abelianizationIso hkl hln)

theorem model_row {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) :
    GrayChainExtension.model.map (GridGlobe.row n k l hkl s) ≫ (modelIso hkl hln).hom =
      (PastingGlobeCylinderBasis.modelIso (hkl.trans hln)).hom ≫
        (RightCylinder.map (inclusion hkl hln s)).realization := by
  let T := rightCylinderFunctor ⋙ realizationFunctor
  exact (T.map_comp (Abelianization.functor.map (GridGlobe.row n k l hkl s))
    (abelianizationIso hkl hln).hom).symm.trans
      ((congrArg T.map (abelianization_row hkl hln s)).trans
        (T.map_comp (PastingGlobeBasis.abelianizationIso (hkl.trans hln)).hom
          (inclusion hkl hln s)))

end
end Thomason.Construction.GridGlobeBasis

end

end OAI
