import OAI.CategoryTheory.Thomason.Gray.GlobePastingDensity
import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.GrayMappingEndpointEvaluation
import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Gray.GraySimplexProjection
import OAI.CategoryTheory.Thomason.Gray.GridGlobeCylinderComparison
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeChains
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeRetractions
import OAI.CategoryTheory.Thomason.Transfer.TripleGlobeCylinderPushout

namespace OAI

section

/-! # Associativity of the actual mapping-cell composition

The constructed three-globe cylinder pushout extends any matching triple.
Evaluation of its strict associativity diagram then proves associativity
at a finite mapping level, and common finite representatives give the
unrestricted carrier law.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

variable {D : StrictOmegaCategory.{0}} {n k : ℕ}

private theorem tripleGlue_condition (hk : k < n)
    (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h) :
    model.map (TripleGlobe.bridge n k) ≫ glue hk f g hfg =
      model.map (Globe.faceMap false k n) ≫ h := by
  change model.map (Globe.faceMap true k n ≫ PastingGlobe.right n n k) ≫ glue hk f g hfg = _
  rw [model.map_comp, Category.assoc, glue_right]
  exact hgh

def tripleGlue (hk : k < n)
    (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h) :
    model.obj (TripleGlobe.category n k) ⟶ D :=
  (TripleGlobeCylinder.isPushout hk).desc (glue hk f g hfg) h (tripleGlue_condition hk f g h hfg hgh)

theorem tripleGlue_pair (hk : k < n)
    (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h) :
    model.map (TripleGlobe.pair n k) ≫ tripleGlue hk f g h hfg hgh = glue hk f g hfg :=
  (TripleGlobeCylinder.isPushout hk).inl_desc _ _ _

theorem tripleGlue_first (hk : k < n)
    (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h) :
    tripleEvaluation (tripleGlue hk f g h hfg hgh) 0 = f := by
  change model.map (PastingGlobe.left n n k ≫ TripleGlobe.pair n k) ≫ _ = _
  rw [model.map_comp, Category.assoc, tripleGlue_pair, glue_left]

theorem tripleGlue_middle (hk : k < n)
    (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h) :
    tripleEvaluation (tripleGlue hk f g h hfg hgh) 1 = g := by
  change model.map (PastingGlobe.right n n k ≫ TripleGlobe.pair n k) ≫ _ = _
  rw [model.map_comp, Category.assoc, tripleGlue_pair, glue_right]

theorem tripleGlue_last (hk : k < n)
    (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h) :
    tripleEvaluation (tripleGlue hk f g h hfg hgh) 2 = h :=
  (TripleGlobeCylinder.isPushout hk).inr_desc _ _ _

/-- Associativity at any common finite mapping level. -/
theorem composite_assoc (hk : k < n) (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h)
    (hl : model.map (Globe.faceMap true k n) ≫ composite hk f g hfg =
      model.map (Globe.faceMap false k n) ≫ h)
    (hr : model.map (Globe.faceMap true k n) ≫ f =
      model.map (Globe.faceMap false k n) ≫ composite hk g h hgh) :
    composite hk (composite hk f g hfg) h hl = composite hk f (composite hk g h hgh) hr := by
  let u := tripleGlue hk f g h hfg hgh
  have h0 : tripleEvaluation u 0 = f := tripleGlue_first hk f g h hfg hgh
  have h1 : tripleEvaluation u 1 = g := tripleGlue_middle hk f g h hfg hgh
  have h2 : tripleEvaluation u 2 = h := tripleGlue_last hk f g h hfg hgh
  have h01 : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 0 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 1 := by
    simpa only [h0, h1] using hfg
  have h12 : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 1 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 2 := by
    simpa only [h1, h2] using hgh
  have hL : model.map (Globe.faceMap true k n) ≫
        composite hk (tripleEvaluation u 0) (tripleEvaluation u 1) h01 =
      model.map (Globe.faceMap false k n) ≫ tripleEvaluation u 2 := by
    simpa only [h0, h1, h2] using hl
  have hR : model.map (Globe.faceMap true k n) ≫ tripleEvaluation u 0 =
      model.map (Globe.faceMap false k n) ≫
        composite hk (tripleEvaluation u 1) (tripleEvaluation u 2) h12 := by
    simpa only [h0, h1, h2] using hr
  simpa only [h0, h1, h2] using triple_associativity hk u h01 h12 hL hR

/-- Associativity on the images of three finite representatives. -/
theorem assoc_ι (hk : k < n) (f g h : model.obj (Globe.category n) ⟶ D)
    (hfg : model.map (Globe.faceMap true k n) ≫ f = model.map (Globe.faceMap false k n) ≫ g)
    (hgh : model.map (Globe.faceMap true k n) ≫ g = model.map (Globe.faceMap false k n) ≫ h)
    (hxy : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n f) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n g))
    (hyz : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n g) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n h))
    (hl : GlobeMappingCells.face model D true k
        (comp k (GlobeMappingCells.ι model D n f) (GlobeMappingCells.ι model D n g) hxy) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n h))
    (hr : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n f) =
      GlobeMappingCells.face model D false k
        (comp k (GlobeMappingCells.ι model D n g) (GlobeMappingCells.ι model D n h) hyz)) :
    comp k (comp k (GlobeMappingCells.ι model D n f) (GlobeMappingCells.ι model D n g) hxy)
        (GlobeMappingCells.ι model D n h) hl =
      comp k (GlobeMappingCells.ι model D n f)
        (comp k (GlobeMappingCells.ι model D n g) (GlobeMappingCells.ι model D n h) hyz) hr := by
  have hxyE := comp_ι hk f g hfg hxy
  have hyzE := comp_ι hk g h hgh hyz
  have hl' : GlobeMappingCells.face model D true k
        (GlobeMappingCells.ι model D n (composite hk f g hfg)) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n h) :=
    (congrArg (GlobeMappingCells.face model D true k) hxyE).symm.trans hl
  have hr' : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n f) =
      GlobeMappingCells.face model D false k
        (GlobeMappingCells.ι model D n (composite hk g h hgh)) :=
    hr.trans (congrArg (GlobeMappingCells.face model D false k) hyzE)
  have hlF := (GlobeMappingCells.faces_eq_iff model D true false k n n
    (composite hk f g hfg) h).mp hl'
  have hrF := (GlobeMappingCells.faces_eq_iff model D true false k n n
    f (composite hk g h hgh)).mp hr'
  exact (comp_congr hxyE rfl hl hl').trans
    ((comp_ι hk _ _ hlF hl').trans
      ((congrArg (GlobeMappingCells.ι model D n) (composite_assoc hk f g h hfg hgh hlF hrF)).trans
        ((comp_ι hk _ _ hrF hr').symm.trans (comp_congr rfl hyzE hr hr').symm)))

/-- The actual carrier operation satisfies strict associativity. -/
theorem assoc (k : ℕ) (x y z : Cell D)
    (hxy : GlobeMappingCells.face model D true k x = GlobeMappingCells.face model D false k y)
    (hyz : GlobeMappingCells.face model D true k y = GlobeMappingCells.face model D false k z)
    (hl : GlobeMappingCells.face model D true k (comp k x y hxy) =
      GlobeMappingCells.face model D false k z)
    (hr : GlobeMappingCells.face model D true k x =
      GlobeMappingCells.face model D false k (comp k y z hyz)) :
    comp k (comp k x y hxy) z hl = comp k x (comp k y z hyz) hr := by
  let cells : Fin 3 → Cell D := ![x, y, z]
  obtain ⟨n, hn, f, hf⟩ := GlobeMappingCells.exists_representatives_fin_above model D 3 cells (k+1)
  have hk : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn
  have h0 : GlobeMappingCells.ι model D n (f 0) = x := hf 0
  have h1 : GlobeMappingCells.ι model D n (f 1) = y := hf 1
  have h2 : GlobeMappingCells.ι model D n (f 2) = z := hf 2
  have hfg := GlobeMappingCells.matching_representatives model D x y hxy (f 0) (f 1) h0 h1
  have hgh := GlobeMappingCells.matching_representatives model D y z hyz (f 1) (f 2) h1 h2
  have hxy' : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n (f 0)) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n (f 1)) := by
    simpa only [h0, h1] using hxy
  have hyz' : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n (f 1)) =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n (f 2)) := by
    simpa only [h1, h2] using hyz
  have hl' : GlobeMappingCells.face model D true k
        (comp k (GlobeMappingCells.ι model D n (f 0)) (GlobeMappingCells.ι model D n (f 1)) hxy') =
      GlobeMappingCells.face model D false k (GlobeMappingCells.ι model D n (f 2)) := by
    simpa only [h0, h1, h2] using hl
  have hr' : GlobeMappingCells.face model D true k (GlobeMappingCells.ι model D n (f 0)) =
      GlobeMappingCells.face model D false k
        (comp k (GlobeMappingCells.ι model D n (f 1)) (GlobeMappingCells.ι model D n (f 2)) hyz') := by
    simpa only [h0, h1, h2] using hr
  simpa only [h0, h1, h2] using assoc_ι hk (f 0) (f 1) (f 2) hfg hgh hxy' hyz' hl' hr'

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # The actual strict right interval internal hom

Its cells are the finite-dimensional maps from the explicit globe
cylinders. All strict laws come from the proved finite parameter gluing.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

/-- The strict mapping category of the actual interval model. -/
def internalHomObj (D : StrictOmegaCategory.{0}) : StrictOmegaCategory.{0} where
  Cell := Cell D
  face := GlobeMappingCells.face model D
  globular := GlobeMappingCells.globular model D
  comp := comp
  source_comp := source_comp
  target_comp := target_comp
  face_comp := face_comp
  left_unit := left_unit
  right_unit := right_unit
  assoc := assoc
  interchange := interchange
  finite_dimension := GlobeMappingCells.finite_dimension model D

/-- Postcomposition as a strict functor on the actual mapping categories. -/
def internalHomMap {D E : StrictOmegaCategory.{0}} (u : D ⟶ E) :
    internalHomObj D ⟶ internalHomObj E where
  toFun := GlobeMappingCells.map model u
  map_face := GlobeMappingCells.map_face model u
  map_comp := by
    intro k x y h h'
    exact map_comp u k x y h h'

/-- The global right interval internal-hom functor. -/
def internalHom : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0} where
  obj := internalHomObj
  map := internalHomMap
  map_id D := by
    apply Hom.ext
    funext x
    exact GlobeMappingCells.map_id model x
  map_comp u v := by
    apply Hom.ext
    funext x
    exact GlobeMappingCells.map_comp model u v x

/-- Natural maps into the cylinder give strict evaluations; in particular
this constructs both interval endpoint evaluations. -/
def evaluation (η : 𝟭 StrictOmegaCategory.{0} ⟶ model) (D : StrictOmegaCategory.{0}) :
    internalHomObj D ⟶ D where
  toFun := GlobeMappingCells.naturalEvaluation η D
  map_face := GlobeMappingCells.naturalEvaluation_face η D
  map_comp := naturalEvaluation_comp η

/-- Evaluation is natural under postcomposition. -/
def evaluationNatTrans (η : 𝟭 StrictOmegaCategory.{0} ⟶ model) :
    internalHom ⟶ 𝟭 StrictOmegaCategory.{0} where
  app := evaluation η
  naturality D E u := by
    apply Hom.ext
    funext x
    exact GlobeMappingCells.naturalEvaluation_map η u x

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # The globe-level right-adjunction bijection

A strict map from a free globe into the constructed internal hom is
exactly a map out of its concrete chain cylinder. The bijection is natural
for every strict map of globes and for postcomposition in the target.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory

noncomputable section

/-- Representability on every free globe. -/
def globeHomEquiv (n : ℕ) (D : StrictOmegaCategory.{0}) :
    (model.obj (Globe.category n) ⟶ D) ≃ (Globe.category n ⟶ internalHomObj D) :=
  (GlobeMappingCells.boundedEquiv model D n).trans (Globe.homEquiv (internalHomObj D) n).symm

@[simp] theorem globeHomEquiv_top (n : ℕ) (D : StrictOmegaCategory.{0})
    (f : model.obj (Globe.category n) ⟶ D) :
    (globeHomEquiv n D f).toFun Globe.Cell.top = GlobeMappingCells.ι model D n f := rfl

@[simp] theorem globeHomEquiv_symm_top (n : ℕ) (D : StrictOmegaCategory.{0})
    (g : Globe.category n ⟶ internalHomObj D) :
    GlobeMappingCells.ι model D n ((globeHomEquiv n D).symm g) = g.toFun Globe.Cell.top :=
  congrArg (fun q : Globe.category n ⟶ internalHomObj D => q.toFun Globe.Cell.top)
    ((globeHomEquiv n D).apply_symm_apply g)

/-- Contravariant naturality includes arbitrary strict globe maps. -/
theorem globeHomEquiv_precomp {n m : ℕ} (D : StrictOmegaCategory.{0})
    (s : Globe.category n ⟶ Globe.category m) (f : model.obj (Globe.category m) ⟶ D) :
    globeHomEquiv n D (model.map s ≫ f) = s ≫ globeHomEquiv m D f := by
  apply Globe.hom_ext
  change GlobeMappingCells.ι model D n (model.map s ≫ f) =
    GlobeMappingCells.evaluateCell model D f (s.toFun Globe.Cell.top)
  exact GlobeMappingCells.globe_naturality model D s f

/-- Covariant naturality is the actual strict postcomposition map. -/
theorem globeHomEquiv_postcomp {n : ℕ} {D E : StrictOmegaCategory.{0}}
    (f : model.obj (Globe.category n) ⟶ D) (u : D ⟶ E) :
    globeHomEquiv n E (f ≫ u) = globeHomEquiv n D f ≫ internalHomMap u := by
  apply Globe.hom_ext
  exact (GlobeMappingCells.map_ι model u n f).symm

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # Natural representability on the actual finite parameters

Cellwise currying is defined on every strict source category. It is a
bijection on free globes and on the actual binary pastings. These natural
bijections are the parameter data for the global Kan-extension adjunction.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B C D E : StrictOmegaCategory.{0}}

/-- A concrete chain-model map gives a strict map into the actual internal hom. -/
def modelCurry (u : model.obj C ⟶ D) : C ⟶ internalHomObj D where
  toFun := cellCurry u
  map_face := cellCurry_face u
  map_comp := cellCurry_comp u

theorem modelCurry_precomp (s : B ⟶ C) (u : model.obj C ⟶ D) :
    modelCurry (model.map s ≫ u) = s ≫ modelCurry u := by
  apply Hom.ext
  funext x
  exact cellCurry_precomp s u x

theorem modelCurry_postcomp (u : model.obj C ⟶ D) (v : D ⟶ E) :
    modelCurry (u ≫ v) = modelCurry u ≫ internalHomMap v := by
  apply Hom.ext
  funext x
  exact cellCurry_postcomp u v x

theorem modelCurry_globe_eq {n : ℕ} (u : model.obj (Globe.category n) ⟶ D) :
    modelCurry u = globeHomEquiv n D u := by
  apply Globe.hom_ext
  have he := cellCurry_globe u (𝟙 (Globe.category n))
  change cellCurry u Globe.Cell.top =
    GlobeMappingCells.ι model D n (model.map (𝟙 (Globe.category n)) ≫ u) at he
  change cellCurry u Globe.Cell.top = GlobeMappingCells.ι model D n u
  simpa only [model.map_id, Category.id_comp] using he

theorem modelCurry_restrict {n : ℕ} (s : Globe.category n ⟶ C) (u : model.obj C ⟶ D) :
    s ≫ modelCurry u = globeHomEquiv n D (model.map s ≫ u) :=
  (modelCurry_precomp s u).symm.trans (modelCurry_globe_eq _)

theorem modelCurry_globe_bijective (n : ℕ) (D : StrictOmegaCategory.{0}) :
    Function.Bijective (modelCurry (C := Globe.category n) (D := D)) := by
  constructor
  · intro u v huv
    apply (globeHomEquiv n D).injective
    rw [← modelCurry_globe_eq, ← modelCurry_globe_eq]
    exact huv
  · intro q
    refine ⟨(globeHomEquiv n D).symm q, ?_⟩
    rw [modelCurry_globe_eq, Equiv.apply_symm_apply]

/-- Binary gluing upgrades the globe bijection to each composition parameter. -/
theorem modelCurry_pasting_bijective {n k : ℕ} (hk : k < n) (D : StrictOmegaCategory.{0}) :
    Function.Bijective (modelCurry (C := PastingGlobe.category n n k) (D := D)) := by
  constructor
  · intro u v huv
    apply (PastingGlobe.CylinderSource.isPushout hk).hom_ext
    · apply (globeHomEquiv n D).injective
      exact (modelCurry_restrict (PastingGlobe.left n n k) u).symm.trans
        ((congrArg (fun q => PastingGlobe.left n n k ≫ q) huv).trans
          (modelCurry_restrict (PastingGlobe.left n n k) v))
    · apply (globeHomEquiv n D).injective
      exact (modelCurry_restrict (PastingGlobe.right n n k) u).symm.trans
        ((congrArg (fun q => PastingGlobe.right n n k ≫ q) huv).trans
          (modelCurry_restrict (PastingGlobe.right n n k) v))
  · intro q
    let f := (globeHomEquiv n D).symm (PastingGlobe.left n n k ≫ q)
    let g := (globeHomEquiv n D).symm (PastingGlobe.right n n k ≫ q)
    have hf : globeHomEquiv n D f = PastingGlobe.left n n k ≫ q :=
      (globeHomEquiv n D).apply_symm_apply _
    have hg : globeHomEquiv n D g = PastingGlobe.right n n k ≫ q :=
      (globeHomEquiv n D).apply_symm_apply _
    have hm : model.map (Globe.faceMap true k n) ≫ f =
        model.map (Globe.faceMap false k n) ≫ g := by
      apply (globeHomEquiv k D).injective
      calc
        _ = Globe.faceMap true k n ≫ (PastingGlobe.left n n k ≫ q) :=
          (globeHomEquiv_precomp D _ f).trans
            (congrArg (fun r => Globe.faceMap true k n ≫ r) hf)
        _ = Globe.faceMap false k n ≫ (PastingGlobe.right n n k ≫ q) := by
          rw [← Category.assoc, ← Category.assoc, pushout.condition]
        _ = _ := ((globeHomEquiv_precomp D _ g).trans
          (congrArg (fun r => Globe.faceMap false k n ≫ r) hg)).symm
    refine ⟨glue hk f g hm, ?_⟩
    apply pushout.hom_ext
    · exact (modelCurry_restrict (PastingGlobe.left n n k) (glue hk f g hm)).trans
        ((congrArg (globeHomEquiv n D) (glue_left hk f g hm)).trans hf)
    · exact (modelCurry_restrict (PastingGlobe.right n n k) (glue hk f g hm)).trans
        ((congrArg (globeHomEquiv n D) (glue_right hk f g hm)).trans hg)

/-- The natural Hom bijection on every globe-and-pasting parameter. -/
def parameterCurryEquiv (i : GlobePasting.Shape) (D : StrictOmegaCategory.{0}) :
    (model.obj (GlobePasting.object i) ⟶ D) ≃
      (GlobePasting.object i ⟶ internalHomObj D) :=
  Equiv.ofBijective modelCurry (by
    cases i with
    | globe n => exact modelCurry_globe_bijective n D
    | pair n k hk => exact modelCurry_pasting_bijective hk D)

theorem parameterCurry_precomp {i j : GlobePasting.Shape}
    (s : GlobePasting.object i ⟶ GlobePasting.object j)
    (u : model.obj (GlobePasting.object j) ⟶ D) :
    parameterCurryEquiv i D (model.map s ≫ u) = s ≫ parameterCurryEquiv j D u :=
  modelCurry_precomp s u

theorem parameterCurry_postcomp (i : GlobePasting.Shape)
    (u : model.obj (GlobePasting.object i) ⟶ D) (v : D ⟶ E) :
    parameterCurryEquiv i E (u ≫ v) = parameterCurryEquiv i D u ≫ internalHomMap v :=
  modelCurry_postcomp u v

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # The actual right interval adjunction

The natural Hom bijections on the globe-and-pasting parameters extend
through the two proved colimit presentations. No global preservation by
chain realization is assumed.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayMapping

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable (C D : StrictOmegaCategory.{0})

def curryCocone (u : GrayChainExtension.cylinder.obj C ⟶ D) : Cocone (GlobePasting.diagram C) where
  pt := internalHomObj D
  ι := {
    app j := parameterCurryEquiv j.left D ((GrayChainExtension.presentationCocone C).ι.app j ≫ u)
    naturality i j f := by
      let s : GlobePasting.object i.left ⟶ GlobePasting.object j.left := f.left
      let li : model.obj (GlobePasting.object i.left) ⟶ GrayChainExtension.cylinder.obj C :=
        (GrayChainExtension.presentationCocone C).ι.app i
      let lj : model.obj (GlobePasting.object j.left) ⟶ GrayChainExtension.cylinder.obj C :=
        (GrayChainExtension.presentationCocone C).ι.app j
      have hw : model.map s ≫ lj = li :=
        (GrayChainExtension.presentationCocone C).w f
      change s ≫ parameterCurryEquiv j.left D (lj ≫ u) =
        parameterCurryEquiv i.left D (li ≫ u) ≫ 𝟙 _
      exact (parameterCurry_precomp s (lj ≫ u)).symm.trans
        ((congrArg (parameterCurryEquiv i.left D)
          ((Category.assoc (model.map s) lj u).symm.trans
            (congrArg (fun q => q ≫ u) hw))).trans (Category.comp_id _).symm) }

def curryHom (u : GrayChainExtension.cylinder.obj C ⟶ D) : C ⟶ internalHomObj D :=
  (GlobePasting.isColimit C).desc (curryCocone C D u)

theorem curryHom_fac (u : GrayChainExtension.cylinder.obj C ⟶ D)
    (j : CostructuredArrow GlobePasting.inclusion C) :
    j.hom ≫ curryHom C D u =
      parameterCurryEquiv j.left D ((GrayChainExtension.presentationCocone C).ι.app j ≫ u) :=
  (GlobePasting.isColimit C).fac (curryCocone C D u) j

def uncurryCocone (g : C ⟶ internalHomObj D) : Cocone (GrayChainExtension.presentationDiagram C) where
  pt := D
  ι := {
    app j := (parameterCurryEquiv j.left D).symm (j.hom ≫ g)
    naturality i j f := by
      let s : GlobePasting.object i.left ⟶ GlobePasting.object j.left := f.left
      let fi : GlobePasting.object i.left ⟶ C := i.hom
      let fj : GlobePasting.object j.left ⟶ C := j.hom
      have hw : s ≫ fj = fi := CostructuredArrow.w f
      change model.map s ≫ (parameterCurryEquiv j.left D).symm (fj ≫ g) =
        (parameterCurryEquiv i.left D).symm (fi ≫ g) ≫ 𝟙 _
      rw [Category.comp_id]
      apply (parameterCurryEquiv i.left D).injective
      exact (parameterCurry_precomp s _).trans
        ((congrArg (fun q => s ≫ q) ((parameterCurryEquiv j.left D).apply_symm_apply _)).trans
          (((Category.assoc s fj g).symm.trans (congrArg (fun q => q ≫ g) hw)).trans
            ((parameterCurryEquiv i.left D).apply_symm_apply _).symm)) }

def uncurryHom (g : C ⟶ internalHomObj D) : GrayChainExtension.cylinder.obj C ⟶ D :=
  (GrayChainExtension.presentationIsColimit C).desc (uncurryCocone C D g)

theorem uncurryHom_fac (g : C ⟶ internalHomObj D)
    (j : CostructuredArrow GlobePasting.inclusion C) :
    (GrayChainExtension.presentationCocone C).ι.app j ≫ uncurryHom C D g =
      (parameterCurryEquiv j.left D).symm (j.hom ≫ g) :=
  (GrayChainExtension.presentationIsColimit C).fac (uncurryCocone C D g) j

theorem uncurry_curry (u : GrayChainExtension.cylinder.obj C ⟶ D) :
    uncurryHom C D (curryHom C D u) = u := by
  apply (GrayChainExtension.presentationIsColimit C).hom_ext
  intro j
  exact (uncurryHom_fac C D (curryHom C D u) j).trans
    ((congrArg (parameterCurryEquiv j.left D).symm (curryHom_fac C D u j)).trans
      ((parameterCurryEquiv j.left D).symm_apply_apply _))

theorem curry_uncurry (g : C ⟶ internalHomObj D) :
    curryHom C D (uncurryHom C D g) = g := by
  apply (GlobePasting.isColimit C).hom_ext
  intro j
  change j.hom ≫ curryHom C D (uncurryHom C D g) = j.hom ≫ g
  exact (curryHom_fac C D (uncurryHom C D g) j).trans
    ((congrArg (parameterCurryEquiv j.left D) (uncurryHom_fac C D g j)).trans
      ((parameterCurryEquiv j.left D).apply_symm_apply _))

/-- The literal Hom bijection for the extended cylinder. -/
def homEquiv : (GrayChainExtension.cylinder.obj C ⟶ D) ≃ (C ⟶ internalHomObj D) where
  toFun := curryHom C D
  invFun := uncurryHom C D
  left_inv := uncurry_curry C D
  right_inv := curry_uncurry C D

variable {C D} {B E : StrictOmegaCategory.{0}}

theorem curryHom_postcomp (u : GrayChainExtension.cylinder.obj C ⟶ D) (v : D ⟶ E) :
    curryHom C E (u ≫ v) = curryHom C D u ≫ internalHomMap v := by
  apply (GlobePasting.isColimit C).hom_ext
  intro j
  change j.hom ≫ curryHom C E (u ≫ v) = j.hom ≫ (curryHom C D u ≫ internalHomMap v)
  let l : model.obj (GlobePasting.object j.left) ⟶ GrayChainExtension.cylinder.obj C :=
    (GrayChainExtension.presentationCocone C).ι.app j
  let fj : GlobePasting.object j.left ⟶ C := j.hom
  exact (curryHom_fac C E (u ≫ v) j).trans
    ((congrArg (parameterCurryEquiv j.left E) (Category.assoc l u v).symm).trans
      ((parameterCurry_postcomp j.left (l ≫ u) v).trans
        ((congrArg (fun q : GlobePasting.object j.left ⟶ internalHomObj D => q ≫ internalHomMap v)
          (curryHom_fac C D u j).symm).trans (Category.assoc fj _ _))))

theorem uncurryHom_precomp (f : B ⟶ C) (g : C ⟶ internalHomObj D) :
    GrayChainExtension.cylinder.map f ≫ uncurryHom C D g = uncurryHom B D (f ≫ g) := by
  apply (GrayChainExtension.presentationIsColimit B).hom_ext
  intro j
  let j' : CostructuredArrow GlobePasting.inclusion C :=
    CostructuredArrow.mk (Y := j.left) (j.hom ≫ f)
  let lB : model.obj (GlobePasting.object j.left) ⟶ GrayChainExtension.cylinder.obj B :=
    (GrayChainExtension.presentationCocone B).ι.app j
  let lC : model.obj (GlobePasting.object j.left) ⟶ GrayChainExtension.cylinder.obj C :=
    (GrayChainExtension.presentationCocone C).ι.app j'
  let fj : GlobePasting.object j.left ⟶ B := j.hom
  have hl : lB ≫ GrayChainExtension.cylinder.map f = lC :=
    GrayChainExtension.presentation_leg_map f j
  exact (Category.assoc lB (GrayChainExtension.cylinder.map f) (uncurryHom C D g)).symm.trans
    ((congrArg (fun q => q ≫ uncurryHom C D g) hl).trans
      ((uncurryHom_fac C D g j').trans
        ((congrArg (parameterCurryEquiv j.left D).symm (Category.assoc fj f g)).trans
          (uncurryHom_fac B D (f ≫ g) j).symm)))

/-- The actual global right interval internal-hom adjunction. -/
def adjunction : GrayChainExtension.cylinder ⊣ internalHom :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := fun f g => (uncurryHom_precomp f g).symm
    homEquiv_naturality_right := fun u v => curryHom_postcomp u v }

end
end Thomason.Construction.StrictOmegaCategory.GrayMapping

end

section

/-! # The right Gray interval and its ordered simplex comparison

The global adjunction and the ordered simplex-cylinder comparison have
compatible endpoints and collapse maps. Restriction of this cylinder to
free globes proves preservation of finite truncations by its right adjoint.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex StrictOmegaCategory

noncomputable section

variable (h : NormalizedSimplexIdentities)

def extendedSimplexModelIso (m : SimplexCategory) :
    GrayChainExtension.cylinder.obj (h.object m.len) ≅
      GrayChainExtension.model.obj (h.object m.len) :=
  GrayChainExtension.simplexCylinderIso h m.len ≪≫ h.constructedChainModelComparison.app m

/-- The ordered-cell isomorphism is the canonical global comparison. -/
theorem extendedSimplexModelIso_hom (m : SimplexCategory) :
    (h.extendedSimplexModelIso m).hom = GrayChainExtension.comparison.app (h.object m.len) := by
  let a := simplexAtoms h
  let e := a.abelianizationIso m.len
  let T := rightCylinderFunctor ⋙ realizationFunctor
  let c := GrayChainExtension.comparison.app (h.object m.len)
  have he : T.map e.hom ≫ T.map e.inv = 𝟙 _ :=
    (T.map_comp e.hom e.inv).symm.trans
      ((congrArg T.map e.hom_inv_id).trans (T.map_id _))
  change (c ≫ T.map e.hom) ≫ T.map e.inv = c
  exact (Category.assoc c _ _).trans
    ((congrArg (fun q => c ≫ q) he).trans (Category.comp_id c))

/-- Naturality is inherited from the actual global comparison. -/
def extendedSimplexModelNatIso :
    h.cosimplicial ⋙ GrayChainExtension.cylinder ≅
      h.cosimplicial ⋙ GrayChainExtension.model :=
  NatIso.ofComponents (h.extendedSimplexModelIso) (by
    intro m n f
    change GrayChainExtension.cylinder.map (h.cosimplicial.map f) ≫
        (h.extendedSimplexModelIso n).hom =
      (h.extendedSimplexModelIso m).hom ≫ GrayChainExtension.model.map (h.cosimplicial.map f)
    rw [h.extendedSimplexModelIso_hom, h.extendedSimplexModelIso_hom]
    exact GrayChainExtension.comparison.naturality (h.cosimplicial.map f))

/-- The explicit right chain simplex cylinder identifies with the global
extended interval tensor, naturally in every simplex operator. -/
def constructedRightSimplexComparison :
    h.cylinderCosimplicial ≅ h.cosimplicial ⋙ GrayChainExtension.cylinder :=
  h.constructedChainModelComparison ≪≫ h.extendedSimplexModelNatIso.symm

theorem constructedRightSimplexComparison_comp (m : SimplexCategory) :
    h.constructedRightSimplexComparison.hom.app m ≫
        GrayChainExtension.comparison.app (h.object m.len) =
      h.constructedChainModelComparison.hom.app m := by
  rw [← h.extendedSimplexModelIso_hom m]
  let f : h.cylinderObject m.len ⟶ GrayChainExtension.model.obj (h.object m.len) :=
    h.constructedChainModelComparison.hom.app m
  let e := h.extendedSimplexModelIso m
  change (f ≫ e.inv) ≫ e.hom = f
  exact (Category.assoc f e.inv e.hom).trans
    ((congrArg (fun q => f ≫ q) e.inv_hom_id).trans (Category.comp_id f))

theorem constructedRightSimplexComparison_endpoint (side : Bool) (m : SimplexCategory) :
    (h.cylinderEndpoint side).app m ≫ h.constructedRightSimplexComparison.hom.app m =
      (GrayChainExtension.endpoint side).app (h.object m.len) := by
  apply (cancel_mono (h.extendedSimplexModelIso m).hom).mp
  rw [h.extendedSimplexModelIso_hom]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (h.cylinderEndpoint side).app m ≫ q)
      (h.constructedRightSimplexComparison_comp m)).trans
        ((h.constructedChainModelComparison_endpoint side m).trans
          (congrArg (fun q => q.app (h.object m.len))
            (GrayChainExtension.endpoint_comparison side)).symm))

theorem constructedRightSimplexComparison_projection (m : SimplexCategory) :
    h.constructedRightSimplexComparison.hom.app m ≫
        GrayChainExtension.projection.app (h.object m.len) = h.cylinderProjection.app m :=
  h.extendedComparison_projection m _ (h.constructedRightSimplexComparison_comp m)

/-- The right interval adjunction with its natural ordered simplex comparison. -/
def constructedRightGrayInput : RightGrayInput h where
  cylinder := GrayChainExtension.cylinder
  internalHom := GrayMapping.internalHom
  adjunction := GrayMapping.adjunction
  endpoint := GrayChainExtension.endpoint
  projection := GrayChainExtension.projection
  endpoint_projection := GrayChainExtension.endpoint_projection
  simplexComparison := h.constructedRightSimplexComparison
  endpoint_comparison := h.constructedRightSimplexComparison_endpoint
  projection_comparison := h.constructedRightSimplexComparison_projection

/-- The same constructed internal hom preserves each finite truncation. -/
theorem constructedRightGrayTruncation : GrayTruncationInput h.constructedRightGrayInput :=
  GrayChainExtension.truncationInput h.constructedRightGrayInput (Iso.refl _)

end
end Thomason.Construction.NormalizedSimplexIdentities

end

end OAI
