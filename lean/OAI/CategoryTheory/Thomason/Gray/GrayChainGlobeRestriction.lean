import OAI.CategoryTheory.Thomason.Gray.CylinderAssembly
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.GlobePastingDensity
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeChains
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderAtoms
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderRetractions
import OAI.CategoryTheory.Thomason.Gray.StrictAbelianization
import OAI.CategoryTheory.Thomason.Transfer.StrictPushoutGeneration

namespace OAI

section

/-! # Exact intersection of the realized cylinder pieces

The two globe pieces have retractions which collapse the opposite piece
to the common face. These identities make their intersection square a
pullback after every functor, in particular after the concrete right-chain
cylinder and realization. Generation of the full realized cylinder is a
separate question.
-/

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe

open CategoryTheory CategoryTheory.Limits

noncomputable section

private theorem pullback_of_piece_retractions
    {D : Type*} [Category D] {A B C P : D}
    (f : A ⟶ B) (g : A ⟶ C) (l : B ⟶ P) (r : C ⟶ P)
    (cB : B ⟶ A) (cC : C ⟶ A) (p : P ⟶ B) (q : P ⟶ C)
    (hw : f ≫ l = g ≫ r) (hl : l ≫ p = 𝟙 B) (hr : r ≫ q = 𝟙 C)
    (hcrossL : r ≫ p = cC ≫ f) (hcrossR : l ≫ q = cB ≫ g)
    (hB : f ≫ cB = 𝟙 A) (hC : g ≫ cC = 𝟙 A) : IsPullback f g l r := by
  have right_lift (s : PullbackCone l r) : (s.fst ≫ cB) ≫ g = s.snd := by
    have h := congrArg (fun u => u ≫ q) s.condition
    simpa only [Category.assoc, hcrossR, hr, Category.comp_id] using h
  refine IsPullback.of_isLimit (c := PullbackCone.mk f g hw) ?_
  refine PullbackCone.IsLimit.mk hw (fun s => s.fst ≫ cB) ?_ right_lift ?_
  · intro s
    have h := congrArg (fun u => u ≫ p) s.condition
    have hu : s.fst = s.snd ≫ cC ≫ f := by
      simpa only [Category.assoc, hl, hcrossL, Category.comp_id] using h
    calc
      (s.fst ≫ cB) ≫ f = ((s.fst ≫ cB) ≫ g) ≫ cC ≫ f := by
        simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
          congrArg (fun v => (s.fst ≫ cB) ≫ v ≫ f) hC.symm
      _ = s.snd ≫ cC ≫ f := by rw [right_lift]
      _ = s.fst := hu.symm
  · intro s m hm _
    calc
      m = (m ≫ f) ≫ cB := by rw [Category.assoc, hB, Category.comp_id]
      _ = s.fst ≫ cB := congrArg (· ≫ cB) hm

/-- The common-face square is an absolute pullback, by its explicit
piece retractions. This theorem does not assert preservation of a colimit. -/
theorem functor_commonFace_isPullback
    {D : Type*} [Category D] (F : StrictOmegaCategory.{0} ⥤ D)
    (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    IsPullback (F.map (Globe.faceMap true k n)) (F.map (Globe.faceMap false k m))
      (F.map (left n m k)) (F.map (right n m k)) := by
  apply pullback_of_piece_retractions
    (F.map (Globe.faceMap true k n)) (F.map (Globe.faceMap false k m))
    (F.map (left n m k)) (F.map (right n m k))
    (F.map (collapseTo n k hkn)) (F.map (collapseTo m k hkm))
    (F.map (retractLeft n m k hkm)) (F.map (retractRight n m k hkn))
  · simpa only [Functor.map_comp] using congrArg F.map
      (pushout.condition (f := Globe.faceMap true k n) (g := Globe.faceMap false k m))
  · rw [← F.map_comp, left_retractLeft, F.map_id]
  · rw [← F.map_comp, right_retractRight, F.map_id]
  · rw [← F.map_comp, right_retractLeft, F.map_comp]
  · rw [← F.map_comp, left_retractRight, F.map_comp]
  · rw [← F.map_comp, collapseTo_face, F.map_id]
  · rw [← F.map_comp, collapseTo_face, F.map_id]

/-- In the actual realized chain cylinder, the two globe pieces intersect
in exactly their common realized face-cylinder. -/
theorem model_commonFace_isPullback (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    IsPullback (GrayChainExtension.model.map (Globe.faceMap true k n))
      (GrayChainExtension.model.map (Globe.faceMap false k m))
      (GrayChainExtension.model.map (left n m k))
      (GrayChainExtension.model.map (right n m k)) :=
  functor_commonFace_isPullback GrayChainExtension.model n m k hkn hkm

end

end Thomason.Construction.StrictOmegaCategory.PastingGlobe

end

section

/-! # The source of the pasted-globe cylinder comparison

This is the actual strict pushout of the two globe cylinders. Its canonical
map lands in the chain-model cylinder of the pasted globes. Retractions of
the two original pieces control equality of all original piece cells.
-/

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

open CategoryTheory CategoryTheory.Limits _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

abbrev model := GrayChainExtension.model

abbrev source (n k : ℕ) : StrictOmegaCategory.{0} :=
  pushout (model.map (Globe.faceMap true k n)) (model.map (Globe.faceMap false k n))

def piece (n k : ℕ) (s : Bool) : model.obj (Globe.category n) ⟶ source n k :=
  if s then pushout.inr _ _ else pushout.inl _ _

def targetPiece (n k : ℕ) (s : Bool) :
    model.obj (Globe.category n) ⟶ model.obj (PastingGlobe.category n n k) :=
  model.map (if s then PastingGlobe.right n n k else PastingGlobe.left n n k)

def comparison (n k : ℕ) : source n k ⟶ model.obj (PastingGlobe.category n n k) :=
  pushout.desc (model.map (PastingGlobe.left n n k)) (model.map (PastingGlobe.right n n k))
    (by rw [← model.map_comp, ← model.map_comp, pushout.condition])

theorem piece_comparison (n k : ℕ) (s : Bool) :
    piece n k s ≫ comparison n k = targetPiece n k s := by
  cases s
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

def globeIso (n : ℕ) : model.obj (Globe.category n) ≅
    (rightCylinder (DirectedGlobeComplex.complex n)).realization :=
  (rightCylinderFunctor ⋙ realizationFunctor).mapIso (DirectedGlobeComplex.abelianizationIso n)

def basisComparison {n k : ℕ} (hkn : k < n) :
    source n k ⟶ (PastingGlobeCylinderBasis.Cylinder hkn).realization :=
  comparison n k ≫ (PastingGlobeCylinderBasis.modelIso hkn).hom

theorem piece_basisComparison {n k : ℕ} (hkn : k < n) (s : Bool) :
    piece n k s ≫ basisComparison hkn =
      (globeIso n).hom ≫ PastingGlobeCylinderBasis.sideMap hkn s := by
  rw [basisComparison, ← Category.assoc, piece_comparison]
  exact PastingGlobeCylinderBasis.model_piece hkn s

private theorem map_retract (n k : ℕ) (hkn : k ≤ n) (s : Bool) :
    targetPiece n k s ≫ model.map
      (if s then PastingGlobe.retractRight n n k hkn else PastingGlobe.retractLeft n n k hkn) =
      𝟙 _ := by
  cases s
  · exact model_left_retractLeft n n k hkn
  · exact model_right_retractRight n n k hkn

/-- Cells from one original piece are distinguished by the comparison. -/
theorem same_piece_injective (n k : ℕ) (hkn : k ≤ n) (s : Bool)
    (x y : model.obj (Globe.category n))
    (he : (targetPiece n k s).toFun x = (targetPiece n k s).toFun y) : x = y := by
  have hh := congrArg (model.map
    (if s then PastingGlobe.retractRight n n k hkn else PastingGlobe.retractLeft n n k hkn)).toFun he
  have hr := congrArg (fun f : model.obj (Globe.category n) ⟶ model.obj (Globe.category n) =>
    f.toFun) (map_retract n k hkn s)
  exact (congrFun hr x).symm.trans (hh.trans (congrFun hr y))

/-- Equality of a left and a right original piece cell is already forced
by the common-face relation in the source pushout. -/
theorem cross_piece_eq (n k : ℕ) (hkn : k ≤ n)
    (x y : model.obj (Globe.category n))
    (he : (targetPiece n k false).toFun x = (targetPiece n k true).toFun y) :
    (piece n k false).toFun x = (piece n k true).toFun y := by
  let z := (model.map (PastingGlobe.collapseTo n k hkn)).toFun y
  have hx : x = (model.map (Globe.faceMap true k n)).toFun z := by
    have hh := congrArg (model.map (PastingGlobe.retractLeft n n k hkn)).toFun he
    have hl := congrArg (fun f => f.toFun x) (model_left_retractLeft n n k hkn)
    have hr := congrArg (fun f => f.toFun y)
      (show targetPiece n k true ≫ model.map (PastingGlobe.retractLeft n n k hkn) =
        model.map (PastingGlobe.collapseTo n k hkn) ≫ model.map (Globe.faceMap true k n) by
        exact (model.map_comp _ _).symm.trans
          ((congrArg model.map (PastingGlobe.right_retractLeft n n k hkn)).trans
            (model.map_comp _ _)))
    exact hl.symm.trans (hh.trans hr)
  have hc : (model.map (PastingGlobe.collapseTo n k hkn)).toFun x = z := by
    rw [hx]
    have hh := congrArg (fun f => f.toFun z)
      (show model.map (Globe.faceMap true k n) ≫ model.map (PastingGlobe.collapseTo n k hkn) =
        𝟙 _ by rw [← model.map_comp, PastingGlobe.collapseTo_face, model.map_id])
    exact hh
  have hy : (model.map (Globe.faceMap false k n)).toFun z = y := by
    have hh := congrArg (model.map (PastingGlobe.retractRight n n k hkn)).toFun he
    have hl := congrArg (fun f => f.toFun x)
      (show targetPiece n k false ≫ model.map (PastingGlobe.retractRight n n k hkn) =
        model.map (PastingGlobe.collapseTo n k hkn) ≫ model.map (Globe.faceMap false k n) by
        exact (model.map_comp _ _).symm.trans
          ((congrArg model.map (PastingGlobe.left_retractRight n n k hkn)).trans
            (model.map_comp _ _)))
    have hr := congrArg (fun f => f.toFun y) (model_right_retractRight n n k hkn)
    exact (congrArg (model.map (Globe.faceMap false k n)).toFun hc).symm.trans
      (hl.symm.trans (hh.trans hr))
  rw [hx, ← hy]
  exact congrArg (fun f : model.obj (Globe.category k) ⟶ source n k => f.toFun z)
    (pushout.condition (f := model.map (Globe.faceMap true k n))
      (g := model.map (Globe.faceMap false k n)))

theorem piece_eq_of_comparison (n k : ℕ) (hkn : k ≤ n) (s t : Bool)
    (x y : model.obj (Globe.category n))
    (he : (targetPiece n k s).toFun x = (targetPiece n k t).toFun y) :
    (piece n k s).toFun x = (piece n k t).toFun y := by
  cases s <;> cases t
  · exact congrArg (piece n k false).toFun (same_piece_injective n k hkn false x y he)
  · exact cross_piece_eq n k hkn x y he
  · exact (cross_piece_eq n k hkn y x he.symm).symm
  · exact congrArg (piece n k true).toFun (same_piece_injective n k hkn true x y he)

end
end Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

end

section

/-! # Bounded atoms in the actual source pushout

Each canonical pasted-cylinder atom is represented in one of the two
globe cylinders. Its image and dimension bound are literal consequences
of the endpoint and prism constructions.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

theorem atom_in_side_bounded {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    ∃ (s : Bool) (x : Cell (rightCylinder (DirectedGlobeComplex.complex n))),
      (rightCylinder (DirectedGlobeComplex.complex n)).realization.DimensionLE p x ∧
      (sideMap hkn s).toFun x = atom hkn b := by
  cases b with
  | endpoint a b =>
    refine ⟨b.val.1, Cell.map (RightCylinder.endpoint _ a)
      ((DirectedGlobeComplex.topCell n).face b.val.2 p), ?_, ?_⟩
    · exact (RightCylinder.endpoint _ a).realization.dimensionLE
        ((DirectedGlobeComplex.complex n).realization.face_dimensionLE b.val.2 p _)
    · apply Cell.ext
      funext c q
      exact RightCylinder.map_endpoint (PastingGlobeBasis.inclusion hkn b.val.1) a q
        (((DirectedGlobeComplex.topCell n).face b.val.2 p).table c q)
  | @mixed r b =>
    refine ⟨b.val.1, RightCylinder.prism
      ((DirectedGlobeComplex.topCell n).face b.val.2 r), ?_, ?_⟩
    · exact RightCylinder.prism_dimension _
        ((DirectedGlobeComplex.complex n).realization.face_dimensionLE b.val.2 r _)
    · exact RightCylinder.prism_naturality (PastingGlobeBasis.inclusion hkn b.val.1) _

end Thomason.Construction.PastingGlobeCylinderBasis

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

abbrev atomBasis {n k : ℕ} (hkn : k < n) := PastingGlobeCylinderBasis.orderedAtomBasis hkn

def representativeSide {n k p : ℕ} (hkn : k < n) (b : PastingGlobeCylinderBasis.Basis n k p) : Bool :=
  Classical.choose (PastingGlobeCylinderBasis.atom_in_side_bounded hkn b)

def representativeCell {n k p : ℕ} (hkn : k < n) (b : PastingGlobeCylinderBasis.Basis n k p) :
    DirectedComplex.Cell (rightCylinder (DirectedGlobeComplex.complex n)) :=
  Classical.choose (Classical.choose_spec (PastingGlobeCylinderBasis.atom_in_side_bounded hkn b))

theorem representative_spec {n k p : ℕ} (hkn : k < n) (b : PastingGlobeCylinderBasis.Basis n k p) :
    (rightCylinder (DirectedGlobeComplex.complex n)).realization.DimensionLE p
      (representativeCell hkn b) ∧
    (PastingGlobeCylinderBasis.sideMap hkn (representativeSide hkn b)).toFun
      (representativeCell hkn b) = PastingGlobeCylinderBasis.atom hkn b :=
  Classical.choose_spec (Classical.choose_spec (PastingGlobeCylinderBasis.atom_in_side_bounded hkn b))

/-- The chosen atom lift lies in an original globe-cylinder piece. -/
def atomLift {n k : ℕ} (hkn : k < n) (a : (atomBasis hkn).AtomIndex) : source n k :=
  (piece n k (representativeSide hkn a.2)).toFun
    ((globeIso n).inv.toFun (representativeCell hkn a.2))

theorem atomLift_dimension {n k : ℕ} (hkn : k < n) (a : (atomBasis hkn).AtomIndex) :
    (source n k).DimensionLE a.1 (atomLift hkn a) :=
  (piece n k (representativeSide hkn a.2)).dimensionLE
    ((globeIso n).inv.dimensionLE (representative_spec hkn a.2).1)

theorem atomLift_image {n k : ℕ} (hkn : k < n) (a : (atomBasis hkn).AtomIndex) :
    (basisComparison hkn).toFun (atomLift hkn a) = (atomBasis hkn).atomCell a := by
  have he := congrArg (fun f => f.toFun ((globeIso n).inv.toFun (representativeCell hkn a.2)))
    (piece_basisComparison hkn (representativeSide hkn a.2))
  have hi : (globeIso n).hom.toFun ((globeIso n).inv.toFun (representativeCell hkn a.2)) =
      representativeCell hkn a.2 := by
    exact congrArg (fun f => f.toFun (representativeCell hkn a.2)) (globeIso n).inv_hom_id
  exact he.trans ((congrArg (PastingGlobeCylinderBasis.sideMap hkn
    (representativeSide hkn a.2)).toFun hi).trans (representative_spec hkn a.2).2)

end
end Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

end

section

/-! # Images of the atoms in each cylinder piece

Canonical representatives may move a shared right face to the left piece.
All lower faces move with it, so the actual cell, not just its top chain,
agrees with the chosen pasted-cylinder atom.
-/

namespace Thomason.Construction.PastingGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

theorem embed_lower {n k p q : ℕ} (hkn : k < n) (s : Bool)
    (b : DirectedGlobeComplex.Basis n p) (c : DirectedGlobeComplex.Basis n q)
    (hqp : q < p) : embed hkn s c = embed hkn (embed hkn s b).val.1 c := by
  cases s
  · rfl
  · by_cases hp : p < k
    · simp [embed, right, hp, show q < k by omega, left]
    · by_cases he : p = k
      · by_cases hb : b.val = false
        · simp [embed, right, he, hb, show q < k by omega, left]
        · simp [embed, right, he, hb]
      · simp [embed, right, hp, he]

theorem inclusion_basisAtom {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : DirectedGlobeComplex.Basis n p) :
    (inclusion hkn s).realization.toFun (DirectedGlobeComplex.basisAtom n p b) =
      atom hkn (embed hkn s b) := by
  apply Cell.ext
  funext side q
  change embedApp hkn s q ((DirectedGlobeComplex.basisAtom n p b).table side q) = _
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · rw [DirectedGlobeComplex.basisAtom_below n p b q hqp side,
      embedApp_single, atom_below hkn (embed hkn s b) hqp side]
    congr 1
    exact embed_lower hkn s b _ hqp
  · rw [DirectedGlobeComplex.basisAtom_top, embedApp_single, atom_top]
  · rw [DirectedGlobeComplex.basisAtom_above n p b q hpq side]
    change embedApp hkn s q (0 : DirectedGlobeComplex.Chains n q) = _
    rw [map_zero, atom_above hkn (embed hkn s b) hpq side]
    rfl

end Thomason.Construction.PastingGlobeBasis

namespace Thomason.Construction.PastingGlobeCylinderBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

def pieceBasisMap {n k : ℕ} (hkn : k < n) (s : Bool) :
    {p : ℕ} → (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p → Basis n k p
  | _, .endpoint a b => .endpoint a (PastingGlobeBasis.embed hkn s b)
  | _, .mixed b => .mixed (PastingGlobeBasis.embed hkn s b)

theorem sideMap_atom {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p) :
    (sideMap hkn s).toFun ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b) =
      atom hkn (pieceBasisMap hkn s b) := by
  cases b with
  | endpoint a b =>
    have he : Cell.map (RightCylinder.map (PastingGlobeBasis.inclusion hkn s))
        (Cell.map (RightCylinder.endpoint _ a) (DirectedGlobeComplex.basisAtom n p b)) =
        Cell.map (RightCylinder.endpoint _ a)
          (Cell.map (PastingGlobeBasis.inclusion hkn s) (DirectedGlobeComplex.basisAtom n p b)) := by
      apply Cell.ext
      funext c q
      exact RightCylinder.map_endpoint (PastingGlobeBasis.inclusion hkn s) a q _
    exact he.trans (congrArg (Cell.map (RightCylinder.endpoint _ a))
      (PastingGlobeBasis.inclusion_basisAtom hkn s b))
  | @mixed r b =>
    exact (RightCylinder.prism_naturality (PastingGlobeBasis.inclusion hkn s)
      (DirectedGlobeComplex.basisAtom n r b)).trans
      (congrArg RightCylinder.prism (PastingGlobeBasis.inclusion_basisAtom hkn s b))

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # Every grid-cylinder atom comes from one of the two rows -/

namespace Thomason.Construction.GridGlobeBasis

open _root_.OAI.Thomason.Construction.DirectedComplex CategoryTheory

noncomputable section

theorem embed_lower {n k l p q : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (b : PastingGlobeBasis.Basis n k p) (a : Bool) (hqp : q < p) :
    embed hkl hln s (PastingGlobeBasis.embed (hkl.trans hln) b.val.1
      ⟨a, Or.inl (hqp.trans_le (PastingGlobeBasis.degree_le b))⟩) =
    embed hkl hln (embed hkl hln s b).val.1
      (PastingGlobeBasis.embed (hkl.trans hln) (embed hkl hln s b).val.2.val.1
        ⟨a, Or.inl (hqp.trans_le (PastingGlobeBasis.degree_le b))⟩) := by
  cases s with
  | false => rfl
  | true =>
    by_cases hp : p < l
    · simp [embed, hp, show q < l by omega, left]
    · by_cases he : p = l
      · by_cases hb : b.val.2 = false
        all_goals simp [embed, he, hb, show q < l by omega, targetBasis, left]
      · simp [embed, hp, he]

theorem inclusion_atom {n k l p : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (b : PastingGlobeBasis.Basis n k p) :
    (inclusion hkl hln s).realization.toFun (PastingGlobeBasis.atom (hkl.trans hln) b) =
      atom hkl hln (embed hkl hln s b) := by
  apply Cell.ext
  funext a q
  change embedApp hkl hln s q ((PastingGlobeBasis.atom (hkl.trans hln) b).table a q) = _
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · rw [PastingGlobeBasis.atom_below _ _ hqp a, embedApp_single,
      atom_below hkl hln (embed hkl hln s b) hqp a]
    congr 1
    exact embed_lower hkl hln s b a hqp
  · rw [PastingGlobeBasis.atom_top, embedApp_single, atom_top]
  · rw [PastingGlobeBasis.atom_above _ _ hpq a]
    change embedApp hkl hln s q (0 : PastingGlobeBasis.Chains n k q) = _
    rw [map_zero, atom_above hkl hln (embed hkl hln s b) hpq a]
    rfl

def rowCylinderIndex {n k l : ℕ} (hkl : k < l) (hln : l < n) (s : Bool) :
    {p : ℕ} → PastingGlobeCylinderBasis.Basis n k p →
      (cylinderOrderedAtomBasis hkl hln).Index p
  | _, .endpoint a b => .endpoint a (embed hkl hln s b)
  | _, .mixed b => .mixed (embed hkl hln s b)

theorem rowCylinder_atom {n k l p : ℕ} (hkl : k < l) (hln : l < n) (s : Bool)
    (b : PastingGlobeCylinderBasis.Basis n k p) :
    (RightCylinder.map (inclusion hkl hln s)).realization.toFun
      (PastingGlobeCylinderBasis.atom (hkl.trans hln) b) =
      (cylinderOrderedAtomBasis hkl hln).atom p (rowCylinderIndex hkl hln s b) := by
  cases b with
  | endpoint a b =>
    have he : Cell.map (RightCylinder.map (inclusion hkl hln s))
        (Cell.map (RightCylinder.endpoint _ a) (PastingGlobeBasis.atom (hkl.trans hln) b)) =
        Cell.map (RightCylinder.endpoint _ a)
          (Cell.map (inclusion hkl hln s) (PastingGlobeBasis.atom (hkl.trans hln) b)) := by
      apply Cell.ext
      funext c q
      exact RightCylinder.map_endpoint (inclusion hkl hln s) a q _
    exact he.trans (congrArg (Cell.map (RightCylinder.endpoint _ a))
      (inclusion_atom hkl hln s b))
  | @mixed r b =>
    exact (RightCylinder.prism_naturality (inclusion hkl hln s)
      (PastingGlobeBasis.atom (hkl.trans hln) b)).trans
      (congrArg RightCylinder.prism (inclusion_atom hkl hln s b))

theorem cylinderAtom_in_row {n k l : ℕ} (hkl : k < l) (hln : l < n)
    (a : (cylinderOrderedAtomBasis hkl hln).AtomIndex) :
    ∃ (s : Bool) (b : PastingGlobeCylinderBasis.Basis n k a.1),
      (RightCylinder.map (inclusion hkl hln s)).realization.toFun
        (PastingGlobeCylinderBasis.atom (hkl.trans hln) b) =
          (cylinderOrderedAtomBasis hkl hln).atomCell a := by
  rcases a with ⟨p, a⟩
  cases a with
  | endpoint t b =>
    refine ⟨b.val.1, .endpoint t b.val.2, ?_⟩
    have hi : rowCylinderIndex hkl hln b.val.1 (.endpoint t b.val.2) =
        .endpoint t b := congrArg (fun c : Basis n k l p =>
          (RightCylinderBasis.Basis.endpoint t c : (cylinderOrderedAtomBasis hkl hln).Index p))
            (embed_self hkl hln b)
    exact (rowCylinder_atom hkl hln b.val.1 (.endpoint t b.val.2)).trans
      (congrArg ((cylinderOrderedAtomBasis hkl hln).atom p) hi)
  | @mixed r b =>
    refine ⟨b.val.1, .mixed b.val.2, ?_⟩
    have hi : rowCylinderIndex hkl hln b.val.1 (.mixed b.val.2) =
        .mixed b := congrArg (fun c : Basis n k l r =>
          (RightCylinderBasis.Basis.mixed c : (cylinderOrderedAtomBasis hkl hln).Index (r+1)))
            (embed_self hkl hln b)
    exact (rowCylinder_atom hkl hln b.val.1 (.mixed b.val.2)).trans
      (congrArg ((cylinderOrderedAtomBasis hkl hln).atom (r+1)) hi)

end
end Thomason.Construction.GridGlobeBasis

end

section

/-! # Generation of the pasted-cylinder source by its chosen atom lifts

The equalities of original piece cells identify every piece atom with its
canonical lift. Generation of the two globe cylinders and then of their
strict pushout gives the required ordinary composition generation.
-/

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

open CategoryTheory CategoryTheory.Limits _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

theorem piece_eq_of_basisComparison {n k : ℕ} (hkn : k < n) (s t : Bool)
    (x y : model.obj (Globe.category n))
    (he : (basisComparison hkn).toFun ((piece n k s).toFun x) =
      (basisComparison hkn).toFun ((piece n k t).toFun y)) :
    (piece n k s).toFun x = (piece n k t).toFun y := by
  apply piece_eq_of_comparison n k hkn.le s t x y
  let e := PastingGlobeCylinderBasis.modelIso hkn
  have he' : e.hom.toFun ((comparison n k).toFun ((piece n k s).toFun x)) =
      e.hom.toFun ((comparison n k).toFun ((piece n k t).toFun y)) := he
  have hi (z : model.obj (PastingGlobe.category n n k)) : e.inv.toFun (e.hom.toFun z) = z :=
    congrArg (fun f => f.toFun z) e.hom_inv_id
  have hc := (hi _).symm.trans ((congrArg e.inv.toFun he').trans (hi _))
  have hl := congrArg (fun f => f.toFun x) (piece_comparison n k s)
  have hr := congrArg (fun f => f.toFun y) (piece_comparison n k t)
  exact hl.symm.trans (hc.trans hr)

private theorem piece_atom_image {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p) :
    (basisComparison hkn).toFun ((piece n k s).toFun ((globeIso n).inv.toFun
      ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b))) =
      PastingGlobeCylinderBasis.atom hkn (PastingGlobeCylinderBasis.pieceBasisMap hkn s b) := by
  let x := (DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b
  have he := congrArg (fun f => f.toFun ((globeIso n).inv.toFun x))
    (piece_basisComparison hkn s)
  have hi : (globeIso n).hom.toFun ((globeIso n).inv.toFun x) = x :=
    congrArg (fun f => f.toFun x) (globeIso n).inv_hom_id
  exact he.trans ((congrArg (PastingGlobeCylinderBasis.sideMap hkn s).toFun hi).trans
    (PastingGlobeCylinderBasis.sideMap_atom hkn s b))

/-- Every original piece atom is the corresponding canonical atom lift. -/
theorem piece_atom_eq_lift {n k p : ℕ} (hkn : k < n) (s : Bool)
    (b : (DirectedGlobeComplex.cylinderOrderedAtomBasis n).Index p) :
    (piece n k s).toFun ((globeIso n).inv.toFun
      ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p b)) =
    atomLift hkn ⟨p, PastingGlobeCylinderBasis.pieceBasisMap hkn s b⟩ := by
  apply piece_eq_of_basisComparison hkn s
    (representativeSide hkn (PastingGlobeCylinderBasis.pieceBasisMap hkn s b))
  exact (piece_atom_image hkn s b).trans (atomLift_image hkn
    ⟨p, PastingGlobeCylinderBasis.pieceBasisMap hkn s b⟩).symm

theorem piece_cell_generated {n k : ℕ} (hkn : k < n) (s : Bool)
    (x : model.obj (Globe.category n)) :
    Nonempty (CompositionExpression (source n k) (atomLift hkn) ((piece n k s).toFun x)) := by
  let F : (rightCylinder (DirectedGlobeComplex.complex n)).realization ⟶ source n k :=
    (globeIso n).inv ≫ piece n k s
  have hgen := DirectedGlobeComplex.cylinder_generated n
    (fun y => Nonempty (CompositionExpression (source n k) (atomLift hkn) (F.toFun y)))
    (fun p b => by
      change Nonempty (CompositionExpression _ _ ((piece n k s).toFun ((globeIso n).inv.toFun _)))
      rw [piece_atom_eq_lift hkn s b]
      exact ⟨CompositionExpression.generator (C := source n k) (g := atomLift hkn)
        (⟨p, PastingGlobeCylinderBasis.pieceBasisMap hkn s b⟩ : (atomBasis hkn).AtomIndex)⟩)
    (fun r y z hyz hy hz => by
      have hf : (source n k).target r (F.toFun y) = (source n k).source r (F.toFun z) :=
        (F.map_face true r y).symm.trans
          ((congrArg F.toFun hyz).trans (F.map_face false r z))
      change Nonempty (CompositionExpression _ _ (F.toFun
        ((rightCylinder (DirectedGlobeComplex.complex n)).realization.comp r y z hyz)))
      rw [F.map_comp r y z hyz hf]
      obtain ⟨ty⟩ := hy
      obtain ⟨tz⟩ := hz
      exact ⟨.comp r hf ty tz⟩)
  have hi : (globeIso n).inv.toFun ((globeIso n).hom.toFun x) = x :=
    congrArg (fun f => f.toFun x) (globeIso n).hom_inv_id
  have hres := hgen ((globeIso n).hom.toFun x)
  change Nonempty (CompositionExpression (source n k) (atomLift hkn)
    ((piece n k s).toFun ((globeIso n).inv.toFun ((globeIso n).hom.toFun x)))) at hres
  rw [hi] at hres
  exact hres

/-- The actual source pushout is composition-generated by the bounded
chosen lifts of the explicit pasted-cylinder atoms. -/
theorem generated {n k : ℕ} (hkn : k < n) (x : source n k) :
    Nonempty (CompositionExpression (source n k) (atomLift hkn) x) := by
  have ht := PushoutGeneration.generated_by_pieces
    (model.map (Globe.faceMap true k n)) (model.map (Globe.faceMap false k n)) x
  obtain ⟨t⟩ := ht
  exact t.substitute (𝟙 (source n k)) (fun a => by
    cases a with
    | inl y => exact piece_cell_generated hkn false y
    | inr y => exact piece_cell_generated hkn true y)

end
end Thomason.Construction.StrictOmegaCategory.PastingGlobe.CylinderSource

end

section

/-! # Natural oriental comparison with the actual chain-cylinder model

Composition generation of the simplex atoms gives naturality and
identifies both endpoint conventions with the global chain model.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Functor _root_.OAI.Thomason.Construction.DirectedComplex SimplexComplex

noncomputable section

namespace NormalizedSimplexIdentities

/-- The normalized directed simplex complexes, including degenerate maps. -/
def chainCosimplicial (h : NormalizedSimplexIdentities) :
    SimplexCategory ⥤ DirectedComplex.{0} where
  obj m := directedComplex m.len (h.squared m.len)
  map f := directedMap (h.squared _) (h.squared _) f.toOrderHom
    (h.naturality f.toOrderHom)
  map_id _ := by
    apply DirectedComplex.Hom.ext_app
    intro n x
    exact mapChains_id x
  map_comp f g := by
    apply DirectedComplex.Hom.ext_app
    intro n x
    exact (mapChains_comp f.toOrderHom g.toOrderHom x).symm

/-- The chain-cylinder cosimplicial object has precisely the earlier literal
strict objects and maps. -/
def chainCylinderRealizationIso (h : NormalizedSimplexIdentities) :
    h.chainCosimplicial ⋙ rightCylinderFunctor ⋙ realizationFunctor ≅
      h.cylinderCosimplicial :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end NormalizedSimplexIdentities

namespace SimplexAtomsInput

variable {h : NormalizedSimplexIdentities} (a : SimplexAtomsInput h)

/-- The inverse presentation of normalized chains commutes with all simplex
operators, including those which collapse a basis element to zero. -/
def abelianizationCosimplicialIso :
    h.cosimplicial ⋙ StrictOmegaCategory.Abelianization.functor ≅
      h.chainCosimplicial :=
  NatIso.ofComponents (fun m => a.abelianizationIso m.len) (by
    intro m n f
    apply DirectedComplex.Hom.ext_app
    intro p z
    have he :
        (a.toSimplexApp n.len p).comp
          ((StrictOmegaCategory.Abelianization.map (h.map f.toOrderHom)).app p) =
        (mapChains f.toOrderHom p).toAddMonoidHom.comp (a.toSimplexApp m.len p) := by
      apply StrictOmegaCategory.Abelianization.hom_ext
      intro x
      change a.toSimplexApp n.len p
          ((StrictOmegaCategory.Abelianization.map (h.map f.toOrderHom)).app p
            (StrictOmegaCategory.Abelianization.generator (h.object m.len) p x)) = _
      rw [StrictOmegaCategory.Abelianization.map_generator,
        a.toSimplexChains_generator]
      simp only [AddMonoidHom.comp_apply, a.toSimplexChains_generator]
      rfl
    exact DFunLike.congr_fun he z)

/-- The actual chain-cylinder comparison, natural in the simplex. -/
def chainModelComparison :
    h.cylinderCosimplicial ≅
      h.cosimplicial ⋙ StrictOmegaCategory.GrayChainExtension.model :=
  h.chainCylinderRealizationIso.symm ≪≫
    isoWhiskerRight a.abelianizationCosimplicialIso.symm
      (rightCylinderFunctor ⋙ realizationFunctor) ≪≫
    Functor.associator h.cosimplicial StrictOmegaCategory.Abelianization.functor
      (rightCylinderFunctor ⋙ realizationFunctor)

/-- On an oriental the actual abelianization unit is the realization of the
inverse normalized-chain presentation. -/
theorem unit_eq_realized_inverse (m : ℕ) :
    StrictOmegaCategory.Abelianization.unit (h.object m) =
      (a.fromSimplexChains m).realization := by
  let e := realizationFunctor.mapIso (a.abelianizationIso m)
  apply (cancel_mono e.hom).mp
  change StrictOmegaCategory.Abelianization.unit (h.object m) ≫
      (a.toSimplexChains m).realization =
    (a.fromSimplexChains m).realization ≫ (a.toSimplexChains m).realization
  exact (StrictOmegaCategory.Abelianization.unit_evaluate (𝟙 (h.object m))).trans
    e.inv_hom_id.symm

/-- The comparison preserves the two concrete interval endpoints. -/
theorem chainModelComparison_endpoint (side : Bool) (m : SimplexCategory) :
    (h.cylinderEndpoint side).app m ≫ a.chainModelComparison.hom.app m =
      (StrictOmegaCategory.GrayChainExtension.modelEndpoint side).app
        (h.object m.len) := by
  let b := a.fromSimplexChains m.len
  let K := directedComplex m.len (h.squared m.len)
  let L := StrictOmegaCategory.Abelianization.complex (h.object m.len)
  let eK : K.realization ⟶ (rightCylinder K).realization :=
    (RightCylinder.endpoint K side).realization
  let eL : L.realization ⟶ (rightCylinder L).realization :=
    (RightCylinder.endpoint L side).realization
  let v : K.realization ⟶ L.realization := b.realization
  let cv : (rightCylinder K).realization ⟶ (rightCylinder L).realization :=
    (RightCylinder.map b).realization
  have hn : eK ≫ cv = v ≫ eL := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    apply Cell.ext
    funext t p
    exact RightCylinder.map_endpoint b side p (x.table t p)
  change eK ≫ cv = StrictOmegaCategory.Abelianization.unit (h.object m.len) ≫ eL
  exact hn.trans (congrArg (fun q : K.realization ⟶ L.realization => q ≫ eL)
    (a.unit_eq_realized_inverse m.len).symm)

end SimplexAtomsInput

end

end Thomason.Construction

end

section

/-! # Source-only finite-globe tests for truncation

In a globular category, fixing every source in degree n also fixes every
target. Thus a right adjoint's truncation can be tested using only source
collapse on the finite globe cylinders.
-/

namespace Thomason.Construction

open CategoryTheory

namespace StrictOmegaCategory.Globe

/-- Source collapse alone detects truncation; target collapse follows from
the same-level globular identity. -/
theorem truncated_iff_source_collapse (C : StrictOmegaCategory.{0}) (n : ℕ) :
    C.IsTruncated n ↔ ∀ (m : ℕ) (f : category m ⟶ C),
      collapse false n m ≫ f = f := by
  constructor
  · intro h m f
    exact (truncated_iff_collapse C n).mp h m f false
  · intro h x
    obtain ⟨m, hx⟩ := C.finite_dimension x
    let f : category m ⟶ C := lift C x hx
    have he := congrArg (fun k : category m ⟶ C => k.toFun Cell.top) (h m f)
    have hs : C.face false n x = x := (f.map_face false n Cell.top).symm.trans he
    refine ⟨hs, ?_⟩
    calc
      C.face true n x = C.face true n (C.face false n x) := congrArg _ hs.symm
      _ = C.face false n x := C.face_face_same true false n x
      _ = x := hs

end StrictOmegaCategory.Globe

/-- The right adjoint is truncated when all source collapses of its left
adjoint's actual globe cylinders are invisible in the target. -/
theorem internalHom_truncated_iff_cylinder_source_globes
    {F R : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}} (adj : F ⊣ R)
    (Y : StrictOmegaCategory.{0}) (n : ℕ) :
    (R.obj Y).IsTruncated n ↔
      ∀ (m : ℕ) (f : F.obj (StrictOmegaCategory.Globe.category m) ⟶ Y),
        F.map (StrictOmegaCategory.Globe.collapse false n m) ≫ f = f := by
  rw [StrictOmegaCategory.Globe.truncated_iff_source_collapse]
  constructor
  · intro h m f
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left]
    exact h m ((adj.homEquiv _ _) f)
  · intro h m g
    have he := congrArg (adj.homEquiv (StrictOmegaCategory.Globe.category m) Y)
      (h m ((adj.homEquiv _ _).symm g))
    simpa only [adj.homEquiv_naturality_left, Equiv.apply_symm_apply] using he

end Thomason.Construction

end

section

/-! # Source collapse of the concrete right-globe cylinder

Collapsing a globe to its n-source changes its n-chain by the positive
boundary of its next-dimensional source generator. After tensoring on the
right with the interval, every map to an n-truncated target identifies
this collapse with the identity.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- The chain map presenting source collapse is the map of the source table. -/
theorem chainMap_sourceCollapse {m n : ℕ} (hnm : n < m) :
    chainMap (StrictOmegaCategory.Globe.collapse false n m) =
      cellMap m ((topCell m).face false n) := by
  apply (realizationHomEquiv m (complex m)).injective
  change (chainMap _).realization = (cellMap _ _).realization
  apply (cancel_epi (globeIso m).hom).mp
  rw [chainMap_realization]
  simp only [Iso.hom_inv_id_assoc]
  apply StrictOmegaCategory.Globe.hom_ext
  change (fromGlobe m).toFun ((StrictOmegaCategory.Globe.category m).face false n
      StrictOmegaCategory.Globe.Cell.top) =
    (cellMap m ((topCell m).face false n)).realization.toFun (topCell m)
  apply ((fromGlobe m).map_face false n
    (show StrictOmegaCategory.Globe.category m from StrictOmegaCategory.Globe.Cell.top)).trans
  exact (cellMap_top_of_bounded m ((topCell m).face false n)
    ((complex m).realization.dimensionLE_mono hnm.le
      ((complex m).realization.face_dimensionLE false n (topCell m)))).symm

/-- Below the collapsed source dimension every chain is unchanged. -/
theorem chainMap_sourceCollapse_agree_below {m n : ℕ} (hnm : n < m) :
    ∀ k, k < n → (chainMap (StrictOmegaCategory.Globe.collapse false n m)).app k =
      (Hom.id (complex m)).app k := by
  intro k hkn
  rw [chainMap_sourceCollapse hnm]
  apply AddMonoidHom.ext
  intro v
  induction v using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add v w hv hw =>
    change cellApp m ((topCell m).face false n) k (v + w) = v + w
    change cellApp m ((topCell m).face false n) k v = v at hv
    change cellApp m ((topCell m).face false n) k w = w at hw
    rw [map_add, hv, hw]
    rfl
  | single s z =>
    change cellApp m ((topCell m).face false n) k (Finsupp.single s z) =
      Finsupp.single s z
    rw [cellApp_single]
    change z • Cell.cutTable (topCell m) false n s.val k = _
    simp only [Cell.cutTable, hkn, ite_true]
    have hkm : k < m := hkn.trans hnm
    change z • topTable m s.val k = _
    simp [topTable, hkm]

/-- The discrepancy at dimension n is an explicit positive boundary. -/
theorem chainMap_sourceCollapse_positive_bridge {m n : ℕ} (hnm : n < m) :
    ∀ v : (complex m).group n, v ∈ (complex m).positive n →
      ∃ z : (complex m).group (n+1), z ∈ (complex m).positive (n+1) ∧
        (complex m).differential n z = (Hom.id (complex m)).app n v -
          (chainMap (StrictOmegaCategory.Globe.collapse false n m)).app n v := by
  classical
  intro v hv
  change Chains m n at v
  change ∀ b : Basis m n, 0 ≤ v b at hv
  let s : Basis m n := ⟨false, Or.inl hnm⟩
  let t : Basis m n := ⟨true, Or.inl hnm⟩
  let q : Basis m (n+1) := ⟨false, by
    by_cases h : n+1 < m
    · exact Or.inl h
    · exact Or.inr ⟨by omega, rfl⟩⟩
  refine ⟨Finsupp.single q (v t), ?_, ?_⟩
  · change ∀ b, 0 ≤ Finsupp.single q (v t) b
    intro b
    by_cases hb : q = b
    · subst b
      simpa only [Finsupp.single_eq_same] using hv t
    · simp only [Finsupp.single_apply, hb, ite_false, le_refl]
  · rw [chainMap_sourceCollapse hnm]
    let c : Chains m n →ₗ[ℤ] Chains m n := cellApp m ((topCell m).face false n) n
    change differential m n (Finsupp.single q (v t)) = v - c v
    have hc (b : Basis m n) (z : ℤ) :
        c (Finsupp.single b z) = z • topTable m false n := by
      change cellApp m ((topCell m).face false n) n (Finsupp.single b z) = _
      rw [cellApp_single]
      change z • (if n < n then topTable m b.val n else
        if n = n then topTable m false n else 0) = z • topTable m false n
      simp only [Nat.lt_irrefl, ite_false, ite_true]
    rw [differential_single]
    have hdecomp : v = Finsupp.single s (v s) + Finsupp.single t (v t) := by
      ext b
      rcases b with ⟨b, hb⟩
      cases b <;> simp [s, t]
    conv_rhs => rw [hdecomp, map_add, hc, hc]
    simp only [boundary, hnm, dite_true, topTable, s, t]
    simp only [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]
    abel

/-- Every map from the actual right-cylinder globe to an n-truncated target
kills source collapse in dimension n. -/
theorem rightGlobeCylinder_sourceCollapse {Y : StrictOmegaCategory.{0}}
    {m n : ℕ} (hY : Y.IsTruncated n)
    (H : rightGlobeCylinder.obj ⟨m⟩ ⟶ Y) :
    rightGlobeCylinder.map (StrictOmegaCategory.Globe.collapse false n m) ≫ H = H := by
  by_cases hnm : n < m
  · have h := rightCylinder_realization_comp_eq_of_positive_degree_bridge
      (chainMap (StrictOmegaCategory.Globe.collapse false n m)) (Hom.id (complex m))
      (chainMap_sourceCollapse_agree_below hnm)
      (chainMap_sourceCollapse_positive_bridge hnm) hY H
    change (RightCylinder.map (chainMap (StrictOmegaCategory.Globe.collapse false n m))).realization ≫ H = H
    have hi : (RightCylinder.map (Hom.id (complex m))).realization =
        𝟙 (rightCylinder (complex m)).realization := by
      apply StrictOmegaCategory.Hom.ext
      funext x
      apply Cell.ext
      funext a k
      cases k <;> rfl
    rw [hi] at h
    exact h.trans (Category.id_comp H)
  · rw [StrictOmegaCategory.Globe.collapse_eq_id false (Nat.le_of_not_gt hnm)]
    change rightGlobeCylinder.map (𝟙 (⟨m⟩ : StrictOmegaCategory.Globe.Shapes)) ≫ H = H
    rw [rightGlobeCylinder.map_id, Category.id_comp]

end

end Thomason.Construction.DirectedGlobeComplex

namespace Thomason.Construction

open CategoryTheory

/-- A literal comparison on all free globe cylinders suffices to derive
truncation of the right adjoint. No claim about arbitrary cells of a tensor
product is needed. -/
theorem internalHom_truncated_of_rightGlobeComparison
    {F R : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}} (adj : F ⊣ R)
    (e : StrictOmegaCategory.Globe.inclusion ⋙ F ≅
      DirectedGlobeComplex.rightGlobeCylinder)
    {Y : StrictOmegaCategory.{0}} {n : ℕ} (hY : Y.IsTruncated n) :
    (R.obj Y).IsTruncated n := by
  apply (internalHom_truncated_iff_cylinder_source_globes adj Y n).mpr
  intro m H
  let u : F.obj (StrictOmegaCategory.Globe.category m) ⟶
      DirectedGlobeComplex.rightGlobeCylinder.obj ⟨m⟩ := e.hom.app ⟨m⟩
  let v : DirectedGlobeComplex.rightGlobeCylinder.obj ⟨m⟩ ⟶
      F.obj (StrictOmegaCategory.Globe.category m) := e.inv.app ⟨m⟩
  have huv : u ≫ v = 𝟙 _ := e.hom_inv_id_app ⟨m⟩
  have he := e.hom.naturality (show (⟨m⟩ : StrictOmegaCategory.Globe.Shapes) ⟶ ⟨m⟩ from
    StrictOmegaCategory.Globe.collapse false n m)
  change F.map (StrictOmegaCategory.Globe.collapse false n m) ≫ u =
    u ≫ DirectedGlobeComplex.rightGlobeCylinder.map
      (StrictOmegaCategory.Globe.collapse false n m) at he
  have hc := DirectedGlobeComplex.rightGlobeCylinder_sourceCollapse hY (v ≫ H)
  calc
    F.map (StrictOmegaCategory.Globe.collapse false n m) ≫ H =
        F.map (StrictOmegaCategory.Globe.collapse false n m) ≫ (u ≫ (v ≫ H)) := by
      rw [← Category.assoc u v H, huv, Category.id_comp]
    _ = u ≫ (DirectedGlobeComplex.rightGlobeCylinder.map
        (StrictOmegaCategory.Globe.collapse false n m) ≫ (v ≫ H)) := by
      rw [← Category.assoc, he, Category.assoc]
    _ = u ≫ (v ≫ H) := congrArg (u ≫ ·) hc
    _ = H := by rw [← Category.assoc, huv, Category.id_comp]

/-- A natural comparison with the concrete free-globe cylinders gives
preservation of finite truncations by the right internal hom. -/
theorem grayTruncationInput_of_rightGlobeComparison
    {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
    (e : StrictOmegaCategory.Globe.inclusion ⋙ G.cylinder ≅
      DirectedGlobeComplex.rightGlobeCylinder) : GrayTruncationInput G :=
  ⟨fun _ Y => internalHom_truncated_of_rightGlobeComparison G.adjunction e Y.property⟩

end Thomason.Construction

end

section

/-! # The actual extended cylinder on all free globes

The finite-parameter Kan extension and the natural globe abelianization
isomorphisms identify the extended cylinder with the concrete right
chain cylinder on every globe and every strict map of globes.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayChainExtension

open CategoryTheory CategoryTheory.Functor _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Restriction of the global extension to globes agrees naturally with
its original chain model. -/
def globeModelIso : Globe.inclusion ⋙ cylinder ≅ Globe.inclusion ⋙ model :=
  (isoWhiskerRight GlobePasting.globesInclusionIso cylinder).symm ≪≫
    Functor.associator _ _ _ ≪≫
    (isoWhiskerLeft GlobePasting.globes parameterIso).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight GlobePasting.globesInclusionIso model

/-- The extended cylinder has the concrete signed right-cylinder values
and maps on the actual finite globes. -/
def globeRestrictionIso : Globe.inclusion ⋙ cylinder ≅
    DirectedGlobeComplex.rightGlobeCylinder :=
  globeModelIso ≪≫ DirectedGlobeComplex.rightCylinderAbelianizationGlobeIso

/-- Every right adjoint of the actual extension preserves truncation.
Adjointness itself is a separate construction; the truncation proof uses
only the now-established concrete globe restriction. -/
theorem rightAdjoint_truncated {R : StrictOmegaCategory.{0} ⥤ StrictOmegaCategory.{0}}
    (adj : cylinder ⊣ R) {Y : StrictOmegaCategory.{0}} {n : ℕ}
    (hY : Y.IsTruncated n) : (R.obj Y).IsTruncated n :=
  internalHom_truncated_of_rightGlobeComparison adj globeRestrictionIso hY

/-- A natural isomorphism of cylinder functors transports preservation of
finite truncations by their right adjoints. -/
theorem truncationInput {h : NormalizedSimplexIdentities} (G : RightGrayInput h)
    (e : G.cylinder ≅ cylinder) : GrayTruncationInput G :=
  grayTruncationInput_of_rightGlobeComparison G
    (isoWhiskerLeft Globe.inclusion e ≪≫ globeRestrictionIso)

end

end Thomason.Construction.StrictOmegaCategory.GrayChainExtension

end

end OAI
