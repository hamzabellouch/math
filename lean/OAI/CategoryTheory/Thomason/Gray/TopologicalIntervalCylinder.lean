import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeFaces
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Gray.GrayChainGlobeRestriction
import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderPath
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import OAI.CategoryTheory.Thomason.Strict.StrictIsomorphisms
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Generator.StrongGenerator

namespace OAI

section

/-! # Top endpoint and prism cells generate all globe-cylinder atoms

Every lower atom is the image of a top endpoint or prism under the literal
globular face map. These formulas allow induction on the dimension of a
cell in the source of the extended cylinder.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayChainExtension

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

def modelGlobeIso (n : ℕ) : model.obj (Globe.category n) ≅
    (rightCylinder (DirectedGlobeComplex.complex n)).realization :=
  DirectedGlobeComplex.rightCylinderAbelianizationGlobeIso.app ⟨n⟩

theorem modelGlobeIso_naturality {m n : ℕ} (f : Globe.category m ⟶ Globe.category n) :
    model.map f ≫ (modelGlobeIso n).hom = (modelGlobeIso m).hom ≫
      (RightCylinder.map (DirectedGlobeComplex.chainMap f)).realization :=
  DirectedGlobeComplex.rightCylinderAbelianizationGlobeIso.hom.naturality
    (show (⟨m⟩ : Globe.Shapes) ⟶ ⟨n⟩ from f)

theorem modelGlobeIso_inv_naturality {m n : ℕ} (f : Globe.category m ⟶ Globe.category n) :
    (modelGlobeIso m).inv ≫ model.map f =
      (RightCylinder.map (DirectedGlobeComplex.chainMap f)).realization ≫ (modelGlobeIso n).inv := by
  apply (cancel_mono (modelGlobeIso n).hom).mp
  rw [Category.assoc, modelGlobeIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem chainMap_faceMap (a : Bool) (m n : ℕ) :
    DirectedGlobeComplex.chainMap (Globe.faceMap a m n) = DirectedGlobeComplex.faceMap a m n := by
  apply (DirectedGlobeComplex.realizationHomEquiv m (DirectedGlobeComplex.complex n)).injective
  change (DirectedGlobeComplex.chainMap (Globe.faceMap a m n)).realization =
    (DirectedGlobeComplex.faceMap a m n).realization
  rw [DirectedGlobeComplex.chainMap_realization]
  apply (cancel_epi (DirectedGlobeComplex.globeIso m).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact DirectedGlobeComplex.fromGlobe_faceMap a m n

def endpointTop (n : ℕ) (a : Bool) : model.obj (Globe.category n) :=
  (modelGlobeIso n).inv.toFun
    (Cell.map (RightCylinder.endpoint (DirectedGlobeComplex.complex n) a)
      (DirectedGlobeComplex.topCell n))

def prismTop (n : ℕ) : model.obj (Globe.category n) :=
  (modelGlobeIso n).inv.toFun (RightCylinder.prism (DirectedGlobeComplex.topCell n))

theorem endpointTop_dimension (n : ℕ) (a : Bool) :
    (model.obj (Globe.category n)).DimensionLE n (endpointTop n a) :=
  (modelGlobeIso n).inv.dimensionLE ((RightCylinder.endpoint _ a).realization.dimensionLE
    (DirectedGlobeComplex.topCell_dimension n))

theorem prismTop_dimension (n : ℕ) :
    (model.obj (Globe.category n)).DimensionLE (n+1) (prismTop n) :=
  (modelGlobeIso n).inv.dimensionLE
    (RightCylinder.prism_dimension _ (DirectedGlobeComplex.topCell_dimension n))

theorem endpointTop_face (a side : Bool) (p n : ℕ) :
    (model.map (Globe.faceMap a p n)).toFun (endpointTop p side) =
      (modelGlobeIso n).inv.toFun
        (Cell.map (RightCylinder.endpoint _ side)
          ((DirectedGlobeComplex.topCell n).face a p)) := by
  have he := congrArg (fun f => f.toFun
    (Cell.map (RightCylinder.endpoint _ side) (DirectedGlobeComplex.topCell p)))
    (modelGlobeIso_inv_naturality (Globe.faceMap a p n))
  rw [chainMap_faceMap] at he
  have ht : Cell.map (RightCylinder.map (DirectedGlobeComplex.faceMap a p n))
      (Cell.map (RightCylinder.endpoint _ side) (DirectedGlobeComplex.topCell p)) =
    Cell.map (RightCylinder.endpoint _ side)
      ((DirectedGlobeComplex.topCell n).face a p) := by
    have hn : Cell.map (RightCylinder.map (DirectedGlobeComplex.faceMap a p n))
        (Cell.map (RightCylinder.endpoint _ side) (DirectedGlobeComplex.topCell p)) =
      Cell.map (RightCylinder.endpoint _ side)
        (Cell.map (DirectedGlobeComplex.faceMap a p n) (DirectedGlobeComplex.topCell p)) := by
      apply Cell.ext
      funext c q
      exact RightCylinder.map_endpoint (DirectedGlobeComplex.faceMap a p n) side q _
    exact hn.trans (congrArg (Cell.map (RightCylinder.endpoint _ side))
      (DirectedGlobeComplex.faceMap_top a p n))
  exact he.trans (congrArg (modelGlobeIso n).inv.toFun ht)

theorem prismTop_face (a : Bool) (p n : ℕ) :
    (model.map (Globe.faceMap a p n)).toFun (prismTop p) =
      (modelGlobeIso n).inv.toFun
        (RightCylinder.prism ((DirectedGlobeComplex.topCell n).face a p)) := by
  have he := congrArg (fun f => f.toFun (RightCylinder.prism (DirectedGlobeComplex.topCell p)))
    (modelGlobeIso_inv_naturality (Globe.faceMap a p n))
  rw [chainMap_faceMap] at he
  exact he.trans (congrArg (modelGlobeIso n).inv.toFun
    ((RightCylinder.prism_naturality (DirectedGlobeComplex.faceMap a p n)
      (DirectedGlobeComplex.topCell p)).trans
        (congrArg RightCylinder.prism (DirectedGlobeComplex.faceMap_top a p n))))

theorem endpointTop_modelAtom {n p : ℕ} (b : DirectedGlobeComplex.Basis n p) (side : Bool) :
    (model.map (Globe.faceMap b.val p n)).toFun (endpointTop p side) =
      (modelGlobeIso n).inv.toFun
        ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom p (.endpoint side b)) :=
  endpointTop_face b.val side p n

theorem prismTop_modelAtom {n p : ℕ} (b : DirectedGlobeComplex.Basis n p) :
    (model.map (Globe.faceMap b.val p n)).toFun (prismTop p) =
      (modelGlobeIso n).inv.toFun
        ((DirectedGlobeComplex.cylinderOrderedAtomBasis n).atom (p+1) (.mixed b)) :=
  prismTop_face b.val p n

end
end Thomason.Construction.StrictOmegaCategory.GrayChainExtension

end

section

/-! # The finite strict globes form a small strong generator -/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

/-- A monic strict functor is injective on cells, as tested by finite globes. -/
theorem cell_injective_of_mono {C D : StrictOmegaCategory.{0}} (f : C ⟶ D) [Mono f] :
    Function.Injective f.toFun := by
  intro x y hxy
  obtain ⟨m, hm⟩ := C.finite_dimension x
  obtain ⟨n, hn⟩ := C.finite_dimension y
  let a := Globe.lift C x (C.dimensionLE_mono (Nat.le_max_left m n) hm)
  let b := Globe.lift C y (C.dimensionLE_mono (Nat.le_max_right m n) hn)
  have he : a ≫ f = b ≫ f := Globe.hom_ext D _ _ hxy
  have hab : a = b := (cancel_mono f).mp he
  exact congrArg (fun k : Globe.category (max m n) ⟶ C => k.toFun Globe.Cell.top) hab

/-- A bijective strict functor has a strict inverse. -/
theorem isIso_of_cell_bijective {C D : StrictOmegaCategory.{0}} (f : C ⟶ D)
    (hf : Function.Bijective f.toFun) : IsIso f := by
  change IsIso (isoOfBijective f hf).hom
  infer_instance

def globes : ObjectProperty StrictOmegaCategory.{0} := ObjectProperty.ofObj Globe.category

instance globes_small : ObjectProperty.Small.{0} globes := by
  change ObjectProperty.Small.{0} (ObjectProperty.ofObj Globe.category)
  infer_instance

theorem globes_isSeparating : globes.IsSeparating := by
  intro C D f g h
  apply Hom.ext
  funext x
  obtain ⟨n, hn⟩ := C.finite_dimension x
  have he := h (Globe.category n) (ObjectProperty.ofObj_apply Globe.category n)
    (Globe.lift C x hn)
  exact congrArg (fun k : Globe.category n ⟶ D => k.toFun Globe.Cell.top) he

theorem globes_isStrongGenerator : globes.IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨globes_isSeparating, ?_⟩
  intro C D f _ hf
  apply isIso_of_cell_bijective f
  refine ⟨cell_injective_of_mono f, ?_⟩
  intro y
  obtain ⟨n, hn⟩ := D.finite_dimension y
  obtain ⟨a, ha⟩ := hf (Globe.category n) (ObjectProperty.ofObj_apply Globe.category n)
    (Globe.lift D y hn)
  exact ⟨a.toFun Globe.Cell.top,
    congrArg (fun k : Globe.category n ⟶ D => k.toFun Globe.Cell.top) ha⟩

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # The two higher factorizations of a lower composite

Unit laws and interchange give the two whiskered r-composites of a fixed
s-composite, for s < r. These are the actual strict operations used in
the adjacent-atom transposition argument.
-/

namespace Thomason.Construction.StrictOmegaCategory

variable (C : StrictOmegaCategory.{0})

theorem matching_face_right {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) (side : Bool) :
    C.target s u = C.source s (C.face side r v) := by
  have he : C.source s (C.face side r v) = C.source s v := by
    simp only [source, C.globular, hsr, ite_true]
  exact huv.trans he.symm

theorem matching_face_left {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) (side : Bool) :
    C.target s (C.face side r u) = C.source s v := by
  have he : C.target s (C.face side r u) = C.target s u := by
    simp only [target, C.globular, hsr, ite_true]
  exact he.trans huv

theorem matching_faces {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) (a b : Bool) :
    C.target s (C.face a r u) = C.source s (C.face b r v) := by
  have he : C.source s (C.face b r v) = C.source s v := by
    simp only [source, C.globular, hsr, ite_true]
  exact (C.matching_face_left hsr u v huv a).trans he.symm

def rightWhisker {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) (side : Bool) : C :=
  C.comp s u (C.face side r v) (C.matching_face_right hsr u v huv side)

def leftWhisker {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) (side : Bool) : C :=
  C.comp s (C.face side r u) v (C.matching_face_left hsr u v huv side)

theorem whiskered_forward_matching {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) :
    C.target r (C.rightWhisker hsr u v huv false) =
      C.source r (C.leftWhisker hsr u v huv true) := by
  dsimp only [rightWhisker, leftWhisker, source, target]
  have hm := C.matching_faces hsr u v huv true false
  have h1 : C.target s (C.target r u) = C.source s (C.target r (C.source r v)) := by
    simpa only [C.face_face_same] using hm
  have h2 : C.target s (C.source r (C.target r u)) = C.source s (C.source r v) := by
    simpa only [C.face_face_same] using hm
  have ht := C.face_comp true r s hsr u (C.source r v)
    (C.matching_face_right hsr u v huv false) h1
  have hs := C.face_comp false r s hsr (C.target r u) v
    (C.matching_face_left hsr u v huv true) h2
  exact ht.trans (by simpa only [C.face_face_same] using hs.symm)

theorem whiskered_reverse_matching {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) :
    C.target r (C.leftWhisker hsr u v huv false) =
      C.source r (C.rightWhisker hsr u v huv true) := by
  dsimp only [rightWhisker, leftWhisker, source, target]
  have hm := C.matching_faces hsr u v huv false true
  have h1 : C.target s (C.target r (C.source r u)) = C.source s (C.target r v) := by
    simpa only [C.face_face_same] using hm
  have h2 : C.target s (C.source r u) = C.source s (C.source r (C.target r v)) := by
    simpa only [C.face_face_same] using hm
  have ht := C.face_comp true r s hsr (C.source r u) v
    (C.matching_face_left hsr u v huv false) h1
  have hs := C.face_comp false r s hsr u (C.target r v)
    (C.matching_face_right hsr u v huv true) h2
  exact ht.trans (by simpa only [C.face_face_same] using hs.symm)

theorem whiskered_forward_comp {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) :
    C.comp r (C.rightWhisker hsr u v huv false) (C.leftWhisker hsr u v huv true)
      (C.whiskered_forward_matching hsr u v huv) = C.comp s u v huv := by
  have hu : C.target r u = C.source r (C.target r u) :=
    (C.face_face_same false true r u).symm
  have hv : C.target r (C.source r v) = C.source r v :=
    C.face_face_same true false r v
  have hur := C.right_unit r u hu
  have hvl := C.left_unit r v hv
  have hr : C.target s (C.comp r u (C.target r u) hu) =
      C.source s (C.comp r (C.source r v) v hv) := by
    rw [hur, hvl]
    exact huv
  have hi := C.interchange s r hsr u (C.source r v) (C.target r u) v
    (C.matching_face_right hsr u v huv false)
    (C.matching_face_left hsr u v huv true) hu hv
    (C.whiskered_forward_matching hsr u v huv) hr
  exact hi.trans (by simp only [hur, hvl])

theorem whiskered_reverse_comp {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) :
    C.comp r (C.leftWhisker hsr u v huv false) (C.rightWhisker hsr u v huv true)
      (C.whiskered_reverse_matching hsr u v huv) = C.comp s u v huv := by
  have hu : C.target r (C.source r u) = C.source r u :=
    C.face_face_same true false r u
  have hv : C.target r v = C.source r (C.target r v) :=
    (C.face_face_same false true r v).symm
  have hul := C.left_unit r u hu
  have hvr := C.right_unit r v hv
  have hr : C.target s (C.comp r (C.source r u) u hu) =
      C.source s (C.comp r v (C.target r v) hv) := by
    rw [hul, hvr]
    exact huv
  have hi := C.interchange s r hsr (C.source r u) v u (C.target r v)
    (C.matching_face_left hsr u v huv false)
    (C.matching_face_right hsr u v huv true) hu hv
    (C.whiskered_reverse_matching hsr u v huv) hr
  exact hi.trans (by simp only [hul, hvr])

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Upper tables of strict whiskers and reflection of their factors

Higher faces contribute zero above their face degree. This concrete
calculation transfers the strict interchange factorizations to the
ordered-atom uniqueness induction.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem map_face_table_above {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (x : C) (r : ℕ) (side : Bool)
    (n : ℕ) (hn : r < n) (a : Bool) :
    (F.toFun (C.face side r x)).table a n = 0 := by
  have he := congrArg (fun X : Cell K => X.table a n) (F.map_face side r x)
  let X : Cell K := F.toFun x
  have hz : (X.face side r).table a n = 0 := by
    simp only [Cell.face_table, Cell.cutTable, Nat.not_lt.mpr hn.le,
      Nat.ne_of_gt hn, ite_false]
  exact he.trans hz

theorem rightWhisker_table_above {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) (side : Bool)
    (n : ℕ) (hn : r < n) (a : Bool) :
    (F.toFun (C.rightWhisker hsr u v huv side)).table a n = (F.toFun u).table a n := by
  let h := C.matching_face_right hsr u v huv side
  have hf : (F.toFun u).face true s = (F.toFun (C.face side r v)).face false s :=
    (F.map_face true s u).symm.trans
      ((congrArg F.toFun h).trans (F.map_face false s (C.face side r v)))
  have he := congrArg (fun X : Cell K => X.table a n)
    (F.map_comp s u (C.face side r v) h hf)
  change (F.toFun (C.rightWhisker hsr u v huv side)).table a n = _ at he
  have hsn : s < n := hsr.trans hn
  have hz := map_face_table_above F v r side n hn a
  let U : Cell K := F.toFun u
  let V : Cell K := F.toFun (C.face side r v)
  have hf' : U.face true s = V.face false s := hf
  have hz' : V.table a n = 0 := hz
  have hp : (Cell.comp U V s hf').table a n = U.table a n := by
    simp only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr hsn.le,
      Nat.ne_of_gt hsn, ite_false, hz', add_zero]
  exact he.trans hp

theorem leftWhisker_table_above {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) {s r : ℕ} (hsr : s < r) (u v : C)
    (huv : C.target s u = C.source s v) (side : Bool)
    (n : ℕ) (hn : r < n) (a : Bool) :
    (F.toFun (C.leftWhisker hsr u v huv side)).table a n = (F.toFun v).table a n := by
  let h := C.matching_face_left hsr u v huv side
  have hf : (F.toFun (C.face side r u)).face true s = (F.toFun v).face false s :=
    (F.map_face true s (C.face side r u)).symm.trans
      ((congrArg F.toFun h).trans (F.map_face false s v))
  have he := congrArg (fun X : Cell K => X.table a n)
    (F.map_comp s (C.face side r u) v h hf)
  change (F.toFun (C.leftWhisker hsr u v huv side)).table a n = _ at he
  have hsn : s < n := hsr.trans hn
  have hz := map_face_table_above F u r side n hn a
  let U : Cell K := F.toFun (C.face side r u)
  let V : Cell K := F.toFun v
  have hf' : U.face true s = V.face false s := hf
  have hz' : U.table a n = 0 := hz
  have hp : (Cell.comp U V s hf').table a n = V.table a n := by
    simp only [Cell.comp_table, Cell.pasteTable, Nat.not_lt.mpr hsn.le,
      Nat.ne_of_gt hsn, ite_false, hz', zero_add]
  exact he.trans hp

theorem reflect_binary_factors {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (r : ℕ)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    (a b c d : C) (hab : C.target r a = C.source r b)
    (hcd : C.target r c = C.source r d)
    (ha : B.AboveAtomOrZero r (F.toFun a)) (hb : B.AboveAtomOrZero r (F.toFun b))
    (he : F.toFun (C.comp r a b hab) = F.toFun (C.comp r c d hcd))
    (hupper : ∀ n, r < n → ∀ side,
      (F.toFun a).table side n = (F.toFun c).table side n) : a = c ∧ b = d := by
  have hfab : (F.toFun a).face true r = (F.toFun b).face false r :=
    (F.map_face true r a).symm.trans
      ((congrArg F.toFun hab).trans (F.map_face false r b))
  have hfcd : (F.toFun c).face true r = (F.toFun d).face false r :=
    (F.map_face true r c).symm.trans
      ((congrArg F.toFun hcd).trans (F.map_face false r d))
  have htotal : Cell.comp (F.toFun a) (F.toFun b) r hfab =
      Cell.comp (F.toFun c) (F.toFun d) r hfcd :=
    (F.map_comp r a b hab hfab).symm.trans (he.trans (F.map_comp r c d hcd hfcd))
  have hfactors := Cell.factors_unique_of_above _ _ _ _ r hfab hfcd htotal hupper
  obtain ⟨_, _, hau⟩ := hunique (F.toFun a) ha
  obtain ⟨_, _, hbu⟩ := hunique (F.toFun b) hb
  exact ⟨(hau a rfl).trans (hau c hfactors.1.symm).symm,
    (hbu b rfl).trans (hbu d hfactors.2.symm).symm⟩

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Transposition of two neighbouring atom factors

This is the local interchange step of Steiner 2004, Lemma 5.10.
Uniqueness at the preceding decomposition level lifts the positive-table
lower factorization and identifies its two whiskered decompositions.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem matching_of_unique_lower_faces {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (r s : ℕ) (hsr : s ≤ r)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    (u v : C) (U V : Cell K) (hu : F.toFun u = U) (hv : F.toFun v = V)
    (hUV : U.face true s = V.face false s) : C.target s u = C.source s v := by
  obtain ⟨_, _, huniq⟩ := hunique (U.face true s)
    (B.aboveAtomOrZero_mono hsr _ (B.aboveAtomOrZero_face U true s))
  have hfu : F.toFun (C.target s u) = U.face true s := by
    rw [F.map_face, hu]
    rfl
  have hfv : F.toFun (C.source s v) = U.face true s := by
    rw [F.map_face, hv]
    exact hUV.symm
  exact (huniq _ hfu).trans (huniq _ hfv).symm

theorem reflect_forward_whiskers {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) {s r : ℕ} (hsr : s < r)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    (y z u v : C) (hyz : C.target r y = C.source r z)
    (huv : C.target s u = C.source s v)
    (hy : B.AboveAtomOrZero r (F.toFun y)) (hz : B.AboveAtomOrZero r (F.toFun z))
    (he : F.toFun (C.comp s u v huv) = F.toFun (C.comp r y z hyz))
    (hupper : ∀ n, r < n → ∀ side, (F.toFun y).table side n = (F.toFun u).table side n) :
    C.comp r y z hyz = C.comp s u v huv := by
  have hh : F.toFun (C.comp r y z hyz) = F.toFun
      (C.comp r (C.rightWhisker hsr u v huv false) (C.leftWhisker hsr u v huv true)
        (C.whiskered_forward_matching hsr u v huv)) :=
    he.symm.trans (congrArg F.toFun (C.whiskered_forward_comp hsr u v huv)).symm
  have hpair := B.reflect_binary_factors F r hunique y z _ _ hyz
    (C.whiskered_forward_matching hsr u v huv) hy hz hh
    (fun n hn side => (hupper n hn side).trans
      (rightWhisker_table_above F hsr u v huv false n hn side).symm)
  calc
    C.comp r y z hyz =
        C.comp r (C.rightWhisker hsr u v huv false) (C.leftWhisker hsr u v huv true)
          (C.whiskered_forward_matching hsr u v huv) := by
      congr 1
      · exact hpair.1
      · exact hpair.2
    _ = _ := C.whiskered_forward_comp hsr u v huv

theorem reflect_reverse_whiskers {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) {s r : ℕ} (hsr : s < r)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    (y z u v : C) (hyz : C.target r y = C.source r z)
    (huv : C.target s u = C.source s v)
    (hy : B.AboveAtomOrZero r (F.toFun y)) (hz : B.AboveAtomOrZero r (F.toFun z))
    (he : F.toFun (C.comp s u v huv) = F.toFun (C.comp r y z hyz))
    (hupper : ∀ n, r < n → ∀ side, (F.toFun y).table side n = (F.toFun v).table side n) :
    C.comp r y z hyz = C.comp s u v huv := by
  have hh : F.toFun (C.comp r y z hyz) = F.toFun
      (C.comp r (C.leftWhisker hsr u v huv false) (C.rightWhisker hsr u v huv true)
        (C.whiskered_reverse_matching hsr u v huv)) :=
    he.symm.trans (congrArg F.toFun (C.whiskered_reverse_comp hsr u v huv)).symm
  have hpair := B.reflect_binary_factors F r hunique y z _ _ hyz
    (C.whiskered_reverse_matching hsr u v huv) hy hz hh
    (fun n hn side => (hupper n hn side).trans
      (leftWhisker_table_above F hsr u v huv false n hn side).symm)
  calc
    C.comp r y z hyz =
        C.comp r (C.leftWhisker hsr u v huv false) (C.rightWhisker hsr u v huv true)
          (C.whiskered_reverse_matching hsr u v huv) := by
      congr 1
      · exact hpair.1
      · exact hpair.2
    _ = _ := C.whiskered_reverse_comp hsr u v huv

/-- A reverse-disjoint neighbouring pair may be exchanged without changing
its actual strict composite. Only preceding-level uniqueness is used. -/
theorem adjacent_transpose {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (s : ℕ)
    (hunique : ∀ X, B.AboveAtomOrZero (s+1) X → ∃! x : C, F.toFun x = X)
    {p q : ℕ} (a : B.Index p) (b : B.Index q) (hp : s+1 < p) (hq : s+1 < q)
    (y z : C) (hyz : C.target (s+1) y = C.source (s+1) z)
    (hy : ∀ n, s+1 < n → ∀ side, (F.toFun y).table side n = (B.atom p a).table side n)
    (hz : ∀ n, s+1 < n → ∀ side, (F.toFun z).table side n = (B.atom q b).table side n)
    (hdis : ∀ e, B.coordinates (s+1) ((B.atom p a).table true (s+1)) e = 0 ∨
      B.coordinates (s+1) ((B.atom q b).table false (s+1)) e = 0) :
    ∃ (y' z' : C) (h : C.target (s+1) y' = C.source (s+1) z'),
      C.comp (s+1) y' z' h = C.comp (s+1) y z hyz ∧
      (∀ n, s+1 < n → ∀ side, (F.toFun y').table side n = (B.atom q b).table side n) ∧
      (∀ n, s+1 < n → ∀ side, (F.toFun z').table side n = (B.atom p a).table side n) := by
  have hfyz : (F.toFun y).face true (s+1) = (F.toFun z).face false (s+1) :=
    (F.map_face true (s+1) y).symm.trans
      ((congrArg F.toFun hyz).trans (F.map_face false (s+1) z))
  obtain ⟨U, V, hUV, he, horder⟩ :=
    B.two_atom_lowering a b s hp hq (F.toFun y) (F.toFun z) hfyz hy hz hdis
  have hU : B.AboveAtomOrZero (s+1) U := by
    rcases horder with ⟨hU, _⟩ | ⟨hU, _⟩
    · exact Or.inr ⟨⟨p,a⟩, hp, hU⟩
    · exact Or.inr ⟨⟨q,b⟩, hq, hU⟩
  have hV : B.AboveAtomOrZero (s+1) V := by
    rcases horder with ⟨_, hV⟩ | ⟨_, hV⟩
    · exact Or.inr ⟨⟨q,b⟩, hq, hV⟩
    · exact Or.inr ⟨⟨p,a⟩, hp, hV⟩
  obtain ⟨u, hu, _⟩ := hunique U hU
  obtain ⟨v, hv, _⟩ := hunique V hV
  have huv := B.matching_of_unique_lower_faces F (s+1) s (Nat.le_succ s)
    hunique u v U V hu hv hUV
  have hfuv : (F.toFun u).face true s = (F.toFun v).face false s :=
    (F.map_face true s u).symm.trans
      ((congrArg F.toFun huv).trans (F.map_face false s v))
  have him : Cell.comp (F.toFun u) (F.toFun v) s hfuv = Cell.comp U V s hUV := by
    congr 1
  have htotal : F.toFun (C.comp s u v huv) = F.toFun (C.comp (s+1) y z hyz) :=
    (F.map_comp s u v huv hfuv).trans
      (him.trans (he.trans (F.map_comp (s+1) y z hyz hfyz).symm))
  have hylevel : B.AboveAtomOrZero (s+1) (F.toFun y) := Or.inr ⟨⟨p,a⟩, hp, hy⟩
  have hzlevel : B.AboveAtomOrZero (s+1) (F.toFun z) := Or.inr ⟨⟨q,b⟩, hq, hz⟩
  rcases horder with ⟨hUa, hVb⟩ | ⟨hUb, hVa⟩
  · have hsource := B.reflect_forward_whiskers F (Nat.lt_succ_self s) hunique
      y z u v hyz huv hylevel hzlevel htotal (fun n hn side =>
        (hy n hn side).trans ((hUa n hn side).symm.trans
          (congrArg (fun X : Cell K => X.table side n) hu).symm))
    refine ⟨C.leftWhisker (Nat.lt_succ_self s) u v huv false,
      C.rightWhisker (Nat.lt_succ_self s) u v huv true,
      C.whiskered_reverse_matching (Nat.lt_succ_self s) u v huv,
      (C.whiskered_reverse_comp (Nat.lt_succ_self s) u v huv).trans hsource.symm, ?_, ?_⟩
    · intro n hn side
      exact (leftWhisker_table_above F (Nat.lt_succ_self s) u v huv false n hn side).trans
        ((congrArg (fun X : Cell K => X.table side n) hv).trans (hVb n hn side))
    · intro n hn side
      exact (rightWhisker_table_above F (Nat.lt_succ_self s) u v huv true n hn side).trans
        ((congrArg (fun X : Cell K => X.table side n) hu).trans (hUa n hn side))
  · have hsource := B.reflect_reverse_whiskers F (Nat.lt_succ_self s) hunique
      y z u v hyz huv hylevel hzlevel htotal (fun n hn side =>
        (hy n hn side).trans ((hVa n hn side).symm.trans
          (congrArg (fun X : Cell K => X.table side n) hv).symm))
    refine ⟨C.rightWhisker (Nat.lt_succ_self s) u v huv false,
      C.leftWhisker (Nat.lt_succ_self s) u v huv true,
      C.whiskered_forward_matching (Nat.lt_succ_self s) u v huv,
      (C.whiskered_forward_comp (Nat.lt_succ_self s) u v huv).trans hsource.symm, ?_, ?_⟩
    · intro n hn side
      exact (rightWhisker_table_above F (Nat.lt_succ_self s) u v huv false n hn side).trans
        ((congrArg (fun X : Cell K => X.table side n) hu).trans (hUb n hn side))
    · intro n hn side
      exact (leftWhisker_table_above F (Nat.lt_succ_self s) u v huv true n hn side).trans
        ((congrArg (fun X : Cell K => X.table side n) hv).trans (hVa n hn side))

/-- The height order supplies the reverse disjointness condition. A degree
zero inversion is impossible by augmentation, so this applies uniformly
to every composition degree. -/
theorem adjacent_transpose_of_height {C : StrictOmegaCategory.{0}}
    (F : C ⟶ K.realization) (r : ℕ)
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    (a b : B.AtomIndex) (ha : r < a.1) (hb : r < b.1)
    (hheight : B.atomHeight b ≤ B.atomHeight a)
    (y z : C) (hyz : C.target r y = C.source r z)
    (hy : ∀ n, r < n → ∀ side, (F.toFun y).table side n = (B.atomCell a).table side n)
    (hz : ∀ n, r < n → ∀ side, (F.toFun z).table side n = (B.atomCell b).table side n) :
    ∃ (y' z' : C) (h : C.target r y' = C.source r z'),
      C.comp r y' z' h = C.comp r y z hyz ∧
      (∀ n, r < n → ∀ side, (F.toFun y').table side n = (B.atomCell b).table side n) ∧
      (∀ n, r < n → ∀ side, (F.toFun z').table side n = (B.atomCell a).table side n) := by
  have hd : ∀ e, B.coordinates r ((B.atom a.1 a.2).table true r) e = 0 ∨
      B.coordinates r ((B.atom b.1 b.2).table false r) e = 0 := by
    intro e
    exact (B.disjoint b.2 a.2 hb ha hheight e).symm
  cases r with
  | zero =>
    have hmatch : (F.toFun y).face true 0 = (F.toFun z).face false 0 :=
      (F.map_face true 0 y).symm.trans
        ((congrArg F.toFun hyz).trans (F.map_face false 0 z))
    have hp := B.two_atom_degree_positive a.2 b.2 0 ha hb (F.toFun y) (F.toFun z)
      hmatch (hy 1 (by omega) false) (hz 1 (by omega) false) hd
    omega
  | succ s =>
    exact B.adjacent_transpose F s hunique a.2 b.2 ha hb y z hyz hy hz hd

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Actual strict composites with retained atom labels

The labels record the upper tables of the actual source factors. This
relation is used only to normalize already constructed composites.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

inductive AtomComposite {C : StrictOmegaCategory.{0}} (F : C ⟶ K.realization) (r : ℕ) :
    List B.AtomIndex → C → Prop
  | singleton (a : B.AtomIndex) (x : C) (ha : r < a.1)
      (hx : ∀ n, r < n → ∀ side, (F.toFun x).table side n = (B.atomCell a).table side n) :
      AtomComposite F r [a] x
  | cons (a : B.AtomIndex) (x : C) {as : List B.AtomIndex} {y : C}
      (ha : r < a.1)
      (hx : ∀ n, r < n → ∀ side, (F.toFun x).table side n = (B.atomCell a).table side n)
      (tail : AtomComposite F r as y) (hxy : C.target r x = C.source r y) :
      AtomComposite F r (a :: as) (C.comp r x y hxy)

namespace AtomComposite

variable {B} {C : StrictOmegaCategory.{0}} {F : C ⟶ K.realization} {r : ℕ}

theorem nonempty {as : List B.AtomIndex} {x : C} (h : B.AtomComposite F r as x) : as ≠ [] := by
  cases h <;> simp

theorem degree {as : List B.AtomIndex} {x : C} (h : B.AtomComposite F r as x) :
    ∀ a ∈ as, r < a.1 := by
  induction h with
  | singleton a x ha hx => simpa only [List.mem_singleton] using
      (fun b (hb : b = a) => hb.symm ▸ ha)
  | cons a x ha hx tail hxy ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ih b hb

theorem to_compositeList {as : List B.AtomIndex} {x : C} (h : B.AtomComposite F r as x) :
    ∃ xs : List C, CompositeList C r xs x ∧
      List.Forall₂ (fun a (y : C) => ∀ n, r < n → ∀ side,
        (F.toFun y).table side n = (B.atomCell a).table side n) as xs := by
  induction h with
  | singleton a x ha hx => exact ⟨[x], .singleton x, .cons hx .nil⟩
  | cons a x ha hx tail hxy ih =>
    obtain ⟨xs, hxs, hrel⟩ := ih
    exact ⟨x :: xs, .cons x hxs hxy, .cons hx hrel⟩

theorem of_compositeList {xs : List C} {x : C} (h : CompositeList C r xs x)
    (hatoms : ∀ y ∈ xs, ∃ a : B.AtomIndex, r < a.1 ∧
      ∀ n, r < n → ∀ side, (F.toFun y).table side n = (B.atomCell a).table side n) :
    ∃ as, B.AtomComposite F r as x := by
  induction h with
  | singleton x =>
    obtain ⟨a, ha, hx⟩ := hatoms x (by simp)
    exact ⟨[a], .singleton a x ha hx⟩
  | @cons x xs y hy hxy ih =>
    obtain ⟨a, ha, hx⟩ := hatoms x (by simp)
    obtain ⟨as, has⟩ := ih (fun z hz => hatoms z (by simp [hz]))
    exact ⟨a :: as, .cons a x ha hx has hxy⟩

theorem upper_sum {as : List B.AtomIndex} {x : C} (h : B.AtomComposite F r as x)
    (n : ℕ) (hn : r < n) (side : Bool) :
    (F.toFun x).table side n = (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n := by
  obtain ⟨xs, hxs, hrel⟩ := h.to_compositeList
  have hr : List.Forall₂ (fun a (Y : Cell K) =>
      ∀ n, r < n → ∀ side, Y.table side n = (B.atomCell a).table side n)
      as (xs.map F.toFun) := List.forall₂_map_right_iff.mpr hrel
  have hs : (as.map (fun a => (B.atomCell a).table side n)).sum =
      (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n := by
    simp only [Cell.PositiveTable.ofCells_table, List.map_map, Function.comp_def]
  exact (Cell.compositeList_table (hxs.map F) n hn side).trans
    ((B.related_table_sum r hr n hn side).trans hs)

end AtomComposite
end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Sorting the labels of an actual strict factorization

Adjacent interchange moves a height-minimal chosen label to the front.
Repeating this operation realizes any prescribed height-sorted permutation
without changing the actual source cell.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis.AtomComposite

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} {B : OrderedAtomBasis K}
variable {C : StrictOmegaCategory.{0}} {F : C ⟶ K.realization} {r : ℕ}

theorem swap_first
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    {a b : B.AtomIndex} {as : List B.AtomIndex} {X : C}
    (h : B.AtomComposite F r (a :: b :: as) X)
    (hheight : B.atomHeight b ≤ B.atomHeight a) :
    B.AtomComposite F r (b :: a :: as) X := by
  cases h with
  | @cons a x bs y ha hx tail hxy =>
    cases tail with
    | singleton b y hb hy =>
      obtain ⟨u, v, huv, he, hu, hv⟩ :=
        B.adjacent_transpose_of_height F r hunique a b ha hb hheight x y hxy hx hy
      exact he ▸ AtomComposite.cons b u hb hu (.singleton a v ha hv) huv
    | @cons b y as z hb hy tail hyz =>
      have hab : C.target r x = C.source r y := hxy.trans (C.source_comp r y z hyz)
      obtain ⟨u, v, huv, he, hu, hv⟩ :=
        B.adjacent_transpose_of_height F r hunique a b ha hb hheight x y hab hx hy
      have hvz : C.target r v = C.source r z :=
        (C.target_comp r u v huv).symm.trans
          ((congrArg (C.target r) he).trans ((C.target_comp r x y hab).trans hyz))
      have hleft : C.target r (C.comp r u v huv) = C.source r z :=
        (C.target_comp r u v huv).trans hvz
      have hright : C.target r u = C.source r (C.comp r v z hvz) :=
        huv.trans (C.source_comp r v z hvz).symm
      have hold : C.target r (C.comp r x y hab) = C.source r z :=
        (C.target_comp r x y hab).trans hyz
      have heq : C.comp r u (C.comp r v z hvz) hright =
          C.comp r x (C.comp r y z hyz) hxy := by
        calc
          _ = C.comp r (C.comp r u v huv) z hleft :=
            (C.assoc r u v z huv hvz hleft hright).symm
          _ = C.comp r (C.comp r x y hab) z hold := by congr 1
          _ = _ := C.assoc r x y z hab hyz hold hxy
      exact heq ▸ AtomComposite.cons b u hb hu (.cons a v ha hv tail hvz) hright

theorem move_minimal_first
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    {as : List B.AtomIndex} {X : C} (h : B.AtomComposite F r as X)
    (a : B.AtomIndex) (ha : a ∈ as)
    (hmin : ∀ b ∈ as, B.atomHeight a ≤ B.atomHeight b) :
    ∃ bs, B.AtomComposite F r (a :: bs) X ∧ (a :: bs).Perm as := by
  induction h generalizing a with
  | singleton b x hb hx =>
    have hab : a = b := List.mem_singleton.mp ha
    subst a
    exact ⟨[], .singleton b x hb hx, .refl _⟩
  | @cons b x bs y hb hx tail hxy ih =>
    by_cases hab : a = b
    · subst a
      exact ⟨bs, .cons b x hb hx tail hxy, .refl _⟩
    · have hat : a ∈ bs := (List.mem_cons.mp ha).resolve_left hab
      obtain ⟨cs, hc, hp⟩ := ih a hat (fun d hd => hmin d (List.mem_cons_of_mem b hd))
      have hs := swap_first hunique (AtomComposite.cons b x hb hx hc hxy)
        (hmin b (List.mem_cons_self))
      exact ⟨b :: cs, hs, (List.Perm.swap b a cs).trans (hp.cons b)⟩

theorem of_sorted_perm
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    {as bs : List B.AtomIndex} {X : C} (h : B.AtomComposite F r as X)
    (hp : as.Perm bs) (hs : bs.Pairwise (fun a b => B.atomHeight a ≤ B.atomHeight b)) :
    B.AtomComposite F r bs X := by
  induction bs generalizing as X with
  | nil =>
    have ha : as = [] := List.perm_nil.mp hp
    exact (h.nonempty ha).elim
  | cons b bs ih =>
    have hb : b ∈ as := hp.mem_iff.mpr List.mem_cons_self
    have hmin : ∀ a ∈ as, B.atomHeight b ≤ B.atomHeight a := by
      intro a ha
      rcases List.mem_cons.mp (hp.mem_iff.mp ha) with rfl | ha
      · exact le_rfl
      · exact (List.pairwise_cons.mp hs).1 a ha
    obtain ⟨cs, hc, hp'⟩ := move_minimal_first hunique h b hb hmin
    have hperm : cs.Perm bs := (hp'.trans hp).cons_inv
    cases hc with
    | singleton b x hb hx =>
      have hbs : bs = [] := List.perm_nil.mp hperm.symm
      subst bs
      exact .singleton b _ hb hx
    | @cons b x cs y hb hx tail hxy =>
      exact .cons b x hb hx (ih tail hperm (List.pairwise_cons.mp hs).2) hxy

end Thomason.Construction.DirectedComplex.OrderedAtomBasis.AtomComposite

end

section

/-! # A fixed ordered atom string has a unique lift

Binary positive-table factor uniqueness identifies the two image factors.
Preceding-level uniqueness identifies the first source factor, and induction
identifies the remaining string.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis.AtomComposite

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} {B : OrderedAtomBasis K}
variable {C : StrictOmegaCategory.{0}} {F : C ⟶ K.realization} {r : ℕ}

theorem total_unique
    (hunique : ∀ X, B.AboveAtomOrZero r X → ∃! x : C, F.toFun x = X)
    {as : List B.AtomIndex} {x y : C}
    (hx : B.AtomComposite F r as x) (hy : B.AtomComposite F r as y)
    (he : F.toFun x = F.toFun y) : x = y := by
  induction hx generalizing y with
  | singleton a x ha hx =>
    obtain ⟨_, _, hu⟩ := hunique (F.toFun x) (Or.inr ⟨a, ha, hx⟩)
    exact (hu x rfl).trans (hu y he.symm).symm
  | @cons a x as z ha hx tail hxz ih =>
    cases hy with
    | singleton a y ha' hy => exact (tail.nonempty rfl).elim
    | @cons a y as w ha' hy tail' hyw =>
      have hfxz : (F.toFun x).face true r = (F.toFun z).face false r :=
        (F.map_face true r x).symm.trans
          ((congrArg F.toFun hxz).trans (F.map_face false r z))
      have hfyw : (F.toFun y).face true r = (F.toFun w).face false r :=
        (F.map_face true r y).symm.trans
          ((congrArg F.toFun hyw).trans (F.map_face false r w))
      have htot : Cell.comp (F.toFun x) (F.toFun z) r hfxz =
          Cell.comp (F.toFun y) (F.toFun w) r hfyw :=
        (F.map_comp r x z hxz hfxz).symm.trans (he.trans (F.map_comp r y w hyw hfyw))
      have hparts := Cell.factors_unique_of_above _ _ _ _ r hfxz hfyw htot
        (fun n hn side => (hx n hn side).trans (hy n hn side).symm)
      obtain ⟨_, _, hu⟩ := hunique (F.toFun x) (Or.inr ⟨a, ha, hx⟩)
      have hxy : x = y := (hu x rfl).trans (hu y hparts.1.symm).symm
      have hzw : z = w := ih tail' hparts.2
      subst y
      subst w
      rfl

end Thomason.Construction.DirectedComplex.OrderedAtomBasis.AtomComposite

end

section

/-! # The actual interval cylinder and path-space adjunction

Only the interval needed for realization and Gray-prism homotopies is used.
Its cylinder preserves colimits by an explicit compact-open adjunction.
-/

namespace Thomason.Construction.TopologicalInterval

open CategoryTheory CategoryTheory.Limits

universe u

/-- Product with the ordinary unit interval. -/
def cylinder : TopCat.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of (X × unitInterval)
  map f := TopCat.ofHom ⟨fun p => (f.hom p.1, p.2), by fun_prop⟩

/-- Paths with the compact-open topology. -/
def pathSpace : TopCat.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of C(unitInterval, X)
  map f := TopCat.ofHom ⟨fun p => f.hom.comp p, ContinuousMap.continuous_postcomp f.hom⟩

/-- Currying and uncurrying are inverse on actual continuous maps. -/
def homEquiv (X Y : TopCat.{u}) : (cylinder.obj X ⟶ Y) ≃ (X ⟶ pathSpace.obj Y) where
  toFun f := TopCat.ofHom f.hom.curry
  invFun f := TopCat.ofHom f.hom.uncurry
  left_inv f := by apply TopCat.hom_ext; apply ContinuousMap.ext; intro p; rfl
  right_inv f := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    rfl

/-- The interval cylinder is left adjoint to compact-open paths. -/
def adjunction : cylinder.{u} ⊣ pathSpace :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      apply ContinuousMap.ext
      intro t
      rfl }

instance : cylinder.{u}.IsLeftAdjoint := adjunction.isLeftAdjoint

instance : PreservesColimitsOfSize.{0,0} cylinder.{u} :=
  adjunction.leftAdjoint_preservesColimits

/-- The section at a chosen interval point. -/
def sectionAt (X : TopCat.{u}) (t : unitInterval) : X ⟶ cylinder.obj X :=
  TopCat.ofHom ⟨fun x => (x, t), by fun_prop⟩

/-- The cylinder projection. -/
def projection (X : TopCat.{u}) : cylinder.obj X ⟶ X :=
  TopCat.ofHom ⟨Prod.fst, by fun_prop⟩

@[simp]
theorem section_projection (X : TopCat.{u}) (t : unitInterval) :
    sectionAt X t ≫ projection X = 𝟙 X := rfl

/-- A straight-line deformation to the section, stationary on that section. -/
noncomputable def sectionDeformation (X : TopCat.{u}) (t : unitInterval) :
    ((sectionAt X t).hom.comp (projection X).hom).HomotopyRel
      (ContinuousMap.id (X × unitInterval)) (Set.range (sectionAt X t).hom) where
  toFun p := (p.2.1, ⟨(1 - (p.1 : ℝ)) * t + p.1 * p.2.2,
    by
      have hs := p.1.property
      have ht := t.property
      have hz := p.2.2.property
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) ht.1)
          (mul_nonneg hs.1 hz.1)
      · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2),
          mul_nonneg hs.1 (sub_nonneg.mpr hz.2)]⟩)
  continuous_toFun := by fun_prop
  map_zero_left p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (0 : ℝ)) * t + 0 * p.2 = (t : ℝ)
      ring
  map_one_left p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (1 : ℝ)) * t + 1 * p.2 = (p.2 : ℝ)
      ring
  prop' s p hp := by
    obtain ⟨x, rfl⟩ := hp
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (s : ℝ)) * t + s * t = (t : ℝ)
      ring

/-- Every cylinder section satisfies the actual weak-equivalence definition. -/
theorem section_weak (X : TopCat.{u}) (t : unitInterval) :
    topologicalWeakEquivalences (sectionAt X t) :=
  weakEquivalence_of_strongDeformationRetract _ _ rfl (sectionDeformation X t)

/-- The cylinder projection is weak at every source basepoint. -/
theorem projection_weak (X : TopCat.{u}) : topologicalWeakEquivalences (projection X) := by
  constructor
  · have hs := (section_weak X 0).1
    apply (hs.of_comp_iff _).mp
    rw [← HomotopyMaps.componentsMap_comp]
    exact IsWeakHomotopyEquivalence.id.1
  · intro n p
    rcases p with ⟨x, t⟩
    have hs := (section_weak X t).2 n x
    apply (hs.of_comp_iff _).mp
    have hcomp := HomotopyMaps.groupMap_comp (sectionAt X t).hom (projection X).hom (n+1) x
    have hid : Function.Bijective (HomotopyMaps.groupMap
        ((projection X).hom.comp (sectionAt X t).hom) (n+1) x) :=
      IsWeakHomotopyEquivalence.id.2 n x
    exact hcomp ▸ hid

end Thomason.Construction.TopologicalInterval

end

end OAI
