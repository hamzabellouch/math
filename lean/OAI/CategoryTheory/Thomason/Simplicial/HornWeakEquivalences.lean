import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Gray.TripleGlobeAtoms
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizedSimplexWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.TerminalConeUniversal
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Strict.FiniteLabelledPresentation
import OAI.CategoryTheory.Thomason.Strict.StrictTerminalConeFunctor
import OAI.CategoryTheory.Thomason.Strict.UnderlyingCategory
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

namespace OAI

section

/-! # Appended greatest vertices in the ordinary nerve

The cone construction is natural on the actual category of simplices.
This supplies the indexing data for the topological cone prisms.
-/

namespace Thomason.Construction.ConePrism

open CategoryTheory Opposite NormalizedSimplexIdentities

variable {P : Type} [PartialOrder P] (v : P) (hv : ∀ x, x ≤ v)

/-- Append the greatest vertex to an original nerve simplex. -/
noncomputable abbrev coneIndex (j : CostructuredArrow SSet.stdSimplex (nerve P)) :
    CostructuredArrow SSet.stdSimplex (nerve P) :=
  CostructuredArrow.mk (SSet.yonedaEquiv.symm
    (orderSimplex (append (simplexOrder (SSet.yonedaEquiv j.hom)) v (hv _))))

/-- Appending commutes with all ordinal operators after extending their final vertex. -/
theorem append_precomp {m n : ℕ} (s : Fin (n+1) →o P)
    (f : Fin (m+1) →o Fin (n+1)) :
    (append s v (hv _)).comp (ordinalMap f) = append (s.comp f) v (hv _) := by
  apply DFunLike.ext
  intro k
  induction k using Fin.lastCases with
  | last => simp only [OrderHom.comp_coe, Function.comp_apply, ordinalMap_last, append_last]
  | cast k => simp only [OrderHom.comp_coe, Function.comp_apply, ordinalMap_castSucc,
      append_castSucc]

/-- The actual map of cone simplices extending an original simplex morphism. -/
noncomputable def coneMap {j k : CostructuredArrow SSet.stdSimplex (nerve P)} (f : j ⟶ k) :
    coneIndex v hv j ⟶ coneIndex v hv k :=
  CostructuredArrow.homMk (SimplexCategory.Hom.mk (ordinalMap f.left.toOrderHom)) (by
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality]
    change orderSimplex ((append (simplexOrder (SSet.yonedaEquiv k.hom)) v (hv _)).comp
      (ordinalMap f.left.toOrderHom)) =
      orderSimplex (append (simplexOrder (SSet.yonedaEquiv j.hom)) v (hv _))
    rw [append_precomp]
    have hs := simplexOrder_precomp k.hom f.left
    rw [CostructuredArrow.w f] at hs
    rw [hs])

/-- The original simplex includes as the face omitting the new final vertex. -/
noncomputable def faceMap (j : CostructuredArrow SSet.stdSimplex (nerve P)) :
    j ⟶ coneIndex v hv j :=
  CostructuredArrow.homMk
    (SimplexCategory.Hom.mk (Fin.castSuccOrderEmb.toOrderHom)) (by
      apply SSet.yonedaEquiv.injective
      rw [← SSet.yonedaEquiv_naturality]
      change orderSimplex ((append (simplexOrder (SSet.yonedaEquiv j.hom)) v (hv _)).comp
        Fin.castSuccOrderEmb.toOrderHom) = SSet.yonedaEquiv j.hom
      have he : (append (simplexOrder (SSet.yonedaEquiv j.hom)) v (hv _)).comp
          Fin.castSuccOrderEmb.toOrderHom = simplexOrder (SSet.yonedaEquiv j.hom) := by
        apply DFunLike.ext
        intro k
        exact append_castSucc _ v (hv _) k
      rw [he, orderSimplex_simplexOrder])

/-- The chosen greatest vertex, as an actual zero-simplex. -/
noncomputable abbrev vertexIndex : CostructuredArrow SSet.stdSimplex (nerve P) :=
  CostructuredArrow.mk (SSet.yonedaEquiv.symm
    (orderSimplex (OrderHom.const (Fin 1) v)))

/-- The greatest vertex is the new final vertex of each cone simplex. -/
noncomputable def vertexMap (j : CostructuredArrow SSet.stdSimplex (nerve P)) :
    vertexIndex v ⟶ coneIndex v hv j :=
  CostructuredArrow.homMk (SimplexCategory.Hom.mk
    (OrderHom.const (Fin 1) (Fin.last (j.left.len+1)))) (by
      apply SSet.yonedaEquiv.injective
      rw [← SSet.yonedaEquiv_naturality]
      apply nerve.ext_of_isThin
      funext k
      exact append_last _ _ _)

/-- The cone on the greatest vertex collapses back to that vertex. -/
noncomputable def collapseVertex : coneIndex v hv (vertexIndex v) ⟶ vertexIndex v :=
  CostructuredArrow.homMk (SimplexCategory.Hom.mk
    (OrderHom.const (Fin 2) (0 : Fin 1))) (by
      apply SSet.yonedaEquiv.injective
      rw [← SSet.yonedaEquiv_naturality]
      apply nerve.ext_of_isThin
      funext k
      fin_cases k <;> rfl)

end Thomason.Construction.ConePrism

end

section

/-! # Canonical maps into the full sieve fibres

These maps retain the original categorified inclusion on every cell.
No full-faithfulness or invertibility is assumed in their construction.
-/

namespace Thomason.Construction

open CategoryTheory StrictOmegaCategory

namespace StrictOmegaCategory

variable {C D : StrictOmegaCategory.{0}}

/-- Factor a strict functor whose entire image has a fixed label through the full fibre. -/
def liftToLabelFiber (p : C ⟶ StrictPoset.category (Fin 2)) (e : Fin 2)
    (f : D ⟶ C) (hf : ∀ x, p.toFun (f.toFun x) = StrictPoset.identity e) :
    D ⟶ labelFiber p e where
  toFun x := ⟨f.toFun x, (fullCell_label_iff p e _).mpr (hf x)⟩
  map_face a n x := Subtype.ext (f.map_face a n x)
  map_comp n x y hxy _ := Subtype.ext (f.map_comp n x y hxy _)

theorem liftToLabelFiber_inclusion (p : C ⟶ StrictPoset.category (Fin 2)) (e : Fin 2)
    (f : D ⟶ C) (hf : ∀ x, p.toFun (f.toFun x) = StrictPoset.identity e) :
    liftToLabelFiber p e f hf ≫ labelFiberInclusion p e = f := by
  apply Hom.ext
  rfl

/-- Compatibility of a canonical fibre factor with precomposition, on all cells. -/
theorem liftToLabelFiber_precomp (p : C ⟶ StrictPoset.category (Fin 2)) (e : Fin 2)
    (f : D ⟶ C) (hf : ∀ x, p.toFun (f.toFun x) = StrictPoset.identity e)
    {B : StrictOmegaCategory.{0}} (g : B ⟶ D) :
    g ≫ liftToLabelFiber p e f hf =
      liftToLabelFiber p e (g ≫ f) (fun x => hf (g.toFun x)) := by
  apply Hom.ext
  rfl

end StrictOmegaCategory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- A monotone map landing in the sieve sends every categorified cell into its full zero-fibre. -/
theorem posetMap_membership_zero {E P : Type} [PartialOrder E] [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) (f : E →o P) (hf : ∀ x, f x ∈ A)
    (x : h.categorification.obj (nerve E)) :
    (h.membershipLabel A hA).toFun ((h.posetMap f).toFun x) = StrictPoset.identity 0 := by
  apply (h.membershipLabel_zero_iff A hA _).mpr
  constructor
  all_goals
    rw [← (h.posetMap f).object_boundary, h.posetObjectsEquiv_naturality]
    exact hf _

/-- The canonical strict map into a categorified sieve's actual full fibre. -/
noncomputable def posetFiberMap {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) :
    h.categorification.obj (nerve A) ⟶ labelFiber (h.membershipLabel A hA) 0 :=
  liftToLabelFiber (h.membershipLabel A hA) 0 (h.posetMap (subposetInclusion A))
    (h.posetMap_membership_zero A hA _ (fun x => x.property))

/-- The factor is the original inclusion after forgetting the fibre. -/
theorem posetFiberMap_inclusion {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) :
    h.posetFiberMap A hA ≫ labelFiberInclusion (h.membershipLabel A hA) 0 =
      h.posetMap (subposetInclusion A) := by
  apply Hom.ext
  rfl

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Finite object names are natural for the original categorified monotone maps. -/
theorem posetObjectsEquiv_naturality {E F : Type} [PartialOrder E] [PartialOrder F]
    (f : E →o F) (x : Objects ((r.categorification h).obj (nerve E)).val) :
    r.posetObjectsEquiv h F ((r.reflect.map (h.posetMap f)).toOneFunctor.obj x) =
      f (r.posetObjectsEquiv h E x) := by
  have he := congrArg (fun k : ((r.categorification h).obj (nerve E)).val ⟶
    StrictPoset.category F => (k.toFun x.val).first) (r.posetEvaluation_naturality h f)
  have hleft := congrArg (fun z : StrictPoset.Cell F => z.first)
    (r.posetEvaluation_object h ((r.reflect.map (h.posetMap f)).toOneFunctor.obj x))
  have hright := congrArg (fun z : StrictPoset.Cell E => f z.first)
    (r.posetEvaluation_object h x)
  exact hleft.symm.trans (he.trans hright)

/-- The finite-dimensional full zero-fibre criterion holds on every cell. -/
theorem membershipLabel_zero_iff {E : Type} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (x : ((r.categorification h).obj (nerve E)).val) :
    (r.membershipLabel h A hA).toFun x = StrictPoset.identity 0 ↔
      r.posetObjectsEquiv h E (((r.categorification h).obj (nerve E)).val.boundaryObject false x) ∈ A ∧
      r.posetObjectsEquiv h E (((r.categorification h).obj (nerve E)).val.boundaryObject true x) ∈ A := by
  have hs := r.membershipLabel_object_zero_iff h A hA
    (((r.categorification h).obj (nerve E)).val.boundaryObject false x)
  have ht := r.membershipLabel_object_zero_iff h A hA
    (((r.categorification h).obj (nerve E)).val.boundaryObject true x)
  exact (fullCell_label_iff (r.membershipLabel h A hA) 0 x).symm.trans (and_congr hs ht)

/-- Reflected monotone maps landing in a sieve land in its actual full zero-fibre. -/
theorem posetMap_membership_zero {E P : Type} [PartialOrder E] [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) (f : E →o P) (hf : ∀ x, f x ∈ A)
    (x : ((r.categorification h).obj (nerve E)).val) :
    (r.membershipLabel h A hA).toFun ((r.reflect.map (h.posetMap f)).toFun x) =
      StrictPoset.identity 0 := by
  apply (r.membershipLabel_zero_iff h A hA _).mpr
  let f' : ((r.categorification h).obj (nerve E)).val ⟶
      ((r.categorification h).obj (nerve P)).val := r.reflect.map (h.posetMap f)
  have hb (b : Bool) : r.posetObjectsEquiv h P
      (((r.categorification h).obj (nerve P)).val.boundaryObject b (f'.toFun x)) ∈ A := by
    have he := congrArg (r.posetObjectsEquiv h P) (f'.object_boundary b x)
    have hn := r.posetObjectsEquiv_naturality h f
      (((r.categorification h).obj (nerve E)).val.boundaryObject b x)
    exact (congrArg (fun z => z ∈ A) (he.symm.trans hn)).mpr (hf _)
  exact ⟨hb false, hb true⟩

/-- The corresponding canonical map in the actual positive finite category. -/
noncomputable def posetFiberMap {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) :
    (r.categorification h).obj (nerve A) ⟶
      (finiteLabelFiberFunctor n 0).obj (Over.mk (r.membershipLabel h A hA)) :=
  liftToLabelFiber (r.membershipLabel h A hA) 0 (r.reflect.map (h.posetMap (subposetInclusion A)))
    (r.posetMap_membership_zero h A hA _ (fun x => x.property))

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # The canonical full one-fibre map for a categorified cosieve -/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory StrictOmegaCategory

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The complement's membership label detects the objects of the cosieve at one. -/
theorem cosieveMembershipLabel_object {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) (x : Objects (h.categorification.obj (nerve P))) :
    (h.membershipLabel Aᶜ hA.compl).toFun x.val = StrictPoset.identity 1 ↔
      h.posetObjectsEquiv P x ∈ A := by
  rw [h.membershipLabel_object]
  constructor
  · intro he
    exact (cosieveCharacteristic_one_iff A hA _).mp
      (congrArg StrictPoset.Cell.first he)
  · intro hx
    exact congrArg StrictPoset.identity ((cosieveCharacteristic_one_iff A hA _).mpr hx)

theorem cosieveMembershipLabel_one_iff {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) (x : h.categorification.obj (nerve P)) :
    (h.membershipLabel Aᶜ hA.compl).toFun x = StrictPoset.identity 1 ↔
      h.posetObjectsEquiv P ((h.categorification.obj (nerve P)).boundaryObject false x) ∈ A ∧
      h.posetObjectsEquiv P ((h.categorification.obj (nerve P)).boundaryObject true x) ∈ A :=
  (fullCell_label_iff (h.membershipLabel Aᶜ hA.compl) 1 x).symm.trans
    (and_congr
      (h.cosieveMembershipLabel_object A hA
        ((h.categorification.obj (nerve P)).boundaryObject false x))
      (h.cosieveMembershipLabel_object A hA
        ((h.categorification.obj (nerve P)).boundaryObject true x)))

theorem posetMap_cosieveMembership_one {E P : Type} [PartialOrder E] [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) (f : E →o P) (hf : ∀ x, f x ∈ A)
    (x : h.categorification.obj (nerve E)) :
    (h.membershipLabel Aᶜ hA.compl).toFun ((h.posetMap f).toFun x) = StrictPoset.identity 1 := by
  apply (h.cosieveMembershipLabel_one_iff A hA _).mpr
  constructor
  all_goals
    rw [← (h.posetMap f).object_boundary, h.posetObjectsEquiv_naturality]
    exact hf _

noncomputable def cosievePosetFiberMap {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) :
    h.categorification.obj (nerve A) ⟶ labelFiber (h.membershipLabel Aᶜ hA.compl) 1 :=
  liftToLabelFiber (h.membershipLabel Aᶜ hA.compl) 1 (h.posetMap (subposetInclusion A))
    (h.posetMap_cosieveMembership_one A hA _ (fun x => x.property))

theorem cosievePosetFiberMap_inclusion {P : Type} [PartialOrder P]
    (A : Set P) (hA : IsUpperSet A) :
    h.cosievePosetFiberMap A hA ≫ labelFiberInclusion (h.membershipLabel Aᶜ hA.compl) 1 =
      h.posetMap (subposetInclusion A) := by
  apply Hom.ext
  rfl

end Thomason.Construction.NormalizedSimplexIdentities

end

section

/-! # Simplexes contained entirely in a cosieve -/

namespace Thomason.Construction.CosieveSimplex

open CategoryTheory StrictOmegaCategory

variable {P : Type} [PartialOrder P] (A : Set P) (hA : IsUpperSet A)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- Every cell of a simplex in the cosieve belongs to its full one fibre. -/
noncomputable def whole {m : ℕ} (s : Fin (m+1) →o A) :
    h.object m ⟶ labelFiber (label A hA ((subposetInclusion A).comp s) h) 1 where
  toFun x := ⟨x, (SimplexComplex.binaryLabel_fullCell_iff h
    ((cosieveCharacteristic A hA).comp ((subposetInclusion A).comp s)) 1 x).mpr
      ⟨(cosieveCharacteristic_one_iff A hA _).mpr (s _).property,
       (cosieveCharacteristic_one_iff A hA _).mpr (s _).property⟩⟩
  map_face _ _ _ := Subtype.ext rfl
  map_comp _ _ _ _ _ := Subtype.ext rfl

omit [StrictColimitsInput] in
/-- The clamped vertex map of a simplex already in the cosieve is unchanged. -/
theorem whole_cut_clamp {m : ℕ} (s : Fin (m+1) →o A)
    (c : Cut A ((subposetInclusion A).comp s)) : c.clamp = s := by
  apply DFunLike.ext
  intro i
  apply Subtype.ext
  exact c.clamp_of_mem i (s i).property

/-- On an entire cosieve simplex, the clamping inverse is its original colimit leg. -/
theorem whole_back {m : ℕ} (s : Fin (m+1) →o A) :
    whole A hA h s ≫ back A hA h ((subposetInclusion A).comp s) = h.posetLeg s := by
  let c := cut A hA ((subposetInclusion A).comp s) ⟨0, (s 0).property⟩
  rw [back_eq_cut A hA h _ c]
  change (whole A hA h s ≫ labelFiberInclusion _ 1) ≫ h.posetLeg c.clamp = _
  have he : whole A hA h s ≫ labelFiberInclusion _ 1 = 𝟙 (h.object _) := by
    apply Hom.ext
    rfl
  rw [he, Category.id_comp, whole_cut_clamp A s c]

end Thomason.Construction.CosieveSimplex

end

section

/-! # Joint labels for full intersections

Taking the maximum of two binary labels represents the intersection of
their zero-fibres on every strict cell. This uses the actual ordered-label
category, so it also records intersections after arbitrary attachments.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

variable {C D : StrictOmegaCategory.{0}}

/-- Combine the two ordered endpoint labels by maximum. -/
def maxLabel (p q : C ⟶ StrictPoset.category (Fin 2)) :
    C ⟶ StrictPoset.category (Fin 2) where
  toFun x := ⟨max (p.toFun x).first (q.toFun x).first,
    max (p.toFun x).last (q.toFun x).last,
    max_le_max (p.toFun x).ordered (q.toFun x).ordered⟩
  map_face a n x := by
    change (⟨max (p.toFun (C.face a n x)).first (q.toFun (C.face a n x)).first,
      max (p.toFun (C.face a n x)).last (q.toFun (C.face a n x)).last, _⟩ :
      StrictPoset.Cell (Fin 2)) = _
    rw [p.map_face, q.map_face]
    cases n <;> cases a <;> rfl
  map_comp n x y hxy h' := by
    have hp' := (p.map_face true n x).symm.trans ((congrArg p.toFun hxy).trans (p.map_face false n y))
    have hq' := (q.map_face true n x).symm.trans ((congrArg q.toFun hxy).trans (q.map_face false n y))
    have hp := p.map_comp n x y hxy hp'
    have hq := q.map_comp n x y hxy hq'
    change (⟨max (p.toFun (C.comp n x y hxy)).first (q.toFun (C.comp n x y hxy)).first,
      max (p.toFun (C.comp n x y hxy)).last (q.toFun (C.comp n x y hxy)).last, _⟩ :
      StrictPoset.Cell (Fin 2)) = _
    rw [hp, hq]
    cases n <;> rfl

/-- A joint zero label is exactly simultaneous membership in the two fibres. -/
theorem maxLabel_zero_iff (p q : C ⟶ StrictPoset.category (Fin 2)) (x : C) :
    (maxLabel p q).toFun x = StrictPoset.identity 0 ↔
      p.toFun x = StrictPoset.identity 0 ∧ q.toFun x = StrictPoset.identity 0 := by
  constructor
  · intro he
    have hs := congrArg (fun z : StrictPoset.Cell (Fin 2) => z.first) he
    have ht := congrArg (fun z : StrictPoset.Cell (Fin 2) => z.last) he
    change max (p.toFun x).first (q.toFun x).first = 0 at hs
    change max (p.toFun x).last (q.toFun x).last = 0 at ht
    have hp₀ : (p.toFun x).first = 0 := le_antisymm ((le_max_left _ _).trans_eq hs) (Fin.zero_le _)
    have hq₀ : (q.toFun x).first = 0 := le_antisymm ((le_max_right _ _).trans_eq hs) (Fin.zero_le _)
    have hp₁ : (p.toFun x).last = 0 := le_antisymm ((le_max_left _ _).trans_eq ht) (Fin.zero_le _)
    have hq₁ : (q.toFun x).last = 0 := le_antisymm ((le_max_right _ _).trans_eq ht) (Fin.zero_le _)
    exact ⟨StrictPoset.Cell.ext hp₀ hp₁, StrictPoset.Cell.ext hq₀ hq₁⟩
  · rintro ⟨hp, hq⟩
    apply StrictPoset.Cell.ext
    · change max (p.toFun x).first (q.toFun x).first = 0
      rw [hp, hq]
      rfl
    · change max (p.toFun x).last (q.toFun x).last = 0
      rw [hp, hq]
      rfl

/-- Joint labels commute with precomposition on every cell. -/
theorem maxLabel_precomp (p q : C ⟶ StrictPoset.category (Fin 2)) (f : D ⟶ C) :
    f ≫ maxLabel p q = maxLabel (f ≫ p) (f ≫ q) := by
  apply Hom.ext
  rfl

/-- The joint zero-fibre is the original full intersection. -/
def maxLabelFiberIso (p q : C ⟶ StrictPoset.category (Fin 2)) :
    labelFiber (maxLabel p q) 0 ≅
      C.fullOn ({x | p.toFun x = StrictPoset.identity 0} ∩
        {x | q.toFun x = StrictPoset.identity 0}) where
  hom :=
    { toFun x := ⟨x.val, by
        exact ⟨(maxLabel_zero_iff p q _).mp x.property.1,
          (maxLabel_zero_iff p q _).mp x.property.2⟩⟩
      map_face _ _ _ := Subtype.ext rfl
      map_comp _ _ _ _ _ := Subtype.ext rfl }
  inv :=
    { toFun x := ⟨x.val, by
        exact ⟨(maxLabel_zero_iff p q _).mpr x.property.1,
          (maxLabel_zero_iff p q _).mpr x.property.2⟩⟩
      map_face _ _ _ := Subtype.ext rfl
      map_comp _ _ _ _ _ := Subtype.ext rfl }
  hom_inv_id := by apply Hom.ext; rfl
  inv_hom_id := by apply Hom.ext; rfl

/-- The intersection identification preserves the original full inclusion. -/
theorem maxLabelFiberIso_inclusion (p q : C ⟶ StrictPoset.category (Fin 2)) :
    (maxLabelFiberIso p q).hom ≫ C.fullInclusion
      ({x | p.toFun x = StrictPoset.identity 0} ∩ {x | q.toFun x = StrictPoset.identity 0}) =
      labelFiberInclusion (maxLabel p q) 0 := by
  apply Hom.ext
  rfl

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Actual points of a realization have simplex representatives -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits

/-- The topological colimit is also a colimit of underlying sets. -/
theorem point_representation (K : SSet.{0}) (x : SSet.toTop.obj K) :
    ∃ (j : CostructuredArrow SSet.stdSimplex K) (p : (diagram K).obj j),
      (leg K j).hom p = x := by
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (isColimit K)) x

end Thomason.Construction.RealizationPrism

end

section

/-! # Continuous parameter maps for individual realized simplices -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- The continuous map from the standard barycentric simplex specified by a simplex of `K`. -/
def simplexPoint (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n))) :
    C(StdSimplex ℝ (Fin (n+1)), SSet.toTop.obj K) :=
  (leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm s))).hom.comp
    ⟨ULift.up, continuous_uliftUp⟩

theorem point_representation_simplex (K : SSet.{0}) (x : SSet.toTop.obj K) :
    ∃ (n : ℕ) (s : K.obj (.op (.mk n))) (p : StdSimplex ℝ (Fin (n+1))),
      simplexPoint K s p = x := by
  obtain ⟨j, p, hp⟩ := point_representation K x
  rcases j with ⟨⟨n⟩, ⟨⟨⟩⟩, g⟩
  rcases p with ⟨p⟩
  refine ⟨n, SSet.yonedaEquiv g, p, ?_⟩
  change (leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.yonedaEquiv g)))).hom
    (ULift.up p) = x
  rw [SSet.yonedaEquiv.symm_apply_apply]
  exact hp

/-- Evaluation commutes with the affine map of a simplex operator. -/
theorem simplexPoint_map (K : SSet.{0}) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (m+1))) :
    simplexPoint K (K.map f.op s) x = simplexPoint K s (StdSimplex.map f.toOrderHom x) := by
  let j := CostructuredArrow.mk (SSet.yonedaEquiv.symm (K.map f.op s))
  let k := CostructuredArrow.mk (SSet.yonedaEquiv.symm s)
  have hj : SSet.stdSimplex.map f ≫ k.hom = j.hom := by
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality]
    simp [j, k]
  let u : j ⟶ k := CostructuredArrow.homMk f hj
  exact (ConcreteCategory.congr_hom ((cocone K).w u) (ULift.up x)).symm

/-- Evaluation of a simplex is natural in the simplicial set. -/
theorem simplexPoint_naturality {K L : SSet.{0}} (f : K ⟶ L) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    (SSet.toTop.map f).hom (simplexPoint K s x) = simplexPoint L (f.app _ s) x := by
  have he := ConcreteCategory.congr_hom
    (leg_naturality f (CostructuredArrow.mk (SSet.yonedaEquiv.symm s))) (ULift.up x)
  change (SSet.toTop.map f).hom (simplexPoint K s x) = _ at he
  change (SSet.toTop.map f).hom (simplexPoint K s x) =
    (leg L (CostructuredArrow.mk (SSet.yonedaEquiv.symm (f.app _ s)))).hom (ULift.up x)
  rw [← SSet.yonedaEquiv_symm_comp]
  exact he

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Compactness of actual finite simplicial realizations -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- The disjoint union of the parameter spaces of nondegenerate simplices. -/
abbrev NondegeneratePoints (K : SSet.{0}) :=
  Σ s : K.N, StdSimplex ℝ (Fin (s.dim+1))

def nondegenerateProjection (K : SSet.{0}) : NondegeneratePoints K → SSet.toTop.obj K :=
  fun p => simplexPoint K p.1.simplex p.2

theorem nondegenerateProjection_continuous (K : SSet.{0}) :
    Continuous (nondegenerateProjection K) := by
  rw [continuous_sigma_iff]
  intro s
  exact (simplexPoint K s.simplex).continuous

/-- Every realized point has a representative on a nondegenerate simplex. -/
theorem nondegenerateProjection_surjective (K : SSet.{0}) :
    Function.Surjective (nondegenerateProjection K) := by
  intro x
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex K x
  obtain ⟨m, f, _, t, rfl⟩ := K.exists_nonDegenerate s
  refine ⟨⟨SSet.N.mk t.val t.property, StdSimplex.map f.toOrderHom p⟩, ?_⟩
  exact (simplexPoint_map K f t.val p).symm

/-- A simplicial set with finitely many nondegenerate simplices has compact realization. -/
theorem compactSpace_of_finite (K : SSet.{0}) [K.Finite] :
    CompactSpace (SSet.toTop.obj K) := by
  have hr : Set.range (nondegenerateProjection K) = Set.univ :=
    Set.range_eq_univ.mpr (nondegenerateProjection_surjective K)
  refine ⟨?_⟩
  rw [← hr]
  exact isCompact_range (nondegenerateProjection_continuous K)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Realizing arbitrary simplicial homotopies

The natural standard prisms descend along the actual realization colimit.
This constructs a continuous homotopy, without any model-category input.
-/

namespace Thomason.Construction.RealizedCylinder

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

/-- The prism on an original simplex, mapped into the global simplicial cylinder. -/
def piece (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K) :
    TopologicalInterval.cylinder.obj ((RealizationPrism.diagram K).obj j) ⟶
      SSet.toTop.obj (K ⊗ Δ[1]) :=
  PrismBarycentric.liftedStandardPrism j.left.len ≫ SSet.toTop.map (j.hom ▷ Δ[1])

theorem piece_naturality (K : SSet.{0})
    {j k : CostructuredArrow SSet.stdSimplex K} (f : j ⟶ k) :
    TopologicalInterval.cylinder.map ((RealizationPrism.diagram K).map f) ≫
      piece K k = piece K j := by
  change TopologicalInterval.cylinder.map (SimplexCategory.toTop.map f.left) ≫
    (PrismBarycentric.liftedStandardPrism k.left.len ≫ SSet.toTop.map (k.hom ▷ Δ[1])) = _
  rw [← Category.assoc, PrismBarycentric.liftedStandardPrism_naturality, Category.assoc,
    ← Functor.map_comp, ← comp_whiskerRight, CostructuredArrow.w f]
  rfl

/-- The canonical continuous comparison from the topological cylinder to
realization of the actual simplicial cylinder. -/
def comparison (K : SSet.{0}) :
    TopologicalInterval.cylinder.obj (SSet.toTop.obj K) ⟶ SSet.toTop.obj (K ⊗ Δ[1]) :=
  RealizationPrism.assemble K _ (piece K) (piece_naturality K)

theorem piece_zero (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K) :
    TopologicalInterval.sectionAt ((RealizationPrism.diagram K).obj j) 0 ≫ piece K j =
      RealizationPrism.leg K j ≫ SSet.toTop.map SSet.ι₀ := by
  change TopologicalInterval.sectionAt (SimplexCategory.toTop.{0}.obj (.mk j.left.len)) 0 ≫
    (PrismBarycentric.liftedStandardPrism j.left.len ≫ SSet.toTop.map (j.hom ▷ Δ[1])) = _
  rw [← Category.assoc, PrismBarycentric.liftedStandardPrism_zero, Category.assoc,
    ← Functor.map_comp]
  change SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map _ =
    (SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map j.hom) ≫ SSet.toTop.map SSet.ι₀
  rw [Category.assoc, ← Functor.map_comp]
  congr 2

theorem piece_one (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K) :
    TopologicalInterval.sectionAt ((RealizationPrism.diagram K).obj j) 1 ≫ piece K j =
      RealizationPrism.leg K j ≫ SSet.toTop.map SSet.ι₁ := by
  change TopologicalInterval.sectionAt (SimplexCategory.toTop.{0}.obj (.mk j.left.len)) 1 ≫
    (PrismBarycentric.liftedStandardPrism j.left.len ≫ SSet.toTop.map (j.hom ▷ Δ[1])) = _
  rw [← Category.assoc, PrismBarycentric.liftedStandardPrism_one, Category.assoc,
    ← Functor.map_comp]
  change SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map _ =
    (SSet.toTopSimplex.inv.app j.left ≫ SSet.toTop.map j.hom) ≫ SSet.toTop.map SSet.ι₁
  rw [Category.assoc, ← Functor.map_comp]
  congr 2

/-- Realization turns every simplicial homotopy into an actual continuous homotopy. -/
def homotopy {K L : SSet.{0}} {f g : K ⟶ L} (H : SSet.Homotopy f g) :
    (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom :=
  RealizationPrism.homotopy K _
    (fun j => piece K j ≫ SSet.toTop.map H.h)
    (fun q => by rw [← Category.assoc, piece_naturality])
    (SSet.toTop.map f) (SSet.toTop.map g)
    (fun j => by rw [← Category.assoc, piece_zero, Category.assoc, ← Functor.map_comp, H.h₀])
    (fun j => by rw [← Category.assoc, piece_one, Category.assoc, ← Functor.map_comp, H.h₁])

/-- The actual realization weak-equivalence test is invariant under any
simplicial homotopy, independently of Kan–Quillen. -/
theorem weakEquivalence_iff {K L : SSet.{0}} {f g : K ⟶ L} (H : SSet.Homotopy f g) :
    realizationWeakEquivalences f ↔ realizationWeakEquivalences g :=
  isWeakHomotopyEquivalence_homotopy_iff (homotopy H)

end

end Thomason.Construction.RealizedCylinder

end

section

/-! # Explicit simplicial contractions of all horns

Clamp a vertex to the missing-face vertex. This map is pointwise below
both the identity and the constant map. The two resulting homotopies
stay in the horn since they introduce no vertex other than the cone vertex.
-/

namespace Thomason.Construction.HornContraction

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

def clamp {n : ℕ} (i : Fin (n+2)) : Fin (n+2) →o Fin (n+2) where
  toFun k := min k i
  monotone' := fun _ _ h => min_le_min_right i h

def upper {n : ℕ} (i : Fin (n+2)) (b : Bool) : Fin (n+2) →o Fin (n+2) :=
  if b then OrderHom.const _ i else OrderHom.id

theorem clamp_le_upper {n : ℕ} (i : Fin (n+2)) (b : Bool) (k : Fin (n+2)) :
    clamp i k ≤ upper i b k := by
  cases b
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- The two homotopies from the lower clamping map. -/
def interpolate {n d : ℕ} (i : Fin (n+2)) (b : Bool)
    (s : Fin (d+1) →o Fin (n+2)) (θ : Fin (d+1) →o Fin 2) :
    Fin (d+1) →o Fin (n+2) :=
  orderInterpolate (clamp i) (upper i b) (clamp_le_upper i b) s θ

theorem interpolate_vertex {n d : ℕ} (i : Fin (n+2)) (b : Bool)
    (s : Fin (d+1) →o Fin (n+2)) (θ : Fin (d+1) →o Fin 2) (k : Fin (d+1)) :
    interpolate i b s θ k = s k ∨ interpolate i b s θ k = i := by
  change (if θ k = 0 then min (s k) i else upper i b (s k)) = s k ∨ _
  by_cases ht : θ k = 0
  · rw [ite_eq_left_iff.mpr (fun h => (h ht).elim)]
    rcases le_total (s k) i with hs | hs
    · exact Or.inl (min_eq_left hs)
    · apply Or.inr
      change (if θ k = 0 then min (s k) i else upper i b (s k)) = i
      rw [ite_eq_left_iff.mpr (fun h => (h ht).elim)]
      exact min_eq_right hs
  · cases b
    · exact Or.inl (by simp [ht, upper])
    · exact Or.inr (by simp [interpolate, orderInterpolate, ht, upper])

/-- Interpolation preserves every missing vertex other than the cone vertex. -/
theorem interpolate_mem {n : ℕ} (i : Fin (n+2)) (b : Bool)
    {m : SimplexCategoryᵒᵖ} (s : (Λ[n+1, i] : SSet.Subcomplex _).toSSet.obj m)
    (θ : (Δ[1] : SSet.{0}).obj m) :
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
      (interpolate i b (SSet.stdSimplex.objEquiv s.val).toOrderHom
        (SSet.stdSimplex.objEquiv θ).toOrderHom)) ∈ (Λ[n+1, i] : SSet.Subcomplex _).obj m := by
  obtain ⟨j, hji, hj⟩ := (SSet.mem_horn_iff_notMem_range s.val i).mp s.property
  apply (SSet.mem_horn_iff_notMem_range _ i).mpr
  refine ⟨j, hji, ?_⟩
  rintro ⟨k, hk⟩
  change interpolate i b (SSet.stdSimplex.objEquiv s.val).toOrderHom
    (SSet.stdSimplex.objEquiv θ).toOrderHom k = j at hk
  rcases interpolate_vertex i b (SSet.stdSimplex.objEquiv s.val).toOrderHom
    (SSet.stdSimplex.objEquiv θ).toOrderHom k with he | he
  · apply hj
    exact ⟨k, he.symm.trans hk⟩
  · exact hji (hk.symm.trans he)

/-- The lower clamping endomorphism of the horn. -/
def lowerMap {n : ℕ} (i : Fin (n+2)) : (Λ[n+1, i] : SSet.{0}) ⟶ Λ[n+1, i] where
  app m := ↾fun s => ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
    ((clamp i).comp (SSet.stdSimplex.objEquiv s.val).toOrderHom)), by
      have h := interpolate_mem i false s (SSet.stdSimplex.const 1 0 m)
      exact h⟩
  naturality m k a := by
    ext s
    rfl

/-- The cone vertex belongs to every nonempty-dimensional horn. -/
def vertex {n : ℕ} (i : Fin (n+2)) : (Λ[n+1, i] : SSet.{0}) _⦋0⦌ :=
  ⟨SSet.stdSimplex.obj₀Equiv.symm i, by
    apply (SSet.mem_horn_iff_notMem_range _ i).mpr
    obtain ⟨j, hj⟩ := exists_ne i
    refine ⟨j, hj, ?_⟩
    rintro ⟨k, hk⟩
    exact hj hk.symm⟩

/-- The horn contracts to its cone vertex through two simplicial homotopies. -/
def homotopy {n : ℕ} (i : Fin (n+2)) (b : Bool) :
    SSet.Homotopy (lowerMap i) (if b then SSet.const (vertex i) else 𝟙 _) where
  h := {
    app m := ↾fun x => ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
      (interpolate i b (SSet.stdSimplex.objEquiv x.1.val).toOrderHom
        (SSet.stdSimplex.objEquiv x.2).toOrderHom)), interpolate_mem i b x.1 x.2⟩
    naturality m k a := by
      ext s
      rfl }
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    ext k
    cases b <;> rfl
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end

end Thomason.Construction.HornContraction

end

section

/-! # All horn generators are actual realization weak equivalences

The two explicit horn contractions prove this semantic generator test
without any Kan–Quillen factorization or anodyne characterization.
-/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

namespace HornContraction

/-- The projection of a positive-dimensional horn to a point is weak. -/
theorem toPoint_weak {n : ℕ} (i : Fin (n+2)) :
    realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (Λ[n+1, i] : SSet.{0})) := by
  let t := SSet.stdSimplex.isTerminalObj₀.from (Λ[n+1, i] : SSet.{0})
  let v : (Δ[0] : SSet.{0}) ⟶ Λ[n+1, i] := SSet.yonedaEquiv.symm (vertex i)
  have htv : t ≫ v = SSet.const (vertex i) := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hvt : v ≫ t = 𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hl : realizationWeakEquivalences (lowerMap i) :=
    (RealizedCylinder.weakEquivalence_iff (homotopy i false)).mpr
      (realizationWeakEquivalences.id_mem _)
  have hc : realizationWeakEquivalences (t ≫ v) := by
    rw [htv]
    exact (RealizedCylinder.weakEquivalence_iff (homotopy i true)).mp hl
  let r : RetractArrow t (t ≫ v) := {
    i := Arrow.homMk (𝟙 _) v (by simp)
    r := Arrow.homMk (𝟙 _) t (by simp [Category.assoc, hvt])
    retract := by
      apply Arrow.hom_ext
      · simp
      · exact hvt }
  exact realizationWeakEquivalences.of_retract r hc

end HornContraction

/-- Every positive-dimensional horn inclusion satisfies the actual weak test. -/
theorem realization_horn_weak {n : ℕ} [NeZero n] (i : Fin (n+1)) :
    realizationWeakEquivalences (Λ[n, i].ι : _ ⟶ (Δ[n] : SSet.{0})) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let a : SimplexCategory.mk (m+1) ⟶ SimplexCategory.mk 0 :=
    SimplexCategory.Hom.mk (OrderHom.const _ 0)
  apply realizationWeakEquivalences.of_postcomp _ (SSet.stdSimplex.map a)
    (realized_simplex_map_weak a)
  have he : (Λ[m+1, i].ι : _ ⟶ (Δ[m+1] : SSet.{0})) ≫ SSet.stdSimplex.map a =
      SSet.stdSimplex.isTerminalObj₀.from _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he]
  exact HornContraction.toPoint_weak i

/-- The full family of generating anodyne maps lies in the semantic weak class. -/
theorem horn_generators_weak :
    SSet.modelCategoryQuillen.J.{0} ≤ realizationWeakEquivalences := by
  intro X Y f hf
  simp only [SSet.modelCategoryQuillen.J, CategoryTheory.MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  exact realization_horn_weak i

end

end Thomason.Construction

end

end OAI
