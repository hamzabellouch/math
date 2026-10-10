import OAI.CategoryTheory.Thomason.Simplicial.HornWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Transfer.HornRealizationGluing
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Homeomorph.Lemmas

namespace OAI

section

/-! # Barycentric coordinates on the actual realization of a horn -/

namespace Thomason.Construction.HornBarycentric

open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial

noncomputable section

abbrev simplexOrder {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})) :
    Fin (s.left.len+1) →o Fin (n+2) :=
  (SSet.stdSimplex.objEquiv (SSet.yonedaEquiv s.hom).val).toOrderHom

theorem simplexOrder_omits {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})) :
    ∃ j, j ≠ i ∧ ∀ k, simplexOrder i s k ≠ j := by
  obtain ⟨j, hj, hs⟩ := (SSet.mem_horn_iff_notMem_range
    (SSet.yonedaEquiv s.hom).val i).mp (SSet.yonedaEquiv s.hom).property
  exact ⟨j, hj, fun k hk => hs ⟨k, hk⟩⟩

theorem simplexOrder_naturality {n : ℕ} (i : Fin (n+2))
    {s t : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})} (f : s ⟶ t) :
    (simplexOrder i t).comp f.left.toOrderHom = simplexOrder i s := by
  have he := congrArg SSet.yonedaEquiv (CostructuredArrow.w f)
  rw [← SSet.yonedaEquiv_naturality] at he
  exact congrArg (fun z => (SSet.stdSimplex.objEquiv z.val).toOrderHom) he

/-- Coordinates of a point in any original simplex lie in the geometric horn. -/
theorem simplexPoint_mem {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0}))
    (x : StdSimplex ℝ (Fin (s.left.len+1))) :
    StdSimplex.map (simplexOrder i s) x ∈ horn i := by
  obtain ⟨j, hj, hs⟩ := simplexOrder_omits i s
  refine ⟨j, hj, ?_⟩
  change x.weights.mapDomain (simplexOrder i s) j = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, hk⟩
  exact hs k hk

/-- Barycentric coordinates on one original realized simplex. -/
def simplexPoint {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})) :
    (RealizationPrism.diagram (Λ[n+1, i] : SSet.{0})).obj s ⟶ TopCat.of (horn i) :=
  TopCat.ofHom ⟨fun x => ⟨StdSimplex.map (simplexOrder i s) x.down,
    simplexPoint_mem i s x.down⟩,
    ((StdSimplex.continuous_map ℝ (simplexOrder i s)).comp continuous_uliftDown).subtype_mk _⟩

theorem simplexPoint_naturality {n : ℕ} (i : Fin (n+2))
    {s t : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})} (f : s ⟶ t) :
    (RealizationPrism.diagram (Λ[n+1, i] : SSet.{0})).map f ≫ simplexPoint i t =
      simplexPoint i s := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change StdSimplex.map (simplexOrder i t) (StdSimplex.map f.left.toOrderHom x.down) =
    StdSimplex.map (simplexOrder i s) x.down
  rw [← StdSimplex.map_comp]
  exact congrArg (fun a => StdSimplex.map a x.down)
    (congrArg DFunLike.coe (simplexOrder_naturality i f))

/-- The actual geometric realization has canonical coordinates in the geometric horn. -/
def fromRealization {n : ℕ} (i : Fin (n+2)) :
    SSet.toTop.obj (Λ[n+1, i] : SSet.{0}) ⟶ TopCat.of (horn i) :=
  (RealizationPrism.isColimit (Λ[n+1, i] : SSet.{0})).desc {
    pt := TopCat.of (horn i)
    ι := { app := simplexPoint i
           naturality := fun s t f => by simpa using simplexPoint_naturality i f } }

@[reassoc]
theorem fromRealization_fac {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})) :
    RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) s ≫ fromRealization i = simplexPoint i s :=
  (RealizationPrism.isColimit (Λ[n+1, i] : SSet.{0})).fac _ s

end

end Thomason.Construction.HornBarycentric

end

section

/-! # The actual horn realization is the geometric horn

Both inverse equations are proved on the original simplex legs. This
identifies the stationary barycentric deformation with the actual
geometric realization used in the Kan–Quillen weak-equivalence test.
-/

namespace Thomason.Construction.HornBarycentric

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- Every original horn simplex factors through any face it omits. -/
def simplexToFace {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0}))
    (j : Fin (n+2)) (hj : j ≠ i) (hs : ∀ k, simplexOrder i s k ≠ j) :
    s ⟶ faceIndex i j hj :=
  CostructuredArrow.homMk
    (SimplexCategory.Hom.mk ((deletion j).comp (simplexOrder i s))) (by
      apply SSet.yonedaEquiv.injective
      rw [← SSet.yonedaEquiv_naturality]
      apply Subtype.ext
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro k
      exact insertion_deletion j _ (hs k))

/-- Gluing the coordinates of an original simplex returns its realization leg. -/
theorem toRealization_simplexPoint {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0}))
    (x : SimplexCategory.toTop.{0}.obj s.left) :
    toRealization i ((simplexPoint i s).hom x) =
      (RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) s).hom x := by
  obtain ⟨j, hj, hs⟩ := simplexOrder_omits i s
  have hz : ((simplexPoint i s).hom x).val.weights j = 0 := by
    change x.down.weights.mapDomain (simplexOrder i s) j = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨k, hk⟩
    exact hs k hk
  rw [toRealization_face i j hj _ hz]
  have he := congrArg (fun f => f.hom x)
    ((RealizationPrism.cocone (Λ[n+1, i] : SSet.{0})).w (simplexToFace i s j hj hs))
  change (RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) (faceIndex i j hj)).hom
    (ULift.up (StdSimplex.map ((deletion j).comp (simplexOrder i s)) x.down)) = _ at he
  change (RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) (faceIndex i j hj)).hom
    (ULift.up (StdSimplex.map ((deletion j) ∘ (simplexOrder i s)) x.down)) = _ at he
  rw [StdSimplex.map_comp] at he
  exact he

/-- One inverse equation follows from the colimit universal property. -/
theorem from_toRealization {n : ℕ} (i : Fin (n+2)) :
    fromRealization i ≫ TopCat.ofHom (toRealization i) =
      𝟙 (SSet.toTop.obj (Λ[n+1, i] : SSet.{0})) := by
  apply (RealizationPrism.isColimit (Λ[n+1, i] : SSet.{0})).hom_ext
  intro s
  rw [← Category.assoc, fromRealization_fac]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact toRealization_simplexPoint i s x

/-- The other inverse equation holds on any zero-coordinate face. -/
theorem toRealization_from {n : ℕ} (i : Fin (n+2)) (x : horn i) :
    (fromRealization i).hom (toRealization i x) = x := by
  obtain ⟨j, hj, hz⟩ := x.property
  rw [toRealization_face i j hj x hz]
  have he := congrArg (fun f => f.hom (ULift.up (StdSimplex.map (deletion j) x.val)))
    (fromRealization_fac i (faceIndex i j hj))
  change (fromRealization i).hom (faceValue i j hj x.val) = _ at he
  rw [he]
  apply Subtype.ext
  exact face_recover j x.val hz

/-- The homeomorphism uses the actual realization, with its original topology. -/
def homeomorph {n : ℕ} (i : Fin (n+2)) :
    SSet.toTop.obj (Λ[n+1, i] : SSet.{0}) ≃ₜ horn i where
  toFun := (fromRealization i).hom
  invFun := toRealization i
  left_inv x := congrArg (fun f => f.hom x) (from_toRealization i)
  right_inv := toRealization_from i
  continuous_toFun := (fromRealization i).hom.continuous
  continuous_invFun := (toRealization i).continuous

end

end Thomason.Construction.HornBarycentric

end

section

/-! # The horn homeomorphism commutes with the actual inclusion -/

namespace Thomason.Construction.HornBarycentric

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- Standard barycentric coordinates on the realization of a representable. -/
def simplexHomeomorph (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{0}) ≃ₜ StdSimplex ℝ (Fin (n+1)) :=
  (TopCat.homeoOfIso (SSet.toTopSimplex.app (.mk n))).trans
    (SimplexCategory.toTop₀.obj (.mk n)).uliftFunctorObjHomeo.symm

/-- An original simplex has its specified vertex map in the ambient simplex. -/
theorem simplex_factor {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})) :
    s.hom ≫ Λ[n+1, i].ι = SSet.stdSimplex.map (SimplexCategory.Hom.mk (simplexOrder i s)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
  exact (SSet.stdSimplex.objEquiv.symm_apply_apply _).symm

/-- The ambient realization coordinates agree on every original simplex leg. -/
theorem ambient_leg {n : ℕ} (i : Fin (n+2))
    (s : CostructuredArrow SSet.stdSimplex (Λ[n+1, i] : SSet.{0})) :
    RealizationPrism.leg (Λ[n+1, i] : SSet.{0}) s ≫ SSet.toTop.map Λ[n+1, i].ι ≫
      SSet.toTopSimplex.hom.app (.mk (n+1)) =
    SimplexCategory.toTop.map (SimplexCategory.Hom.mk (simplexOrder i s)) := by
  change (SSet.toTopSimplex.inv.app s.left ≫ SSet.toTop.map s.hom) ≫
    SSet.toTop.map Λ[n+1, i].ι ≫ SSet.toTopSimplex.hom.app (.mk (n+1)) = _
  rw [Category.assoc, ← Category.assoc (SSet.toTop.map s.hom), ← Functor.map_comp,
    simplex_factor]
  have hn : SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.Hom.mk (simplexOrder i s))) ≫
      SSet.toTopSimplex.hom.app (.mk (n+1)) = SSet.toTopSimplex.hom.app s.left ≫
      SimplexCategory.toTop.map (SimplexCategory.Hom.mk (simplexOrder i s)) :=
    SSet.toTopSimplex.hom.naturality _
  rw [hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The horn homeomorphism sends the actual inclusion to the literal subset inclusion. -/
theorem homeomorph_inclusion {n : ℕ} (i : Fin (n+2))
    (x : SSet.toTop.obj (Λ[n+1, i] : SSet.{0})) :
    simplexHomeomorph (n+1) ((SSet.toTop.map Λ[n+1, i].ι).hom x) =
      (homeomorph i x).val := by
  have he : fromRealization i ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ =
      SSet.toTop.map Λ[n+1, i].ι ≫
        TopCat.ofHom ⟨simplexHomeomorph (n+1), (simplexHomeomorph (n+1)).continuous⟩ := by
    apply (RealizationPrism.isColimit (Λ[n+1, i] : SSet.{0})).hom_ext
    intro s
    rw [← Category.assoc, fromRealization_fac]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    have h := congrArg (fun f => (f.hom p).down) (ambient_leg i s)
    exact h.symm
  exact (congrArg (fun f => f.hom x) he).symm

end

end Thomason.Construction.HornBarycentric

end

section

/-! # A stationary deformation for the actual realized horn inclusion -/

namespace Thomason.Construction.HornBarycentric

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- The actual continuous retraction from a realized simplex to its horn. -/
def realizedRetraction {n : ℕ} (i : Fin (n+2)) :
    C(SSet.toTop.obj (Δ[n+1] : SSet.{0}), SSet.toTop.obj (Λ[n+1, i] : SSet.{0})) where
  toFun x := (homeomorph i).symm (retraction i (simplexHomeomorph (n+1) x))
  continuous_toFun := (homeomorph i).symm.continuous.comp
    ((retraction i).continuous.comp (simplexHomeomorph (n+1)).continuous)

/-- The retraction is an exact left inverse to the realized horn inclusion. -/
theorem realizedRetraction_left {n : ℕ} (i : Fin (n+2))
    (x : SSet.toTop.obj (Λ[n+1, i] : SSet.{0})) :
    realizedRetraction i ((SSet.toTop.map Λ[n+1, i].ι).hom x) = x := by
  change (homeomorph i).symm (retraction i
    (simplexHomeomorph (n+1) ((SSet.toTop.map Λ[n+1, i].ι).hom x))) = x
  rw [homeomorph_inclusion]
  have hfix : retraction i (homeomorph i x).val = homeomorph i x :=
    Subtype.ext (retraction_fixed i (homeomorph i x))
  rw [hfix]
  exact (homeomorph i).symm_apply_apply x

/-- The deformation is stationary on the entire realized horn, so it can
be glued after arbitrary horn attachments. -/
def realizedDeformation {n : ℕ} (i : Fin (n+2)) :
    ((SSet.toTop.map Λ[n+1, i].ι).hom.comp (realizedRetraction i)).HomotopyRel
      (ContinuousMap.id _) (Set.range (SSet.toTop.map Λ[n+1, i].ι).hom) where
  toFun p := (simplexHomeomorph (n+1)).symm
    (deformation i (simplexHomeomorph (n+1) p.2, unitInterval.symm p.1))
  continuous_toFun := (simplexHomeomorph (n+1)).symm.continuous.comp
    ((deformation i).continuous.comp (by fun_prop))
  map_zero_left x := by
    change (simplexHomeomorph (n+1)).symm
      (deformation i (simplexHomeomorph (n+1) x, unitInterval.symm 0)) = _
    rw [unitInterval.symm_zero, deformation_one]
    apply (simplexHomeomorph (n+1)).injective
    rw [Homeomorph.apply_symm_apply]
    change _ = simplexHomeomorph (n+1)
      ((SSet.toTop.map Λ[n+1, i].ι).hom (realizedRetraction i x))
    rw [homeomorph_inclusion]
    change _ = ((homeomorph i) ((homeomorph i).symm _)).val
    rw [Homeomorph.apply_symm_apply]
  map_one_left x := by
    change (simplexHomeomorph (n+1)).symm
      (deformation i (simplexHomeomorph (n+1) x, unitInterval.symm 1)) = x
    rw [unitInterval.symm_one, deformation_zero, Homeomorph.symm_apply_apply]
  prop' t x hx := by
    obtain ⟨a, rfl⟩ := hx
    change (simplexHomeomorph (n+1)).symm
      (deformation i (simplexHomeomorph (n+1) ((SSet.toTop.map Λ[n+1, i].ι).hom a),
        unitInterval.symm t)) =
      (SSet.toTop.map Λ[n+1, i].ι).hom (realizedRetraction i
        ((SSet.toTop.map Λ[n+1, i].ι).hom a))
    rw [realizedRetraction_left, homeomorph_inclusion, deformation_fixed]
    exact (simplexHomeomorph (n+1)).symm_apply_eq.mpr (homeomorph_inclusion i a).symm

end

end Thomason.Construction.HornBarycentric

end

section

/-! # The supported simplex of an actual realization point -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

noncomputable section

/-- The subcomplex generated by the restriction to the nonzero barycentric coordinates. -/
def simplexCarrier (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (n+1))) : K.Subcomplex :=
  SSet.Subcomplex.ofSimplex
    (K.map (show SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n from
      SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom).op s)

/-- Degenerate operators may merge support vertices but preserve the generated carrier. -/
theorem simplexCarrier_naturality (K : SSet.{0}) {m n : ℕ}
    (f : Fin (m+1) →o Fin (n+1)) (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (m+1))) :
    simplexCarrier K (K.map (show SimplexCategory.mk m ⟶ .mk n from SimplexCategory.Hom.mk f).op s) x =
      simplexCarrier K s (StdSimplex.map f x) := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk m :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  let b : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶
      .mk (HornBarycentric.supportLen (StdSimplex.map f x)) :=
    SimplexCategory.Hom.mk (HornBarycentric.supportOrdinal f x)
  let c : SimplexCategory.mk (HornBarycentric.supportLen (StdSimplex.map f x)) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap (StdSimplex.map f x)).toOrderHom
  let F : SimplexCategory.mk m ⟶ .mk n := SimplexCategory.Hom.mk f
  have he : a ≫ F = b ≫ c := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro k
    exact (HornBarycentric.supportOrdinal_commutes f x k).symm
  have hb : Epi b := (SimplexCategory.epi_iff_surjective).mpr
    (HornBarycentric.supportOrdinal_surjective f x)
  have hv : K.map a.op (K.map F.op s) =
      K.map b.op (K.map c.op s) := by
    change (K.map F.op ≫ K.map a.op) s =
      (K.map c.op ≫ K.map b.op) s
    rw [← K.map_comp, ← K.map_comp, ← op_comp, ← op_comp, he]
  change SSet.Subcomplex.ofSimplex (K.map a.op (K.map F.op s)) =
    SSet.Subcomplex.ofSimplex (K.map c.op s)
  rw [hv]
  exact SSet.Subcomplex.ofSimplex_map_of_epi b _

/-- The supported carriers are compatible with every simplex arrow. -/
def carrierCocone (K : SSet.{0}) : Cocone (diagram K ⋙ forget TopCat) where
  pt := K.Subcomplex
  ι := {
    app j := ↾fun p => simplexCarrier K (SSet.yonedaEquiv j.hom) p.down
    naturality j k f := by
      apply ConcreteCategory.hom_ext
      intro p
      have hs : K.map f.left.op (SSet.yonedaEquiv k.hom) = SSet.yonedaEquiv j.hom := by
        rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w f]
      exact (simplexCarrier_naturality K f.left.toOrderHom
        (SSet.yonedaEquiv k.hom) p.down).symm.trans (congrArg
          (fun s => simplexCarrier K s p.down) hs) }

/-- Every actual realization point has a well-defined supported simplex subcomplex. -/
def carrier (K : SSet.{0}) : SSet.toTop.obj K → K.Subcomplex :=
  fun p => (isColimitOfPreserves (forget TopCat) (isColimit K)).desc (carrierCocone K) p

/-- The intrinsic carrier is computed on any representative simplex. -/
theorem carrier_leg (K : SSet.{0}) (j : CostructuredArrow SSet.stdSimplex K)
    (p : (diagram K).obj j) :
    carrier K ((leg K j).hom p) = simplexCarrier K (SSet.yonedaEquiv j.hom) p.down :=
  congrArg (fun f => f p)
    ((isColimitOfPreserves (forget TopCat) (isColimit K)).fac (carrierCocone K) j)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Closed subcomplex conditions in the actual realization topology -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

theorem simplexCarrier_le (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (n+1))) : simplexCarrier K s x ≤ SSet.Subcomplex.ofSimplex s :=
  SSet.Subcomplex.ofSimplex_map_le _ s

/-- Only finitely many parameter simplices of dimension at most `n` are needed. -/
abbrev FaceIndex (n : ℕ) := Σ k : Fin (n+1), (SimplexCategory.mk k.val ⟶ .mk n)

theorem supportLen_le {n : ℕ} (x : StdSimplex ℝ (Fin (n+1))) :
    HornBarycentric.supportLen x ≤ n := by
  have h := Finset.card_le_card (Finset.subset_univ x.weights.support)
  rw [Finset.card_univ, Fintype.card_fin, HornBarycentric.support_card] at h
  omega

/-- The points carried by a subcomplex form a finite union of affine simplex images. -/
theorem simplexCarrier_le_iff (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    simplexCarrier K s x ≤ A ↔
      ∃ i : FaceIndex n, K.map i.2.op s ∈ A.obj (.op (.mk i.1.val)) ∧
        x ∈ Set.range (StdSimplex.map i.2.toOrderHom) := by
  constructor
  · intro hx
    let k : Fin (n+1) := ⟨HornBarycentric.supportLen x, by
      have h := supportLen_le x
      omega⟩
    let f : SimplexCategory.mk k.val ⟶ .mk n :=
      SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
    refine ⟨⟨k, f⟩, ?_, HornBarycentric.supportCoordinates x, ?_⟩
    · exact (SSet.Subcomplex.ofSimplex_le_iff _ _).mp hx
    · exact HornBarycentric.support_recover x
  · rintro ⟨⟨k, f⟩, hf, y, rfl⟩
    rw [← simplexCarrier_naturality K f.toOrderHom s y]
    exact (simplexCarrier_le K _ y).trans ((SSet.Subcomplex.ofSimplex_le_iff _ _).mpr hf)

/-- The carrier condition is closed on each parameter simplex. -/
theorem simplexCarrier_isClosed (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) :
    IsClosed (Set.ofPred (fun x : StdSimplex ℝ (Fin (n+1)) => simplexCarrier K s x ≤ A)) := by
  let : T2Space (StdSimplex ℝ (Fin (n+1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  let F := {i : FaceIndex n // K.map i.2.op s ∈ A.obj (.op (.mk i.1.val))}
  have he : (Set.ofPred (fun x : StdSimplex ℝ (Fin (n+1)) => simplexCarrier K s x ≤ A)) =
      ⋃ i : F, Set.range (StdSimplex.map i.val.2.toOrderHom) := by
    ext x
    simp only [simplexCarrier_le_iff, Set.mem_iUnion]
    exact ⟨fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, hx⟩, fun ⟨i, hx⟩ => ⟨i.val, i.property, hx⟩⟩
  rw [he]
  apply isClosed_iUnion_of_finite
  intro i
  exact (isCompact_range (show Continuous (StdSimplex.map i.val.2.toOrderHom) by fun_prop)).isClosed

/-- The intrinsic condition of lying in a subcomplex is closed in geometric realization. -/
theorem carrier_isClosed (K : SSet.{0}) (A : K.Subcomplex) :
    IsClosed (Set.ofPred (fun x : SSet.toTop.obj K => carrier K x ≤ A)) := by
  apply (isClosed_iff_simplex K _).mpr
  intro j
  have he : (leg K j).hom ⁻¹' (Set.ofPred (fun x => carrier K x ≤ A)) =
      ULift.down ⁻¹' (Set.ofPred (fun x => simplexCarrier K (SSet.yonedaEquiv j.hom) x ≤ A)) := by
    ext p
    change (carrier K ((leg K j).hom p) ≤ A) ↔ _
    rw [carrier_leg]
    rfl
  exact he.symm ▸ (simplexCarrier_isClosed K A (SSet.yonedaEquiv j.hom)).preimage continuous_uliftDown

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Carriers and the actual image of a realized subcomplex -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

theorem simplexCarrier_image {K L : SSet.{0}} (f : K ⟶ L) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    simplexCarrier L (f.app _ s) x = (simplexCarrier K s x).image f := by
  unfold simplexCarrier
  rw [SSet.Subcomplex.image_ofSimplex]
  congr 1
  exact (ConcreteCategory.congr_hom (f.naturality _) s).symm

/-- The supported carrier commutes with every simplicial map. -/
theorem carrier_image {K L : SSet.{0}} (f : K ⟶ L) (x : SSet.toTop.obj K) :
    carrier L ((SSet.toTop.map f).hom x) = (carrier K x).image f := by
  obtain ⟨j, p, rfl⟩ := point_representation K x
  have he := ConcreteCategory.congr_hom (leg_naturality f j) p
  change (SSet.toTop.map f).hom ((leg K j).hom p) = _ at he
  rw [he, carrier_leg, carrier_leg]
  change simplexCarrier L (SSet.yonedaEquiv (j.hom ≫ f)) p.down = _
  rw [SSet.yonedaEquiv_comp]
  exact simplexCarrier_image f _ _

/-- A point of a realized subcomplex has its ambient carrier in that subcomplex. -/
theorem carrier_inclusion_le (K : SSet.{0}) (A : K.Subcomplex)
    (x : SSet.toTop.obj (A : SSet)) :
    carrier K ((SSet.toTop.map A.ι).hom x) ≤ A := by
  rw [carrier_image, SSet.Subcomplex.image_le_iff, SSet.Subcomplex.preimage_ι]
  exact le_top

/-- A supported simplex whose carrier lies in `A` lifts to an actual point of `|A|`. -/
def supportedLift (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1)))
    (h : simplexCarrier K s x ≤ A) : SSet.toTop.obj (A : SSet) :=
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  let t : (A : SSet).obj (.op (.mk (HornBarycentric.supportLen x))) :=
    ⟨K.map a.op s, (SSet.Subcomplex.ofSimplex_le_iff _ _).mp h⟩
  (leg (A : SSet) (CostructuredArrow.mk (SSet.yonedaEquiv.symm t))).hom
    (ULift.up (HornBarycentric.supportCoordinates x))

/-- The lift evaluates to the original simplex point, with its zero coordinates restored. -/
theorem supportedLift_inclusion (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1)))
    (h : simplexCarrier K s x ≤ A) :
    (SSet.toTop.map A.ι).hom (supportedLift K A s x h) =
      (leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm s))).hom (ULift.up x) := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  let t : (A : SSet).obj (.op (.mk (HornBarycentric.supportLen x))) :=
    ⟨K.map a.op s, (SSet.Subcomplex.ofSimplex_le_iff _ _).mp h⟩
  let j := CostructuredArrow.mk (SSet.yonedaEquiv.symm t)
  let k := CostructuredArrow.mk (SSet.yonedaEquiv.symm s)
  have hj : j.hom ≫ A.ι = SSet.stdSimplex.map a ≫ k.hom := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_naturality]
    simp [j, k, t]
  let u : (CostructuredArrow.map A.ι).obj j ⟶ k := CostructuredArrow.homMk a hj.symm
  have he := ConcreteCategory.congr_hom ((cocone K).w u)
    (ULift.up (HornBarycentric.supportCoordinates x))
  have hn := ConcreteCategory.congr_hom (leg_naturality A.ι j)
    (ULift.up (HornBarycentric.supportCoordinates x))
  change (SSet.toTop.map A.ι).hom (supportedLift K A s x h) = _ at hn
  calc
    _ = (leg K ((CostructuredArrow.map A.ι).obj j)).hom
        (ULift.up (HornBarycentric.supportCoordinates x)) := hn
    _ = (leg K k).hom ((diagram K).map u
        (ULift.up (HornBarycentric.supportCoordinates x))) := he.symm
    _ = (leg K k).hom (ULift.up x) := by
      apply congrArg (leg K k).hom
      exact congrArg ULift.up (HornBarycentric.support_recover x)

/-- Membership in a realized subcomplex is exactly the intrinsic carrier condition. -/
theorem mem_range_inclusion_iff (K : SSet.{0}) (A : K.Subcomplex)
    (x : SSet.toTop.obj K) :
    x ∈ Set.range (SSet.toTop.map A.ι).hom ↔ carrier K x ≤ A := by
  constructor
  · rintro ⟨y, rfl⟩
    exact carrier_inclusion_le K A y
  · intro hx
    obtain ⟨j, p, rfl⟩ := point_representation K x
    rw [carrier_leg] at hx
    cases j with
    | mk j r g =>
      rcases r with ⟨⟨⟩⟩
      cases j with
      | mk n =>
        refine ⟨supportedLift K A (SSet.yonedaEquiv g) p.down hx, ?_⟩
        have hh := supportedLift_inclusion K A (SSet.yonedaEquiv g) p.down hx
        have hg : SSet.yonedaEquiv.symm (SSet.yonedaEquiv g) = g :=
          SSet.yonedaEquiv.symm_apply_apply g
        rw [hg] at hh
        exact hh

/-- Every simplicial subcomplex has closed image under actual geometric realization. -/
theorem inclusion_isClosed_range (K : SSet.{0}) (A : K.Subcomplex) :
    IsClosed (Set.range (SSet.toTop.map A.ι).hom) := by
  have he : Set.range (SSet.toTop.map A.ι).hom =
      Set.ofPred (fun x => carrier K x ≤ A) := by
    ext x
    exact mem_range_inclusion_iff K A x
  rw [he]
  exact carrier_isClosed K A

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Compatibility of supported subcomplex lifts -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- Supported lifts agree across arbitrary simplex operators, including degeneracies. -/
theorem supportedLift_naturality (K : SSet.{0}) (A : K.Subcomplex) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (m+1)))
    (h₁ : simplexCarrier K (K.map f.op s) x ≤ A)
    (h₂ : simplexCarrier K s (StdSimplex.map f.toOrderHom x) ≤ A) :
    supportedLift K A (K.map f.op s) x h₁ =
      supportedLift K A s (StdSimplex.map f.toOrderHom x) h₂ := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk m :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  let b : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶
      .mk (HornBarycentric.supportLen (StdSimplex.map f.toOrderHom x)) :=
    SimplexCategory.Hom.mk (HornBarycentric.supportOrdinal f.toOrderHom x)
  let c : SimplexCategory.mk (HornBarycentric.supportLen (StdSimplex.map f.toOrderHom x)) ⟶
      .mk n := SimplexCategory.Hom.mk
        (HornBarycentric.supportMap (StdSimplex.map f.toOrderHom x)).toOrderHom
  let t₁ : (A : SSet).obj (.op (.mk (HornBarycentric.supportLen x))) :=
    ⟨K.map a.op (K.map f.op s), (SSet.Subcomplex.ofSimplex_le_iff _ _).mp h₁⟩
  let t₂ : (A : SSet).obj
      (.op (.mk (HornBarycentric.supportLen (StdSimplex.map f.toOrderHom x)))) :=
    ⟨K.map c.op s, (SSet.Subcomplex.ofSimplex_le_iff _ _).mp h₂⟩
  have hsquare : a ≫ f = b ≫ c := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    exact (HornBarycentric.supportOrdinal_commutes f.toOrderHom x i).symm
  have ht : (A : SSet).map b.op t₂ = t₁ := by
    apply Subtype.ext
    change K.map b.op (K.map c.op s) = K.map a.op (K.map f.op s)
    change (K.map c.op ≫ K.map b.op) s = (K.map f.op ≫ K.map a.op) s
    rw [← K.map_comp, ← K.map_comp, ← op_comp, ← op_comp, hsquare]
  let j₁ := CostructuredArrow.mk (SSet.yonedaEquiv.symm t₁)
  let j₂ := CostructuredArrow.mk (SSet.yonedaEquiv.symm t₂)
  have hj : SSet.stdSimplex.map b ≫ j₂.hom = j₁.hom := by
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality]
    simpa [j₁, j₂] using ht
  let u : j₁ ⟶ j₂ := CostructuredArrow.homMk b hj
  have he := ConcreteCategory.congr_hom ((cocone (A : SSet)).w u)
    (ULift.up (HornBarycentric.supportCoordinates x))
  calc
    _ = (leg (A : SSet) j₂).hom ((diagram (A : SSet)).map u
        (ULift.up (HornBarycentric.supportCoordinates x))) := he.symm
    _ = _ := by
      apply congrArg (leg (A : SSet) j₂).hom
      exact congrArg ULift.up (HornBarycentric.supportCoordinates_naturality f.toOrderHom x)

/-- When the entire simplex is in the subcomplex, its lift is its original realization. -/
theorem supportedLift_of_mem (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : (A : SSet).obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1)))
    (h : simplexCarrier K s.val x ≤ A) :
    supportedLift K A s.val x h =
      (leg (A : SSet) (CostructuredArrow.mk (SSet.yonedaEquiv.symm s))).hom (ULift.up x) := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  let t : (A : SSet).obj (.op (.mk (HornBarycentric.supportLen x))) :=
    ⟨K.map a.op s.val, (SSet.Subcomplex.ofSimplex_le_iff _ _).mp h⟩
  let j := CostructuredArrow.mk (SSet.yonedaEquiv.symm t)
  let k := CostructuredArrow.mk (SSet.yonedaEquiv.symm s)
  have ht : (A : SSet).map a.op s = t := by apply Subtype.ext; rfl
  have hj : SSet.stdSimplex.map a ≫ k.hom = j.hom := by
    apply SSet.yonedaEquiv.injective
    rw [← SSet.yonedaEquiv_naturality]
    simpa [j, k] using ht
  let u : j ⟶ k := CostructuredArrow.homMk a hj
  have he := ConcreteCategory.congr_hom ((cocone (A : SSet)).w u)
    (ULift.up (HornBarycentric.supportCoordinates x))
  calc
    _ = (leg (A : SSet) k).hom ((diagram (A : SSet)).map u
        (ULift.up (HornBarycentric.supportCoordinates x))) := he.symm
    _ = _ := by
      apply congrArg (leg (A : SSet) k).hom
      exact congrArg ULift.up (HornBarycentric.support_recover x)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Injectivity of actual realized subcomplex inclusions -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits Convexity Opposite Classical
open scoped Simplicial

noncomputable section

/-- The partial lift of a simplex point, defined precisely when its carrier is in `A`. -/
def liftOrNone (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    Option (SSet.toTop.obj (A : SSet)) :=
  if h : simplexCarrier K s x ≤ A then some (supportedLift K A s x h) else none

theorem liftOrNone_naturality (K : SSet.{0}) (A : K.Subcomplex) {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ .mk n) (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (m+1))) :
    liftOrNone K A (K.map f.op s) x = liftOrNone K A s (StdSimplex.map f.toOrderHom x) := by
  by_cases h₁ : simplexCarrier K (K.map f.op s) x ≤ A
  · have h₂ : simplexCarrier K s (StdSimplex.map f.toOrderHom x) ≤ A := by
      rwa [← simplexCarrier_naturality]
    simp only [liftOrNone, dite_eq_left h₁, dite_eq_left h₂, Option.some.injEq]
    exact supportedLift_naturality K A f s x h₁ h₂
  · have h₂ : ¬ simplexCarrier K s (StdSimplex.map f.toOrderHom x) ≤ A := by
      rwa [← simplexCarrier_naturality]
    simp only [liftOrNone, dite_eq_right h₁, dite_eq_right h₂]

/-- Partial lifts form a cocone of underlying sets; no continuity of the partial map is asserted. -/
def partialLiftCocone (K : SSet.{0}) (A : K.Subcomplex) :
    Cocone (diagram K ⋙ forget TopCat) where
  pt := Option (SSet.toTop.obj (A : SSet))
  ι := {
    app j := ↾fun p => liftOrNone K A (SSet.yonedaEquiv j.hom) p.down
    naturality j k f := by
      apply ConcreteCategory.hom_ext
      intro p
      have hs : K.map f.left.op (SSet.yonedaEquiv k.hom) = SSet.yonedaEquiv j.hom := by
        rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w f]
      change liftOrNone K A (SSet.yonedaEquiv k.hom)
        (StdSimplex.map f.left.toOrderHom p.down) = _
      rw [← hs]
      exact (liftOrNone_naturality K A f.left (SSet.yonedaEquiv k.hom) p.down).symm }

/-- A set-theoretic partial inverse to the realized inclusion. -/
def partialLift (K : SSet.{0}) (A : K.Subcomplex) :
    SSet.toTop.obj K → Option (SSet.toTop.obj (A : SSet)) :=
  fun p => (isColimitOfPreserves (forget TopCat) (isColimit K)).desc
    (partialLiftCocone K A) p

theorem partialLift_leg (K : SSet.{0}) (A : K.Subcomplex)
    (j : CostructuredArrow SSet.stdSimplex K) (p : (diagram K).obj j) :
    partialLift K A ((leg K j).hom p) = liftOrNone K A (SSet.yonedaEquiv j.hom) p.down :=
  congrArg (fun f => f p)
    ((isColimitOfPreserves (forget TopCat) (isColimit K)).fac (partialLiftCocone K A) j)

/-- On points already in `|A|`, the partial inverse recovers the point itself. -/
theorem partialLift_inclusion (K : SSet.{0}) (A : K.Subcomplex)
    (x : SSet.toTop.obj (A : SSet)) :
    partialLift K A ((SSet.toTop.map A.ι).hom x) = some x := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex (A : SSet) x
  rw [simplexPoint_naturality]
  have hp := partialLift_leg K A
    (CostructuredArrow.mk (SSet.yonedaEquiv.symm (A.ι.app _ s))) (ULift.up p)
  change partialLift K A (simplexPoint K (A.ι.app _ s) p) =
    liftOrNone K A (SSet.yonedaEquiv (SSet.yonedaEquiv.symm (A.ι.app _ s))) p at hp
  rw [SSet.yonedaEquiv.apply_symm_apply] at hp
  rw [hp]
  have h : simplexCarrier K (A.ι.app _ s) p ≤ A := by
    rw [simplexCarrier_image, SSet.Subcomplex.image_le_iff, SSet.Subcomplex.preimage_ι]
    exact le_top
  rw [liftOrNone, dite_eq_left h]
  exact congrArg some (supportedLift_of_mem K A s p h)

/-- Geometric realization sends a simplicial subcomplex inclusion to an injective map. -/
theorem inclusion_injective (K : SSet.{0}) (A : K.Subcomplex) :
    Function.Injective (SSet.toTop.map A.ι).hom := by
  intro x y h
  apply Option.some.inj
  simpa only [partialLift_inclusion] using congrArg (partialLift K A) h

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Subcomplex inclusions are closed embeddings after geometric realization -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

theorem carrier_simplexPoint (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    carrier K (simplexPoint K s x) = simplexCarrier K s x := by
  have h := carrier_leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm s)) (ULift.up x)
  change carrier K (simplexPoint K s x) =
    simplexCarrier K (SSet.yonedaEquiv (SSet.yonedaEquiv.symm s)) x at h
  rw [SSet.yonedaEquiv.apply_symm_apply] at h
  exact h

/-- A simplex of the subcomplex obtained by applying an ambient face operator. -/
def faceSimplex (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) (i : FaceIndex n)
    (h : K.map i.2.op s ∈ A.obj (.op (.mk i.1.val))) :
    (A : SSet).obj (.op (.mk i.1.val)) := ⟨K.map i.2.op s, h⟩

theorem faceSimplex_inclusion (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) (i : FaceIndex n)
    (h : K.map i.2.op s ∈ A.obj (.op (.mk i.1.val)))
    (y : StdSimplex ℝ (Fin (i.1.val+1))) :
    (SSet.toTop.map A.ι).hom (simplexPoint (A : SSet) (faceSimplex K A s i h) y) =
      simplexPoint K s (StdSimplex.map i.2.toOrderHom y) := by
  rw [simplexPoint_naturality]
  exact simplexPoint_map K i.2 s y

/-- On a parameter simplex, the image of a subset of `|A|` is a finite union of face images. -/
theorem simplexPoint_preimage_inclusion_image (K : SSet.{0}) (A : K.Subcomplex)
    (B : Set (SSet.toTop.obj (A : SSet))) {n : ℕ} (s : K.obj (.op (.mk n))) :
    (simplexPoint K s) ⁻¹' ((SSet.toTop.map A.ι).hom '' B) =
      ⋃ i : {i : FaceIndex n // K.map i.2.op s ∈ A.obj (.op (.mk i.1.val))},
        (StdSimplex.map i.val.2.toOrderHom) ''
          ((simplexPoint (A : SSet) (faceSimplex K A s i.val i.property)) ⁻¹' B) := by
  ext x
  constructor
  · rintro ⟨z, hz, he⟩
    have hc : simplexCarrier K s x ≤ A := by
      have hc := carrier_inclusion_le K A z
      rw [he] at hc
      rwa [carrier_simplexPoint] at hc
    obtain ⟨i, hi, y, hy⟩ := (simplexCarrier_le_iff K A s x).mp hc
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, y, ?_, hy⟩
    have hp : simplexPoint (A : SSet) (faceSimplex K A s i hi) y = z := by
      apply inclusion_injective K A
      rw [faceSimplex_inclusion, hy, he]
    simpa only [Set.mem_preimage, hp] using hz
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨simplexPoint (A : SSet) (faceSimplex K A s i.val i.property) y,
      hy, faceSimplex_inclusion K A s i.val i.property y⟩

/-- Realization of a subcomplex inclusion is a closed map. -/
theorem inclusion_isClosedMap (K : SSet.{0}) (A : K.Subcomplex) :
    IsClosedMap (SSet.toTop.map A.ι).hom := by
  intro B hB
  apply (isClosed_iff_simplex K _).mpr
  intro j
  have h (n : ℕ) (s : K.obj (.op (.mk n))) :
      IsClosed ((simplexPoint K s) ⁻¹' ((SSet.toTop.map A.ι).hom '' B)) := by
    let : T2Space (StdSimplex ℝ (Fin (n+1))) :=
      (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
    rw [simplexPoint_preimage_inclusion_image]
    apply isClosed_iUnion_of_finite
    intro i
    exact ((hB.preimage (simplexPoint (A : SSet)
      (faceSimplex K A s i.val i.property)).continuous).isCompact.image
        (StdSimplex.continuous_map ℝ i.val.2.toOrderHom)).isClosed
  rcases j with ⟨⟨n⟩, ⟨⟨⟩⟩, g⟩
  have hs := (h n (SSet.yonedaEquiv g)).preimage continuous_uliftDown
  have he : (leg K (CostructuredArrow.mk g)).hom ⁻¹'
      ((SSet.toTop.map A.ι).hom '' B) =
      ULift.down ⁻¹' ((simplexPoint K (SSet.yonedaEquiv g)) ⁻¹'
        ((SSet.toTop.map A.ι).hom '' B)) := by
    ext p
    change (leg K (CostructuredArrow.mk g)).hom p ∈ ((SSet.toTop.map A.ι).hom '' B) ↔
      (leg K (CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.yonedaEquiv g)))).hom
        (ULift.up p.down) ∈ ((SSet.toTop.map A.ι).hom '' B)
    rw [SSet.yonedaEquiv.symm_apply_apply]
    rfl
  exact he.symm ▸ hs

/-- The actual topological map induced by a simplicial subcomplex is a closed embedding. -/
theorem inclusion_isClosedEmbedding (K : SSet.{0}) (A : K.Subcomplex) :
    IsClosedEmbedding (SSet.toTop.map A.ι).hom :=
  .of_continuous_injective_isClosedMap (SSet.toTop.map A.ι).hom.continuous
    (inclusion_injective K A) (inclusion_isClosedMap K A)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Subcomplex topology and the actual Kan–Quillen weak-equivalence test -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

/-- The realization of a subcomplex is its intrinsic carrier subspace, homeomorphically. -/
def carrierHomeomorph (K : SSet.{0}) (A : K.Subcomplex) :
    SSet.toTop.obj (A : SSet) ≃ₜ Set.ofPred (fun x : SSet.toTop.obj K => carrier K x ≤ A) :=
  (inclusion_isClosedEmbedding K A).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (by ext x; exact mem_range_inclusion_iff K A x))

def carrierInclusion (K : SSet.{0}) (A : K.Subcomplex) :
    C(Set.ofPred (fun x : SSet.toTop.obj K => carrier K x ≤ A), SSet.toTop.obj K) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem carrierHomeomorph_inclusion (K : SSet.{0}) (A : K.Subcomplex) :
    (carrierInclusion K A).comp (carrierHomeomorph K A : C(_, _)) =
      (SSet.toTop.map A.ι).hom := by
  ext x
  rfl

/-- The Kan–Quillen realization test of an actual subcomplex inclusion is exactly
    the weak homotopy test of the corresponding intrinsic closed subspace. -/
theorem inclusion_weak_iff_carrier (K : SSet.{0}) (A : K.Subcomplex) :
    realizationWeakEquivalences A.ι ↔ IsWeakHomotopyEquivalence (carrierInclusion K A) := by
  change IsWeakHomotopyEquivalence (SSet.toTop.map A.ι).hom ↔ _
  have hh := homeomorph_isWeakHomotopyEquivalence (carrierHomeomorph K A)
  rw [← carrierHomeomorph_inclusion]
  exact ⟨fun h => hh.of_precomp h, fun h => hh.comp h⟩

/-- Realization commutes with the underlying sets of inverse images of subcomplexes. -/
theorem range_preimage_inclusion {K L : SSet.{0}} (f : K ⟶ L) (A : L.Subcomplex) :
    Set.range (SSet.toTop.map (A.preimage f).ι).hom =
      (SSet.toTop.map f).hom ⁻¹' Set.range (SSet.toTop.map A.ι).hom := by
  ext x
  simp only [Set.mem_preimage, mem_range_inclusion_iff]
  rw [carrier_image, SSet.Subcomplex.image_le_iff]

/-- The inverse-image subcomplex realizes to the actual topological inverse-image subspace. -/
def preimageHomeomorph {K L : SSet.{0}} (f : K ⟶ L) (A : L.Subcomplex) :
    SSet.toTop.obj (A.preimage f : SSet) ≃ₜ
      ((SSet.toTop.map f).hom ⁻¹' Set.range (SSet.toTop.map A.ι).hom) :=
  (inclusion_isClosedEmbedding K (A.preimage f)).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (range_preimage_inclusion f A))

/-- Both projections of the inverse-image square are the actual realized maps. -/
theorem fromPreimage_commutes {K L : SSet.{0}} (f : K ⟶ L) (A : L.Subcomplex) :
    SSet.toTop.map (A.fromPreimage f) ≫ SSet.toTop.map A.ι =
      SSet.toTop.map (A.preimage f).ι ≫ SSet.toTop.map f := by
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, SSet.Subcomplex.fromPreimage_ι]

end

end Thomason.Construction.RealizationPrism

end

end OAI
