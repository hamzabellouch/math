import OAI.CategoryTheory.Thomason.Chains.BarycentricSupportPositive
import OAI.CategoryTheory.Thomason.Gray.GrayMappingInterchangeEvaluation
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.RealizationCellClosure
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

namespace OAI

section

/-! # Every realization point has unique nondegenerate interior coordinates -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

theorem normalizeSimplex_fullSupport (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1)))
    (hx : x ∈ fullSupport n) :
    (normalizeSimplex K s x).2 ∈ fullSupport (normalizeSimplex K s x).1.dim := by
  intro j
  exact HornBarycentric.map_nonzero (SSet.S.mk s).toNπ.toOrderHom
    (SimplexCategory.epi_iff_surjective.mp inferInstance) x hx j

theorem normalizeSupported_fullSupport (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    (normalizeSupported K s x).2 ∈ fullSupport (normalizeSupported K s x).1.dim :=
  normalizeSimplex_fullSupport K _ (HornBarycentric.supportCoordinates x)
    (HornBarycentric.supportCoordinates_nonzero x)

/-- No coordinate of the intrinsic nondegenerate representative vanishes. -/
theorem normalization_fullSupport (K : SSet.{0}) (x : SSet.toTop.obj K) :
    (normalization K x).2 ∈ fullSupport (normalization K x).1.dim := by
  obtain ⟨n, s, p, rfl⟩ := point_representation_simplex K x
  rw [normalization_simplexPoint]
  exact normalizeSupported_fullSupport K s p

/-- The underlying set of a realization is the disjoint union of nondegenerate
    simplex interiors. This does not give the disjoint-union topology. -/
def interiorCoordinatesEquiv (K : SSet.{0}) :
    SSet.toTop.obj K ≃ Σ s : K.N, fullSupport s.dim where
  toFun x := ⟨(normalization K x).1, ⟨(normalization K x).2, normalization_fullSupport K x⟩⟩
  invFun p := simplexPoint K p.1.simplex p.2.val
  left_inv x := denormalize_normalization K x
  right_inv p := by
    have hi : Function.Injective (fun u : Σ s : K.N, fullSupport s.dim =>
        (⟨u.1, u.2.val⟩ : NondegenerateCoordinates K)) := by
      intro u v huv
      rcases u with ⟨su, u, hu⟩
      rcases v with ⟨sv, v, hv⟩
      cases huv
      rfl
    apply hi
    exact normalization_nondegenerate_interior K p.1 p.2.val p.2.property

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Explicit barycentric coordinates of realized simplex boundaries -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Classical
open scoped Simplicial

noncomputable section

/-- A supported simplex of the standard simplex belongs to its boundary precisely
    when some original barycentric coordinate vanishes. -/
theorem standard_boundary_carrier_iff (n : ℕ) (x : StdSimplex ℝ (Fin (n+1))) :
    simplexCarrier (Δ[n] : SSet.{0}) (SSet.yonedaEquiv (𝟙 _)) x ≤ SSet.boundary n ↔
      ∃ i, x.weights i = 0 := by
  let a : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  change SSet.Subcomplex.ofSimplex ((Δ[n] : SSet.{0}).map a.op
    (SSet.yonedaEquiv (𝟙 _))) ≤ SSet.boundary n ↔ _
  rw [SSet.Subcomplex.ofSimplex_le_iff, SSet.yonedaEquiv_naturality,
    Category.comp_id, SSet.yonedaEquiv_map]
  change (¬ Function.Surjective (HornBarycentric.supportMap x)) ↔ _
  constructor
  · intro h
    obtain ⟨i, hi⟩ := not_forall.mp h
    refine ⟨i, ?_⟩
    apply Finsupp.notMem_support_iff.mp
    intro him
    have hr : i ∈ Set.range (HornBarycentric.supportMap x) := by
      rw [HornBarycentric.supportMap_range]
      exact him
    exact hi hr
  · rintro ⟨i, hi⟩ h
    obtain ⟨j, hj⟩ := h i
    exact (HornBarycentric.supportMap_ne x hi j) hj

/-- The actual realized boundary has exactly the familiar zero-coordinate locus. -/
theorem standard_boundary_point_iff (n : ℕ) (x : StdSimplex ℝ (Fin (n+1))) :
    simplexPoint (Δ[n] : SSet.{0}) (SSet.yonedaEquiv (𝟙 _)) x ∈
        Set.range (SSet.toTop.map (SSet.boundary n).ι).hom ↔
      ∃ i, x.weights i = 0 := by
  rw [mem_range_inclusion_iff, carrier_simplexPoint, standard_boundary_carrier_iff]

end

end Thomason.Construction.RealizationPrism

end

section

/-! # The actual realized boundary and its barycentric homeomorphism -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

/-- The parameter map of the identity simplex is the inverse of the standard
    realization homeomorphism. -/
theorem simplexPoint_standard_id (n : ℕ) (x : StdSimplex ℝ (Fin (n+1))) :
    simplexPoint (Δ[n] : SSet.{0}) (SSet.yonedaEquiv (𝟙 _)) x =
      (SimplexCategory.mk n).toTopHomeo.symm x := by
  have he : leg (Δ[n] : SSet.{0})
      (CostructuredArrow.mk (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (𝟙 _)))) =
      SSet.toTopSimplex.inv.app (.mk n) := by
    change SSet.toTopSimplex.inv.app (.mk n) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (𝟙 _))) = _
    rw [SSet.yonedaEquiv.symm_apply_apply, SSet.toTop.map_id]
    exact Category.comp_id _
  exact ConcreteCategory.congr_hom he (ULift.up x)

/-- The boundary locus, including the empty boundary in dimension zero. -/
def boundaryLocus (n : ℕ) : Set (StdSimplex ℝ (Fin (n+1))) :=
  Set.ofPred (fun x => ∃ i, x.weights i = 0)

/-- The barycentric coordinates of the actual boundary inclusion. -/
def boundaryCoordinates (n : ℕ) :
    C(SSet.toTop.obj (SSet.boundary n : SSet.{0}), StdSimplex ℝ (Fin (n+1))) :=
  ((SimplexCategory.mk n).toTopHomeo : C(_, _)).comp
    (SSet.toTop.map (SSet.boundary n).ι).hom

theorem boundaryCoordinates_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (boundaryCoordinates n) :=
  (SimplexCategory.mk n).toTopHomeo.isClosedEmbedding.comp
    (inclusion_isClosedEmbedding _ _)

theorem range_boundaryCoordinates (n : ℕ) :
    Set.range (boundaryCoordinates n) = boundaryLocus n := by
  ext x
  change x ∈ Set.range (boundaryCoordinates n) ↔ ∃ i, x.weights i = 0
  rw [← standard_boundary_point_iff, simplexPoint_standard_id]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hy' : (SimplexCategory.mk n).toTopHomeo
        ((SSet.toTop.map (SSet.boundary n).ι).hom y) = x := hy
    exact (SimplexCategory.mk n).toTopHomeo.injective
      (hy'.trans ((SimplexCategory.mk n).toTopHomeo.apply_symm_apply x).symm)
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change (SimplexCategory.mk n).toTopHomeo
      ((SSet.toTop.map (SSet.boundary n).ι).hom y) = x
    rw [hy, Homeomorph.apply_symm_apply]

/-- The actual boundary realization is homeomorphic to the zero-coordinate
    locus of the barycentric simplex. -/
def boundaryHomeomorph (n : ℕ) :
    SSet.toTop.obj (SSet.boundary n : SSet.{0}) ≃ₜ boundaryLocus n :=
  (boundaryCoordinates_isClosedEmbedding n).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (range_boundaryCoordinates n))

/-- The homeomorphism identifies the realized boundary arrow with the actual
    barycentric subspace inclusion, not just with an abstract homeomorphic pair. -/
theorem boundaryHomeomorph_inclusion (n : ℕ)
    (x : SSet.toTop.obj (SSet.boundary n : SSet.{0})) :
    (boundaryHomeomorph n x).val =
      (SimplexCategory.mk n).toTopHomeo
        ((SSet.toTop.map (SSet.boundary n).ι).hom x) := rfl

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Barycentric boundary lifting and the actual singular weak-equivalence test

This is a compatibility theorem for the concrete realization/singular
adjunction. No Kan--Quillen model structure is assumed.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The literal inclusion of the barycentric boundary subspace. -/
def boundaryInclusion (n : ℕ) :
    TopCat.of (boundaryLocus n) ⟶ TopCat.of (StdSimplex ℝ (Fin (n+1))) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The whole realized boundary arrow agrees with the barycentric pair. -/
def boundaryArrowIso (n : ℕ) :
    Arrow.mk (SSet.toTop.map (SSet.boundary n).ι) ≅ Arrow.mk (boundaryInclusion n) :=
  Arrow.isoMk' _ _ (TopCat.isoOfHomeo (boundaryHomeomorph n))
    (TopCat.isoOfHomeo (SimplexCategory.mk n).toTopHomeo) (by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      exact boundaryHomeomorph_inclusion n x)

/-- Singular boundary filling is exactly lifting against the actual
    barycentric boundary inclusion. -/
theorem singular_boundary_lifting_iff {X Y : TopCat.{0}} (p : X ⟶ Y) (n : ℕ) :
    HasLiftingProperty (SSet.boundary n).ι (TopCat.toSSet.map p) ↔
      HasLiftingProperty (boundaryInclusion n) p :=
  (sSetTopAdj.hasLiftingProperty_iff _ p).symm.trans
    (HasLiftingProperty.iff_of_arrow_iso_left (boundaryArrowIso n) p)

/-- The entire simplicial boundary lifting class has this concrete
    topological interpretation. -/
theorem singular_boundary_rlp_iff {X Y : TopCat.{0}} (p : X ⟶ Y) :
    I.rlp (TopCat.toSSet.map p) ↔ ∀ n, HasLiftingProperty (boundaryInclusion n) p := by
  constructor
  · intro h n
    exact (singular_boundary_lifting_iff p n).mp (h _ (boundary_ι_mem_I n))
  · intro h A B i hi
    obtain ⟨n⟩ := hi
    exact (singular_boundary_lifting_iff p n).mpr (h n)

/-- Maps lifting against every barycentric boundary induce actual weak
    homotopy equivalences of singular realizations. -/
theorem singular_weak_of_boundary_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    (h : ∀ n, HasLiftingProperty (boundaryInclusion n) p) :
    realizationWeakEquivalences (TopCat.toSSet.map p) :=
  boundary_rlp_weak _ ((singular_boundary_rlp_iff p).mpr h)

/-- Elementary barycentric boundary lifts extend over every realized simplicial
    monomorphism. This is the actual topological lifting property, obtained
    through the adjunction and the proved boundary generation theorem. -/
theorem realization_mono_lifting {X Y : TopCat.{0}} (p : X ⟶ Y)
    (h : ∀ n, HasLiftingProperty (boundaryInclusion n) p)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    HasLiftingProperty (SSet.toTop.map i) p := by
  have hp : I.rlp (TopCat.toSSet.map p) := (singular_boundary_rlp_iff p).mpr h
  have hm : (MorphismProperty.monomorphisms SSet.{0}).rlp (TopCat.toSSet.map p) := by
    rwa [SSet.rlp_monomorphisms]
  exact (sSetTopAdj.hasLiftingProperty_iff i p).mpr (hm i (by infer_instance))

/-- A concrete continuous extension preserving the prescribed map on a
    subcomplex and its image under `p`. -/
def relativeBoundaryExtension {X Y : TopCat.{0}} (p : X ⟶ Y)
    (h : ∀ n, HasLiftingProperty (boundaryInclusion n) p)
    (K : SSet.{0}) (A : K.Subcomplex)
    (a : SSet.toTop.obj (A : SSet) ⟶ X) (b : SSet.toTop.obj K ⟶ Y)
    (sq : CommSq a (SSet.toTop.map A.ι) p b) : SSet.toTop.obj K ⟶ X := by
  let := realization_mono_lifting p h A.ι
  exact sq.lift

@[reassoc]
theorem relativeBoundaryExtension_restrict {X Y : TopCat.{0}} (p : X ⟶ Y)
    (h : ∀ n, HasLiftingProperty (boundaryInclusion n) p)
    (K : SSet.{0}) (A : K.Subcomplex)
    (a : SSet.toTop.obj (A : SSet) ⟶ X) (b : SSet.toTop.obj K ⟶ Y)
    (sq : CommSq a (SSet.toTop.map A.ι) p b) :
    SSet.toTop.map A.ι ≫ relativeBoundaryExtension p h K A a b sq = a := by
  let := realization_mono_lifting p h A.ι
  exact sq.fac_left

@[reassoc]
theorem relativeBoundaryExtension_comp {X Y : TopCat.{0}} (p : X ⟶ Y)
    (h : ∀ n, HasLiftingProperty (boundaryInclusion n) p)
    (K : SSet.{0}) (A : K.Subcomplex)
    (a : SSet.toTop.obj (A : SSet) ⟶ X) (b : SSet.toTop.obj K ⟶ Y)
    (sq : CommSq a (SSet.toTop.map A.ι) p b) :
    relativeBoundaryExtension p h K A a b sq ≫ p = b := by
  let := realization_mono_lifting p h A.ι
  exact sq.fac_right

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Actual attaching maps of nondegenerate realization cells -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite Topology
open scoped Simplicial

noncomputable section

theorem simplexPoint_as_realized_map (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) :
    simplexPoint K s x = (SSet.toTop.map (SSet.yonedaEquiv.symm s)).hom
      ((SimplexCategory.mk n).toTopHomeo.symm x) := by
  have h := simplexPoint_naturality (SSet.yonedaEquiv.symm s)
    (SSet.yonedaEquiv (𝟙 _)) x
  rw [SSet.yonedaEquiv_symm_app_id, simplexPoint_standard_id] at h
  exact h.symm

theorem boundaryLocus_eq_compl_fullSupport (n : ℕ) :
    boundaryLocus n = (fullSupport n)ᶜ := by
  ext x
  change (∃ i, x.weights i = 0) ↔ ¬ ∀ i, x.weights i ≠ 0
  simp only [not_forall, not_not]

/-- The actual attaching map is the realization of the simplicial boundary
    followed by the given characteristic simplex. -/
def cellBoundaryMap (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n))) :
    SSet.toTop.obj (SSet.boundary n : SSet.{0}) ⟶ SSet.toTop.obj K :=
  SSet.toTop.map ((SSet.boundary n).ι ≫ SSet.yonedaEquiv.symm s)

theorem cellBoundaryMap_coordinates (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) :
    (cellBoundaryMap K s).hom = (simplexPoint K s).comp (boundaryCoordinates n) := by
  apply ContinuousMap.ext
  intro x
  change (SSet.toTop.map ((SSet.boundary n).ι ≫ SSet.yonedaEquiv.symm s)).hom x = _
  rw [SSet.toTop.map_comp]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm s)).hom
    ((SSet.toTop.map (SSet.boundary n).ι).hom x) =
      simplexPoint K s ((SimplexCategory.mk n).toTopHomeo
        ((SSet.toTop.map (SSet.boundary n).ι).hom x))
  rw [simplexPoint_as_realized_map, Homeomorph.symm_apply_apply]

theorem range_cellBoundaryMap (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) :
    Set.range (cellBoundaryMap K s).hom = simplexPoint K s '' boundaryLocus n := by
  rw [cellBoundaryMap_coordinates]
  change Set.range ((simplexPoint K s) ∘ (boundaryCoordinates n)) = _
  rw [Set.range_comp, range_boundaryCoordinates]

/-- The boundary image is exactly the part of the closed characteristic cell
    outside its own interior, allowing arbitrary identifications of faces. -/
theorem cell_boundary_eq_closure_diff (K : SSet.{0}) (s : K.N) :
    Set.range (cellBoundaryMap K s.simplex).hom =
      closure (simplexPoint K s.simplex '' fullSupport s.dim) \
        (simplexPoint K s.simplex '' fullSupport s.dim) := by
  rw [range_cellBoundaryMap, boundaryLocus_eq_compl_fullSupport, closure_cellInterior]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    intro hi
    have hx' : x ∈ fullSupport s.dim := by
      rw [← interior_preimage_image K s]
      exact hi
    exact hx hx'
  · rintro ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, ?_, rfl⟩
    intro hx
    exact hy ⟨x, hx, rfl⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Cell support, subcomplex membership, and the dimension of attaching maps -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- An interior point has the whole characteristic simplex as its carrier. -/
theorem carrier_interior (K : SSet.{0}) {n : ℕ} (s : K.obj (.op (.mk n)))
    (x : StdSimplex ℝ (Fin (n+1))) (hx : x ∈ fullSupport n) :
    carrier K (simplexPoint K s x) = SSet.Subcomplex.ofSimplex s := by
  rw [carrier_simplexPoint]
  let f : SimplexCategory.mk (HornBarycentric.supportLen x) ⟶ .mk n :=
    SimplexCategory.Hom.mk (HornBarycentric.supportMap x).toOrderHom
  have hs : Function.Surjective f.toOrderHom := by
    intro i
    have hi : i ∈ Set.range (HornBarycentric.supportMap x) := by
      rw [HornBarycentric.supportMap_range]
      exact Finsupp.mem_support_iff.mpr (hx i)
    exact hi
  let : Epi f := SimplexCategory.epi_iff_surjective.mpr hs
  exact SSet.Subcomplex.ofSimplex_map_of_epi f s

/-- A subcomplex contains a point of a simplex interior exactly when it
    contains the simplex itself. -/
theorem interior_mem_subcomplex_iff (K : SSet.{0}) (A : K.Subcomplex) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) (hx : x ∈ fullSupport n) :
    simplexPoint K s x ∈ Set.range (SSet.toTop.map A.ι).hom ↔ s ∈ A.obj _ := by
  rw [mem_range_inclusion_iff, carrier_interior K s x hx,
    SSet.Subcomplex.ofSimplex_le_iff]

/-- Boundary points of an `n`-simplex belong to cells of strictly smaller
    dimension, including when the original simplex or its faces are degenerate. -/
theorem boundary_point_dimension_lt (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n))) (x : StdSimplex ℝ (Fin (n+1))) (hx : x ∈ boundaryLocus n) :
    (normalization K (simplexPoint K s x)).1.dim < n := by
  have hnot : x ∉ fullSupport n := by
    rwa [boundaryLocus_eq_compl_fullSupport] at hx
  have hlen : HornBarycentric.supportLen x < n := by
    by_contra hn
    exact hnot (fullSupport_of_supportLen_ge x (by omega))
  exact lt_of_le_of_lt (normalization_dim_le_supportLen K s x) hlen

/-- The actual attaching map lands entirely in lower-dimensional cells. -/
theorem cellBoundaryMap_dimension_lt (K : SSet.{0}) {n : ℕ}
    (s : K.obj (.op (.mk n)))
    (x : SSet.toTop.obj (SSet.boundary n : SSet.{0})) :
    (normalization K ((cellBoundaryMap K s).hom x)).1.dim < n := by
  have hx : (cellBoundaryMap K s).hom x ∈ Set.range (cellBoundaryMap K s).hom := ⟨x, rfl⟩
  rw [range_cellBoundaryMap] at hx
  obtain ⟨y, hy, he⟩ := hx
  rw [← he]
  exact boundary_point_dimension_lt K s y hy

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Realization by actual barycentric cell attachments

The simplicial skeletal presentation maps to a topological relative cell
complex. The basic cell arrows are the literal inclusions of the
zero-coordinate loci, using the constructed boundary-arrow isomorphisms.
-/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Convexity
open scoped Simplicial

noncomputable section

abbrev simplicialBoundaryCell (n : ℕ) (_ : Unit) := (SSet.boundary n).ι

abbrev realizedBoundaryCell (n : ℕ) (_ : Unit) := SSet.toTop.map (SSet.boundary n).ι

abbrev barycentricBoundaryCell (n : ℕ) (_ : Unit) := boundaryInclusion n

/-- Realization carries a simultaneous simplicial boundary attachment to
    the corresponding simultaneous topological attachment. -/
def realizeBoundaryAttachment {X Y : SSet.{0}} {n : ℕ} {f : X ⟶ Y}
    (c : AttachCells.{0} (simplicialBoundaryCell n) f) :
    AttachCells.{0} (realizedBoundaryCell n) (SSet.toTop.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk (SSet.toTop.obj c.cofan₁.pt) (fun i => SSet.toTop.map (c.cofan₁.inj i))
  cofan₂ := Cofan.mk (SSet.toTop.obj c.cofan₂.pt) (fun i => SSet.toTop.map (c.cofan₂.inj i))
  isColimit₁ := isColimitCofanMkObjOfIsColimit SSet.toTop _ _
    (IsColimit.ofIsoColimit c.isColimit₁ (Cofan.ext (Iso.refl _) (fun _ => by simp)))
  isColimit₂ := isColimitCofanMkObjOfIsColimit SSet.toTop _ _
    (IsColimit.ofIsoColimit c.isColimit₂ (Cofan.ext (Iso.refl _) (fun _ => by simp)))
  m := SSet.toTop.map c.m
  hm i := by
    change SSet.toTop.map (c.cofan₁.inj i) ≫ SSet.toTop.map c.m =
      SSet.toTop.map (SSet.boundary n).ι ≫ SSet.toTop.map (c.cofan₂.inj i)
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, c.hm]
  g₁ := SSet.toTop.map c.g₁
  g₂ := SSet.toTop.map c.g₂
  isPushout := SSet.toTop.map_isPushout c.isPushout

/-- The topological skeletal presentation with the original realized
    boundary arrows. -/
def realizedCellComplexOfMono {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] :
    RelativeCellComplex.{0} realizedBoundaryCell (SSet.toTop.map i) := by
  let : PreservesWellOrderContinuousOfShape ℕ SSet.toTop.{0} := {}
  exact {
    toTransfiniteCompositionOfShape :=
      (SSet.relativeCellComplexOfMono i).toTransfiniteCompositionOfShape.map SSet.toTop
    attachCells n hn := realizeBoundaryAttachment
      ((SSet.relativeCellComplexOfMono i).attachCells n hn) }

/-- Every realized monomorphism is obtained by attaching actual barycentric
    `n`-simplices along their boundaries at stage `n`. -/
def barycentricCellComplexOfMono {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] :
    RelativeCellComplex.{0} barycentricBoundaryCell (SSet.toTop.map i) where
  toTransfiniteCompositionOfShape :=
    (realizedCellComplexOfMono i).toTransfiniteCompositionOfShape
  attachCells n hn := ((realizedCellComplexOfMono i).attachCells n hn).reindexCellTypes
    (barycentricBoundaryCell n) id (fun _ => boundaryArrowIso n)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Actual images and unions of realized subcomplexes -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Convexity Opposite
open scoped Simplicial

noncomputable section

/-- Subcomplex membership can be tested on the unique nondegenerate
    interior representative of the point. -/
theorem mem_range_iff_normalization (K : SSet.{0}) (A : K.Subcomplex)
    (x : SSet.toTop.obj K) :
    x ∈ Set.range (SSet.toTop.map A.ι).hom ↔
      (normalization K x).1.simplex ∈ A.obj _ := by
  have h := interior_mem_subcomplex_iff K A (normalization K x).1.simplex
    (normalization K x).2 (normalization_fullSupport K x)
  have he : simplexPoint K (normalization K x).1.simplex (normalization K x).2 = x :=
    denormalize_normalization K x
  rw [he] at h
  exact h

/-- Realization carries an arbitrary subcomplex union to the literal union
    of the corresponding topological subspaces. -/
theorem range_iSup_inclusion (K : SSet.{0}) {ι : Type} (A : ι → K.Subcomplex) :
    Set.range (SSet.toTop.map (iSup A).ι).hom =
      ⋃ i, Set.range (SSet.toTop.map (A i).ι).hom := by
  ext x
  simp only [Set.mem_iUnion, mem_range_iff_normalization]
  rw [Subfunctor.iSup_obj]
  simp only [Set.mem_iUnion]

/-- The actual point-set image of a realized simplicial map is exactly
    the realization of its simplicial image subcomplex. -/
theorem range_realized_map {K L : SSet.{0}} (f : K ⟶ L) :
    Set.range (SSet.toTop.map f).hom =
      Set.range (SSet.toTop.map (SSet.Subcomplex.range f).ι).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_range_inclusion_iff, carrier_image]
    rw [SSet.Subcomplex.image_le_iff]
    intro n s hs
    exact ⟨s, rfl⟩
  · intro hx
    rw [mem_range_iff_normalization] at hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨simplexPoint K s (normalization L x).2, ?_⟩
    rw [simplexPoint_naturality, hs]
    exact denormalize_normalization L x

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Compact maps and homotopies land in one stage of an increasing exhaustion -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory Topology

noncomputable section

/-- A compact subset of an exhausted realization lies in one actual stage.
The proof bounds its finitely many intrinsic carriers simultaneously. -/
theorem compact_subset_stage (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤)
    (C : Set (SSet.toTop.obj K)) (hC : IsCompact C) :
    ∃ n, C ⊆ Set.range (SSet.toTop.map (A n).ι).hom := by
  classical
  have hx (x : SSet.toTop.obj K) :
      ∃ n, x ∈ Set.range (SSet.toTop.map (A n).ι).hom := by
    have hm : x ∈ Set.range (SSet.toTop.map (iSup A).ι).hom := by
      apply (mem_range_inclusion_iff K (iSup A) x).mpr
      rw [hcover]
      exact le_top
    rw [range_iSup_inclusion] at hm
    exact Set.mem_iUnion.mp hm
  let I := carrier K '' C
  have : Finite I := (compact_carriers_finite K C hC).to_subtype
  let k : I → ℕ := fun c => (hx (Classical.choose c.property)).choose
  have hk (c : I) : c.val ≤ A (k c) := by
    have hc := Classical.choose_spec c.property
    have hm := (hx (Classical.choose c.property)).choose_spec
    have hl := (mem_range_inclusion_iff K _ _).mp hm
    exact hc.2.symm ▸ hl
  let : Fintype I := Fintype.ofFinite I
  refine ⟨Finset.univ.sup k, ?_⟩
  intro x hxC
  let c : I := ⟨carrier K x, x, hxC, rfl⟩
  apply (mem_range_inclusion_iff K _ x).mpr
  exact (hk c).trans (hA (Finset.le_sup (Finset.mem_univ c)))

/-- Every compact continuous map factors continuously through a single stage,
with exact equality after the actual inclusion. -/
theorem compact_map_factors_stage {P : Type} [TopologicalSpace P] [CompactSpace P]
    (K : SSet.{0}) (A : ℕ → K.Subcomplex) (hA : Monotone A) (hcover : iSup A = ⊤)
    (f : C(P, SSet.toTop.obj K)) :
    ∃ (n : ℕ) (g : C(P, SSet.toTop.obj (A n : SSet))),
      (SSet.toTop.map (A n).ι).hom.comp g = f := by
  obtain ⟨n, hn⟩ := compact_subset_stage K A hA hcover (Set.range f)
    (isCompact_range f.continuous)
  have hf (x : P) : f x ∈ Set.range (SSet.toTop.map (A n).ι).hom := hn ⟨x, rfl⟩
  let g : P → SSet.toTop.obj (A n : SSet) := fun x => (hf x).choose
  have hg (x : P) : (SSet.toTop.map (A n).ι).hom (g x) = f x := (hf x).choose_spec
  have hc : Continuous g := by
    apply (inclusion_isClosedEmbedding K (A n)).isEmbedding.continuous_iff.mpr
    have he : (SSet.toTop.map (A n).ι).hom ∘ g = f := funext hg
    rw [he]
    exact f.continuous
  exact ⟨n, ⟨g, hc⟩, ContinuousMap.ext hg⟩

/-- The stage can be chosen beyond any previously fixed stage. -/
theorem compact_map_factors_stage_after {P : Type} [TopologicalSpace P] [CompactSpace P]
    (K : SSet.{0}) (A : ℕ → K.Subcomplex) (hA : Monotone A) (hcover : iSup A = ⊤)
    (m : ℕ) (f : C(P, SSet.toTop.obj K)) :
    ∃ (n : ℕ), m ≤ n ∧ ∃ g : C(P, SSet.toTop.obj (A n : SSet)),
      (SSet.toTop.map (A n).ι).hom.comp g = f := by
  obtain ⟨n, g, hg⟩ := compact_map_factors_stage K A hA hcover f
  let j := SSet.Subcomplex.homOfLE (hA (Nat.le_max_left n m))
  refine ⟨max n m, Nat.le_max_right n m, (SSet.toTop.map j).hom.comp g, ?_⟩
  have he : SSet.toTop.map j ≫ SSet.toTop.map (A (max n m)).ι = SSet.toTop.map (A n).ι := by
    rw [← SSet.toTop.map_comp]
    rfl
  apply ContinuousMap.ext
  intro x
  exact (congrArg (fun q => q.hom (g x)) he).trans
    (congrArg (fun q : C(_, _) => q x) hg)

/-- Two compact maps with unrelated domains have a common stage. This
also synchronizes point representatives of different path components. -/
theorem compact_pair_factors_stage {P Q : Type}
    [TopologicalSpace P] [CompactSpace P] [TopologicalSpace Q] [CompactSpace Q]
    (K : SSet.{0}) (A : ℕ → K.Subcomplex) (hA : Monotone A) (hcover : iSup A = ⊤)
    (f : C(P, SSet.toTop.obj K)) (g : C(Q, SSet.toTop.obj K)) :
    ∃ (n : ℕ) (f' : C(P, SSet.toTop.obj (A n : SSet)))
      (g' : C(Q, SSet.toTop.obj (A n : SSet))),
      (SSet.toTop.map (A n).ι).hom.comp f' = f ∧
      (SSet.toTop.map (A n).ι).hom.comp g' = g := by
  obtain ⟨n, hn⟩ := compact_subset_stage K A hA hcover (Set.range f ∪ Set.range g)
    ((isCompact_range f.continuous).union (isCompact_range g.continuous))
  have hf (x : P) : f x ∈ Set.range (SSet.toTop.map (A n).ι).hom := hn (Or.inl ⟨x, rfl⟩)
  have hg (x : Q) : g x ∈ Set.range (SSet.toTop.map (A n).ι).hom := hn (Or.inr ⟨x, rfl⟩)
  let f' : P → SSet.toTop.obj (A n : SSet) := fun x => (hf x).choose
  let g' : Q → SSet.toTop.obj (A n : SSet) := fun x => (hg x).choose
  have ef (x : P) : (SSet.toTop.map (A n).ι).hom (f' x) = f x := (hf x).choose_spec
  have eg (x : Q) : (SSet.toTop.map (A n).ι).hom (g' x) = g x := (hg x).choose_spec
  have cf : Continuous f' := by
    apply (inclusion_isClosedEmbedding K (A n)).isEmbedding.continuous_iff.mpr
    have he : (SSet.toTop.map (A n).ι).hom ∘ f' = f := funext ef
    rw [he]
    exact f.continuous
  have cg : Continuous g' := by
    apply (inclusion_isClosedEmbedding K (A n)).isEmbedding.continuous_iff.mpr
    have he : (SSet.toTop.map (A n).ι).hom ∘ g' = g := funext eg
    rw [he]
    exact g.continuous
  exact ⟨n, ⟨f', cf⟩, ⟨g', cg⟩, ContinuousMap.ext ef, ContinuousMap.ext eg⟩

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Exact finite-stage control of based cubes and their relative homotopies -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory

noncomputable section

/-- A based cube whose basepoint is already in one stage lifts to a later
stage with that same basepoint and its entire boundary fixed. -/
theorem based_cube_factors_stage (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤) (m : ℕ)
    (x : SSet.toTop.obj (A m : SSet)) (d : ℕ)
    (p : GenLoop (Fin d) (SSet.toTop.obj K) ((SSet.toTop.map (A m).ι).hom x)) :
    ∃ (n : ℕ) (hn : m ≤ n),
      ∃ q : GenLoop (Fin d) (SSet.toTop.obj (A n : SSet))
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom x),
        ∀ t, (SSet.toTop.map (A n).ι).hom (q t) = p t := by
  obtain ⟨n, hn, g, hg⟩ := compact_map_factors_stage_after K A hA hcover m p.val
  let j := SSet.Subcomplex.homOfLE (hA hn)
  have hj : SSet.toTop.map j ≫ SSet.toTop.map (A n).ι = SSet.toTop.map (A m).ι := by
    rw [← SSet.toTop.map_comp]
    rfl
  have he (t) : (SSet.toTop.map (A n).ι).hom (g t) = p t :=
    congrArg (fun q : C(_, _) => q t) hg
  refine ⟨n, hn, ⟨g, ?_⟩, he⟩
  intro t ht
  apply inclusion_injective K (A n)
  exact (he t).trans ((p.property t ht).trans (congrArg (fun q => q.hom x) hj).symm)

/-- A homotopy between two cubes in one stage is already a homotopy in a
later stage, with the original endpoint cubes and whole boundary retained. -/
theorem based_homotopy_factors_stage (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤) (m : ℕ)
    (x : SSet.toTop.obj (A m : SSet)) (d : ℕ)
    (p q : GenLoop (Fin d) (SSet.toTop.obj (A m : SSet)) x)
    (H : (HomotopyMaps.loopMap (SSet.toTop.map (A m).ι).hom p).val.HomotopyRel
      (HomotopyMaps.loopMap (SSet.toTop.map (A m).ι).hom q).val (Cube.boundary (Fin d))) :
    ∃ (n : ℕ) (hn : m ≤ n),
      Nonempty ((HomotopyMaps.loopMap
        (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom p).val.HomotopyRel
        (HomotopyMaps.loopMap
          (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom q).val
        (Cube.boundary (Fin d))) := by
  obtain ⟨n, hn, F, hF⟩ := compact_map_factors_stage_after K A hA hcover m H.toContinuousMap
  let j := SSet.Subcomplex.homOfLE (hA hn)
  have hj : SSet.toTop.map j ≫ SSet.toTop.map (A n).ι = SSet.toTop.map (A m).ι := by
    rw [← SSet.toTop.map_comp]
    rfl
  have he (z) : (SSet.toTop.map (A n).ι).hom (F z) = H z :=
    congrArg (fun q : C(_, _) => q z) hF
  refine ⟨n, hn, ⟨{ toContinuousMap := F, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }⟩⟩
  · intro t
    apply inclusion_injective K (A n)
    exact (he (0, t)).trans ((H.apply_zero t).trans
      (congrArg (fun z => z.hom (p t)) hj).symm)
  · intro t
    apply inclusion_injective K (A n)
    exact (he (1, t)).trans ((H.apply_one t).trans
      (congrArg (fun z => z.hom (q t)) hj).symm)
  · intro s t ht
    apply inclusion_injective K (A n)
    exact (he (s, t)).trans ((H.eq_fst s ht).trans (congrArg (fun z => z.hom (p t)) hj).symm)

/-- Equality of homotopy classes in the exhausted realization is witnessed
in one later stage, retaining the original chosen basepoint. -/
theorem homotopyGroup_eventual_eq (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤) (m : ℕ)
    (x : SSet.toTop.obj (A m : SSet)) (d : ℕ)
    (a b : HomotopyGroup.Pi d (SSet.toTop.obj (A m : SSet)) x)
    (hab : HomotopyMaps.groupMap (SSet.toTop.map (A m).ι).hom d x a =
      HomotopyMaps.groupMap (SSet.toTop.map (A m).ι).hom d x b) :
    ∃ (n : ℕ) (hn : m ≤ n),
      HomotopyMaps.groupMap (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom d x a =
      HomotopyMaps.groupMap (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom d x b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      obtain ⟨H⟩ : GenLoop.Homotopic
          (HomotopyMaps.loopMap (SSet.toTop.map (A m).ι).hom p)
          (HomotopyMaps.loopMap (SSet.toTop.map (A m).ι).hom q) := Quotient.exact hab
      obtain ⟨n, hn, ⟨H'⟩⟩ := based_homotopy_factors_stage K A hA hcover m x d p q H
      exact ⟨n, hn, Quotient.sound ⟨H'⟩⟩

/-- Equality of components also occurs at a finite stage. -/
theorem components_eventual_eq (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤) (m : ℕ)
    (a b : ZerothHomotopy (SSet.toTop.obj (A m : SSet)))
    (hab : HomotopyMaps.componentsMap (SSet.toTop.map (A m).ι).hom a =
      HomotopyMaps.componentsMap (SSet.toTop.map (A m).ι).hom b) :
    ∃ (n : ℕ) (hn : m ≤ n),
      HomotopyMaps.componentsMap (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom a =
      HomotopyMaps.componentsMap (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom b := by
  induction a using ZerothHomotopy.rec with
  | mk x =>
    induction b using ZerothHomotopy.rec with
    | mk y =>
      obtain ⟨H⟩ : Joined ((SSet.toTop.map (A m).ι).hom x)
        ((SSet.toTop.map (A m).ι).hom y) := Quotient.exact hab
      obtain ⟨n, hn, g, hg⟩ := compact_map_factors_stage_after K A hA hcover m H.toContinuousMap
      have he (t) : (SSet.toTop.map (A n).ι).hom (g t) = H t :=
        congrArg (fun q : C(_, _) => q t) hg
      have hj : SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn)) ≫
          SSet.toTop.map (A n).ι = SSet.toTop.map (A m).ι := by
        rw [← SSet.toTop.map_comp]
        rfl
      let q : Path ((SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom x)
          ((SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom y) := {
        toContinuousMap := g
        source' := by
          apply inclusion_injective K (A n)
          exact (he 0).trans (H.source.trans (congrArg (fun f => f.hom x) hj).symm)
        target' := by
          apply inclusion_injective K (A n)
          exact (he 1).trans (H.target.trans (congrArg (fun f => f.hom y) hj).symm) }
      exact ⟨n, hn, ZerothHomotopy.sound q⟩

/-- A pair of based cubes can be placed in the same stage, beyond the stage
of their specified basepoint. Both cubes retain their entire boundary. -/
theorem based_pair_factors_stage (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤) (m : ℕ)
    (x : SSet.toTop.obj (A m : SSet)) (d : ℕ)
    (p q : GenLoop (Fin d) (SSet.toTop.obj K) ((SSet.toTop.map (A m).ι).hom x)) :
    ∃ (n : ℕ) (hn : m ≤ n),
      ∃ p' q' : GenLoop (Fin d) (SSet.toTop.obj (A n : SSet))
        ((SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom x),
        (∀ t, (SSet.toTop.map (A n).ι).hom (p' t) = p t) ∧
        (∀ t, (SSet.toTop.map (A n).ι).hom (q' t) = q t) := by
  obtain ⟨i, hi, p', hp⟩ := based_cube_factors_stage K A hA hcover m x d p
  obtain ⟨j, hj, q', hq⟩ := based_cube_factors_stage K A hA hcover m x d q
  let n := max i j
  let hn : m ≤ n := hi.trans (Nat.le_max_left i j)
  let fi := SSet.toTop.map (SSet.Subcomplex.homOfLE (hA (Nat.le_max_left i j)))
  let fj := SSet.toTop.map (SSet.Subcomplex.homOfLE (hA (Nat.le_max_right i j)))
  have ei : fi.hom ((SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hi))).hom x) =
      (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom x := by
    have he : SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hi)) ≫ fi =
        SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn)) := by
      rw [← SSet.toTop.map_comp]
      rfl
    exact congrArg (fun f => f.hom x) he
  have ej : fj.hom ((SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hj))).hom x) =
      (SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn))).hom x := by
    have he : SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hj)) ≫ fj =
        SSet.toTop.map (SSet.Subcomplex.homOfLE (hA hn)) := by
      rw [← SSet.toTop.map_comp]
      rfl
    exact congrArg (fun f => f.hom x) he
  refine ⟨n, hn, HomotopyMaps.basedLoopMap fi.hom ei p',
    HomotopyMaps.basedLoopMap fj.hom ej q', ?_, ?_⟩
  · intro t
    have he : fi ≫ SSet.toTop.map (A n).ι = SSet.toTop.map (A i).ι := by
      rw [← SSet.toTop.map_comp]
      rfl
    exact (congrArg (fun f => f.hom (p' t)) he).trans (hp t)
  · intro t
    have he : fj ≫ SSet.toTop.map (A n).ι = SSet.toTop.map (A j).ι := by
      rw [← SSet.toTop.map_comp]
      rfl
    exact (congrArg (fun f => f.hom (q' t)) he).trans (hq t)

end

end Thomason.Construction.RealizationPrism

end

section

/-! # Passing actual weak equivalences through increasing simplicial exhaustions -/

namespace Thomason.Construction.RealizationPrism

open CategoryTheory

noncomputable section

/-- If the inclusion of the initial stage into every stage is weak, then
its inclusion into the exhausted realization is weak. Compact cubes and
relative homotopies provide the required finite-stage witnesses. -/
theorem exhaustion_initial_weak (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤)
    (hW : ∀ n, realizationWeakEquivalences
      (SSet.Subcomplex.homOfLE (hA (Nat.zero_le n)))) :
    realizationWeakEquivalences (A 0).ι := by
  let j (n : ℕ) := SSet.Subcomplex.homOfLE (hA (Nat.zero_le n))
  have hj (n : ℕ) : SSet.toTop.map (j n) ≫ SSet.toTop.map (A n).ι =
      SSet.toTop.map (A 0).ι := by
    rw [← SSet.toTop.map_comp]
    rfl
  change IsWeakHomotopyEquivalence (SSet.toTop.map (A 0).ι).hom
  constructor
  · constructor
    · intro a b hab
      induction a using ZerothHomotopy.rec with
      | mk x =>
        induction b using ZerothHomotopy.rec with
        | mk y =>
          obtain ⟨H⟩ : Joined ((SSet.toTop.map (A 0).ι).hom x)
              ((SSet.toTop.map (A 0).ι).hom y) := Quotient.exact hab
          obtain ⟨n, _, g, hg⟩ := compact_map_factors_stage_after K A hA hcover 0 H.toContinuousMap
          have he (t) : (SSet.toTop.map (A n).ι).hom (g t) = H t :=
            congrArg (fun q : C(_, _) => q t) hg
          let q : Path ((SSet.toTop.map (j n)).hom x) ((SSet.toTop.map (j n)).hom y) := {
            toContinuousMap := g
            source' := by
              apply inclusion_injective K (A n)
              exact (he 0).trans (H.source.trans (congrArg (fun f => f.hom x) (hj n)).symm)
            target' := by
              apply inclusion_injective K (A n)
              exact (he 1).trans (H.target.trans (congrArg (fun f => f.hom y) (hj n)).symm) }
          exact (hW n).1.1 (ZerothHomotopy.sound q)
    · intro a
      induction a using ZerothHomotopy.rec with
      | mk y =>
        obtain ⟨n, g, hg⟩ := compact_map_factors_stage K A hA hcover
          (ContinuousMap.const Unit y)
        obtain ⟨x, hx⟩ := (hW n).1.2 (ZerothHomotopy.mk (g ()))
        refine ⟨x, ?_⟩
        have hc := congrArg (fun f => HomotopyMaps.componentsMap f.hom) (hj n)
        change HomotopyMaps.componentsMap
          ((SSet.toTop.map (A n).ι).hom.comp (SSet.toTop.map (j n)).hom) = _ at hc
        rw [HomotopyMaps.componentsMap_comp] at hc
        rw [← hc]
        change HomotopyMaps.componentsMap (SSet.toTop.map (A n).ι).hom
          (HomotopyMaps.componentsMap (SSet.toTop.map (j n)).hom x) = _
        rw [hx]
        exact congrArg ZerothHomotopy.mk (congrArg (fun q : C(_, _) => q ()) hg)
  · intro d x
    constructor
    · intro a b hab
      obtain ⟨n, _, he⟩ := homotopyGroup_eventual_eq K A hA hcover 0 x (d+1) a b hab
      exact (hW n).2 d x |>.1 he
    · intro b
      induction b using Quotient.inductionOn with
      | h p =>
        obtain ⟨n, _, q, hq⟩ := based_cube_factors_stage K A hA hcover 0 x (d+1) p
        obtain ⟨a, ha⟩ := (hW n).2 d x |>.2 (Quotient.mk _ q)
        refine ⟨a, ?_⟩
        have hx : (SSet.toTop.map (A n).ι).hom ((SSet.toTop.map (j n)).hom x) =
            (SSet.toTop.map (A 0).ι).hom x := congrArg (fun f => f.hom x) (hj n)
        have hc (c : HomotopyGroup.Pi (d+1) (SSet.toTop.obj (A 0 : SSet)) x) :
            HomotopyMaps.basedGroupMap (SSet.toTop.map (A n).ι).hom hx (d+1)
                (HomotopyMaps.groupMap (SSet.toTop.map (j n)).hom (d+1) x c) =
              HomotopyMaps.groupMap (SSet.toTop.map (A 0).ι).hom (d+1) x c := by
          induction c using Quotient.inductionOn with
          | h c =>
            apply congrArg (Quotient.mk _)
            apply GenLoop.ext
            intro t
            exact congrArg (fun f => f.hom (c t)) (hj n)
        rw [← hc a, ha]
        apply congrArg (Quotient.mk _)
        apply GenLoop.ext
        exact hq

/-- Successive weak inclusions in a simplicial exhaustion induce a weak
inclusion of its initial stage into the whole realization. -/
theorem exhaustion_weak_of_successor (K : SSet.{0}) (A : ℕ → K.Subcomplex)
    (hA : Monotone A) (hcover : iSup A = ⊤)
    (hW : ∀ n, realizationWeakEquivalences
      (SSet.Subcomplex.homOfLE (hA (Nat.le_succ n)))) :
    realizationWeakEquivalences (A 0).ι := by
  apply exhaustion_initial_weak K A hA hcover
  intro n
  induction n with
  | zero =>
      exact realizationWeakEquivalences.id_mem _
  | succ n ih =>
      exact realizationWeakEquivalences.comp_mem _ _ ih (hW n)

end

end Thomason.Construction.RealizationPrism

end

end OAI
