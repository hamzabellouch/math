import OAI.CategoryTheory.Thomason.Chains.FiniteChainMesh
import OAI.CategoryTheory.Thomason.Simplicial.ExhaustionWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetCoordinates
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

section

/-! # Uniform shrinking on the actual iterated chain posets

The same dimension bound controls every stage, although the number of
vertices increases. Vertex locations are recursively their actual face
barycenters, so the estimate applies to geometric subdivision.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Filter

noncomputable section

def meshRatio (N : ℕ) : ℝ := 1-1/((N : ℝ)+1)

theorem meshRatio_nonneg (N : ℕ) : 0 ≤ meshRatio N := by
  unfold meshRatio
  apply sub_nonneg.mpr
  apply (div_le_one (by positivity : (0 : ℝ) < (N : ℝ)+1)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem meshRatio_lt_one (N : ℕ) : meshRatio N < 1 := by
  unfold meshRatio
  have : (0 : ℝ) < 1/((N : ℝ)+1) := by positivity
  linarith

def iteratedAffineVertices (P : PartOrd.{0}) [Finite P] {d : ℕ}
    (x : P → Fin d → ℝ) : (r : ℕ) → iteratedChainPoset P r → Fin d → ℝ
  | 0 => x
  | r+1 => by
      letI := Fintype.ofFinite (iteratedChainPoset P r)
      exact chainAverage (iteratedAffineVertices P x r)

theorem iteratedAffineVertices_mesh (P : PartOrd.{0}) [Finite P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D) (r : ℕ) :
    ChainMesh (iteratedAffineVertices P x r) ((meshRatio N)^r*D) := by
  induction r with
  | zero =>
      change ChainMesh x ((meshRatio N)^0*D)
      simpa only [pow_zero, one_mul] using hx
  | succ r ih =>
      let := Fintype.ofFinite (iteratedChainPoset P r)
      change ChainMesh (chainAverage (iteratedAffineVertices P x r))
        ((meshRatio N)^(r+1)*D)
      have h := chainMesh_average (iteratedChainPoset_cardBound P hP r)
        (iteratedAffineVertices P x r) ((meshRatio N)^r*D)
        (mul_nonneg (pow_nonneg (meshRatio_nonneg N) r) hD) ih
      simpa only [iteratedAffineVertices, meshRatio, pow_succ, mul_assoc,
        mul_left_comm, mul_comm] using h

theorem iteratedAffineVertices_mesh_tendsto_zero (N : ℕ) (D : ℝ) :
    Tendsto (fun r : ℕ => (meshRatio N)^r*D) atTop (nhds 0) := by
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (meshRatio_nonneg N)
      (meshRatio_lt_one N)).mul_const D

/-- Every positive geometric scale is reached uniformly on all chains
of one subdivision stage. -/
theorem exists_iteratedAffineVertices_small (P : PartOrd.{0}) [Finite P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ i j : iteratedChainPoset P r, (i ≤ j ∨ j ≤ i) →
      dist (iteratedAffineVertices P x r i) (iteratedAffineVertices P x r j) < ε := by
  obtain ⟨r, hr⟩ := (Tendsto.eventually_lt_const hε
    (iteratedAffineVertices_mesh_tendsto_zero N D)).exists
  exact ⟨r, fun i j hij =>
    (iteratedAffineVertices_mesh P hP x D hD hx r i j hij).trans_lt hr⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Affine geometry on actual finite-poset realizations

The mesh bounds apply to the complete closed characteristic simplices,
including their faces, rather than only to abstract vertex locations.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory Convexity PartialOrder

noncomputable section

theorem finiteAffineValue_map {P Q : Type} [Fintype P] [Fintype Q]
    (f : P → Q) (x : Q → ℝ) (p : StdSimplex ℝ P) :
    finiteAffineValue x (StdSimplex.map f p) = finiteAffineValue (x ∘ f) p := by
  classical
  have hs {R : Type} [Fintype R] (a : R →₀ ℝ) (y : R → ℝ) :
      (∑ i, a i*y i) = a.sum (fun i r => r*y i) :=
    (Finsupp.sum_fintype a (fun i r => r*y i) (fun _ => zero_mul _)).symm
  unfold finiteAffineValue
  rw [hs, hs]
  change (p.weights.mapDomain f).sum (fun i r => r*x i) = _
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)]
  rfl

def affineRealization {P : Type} [PartialOrder P] [Fintype P] {d : ℕ}
    (x : P → Fin d → ℝ) : C(SSet.toTop.obj (nerve P), Fin d → ℝ) where
  toFun z j := finiteAffineValue (fun i => x i j) (PosetGeometry.coordinates P z)
  continuous_toFun := by
    classical
    apply continuous_pi
    intro j
    apply continuous_finsetSum
    intro i _
    exact ((StdSimplex.continuous_weights_apply ℝ i).comp
      (PosetGeometry.coordinates P).continuous).mul continuous_const

theorem affineRealization_simplexPoint {P : Type} [PartialOrder P] [Fintype P]
    {d m : ℕ} (x : P → Fin d → ℝ) (s : Fin (m+1) ⥤ P)
    (p : StdSimplex ℝ (Fin (m+1))) :
    affineRealization x (RealizationPrism.simplexPoint (nerve P) s p) =
      affineCoordinates (x ∘ s.obj) p := by
  funext j
  change finiteAffineValue (fun i => x i j)
    (PosetGeometry.coordinates P (RealizationPrism.simplexPoint (nerve P) s p)) = _
  calc
    _ = finiteAffineValue (fun i => x i j) (StdSimplex.map s.obj p) :=
      congrArg (finiteAffineValue (fun i => x i j))
        (PosetGeometry.coordinates_simplexPoint P s p)
    _ = _ := finiteAffineValue_map s.obj (fun i => x i j) p

theorem affineCoordinates_dist {m d : ℕ} (x : Fin (m+1) → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ∀ i j, dist (x i) (x j) ≤ D)
    (p q : StdSimplex ℝ (Fin (m+1))) :
    dist (affineCoordinates x p) (affineCoordinates x q) ≤ D := by
  classical
  apply (dist_pi_le_iff hD).mpr
  intro j
  obtain ⟨a, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => x i j)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (m+1))).Nonempty)
  obtain ⟨b, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => x i j)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (m+1))).Nonempty)
  have hb (i : Fin (m+1)) : x a j ≤ x i j ∧ x i j ≤ x b j :=
    ⟨hmin i (Finset.mem_univ i), hmax i (Finset.mem_univ i)⟩
  have hw : x b j-x a j ≤ D := by
    calc
      _ ≤ |x b j-x a j| := le_abs_self _
      _ = dist (x b j) (x a j) := (Real.dist_eq _ _).symm
      _ ≤ dist (x b) (x a) := dist_le_pi_dist (x b) (x a) j
      _ ≤ D := hx b a
  change |finiteAffineValue (fun i => x i j) p-
    finiteAffineValue (fun i => x i j) q| ≤ D
  have h := supported_common_mass_dist (fun i => x i j) p q 0 0
    (x a j) (x b j) (p.nonneg 0) (q.nonneg 0) (hb 0)
    (fun i _ => hb i) (fun i _ => hb i)
  simp only [sub_zero, one_mul] at h
  exact h.trans hw

theorem affineRealization_simplex_dist {P : Type} [PartialOrder P] [Fintype P]
    {d m : ℕ} (x : P → Fin d → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hx : ChainMesh x D) (s : Fin (m+1) ⥤ P)
    (p q : StdSimplex ℝ (Fin (m+1))) :
    dist (affineRealization x (RealizationPrism.simplexPoint (nerve P) s p))
      (affineRealization x (RealizationPrism.simplexPoint (nerve P) s q)) ≤ D := by
  rw [affineRealization_simplexPoint, affineRealization_simplexPoint]
  apply affineCoordinates_dist _ D hD
  intro i j
  exact hx _ _ ((le_total i j).elim
    (fun h => Or.inl (s.monotone h)) (fun h => Or.inr (s.monotone h)))

theorem iteratedAffineRealization_simplex_dist (P : PartOrd.{0}) [Finite P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D) (r m : ℕ)
    (s : Fin (m+1) ⥤ iteratedChainPoset P r)
    (p q : StdSimplex ℝ (Fin (m+1))) :
    letI := Fintype.ofFinite (iteratedChainPoset P r)
    dist (affineRealization (iteratedAffineVertices P x r)
      (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p))
      (affineRealization (iteratedAffineVertices P x r)
      (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s q)) ≤
      (meshRatio N)^r*D := by
  let := Fintype.ofFinite (iteratedChainPoset P r)
  exact affineRealization_simplex_dist _ _
    (mul_nonneg (pow_nonneg (meshRatio_nonneg N) r) hD)
    (iteratedAffineVertices_mesh P hP x D hD hx r) s p q

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Exact carriers for subcomplexes of poset nerves

Positive vertex coordinates in one point of a subcomplex force every
simplex on those vertices into that same subcomplex. This retains the
specified target for chain-label approximations, including non-full
subcomplexes of poset nerves.
-/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Opposite Convexity RealizationPrism PartialOrder
open scoped Simplicial

noncomputable section

variable {P : Type} [PartialOrder P]

/-- The actual carrier order is exactly inclusion of positive coordinate
supports, even when the ambient poset is infinite. -/
theorem carrier_le_iff_coordinates_support_subset
    (y z : SSet.toTop.obj (nerve P)) :
    carrier (nerve P) y ≤ carrier (nerve P) z ↔
      (coordinates P y).weights.support ⊆ (coordinates P z).weights.support := by
  let s := (normalization (nerve P) y).1
  let t := (normalization (nerve P) z).1
  let p := (normalization (nerve P) y).2
  let q := (normalization (nerve P) z).2
  have hy : simplexPoint (nerve P) s.simplex p = y :=
    denormalize_normalization _ y
  have hz : simplexPoint (nerve P) t.simplex q = z :=
    denormalize_normalization _ z
  have hp : p ∈ fullSupport s.dim := normalization_fullSupport _ y
  have hq : q ∈ fullSupport t.dim := normalization_fullSupport _ z
  have hcy : carrier (nerve P) y = SSet.Subcomplex.ofSimplex s.simplex := by
    rw [← hy]
    exact carrier_interior (nerve P) s.simplex p hp
  have hcz : carrier (nerve P) z = SSet.Subcomplex.ofSimplex t.simplex := by
    rw [← hz]
    exact carrier_interior (nerve P) t.simplex q hq
  have hsy (v : P) : v ∈ (coordinates P y).weights.support ↔
      v ∈ Set.range s.simplex.obj := by
    rw [← hy]
    exact coordinates_support_interior P s.simplex p hp v
  have hsz (v : P) : v ∈ (coordinates P z).weights.support ↔
      v ∈ Set.range t.simplex.obj := by
    rw [← hz]
    exact coordinates_support_interior P t.simplex q hq v
  rw [hcy, hcz, PartialOrder.nerve_ofSimplex_le_ofSimplex_iff]
  constructor
  · intro h v hv
    exact (hsz v).mpr (h ((hsy v).mp hv))
  · intro h v hv
    exact (hsz v).mp (h ((hsy v).mpr hv))

/-- Decreasing positive support cannot leave a specified subcomplex. -/
theorem mem_subcomplex_of_coordinates_support_subset
    (A : (nerve P).Subcomplex) (y z : SSet.toTop.obj (nerve P))
    (hz : z ∈ Set.range (SSet.toTop.map A.ι).hom)
    (hyz : (coordinates P y).weights.support ⊆ (coordinates P z).weights.support) :
    y ∈ Set.range (SSet.toTop.map A.ι).hom := by
  apply (mem_range_inclusion_iff (nerve P) A y).mpr
  exact ((carrier_le_iff_coordinates_support_subset y z).mpr hyz).trans
    ((mem_range_inclusion_iff (nerve P) A z).mp hz)

/-- A simplex whose vertices belong to the positive support of a point
of a subcomplex belongs to that subcomplex. No fullness is required. -/
theorem simplex_mem_of_vertices_positive (A : (nerve P).Subcomplex)
    (z : SSet.toTop.obj (nerve P))
    (hz : z ∈ Set.range (SSet.toTop.map A.ι).hom)
    {n : ℕ} (s : (nerve P).obj (.op (.mk n)))
    (hs : ∀ i, 0 < (coordinates P z).weights (s.obj i)) : s ∈ A.obj _ := by
  let t := (normalization (nerve P) z).1
  let p := (normalization (nerve P) z).2
  have he : simplexPoint (nerve P) t.simplex p = z :=
    denormalize_normalization _ z
  have hp : p ∈ fullSupport t.dim := normalization_fullSupport _ z
  have ht : SSet.Subcomplex.ofSimplex t.simplex ≤ A := by
    rw [← carrier_interior (nerve P) t.simplex p hp, he]
    exact (mem_range_inclusion_iff (nerve P) A z).mp hz
  apply (SSet.Subcomplex.ofSimplex_le_iff s A).mp
  apply le_trans _ ht
  apply (PartialOrder.nerve_ofSimplex_le_ofSimplex_iff s t.simplex).mpr
  rintro _ ⟨i, rfl⟩
  apply (coordinates_support_interior P t.simplex p hp (s.obj i)).mp
  rw [he]
  exact Finsupp.mem_support_iff.mpr (ne_of_gt (hs i))

/-- The same carrier test for all degrees of the nerve. -/
theorem simplex_mem_of_vertices_positive' (A : (nerve P).Subcomplex)
    (z : SSet.toTop.obj (nerve P))
    (hz : z ∈ Set.range (SSet.toTop.map A.ι).hom)
    (d : SimplexCategoryᵒᵖ) (s : (nerve P).obj d)
    (hs : ∀ i, 0 < (coordinates P z).weights (s.obj i)) : s ∈ A.obj d := by
  exact simplex_mem_of_vertices_positive A z hz s hs

end

end Thomason.Construction.PosetGeometry

namespace Thomason.Construction.ChainLabelApproximation

open CategoryTheory PartialOrder

noncomputable section

variable {Q P : Type} [PartialOrder Q] [PartialOrder P]

/-- A point in the target subcomplex carrying the labels of each source
face suffices to factor the whole nerve map through the subcomplex. -/
theorem nerveMapOfLabels_range_le (A : (nerve P).Subcomplex)
    (label : Q → P) (hlabel : MapsChains label)
    (hcarrier : ∀ C : NonemptyFiniteChains Q,
      ∃ z : SSet.toTop.obj (nerve P),
        z ∈ Set.range (SSet.toTop.map A.ι).hom ∧
          ∀ q ∈ C.finset, 0 < (PosetGeometry.coordinates P z).weights (label q)) :
    SSet.Subcomplex.range (nerveMapOfLabels label hlabel) ≤ A := by
  intro d x hx
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨z, hz, hc⟩ := hcarrier (s.obj (Fin.last d.unop.len))
  apply PosetGeometry.simplex_mem_of_vertices_positive' A z hz
  intro i
  obtain ⟨q, hq, he⟩ := nerveMapOfLabels_carrier label hlabel d s i
  rw [← he]
  exact hc q hq

/-- The label map with its actual prescribed subcomplex as codomain. -/
def nerveMapOfLabelsToSubcomplex (A : (nerve P).Subcomplex)
    (label : Q → P) (hlabel : MapsChains label)
    (hcarrier : ∀ C : NonemptyFiniteChains Q,
      ∃ z : SSet.toTop.obj (nerve P),
        z ∈ Set.range (SSet.toTop.map A.ι).hom ∧
          ∀ q ∈ C.finset, 0 < (PosetGeometry.coordinates P z).weights (label q)) :
    nerve (NonemptyFiniteChains Q) ⟶ A :=
  SSet.Subcomplex.lift (nerveMapOfLabels label hlabel)
    (nerveMapOfLabels_range_le A label hlabel hcarrier)

@[reassoc (attr := simp)]
theorem nerveMapOfLabelsToSubcomplex_ι (A : (nerve P).Subcomplex)
    (label : Q → P) (hlabel : MapsChains label)
    (hcarrier : ∀ C : NonemptyFiniteChains Q,
      ∃ z : SSet.toTop.obj (nerve P),
        z ∈ Set.range (SSet.toTop.map A.ι).hom ∧
          ∀ q ∈ C.finset, 0 < (PosetGeometry.coordinates P z).weights (label q)) :
    nerveMapOfLabelsToSubcomplex A label hlabel hcarrier ≫ A.ι =
      nerveMapOfLabels label hlabel := rfl

end

end Thomason.Construction.ChainLabelApproximation

end

section

/-! # Coordinate interpolation inside a prescribed target subcomplex

When the second endpoint has smaller positive support, the whole
interpolation remains in the first endpoint's actual carrier. The
resulting homotopy therefore lifts to any prescribed subcomplex.
-/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory Convexity RealizationPrism Topology

noncomputable section

theorem blend_support_subset {P : Type} (p q : StdSimplex ℝ P)
    (hq : q.weights.support ⊆ p.weights.support) (t : unitInterval) :
    (blend p q t).weights.support ⊆ p.weights.support := by
  intro v hv
  by_contra hp
  have hp0 : p.weights v = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hp
  have hq0 : q.weights v = 0 := by
    by_contra hn
    exact hp (hq (Finsupp.mem_support_iff.mpr hn))
  have hh : (blend p q t).weights v = 0 := by
    simp [blend, hp0, hq0]
  exact (Finsupp.mem_support_iff.mp hv) hh

theorem interpolate_mem_subcomplex {P : Type} [PartialOrder P] [Finite P]
    (A : (nerve P).Subcomplex) (x y : SSet.toTop.obj (nerve P))
    (h : CompatibleSupport (coordinates P x) (coordinates P y))
    (hx : x ∈ Set.range (SSet.toTop.map A.ι).hom)
    (hy : (coordinates P y).weights.support ⊆ (coordinates P x).weights.support)
    (t : unitInterval) :
    interpolate x y h t ∈ Set.range (SSet.toTop.map A.ι).hom := by
  apply mem_subcomplex_of_coordinates_support_subset A _ x hx
  rw [coordinates_interpolate]
  exact blend_support_subset _ _ hy t

def liftSubcomplexHomotopy {P X : Type} [PartialOrder P] [TopologicalSpace X]
    (A : (nerve P).Subcomplex)
    {f g : C(X, SSet.toTop.obj A.toSSet)}
    (H : ((SSet.toTop.map A.ι).hom.comp f).Homotopy ((SSet.toTop.map A.ι).hom.comp g))
    (hH : ∀ t x, H (t,x) ∈ Set.range (SSet.toTop.map A.ι).hom) : f.Homotopy g := by
  let e := (inclusion_isClosedEmbedding (nerve P) A).isEmbedding.toHomeomorph
  exact {
    toFun tx := e.symm ⟨H tx, hH tx.1 tx.2⟩
    continuous_toFun := e.symm.continuous.comp (H.continuous.subtype_mk _)
    map_zero_left x := by
      apply (inclusion_isClosedEmbedding (nerve P) A).injective
      exact (congrArg Subtype.val (e.apply_symm_apply ⟨H (0,x), hH 0 x⟩)).trans
        (H.map_zero_left x)
    map_one_left x := by
      apply (inclusion_isClosedEmbedding (nerve P) A).injective
      exact (congrArg Subtype.val (e.apply_symm_apply ⟨H (1,x), hH 1 x⟩)).trans
        (H.map_one_left x) }

def subcomplexHomotopyOfSupportSubset {P X : Type} [PartialOrder P] [Finite P]
    [TopologicalSpace X] (A : (nerve P).Subcomplex)
    (f g : C(X, SSet.toTop.obj A.toSSet))
    (h : ∀ x, (coordinates P ((SSet.toTop.map A.ι).hom (g x))).weights.support ⊆
      (coordinates P ((SSet.toTop.map A.ι).hom (f x))).weights.support) : f.Homotopy g := by
  let F := (SSet.toTop.map A.ι).hom.comp f
  let G := (SSet.toTop.map A.ι).hom.comp g
  have hc x : CompatibleSupport (coordinates P (F x)) (coordinates P (G x)) :=
    compatibleSupport_of_subset _ _ (coordinates_chainSupported (F x)) (h x)
  exact liftSubcomplexHomotopy A (commonChainHomotopy F G hc) (fun t x =>
    interpolate_mem_subcomplex A (F x) (G x) (hc x) ⟨f x, rfl⟩ (h x) t)

end

end Thomason.Construction.PosetGeometry

end

end OAI
