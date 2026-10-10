import OAI.CategoryTheory.Thomason.Chains.FiniteChainMesh
import OAI.CategoryTheory.Thomason.Chains.NerveFaceChains
import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.LastVertexWeakEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.PosetSubcomplexHomotopy
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OAI

section

/-! # Realization compatibility for the iterated affine mesh

The recursively averaged vertex coordinates are exactly the coordinates
of the corresponding continuous maps into the ORIGINAL finite-poset
realization. This is the geometric bridge needed by finite approximation.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder

noncomputable section

def iteratedChainRealization (P : PartOrd.{0}) [Finite P] : (r : ℕ) →
    C(SSet.toTop.obj (nerve (iteratedChainPoset P r)), SSet.toTop.obj (nerve P))
  | 0 => ContinuousMap.id _
  | r+1 => by
      letI := Fintype.ofFinite (iteratedChainPoset P r)
      exact (iteratedChainRealization P r).comp (chainRealizationMap (iteratedChainPoset P r))

theorem affineRealization_iteratedChainRealization (P : PartOrd.{0}) [Fintype P]
    {d : ℕ} (x : P → Fin d → ℝ) (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset P r))) :
    letI := Fintype.ofFinite (iteratedChainPoset P r)
    affineRealization x (iteratedChainRealization P r z) =
      affineRealization (iteratedAffineVertices P x r) z := by
  induction r with
  | zero =>
      change @affineRealization P P.str _ d x z =
        @affineRealization P P.str (Fintype.ofFinite P) d x z
      exact congrArg (fun h : Fintype P => @affineRealization P P.str h d x z)
        (Subsingleton.elim _ _)
  | succ r ih =>
      let := Fintype.ofFinite (iteratedChainPoset P r)
      let := Fintype.ofFinite (iteratedChainPoset P (r+1))
      let : Finite (NonemptyFiniteChains (iteratedChainPoset P r)) :=
        finite_nonemptyFiniteChains _
      let := Fintype.ofFinite (NonemptyFiniteChains (iteratedChainPoset P r))
      change affineRealization x (iteratedChainRealization P r
        (chainRealizationMap (iteratedChainPoset P r) z)) = _
      calc
        _ = affineRealization (iteratedAffineVertices P x r)
            (chainRealizationMap (iteratedChainPoset P r) z) := ih _
        _ = affineRealization (chainAverage (iteratedAffineVertices P x r)) z :=
          affineRealization_chainRealizationMap (iteratedChainPoset P r) _ z
        _ = _ := congrArg (fun h : Fintype (NonemptyFiniteChains (iteratedChainPoset P r)) =>
          @affineRealization _ _ h d (chainAverage (iteratedAffineVertices P x r)) z)
            (Subsingleton.elim _ _)

/-- Complete closed simplices of every stage have the asserted shrinking
diameter after mapping into the original realization. -/
theorem iteratedChainRealization_simplex_dist (P : PartOrd.{0}) [Fintype P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D) (r m : ℕ)
    (s : Fin (m+1) ⥤ iteratedChainPoset P r)
    (p q : Convexity.StdSimplex ℝ (Fin (m+1))) :
    dist (affineRealization x (iteratedChainRealization P r
        (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p)))
      (affineRealization x (iteratedChainRealization P r
        (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s q))) ≤
      (meshRatio N)^r*D := by
  rw [affineRealization_iteratedChainRealization, affineRealization_iteratedChainRealization]
  exact iteratedAffineRealization_simplex_dist P hP x D hD hx r m s p q

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Uniform cover refinement by genuine barycentric parameter maps

Compactness and the mesh estimate put every complete closed
characteristic simplex of one subdivision stage in a member of a given
open cover of the original geometric image.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Filter Convexity

noncomputable section

theorem exists_iteratedChainRealization_cover (P : PartOrd.{0}) [Fintype P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D)
    {ι : Type*} (U : ι → Set (Fin d → ℝ)) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range (affineRealization x) ⊆ ⋃ i, U i) :
    ∃ r : ℕ, ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset P r),
      ∃ i : ι, ∀ p : StdSimplex ℝ (Fin (m+1)),
        affineRealization x (iteratedChainRealization P r
          (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p)) ∈ U i := by
  let := PosetGeometry.nerve_finite P
  let := RealizationPrism.compactSpace_of_finite (nerve P)
  have hc : IsCompact (Set.range (affineRealization x)) :=
    isCompact_range (affineRealization x).continuous
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hc hU hcover
  obtain ⟨r, hr⟩ := (Tendsto.eventually_lt_const hδ
    (iteratedAffineVertices_mesh_tendsto_zero N D)).exists
  refine ⟨r, fun m s => ?_⟩
  let z := RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s
    (StdSimplex.single (0 : Fin (m+1)))
  obtain ⟨i, hi⟩ := hball (affineRealization x (iteratedChainRealization P r z))
    ⟨iteratedChainRealization P r z, rfl⟩
  refine ⟨i, fun p => hi ?_⟩
  apply Metric.mem_ball.mpr
  exact (iteratedChainRealization_simplex_dist P hP x D hD hx r m s p
    (StdSimplex.single (0 : Fin (m+1)))).trans_lt hr

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Barycentric refinement for intrinsic open covers

The canonical finite coordinate embedding transfers the geometric mesh
estimate to every open cover of the actual finite-poset realization.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity Topology

noncomputable section

def standardVertexPositions (P : Type) [Fintype P] (i : P)
    (j : Fin (Fintype.card P)) : ℝ := if Fintype.equivFin P i = j then 1 else 0

theorem finiteAffineValue_standardVertexPositions (P : Type) [Fintype P]
    (p : StdSimplex ℝ P) (j : Fin (Fintype.card P)) :
    finiteAffineValue (fun i => standardVertexPositions P i j) p =
      p.weights ((Fintype.equivFin P).symm j) := by
  classical
  simp [finiteAffineValue, standardVertexPositions,
    ← (Fintype.equivFin P).eq_symm_apply]

theorem standardVertexPositions_mesh (P : Type) [PartialOrder P] [Fintype P] :
    ChainMesh (standardVertexPositions P) 1 := by
  intro i j _
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro k
  rw [Real.dist_eq]
  unfold standardVertexPositions
  split_ifs <;> norm_num

theorem standardVertexPositions_isClosedEmbedding (P : Type) [PartialOrder P] [Fintype P] :
    IsClosedEmbedding (affineRealization (standardVertexPositions P)) := by
  let := PosetGeometry.nerve_finite P
  let := RealizationPrism.compactSpace_of_finite (nerve P)
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (affineRealization (standardVertexPositions P)).continuous ?_
    (affineRealization (standardVertexPositions P)).continuous.isClosedMap
  intro z w h
  apply PosetGeometry.coordinates_injective P
  apply StdSimplex.ext
  ext i
  have he := congrFun h (Fintype.equivFin P i)
  change finiteAffineValue (fun k => standardVertexPositions P k (Fintype.equivFin P i))
    (PosetGeometry.coordinates P z) =
    finiteAffineValue (fun k => standardVertexPositions P k (Fintype.equivFin P i))
      (PosetGeometry.coordinates P w) at he
  simpa only [finiteAffineValue_standardVertexPositions, Equiv.symm_apply_apply] using he

/-- One stage refines the open cover on every whole closed simplex, in
the actual original realization topology. -/
theorem exists_iteratedChainRealization_intrinsic_cover (P : PartOrd.{0}) [Fintype P]
    {ι : Type*} (U : ι → Set (SSet.toTop.obj (nerve P)))
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
    ∃ r : ℕ, ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset P r),
      ∃ i : ι, ∀ p : StdSimplex ℝ (Fin (m+1)),
        iteratedChainRealization P r
          (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p) ∈ U i := by
  classical
  let c := affineRealization (standardVertexPositions P)
  have he := (standardVertexPositions_isClosedEmbedding P).isEmbedding.isInducing
  choose V hV hpre using fun i => he.isOpen_iff.mp (hU i)
  have hVcover : Set.range c ⊆ ⋃ i, V i := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ ⋃ i, U i := hcover.symm ▸ Set.mem_univ z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change z ∈ c ⁻¹' V i
    rw [hpre i]
    exact hi
  have hP : ChainCardBound P (Fintype.card P) := fun C =>
    (Finset.card_le_univ C.finset).trans (Nat.le_succ _)
  obtain ⟨r, hr⟩ := exists_iteratedChainRealization_cover P hP
    (standardVertexPositions P) 1 (by norm_num) (standardVertexPositions_mesh P) V hV hVcover
  refine ⟨r, fun m s => ?_⟩
  obtain ⟨i, hi⟩ := hr m s
  refine ⟨i, fun p => ?_⟩
  have hp := hi p
  change iteratedChainRealization P r
    (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p) ∈ c ⁻¹' V i at hp
  rwa [hpre i] at hp

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Uniform refinement of complete vertex stars

One label is chosen for each vertex of a subdivision stage, and works
simultaneously on every closed simplex through that vertex. This is the
compatibility needed to turn geometric refinement into simplicial data.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity Filter Topology

noncomputable section

def posetVertexPoint {P : Type} [PartialOrder P] (v : P) : SSet.toTop.obj (nerve P) :=
  RealizationPrism.simplexPoint (nerve P) (PosetGeometry.vertex v) (StdSimplex.single 0)

theorem simplexPoint_single {P : Type} [PartialOrder P] {m : ℕ}
    (s : Fin (m+1) ⥤ P) (k : Fin (m+1)) :
    RealizationPrism.simplexPoint (nerve P) s (StdSimplex.single k) =
      posetVertexPoint (s.obj k) := by
  apply PosetGeometry.coordinates_injective P
  calc
    _ = StdSimplex.map s.obj (StdSimplex.single k) :=
      PosetGeometry.coordinates_simplexPoint P s _
    _ = StdSimplex.single (s.obj k) := StdSimplex.map_single _ _
    _ = _ := by
      unfold posetVertexPoint
      rw [PosetGeometry.coordinates_simplexPoint, StdSimplex.map_single]
      rfl

theorem exists_iteratedChainRealization_star_cover (P : PartOrd.{0}) [Fintype P]
    {N d : ℕ} (hP : ChainCardBound P N) (x : P → Fin d → ℝ)
    (D : ℝ) (hD : 0 ≤ D) (hx : ChainMesh x D)
    {ι : Type*} (U : ι → Set (Fin d → ℝ)) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range (affineRealization x) ⊆ ⋃ i, U i) :
    ∃ (r : ℕ) (label : iteratedChainPoset P r → ι),
      ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset P r)
        (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
        affineRealization x (iteratedChainRealization P r
          (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p)) ∈
            U (label (s.obj k)) := by
  classical
  let := PosetGeometry.nerve_finite P
  let := RealizationPrism.compactSpace_of_finite (nerve P)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_range (affineRealization x).continuous) hU hcover
  obtain ⟨r, hr⟩ := (Tendsto.eventually_lt_const hδ
    (iteratedAffineVertices_mesh_tendsto_zero N D)).exists
  let center (v : iteratedChainPoset P r) :=
    affineRealization x (iteratedChainRealization P r (posetVertexPoint v))
  have hc (v : iteratedChainPoset P r) : center v ∈ Set.range (affineRealization x) :=
    ⟨iteratedChainRealization P r (posetVertexPoint v), rfl⟩
  choose label hlabel using fun v => hball (center v) (hc v)
  refine ⟨r, label, fun m s p k => hlabel (s.obj k) ?_⟩
  apply Metric.mem_ball.mpr
  have h := iteratedChainRealization_simplex_dist P hP x D hD hx r m s p
    (StdSimplex.single k)
  have he := simplexPoint_single s k
  apply lt_of_le_of_lt ?_ hr
  dsimp only [center]
  simpa only [he] using h

theorem exists_iteratedChainRealization_intrinsic_star_cover (P : PartOrd.{0}) [Fintype P]
    {ι : Type*} (U : ι → Set (SSet.toTop.obj (nerve P)))
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
    ∃ (r : ℕ) (label : iteratedChainPoset P r → ι),
      ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset P r)
        (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
        iteratedChainRealization P r
          (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p) ∈
            U (label (s.obj k)) := by
  classical
  let c := affineRealization (standardVertexPositions P)
  have he := (standardVertexPositions_isClosedEmbedding P).isEmbedding.isInducing
  choose V hV hpre using fun i => he.isOpen_iff.mp (hU i)
  have hVcover : Set.range c ⊆ ⋃ i, V i := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ ⋃ i, U i := hcover.symm ▸ Set.mem_univ z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change z ∈ c ⁻¹' V i
    rw [hpre i]
    exact hi
  have hP : ChainCardBound P (Fintype.card P) := fun C =>
    (Finset.card_le_univ C.finset).trans (Nat.le_succ _)
  obtain ⟨r, label, hl⟩ := exists_iteratedChainRealization_star_cover P hP
    (standardVertexPositions P) 1 (by norm_num) (standardVertexPositions_mesh P) V hV hVcover
  refine ⟨r, label, fun m s p k => ?_⟩
  have hp := hl m s p k
  change iteratedChainRealization P r
    (RealizationPrism.simplexPoint (nerve (iteratedChainPoset P r)) s p) ∈
      c ⁻¹' V (label (s.obj k)) at hp
  rwa [hpre (label (s.obj k))] at hp

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Weak equivalences for the actual shrinking parameter maps

The maps used by the mesh and cover-refinement theorems preserve the
actual weak homotopy type at every stage, by comparison with last vertex.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder

noncomputable section

theorem iteratedChainRealization_weak (P : PartOrd.{0}) [Finite P] (r : ℕ) :
    IsWeakHomotopyEquivalence (iteratedChainRealization P r) := by
  induction r with
  | zero =>
      change IsWeakHomotopyEquivalence (ContinuousMap.id (SSet.toTop.obj (nerve P)))
      exact IsWeakHomotopyEquivalence.id
  | succ r ih =>
      let := Fintype.ofFinite (iteratedChainPoset P r)
      change IsWeakHomotopyEquivalence ((iteratedChainRealization P r).comp
        (chainRealizationMap (iteratedChainPoset P r)))
      exact (chainRealizationMap_weak (iteratedChainPoset P r)).comp ih

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Actual approximation labels for maps of finite-poset realizations

Uniform closed-star refinement produces labels that carry chains to
chains, hence an actual simplicial approximation after one further
subdivision. The target is the original nerve throughout.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity

noncomputable section

def edgeOrderHom {P : Type} [PartialOrder P] (a b : P) (hab : a ≤ b) : Fin 2 →o P where
  toFun i := if i = 0 then a else b
  monotone' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem exists_poset_approximation_labels (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P))) :
    ∃ (r : ℕ) (label : iteratedChainPoset Q r → P),
      ChainLabelApproximation.MapsChains label ∧
      ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset Q r)
        (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
        0 < (PosetGeometry.coordinates P (f (iteratedChainRealization Q r
          (RealizationPrism.simplexPoint (nerve (iteratedChainPoset Q r)) s p)))).weights
            (label (s.obj k)) := by
  classical
  let U (v : P) : Set (SSet.toTop.obj (nerve Q)) :=
    {z | 0 < (PosetGeometry.coordinates P (f z)).weights v}
  have hU (v : P) : IsOpen (U v) :=
    isOpen_lt continuous_const
      ((StdSimplex.continuous_weights_apply ℝ v).comp
        ((PosetGeometry.coordinates P).continuous.comp f.continuous))
  have hcover : ⋃ v, U v = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨v, hv⟩ := PosetGeometry.probability_support_nonempty
      (PosetGeometry.coordinates P (f z))
    exact Set.mem_iUnion.mpr ⟨v, lt_of_le_of_ne
      ((PosetGeometry.coordinates P (f z)).nonneg v)
      (Finsupp.mem_support_iff.mp hv).symm⟩
  obtain ⟨r, label, hl⟩ := exists_iteratedChainRealization_intrinsic_star_cover Q U hU hcover
  refine ⟨r, label, ?_, hl⟩
  intro a b hab
  let s : Fin 2 ⥤ iteratedChainPoset Q r := (edgeOrderHom a b hab).monotone.functor
  let z := f (iteratedChainRealization Q r
    (RealizationPrism.simplexPoint (nerve (iteratedChainPoset Q r)) s (StdSimplex.single 0)))
  have ha : 0 < (PosetGeometry.coordinates P z).weights (label a) :=
    hl 1 s (StdSimplex.single 0) 0
  have hb : 0 < (PosetGeometry.coordinates P z).weights (label b) :=
    hl 1 s (StdSimplex.single 0) 1
  exact PosetGeometry.coordinates_chainSupported z _
    (Finsupp.mem_support_iff.mpr (ne_of_gt ha)) _
    (Finsupp.mem_support_iff.mpr (ne_of_gt hb))

/-- The chosen labels already give an actual map from a finite
subdivision into the original simplicial target. -/
theorem exists_poset_approximation_map (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P))) :
    ∃ (r : ℕ) (label : iteratedChainPoset Q r → P)
      (hlabel : ChainLabelApproximation.MapsChains label),
      ∃ g : SSet.sd.obj (nerve (iteratedChainPoset Q r)) ⟶ nerve P,
        g = ChainLabelApproximation.subdivisionMapOfLabels label hlabel ∧
        ∀ (m : ℕ) (s : Fin (m+1) ⥤ iteratedChainPoset Q r)
          (p : StdSimplex ℝ (Fin (m+1))) (k : Fin (m+1)),
          0 < (PosetGeometry.coordinates P (f (iteratedChainRealization Q r
            (RealizationPrism.simplexPoint (nerve (iteratedChainPoset Q r)) s p)))).weights
              (label (s.obj k)) := by
  obtain ⟨r, label, hlabel, hl⟩ := exists_poset_approximation_labels Q P f
  exact ⟨r, label, hlabel, _, rfl, hl⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # A genuine simplicial approximation homotopy for poset targets

The positive-coordinate star condition puts every vertex of the
approximating simplex in the support of the original point. Straight
interpolation stays inside one chain of the original target.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity

noncomputable section

theorem labelApproximation_support {Q P : Type} [PartialOrder Q] [Fintype Q]
    [PartialOrder P] (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P)))
    (label : Q → P) (hlabel : ChainLabelApproximation.MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ Q) (p : StdSimplex ℝ (Fin (m+1)))
      (k : Fin (m+1)), 0 < (PosetGeometry.coordinates P
        (f (RealizationPrism.simplexPoint (nerve Q) s p))).weights (label (s.obj k)))
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains Q))) :
    (PosetGeometry.coordinates P
      ((SSet.toTop.map (ChainLabelApproximation.nerveMapOfLabels label hlabel)).hom z)).weights.support ⊆
        (PosetGeometry.coordinates P (f (chainRealizationMap Q z))).weights.support := by
  classical
  obtain ⟨m, s, p, rfl⟩ := RealizationPrism.point_representation_simplex
    (nerve (NonemptyFiniteChains Q)) z
  obtain ⟨q, hq⟩ := chainRealizationMap_simplex_representation s p
  let g := ChainLabelApproximation.nerveMapOfLabels label hlabel
  have he : PosetGeometry.coordinates P
      ((SSet.toTop.map g).hom
        (RealizationPrism.simplexPoint (nerve (NonemptyFiniteChains Q)) s p)) =
      StdSimplex.map (g.app _ s).obj p := by
    calc
      _ = PosetGeometry.coordinates P
          (RealizationPrism.simplexPoint (nerve P) (g.app _ s) p) :=
        congrArg (PosetGeometry.coordinates P) (RealizationPrism.simplexPoint_naturality g s p)
      _ = _ := PosetGeometry.coordinates_simplexPoint P _ p
  intro y hy
  change y ∈ (PosetGeometry.coordinates P
    ((SSet.toTop.map g).hom
      (RealizationPrism.simplexPoint (nerve (NonemptyFiniteChains Q)) s p))).weights.support at hy
  rw [he] at hy
  change y ∈ (p.weights.mapDomain (g.app _ s).obj).support at hy
  rw [Finsupp.support_mapDomain_of_nonneg p.nonneg] at hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨v, hv, heq⟩ := ChainLabelApproximation.nerveMapOfLabels_carrier label hlabel _ s i
  have hr : v ∈ Set.range (finiteChainSimplex (s.obj (Fin.last m))).obj := by
    rw [finiteChainSimplex_range]
    exact hv
  obtain ⟨k, hk⟩ := hr
  have hp := hl _ (finiteChainSimplex (s.obj (Fin.last m))) q k
  rw [hk] at hp
  apply Finsupp.mem_support_iff.mpr
  rw [← heq]
  have hf := congrArg f hq
  rw [hf]
  exact ne_of_gt hp

def labelApproximationHomotopy {Q P : Type} [PartialOrder Q] [Fintype Q]
    [PartialOrder P] [Finite P]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P)))
    (label : Q → P) (hlabel : ChainLabelApproximation.MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ Q) (p : StdSimplex ℝ (Fin (m+1)))
      (k : Fin (m+1)), 0 < (PosetGeometry.coordinates P
        (f (RealizationPrism.simplexPoint (nerve Q) s p))).weights (label (s.obj k))) :
    (f.comp (chainRealizationMap Q)).Homotopy
      (SSet.toTop.map (ChainLabelApproximation.nerveMapOfLabels label hlabel)).hom :=
  PosetGeometry.commonChainHomotopy _ _ (fun z =>
    PosetGeometry.compatibleSupport_of_subset _ _
      (PosetGeometry.coordinates_chainSupported _)
      (labelApproximation_support f label hlabel hl z))

theorem labelApproximation_weak_iff {Q P : Type} [PartialOrder Q] [Fintype Q]
    [PartialOrder P] [Finite P]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P)))
    (label : Q → P) (hlabel : ChainLabelApproximation.MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ Q) (p : StdSimplex ℝ (Fin (m+1)))
      (k : Fin (m+1)), 0 < (PosetGeometry.coordinates P
        (f (RealizationPrism.simplexPoint (nerve Q) s p))).weights (label (s.obj k))) :
    IsWeakHomotopyEquivalence f ↔
      realizationWeakEquivalences (ChainLabelApproximation.nerveMapOfLabels label hlabel) := by
  have he := isWeakHomotopyEquivalence_homotopy_iff
    (labelApproximationHomotopy f label hlabel hl)
  constructor
  · intro hf
    exact he.mp ((chainRealizationMap_weak Q).comp hf)
  · intro hg
    exact IsWeakHomotopyEquivalence.of_precomp (chainRealizationMap_weak Q) (he.mpr hg)

theorem exists_poset_simplicial_approximation (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P] [Finite P]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P))) :
    ∃ (r : ℕ) (g : nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) ⟶ nerve P),
      letI := Fintype.ofFinite (iteratedChainPoset Q r)
      Nonempty (((f.comp (iteratedChainRealization Q r)).comp
        (chainRealizationMap (iteratedChainPoset Q r))).Homotopy (SSet.toTop.map g).hom) := by
  obtain ⟨r, label, hlabel, hl⟩ := exists_poset_approximation_labels Q P f
  let := Fintype.ofFinite (iteratedChainPoset Q r)
  exact ⟨r, ChainLabelApproximation.nerveMapOfLabels label hlabel,
    ⟨labelApproximationHomotopy (f.comp (iteratedChainRealization Q r)) label hlabel hl⟩⟩

/-- The approximation retains the original actual weak-equivalence
test, with no Kan--Quillen or simplicial-approximation assumption. -/
theorem exists_poset_weak_simplicial_approximation (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P] [Finite P]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P))) :
    ∃ (r : ℕ) (g : nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) ⟶ nerve P),
      (IsWeakHomotopyEquivalence f ↔ realizationWeakEquivalences g) ∧
      letI := Fintype.ofFinite (iteratedChainPoset Q r)
      Nonempty (((f.comp (iteratedChainRealization Q r)).comp
        (chainRealizationMap (iteratedChainPoset Q r))).Homotopy (SSet.toTop.map g).hom) := by
  obtain ⟨r, label, hlabel, hl⟩ := exists_poset_approximation_labels Q P f
  let := Fintype.ofFinite (iteratedChainPoset Q r)
  refine ⟨r, ChainLabelApproximation.nerveMapOfLabels label hlabel, ?_,
    ⟨labelApproximationHomotopy (f.comp (iteratedChainRealization Q r)) label hlabel hl⟩⟩
  have he : IsWeakHomotopyEquivalence f ↔
      IsWeakHomotopyEquivalence (f.comp (iteratedChainRealization Q r)) :=
    ⟨fun hf => (iteratedChainRealization_weak Q r).comp hf,
      IsWeakHomotopyEquivalence.of_precomp (iteratedChainRealization_weak Q r)⟩
  exact he.trans (labelApproximation_weak_iff (f.comp (iteratedChainRealization Q r))
    label hlabel hl)

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Continuous approximation into finite nonsingular targets

The actual weak face-poset comparison has a continuous homotopy inverse
by the proved realization Whitehead theorem. Approximation in its finite
poset nerve and composition with the original comparison then produce
simplicial maps into the original nonsingular target.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder

noncomputable section

/-- Approximation into the original finite nonsingular target, together
with its actual continuous comparison homotopy and weak-equivalence test. -/
theorem exists_nonsingular_weak_simplicial_approximation
    (Q : PartOrd.{0}) [Fintype Q] (K : SSet.{0}) [K.Nonsingular] [K.Finite]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj K)) :
    ∃ (r : ℕ) (g : nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) ⟶ K),
      (IsWeakHomotopyEquivalence f ↔ realizationWeakEquivalences g) ∧
      letI := Fintype.ofFinite (iteratedChainPoset Q r)
      Nonempty (((f.comp (iteratedChainRealization Q r)).comp
        (chainRealizationMap (iteratedChainPoset Q r))).Homotopy (SSet.toTop.map g).hom) := by
  let k := NonsingularLastVertex.map K
  have hk : realizationWeakEquivalences k := NonsingularLastVertex.map_weak K
  let e := realizationWhiteheadEquiv (SSet.toTop.map k) hk
  let f' : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve K.N)) := e.invFun.comp f
  obtain ⟨r, g₀, hg₀, hH⟩ := exists_poset_weak_simplicial_approximation Q K.N f'
  let := Fintype.ofFinite (iteratedChainPoset Q r)
  obtain ⟨H⟩ := hH
  let p := (iteratedChainRealization Q r).comp
    (chainRealizationMap (iteratedChainPoset Q r))
  refine ⟨r, g₀ ≫ k, ?_, ?_⟩
  · have hi : IsWeakHomotopyEquivalence e.invFun :=
      homotopyEquiv_isWeakHomotopyEquivalence e.symm
    constructor
    · intro hf
      exact realizationWeakEquivalences.comp_mem _ _ (hg₀.mp (hf.comp hi)) hk
    · intro hg
      have hg₀' := realizationWeakEquivalences.of_postcomp g₀ k hk hg
      exact IsWeakHomotopyEquivalence.of_postcomp hi (hg₀.mpr hg₀')
  · have H₀ : (f.comp p).Homotopy (e.toFun.comp (f'.comp p)) := by
      exact ((Classical.choice e.right_inv).symm.comp
        (ContinuousMap.Homotopy.refl (f.comp p))).cast (by ext; rfl) (by ext; rfl)
    have he : (SSet.toTop.map (g₀ ≫ k)).hom =
        e.toFun.comp (SSet.toTop.map g₀).hom := by
      change (SSet.toTop.map (g₀ ≫ k)).hom =
        (SSet.toTop.map k).hom.comp (SSet.toTop.map g₀).hom
      rw [Functor.map_comp]
      rfl
    have H₁ : (e.toFun.comp (f'.comp p)).Homotopy (SSet.toTop.map (g₀ ≫ k)).hom := by
      exact ((ContinuousMap.Homotopy.refl e.toFun).comp H).cast (by ext; rfl) he.symm
    exact ⟨H₀.trans H₁⟩

/-- The same existence statement on the actual iterated subdivision,
with the original target and the original continuous weak-equivalence test. -/
theorem exists_nonsingular_iterated_weak_approximation
    (Q : PartOrd.{0}) [Fintype Q] (K : SSet.{0}) [K.Nonsingular] [K.Finite]
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj K)) :
    ∃ (r : ℕ) (g : (iteratedSubdivision r).obj (nerve Q) ⟶ K),
      IsWeakHomotopyEquivalence f ↔ realizationWeakEquivalences g := by
  obtain ⟨r, g, hg, _⟩ := exists_nonsingular_weak_simplicial_approximation Q K f
  let e : (iteratedSubdivision (r+1)).obj (nerve Q) ≅
      nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) :=
    iteratedSubdivisionNerveIso Q (r+1)
  exact ⟨r+1, e.hom ≫ g,
    hg.trans (realizationWeakEquivalences.cancel_left_of_respectsIso e.hom g).symm⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Chain-label approximations retain a prescribed target subcomplex

The open-cover labels for a continuous map into an arbitrary subcomplex
of a poset nerve give a simplicial map into that subcomplex itself. The
construction allows non-full targets and does not require a finite
ambient target poset.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity

noncomputable section

/-- Approximate labels for a map into a subcomplex already have carriers
in that exact subcomplex. -/
theorem exists_subcomplex_approximation_map (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P] (A : (nerve P).Subcomplex)
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj A.toSSet)) :
    ∃ (r : ℕ) (label : iteratedChainPoset Q r → P)
      (hlabel : ChainLabelApproximation.MapsChains label),
      ∃ g : SSet.sd.obj (nerve (iteratedChainPoset Q r)) ⟶ A.toSSet,
        g ≫ A.ι = ChainLabelApproximation.subdivisionMapOfLabels label hlabel := by
  let F : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj (nerve P)) :=
    (SSet.toTop.map A.ι).hom.comp f
  obtain ⟨r, label, hlabel, hl⟩ := exists_poset_approximation_labels Q P F
  have hc : ∀ C : NonemptyFiniteChains (iteratedChainPoset Q r),
      ∃ z : SSet.toTop.obj (nerve P),
        z ∈ Set.range (SSet.toTop.map A.ι).hom ∧
          ∀ q ∈ C.finset, 0 < (PosetGeometry.coordinates P z).weights (label q) := by
    intro C
    let s := finiteChainSimplex C
    let p : StdSimplex ℝ (Fin ((ChainOrdinal.choose C).dim+1)) := StdSimplex.single 0
    let x := iteratedChainRealization Q r
      (RealizationPrism.simplexPoint (nerve (iteratedChainPoset Q r)) s p)
    refine ⟨F x, ⟨f x, rfl⟩, ?_⟩
    intro q hq
    obtain ⟨i, hi⟩ := (ChainOrdinal.choose C).enum.surjective ⟨q, hq⟩
    have hh := hl (ChainOrdinal.choose C).dim s p i
    change 0 < (PosetGeometry.coordinates P (F x)).weights
      (label (((ChainOrdinal.choose C).enum i).val)) at hh
    simpa only [hi] using hh
  refine ⟨r, label, hlabel,
    NerveSubdivisionMap.map (iteratedChainPoset Q r) ≫
      ChainLabelApproximation.nerveMapOfLabelsToSubcomplex A label hlabel hc, ?_⟩
  rw [Category.assoc, ChainLabelApproximation.nerveMapOfLabelsToSubcomplex_ι]
  rfl

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Approximation homotopies remain in the exact target subcomplex

The construction applies to arbitrary subcomplexes of finite poset
nerves, without a fullness assumption. Both the approximating simplicial
map and the comparison homotopy retain that target.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder Convexity

noncomputable section

theorem exists_label_subcomplex_homotopy {Q P : Type} [PartialOrder Q] [Fintype Q]
    [PartialOrder P] [Finite P] (A : (nerve P).Subcomplex)
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj A.toSSet))
    (label : Q → P) (hlabel : ChainLabelApproximation.MapsChains label)
    (hl : ∀ (m : ℕ) (s : Fin (m+1) ⥤ Q) (p : StdSimplex ℝ (Fin (m+1)))
      (k : Fin (m+1)), 0 < (PosetGeometry.coordinates P
        ((SSet.toTop.map A.ι).hom (f (RealizationPrism.simplexPoint (nerve Q) s p)))).weights
          (label (s.obj k))) :
    ∃ g : nerve (NonemptyFiniteChains Q) ⟶ A.toSSet,
      g ≫ A.ι = ChainLabelApproximation.nerveMapOfLabels label hlabel ∧
      Nonempty ((f.comp (chainRealizationMap Q)).Homotopy (SSet.toTop.map g).hom) := by
  let F := (SSet.toTop.map A.ι).hom.comp f
  have hc (C : NonemptyFiniteChains Q) :
      ∃ z : SSet.toTop.obj (nerve P),
        z ∈ Set.range (SSet.toTop.map A.ι).hom ∧
          ∀ q ∈ C.finset, 0 < (PosetGeometry.coordinates P z).weights (label q) := by
    let s := finiteChainSimplex C
    let p : StdSimplex ℝ (Fin ((ChainOrdinal.choose C).dim+1)) := StdSimplex.single 0
    let z := RealizationPrism.simplexPoint (nerve Q) s p
    refine ⟨F z, ⟨f z, rfl⟩, fun q hq => ?_⟩
    obtain ⟨i, hi⟩ := (ChainOrdinal.choose C).enum.surjective ⟨q, hq⟩
    have hh := hl _ s p i
    change 0 < (PosetGeometry.coordinates P (F z)).weights
      (label (((ChainOrdinal.choose C).enum i).val)) at hh
    simpa only [hi] using hh
  let g := ChainLabelApproximation.nerveMapOfLabelsToSubcomplex A label hlabel hc
  have hg : g ≫ A.ι = ChainLabelApproximation.nerveMapOfLabels label hlabel :=
    ChainLabelApproximation.nerveMapOfLabelsToSubcomplex_ι A label hlabel hc
  refine ⟨g, hg, ⟨PosetGeometry.subcomplexHomotopyOfSupportSubset A
    (f.comp (chainRealizationMap Q)) (SSet.toTop.map g).hom ?_⟩⟩
  intro z
  have he : (SSet.toTop.map A.ι).hom ((SSet.toTop.map g).hom z) =
      (SSet.toTop.map (ChainLabelApproximation.nerveMapOfLabels label hlabel)).hom z := by
    have hmap : SSet.toTop.map g ≫ SSet.toTop.map A.ι =
        SSet.toTop.map (ChainLabelApproximation.nerveMapOfLabels label hlabel) := by
      rw [← SSet.toTop.map_comp, hg]
    exact ConcreteCategory.congr_hom hmap z
  rw [he]
  exact labelApproximation_support F label hlabel hl z

theorem exists_subcomplex_simplicial_approximation (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P] [Finite P] (A : (nerve P).Subcomplex)
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj A.toSSet)) :
    ∃ (r : ℕ) (g : nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) ⟶ A.toSSet),
      letI := Fintype.ofFinite (iteratedChainPoset Q r)
      Nonempty (((f.comp (iteratedChainRealization Q r)).comp
        (chainRealizationMap (iteratedChainPoset Q r))).Homotopy (SSet.toTop.map g).hom) := by
  let F := (SSet.toTop.map A.ι).hom.comp f
  obtain ⟨r, label, hlabel, hl⟩ := exists_poset_approximation_labels Q P F
  let := Fintype.ofFinite (iteratedChainPoset Q r)
  obtain ⟨g, _, hH⟩ := exists_label_subcomplex_homotopy A
    (f.comp (iteratedChainRealization Q r)) label hlabel hl
  exact ⟨r, g, hH⟩

/-- The actual realization-W test of the simplicial approximation agrees
with the original continuous map, inside the prescribed target. -/
theorem exists_subcomplex_weak_simplicial_approximation (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P] [Finite P] (A : (nerve P).Subcomplex)
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj A.toSSet)) :
    ∃ (r : ℕ) (g : nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) ⟶ A.toSSet),
      IsWeakHomotopyEquivalence f ↔ realizationWeakEquivalences g := by
  obtain ⟨r, g, ⟨H⟩⟩ := exists_subcomplex_simplicial_approximation Q P A f
  let := Fintype.ofFinite (iteratedChainPoset Q r)
  have h := isWeakHomotopyEquivalence_homotopy_iff H
  refine ⟨r, g, ?_⟩
  constructor
  · intro hf
    apply h.mp
    exact (chainRealizationMap_weak (iteratedChainPoset Q r)).comp
      ((iteratedChainRealization_weak Q r).comp hf)
  · intro hg
    have hh := h.mpr hg
    exact IsWeakHomotopyEquivalence.of_precomp (iteratedChainRealization_weak Q r)
      (IsWeakHomotopyEquivalence.of_precomp (chainRealizationMap_weak (iteratedChainPoset Q r)) hh)

/-- The same approximation on the actual iterated-subdivision functor,
using the proved canonical chain-nerve isomorphism. -/
theorem exists_subcomplex_iterated_weak_approximation (Q : PartOrd.{0}) [Fintype Q]
    (P : Type) [PartialOrder P] [Finite P] (A : (nerve P).Subcomplex)
    (f : C(SSet.toTop.obj (nerve Q), SSet.toTop.obj A.toSSet)) :
    ∃ (r : ℕ) (g : (iteratedSubdivision r).obj (nerve Q) ⟶ A.toSSet),
      IsWeakHomotopyEquivalence f ↔ realizationWeakEquivalences g := by
  obtain ⟨r, g, hg⟩ := exists_subcomplex_weak_simplicial_approximation Q P A f
  let e : (iteratedSubdivision (r+1)).obj (nerve Q) ≅
      nerve (NonemptyFiniteChains (iteratedChainPoset Q r)) :=
    iteratedSubdivisionNerveIso Q (r+1)
  exact ⟨r+1, e.hom ≫ g,
    hg.trans (realizationWeakEquivalences.cancel_left_of_respectsIso e.hom g).symm⟩

end

end Thomason.Construction.SubdivisionBarycentric

end

section

/-! # Barycentric boundary labels lie below the prescribed last vertex

Positive coordinates of an iterated barycentric image stay in an
original face below its recursively greatest vertex. Composing with a
monotone map therefore gives the bound needed to compare arbitrary
approximation labels with the prescribed boundary map.
-/

namespace Thomason.Construction.RelativeLabelCarrier

open CategoryTheory PartialOrder Opposite Convexity
open SubdivisionBarycentric ChainLabelApproximation
open scoped Simplicial

noncomputable section

/-- The recursively greatest original vertex of a subdivided vertex. -/
def greatestVertex (Q : PartOrd.{0}) (r : ℕ) : iteratedChainPoset Q r →o Q :=
  match r with
  | 0 => OrderHom.id
  | r+1 => (greatestVertex Q r).comp greatestHom

/-- Positive coordinates of a realized order map come from positive
coordinates in its source. -/
theorem coordinate_map_support {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (g : Q →o P) (z : SSet.toTop.obj (nerve Q)) (p : P)
    (hp : (PosetGeometry.coordinates P ((SSet.toTop.map (nerveMap g.monotone.functor)).hom z)).weights p ≠ 0) :
    ∃ q : Q, (PosetGeometry.coordinates Q z).weights q ≠ 0 ∧ g q = p := by
  classical
  rw [PosetGeometry.coordinates_nerveMap] at hp
  have hs : p ∈ ((PosetGeometry.coordinates Q z).weights.mapDomain g).support :=
    Finsupp.mem_support_iff.mpr hp
  rw [Finsupp.support_mapDomain_of_nonneg (PosetGeometry.coordinates Q z).nonneg] at hs
  obtain ⟨q, hq, hgp⟩ := Finset.mem_image.mp hs
  exact ⟨q, Finsupp.mem_support_iff.mp hq, hgp⟩

/-- Every original positive coordinate comes from a stage face containing
it below that face's recursively greatest vertex. -/
theorem iterated_coordinate_support (Q : PartOrd.{0}) [Finite Q] (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset Q r))) (q : Q)
    (hq : (PosetGeometry.coordinates Q (iteratedChainRealization Q r z)).weights q ≠ 0) :
    ∃ v : iteratedChainPoset Q r,
      (PosetGeometry.coordinates (iteratedChainPoset Q r) z).weights v ≠ 0 ∧
        q ≤ greatestVertex Q r v := by
  induction r with
  | zero => exact ⟨q, hq, le_rfl⟩
  | succ r ih =>
      let := Fintype.ofFinite (iteratedChainPoset Q r)
      change SSet.toTop.obj (nerve (NonemptyFiniteChains (iteratedChainPoset Q r))) at z
      change (PosetGeometry.coordinates Q (iteratedChainRealization Q r
        (chainRealizationMap (iteratedChainPoset Q r) z))).weights q ≠ 0 at hq
      obtain ⟨v, hv, hqv⟩ := ih _ hq
      rw [coordinates_chainRealizationMap] at hv
      obtain ⟨C, hC, hvC⟩ := chainPoint_support (iteratedChainPoset Q r) z v hv
      refine ⟨C, hC, hqv.trans ?_⟩
      exact (greatestVertex Q r).monotone (le_greatest C v hvC)

@[simp]
theorem coordinates_vertexPoint {Q : Type} [PartialOrder Q] (q : Q) :
    PosetGeometry.coordinates Q (posetVertexPoint q) = StdSimplex.single q := by
  unfold posetVertexPoint
  rw [PosetGeometry.coordinates_simplexPoint, StdSimplex.map_single]
  rfl

/-- In particular, the barycentric image of a stage vertex lies below its
recursively greatest original vertex. -/
theorem iterated_vertex_coordinate_le (Q : PartOrd.{0}) [Finite Q] (r : ℕ)
    (v : iteratedChainPoset Q r) (q : Q)
    (hq : (PosetGeometry.coordinates Q
      (iteratedChainRealization Q r (posetVertexPoint v))).weights q ≠ 0) :
    q ≤ greatestVertex Q r v := by
  classical
  obtain ⟨w, hw, hqw⟩ := iterated_coordinate_support Q r (posetVertexPoint v) q hq
  rw [coordinates_vertexPoint] at hw
  have hwv : w = v := by
    by_contra h
    simp [StdSimplex.weights_single, h] at hw
  simpa only [hwv] using hqw

/-- This is the boundary-label bound: positivity after the prescribed
realized order map gives an order comparison to the exact last vertex. -/
theorem label_le_prescribed (Q : PartOrd.{0}) [Finite Q]
    {P : Type} [PartialOrder P] (g : Q →o P) (r : ℕ)
    (v : iteratedChainPoset Q r) (p : P)
    (hp : 0 < (PosetGeometry.coordinates P
      ((SSet.toTop.map (nerveMap g.monotone.functor)).hom
        (iteratedChainRealization Q r (posetVertexPoint v)))).weights p) :
    p ≤ g (greatestVertex Q r v) := by
  obtain ⟨q, hq, hgp⟩ := coordinate_map_support g
    (iteratedChainRealization Q r (posetVertexPoint v)) p (ne_of_gt hp)
  rw [← hgp]
  exact g.monotone (iterated_vertex_coordinate_le Q r v q hq)

/-- The recursively greatest map is the actual iterated last-vertex map. -/
theorem greatestVertex_lastVertex (Q : PartOrd.{0}) [Finite Q] (r : ℕ) :
    (iteratedSubdivisionNerveIso Q r).hom ≫ nerveMap (greatestVertex Q r).monotone.functor =
      iteratedLastVertex (nerve Q) r := by
  induction r with
  | zero =>
      change 𝟙 _ ≫ nerveMap (OrderHom.id : Q →o Q).monotone.functor = 𝟙 _
      rw [Category.id_comp, orderNerveMap_id]
  | succ r ih =>
      change SSet.sd.map (iteratedSubdivisionNerveIso Q r).hom ≫
          NerveSubdivisionMap.map (iteratedChainPoset Q r) ≫
          nerveMap ((greatestVertex Q r).comp (greatestHom (P := iteratedChainPoset Q r))).monotone.functor =
        lastVertex.app ((iteratedSubdivision r).obj (nerve Q)) ≫
          iteratedLastVertex (nerve Q) r
      rw [orderNerveMap_comp]
      calc
        _ = (SSet.sd.map (iteratedSubdivisionNerveIso Q r).hom ≫
            lastVertex.app (nerve (iteratedChainPoset Q r))) ≫
            nerveMap (greatestVertex Q r).monotone.functor := by
          rw [← subdivision_greatest_eq_lastVertex]
          simp only [Category.assoc]
        _ = (lastVertex.app ((iteratedSubdivision r).obj (nerve Q)) ≫
            (iteratedSubdivisionNerveIso Q r).hom) ≫
            nerveMap (greatestVertex Q r).monotone.functor := by
          rw [lastVertex.naturality]
          rfl
        _ = _ := by rw [Category.assoc, ih]

end

end Thomason.Construction.RelativeLabelCarrier

end

section

/-! # Last-vertex support lies in the barycentric carrier

Every positive chain coefficient gives positive weight to each vertex
of that chain. Iteration shows that the exact last-vertex parameter map
has support contained in the shrinking barycentric parameter map.
-/

namespace Thomason.Construction.SubdivisionBarycentric

open CategoryTheory PartialOrder
open RelativeLabelCarrier

noncomputable section

theorem chainPoint_positive_of_mem (P : Type) [PartialOrder P] [Fintype P]
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P)))
    (C : NonemptyFiniteChains P)
    (hC : 0 < (PosetGeometry.coordinates (NonemptyFiniteChains P) z).weights C)
    (x : P) (hx : x ∈ C.finset) :
    0 < (chainPoint P z).weights x := by
  classical
  let := finite_nonemptyFiniteChains P
  let := Fintype.ofFinite (NonemptyFiniteChains P)
  rw [chainPoint_weight]
  have hp : 0 < (chainDistribution C).weights x := by
    rw [chainDistribution_weight, ite_eq_left hx]
    exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr C.nonempty)
  exact (mul_pos hC hp).trans_le (Finset.single_le_sum
    (fun D _ => mul_nonneg ((PosetGeometry.coordinates (NonemptyFiniteChains P) z).nonneg D)
      ((chainDistribution D).nonneg x)) (Finset.mem_univ C))

theorem iterated_greatest_coordinate_positive (P : PartOrd.{0}) [Finite P] (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset P r)))
    (v : iteratedChainPoset P r)
    (hv : 0 < (PosetGeometry.coordinates (iteratedChainPoset P r) z).weights v) :
    0 < (PosetGeometry.coordinates P (iteratedChainRealization P r z)).weights
      (greatestVertex P r v) := by
  induction r with
  | zero => exact hv
  | succ r ih =>
      let := Fintype.ofFinite (iteratedChainPoset P r)
      change SSet.toTop.obj (nerve (NonemptyFiniteChains (iteratedChainPoset P r))) at z
      change NonemptyFiniteChains (iteratedChainPoset P r) at v
      apply ih (chainRealizationMap (iteratedChainPoset P r) z)
        (ChainLabelApproximation.greatest v)
      rw [coordinates_chainRealizationMap]
      exact chainPoint_positive_of_mem (iteratedChainPoset P r) z v hv _
        (ChainLabelApproximation.greatest_mem v)

theorem iterated_lastVertex_support_subset (P : PartOrd.{0}) [Finite P] (r : ℕ)
    (z : SSet.toTop.obj (nerve (iteratedChainPoset P r))) :
    (PosetGeometry.coordinates P
      ((SSet.toTop.map (nerveMap (greatestVertex P r).monotone.functor)).hom z)).weights.support ⊆
      (PosetGeometry.coordinates P (iteratedChainRealization P r z)).weights.support := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := coordinate_map_support (greatestVertex P r) z x
    (Finsupp.mem_support_iff.mp hx)
  exact Finsupp.mem_support_iff.mpr (ne_of_gt
    (iterated_greatest_coordinate_positive P r z v
      (lt_of_le_of_ne ((PosetGeometry.coordinates (iteratedChainPoset P r) z).nonneg v) hv.symm)))

/-- The comparison with exact last vertex can be made wholly inside
the original barycentric carrier at each point. -/
def iteratedCarrierHomotopy (P : PartOrd.{0}) [Finite P] (r : ℕ) :
    (iteratedChainRealization P r).Homotopy
      (SSet.toTop.map (nerveMap (greatestVertex P r).monotone.functor)).hom :=
  PosetGeometry.commonChainHomotopy _ _ (fun z =>
    PosetGeometry.compatibleSupport_of_subset _ _
      (PosetGeometry.coordinates_chainSupported (iteratedChainRealization P r z))
      (iterated_lastVertex_support_subset P r z))

end

end Thomason.Construction.SubdivisionBarycentric

end

end OAI
