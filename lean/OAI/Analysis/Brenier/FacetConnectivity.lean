import OAI.Analysis.Brenier.CellGeometry

namespace OAI

/-! Connectivity of finite closed covers and active-cell intersection graphs. -/

noncomputable section
open Set

namespace Problem358

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

/-- Distinct cover members are adjacent when they meet. -/
def closedCoverGraph (s : ι → Set X) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (s i ∩ s j).Nonempty
  symm := ⟨by
    intro i j hij
    exact ⟨hij.1.symm, by simpa only [inter_comm] using hij.2⟩⟩
  loopless := ⟨by
    intro i hi
    exact hi.1 rfl⟩

/-- Any two nonempty members of a finite closed cover of a preconnected set
are joined by a chain of nonempty intersections. Empty cover members are harmless. -/
theorem closedCoverGraph_reachable (s : ι → Set X)
    (hclosed : ∀ i, IsClosed (s i)) (hconn : IsPreconnected (⋃ i, s i))
    (i j : ι) (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    (closedCoverGraph s).Reachable i j := by
  classical
  let G := closedCoverGraph s
  by_contra hij
  let U : Set X := ⋃ k : {k : ι // G.Reachable i k}, s k
  let V : Set X := ⋃ k : {k : ι // ¬ G.Reachable i k}, s k
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun k => hclosed k)
  have hV : IsClosed V := isClosed_iUnion_of_finite (fun k => hclosed k)
  have hcover : (⋃ k, s k) ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hik : G.Reachable i k
    · exact Or.inl (mem_iUnion.mpr ⟨⟨k, hik⟩, hk⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hik⟩, hk⟩)
  have hUne : ((⋃ k, s k) ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := hi
    exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩,
      mem_iUnion.mpr ⟨⟨i, SimpleGraph.Reachable.refl i⟩, hx⟩⟩
  have hVne : ((⋃ k, s k) ∩ V).Nonempty := by
    obtain ⟨x, hx⟩ := hj
    exact ⟨x, mem_iUnion.mpr ⟨j, hx⟩, mem_iUnion.mpr ⟨⟨j, hij⟩, hx⟩⟩
  obtain ⟨x, _, hxU, hxV⟩ :=
    isPreconnected_closed_iff.mp hconn U V hU hV hcover hUne hVne
  obtain ⟨⟨k, hk⟩, hxk⟩ := mem_iUnion.mp hxU
  obtain ⟨⟨l, hl⟩, hxl⟩ := mem_iUnion.mp hxV
  apply hl
  by_cases hkl : k = l
  · exact hkl ▸ hk
  · have hedge : G.Adj k l := ⟨hkl, ⟨x, hxk, hxl⟩⟩
    exact hk.trans hedge.reachable

/-- A finite closed cover of a preconnected set has connected intersection graph,
provided every member of the cover is nonempty. -/
theorem closedCoverGraph_connected [Nonempty ι] (s : ι → Set X)
    (hclosed : ∀ i, IsClosed (s i)) (hne : ∀ i, (s i).Nonempty)
    (hconn : IsPreconnected (⋃ i, s i)) : (closedCoverGraph s).Connected :=
  ⟨fun i j => closedCoverGraph_reachable s hclosed hconn i j (hne i) (hne j)⟩

namespace ClosedCoverConnectivity

/-- The closed weak-maximizer cell of a continuous finite family. -/
def maximalCell (K : Set X) (f : ι → X → ℝ) (i : ι) : Set X :=
  {x | x ∈ K ∧ ∀ j, f j x ≤ f i x}

omit [Finite ι] in
lemma maximalCell_isClosed (K : Set X) (hK : IsClosed K)
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i)) (i : ι) :
    IsClosed (maximalCell K f i) := by
  have heq : maximalCell K f i = K ∩ ⋂ j, {x | f j x ≤ f i x} := by
    ext x
    simp [maximalCell]
  rw [heq]
  exact hK.inter (isClosed_iInter (fun j => isClosed_le (hf j) (hf i)))

omit [TopologicalSpace X] in
lemma iUnion_maximalCell [Nonempty ι] (K : Set X) (f : ι → X → ℝ) :
    (⋃ i, maximalCell K f i) = K := by
  classical
  let := Fintype.ofFinite ι
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hi.1
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => f i x)
      Finset.univ_nonempty
    exact mem_iUnion.mpr ⟨i, hx, fun j => hi j (Finset.mem_univ j)⟩

/-- The nonempty affine-max cells have a connected intersection graph.
This statement concerns nonempty intersections, not positive-area common facets. -/
theorem maximalCell_graph_connected [Nonempty ι] (K : Set X)
    (hclosed : IsClosed K) (hconnected : IsPreconnected K)
    (f : ι → X → ℝ) (hf : ∀ i, Continuous (f i))
    (hactive : ∀ i, (maximalCell K f i).Nonempty) :
    (closedCoverGraph (maximalCell K f)).Connected := by
  apply closedCoverGraph_connected _ (maximalCell_isClosed K hclosed f hf) hactive
  rw [iUnion_maximalCell]
  exact hconnected

end ClosedCoverConnectivity

end Problem358

end

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Problem358

/-- A persistent tie which strictly dominates every other score is a positive
measure face whenever the parameter point maps into the interior of the source.
Only topology and positivity of nonempty open sets are needed. -/
theorem measure_face_pos_of_strict_tie
    {X W ι : Type*} [TopologicalSpace X] [TopologicalSpace W]
    [MeasurableSpace W] [Finite ι]
    (μ : Measure W) [Measure.IsOpenPosMeasure μ]
    (φ : W → X) (hφ : Continuous φ) (score : ι → X → ℝ)
    (hs : ∀ k, Continuous (score k)) (K : Set X) (z : W) (i j : ι)
    (hz : φ z ∈ interior K)
    (htie : ∀ w, score i (φ w) = score j (φ w))
    (hstrict : ∀ k, k ≠ i → k ≠ j → score k (φ z) < score i (φ z)) :
    0 < μ {w | φ w ∈ K ∧ score i (φ w) = score j (φ w) ∧
      ∀ k, score k (φ w) ≤ score i (φ w)} := by
  classical
  apply μ.measure_pos_of_mem_nhds (x := z)
  have hK : ∀ᶠ w in 𝓝 z, φ w ∈ K :=
    hφ.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
  have hall : ∀ᶠ w in 𝓝 z,
      ∀ k, k ≠ i → k ≠ j → score k (φ w) < score i (φ w) := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hki : k = i
    · exact Filter.Eventually.of_forall fun w hk _ => (hk hki).elim
    by_cases hkj : k = j
    · exact Filter.Eventually.of_forall fun w _ hk => (hk hkj).elim
    have hklt : ∀ᶠ w in 𝓝 z, score k (φ w) < score i (φ w) :=
      (isOpen_lt ((hs k).comp hφ) ((hs i).comp hφ)).mem_nhds (hstrict k hki hkj)
    exact hklt.mono fun w hw _ _ => hw
  filter_upwards [hK, hall] with w hw hws
  refine ⟨hw, htie w, fun k => ?_⟩
  by_cases hki : k = i
  · subst k
    exact le_rfl
  by_cases hkj : k = j
  · subst k
    exact (htie w).symm.le
  exact (hws k hki hkj).le

/-- A two-site strict tie in the interior has positive surface measure in the
tangent hyperplane of the two affine scores. No ambient volume assertion is
made: the measure is intrinsically on the tangent subspace. -/
theorem affine_pair_face_surface_pos
    {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [Finite ι]
    (y : ι → V) (c : ι → ℝ) (i j : ι) (x : V) (K : Set V)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [Measure.IsOpenPosMeasure μ]
    (hx : x ∈ interior K)
    (htie : ⟪y i, x⟫_ℝ + c i = ⟪y j, x⟫_ℝ + c j)
    (hstrict : ∀ k, k ≠ i → k ≠ j →
      ⟪y k, x⟫_ℝ + c k < ⟪y i, x⟫_ℝ + c i) :
    0 < μ {w | x + (w : V) ∈ K ∧
      ⟪y i, x + (w : V)⟫_ℝ + c i = ⟪y j, x + (w : V)⟫_ℝ + c j ∧
      ∀ k, ⟪y k, x + (w : V)⟫_ℝ + c k ≤ ⟪y i, x + (w : V)⟫_ℝ + c i} := by
  apply measure_face_pos_of_strict_tie μ (fun w => x + (w : V))
    (by fun_prop) (fun k z => ⟪y k, z⟫_ℝ + c k) (by intro k; fun_prop)
    K 0 i j
  · simpa using hx
  · intro w
    have hw : ⟪y i - y j, (w : V)⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
    simp only [inner_sub_left] at hw
    simp only [inner_add_right]
    linarith
  · simpa using hstrict

end Problem358

end

/-! Connectivity through strict two-cell interfaces. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {V W ι : Type*} [TopologicalSpace V] [TopologicalSpace W] [Finite ι]

/-- Edges are interior ties with no third maximizing branch. For affine
families these are precisely the local witnesses of positive-area facets. -/
def strictTieGraph (K : Set V) (f : ι → V → ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∃ x ∈ interior K, f i x = f j x ∧
    ∀ k, k ≠ i → k ≠ j → f k x < f i x
  symm := ⟨by
    rintro i j ⟨hij, x, hx, heq, hlt⟩
    exact ⟨hij.symm, x, hx, heq.symm, fun k hkj hki =>
      (hlt k hki hkj).trans_eq heq⟩⟩
  loopless := ⟨fun i hi => hi.1 rfl⟩

/-- A connected closed parameter domain without triple ties generates a chain
of strict two-cell interfaces between any two active endpoint labels. Empty
cells on this particular path do not cause an obstruction. -/
theorem strictTieGraph_reachable_of_parametric
    (K : Set V) (f : ι → V → ℝ) (hf : ∀ i, Continuous (f i))
    (s : Set W) (hs : IsClosed s) (hconn : IsPreconnected s)
    (a : W → V) (ha : Continuous a)
    (hK : ∀ t ∈ s, a t ∈ interior K)
    (htriple : ∀ t ∈ s, ∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      f i (a t) = f j (a t) → f i (a t) ≠ f k (a t))
    (i j : ι) (ti tj : W) (hti : ti ∈ s) (htj : tj ∈ s)
    (hi : ∀ k, f k (a ti) ≤ f i (a ti))
    (hj : ∀ k, f k (a tj) ≤ f j (a tj)) :
    (strictTieGraph K f).Reachable i j := by
  let : Nonempty ι := ⟨i⟩
  let cells := ClosedCoverConnectivity.maximalCell s (fun k => f k ∘ a)
  have hclosed : ∀ k, IsClosed (cells k) := fun k =>
    ClosedCoverConnectivity.maximalCell_isClosed s hs _ (fun k => (hf k).comp ha) k
  have hcover : (⋃ k, cells k) = s :=
    ClosedCoverConnectivity.iUnion_maximalCell s _
  have hpath : (closedCoverGraph cells).Reachable i j :=
    closedCoverGraph_reachable cells hclosed (hcover ▸ hconn) i j
      ⟨ti, hti, hi⟩ ⟨tj, htj, hj⟩
  apply SimpleGraph.Reachable.mono (Guv := hpath)
  rintro k l ⟨hkl, t, htk, htl⟩
  have heq : f k (a t) = f l (a t) := le_antisymm (htl.2 k) (htk.2 l)
  refine ⟨hkl, a t, hK t htk.1, heq, ?_⟩
  intro m hmk hml
  exact lt_of_le_of_ne (htk.2 m) (Ne.symm (htriple t htk.1 k l m hkl hmk hml heq))

end Problem358.PositiveFacet

end

/-! Connectivity of the strict-facet graph of an active affine partition. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Finite ι] [Nonempty ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Finite ι] [Nonempty ι] in
private lemma score_difference (y : ι → E) (c : ι → ℝ) (i j : ι) (x : E) :
    GenericSegment.affineScore (y i - y j) (c i - c j) x =
      TripleCell.score (y i) (c i) x - TripleCell.score (y j) (c j) x := by
  simp only [GenericSegment.affineScore, TripleCell.score, inner_sub_left,
    real_inner_comm (y i) x, real_inner_comm (y j) x]
  ring

/-- Every strictly active affine label is connected to every other by interior
two-cell ties. The proof chooses an actual generic segment avoiding all triple
ties, then applies finite closed-cover connectivity along that segment. -/
theorem affine_strictTieGraph_connected
    (μ : Measure E) [IsAddHaarMeasure μ]
    (K : Set E) (hK : Convex ℝ K) (y : ι → E) (c : ι → ℝ)
    (hactive : ∀ i, ∃ x ∈ interior K, ∀ j, j ≠ i →
      TripleCell.score (y j) (c j) x < TripleCell.score (y i) (c i) x) :
    (strictTieGraph K (fun i => TripleCell.score (y i) (c i))).Connected := by
  classical
  let f : ι → E → ℝ := fun i => TripleCell.score (y i) (c i)
  have hf : ∀ i, Continuous (f i) := by
    intro i
    exact (continuous_id.inner continuous_const).add continuous_const
  have hy : Function.Injective y := by
    intro i j heq
    by_contra hij
    obtain ⟨x, _, hx⟩ := hactive i
    obtain ⟨z, _, hz⟩ := hactive j
    have hxi := hx j (fun h => hij h.symm)
    have hzj := hz i hij
    simp only [TripleCell.score, heq] at hxi hzj
    linarith
  let U : ι → Set E := fun i => {x | x ∈ interior K ∧ ∀ j, j ≠ i → f j x < f i x}
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    simp only [U, ofPred_and, ofPred_forall]
    exact isOpen_interior.inter (isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (hf j) (hf i))
  have hUne : ∀ i, (U i).Nonempty := hactive
  have hae : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → f i x ≠ f j x := by
    filter_upwards [ae_affine_tie_implies_slopes_eq μ y c] with x hx i j hij heq
    exact hij (hy (hx i j heq))
  let T := {t : ι × ι × ι //
    LinearIndependent ℝ ![y t.1 - y t.2.1, y t.1 - y t.2.2]}
  let v : T → E := fun t => y t.1.1 - y t.1.2.1
  let w : T → E := fun t => y t.1.1 - y t.1.2.2
  let a : T → ℝ := fun t => c t.1.1 - c t.1.2.1
  let b : T → ℝ := fun t => c t.1.1 - c t.1.2.2
  refine ⟨fun i j => ?_⟩
  obtain ⟨p, hpU, hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    ((hU i).measure_ne_zero μ (hUne i)) (ae_restrict_of_ae hae)
  have hnormal : ∀ t : T, LinearIndependent ℝ ![v t, w t] := fun t => t.2
  have hpfirst : ∀ t : T, GenericSegment.affineScore (v t) (a t) p ≠ 0 := by
    intro t
    have ht : t.1.1 ≠ t.1.2.1 := by
      intro heq
      have hn := t.2.ne_zero (0 : Fin 2)
      simp [heq] at hn
    rw [score_difference]
    exact sub_ne_zero.mpr (hp _ _ ht)
  obtain ⟨q, hqU, hq⟩ := GenericSegment.exists_endpoint_in_open_avoiding_common_zeros
    μ v w a b hnormal hpfirst (hU j) (hUne j)
  have hsegment : segment ℝ p q ⊆ interior K :=
    hK.interior.segment_subset hpU.1 hqU.1
  have htriple : ∀ x ∈ segment ℝ p q, ∀ l m n,
      l ≠ m → n ≠ l → n ≠ m → f l x = f m x → f l x ≠ f n x := by
    intro x hx l m n hlm hnl hnm hlmEq hlnEq
    have hind : LinearIndependent ℝ ![y l - y m, y l - y n] := by
      apply TripleCell.linearIndependent_slopes_of_tie ?_ ?_ ?_ hlmEq hlnEq
      · obtain ⟨z, _, hz⟩ := hactive l
        exact ⟨z, hz m hlm.symm, hz n hnl⟩
      · obtain ⟨z, _, hz⟩ := hactive m
        exact ⟨z, hz l hlm, hz n hnm⟩
      · obtain ⟨z, _, hz⟩ := hactive n
        exact ⟨z, hz l hnl.symm, hz m hnm.symm⟩
    let t : T := ⟨(l, m, n), hind⟩
    apply hq t x hx
    constructor
    · change GenericSegment.affineScore (y l - y m) (c l - c m) x = 0
      rw [score_difference]
      exact sub_eq_zero.mpr hlmEq
    · change GenericSegment.affineScore (y l - y n) (c l - c n) x = 0
      rw [score_difference]
      exact sub_eq_zero.mpr hlnEq
  have hcompact : IsCompact (segment ℝ p q) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  apply strictTieGraph_reachable_of_parametric K f hf
    (segment ℝ p q) hcompact.isClosed (convex_segment p q : Convex ℝ _).isPreconnected
    id continuous_id (fun t ht => hsegment ht) htriple i j p q
    (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  · intro k
    by_cases hki : k = i
    · subst k
      exact le_rfl
    exact (hpU.2 k hki).le
  · intro k
    by_cases hkj : k = j
    · subst k
      exact le_rfl
    exact (hqU.2 k hkj).le

end Problem358.PositiveFacet

end

/-! Positive surface measures on every edge of the connected strict-facet graph. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped Topology InnerProductSpace

namespace Problem358.PositiveFacet

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Finite ι]

/-- The surface face in a tie hyperplane, translated from an arbitrary point
of that plane. This is an intrinsic measure domain, not ambient volume. -/
def surfaceFace (K : Set E) (y : ι → E) (c : ι → ℝ) (i j : ι) (base : E) :
    Set ((ℝ ∙ (y i - y j))ᗮ) :=
  {w | base + (w : E) ∈ K ∧
    TripleCell.score (y i) (c i) (base + (w : E)) =
      TripleCell.score (y j) (c j) (base + (w : E)) ∧
    ∀ k, TripleCell.score (y k) (c k) (base + (w : E)) ≤
      TripleCell.score (y i) (c i) (base + (w : E))}

omit [BorelSpace E] in
/-- Strict-facet edges have positive surface measure in a parametrization at
any point of their tie plane. This transfers the local strict-face theorem to
the fixed bases used when defining geometric graph coefficients. -/
theorem strictTieGraph_adj_surfaceFace_pos
    (K : Set E) (y : ι → E) (c : ι → ℝ) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j)
    (base : E)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [IsOpenPosMeasure μ] :
    0 < μ (surfaceFace K y c i j base) := by
  obtain ⟨_, x, hx, htie, hstrict⟩ := hedge
  have horth : x - base ∈ (ℝ ∙ (y i - y j))ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    simp only [inner_sub_left, inner_sub_right]
    unfold TripleCell.score at htie hbase
    linarith
  let w0 : (ℝ ∙ (y i - y j))ᗮ := ⟨x - base, horth⟩
  have hw0 : base + (w0 : E) = x := by
    change base + (x - base) = x
    abel
  apply measure_face_pos_of_strict_tie μ (fun w => base + (w : E))
    (by fun_prop) (fun k => TripleCell.score (y k) (c k))
    (by intro k; exact (continuous_id.inner continuous_const).add continuous_const)
    K w0 i j
  · simpa only [hw0] using hx
  · intro w
    have hw : ⟪(w : E), y i - y j⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.property
    simp only [inner_sub_right] at hw
    unfold TripleCell.score at hbase ⊢
    simp only [inner_add_left]
    linarith
  · simpa only [hw0] using hstrict

/-- The geometric strict-facet graph is connected and each of its edges has
positive intrinsic face measure, uniformly over arbitrary tie-plane bases.
No quantitative lower bound on individual face areas is needed. -/
theorem exists_connected_positive_surface_graph
    [FiniteDimensional ℝ E] [Nonempty ι]
    (ρ : Measure E) [IsAddHaarMeasure ρ]
    (K : Set E) (hK : Convex ℝ K) (y : ι → E) (c : ι → ℝ)
    (hactive : ∀ i, ∃ x ∈ interior K, ∀ j, j ≠ i →
      TripleCell.score (y j) (c j) x < TripleCell.score (y i) (c i) x) :
    ∃ G : SimpleGraph ι, G.Connected ∧ ∀ i j, G.Adj i j →
      ∀ base : E,
      TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base →
      ∀ μ : Measure ((ℝ ∙ (y i - y j))ᗮ), IsOpenPosMeasure μ →
        0 < μ (surfaceFace K y c i j base) := by
  refine ⟨strictTieGraph K (fun k => TripleCell.score (y k) (c k)),
    affine_strictTieGraph_connected ρ K hK y c hactive, ?_⟩
  intro i j hij base hbase μ hμ
  let := hμ
  exact strictTieGraph_adj_surfaceFace_pos K y c hij base hbase μ

end Problem358.PositiveFacet

end

/-! Positive-mass convex affine partitions have a connected positive-facet graph. -/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace

namespace Problem358.PositiveFacet

variable {d : ℕ} {ι : Type*} [Finite ι]

omit [Finite ι] in
/-- The intrinsic face domain is exactly the pullback of the intersection of
the two canonical closed cells. -/
theorem surfaceFace_eq_preimage_closedCells
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i j : ι) (base : E d) :
    surfaceFace K y c i j base =
      (fun w : (ℝ ∙ (y i - y j))ᗮ => base + (w : E d)) ⁻¹'
        (CellGeometry.closedCell K y c i ∩ CellGeometry.closedCell K y c j) := by
  ext w
  simp only [surfaceFace, CellGeometry.closedCell, TripleCell.score,
    mem_ofPred_eq, mem_preimage, mem_inter_iff]
  constructor
  · rintro ⟨hK, hij, hi⟩
    exact ⟨⟨hK, hi⟩, hK, fun k => (hi k).trans_eq hij⟩
  · rintro ⟨⟨hK, hi⟩, _, hj⟩
    exact ⟨hK, le_antisymm (hj i) (hi j), hi⟩

omit [Finite ι] in
/-- Compact source cells give compact surface domains in every translated
tangent-plane parametrization. -/
theorem isCompact_surfaceFace
    (K : Set (E d)) (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ)
    (i j : ι) (base : E d) : IsCompact (surfaceFace K y c i j base) := by
  rw [surfaceFace_eq_preimage_closedCells]
  have he : Topology.IsClosedEmbedding
      (fun w : (ℝ ∙ (y i - y j))ᗮ => base + (w : E d)) :=
    (Homeomorph.addLeft base).isClosedEmbedding.comp
      (Submodule.isClosedEmbedding_subtype _ (Submodule.isClosed_orthogonal _))
  exact he.isCompact_preimage
    ((CellGeometry.isCompact_closedCell hK y c i).inter_right
      (CellGeometry.isClosed_closedCell hK.isClosed y c j))

/-- Positivity remains genuine after `ENNReal.toReal`: compactness excludes
an infinite surface measure from being silently converted to zero. -/
theorem strictTieGraph_adj_surfaceFace_real_pos
    (K : Set (E d)) (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j)
    (base : E d)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ))
    [IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ] :
    0 < (μ (surfaceFace K y c i j base)).toReal := by
  exact ENNReal.toReal_pos (strictTieGraph_adj_surfaceFace_pos K y c hedge base hbase μ).ne'
    (isCompact_surfaceFace K hK y c i j base).measure_ne_top

/-- The coefficient used in the cell Laplacian is positive on every strict
facet edge. Both the source-volume and surface-area `toReal` conversions are
justified by compactness. -/
theorem strictTieGraph_adj_normalized_surface_pos
    (K : Set (E d)) (hK : IsCompact K) (hvol : volume K ≠ 0)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) {i j : ι}
    (hedge : (strictTieGraph K (fun k => TripleCell.score (y k) (c k))).Adj i j)
    (base : E d)
    (hbase : TripleCell.score (y i) (c i) base = TripleCell.score (y j) (c j) base)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ))
    [IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ] :
    0 < (μ (surfaceFace K y c i j base)).toReal /
      ((volume K).toReal * ‖y i - y j‖) := by
  apply div_pos (strictTieGraph_adj_surfaceFace_real_pos K hK y c hedge base hbase μ)
  exact mul_pos (ENNReal.toReal_pos hvol hK.measure_ne_top)
    (norm_pos_iff.mpr (sub_ne_zero.mpr (hy.ne hedge.1)))

/-- No generic-position, no facet positivity, and no strict-activation premise
is left in this connectivity statement: all are consequences of positive cell
masses and absolute continuity of the source. -/
theorem strictTieGraph_connected_of_positive_cells [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0) :
    (strictTieGraph K (fun i => TripleCell.score (y i) (c i))).Connected := by
  apply affine_strictTieGraph_connected volume K hK y c
  intro i
  exact CellGeometry.exists_strict_active_interior_of_mass hρ hK y c hy i (hpos i)

/-- The exact positive-surface connectivity conclusion for positive-mass
convex cells. Surface measures can be independently selected on each tangent
hyperplane; fixed affine-plane basepoints are explicitly permitted. -/
theorem exists_connected_surface_graph_of_positive_cells [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0) :
    ∃ G : SimpleGraph ι, G.Connected ∧ ∀ i j, G.Adj i j →
      ∀ base : E d,
      (⟪base, y i⟫_ℝ + c i = ⟪base, y j⟫_ℝ + c j) →
      ∀ μ : Measure ((ℝ ∙ (y i - y j))ᗮ), IsOpenPosMeasure μ →
        0 < μ ((fun w : (ℝ ∙ (y i - y j))ᗮ => base + (w : E d)) ⁻¹'
          (CellGeometry.closedCell K y c i ∩ CellGeometry.closedCell K y c j)) := by
  obtain ⟨G, hG, hfaces⟩ := exists_connected_positive_surface_graph volume K hK y c
    (fun i => CellGeometry.exists_strict_active_interior_of_mass hρ hK y c hy i (hpos i))
  refine ⟨G, hG, fun i j hij base hb μ hμ => ?_⟩
  rw [← surfaceFace_eq_preimage_closedCells]
  exact hfaces i j hij base hb μ hμ

/-- The weighted graph needed by the cell-Laplacian range theorem, with
normalized geometric face coefficients rather than assumed positive weights. -/
theorem exists_connected_normalized_surface_graph [Nonempty ι]
    (ρ : Measure (E d)) (hρ : ρ ≪ volume)
    (K : Set (E d)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ i, ρ (CellGeometry.closedCell K y c i) ≠ 0) :
    ∃ G : SimpleGraph ι, G.Connected ∧ ∀ i j, G.Adj i j →
      ∀ base : E d,
      (⟪base, y i⟫_ℝ + c i = ⟪base, y j⟫_ℝ + c j) →
      ∀ μ : Measure ((ℝ ∙ (y i - y j))ᗮ),
        IsOpenPosMeasure μ → IsFiniteMeasureOnCompacts μ →
        0 < (μ (surfaceFace K y c i j base)).toReal /
          ((volume K).toReal * ‖y i - y j‖) := by
  have hvol : volume K ≠ 0 := by
    intro hz
    let i : ι := Classical.choice inferInstance
    exact hpos i (hρ (measure_mono_null (CellGeometry.closedCell_subset K y c i) hz))
  refine ⟨strictTieGraph K (fun i => TripleCell.score (y i) (c i)),
    strictTieGraph_connected_of_positive_cells ρ hρ K hconv y c hy hpos, ?_⟩
  intro i j hij base hb μ hμ hfin
  let := hμ
  let := hfin
  exact strictTieGraph_adj_normalized_surface_pos K hK hvol y c hy hij base hb μ

end Problem358.PositiveFacet

end

end OAI
