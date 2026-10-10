import OAI.Analysis.Brenier.CellGeometry
import OAI.Analysis.Brenier.MovingTrace

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology

namespace Problem358

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- If an affine slice meets the interior of a convex set, its relative interior
contains no new boundary points of the ambient convex set. -/
theorem interior_affine_preimage_eq (f : U →ᵃ[ℝ] V) (hf : Continuous f)
    {K : Set V} (hK : Convex ℝ K) (hmeet : (f ⁻¹' interior K).Nonempty) :
    interior (f ⁻¹' K) = f ⁻¹' interior K := by
  apply Subset.antisymm ?_ (preimage_interior_subset_interior_preimage hf)
  intro x hx
  obtain ⟨p, hp⟩ := hmeet
  have hone := AffineMap.lineMap_apply_one (k := ℝ) p x
  obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ hone |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp hx) |>.exists_gt
  have hft : AffineMap.lineMap (f p) (f x) t ∈ K := by
    simpa only [Set.mem_preimage, f.apply_lineMap] using ht
  change f x ∈ interior K
  apply hK.openSegment_interior_self_subset_interior hp hft
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := ℝ) (f p) (f x), ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩,
    AffineMap.lineMap_apply_one (k := ℝ) (f p) (f x)⟩

/-- Boundary commutes with an affine slice through the interior of a closed convex set. -/
theorem frontier_affine_preimage_eq (f : U →ᵃ[ℝ] V) (hf : Continuous f)
    {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty) :
    frontier (f ⁻¹' K) = f ⁻¹' frontier K := by
  rw [frontier, frontier, (hclosed.preimage hf).closure_eq, hclosed.closure_eq,
    interior_affine_preimage_eq f hf hK hmeet, Set.preimage_sdiff]

/-- The ambient boundary cuts an interior-crossing affine slice in a Haar-null set.
This applies to the hyperplane and lower-dimensional fibers in cell differentiation. -/
theorem haar_affine_preimage_frontier_null [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [IsAddHaarMeasure μ]
    (f : U →ᵃ[ℝ] V) {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty) : μ (f ⁻¹' frontier K) = 0 := by
  rw [← frontier_affine_preimage_eq f f.continuous_of_finiteDimensional hclosed hK hmeet]
  exact (Convex.affine_preimage f hK).addHaar_frontier μ

/-- Continuous integrands restricted to a convex body are continuous almost
 everywhere along an affine slice crossing its interior. -/
theorem ae_continuousAt_indicator_on_affine_slice [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [IsAddHaarMeasure μ]
    (f : U →ᵃ[ℝ] V) {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty)
    {W : Type*} [TopologicalSpace W] [Zero W] {g : V → W}
    (hg : ContinuousOn g (interior K)) :
    ∀ᵐ x ∂μ, ContinuousAt (K.indicator g) (f x) := by
  have haway : ∀ᵐ x ∂μ, f x ∉ frontier K := by
    rw [ae_iff]
    simpa only [not_not, Set.preimage] using
      haar_affine_preimage_frontier_null μ f hclosed hK hmeet
  exact haway.mono fun x hx => hg.continuousAt_indicator hx

/-- Moving-slice indicators converge almost everywhere before invoking dominated
convergence; no differentiability in the transverse parameter is required. -/
theorem ae_tendsto_indicator_on_affine_slice [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [IsAddHaarMeasure μ]
    (f : U →ᵃ[ℝ] V) {K : Set V} (hclosed : IsClosed K) (hK : Convex ℝ K)
    (hmeet : (f ⁻¹' interior K).Nonempty)
    {W : Type*} [TopologicalSpace W] [Zero W] {g : V → W}
    (hg : ContinuousOn g (interior K))
    {A : Type*} {l : Filter A} {F : A → U → V}
    (hF : ∀ᵐ x ∂μ, Filter.Tendsto (fun a => F a x) l (𝓝 (f x))) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun a => K.indicator g (F a x)) l
      (𝓝 (K.indicator g (f x))) := by
  filter_upwards [ae_continuousAt_indicator_on_affine_slice μ f hclosed hK hmeet hg,
    hF] with x hx hFx
  exact hx.tendsto.comp hFx

end Problem358

end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Positive-mass affine cells have regular interfaces: the source boundary and
all third-branch ties are negligible for surface Haar measure. -/
theorem ae_regular_interface {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : inner ℝ z (y i) + c i = inner ℝ z (y j) + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      z + (w : E d) ∉ frontier K ∧ ∀ k, k ≠ i → k ≠ j →
      inner ℝ (z + (w : E d)) (y i) + c i ≠
        inner ℝ (z + (w : E d)) (y k) + c k := by
  let W := (ℝ ∙ (y i - y j))ᗮ
  let f : W →ᵃ[ℝ] E d := AffineMap.const ℝ W z + W.subtype.toAffineMap
  have hmeet : (f ⁻¹' interior K).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [f] using hz
  have hboundary : ∀ᵐ w : W ∂μ, z + (w : E d) ∉ frontier K := by
    have hn := Problem358.haar_affine_preimage_frontier_null μ f hclosed hconv hmeet
    change μ {w : W | z + (w : E d) ∈ frontier K} = 0 at hn
    simpa only [ae_iff, not_not] using hn
  have hactive : ∀ k, ∃ x, ∀ l, l ≠ k →
      TripleCell.score (y l) (c l) x < TripleCell.score (y k) (c k) x := by
    intro k
    obtain ⟨x, _, hx⟩ := exists_strict_active_interior_of_mass hρ hconv y c hy k (hpos k)
    exact ⟨x, hx⟩
  exact hboundary.and (TripleCell.ae_no_other_ties_on_interface y c hactive hij htie μ)

/-- Membership in a set is eventually constant under convergence away from its boundary. -/
theorem eventually_mem_iff_of_not_mem_frontier {X A : Type*} [TopologicalSpace X]
    {s : Set X} {x : X} (hx : x ∉ frontier s) {l : Filter A} {f : A → X}
    (hf : Tendsto f l (𝓝 x)) : ∀ᶠ a in l, f a ∈ s ↔ x ∈ s := by
  have hcases : x ∈ interior s ∨ x ∈ interior sᶜ := by
    simpa only [← Set.mem_union, ← compl_frontier_eq_union_interior,
      Set.mem_compl_iff] using hx
  rcases hcases with hinside | houtside
  · filter_upwards [hf.eventually (isOpen_interior.eventually_mem hinside)] with a ha
    exact iff_of_true (interior_subset ha) (interior_subset hinside)
  · filter_upwards [hf.eventually (isOpen_interior.eventually_mem houtside)] with a ha
    exact iff_of_false (interior_subset ha) (interior_subset houtside)

/-- A strict limiting inequality has an eventually constant weak-inequality indicator. -/
theorem eventually_le_iff_of_tendsto_ne {A : Type*} {l : Filter A}
    {f g : A → ℝ} {a b : ℝ} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hne : a ≠ b) :
    ∀ᶠ t in l, f t ≤ g t ↔ a ≤ b := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · filter_upwards [hf.eventually_lt hg hlt] with t ht
    exact iff_of_true ht.le hlt.le
  · filter_upwards [hg.eventually_lt hf hgt] with t ht
    exact iff_of_false (not_le_of_gt ht) (not_le_of_gt hgt)

/-- The unchanged cell factors in a moving-interface argument are eventually
constant at surface-almost every point. Both source points and affine branches
may vary along an arbitrary filter. -/
theorem ae_eventually_stable_interface {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : inner ℝ z (y i) + c i = inner ℝ z (y j) + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure]
    {A : Type*} {l : Filter A}
    {F : A → ((ℝ ∙ (y i - y j))ᗮ) → E d}
    {y' : A → ι → E d} {c' : A → ι → ℝ}
    (hy' : ∀ k, Tendsto (fun a => y' a k) l (𝓝 (y k)))
    (hc' : ∀ k, Tendsto (fun a => c' a k) l (𝓝 (c k)))
    (hF : ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      Tendsto (fun a => F a w) l (𝓝 (z + (w : E d)))) :
    ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ, ∀ᶠ a in l,
      (F a w ∈ K ↔ z + (w : E d) ∈ K) ∧
      ∀ k, k ≠ i → k ≠ j →
      (inner ℝ (F a w) (y' a k) + c' a k ≤ inner ℝ (F a w) (y' a i) + c' a i ↔
        inner ℝ (z + (w : E d)) (y k) + c k ≤
          inner ℝ (z + (w : E d)) (y i) + c i) := by
  filter_upwards [ae_regular_interface hρ hclosed hconv y c hy hpos hij hz htie μ,
    hF] with w hw hFw
  have hmem := eventually_mem_iff_of_not_mem_frontier hw.1 hFw
  have hother : ∀ᶠ a in l, ∀ k, k ≠ i → k ≠ j →
      (inner ℝ (F a w) (y' a k) + c' a k ≤ inner ℝ (F a w) (y' a i) + c' a i ↔
        inner ℝ (z + (w : E d)) (y k) + c k ≤
          inner ℝ (z + (w : E d)) (y i) + c i) := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hki : k = i
    · subst k
      exact Filter.Eventually.of_forall (fun _ h => (h rfl).elim)
    by_cases hkj : k = j
    · subst k
      exact Filter.Eventually.of_forall (fun _ _ h => (h rfl).elim)
    have ht (k : ι) : Tendsto (fun a => inner ℝ (F a w) (y' a k) + c' a k) l
        (𝓝 (inner ℝ (z + (w : E d)) (y k) + c k)) :=
      (hFw.inner (hy' k)).add (hc' k)
    have he := eventually_le_iff_of_tendsto_ne (ht k) (ht i) (Ne.symm (hw.2 k hki hkj))
    exact he.mono (fun _ ha _ _ => ha)
  exact hmem.and hother

end Problem358.CellGeometry

namespace Problem358.CellGeometry

/-- The regular-interface theorem for an arbitrary point on the equality plane.
Positive cell masses supply an interior crossing, so the chosen affine-chart base
need not itself belong to the convex source. -/
theorem ae_regular_interface_of_tie
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d}
    (htie : inner ℝ z (y i) + c i = inner ℝ z (y j) + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure] :
    ∀ᵐ w : (ℝ ∙ (y i - y j))ᗮ ∂μ,
      z + (w : E d) ∉ frontier K ∧ ∀ k, k ≠ i → k ≠ j →
      inner ℝ (z + (w : E d)) (y i) + c i ≠
        inner ℝ (z + (w : E d)) (y k) + c k := by
  let W := (ℝ ∙ (y i - y j))ᗮ
  let f : W →ᵃ[ℝ] E d := AffineMap.const ℝ W z + W.subtype.toAffineMap
  obtain ⟨x, hx, hxtie⟩ := exists_equality_interior_of_positive_cells
    hρ hconv y c hy hij (hpos i) (hpos j)
  have hxz : x - z ∈ W := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    simp only [inner_sub_left, inner_sub_right]
    linarith
  have hmeet : (f ⁻¹' interior K).Nonempty := by
    refine ⟨⟨x - z, hxz⟩, ?_⟩
    change z + (x - z) ∈ interior K
    convert hx using 1
    abel
  have hboundary : ∀ᵐ w : W ∂μ, z + (w : E d) ∉ frontier K := by
    have hn := Problem358.haar_affine_preimage_frontier_null μ f hclosed hconv hmeet
    change μ {w : W | z + (w : E d) ∈ frontier K} = 0 at hn
    simpa only [ae_iff, not_not] using hn
  have hactive : ∀ k, ∃ x, ∀ l, l ≠ k →
      TripleCell.score (y l) (c l) x < TripleCell.score (y k) (c k) x := by
    intro k
    obtain ⟨x, _, hx⟩ := exists_strict_active_interior_of_mass hρ hconv y c hy k (hpos k)
    exact ⟨x, hx⟩
  exact hboundary.and (TripleCell.ae_no_other_ties_on_interface y c hactive hij htie μ)

end Problem358.CellGeometry

end

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology RealInnerProductSpace

namespace Problem358.MovingCellTrace

/-- The actual surface-almost-everywhere trace needed by moving-cell
 differentiation. Regularity is derived from positive cells, rather than assumed.
 The varying cut normals are independent, so this also permits the mixed
 current/base cuts in the finite-product telescoping identity. -/
theorem ae_tendsto_interface_remainder
    {d : ℕ} {ι α U : Type*} [Fintype ι] {l : Filter α}
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {K : Set (E d)} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hpos : ∀ k, ρ (CellGeometry.closedCell K y c k) ≠ 0)
    {i j : ι} (hij : i ≠ j) {z : E d} (hz : z ∈ interior K)
    (htie : ⟪z, y i⟫ + c i = ⟪z, y j⟫ + c j)
    (μ : Measure ((ℝ ∙ (y i - y j))ᗮ)) [μ.IsAddHaarMeasure]
    (J : Finset ι) (hJ : ∀ k ∈ J, k ≠ i ∧ k ≠ j)
    {w : E d → ℝ} (hw : ContinuousOn w (interior K))
    {F : α → U → ((ℝ ∙ (y i - y j))ᗮ) → E d}
    {a : α → ι → E d} {b : α → ι → ℝ}
    (ha : ∀ k ∈ J, Tendsto (fun q => a q k) l (𝓝 (y i - y k)))
    (hb : ∀ k ∈ J, Tendsto (fun q => b q k) l (𝓝 (c i - c k)))
    (hF : ∀ᵐ p : (ℝ ∙ (y i - y j))ᗮ ∂μ, ∀ u : U,
      Tendsto (fun q => F q u p) l (𝓝 (z + (p : E d)))) :
    ∀ᵐ p : (ℝ ∙ (y i - y j))ᗮ ∂μ, ∀ u : U,
      Tendsto (fun q => K.indicator w (F q u p) * ∏ k ∈ J,
        cutIndicator (⟪F q u p, a q k⟫ + b q k)) l
        (𝓝 (K.indicator w (z + (p : E d)) * ∏ k ∈ J,
          cutIndicator (⟪z + (p : E d), y i - y k⟫ + (c i - c k)))) := by
  filter_upwards [CellGeometry.ae_regular_interface hρ hclosed hconv y c hy hpos
    hij hz htie μ, hF] with p hp hFp
  intro u
  apply tendsto_remainder_trace J (hFp u) hp.1 hw
  · intro k hk
    exact ((hFp u).inner (ha k hk)).add (hb k hk)
  · intro k hk heq
    apply hp.2 k (hJ k hk).1 (hJ k hk).2
    rw [inner_sub_right] at heq
    linarith

end Problem358.MovingCellTrace

end

end OAI
