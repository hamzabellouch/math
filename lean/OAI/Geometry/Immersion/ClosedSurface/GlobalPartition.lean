import OAI.Geometry.Immersion.ClosedSurface.MetricPatches
import OAI.Geometry.Immersion.ClosedSurface.CompactPartition

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set Function Filter PhaseGeometry SmallModes RealModes PhaseGrid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
lemma chartCoordinates_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ, SmallModes.Base) ∞ (chartCoordinates p) (chartAt Plane p).source :=
  planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

def refinedCutoff (p : M) (ψ : M → ℝ) (s : Finset Index) (h : ℝ) (a : Index) : M → ℝ :=
  fun q => ψ q * normalizedCutoff s h a (chartCoordinates p q)

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma refinedCutoff_tsupport_outer (p : M) (ψ : M → ℝ) (s : Finset Index) (h : ℝ) (a : Index) :
    tsupport (refinedCutoff p ψ s h a) ⊆ tsupport ψ := tsupport_mul_subset_left

omit [T2Space M] [CompactSpace M] in
lemma refinedCutoff_smooth (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsource : tsupport ψ ⊆ (chartAt Plane p).source)
    {s : Finset Index} {h : ℝ} (hh : 0 < h)
    (hcover : chartSupport p ψ ⊆ coverRegion s h) (a : Index) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (refinedCutoff p ψ s h a) := by
  apply contMDiff_of_tsupport
  intro q hq
  have hqψ := refinedCutoff_tsupport_outer p ψ s h a hq
  have hqc : chartCoordinates p q ∈ coverRegion s h := hcover ⟨q,hqψ,rfl⟩
  have hc := (chartCoordinates_smoothOn p q (hsource hqψ)).contMDiffAt
    ((chartAt Plane p).open_source.mem_nhds (hsource hqψ))
  have hn := (normalizedCutoff_smooth hh (fun x hx => coverRegion_covers s h hx) a
    (chartCoordinates p q) hqc).contDiffAt ((coverRegion_open s h).mem_nhds hqc)
  exact (hψ q).mul (hn.contMDiffAt.comp q hc)

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma refinedCutoff_hasCompactSupport (p : M) (ψ : M → ℝ) (s : Finset Index) (h : ℝ) (a : Index)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (refinedCutoff p ψ s h a) :=
  hψ.of_isClosed_subset (isClosed_tsupport _) (refinedCutoff_tsupport_outer p ψ s h a)



omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma refinedCutoff_tsupport_inner (p : M) {ψ : M → ℝ}
    (hsource : tsupport ψ ⊆ (chartAt Plane p).source)
    (s : Finset Index) (h : ℝ) (a : Index) :
    tsupport (refinedCutoff p ψ s h a) ⊆
      (chartCoordinates p) ⁻¹' tsupport (normalizedCutoff s h a) := by
  intro q hq
  have hqψ := refinedCutoff_tsupport_outer p ψ s h a hq
  have hc := (chartCoordinates_continuousOn p q (hsource hqψ)).continuousAt
    ((chartAt Plane p).open_source.mem_nhds (hsource hqψ))
  by_contra hn
  have heq := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hc
  have hz : refinedCutoff p ψ s h a =ᶠ[𝓝 q] 0 := by
    filter_upwards [heq] with x hx
    simp only [refinedCutoff,Pi.zero_apply,Function.comp_apply] at hx ⊢
    rw [hx,mul_zero]
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hq

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
lemma refinedCutoff_squares (p : M) (ψ : M → ℝ) {s : Finset Index} {h : ℝ}
    (hh : 0 < h) (hcover : chartSupport p ψ ⊆ coverRegion s h) (q : M) :
    ∑ a ∈ s, (refinedCutoff p ψ s h a q)^2 = (ψ q)^2 := by
  by_cases hq : ψ q = 0
  · simp [refinedCutoff,hq]
  · have hqc := hcover ⟨q,subset_closure hq,rfl⟩
    have hsum := normalizedCutoff_squares (s := s) (h := h) (x := chartCoordinates p q)
      (zero_lt_one.trans_le (squareSum_ge_one hh (coverRegion_covers s h hqc)))
    simp only [refinedCutoff,mul_pow,← Finset.mul_sum,hsum,mul_one]




omit [T2Space M] [CompactSpace M] in
theorem global_grid_square_partition {ι : Type*} [Fintype ι]
    (p : ι → M) (ψ : ι → M → ℝ) (hsmooth : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i))
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i))
    (hsquares : ∀ q, ∑ i, (ψ i q)^2 = 1)
    (s : ι → Finset Index) (h : ℝ) (hh : 0 < h)
    (hcover : ∀ i, chartSupport (p i) (ψ i) ⊆ coverRegion (s i) h) :
    (∀ i a, ContMDiff planeModel 𝓘(ℝ) ∞ (refinedCutoff (p i) (ψ i) (s i) h a)) ∧
    (∀ i a, HasCompactSupport (refinedCutoff (p i) (ψ i) (s i) h a)) ∧
    (∀ i a, tsupport (refinedCutoff (p i) (ψ i) (s i) h a) ⊆ tsupport (ψ i) ∩
      chartCoordinates (p i) ⁻¹' tsupport (normalizedCutoff (s i) h a)) ∧
    (∀ q, ∑ i, ∑ a ∈ s i, (refinedCutoff (p i) (ψ i) (s i) h a q)^2 = 1) := by
  refine ⟨fun i a => refinedCutoff_smooth (p i) (hsmooth i) (hsource i) hh (hcover i) a,
    fun i a => refinedCutoff_hasCompactSupport (p i) (ψ i) (s i) h a (hcompact i),?_,?_⟩
  · exact fun i a q hq => ⟨refinedCutoff_tsupport_outer (p i) (ψ i) (s i) h a hq,
      refinedCutoff_tsupport_inner (p i) (hsource i) (s i) h a hq⟩
  · intro q
    simp_rw [refinedCutoff_squares _ _ hh (hcover _) q]
    exact hsquares q

end ClosedSurfaceR4

end

end OAI
