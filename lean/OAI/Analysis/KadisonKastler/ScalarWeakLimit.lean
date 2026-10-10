import OAI.Analysis.KadisonKastler.ScalarBoundaryMean
import OAI.Analysis.KadisonKastler.WeakHilbertConvexLimit

namespace OAI

/-! # Bounded scalar weak limits

Uniformly bounded scalar functions have simultaneous weak L2 cluster points
on a probability space. Closed convex disk constraints retain the essential
bound, so the limits are actual L-infinity classes.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

def scalarInfinityToL2 (f : ScalarLInfinity μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).mono_exponent le_top).toLp f

theorem scalarInfinityToL2_ae (f : ScalarLInfinity μ) :
    scalarInfinityToL2 f =ᵐ[μ] f := MemLp.coeFn_toLp _

theorem norm_scalarInfinityToL2_le (f : ScalarLInfinity μ) :
    ‖scalarInfinityToL2 f‖ ≤ ‖f‖ := by
  have ha : ∀ᵐ x ∂μ, ‖scalarInfinityToL2 f x‖ ≤ ‖f‖ := by
    filter_upwards [scalarInfinityToL2_ae f, scalarInfinity_ae_norm_le f] with x hx hf
    rwa [hx]
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (norm_nonneg f) ha

theorem scalarInfinityToL2_injective :
    Function.Injective (scalarInfinityToL2 (μ := μ)) := by
  intro f g hfg
  apply Lp.ext
  have hf := scalarInfinityToL2_ae f
  rw [hfg] at hf
  exact hf.symm.trans (scalarInfinityToL2_ae g)

theorem scalarInfinityToL2_add (f g : ScalarLInfinity μ) :
    scalarInfinityToL2 (f + g) = scalarInfinityToL2 f + scalarInfinityToL2 g := by
  apply Lp.ext
  filter_upwards [scalarInfinityToL2_ae (f + g), scalarInfinityToL2_ae f,
    scalarInfinityToL2_ae g, Lp.coeFn_add f g,
    Lp.coeFn_add (scalarInfinityToL2 f) (scalarInfinityToL2 g)] with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, hd, he, hb, hc]

theorem scalarInfinityToL2_smul (c : ℂ) (f : ScalarLInfinity μ) :
    scalarInfinityToL2 (c • f) = c • scalarInfinityToL2 f := by
  apply Lp.ext
  filter_upwards [scalarInfinityToL2_ae (c • f), scalarInfinityToL2_ae f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (scalarInfinityToL2 f)] with x ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hc, hd, hb]

def scalarInfinityToL2L : ScalarLInfinity μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := scalarInfinityToL2
      map_add' := scalarInfinityToL2_add
      map_smul' := scalarInfinityToL2_smul }
    1 (fun f => by simpa using norm_scalarInfinityToL2_le f)

@[simp]
theorem scalarInfinityToL2L_apply (f : ScalarLInfinity μ) :
    scalarInfinityToL2L f = scalarInfinityToL2 f := rfl

theorem exists_scalar_weak_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (f : ι → ScalarLInfinity μ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ∃ g : ScalarLInfinity μ, ‖g‖ ≤ C ∧ ∀ y : Lp ℂ 2 μ,
      Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (f i))) (ω : Filter ι)
        (𝓝 (inner ℂ y (scalarInfinityToL2 g))) := by
  obtain ⟨z, _, ht⟩ := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => scalarInfinityToL2 (f i)) C
    (fun i => (norm_scalarInfinityToL2_le (f i)).trans (hf i))
  have hz : ∀ᵐ x ∂μ, ‖z x‖ ≤ C := by
    have hb (i : ι) : ∀ᵐ x ∂μ, scalarInfinityToL2 (f i) x ∈ Metric.closedBall (0 : ℂ) C := by
      filter_upwards [scalarInfinityToL2_ae (f i), scalarInfinity_ae_norm_le (f i)] with x hx hn
      simpa only [Metric.mem_closedBall, dist_zero_right, hx] using hn.trans (hf i)
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      L2_ae_mem_of_inner_tendsto Metric.isClosed_closedBall (convex_closedBall (0 : ℂ) C)
        (fun i => scalarInfinityToL2 (f i)) z hb ht
  let g : ScalarLInfinity μ := (memLp_top_of_bound (Lp.aestronglyMeasurable z) C hz).toLp z
  have hg : g =ᵐ[μ] z := MemLp.coeFn_toLp _
  have he : scalarInfinityToL2 g = z := Lp.ext ((scalarInfinityToL2_ae g).trans hg)
  refine ⟨g, ?_, ?_⟩
  · have hbg : ∀ᵐ x ∂μ, ‖g x‖ ≤ C := by
      filter_upwards [hg, hz] with x hx hb
      rwa [hx]
    simpa using Lp.norm_le_of_ae_bound hC hbg
  · simpa only [he] using ht

/-- One ultrafilter gives a simultaneous linear, contractive scalar limit. -/
theorem exists_scalar_linear_weak_ultralimit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (ω : Ultrafilter ι) (A : ι → E →L[ℂ] ScalarLInfinity μ)
    (hA : ∀ i x, ‖A i x‖ ≤ ‖x‖) :
    ∃ B : E →L[ℂ] ScalarLInfinity μ, (∀ x, ‖B x‖ ≤ ‖x‖) ∧
      ∀ x y, Tendsto (fun i => inner ℂ y (scalarInfinityToL2 (A i x))) (ω : Filter ι)
        (𝓝 (inner ℂ y (scalarInfinityToL2 (B x)))) := by
  choose B hB ht using fun x : E =>
    exists_scalar_weak_ultralimit ω (fun i => A i x) ‖x‖ (norm_nonneg x) (fun i => hA i x)
  have hadd (x z : E) : B (x + z) = B x + B z := by
    apply scalarInfinityToL2_injective
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x + z) y)
    simpa only [map_add, scalarInfinityToL2_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : E) : B (c • x) = c • B x := by
    apply scalarInfinityToL2_injective
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, scalarInfinityToL2_smul, inner_smul_right] using (ht x y).const_mul c
  let L : E →L[ℂ] ScalarLInfinity μ := LinearMap.mkContinuous
    { toFun := B, map_add' := hadd, map_smul' := hsmul }
    1 (fun x => by simpa using hB x)
  exact ⟨L, hB, ht⟩

end

end KadisonKastler

end OAI
