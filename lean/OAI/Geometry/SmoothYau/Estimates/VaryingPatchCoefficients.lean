import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ChartDerivativeNeZeroTransfer

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
open Set Filter Function
open scoped ContDiff Topology Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

structure VaryingPatchCoefficients (q : SmoothMetric E M) (i : A.t) where
  a : CoordIndex E → CoordIndex E → E → ℝ
  c : CoordIndex E → E → ℝ
  smooth_a : ∀ j l, ContDiff ℝ ∞ (a j l)
  smooth_c : ∀ j, ContDiff ℝ ∞ (c j)
  eq_a : ∀ x ∈ tsupport (A.χcoord i), ∀ j l, a j l x = (metricCoefficients q (A.p i) x)⁻¹ j l
  eq_c : ∀ x ∈ tsupport (A.χcoord i), ∀ j, c j x = metricFirstCoefficient q (A.p i) j x

omit [T2Space M] in
lemma nonempty_varyingPatchCoefficients (q : SmoothMetric E M) (i : A.t) :
    Nonempty (A.VaryingPatchCoefficients q i) := by
  obtain ⟨a, c, ha, hc, he⟩ := exists_smooth_metric_coefficients_on_compact q (A.p i)
    (isCompact_closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius)
    (A.localInverse i).in_target
  exact ⟨⟨a, c, ha, hc, fun x hx => (he x (A.χcoord_support i hx)).1,
    fun x hx => (he x (A.χcoord_support i hx)).2⟩⟩
variable (q : SmoothMetric E M)

def varyingLaplacianPatch (i : A.t) (B : A.VaryingPatchCoefficients q i) :
    FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k ∘L
    (coefficientPerturbation (Module.finBasis ℝ E) hs
      (fun j l => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.a j l) (B.smooth_a j l)))
      (fun j => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.c j) (B.smooth_c j)))).restrictScalars ℝ

def varyingLaplacianCLM (B : ∀ i, A.VaryingPatchCoefficients q i) :
    A.H (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  ∑ i, A.varyingLaplacianPatch q i (B i) ∘L
    A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1)

omit [T2Space M] in
lemma varyingLaplacianPatch_representative (i : A.t) (B : A.VaryingPatchCoefficients q i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ))
      (A.varyingLaplacianPatch q i B (A.cutoffLocalization (A.p i) (A.χ i)
        (A.chart_χ i) (A.smooth_χ i) (k + 1) u)) x =
      A.η i x * complexLaplaceBeltrami q (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  have ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by push_cast; linarith
  have ht' : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2) := by linarith
  let w := A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1) u
  let v : M → ℂ := A.representative (2 * ((k + 1 : ℕ) : ℝ)) u
  change A.representative _ (A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k _) x = _
  rw [A.lift_representative _ _ _ _ k hs]
  by_cases hx : A.η i x = 0
  · simp only [hx, zero_mul]
  have hxs := A.chart_η i (subset_tsupport _ hx)
  have hys := (chartAt E (A.p i)).map_source hxs
  change A.η i x * sobolevRepresentative hs
    (coefficientPerturbation (Module.finBasis ℝ E) hs _ _ w) ((chartAt E (A.p i)) x) = _
  congr 1
  rw [coefficientPerturbation_representative (Module.finBasis ℝ E) hs ht']
  have hχ : A.χ i =ᶠ[𝓝 x] 1 := (A.one_χ i).filter_mono
    (nhds_le_nhdsSet (subset_tsupport _ hx))
  have hχx : A.χcoord i ((chartAt E (A.p i)) x) = 1 := by
    rw [χcoord, chartLocalize_eq _ _ _ hys, (chartAt E (A.p i)).left_inv hxs,
      Pi.one_apply, mul_one]
    exact hχ.eq_of_nhds
  have hc : (chartAt E (A.p i)) x ∈ tsupport (A.χcoord i) :=
    subset_tsupport _ (by change A.χcoord i ((chartAt E (A.p i)) x) ≠ 0; rw [hχx]; exact one_ne_zero)
  have hw : (sobolevRepresentative ht' w : E → ℂ) = chartLocalize (E := E) (A.p i) (A.χ i) v := by
    funext y
    rw [sobolevRepresentative_congr _ _ (by push_cast; ring) ht' ht]
    exact A.cutoffLocalization_representative _ _ _ _ (k + 1) ht u y
  simp only [sobolevRepresentative_schwartz, SchwartzMap.toBoundedContinuousFunction_apply]
  change (∑ j, ∑ l, (A.χcoord i ((chartAt E (A.p i)) x) *
      (B.a j l ((chartAt E (A.p i)) x) : ℂ)) * _) + ∑ j,
      (A.χcoord i ((chartAt E (A.p i)) x) * (B.c j ((chartAt E (A.p i)) x) : ℂ)) * _ = _
  simp only [hχx, one_mul, B.eq_a _ hc, B.eq_c _ hc]
  change euclideanElliptic (Module.finBasis ℝ E)
    (fun j l y => (metricCoefficients q (A.p i) y)⁻¹ j l)
    (metricFirstCoefficient q (A.p i)) (sobolevRepresentative ht' w) ((chartAt E (A.p i)) x) = _
  rw [hw, complexLaplaceBeltrami_inChart (A.representative_C2 u) q (A.p i) hxs]
  exact euclideanElliptic_congr _ _ _ (chartLocalize_eventually_eq _ _ _ hxs hχ)

omit [T2Space M] in
lemma varyingLaplacianCLM_representative (B : ∀ i, A.VaryingPatchCoefficients q i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ)) (A.varyingLaplacianCLM q B u) x =
      complexLaplaceBeltrami q (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [varyingLaplacianCLM, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, A.varyingLaplacianPatch_representative]
  rw [← Finset.sum_mul, A.sum_η, one_mul]

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
