import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RescaledCommutatorSobolev
import OAI.Geometry.SmoothYau.Geometry.ContMDiffComplexMul
import OAI.Geometry.SmoothYau.Geometry.MetricPatchSource
import OAI.Geometry.SmoothYau.Spectrum.ScalarCompDirectional

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
    (hηone : ∀ x, ∑ i, η i x = 1)

include hηone

theorem manifoldSobolevRepresentative_localize
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : ManifoldSobolev p η hηc hηs hηm s) (i : ι) (y : E) :
    sobolevRepresentative hs (u.val i) y = chartLocalize (E := E) (p i) (η i)
      (manifoldSobolevRepresentative p η hηc hηs hηm s u) y := by
  classical
  refine (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
        ((sobolevRepresentative hs).continuous.comp
          ((continuous_apply i).comp continuous_subtype_val))
    · unfold chartLocalize
      split_ifs <;> fun_prop
  · intro f
    rw [manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone hs]
    change sobolevRepresentative hs
      (schwartzToSobolev s (chartSchwartz (p i) (η i) f (hηc i) (hηs i) (hηm i) f.contMDiff)) y = _
    rw [sobolevRepresentative_schwartz]
    rfl

theorem manifoldSobolevRepresentative_injective
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) :
    Function.Injective (manifoldSobolevRepresentative p η hηc hηs hηm s) := by
  intro u v huv
  apply Subtype.ext
  funext i
  apply fourierSobolevDistribution_injective
  rw [← sobolevRepresentative_distribution hs, ← sobolevRepresentative_distribution hs]
  congr 1
  ext y
  simp only [manifoldSobolevRepresentative_localize p η hηc hηs hηm hηone hs, huv]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
variable (q : M) (χ : M → ℂ) (hχs : tsupport χ ⊆ (chartAt E q).source)
    (hχm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ)

def chartLiftSmoothLinear : 𝓢(E, ℂ) →ₗ[ℝ] ManifoldSmoothFunctions E M where
  toFun f := ⟨chartLift q χ f, contMDiff_chartLift q χ hχs hχm (f.smooth ⊤)⟩
  map_add' f g := by
    ext x
    change χ x * (f (chartAt E q x) + g (chartAt E q x)) =
      χ x * f (chartAt E q x) + χ x * g (chartAt E q x)
    exact mul_add _ _ _
  map_smul' c f := by
    ext x
    change χ x * ((c : ℂ) * f (chartAt E q x)) = (c : ℂ) * (χ x * f (chartAt E q x))
    ring

def chartLiftToManifoldSobolev (s : ℝ) : 𝓢(E, ℂ) →ₗ[ℝ]
    ManifoldSobolev p η hηc hηs hηm s :=
  (smoothToManifoldSobolev p η hηc hηs hηm s).comp (chartLiftSmoothLinear q χ hχs hχm)

omit [CompactSpace M] in
lemma chartLiftToManifoldSobolev_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(E, ℂ),
      ‖chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ)) f‖ ≤
        C * ‖schwartzToSobolev (2 * (k : ℝ)) f‖ := by
  classical
  choose C hC hb using fun i => chartLift_localization_bound
    (p i) q (η i) χ (hηc i) (hηs i) (hηm i) hχs hχm k
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => (hC i).le), fun f => ?_⟩
  change ‖(chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ)) f).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => (hC i).le)) (norm_nonneg _))).mpr
  intro i
  exact (hb i f).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)) (norm_nonneg _))

def sobolevChartLift (k : ℕ) : FourierSobolevSpace E ℂ (2 * (k : ℝ)) →L[ℝ]
    ManifoldSobolev p η hηc hηs hηm (2 * (k : ℝ)) :=
  (chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ))).extendOfNorm
    ((schwartzToSobolev (2 * (k : ℝ))).restrictScalars ℝ).toLinearMap

omit [CompactSpace M] in
lemma sobolevChartLift_schwartz (k : ℕ) (f : 𝓢(E, ℂ)) :
    sobolevChartLift p η hηc hηs hηm q χ hχs hχm k (schwartzToSobolev (2 * (k : ℝ)) f) =
      smoothToManifoldSobolev p η hηc hηs hηm (2 * (k : ℝ))
        (chartLiftSmoothLinear q χ hχs hχm f) := by
  obtain ⟨C, _, hC⟩ := chartLiftToManifoldSobolev_bound p η hηc hηs hηm q χ hχs hχm k
  exact LinearMap.extendOfNorm_eq
    (f := chartLiftToManifoldSobolev p η hηc hηs hηm q χ hχs hχm (2 * (k : ℝ)))
    (e := ((schwartzToSobolev (2 * (k : ℝ))).restrictScalars ℝ).toLinearMap)
    (denseRange_schwartzToSobolev (E := E) (2 * (k : ℝ))) ⟨C, hC⟩ f

lemma sobolevChartLift_representative (hηone : ∀ x, ∑ i, η i x = 1)
    (k : ℕ) (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ)))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ))) (x : M) :
    manifoldSobolevRepresentative p η hηc hηs hηm (2 * (k : ℝ))
      (sobolevChartLift p η hηc hηs hηm q χ hχs hχm k u) x =
      χ x * sobolevRepresentative hs u (chartAt E q x) := by
  refine (denseRange_schwartzToSobolev (E := E) (2 * (k : ℝ))).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp
        ((manifoldSobolevRepresentative p η hηc hηs hηm (2 * (k : ℝ))).continuous.comp
          (sobolevChartLift p η hηc hηs hηm q χ hχs hχm k).continuous)
    · exact continuous_const.mul ((BoundedContinuousFunction.evalCLM ℂ (chartAt E q x)).continuous.comp
        (sobolevRepresentative hs).continuous)
  · intro f
    rw [sobolevChartLift_schwartz, manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone hs,
      sobolevRepresentative_schwartz]
    rfl


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open scoped SchwartzMap ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
    (χ : ι → M → ℂ) (hχs : ∀ i, tsupport (χ i) ⊆ (chartAt E (p i)).source)
    (hχm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i))

def atlasSobolevGluing (k : ℕ) : (ι → FourierSobolevSpace E ℂ (2 * (k : ℝ))) →L[ℝ]
    ManifoldSobolev p η hηc hηs hηm (2 * (k : ℝ)) :=
  ∑ i, (sobolevChartLift p η hηc hηs hηm (p i) (χ i) (hχs i) (hχm i) k).comp
    (ContinuousLinearMap.proj i)

include hηs hχs in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) ∞ M] [Fintype ι] in
lemma chartLift_chartLocalize_buffer (i : ι) (hχone : EqOn (χ i) 1 (tsupport (η i)))
    (f : M → ℂ) (x : M) :
    chartLift (E := E) (p i) (χ i) (chartLocalize (E := E) (p i) (η i) f) x = η i x * f x := by
  change χ i x * chartLocalize (E := E) (p i) (η i) f (chartAt E (p i) x) = _
  by_cases hx : x ∈ (chartAt E (p i)).source
  · rw [chartLocalize_eq _ _ _ ((chartAt E (p i)).map_source hx), (chartAt E (p i)).left_inv hx]
    by_cases hηx : η i x = 0
    · simp [hηx]
    · rw [hχone (subset_tsupport _ hηx)]
      simp
  · have ha : η i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hηs i h))
    have hb : χ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχs i h))
    simp [ha, hb]

include hηs hχs in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma atlasGluing_partition_identity (hηone : ∀ x, ∑ i, η i x = 1)
    (hχone : ∀ i, EqOn (χ i) 1 (tsupport (η i))) (f : M → ℂ) (x : M) :
    ∑ i, chartLift (E := E) (p i) (χ i) (chartLocalize (E := E) (p i) (η i) f) x = f x := by
  simp only [chartLift_chartLocalize_buffer p η hηs χ hχs _ (hχone _) f x]
  rw [← Finset.sum_mul, hηone x, one_mul]

theorem atlasSobolevGluing_leftInverse (hηone : ∀ x, ∑ i, η i x = 1)
    (hχone : ∀ i, EqOn (χ i) 1 (tsupport (η i))) (k : ℕ)
    (u : ManifoldSobolev p η hηc hηs hηm (2 * (k : ℝ))) :
    atlasSobolevGluing p η hηc hηs hηm χ hχs hχm k u.val = u := by
  refine (denseRange_smoothToManifoldSobolev p η hηc hηs hηm (2 * (k : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq ((atlasSobolevGluing p η hηc hηs hηm χ hχs hχm k).continuous.comp
      continuous_subtype_val) continuous_id
  · intro f
    change (∑ i, (sobolevChartLift p η hηc hηs hηm (p i) (χ i) (hχs i) (hχm i) k).comp
      (ContinuousLinearMap.proj i)) (atlasSobolevLocalization p η hηc hηs hηm (2 * (k : ℝ)) f) = _
    simp only [sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    change (∑ i, sobolevChartLift p η hηc hηs hηm (p i) (χ i) (hχs i) (hχm i) k
      (schwartzToSobolev (2 * (k : ℝ)) (chartSchwartzLinear (p i) (η i) (hηc i) (hηs i) (hηm i) f))) = _
    simp only [sobolevChartLift_schwartz]
    rw [← map_sum]
    congr 1
    ext x
    simp only [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    change (∑ i, chartLift (E := E) (p i) (χ i) (chartLocalize (E := E) (p i) (η i) f) x) = f x
    exact atlasGluing_partition_identity p η hηs χ hχs hηone hχone f x


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
open MeasureTheory Set
open scoped ENNReal NNReal
open Function
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
  {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))
    (χ : ι → M → ℂ) (hχs : ∀ i, tsupport (χ i) ⊆ (chartAt E (p i)).source)
    (hχm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompactSpace M]
  [Fintype ι] in
lemma contMDiff_chartLift_finite (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (N : ℕ)
    {f : E → ℂ} (hf : ContDiff ℝ N f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) N (chartLift (E := E) q ξ f) := by
  have hN : (N : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl N
  apply contMDiff_of_tsupport
  intro x hx
  have hxs : x ∈ (chartAt E q).source := hξs (tsupport_mul_subset_left hx)
  exact ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.contMDiffAt.comp x
    (hξ.of_le hN).contMDiffAt).clm_apply
    ((contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
      ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hxs).of_le hN))

include hηs hχs in
lemma manifoldSobolevRepresentative_eq_sum
    (hηone : ∀ x, ∑ i, η i x = 1) (hχone : ∀ i, EqOn (χ i) 1 (tsupport (η i)))
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (u : ManifoldSobolev p η hηc hηs hηm s) (x : M) :
    manifoldSobolevRepresentative p η hηc hηs hηm s u x =
      ∑ i, chartLift (E := E) (p i) (χ i) (sobolevRepresentative hs (u.val i)) x := by
  have he (i : ι) : (sobolevRepresentative hs (u.val i) : E → ℂ) =
      chartLocalize (E := E) (p i) (η i)
        (manifoldSobolevRepresentative p η hηc hηs hηm s u) := by
    funext y
    exact manifoldSobolevRepresentative_localize p η hηc hηs hηm hηone hs u i y
  simp only [he]
  exact (atlasGluing_partition_identity p η hηs χ hχs hηone hχone _ x).symm

include hχs hχm in

theorem contMDiff_manifoldSobolevRepresentative
    (hηone : ∀ x, ∑ i, η i x = 1) (hχone : ∀ i, EqOn (χ i) 1 (tsupport (η i)))
    {s : ℝ} (N : ℕ) (hs : Module.finrank ℝ E < 2 * (s - N))
    (u : ManifoldSobolev p η hηc hηs hηm s) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) N
      (manifoldSobolevRepresentative p η hηc hηs hηm s u : M → ℂ) := by
  have ht : Module.finrank ℝ E < 2 * s := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have he : (manifoldSobolevRepresentative p η hηc hηs hηm s u : M → ℂ) =
      fun x => ∑ i, chartLift (E := E) (p i) (χ i) (sobolevRepresentative ht (u.val i)) x := by
    funext x
    exact manifoldSobolevRepresentative_eq_sum p η hηc hηs hηm χ hχs hηone hχone ht u x
  rw [he]
  apply ContMDiff.sum
  intro i _
  exact contMDiff_chartLift_finite (p i) (χ i) (hχs i) (hχm i) N
    (contDiff_sobolevRepresentative N hs ht (u.val i))



end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

structure CompactMetricAtlas (g : SmoothMetric E M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))) where
  t : Finset M
  localInverse : ∀ i : t, LocalMetricInverse g (i : M) (2 * (k : ℝ)) hs
  η : t → M → ℂ
  χ : t → M → ℂ
  ψ : t → M → ℂ
  smooth_η : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i)
  sum_η : ∀ x, ∑ i, η i x = 1
  support_η : ∀ i, tsupport (η i) ⊆ metricInversePatch (localInverse i)
  smooth_χ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (χ i)
  support_χ : ∀ i, tsupport (χ i) ⊆ metricInversePatch (localInverse i)
  one_χ : ∀ i, χ i =ᶠ[𝓝ˢ (tsupport (η i))] 1
  smooth_ψ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (ψ i)
  support_ψ : ∀ i, tsupport (ψ i) ⊆ metricInversePatch (localInverse i)
  one_ψ : ∀ i, ψ i =ᶠ[𝓝ˢ (tsupport (χ i))] 1

theorem nonempty_compactMetricAtlas (g : SmoothMetric E M) (k : ℕ)
    (hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))) :
    Nonempty (CompactMetricAtlas g k hs) := by
  obtain ⟨t, D, η, χ, ψ, hηm, hηone, hηs, hχm, hχs, hχη, hψm, hψs, hψχ⟩ :=
    exists_compact_metric_patches g hs
  exact ⟨⟨t, D, η, χ, ψ, hηm, hηone, hηs, hχm, hχs, hχη, hψm, hψs, hψχ⟩⟩

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

abbrev p (i : A.t) : M := i
omit [T2Space M] [CompactSpace M] in
lemma chart_η (i : A.t) : tsupport (A.η i) ⊆ (chartAt E (A.p i)).source :=
  fun _ h => (A.support_η i h).1
omit [T2Space M] [CompactSpace M] in
lemma chart_χ (i : A.t) : tsupport (A.χ i) ⊆ (chartAt E (A.p i)).source :=
  fun _ h => (A.support_χ i h).1
omit [T2Space M] [CompactSpace M] in
lemma chart_ψ (i : A.t) : tsupport (A.ψ i) ⊆ (chartAt E (A.p i)).source :=
  fun _ h => (A.support_ψ i h).1

abbrev H (s : ℝ) := ManifoldSobolev A.p A.η
  (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η s

def representative (s : ℝ) : A.H s →L[ℝ] M →ᵇ ℂ :=
  manifoldSobolevRepresentative A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η s

def lift (q : M) (ξ : M → ℂ) (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    FourierSobolevSpace E ℂ (2 * (l : ℝ)) →L[ℝ] A.H (2 * (l : ℝ)) :=
  sobolevChartLift A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
    A.chart_η A.smooth_η q ξ hξs hξ l

omit [T2Space M] in
lemma lift_representative (q : M) (ξ : M → ℂ) (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ)
    (hl : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f : FourierSobolevSpace E ℂ (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.lift q ξ hξs hξ l f) x =
      ξ x * sobolevRepresentative hl f ((chartAt E q) x) :=
  sobolevChartLift_representative A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    q ξ hξs hξ A.sum_η l hl f x

def χcoord (i : A.t) : E → ℂ := chartLocalize (E := E) (A.p i) (A.χ i) 1
omit [T2Space M] in
lemma compact_χcoord (i : A.t) : HasCompactSupport (A.χcoord i) :=
  hasCompactSupport_chartLocalize (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i)
omit [T2Space M] in
lemma smooth_χcoord (i : A.t) : ContDiff ℝ ∞ (A.χcoord i) :=
  contDiff_chartLocalize (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i) (A.smooth_χ i) contMDiff_const

omit [T2Space M] [CompactSpace M] in
lemma ψ_mul_χ (i : A.t) (x : M) : A.ψ i x * A.χ i x = A.χ i x := by
  by_cases hx : A.χ i x = 0
  · simp only [hx, mul_zero]
  · rw [(A.one_ψ i).self_of_nhdsSet (subset_tsupport _ hx), Pi.one_apply, one_mul]

def localize (s : ℝ) (i : A.t) : A.H s →L[ℝ] FourierSobolevSpace E ℂ s :=
  (ContinuousLinearMap.proj i) ∘L
    (manifoldSobolevSubmodule A.p A.η (fun j => HasCompactSupport.of_compactSpace (A.η j))
      A.chart_η A.smooth_η s).subtypeL

def patchParametrix (α : ℝ) (i : A.t) (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  A.lift (A.p i) (A.ψ i) (A.chart_ψ i) (A.smooth_ψ i) (k + 1) ∘L
    (sobolevAffineCutoff (A.χcoord i) (A.compact_χcoord i) (A.smooth_χcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ (k + 1)).restrictScalars ℝ ∘L
    (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα).restrictScalars ℝ ∘L
    A.localize (2 * (k : ℝ)) i

omit [T2Space M] in
lemma patchParametrix_representative (α : ℝ) (i : A.t)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)))
    (u : A.H (2 * (k : ℝ))) (x : M) :
    A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i hα u) x =
      A.χ i x * sobolevRepresentative ht
        (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i))
        ((A.localInverse i).radius⁻¹ • ((chartAt E (A.p i)) x - (chartAt E (A.p i)) (A.p i))) := by
  simp only [patchParametrix, ContinuousLinearMap.comp_apply]
  rw [A.lift_representative _ _ _ _ (k + 1) ht]
  change A.ψ i x * sobolevRepresentative ht
    (sobolevAffineCutoff (A.χcoord i) (A.compact_χcoord i) (A.smooth_χcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ (k + 1)
      (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i)))
    ((chartAt E (A.p i)) x) = _
  rw [sobolevAffineCutoff_representative _ _ _ _
    (inv_ne_zero (A.localInverse i).radius_pos.ne') (k + 1) ht]
  have he : -((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)) +
      (A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) x =
      (A.localInverse i).radius⁻¹ • ((chartAt E (A.p i)) x - (chartAt E (A.p i)) (A.p i)) := by
    rw [smul_sub, sub_eq_add_neg, add_comm]
  rw [he]
  change A.ψ i x * (A.χcoord i ((chartAt E (A.p i)) x) * _) = _
  by_cases hx : x ∈ (chartAt E (A.p i)).source
  · rw [χcoord, chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
      (chartAt E (A.p i)).left_inv hx, Pi.one_apply, mul_one, ← mul_assoc, A.ψ_mul_χ]
  · have hψ : A.ψ i x = 0 := notMem_support.mp (fun h => hx (A.chart_ψ i (subset_tsupport _ h)))
    have hχ : A.χ i x = 0 := notMem_support.mp (fun h => hx (A.chart_χ i (subset_tsupport _ h)))
    simp only [hψ, hχ, zero_mul]
end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def ψcoord (i : A.t) : E → ℂ := chartLocalize (E := E) (A.p i) (A.ψ i) 1
omit [T2Space M] in
lemma compact_ψcoord (i : A.t) : HasCompactSupport (A.ψcoord i) :=
  hasCompactSupport_chartLocalize (A.p i) (A.ψ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_ψ i)
omit [T2Space M] in
lemma smooth_ψcoord (i : A.t) : ContDiff ℝ ∞ (A.ψcoord i) :=
  contDiff_chartLocalize (A.p i) (A.ψ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_ψ i) (A.smooth_ψ i) contMDiff_const

omit [T2Space M] in
lemma χcoord_support (i : A.t) : tsupport (A.χcoord i) ⊆
    Metric.closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := tsupport_chartLocalize_image (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i) hx
  exact Metric.closedBall_subset_closedBall (by linarith [(A.localInverse i).radius_pos])
    (Metric.ball_subset_closedBall (A.support_χ i hy).2)

omit [T2Space M] in
lemma χcoord_unit_support (i : A.t) {x : E} (hx : x ∈ tsupport (A.χcoord i)) :
    ‖(A.localInverse i).radius⁻¹ • (x - (chartAt E (A.p i)) (A.p i))‖ ≤ 1 := by
  have hh := A.χcoord_support i hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (A.localInverse i).radius_pos),
    inv_mul_le_iff₀ (A.localInverse i).radius_pos, mul_one]
  exact hh

omit [T2Space M] in
lemma χcoord_target (i : A.t) : tsupport (A.χcoord i) ⊆ (chartAt E (A.p i)).target :=
  (A.χcoord_support i).trans (A.localInverse i).in_target

structure PatchCoefficients (i : A.t) where
  a : CoordIndex E → CoordIndex E → E → ℝ
  c : CoordIndex E → E → ℝ
  smooth_a : ∀ j l, ContDiff ℝ ∞ (a j l)
  smooth_c : ∀ j, ContDiff ℝ ∞ (c j)
  eq_a : ∀ x ∈ tsupport (A.χcoord i), ∀ j l, a j l x = (metricCoefficients g (A.p i) x)⁻¹ j l
  eq_c : ∀ x ∈ tsupport (A.χcoord i), ∀ j, c j x = metricFirstCoefficient g (A.p i) j x

omit [T2Space M] in
lemma nonempty_patchCoefficients (i : A.t) : Nonempty (A.PatchCoefficients i) := by
  obtain ⟨a, c, ha, hc, he⟩ := exists_smooth_metric_coefficients_on_compact g (A.p i)
    (isCompact_closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius)
    (A.localInverse i).in_target
  exact ⟨⟨a, c, ha, hc, fun x hx => (he x (A.χcoord_support i hx)).1,
    fun x hx => (he x (A.χcoord_support i hx)).2⟩⟩

def patchErrorTail (i : A.t) (B : A.PatchCoefficients i) :
    FourierSobolevSpace E ℂ (2 * (k : ℝ) + 1) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.lift (A.p i) (A.ψ i) (A.chart_ψ i) (A.smooth_ψ i) k ∘L
    (sobolevAffineCutoff (A.ψcoord i) (A.compact_ψcoord i) (A.smooth_ψcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ k).restrictScalars ℝ ∘L
    (rescaledCommutatorSobolev hs (Module.finBasis ℝ E) B.a B.c B.smooth_a B.smooth_c
      (A.χcoord i) (A.smooth_χcoord i) (A.compact_χcoord i)
      ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius
      (A.localInverse i).radius_pos.ne').restrictScalars ℝ

def patchError (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.patchErrorTail i B ∘L
    (sobolevInclusion (2 * (k : ℝ) + 2) (2 * (k : ℝ) + 1) (by linarith)).restrictScalars ℝ ∘L
    (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα).restrictScalars ℝ ∘L
    A.localize (2 * (k : ℝ)) i

omit [T2Space M] in
lemma patchError_bound (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) (f : A.H (2 * (k : ℝ))) :
    ‖A.patchError α i B hα f‖ ≤
      (‖A.patchErrorTail i B‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
      (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹ * ‖f‖ := by
  have hf : ‖f.val i‖ ≤ ‖f‖ := norm_le_pi_norm f.val i
  apply ((A.patchErrorTail i B).le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_left
    (metricPatchRawInverse_half_bound g (A.p i) k hs (A.localInverse i) α hα (f.val i))
    (norm_nonneg _)).trans
  calc
    _ ≤ ‖A.patchErrorTail i B‖ *
        (((A.localInverse i).bound * ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) *
          (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹ * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf
        (mul_nonneg (mul_nonneg (A.localInverse i).bound_pos.le (norm_nonneg _))
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))) (norm_nonneg _)
    _ = _ := by ring
end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma localize_representative (u : A.H (2 * (k : ℝ))) (i : A.t) (y : E) :
    sobolevRepresentative hs (u.val i) y =
      chartLocalize (E := E) (A.p i) (A.η i) (A.representative (2 * (k : ℝ)) u) y :=
  manifoldSobolevRepresentative_localize A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η hs u i y

omit [T2Space M] [CompactSpace M] in
lemma χ_mul_η (i : A.t) (x : M) : A.χ i x * A.η i x = A.η i x := by
  by_cases hx : A.η i x = 0
  · simp only [hx, mul_zero]
  · rw [(A.one_χ i).self_of_nhdsSet (subset_tsupport _ hx), Pi.one_apply, one_mul]

omit [T2Space M] in
lemma ψ_one_on_χcoord (i : A.t) {x : M} (hx : x ∈ (chartAt E (A.p i)).source)
    (hc : (chartAt E (A.p i)) x ∈ tsupport (A.χcoord i)) : A.ψ i x = 1 := by
  obtain ⟨y, hy, he⟩ := tsupport_chartLocalize_image (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i) hc
  have hxy : y = x := (chartAt E (A.p i)).injOn (A.chart_χ i hy) hx he
  subst y
  exact (A.one_ψ i).self_of_nhdsSet hy

omit [T2Space M] in
lemma patchErrorTail_representative (i : A.t) (B : A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 1))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 1)) (x : M) :
    A.representative (2 * (k : ℝ)) (A.patchErrorTail i B u) x =
      A.ψ i x * (A.ψcoord i ((chartAt E (A.p i)) x) *
        ellipticCommutator (Module.finBasis ℝ E) B.a B.c (A.χcoord i)
          (fun y => sobolevRepresentative ht u
            ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i))))
          ((chartAt E (A.p i)) x)) := by
  simp only [patchErrorTail, ContinuousLinearMap.comp_apply]
  rw [A.lift_representative _ _ _ _ k hs]
  change A.ψ i x * sobolevRepresentative hs
    (sobolevAffineCutoff (A.ψcoord i) (A.compact_ψcoord i) (A.smooth_ψcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ k
      (rescaledCommutatorSobolev hs (Module.finBasis ℝ E) B.a B.c B.smooth_a B.smooth_c
        (A.χcoord i) (A.smooth_χcoord i) (A.compact_χcoord i)
        ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius
        (A.localInverse i).radius_pos.ne' u)) ((chartAt E (A.p i)) x) = _
  rw [sobolevAffineCutoff_representative _ _ _ _
    (inv_ne_zero (A.localInverse i).radius_pos.ne') k hs]
  have he : -((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)) +
      (A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) x =
      (A.localInverse i).radius⁻¹ • ((chartAt E (A.p i)) x - (chartAt E (A.p i)) (A.p i)) := by
    rw [smul_sub, sub_eq_add_neg, add_comm]
  rw [he, rescaledCommutatorSobolev_physical hs ht]

omit [T2Space M] in
lemma patchErrorTail_representative_inChart (i : A.t) (B : A.PatchCoefficients i)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 1))
    (u : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 1)) {x : M}
    (hx : x ∈ (chartAt E (A.p i)).source) :
    A.representative (2 * (k : ℝ)) (A.patchErrorTail i B u) x =
      ellipticCommutator (Module.finBasis ℝ E)
        (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
        (metricFirstCoefficient g (A.p i)) (A.χcoord i)
        (fun y => sobolevRepresentative ht u
          ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i))))
        ((chartAt E (A.p i)) x) := by
  rw [A.patchErrorTail_representative i B ht, ψcoord,
    chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
    (chartAt E (A.p i)).left_inv hx, Pi.one_apply, mul_one]
  rw [ellipticCommutator_congr_coeff _ B.a _ B.c _ _ _ B.eq_a B.eq_c]
  by_cases hh : (chartAt E (A.p i)) x ∈ tsupport (A.χcoord i)
  · rw [A.ψ_one_on_χcoord i hx hh, one_mul, one_mul]
  · have he := notMem_support.mp (mt (fun h => support_ellipticCommutator
      (Module.finBasis ℝ E) (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
      (metricFirstCoefficient g (A.p i)) (A.χcoord i)
      (fun y => sobolevRepresentative ht u
        ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i)))) h) hh)
    rw [he, mul_zero, mul_zero]

omit [T2Space M] in
lemma patchError_representative_inChart (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2)
    (ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2))
    (u : A.H (2 * (k : ℝ))) {x : M} (hx : x ∈ (chartAt E (A.p i)).source) :
    A.representative (2 * (k : ℝ)) (A.patchError α i B hα u) x =
      ellipticCommutator (Module.finBasis ℝ E)
        (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
        (metricFirstCoefficient g (A.p i)) (A.χcoord i)
        (fun y => sobolevRepresentative ht
          (metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i))
          ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i))))
        ((chartAt E (A.p i)) x) := by
  have h1 : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 1) := by linarith
  simp only [patchError, ContinuousLinearMap.comp_apply]
  rw [A.patchErrorTail_representative_inChart i B h1 _ hx]
  congr 2
  funext y
  exact congrArg (fun f : E →ᵇ ℂ => f _) (sobolevInclusion_representative _ _
    (by linarith : 2 * (k : ℝ) + 1 ≤ 2 * (k : ℝ) + 2) ht h1 _)

lemma patchParametrix_equation (α : ℝ) (i : A.t) (B : A.PatchCoefficients i)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2)
    (u : A.H (2 * (k : ℝ))) (x : M) :
    (α : ℂ) * A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i hα u) x -
      complexLaplaceBeltrami g
        (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i hα u)) x =
      A.η i x * A.representative (2 * (k : ℝ)) u x -
        A.representative (2 * (k : ℝ)) (A.patchError α i B hα u) x := by
  have ht : Module.finrank ℝ E < 2 * (2 * (k : ℝ) + 2) := by linarith
  have ht' : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_add, Nat.cast_one]; linarith
  let w := metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα (u.val i)
  let v : E → ℂ := fun y => sobolevRepresentative ht w
    ((A.localInverse i).radius⁻¹ • (y - (chartAt E (A.p i)) (A.p i)))
  have hv : ContDiff ℝ 2 v :=
    (contDiff_sobolevRepresentative 2 (by norm_num; linarith) ht w).comp (by fun_prop)
  have hQ : (A.representative (2 * ((k + 1 : ℕ) : ℝ))
      (A.patchParametrix α i hα u) : M → ℂ) = chartLift (E := E) (A.p i) (A.χ i) v := by
    funext y
    rw [A.patchParametrix_representative α i hα ht']
    rw [sobolevRepresentative_congr _ _ (by push_cast; ring) ht' ht]
    rfl
  rw [hQ]
  have hQm := contMDiff_chartLift_order (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) 2 hv
  by_cases hx : x ∈ (chartAt E (A.p i)).source
  · rw [complexLaplaceBeltrami_chartLift g (A.p i) (A.χ i) (A.chart_χ i)
      (A.smooth_χ i) hv hx, A.patchError_representative_inChart α i B hα ht u hx]
    have hcut := cutoff_parametrix_equation (Module.finBasis ℝ E)
      (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
      (metricFirstCoefficient g (A.p i)) ((A.smooth_χcoord i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hv α
      (sobolevRepresentative hs (u.val i))
      (fun y hy => metricPatchRawInverse_physical_equation g (A.p i) k hs
        (A.localInverse i) α hα ht (u.val i) y (A.χcoord_unit_support i (subset_tsupport _ hy)))
      ((chartAt E (A.p i)) x)
    have hc : A.χcoord i ((chartAt E (A.p i)) x) = A.χ i x := by
      rw [χcoord, chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
        (chartAt E (A.p i)).left_inv hx, Pi.one_apply, mul_one]
    rw [hc, A.localize_representative u i,
      chartLocalize_eq _ _ _ ((chartAt E (A.p i)).map_source hx),
      (chartAt E (A.p i)).left_inv hx] at hcut
    have hprod := congrArg (fun z : ℂ => z * A.representative (2 * (k : ℝ)) u x) (A.χ_mul_η i x)
    rw [mul_assoc] at hprod
    rw [hprod] at hcut
    exact hcut
  · have hψ : A.ψ i x = 0 := notMem_support.mp (fun h => hx (A.chart_ψ i (subset_tsupport _ h)))
    have hχ : x ∉ tsupport (A.χ i) := fun h => hx (A.chart_χ i h)
    have hη : A.η i x = 0 := notMem_support.mp (fun h => hx (A.chart_η i (subset_tsupport _ h)))
    have he : A.representative (2 * (k : ℝ)) (A.patchError α i B hα u) x = 0 := by
      simp only [patchError, ContinuousLinearMap.comp_apply]
      rw [A.patchErrorTail_representative i B (by linarith), hψ, zero_mul]
    have hzero : chartLift (E := E) (A.p i) (A.χ i) v =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hχ] with y hy
      simp only [chartLift, hy, Pi.zero_apply, zero_mul]
    have hzlap : complexLaplaceBeltrami g (chartLift (E := E) (A.p i) (A.χ i) v) x = 0 :=
      (complexLaplaceBeltrami_congr hQm (show ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 (0 : M → ℂ) from contMDiff_const) g hzero).trans (complexLaplaceBeltrami_zero g x)
    rw [hzlap, hzero.eq_of_nhds, Pi.zero_apply, mul_zero,
      sub_zero, hη, zero_mul, he, sub_zero]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def parametrix (α : ℝ) (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  ∑ i, A.patchParametrix α i (hα i)

def error (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  ∑ i, A.patchError α i (B i) (hα i)

def errorBound (B : ∀ i, A.PatchCoefficients i) (α : ℝ) : ℝ :=
  ∑ i, (‖A.patchErrorTail i (B i)‖ * ((A.localInverse i).bound *
    ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
    (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹

omit [T2Space M] in
lemma errorBound_nonneg (B : ∀ i, A.PatchCoefficients i) (α : ℝ) : 0 ≤ A.errorBound B α := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (A.patchErrorTail i (B i)).opNorm_nonneg (mul_nonneg (A.localInverse i).bound_pos.le
    (metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k).opNorm_nonneg)) (inv_nonneg.mpr (Real.sqrt_nonneg _))

omit [T2Space M] in
lemma error_norm_bound (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) :
    ‖A.error B α hα‖ ≤ A.errorBound B α := by
  apply ContinuousLinearMap.opNorm_le_bound _ (A.errorBound_nonneg B α)
  intro u
  calc
    ‖A.error B α hα u‖ ≤ ∑ i, ‖A.patchError α i (B i) (hα i) u‖ := by
      simpa only [error, sum_apply] using norm_sum_le _ _
    _ ≤ ∑ i, (‖A.patchErrorTail i (B i)‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
        (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹ * ‖u‖ :=
      Finset.sum_le_sum (fun i _ => A.patchError_bound α i (B i) (hα i) u)
    _ = A.errorBound B α * ‖u‖ := (Finset.sum_mul ..).symm

omit [T2Space M] in
lemma errorBound_tendsto (B : ∀ i, A.PatchCoefficients i) :
    Tendsto (A.errorBound B) atTop (𝓝 0) := by
  have hi (i : A.t) : Tendsto (fun α : ℝ =>
      (‖A.patchErrorTail i (B i)‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)) *
        (Real.sqrt (α * (A.localInverse i).radius ^ 2))⁻¹) atTop (𝓝 0) := by
    have hm : Tendsto (fun α : ℝ => α * (A.localInverse i).radius ^ 2) atTop atTop :=
      tendsto_id.atTop_mul_const (sq_pos_of_pos (A.localInverse i).radius_pos)
    simpa only [mul_zero, Function.comp_def] using! tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hm))
  simpa only [errorBound, Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun i _ => hi i)

omit [T2Space M] [CompactSpace M] in
lemma eventually_admissible : ∀ᶠ α : ℝ in atTop, ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2 := by
  apply Filter.eventually_all.mpr
  intro i
  exact (tendsto_id.atTop_mul_const (sq_pos_of_pos (A.localInverse i).radius_pos)).eventually
    (eventually_ge_atTop 1)

omit [T2Space M] in
lemma exists_parametrix_threshold (B : ∀ i, A.PatchCoefficients i) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ α ≥ a,
      (∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) ∧ A.errorBound B α ≤ 1 / 2 := by
  have he : ∀ᶠ α : ℝ in atTop, 1 ≤ α ∧
      (∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) ∧ A.errorBound B α ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), A.eventually_admissible,
      (A.errorBound_tendsto B).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with α hα ha he
    exact ⟨hα, ha, he.le⟩
  obtain ⟨a, ha⟩ := eventually_atTop.mp he
  exact ⟨a, (ha a le_rfl).1, fun α hα => (ha α hα).2⟩

omit [T2Space M] in
lemma representative_C2 (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2
      (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u : M → ℂ) := by
  apply contMDiff_manifoldSobolevRepresentative A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    A.χ A.chart_χ A.smooth_χ A.sum_η
    (fun i x hx => (A.one_χ i).self_of_nhdsSet hx) 2 _ u
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  linarith

lemma parametrix_equation (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (u : A.H (2 * (k : ℝ))) (x : M) :
    (α : ℂ) * A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.parametrix α hα u) x -
      complexLaplaceBeltrami g
        (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.parametrix α hα u)) x =
      A.representative (2 * (k : ℝ)) u x -
        A.representative (2 * (k : ℝ)) (A.error B α hα u) x := by
  have hq : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.parametrix α hα u) : M → ℂ) =
      fun y => ∑ i, A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.patchParametrix α i (hα i) u) y := by
    funext y
    simp only [parametrix, sum_apply, map_sum, BoundedContinuousFunction.sum_apply]
  rw [hq, complexLaplaceBeltrami_sum _ _
    (fun i _ => A.representative_C2 (A.patchParametrix α i (hα i) u)),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [A.patchParametrix_equation α _ (B _) (hα _) u x]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, A.sum_η, one_mul]
  simp only [error, sum_apply, map_sum, BoundedContinuousFunction.sum_apply]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def patchOutput (i : A.t) : FourierSobolevSpace E ℂ (2 * (k : ℝ) + 2) →L[ℝ]
    A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  A.lift (A.p i) (A.ψ i) (A.chart_ψ i) (A.smooth_ψ i) (k + 1) ∘L
    (sobolevAffineCutoff (A.χcoord i) (A.compact_χcoord i) (A.smooth_χcoord i)
      (-((A.localInverse i).radius⁻¹ • (chartAt E (A.p i)) (A.p i)))
      (A.localInverse i).radius⁻¹ (k + 1)).restrictScalars ℝ

def parametrixBound : ℝ := ∑ i,
  ‖A.patchOutput i‖ * ((A.localInverse i).bound *
    ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖)

omit [T2Space M] in
lemma parametrixBound_nonneg : 0 ≤ A.parametrixBound := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (A.patchOutput i).opNorm_nonneg (mul_nonneg (A.localInverse i).bound_pos.le
    (metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k).opNorm_nonneg)

omit [T2Space M] in
lemma patchParametrix_bound (α : ℝ) (i : A.t)
    (hα : 1 ≤ α * (A.localInverse i).radius ^ 2) (u : A.H (2 * (k : ℝ))) :
    ‖A.patchParametrix α i hα u‖ ≤
      ‖A.patchOutput i‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) * ‖u‖ := by
  let R := metricPatchRawInverse g (A.p i) k hs (A.localInverse i) α hα
  have hR : ‖R‖ ≤ (A.localInverse i).bound *
      ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right ((A.localInverse i).norm_bound _ hα)
        (metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k).opNorm_nonneg)
  change ‖A.patchOutput i (R (u.val i))‖ ≤ _
  calc
    _ ≤ ‖A.patchOutput i‖ * (‖R‖ * ‖u.val i‖) :=
      ((A.patchOutput i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (R.le_opNorm _) (A.patchOutput i).opNorm_nonneg)
    _ ≤ ‖A.patchOutput i‖ * (((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (A.patchOutput i).opNorm_nonneg
      exact mul_le_mul hR (norm_le_pi_norm u.val i) (norm_nonneg _) (R.opNorm_nonneg.trans hR)
    _ = _ := by ring

omit [T2Space M] in
lemma parametrix_bound (α : ℝ) (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (u : A.H (2 * (k : ℝ))) : ‖A.parametrix α hα u‖ ≤ A.parametrixBound * ‖u‖ := by
  calc
    _ ≤ ∑ i, ‖A.patchParametrix α i (hα i) u‖ := by
      simpa only [parametrix, sum_apply] using norm_sum_le _ _
    _ ≤ ∑ i, ‖A.patchOutput i‖ * ((A.localInverse i).bound *
        ‖metricPatchSource (E := E) (A.p i) (A.localInverse i).radius k‖) * ‖u‖ :=
      Finset.sum_le_sum (fun i _ => A.patchParametrix_bound α i (hα i) u)
    _ = _ := (Finset.sum_mul ..).symm

omit [T2Space M] in
lemma error_lt_one (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) :
    ‖ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ))) ∘L A.error B α hα‖ < 1 := by
  rw [ContinuousLinearMap.id_comp]
  exact lt_of_le_of_lt ((A.error_norm_bound B α hα).trans he) (by norm_num)

def resolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) :
    A.H (2 * (k : ℝ)) →L[ℝ] A.H (2 * ((k + 1 : ℕ) : ℝ)) :=
  A.parametrix α hα ∘L neumannCorrectedInverse
    (ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ)))) (A.error B α hα) (A.error_lt_one B α hα he)

omit [T2Space M] in
lemma resolvent_bound (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.H (2 * (k : ℝ))) :
    ‖A.resolvent B α hα he u‖ ≤ 2 * A.parametrixBound * ‖u‖ := by
  have hN := neumannCorrectedInverse_bound
    (ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ)))) (A.error B α hα)
    (A.error_lt_one B α hα he) 1 ContinuousLinearMap.norm_id_le
    (by simpa only [one_mul] using (A.error_norm_bound B α hα).trans he) u
  apply (A.parametrix_bound α hα _).trans
  calc
    _ ≤ A.parametrixBound * (2 * 1 * ‖u‖) := mul_le_mul_of_nonneg_left hN A.parametrixBound_nonneg
    _ = _ := by ring

lemma resolvent_equation (B : ∀ i, A.PatchCoefficients i) (α : ℝ)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.H (2 * (k : ℝ))) (x : M) :
    (α : ℂ) * A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.resolvent B α hα he u) x -
      complexLaplaceBeltrami g
        (A.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.resolvent B α hα he u)) x =
      A.representative (2 * (k : ℝ)) u x := by
  rw [resolvent, ContinuousLinearMap.comp_apply, A.parametrix_equation]
  have hn := neumannCorrectedInverse_fixed
    (ContinuousLinearMap.id ℝ (A.H (2 * (k : ℝ)))) (A.error B α hα)
    (A.error_lt_one B α hα he) u
  have hh := congrArg (fun v : A.H (2 * (k : ℝ)) => A.representative (2 * (k : ℝ)) v x) hn
  simp only [ContinuousLinearMap.id_apply, map_add, BoundedContinuousFunction.add_apply] at hh
  exact sub_eq_iff_eq_add.mpr hh

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma complexLaplaceBeltrami_sub {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v) (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (u - v) x =
      complexLaplaceBeltrami g u x - complexLaplaceBeltrami g v x := by
  have hh : u - v = fun y => u y + (-1 : ℂ) * v y := by funext y; simp [sub_eq_add_neg]
  rw [hh, complexLaplaceBeltrami_add hu (contMDiff_const_mul_complex hv (-1)),
    complexLaplaceBeltrami_const_mul hv]
  simp [sub_eq_add_neg]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] in
lemma complex_positive_shift_solution_unique (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v)
    (he : ∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x =
      (α : ℂ) * v x - complexLaplaceBeltrami g v x) : u = v := by
  apply sub_eq_zero.mp
  apply complex_positive_shift_kernel_eq_zero g hα (hu.sub hv)
  intro x
  change (α : ℂ) * (u - v) x - complexLaplaceBeltrami g (u - v) x = 0
  rw [complexLaplaceBeltrami_sub hu hv, Pi.sub_apply, mul_sub]
  have h := he x
  linear_combination h

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def transfer {l : ℕ} {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))}
    (B : CompactMetricAtlas g l ht) (n : ℕ) :
    A.H (2 * (n : ℝ)) →L[ℝ] B.H (2 * (n : ℝ)) :=
  ∑ i, B.lift (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) n ∘L
    A.localize (2 * (n : ℝ)) i

omit [T2Space M] in
lemma transfer_representative {l : ℕ} {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))}
    (B : CompactMetricAtlas g l ht) (n : ℕ)
    (hn : Module.finrank ℝ E < 2 * (2 * (n : ℝ))) (u : A.H (2 * (n : ℝ))) :
    B.representative (2 * (n : ℝ)) (A.transfer B n u) =
      A.representative (2 * (n : ℝ)) u := by
  ext x
  simp only [transfer, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, B.lift_representative _ _ _ _ n hn]
  exact (manifoldSobolevRepresentative_eq_sum A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    A.χ A.chart_χ A.sum_η (fun i y hy => (A.one_χ i).self_of_nhdsSet hy) hn u x).symm

def ofSmooth (s : ℝ) (f : ManifoldSmoothFunctions E M) : A.H s :=
  smoothToManifoldSobolev A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
    A.chart_η A.smooth_η s f

omit [T2Space M] in
lemma ofSmooth_representative (s : ℝ) (ht : Module.finrank ℝ E < 2 * s)
    (f : ManifoldSmoothFunctions E M) :
    (A.representative s (A.ofSmooth s f) : M → ℂ) = f := by
  exact congrArg (fun z : M →ᵇ ℂ => (z : M → ℂ))
    (manifoldSobolevRepresentative_smooth A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η ht f)

theorem regularity_step (α : ℝ) (f : ManifoldSmoothFunctions E M) {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x = f x)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = u)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ))) :
    ∃ (B : CompactMetricAtlas g (k + 1) ht)
      (w : B.H (2 * ((k + 1 + 1 : ℕ) : ℝ))),
      (B.representative (2 * ((k + 1 + 1 : ℕ) : ℝ)) w : M → ℂ) = u := by
  let B := (nonempty_compactMetricAtlas g (k + 1) ht).some
  let C : ∀ i, B.PatchCoefficients i := fun i => (B.nonempty_patchCoefficients i).some
  obtain ⟨β, hβ, ha⟩ := B.exists_parametrix_threshold C
  obtain ⟨hb, hc⟩ := ha β le_rfl
  let F := B.ofSmooth (2 * ((k + 1 : ℕ) : ℝ)) f + (β - α) • A.transfer B (k + 1) v
  let w := B.resolvent C β hb hc F
  refine ⟨B, w, ?_⟩
  apply complex_positive_shift_solution_unique g (by linarith : 0 < β) (B.representative_C2 w) hu
  intro x
  rw [B.resolvent_equation]
  have hF : B.representative (2 * ((k + 1 : ℕ) : ℝ)) F x = f x + ((β - α : ℝ) : ℂ) * u x := by
    simp only [F, map_add, map_smul, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, Complex.real_smul, A.transfer_representative B (k + 1) ht]
    rw [congrFun (B.ofSmooth_representative _ ht f) x, congrFun hv x]
  rw [hF]
  have hx := he x
  push_cast
  linear_combination -hx

theorem represented_solution_smooth (α : ℝ) (f : ManifoldSmoothFunctions E M)
    {u : M → ℂ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x = f x)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = u) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u := by
  have hkn (n : ℕ) : Module.finrank ℝ E < 2 * (2 * ((k + n : ℕ) : ℝ)) := by
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hrep (n : ℕ) : ∃ (B : CompactMetricAtlas g (k + n) (hkn n))
      (w : B.H (2 * ((k + n + 1 : ℕ) : ℝ))),
      (B.representative (2 * ((k + n + 1 : ℕ) : ℝ)) w : M → ℂ) = u := by
    induction n with
    | zero =>
      simp only [Nat.add_zero]
      exact ⟨A, v, hv⟩
    | succ n ih =>
      obtain ⟨B, w, hw⟩ := ih
      have ht : Module.finrank ℝ E < 2 * (2 * ((k + n + 1 : ℕ) : ℝ)) := by
        simpa only [Nat.add_assoc] using hkn (n + 1)
      convert B.regularity_step α f hu he w hw ht using 1
  apply contMDiff_infty.mpr
  intro N
  obtain ⟨B, w, hw⟩ := hrep (N + 1)
  rw [← hw]
  apply contMDiff_manifoldSobolevRepresentative B.p B.η
    (fun i => HasCompactSupport.of_compactSpace (B.η i)) B.chart_η B.smooth_η
    B.χ B.chart_χ B.smooth_χ B.sum_η
    (fun i x hx => (B.one_χ i).self_of_nhdsSet hx) N _ w
  push_cast
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

theorem exists_smooth_resolvent_threshold :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ α ≥ a, ∀ f : ManifoldSmoothFunctions E M,
      ∃ u : ManifoldSmoothFunctions E M,
        (∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x = f x) ∧
        ∃ v : A.H (2 * ((k + 1 : ℕ) : ℝ)),
          (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = u ∧
          ‖v‖ ≤ 2 * A.parametrixBound * ‖A.ofSmooth (2 * (k : ℝ)) f‖ := by
  let C : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨a, ha, hab⟩ := A.exists_parametrix_threshold C
  refine ⟨a, ha, fun α hα f => ?_⟩
  obtain ⟨hb, hc⟩ := hab α hα
  let v := A.resolvent C α hb hc (A.ofSmooth (2 * (k : ℝ)) f)
  let u : M → ℂ := A.representative (2 * ((k + 1 : ℕ) : ℝ)) v
  have he : ∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x = f x := by
    intro x
    exact (A.resolvent_equation C α hb hc (A.ofSmooth (2 * (k : ℝ)) f) x).trans
      (congrFun (A.ofSmooth_representative _ hs f) x)
  have hum := A.represented_solution_smooth α f (A.representative_C2 v) he v rfl
  exact ⟨⟨u, hum⟩, he, v, rfl, A.resolvent_bound C α hb hc _⟩

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
def smoothMul (f h : ManifoldSmoothFunctions E M) : ManifoldSmoothFunctions E M :=
  ⟨fun x => f x * h x, contMDiff_complex_mul f.contMDiff h.contMDiff⟩

def smoothMulLinear : ManifoldSmoothFunctions E M →ₗ[ℝ]
    ManifoldSmoothFunctions E M →ₗ[ℝ] ManifoldSmoothFunctions E M where
  toFun f :=
    { toFun := smoothMul f
      map_add' := fun h j => by ext x; exact mul_add (f x) (h x) (j x)
      map_smul' := fun c h => by ext x; exact mul_smul_comm c (f x) (h x) }
  map_add' f h := by ext j x; exact add_mul (f x) (h x) (j x)
  map_smul' c f := by ext h x; exact smul_mul_assoc c (f x) (h x)

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma smooth_partition (f : ManifoldSmoothFunctions E M) :
    ∑ i, chartLiftSmoothLinear (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i)
      (chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
        (A.chart_η i) (A.smooth_η i) f) = f := by
  ext x
  simp only [← ContMDiffMap.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  exact atlasGluing_partition_identity A.p A.η A.chart_η A.χ A.chart_χ A.sum_η
    (fun i y hy => (A.one_χ i).self_of_nhdsSet hy) f x

def smoothCutoffLocalization (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    ManifoldSmoothFunctions E M →ₗ[ℝ] FourierSobolevSpace E ℂ (2 * (l : ℝ)) :=
  ((schwartzToSobolev (2 * (l : ℝ))).restrictScalars ℝ).toLinearMap.comp
    (chartSchwartzLinear q ξ (HasCompactSupport.of_compactSpace ξ) hξs hξ)

omit [T2Space M] in
lemma smoothCutoffLocalization_bound (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ManifoldSmoothFunctions E M,
      ‖smoothCutoffLocalization q ξ hξs hξ l f‖ ≤ C * ‖A.ofSmooth (2 * (l : ℝ)) f‖ := by
  choose C hC hb using fun i => chartLift_localization_bound q (A.p i) ξ (A.χ i)
    (HasCompactSupport.of_compactSpace ξ) hξs hξ (A.chart_χ i) (A.smooth_χ i) l
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => (hC i).le), fun f => ?_⟩
  have he := congrArg (smoothCutoffLocalization q ξ hξs hξ l) (A.smooth_partition f)
  rw [map_sum] at he
  rw [← he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i, C i * ‖schwartzToSobolev (2 * (l : ℝ))
        (chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
          (A.chart_η i) (A.smooth_η i) f)‖ := Finset.sum_le_sum (fun i _ => hb i _)
    _ ≤ ∑ i, C i * ‖A.ofSmooth (2 * (l : ℝ)) f‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hC i).le
      exact norm_le_pi_norm (A.ofSmooth (2 * (l : ℝ)) f).val i
    _ = _ := (Finset.sum_mul ..).symm

def cutoffLocalization (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) :
    A.H (2 * (l : ℝ)) →L[ℝ] FourierSobolevSpace E ℂ (2 * (l : ℝ)) :=
  (smoothCutoffLocalization q ξ hξs hξ l).extendOfNorm
    (smoothToManifoldSobolev A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
      A.chart_η A.smooth_η (2 * (l : ℝ)))

omit [T2Space M] in
lemma cutoffLocalization_smooth (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ) (f : ManifoldSmoothFunctions E M) :
    A.cutoffLocalization q ξ hξs hξ l (A.ofSmooth (2 * (l : ℝ)) f) =
      smoothCutoffLocalization q ξ hξs hξ l f := by
  obtain ⟨C, _, hb⟩ := A.smoothCutoffLocalization_bound q ξ hξs hξ l
  exact LinearMap.extendOfNorm_eq
    (denseRange_smoothToManifoldSobolev A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η _) ⟨C, hb⟩ f

omit [T2Space M] in
lemma cutoffLocalization_representative (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (l : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) (f : A.H (2 * (l : ℝ))) (y : E) :
    sobolevRepresentative ht (A.cutoffLocalization q ξ hξs hξ l f) y =
      chartLocalize (E := E) q ξ (A.representative (2 * (l : ℝ)) f) y := by
  refine (denseRange_smoothToManifoldSobolev A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η _).induction_on f ?_ ?_
  · apply isClosed_eq
    · exact (BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
        ((sobolevRepresentative ht).continuous.comp (A.cutoffLocalization q ξ hξs hξ l).continuous)
    · unfold chartLocalize
      split_ifs <;> fun_prop
  · intro u
    change sobolevRepresentative ht
      (A.cutoffLocalization q ξ hξs hξ l (A.ofSmooth (2 * (l : ℝ)) u)) y = _
    rw [A.cutoffLocalization_smooth]
    change sobolevRepresentative ht (schwartzToSobolev (2 * (l : ℝ))
      (chartSchwartzLinear q ξ (HasCompactSupport.of_compactSpace ξ) hξs hξ u)) y = _
    rw [sobolevRepresentative_schwartz]
    change chartLocalize (E := E) q ξ u y =
      chartLocalize (E := E) q ξ (A.representative (2 * (l : ℝ)) (A.ofSmooth (2 * (l : ℝ)) u)) y
    rw [A.ofSmooth_representative _ ht u]

omit [T2Space M] in
lemma smooth_product_bound (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : ManifoldSmoothFunctions E M,
      ‖A.ofSmooth (2 * (l : ℝ)) (smoothMul f h)‖ ≤
        C * ‖A.ofSmooth (2 * (l : ℝ)) f‖ * ‖A.ofSmooth (2 * (l : ℝ)) h‖ := by
  let D : A.t → ℝ := fun i => ‖A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) l‖
  have hD : ∀ i, 0 ≤ D i := fun i =>
    (A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) l).opNorm_nonneg
  let C := sobolevAlgebraConstant (E := E) (2 * (l : ℝ)) * ∑ i, D i
  have hC : 0 ≤ C := mul_nonneg (sobolevAlgebraConstant_nonneg _) (Finset.sum_nonneg (fun i _ => hD i))
  refine ⟨C, hC, fun f h => ?_⟩
  change ‖(A.ofSmooth (2 * (l : ℝ)) (smoothMul f h)).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hC (norm_nonneg _)) (norm_nonneg _))).mpr
  intro i
  let F := chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i) (A.smooth_η i) f
  let H := chartSchwartzLinear (A.p i) (A.χ i) (HasCompactSupport.of_compactSpace _) (A.chart_χ i) (A.smooth_χ i) h
  have he : chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
      (A.chart_η i) (A.smooth_η i) (smoothMul f h) = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) F H := by
    ext y
    change chartLocalize (E := E) (A.p i) (A.η i) (smoothMul f h) y =
      chartLocalize (E := E) (A.p i) (A.η i) f y * chartLocalize (E := E) (A.p i) (A.χ i) h y
    by_cases hy : y ∈ (chartAt E (A.p i)).target
    · simp only [chartLocalize_eq _ _ _ hy]
      change A.η i ((chartAt E (A.p i)).symm y) *
        (f ((chartAt E (A.p i)).symm y) * h ((chartAt E (A.p i)).symm y)) = _
      by_cases hx : A.η i ((chartAt E (A.p i)).symm y) = 0
      · simp only [hx, zero_mul]
      · rw [(A.one_χ i).self_of_nhdsSet (subset_tsupport _ hx), Pi.one_apply, one_mul]
        ring
    · simp only [chartLocalize, hy, ↓reduceIte, zero_mul]
  change ‖schwartzToSobolev (2 * (l : ℝ))
    (chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i) (A.smooth_η i) (smoothMul f h))‖ ≤ _
  rw [he]
  apply (schwartz_sobolev_product_bound ht F H).trans
  have hF : ‖schwartzToSobolev (2 * (l : ℝ)) F‖ ≤ ‖A.ofSmooth (2 * (l : ℝ)) f‖ :=
    norm_le_pi_norm (A.ofSmooth (2 * (l : ℝ)) f).val i
  have hH : ‖schwartzToSobolev (2 * (l : ℝ)) H‖ ≤ D i * ‖A.ofSmooth (2 * (l : ℝ)) h‖ := by
    have hh := (A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) l).le_opNorm
      (A.ofSmooth (2 * (l : ℝ)) h)
    rw [A.cutoffLocalization_smooth] at hh
    exact hh
  have ha := sobolevAlgebraConstant_nonneg (E := E) (2 * (l : ℝ))
  calc
    _ ≤ sobolevAlgebraConstant (E := E) (2 * (l : ℝ)) *
        ‖A.ofSmooth (2 * (l : ℝ)) f‖ * (D i * ‖A.ofSmooth (2 * (l : ℝ)) h‖) := by gcongr
    _ ≤ sobolevAlgebraConstant (E := E) (2 * (l : ℝ)) *
        ‖A.ofSmooth (2 * (l : ℝ)) f‖ * ((∑ j, D j) * ‖A.ofSmooth (2 * (l : ℝ)) h‖) := by
      gcongr
      exact Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)
    _ = _ := by dsimp [C]; ring

local instance H_smulCommClass (s : ℝ) : SMulCommClass ℝ ℝ (A.H s) where
  smul_comm r t x := by rw [smul_smul, smul_smul, mul_comm]

local instance H_isScalarTower (s : ℝ) : IsScalarTower ℝ ℝ (A.H s) where
  smul_assoc r t x := mul_smul r t x

def smoothProduct (l : ℕ) : ManifoldSmoothFunctions E M →ₗ[ℝ]
    ManifoldSmoothFunctions E M →ₗ[ℝ] A.H (2 * (l : ℝ)) :=
  smoothMulLinear.compr₂ (smoothToManifoldSobolev A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    (2 * (l : ℝ)))

def productConstant (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) : ℝ :=
  (A.smooth_product_bound l ht).choose

omit [T2Space M] in
lemma productConstant_nonneg (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    0 ≤ A.productConstant l ht := (A.smooth_product_bound l ht).choose_spec.1

omit [T2Space M] in
lemma smoothProduct_bound (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f h : ManifoldSmoothFunctions E M) :
    ‖A.smoothProduct l f h‖ ≤ A.productConstant l ht *
      ‖A.ofSmooth (2 * (l : ℝ)) f‖ * ‖A.ofSmooth (2 * (l : ℝ)) h‖ :=
  (A.smooth_product_bound l ht).choose_spec.2 f h

def product (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    A.H (2 * (l : ℝ)) →L[ℝ] A.H (2 * (l : ℝ)) →L[ℝ] A.H (2 * (l : ℝ)) :=
  bilinearExtension (A.smoothProduct l)
    (smoothToManifoldSobolev A.p A.η (fun i => HasCompactSupport.of_compactSpace (A.η i))
      A.chart_η A.smooth_η (2 * (l : ℝ)))
    (denseRange_smoothToManifoldSobolev A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η _)
    (A.productConstant l ht) (A.smoothProduct_bound l ht)

omit [T2Space M] in
lemma product_smooth (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f h : ManifoldSmoothFunctions E M) :
    A.product l ht (A.ofSmooth (2 * (l : ℝ)) f) (A.ofSmooth (2 * (l : ℝ)) h) =
      A.ofSmooth (2 * (l : ℝ)) (smoothMul f h) :=
  bilinearExtension_apply _ _ _ _ _ (A.productConstant_nonneg l ht) f h

omit [T2Space M] in
lemma product_bound (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f h : A.H (2 * (l : ℝ))) :
    ‖A.product l ht f h‖ ≤ A.productConstant l ht * ‖f‖ * ‖h‖ :=
  bilinearExtension_bound _ _ _ _ _ (A.productConstant_nonneg l ht) f h

omit [T2Space M] in
lemma product_representative (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (f h : A.H (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.product l ht f h) x =
      A.representative (2 * (l : ℝ)) f x * A.representative (2 * (l : ℝ)) h x := by
  have hd := denseRange_smoothToManifoldSobolev A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η (2 * (l : ℝ))
  refine hd.induction_on f ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro u
    refine hd.induction_on h ?_ ?_
    · apply isClosed_eq <;> fun_prop
    · intro v
      change A.representative (2 * (l : ℝ))
        (A.product l ht (A.ofSmooth (2 * (l : ℝ)) u) (A.ofSmooth (2 * (l : ℝ)) v)) x = _
      rw [A.product_smooth l ht]
      rw [A.ofSmooth_representative _ ht]
      change smoothMul u v x = A.representative (2 * (l : ℝ)) (A.ofSmooth (2 * (l : ℝ)) u) x *
        A.representative (2 * (l : ℝ)) (A.ofSmooth (2 * (l : ℝ)) v) x
      rw [A.ofSmooth_representative _ ht, A.ofSmooth_representative _ ht]
      rfl

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma chartLocalize_eventually_eq (p : M) (χ u : M → ℂ) {x : M}
    (hx : x ∈ (chartAt E p).source) (hχ : χ =ᶠ[𝓝 x] 1) :
    chartLocalize (E := E) p χ u =ᶠ[𝓝 ((chartAt E p) x)] u ∘ (chartAt E p).symm := by
  have hy := (chartAt E p).map_source hx
  have hc' := ((chartAt E p).continuousAt_symm hy).tendsto
  rw [(chartAt E p).left_inv hx] at hc'
  have hc := hχ.comp_tendsto hc'
  filter_upwards [hc, (chartAt E p).open_target.mem_nhds hy] with y hcy hty
  change χ ((chartAt E p).symm y) = 1 at hcy
  rw [chartLocalize_eq _ _ _ hty, hcy, one_mul]
  rfl

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def metricCoefficientSchwartz (i : A.t) (f : E → ℝ) (hf : ContDiff ℝ ∞ f) : 𝓢(E, ℂ) :=
  (show HasCompactSupport (fun y => A.χcoord i y * (f y : ℂ)) from
    (A.compact_χcoord i).mul_right).toSchwartzMap
    ((A.smooth_χcoord i).mul (Complex.ofRealCLM.contDiff.comp hf))

def laplacianPatch (i : A.t) (B : A.PatchCoefficients i) :
    FourierSobolevSpace E ℂ (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  A.lift (A.p i) (A.η i) (A.chart_η i) (A.smooth_η i) k ∘L
    (coefficientPerturbation (Module.finBasis ℝ E) hs
      (fun j l => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.a j l) (B.smooth_a j l)))
      (fun j => schwartzToSobolev (2 * (k : ℝ))
        (A.metricCoefficientSchwartz i (B.c j) (B.smooth_c j)))).restrictScalars ℝ

def laplacianCLM (B : ∀ i, A.PatchCoefficients i) :
    A.H (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  ∑ i, A.laplacianPatch i (B i) ∘L
    A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k + 1)

omit [T2Space M] in
lemma laplacianPatch_representative (i : A.t) (B : A.PatchCoefficients i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ))
      (A.laplacianPatch i B (A.cutoffLocalization (A.p i) (A.χ i)
        (A.chart_χ i) (A.smooth_χ i) (k + 1) u)) x =
      A.η i x * complexLaplaceBeltrami g (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
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
    (fun j l y => (metricCoefficients g (A.p i) y)⁻¹ j l)
    (metricFirstCoefficient g (A.p i)) (sobolevRepresentative ht' w) ((chartAt E (A.p i)) x) = _
  rw [hw, complexLaplaceBeltrami_inChart (A.representative_C2 u) g (A.p i) hxs]
  exact euclideanElliptic_congr _ _ _ (chartLocalize_eventually_eq _ _ _ hxs hχ)

omit [T2Space M] in
lemma laplacianCLM_representative (B : ∀ i, A.PatchCoefficients i)
    (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.representative (2 * (k : ℝ)) (A.laplacianCLM B u) x =
      complexLaplaceBeltrami g (A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [laplacianCLM, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, A.laplacianPatch_representative]
  rw [← Finset.sum_mul, A.sum_η, one_mul]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
section SubspaceBilinear
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local instance subspace_smulCommClass (S : Submodule ℝ X) : SMulCommClass ℝ ℝ S :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance subspace_isScalarTower (S : Submodule ℝ X) : IsScalarTower ℝ ℝ S :=
  ⟨fun a b c => mul_smul a b c⟩
def restrictBilinear (p : X →L[ℝ] X →L[ℝ] X) (S : Submodule ℝ X)
    (hp : ∀ u v : S, p u v ∈ S) : S →L[ℝ] S →L[ℝ] S :=
  (LinearMap.mk₂ ℝ (fun (u v : S) => (⟨p u v, hp u v⟩ : S))
    (fun u v w => by apply Subtype.ext; exact congrArg (fun f : X →L[ℝ] X => f (w : X)) (map_add p (u : X) (v : X)))
    (fun c u v => by apply Subtype.ext; exact congrArg (fun f : X →L[ℝ] X => f (v : X)) (map_smul p c (u : X)))
    (fun u v w => by apply Subtype.ext; exact map_add (p (u : X)) (v : X) (w : X))
    (fun c u v => by apply Subtype.ext; exact map_smul (p (u : X)) c (v : X))).mkContinuous₂
      ‖p‖ (fun u v => p.le_opNorm₂ u v)
lemma norm_restrict_of_bound (f : X →L[ℝ] Y) (S : Submodule ℝ X) (T : Submodule ℝ Y)
    (hf : ∀ x ∈ S, f x ∈ T) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.restrict hf‖ ≤ C := by
  apply (f.restrict hf).opNorm_le_bound hC
  intro x
  change ‖f (x : X)‖ ≤ C * ‖(x : X)‖
  exact hb (x : X)
end SubspaceBilinear
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma laplaceBeltrami_zero (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun _ => 0) x = 0 := by
  simp [laplaceBeltrami, Function.comp_def]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma complexLaplaceBeltrami_ofReal (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    complexLaplaceBeltrami g (fun y => (u y : ℂ)) x = (laplaceBeltrami g u x : ℂ) := by
  apply Complex.ext
  · rfl
  · exact laplaceBeltrami_zero g x

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

abbrev realH (s : ℝ) : Submodule ℝ (A.H s) where
  carrier := {u | ∀ x, (A.representative s u x).im = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv x; simp only [map_add, BoundedContinuousFunction.add_apply, Complex.add_im, hu x, hv x, add_zero]
  smul_mem' := by intro c u hu x; simp only [map_smul, BoundedContinuousFunction.smul_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hu x, mul_zero, zero_mul, add_zero]

@[reducible] instance realH_nacg (s : ℝ) : NormedAddCommGroup (A.realH s) := inferInstance
@[reducible] instance realH_snacg (s : ℝ) : SeminormedAddCommGroup (A.realH s) := inferInstance
@[reducible] instance realH_acg (s : ℝ) : AddCommGroup (A.realH s) := inferInstance
@[reducible] instance realH_ns (s : ℝ) : NormedSpace ℝ (A.realH s) := inferInstance
@[reducible] instance realH_mod (s : ℝ) : Module ℝ (A.realH s) := inferInstance

omit [T2Space M] in
lemma realH_closed (s : ℝ) : IsClosed (A.realH s : Set (A.H s)) := by
  change IsClosed {u | ∀ x, (A.representative s u x).im = 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_eq _ continuous_const
  exact Complex.continuous_im.comp ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
    (A.representative s).continuous)

instance realH_completeSpace (s : ℝ) : CompleteSpace (A.realH s) :=
  (A.realH_closed s).completeSpace_coe

local instance realH_smulCommClass (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance realH_isScalarTower (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩

omit [T2Space M] in
lemma realH_coe_representative (s : ℝ) (u : A.realH s) (x : M) :
    (((A.representative s u x).re : ℝ) : ℂ) = A.representative s u x := by
  apply Complex.ext
  · rfl
  · exact (u.property x).symm

def inclusion : A.H (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.H (2 * (k : ℝ)) :=
  manifoldSobolevInclusion A.p A.η (fun _ => HasCompactSupport.of_compactSpace _)
    A.chart_η A.smooth_η _ _

omit [T2Space M] in
lemma inclusion_representative (u : A.H (2 * ((k + 1 : ℕ) : ℝ))) :
    A.representative (2 * (k : ℝ)) (A.inclusion u) =
      A.representative (2 * ((k + 1 : ℕ) : ℝ)) u :=
  manifoldSobolevInclusion_representative A.p A.η
    (fun _ => HasCompactSupport.of_compactSpace _) A.chart_η A.smooth_η A.sum_η _ _
    (by push_cast; linarith) hs u

omit [T2Space M] in
lemma norm_inclusion_le : ‖A.inclusion‖ ≤ 1 :=
  norm_manifoldSobolevInclusion_le A.p A.η
    (fun _ => HasCompactSupport.of_compactSpace _) A.chart_η A.smooth_η _ _ (by push_cast; linarith)

def realInclusion : A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.inclusion.restrict fun u hu x => by rw [A.inclusion_representative]; exact hu x

omit [T2Space M] in
lemma product_mem_realH (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u v : A.realH (2 * (l : ℝ))) : A.product l ht u v ∈ A.realH (2 * (l : ℝ)) := by
  intro x
  rw [A.product_representative l ht]
  simp only [Complex.mul_im, u.property x, v.property x, mul_zero, zero_mul, add_zero]

local instance H_real_smulCommClass (s : ℝ) : SMulCommClass ℝ ℝ (A.H s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance H_real_isScalarTower (s : ℝ) : IsScalarTower ℝ ℝ (A.H s) :=
  ⟨fun a b c => mul_smul a b c⟩

def realProduct (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))) :
    A.realH (2 * (l : ℝ)) →L[ℝ] A.realH (2 * (l : ℝ)) →L[ℝ] A.realH (2 * (l : ℝ)) :=
  restrictBilinear (A.product l ht) (A.realH (2 * (l : ℝ))) (A.product_mem_realH l ht)

omit [T2Space M] in
lemma realProduct_representative (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u v : A.realH (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.realProduct l ht u v) x =
      A.representative (2 * (l : ℝ)) u x * A.representative (2 * (l : ℝ)) v x :=
  A.product_representative l ht u v x

omit [T2Space M] in
lemma laplacian_mem_realH (B : ∀ i, A.PatchCoefficients i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) : A.laplacianCLM B u ∈ A.realH (2 * (k : ℝ)) := by
  intro x
  rw [A.laplacianCLM_representative]
  change laplaceBeltrami g (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) x = 0
  have he : (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) u) = fun _ => 0 :=
    funext u.property
  rw [he, laplaceBeltrami_zero]

def realLaplacian (B : ∀ i, A.PatchCoefficients i) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  A.laplacianCLM B |>.restrict fun u hu => A.laplacian_mem_realH B ⟨u, hu⟩

lemma resolvent_mem_realH (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.realH (2 * (k : ℝ))) :
    A.resolvent B α hα he u ∈ A.realH (2 * ((k + 1 : ℕ) : ℝ)) := by
  let v := A.resolvent B α hα he u
  have hv := A.representative_C2 v
  have him : (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℝ) = 0 := by
    apply positive_shift_kernel_eq_zero_C2 g hα0 (Complex.imCLM.contMDiff.comp hv)
    intro x
    change α * (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v x).im -
      laplaceBeltrami g (Complex.im ∘ A.representative (2 * ((k + 1 : ℕ) : ℝ)) v) x = 0
    have h := congrArg Complex.im (A.resolvent_equation B α hα he u x)
    simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, u.property x, complexLaplaceBeltrami, Complex.add_im,
      Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, zero_add, Function.comp_apply] using h
  exact fun x => congrFun him x

def realResolvent (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) (he : A.errorBound B α ≤ 1 / 2) :
    A.realH (2 * (k : ℝ)) →L[ℝ] A.realH (2 * ((k + 1 : ℕ) : ℝ)) :=
  (A.resolvent B α hα he).restrict fun u hu => A.resolvent_mem_realH B α hα0 hα he ⟨u, hu⟩

lemma realResolvent_norm_bound (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2) (he : A.errorBound B α ≤ 1 / 2) :
    ‖A.realResolvent B α hα0 hα he‖ ≤ 2 * A.parametrixBound := by
  exact norm_restrict_of_bound (A.resolvent B α hα he) _ _ _ _ (mul_nonneg (by norm_num) A.parametrixBound_nonneg)
    (A.resolvent_bound B α hα he)

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def boundedDivergence (p : X →L[ℝ] X →L[ℝ] X) (q : Y →L[ℝ] Y →L[ℝ] Y)
    (I L : X →L[ℝ] Y) (b : X) : X →L[ℝ] Y :=
  (1 / 2 : ℝ) • (L.comp (p b) + (q (I b)).comp L - (q (L b)).comp I)

lemma boundedDivergence_norm (p : X →L[ℝ] X →L[ℝ] X) (q : Y →L[ℝ] Y →L[ℝ] Y)
    (I L : X →L[ℝ] Y) (b : X) :
    ‖boundedDivergence p q I L b‖ ≤
      (‖L‖ * ‖p‖ + 2 * ‖q‖ * ‖I‖ * ‖L‖) / 2 * ‖b‖ := by
  rw [boundedDivergence, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖L.comp (p b)‖ + ‖(q (I b)).comp L‖ + ‖(q (L b)).comp I‖) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (1 / 2 : ℝ) * (‖L‖ * (‖p‖ * ‖b‖) +
        (‖q‖ * (‖I‖ * ‖b‖)) * ‖L‖ + (‖q‖ * (‖L‖ * ‖b‖)) * ‖I‖) := by
      gcongr
      · exact (L.opNorm_comp_le (p b)).trans (mul_le_mul_of_nonneg_left (p.le_opNorm b) (norm_nonneg _))
      · exact ((q (I b)).opNorm_comp_le L).trans (mul_le_mul_of_nonneg_right ((q.le_opNorm (I b)).trans (mul_le_mul_of_nonneg_left (I.le_opNorm b) (norm_nonneg _))) (norm_nonneg _))
      · exact ((q (L b)).opNorm_comp_le I).trans (mul_le_mul_of_nonneg_right ((q.le_opNorm (L b)).trans (mul_le_mul_of_nonneg_left (L.le_opNorm b) (norm_nonneg _))) (norm_nonneg _))
    _ = _ := by ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

local instance realH_smulCommClass' (s : ℝ) : SMulCommClass ℝ ℝ (A.realH s) :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance realH_isScalarTower' (s : ℝ) : IsScalarTower ℝ ℝ (A.realH s) :=
  ⟨fun a b c => mul_smul a b c⟩

def realValue (s : ℝ) (u : A.realH s) (x : M) : ℝ := (A.representative s u x).re

omit [T2Space M] in
lemma ofReal_realValue (s : ℝ) (u : A.realH s) (x : M) :
    (A.realValue s u x : ℂ) = A.representative s u x := A.realH_coe_representative s u x

omit [T2Space M] in
lemma realValue_add (s : ℝ) (u v : A.realH s) (x : M) :
    A.realValue s (u + v) x = A.realValue s u x + A.realValue s v x := by
  simp [realValue]

omit [T2Space M] in
lemma realValue_sub (s : ℝ) (u v : A.realH s) (x : M) :
    A.realValue s (u - v) x = A.realValue s u x - A.realValue s v x := by
  simp [realValue]

omit [T2Space M] in
lemma realValue_smul (s : ℝ) (c : ℝ) (u : A.realH s) (x : M) :
    A.realValue s (c • u) x = c * A.realValue s u x := by
  simp [realValue]

omit [T2Space M] in
lemma realValue_product (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u v : A.realH (2 * (l : ℝ))) (x : M) :
    A.realValue (2 * (l : ℝ)) (A.realProduct l ht u v) x =
      A.realValue (2 * (l : ℝ)) u x * A.realValue (2 * (l : ℝ)) v x := by
  simpa only [realValue, Complex.mul_re, u.property x, zero_mul, sub_zero] using
    congrArg Complex.re (A.realProduct_representative l ht u v x)

omit [T2Space M] in
lemma realValue_inclusion (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.realInclusion u) x =
      A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u x := by
  change (A.representative _ (A.inclusion u) x).re = _
  rw [A.inclusion_representative]
  rfl

omit [T2Space M] in
lemma realValue_C2 (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) :=
  Complex.reCLM.contMDiff.comp (A.representative_C2 u)

omit [T2Space M] in
lemma realValue_laplacian (B : ∀ i, A.PatchCoefficients i)
    (u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.realLaplacian B u) x =
      laplaceBeltrami g (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  change (A.representative _ (A.laplacianCLM B u) x).re = _
  rw [A.laplacianCLM_representative]
  rfl

def realDivergence (B : ∀ i, A.PatchCoefficients i)
    (b : A.realH (2 * ((k + 1 : ℕ) : ℝ))) :
    A.realH (2 * ((k + 1 : ℕ) : ℝ)) →L[ℝ] A.realH (2 * (k : ℝ)) :=
  boundedDivergence (A.realProduct (k + 1) (by push_cast; linarith))
    (A.realProduct k hs) A.realInclusion (A.realLaplacian B) b

omit [T2Space M] in
lemma realDivergence_value (B : ∀ i, A.PatchCoefficients i)
    (b u : A.realH (2 * ((k + 1 : ℕ) : ℝ))) (x : M) :
    A.realValue (2 * (k : ℝ)) (A.realDivergence B b u) x =
      weightedLaplacian g (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) b)
        (A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u) x := by
  simp only [realDivergence, boundedDivergence, _root_.smul_apply,
    _root_.add_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, A.realValue_smul, A.realValue_sub,
    A.realValue_add, A.realValue_product, A.realValue_inclusion, A.realValue_laplacian]
  rw [weightedLaplacian_product_formula (A.realValue_C2 b) (A.realValue_C2 u)]
  have hfun : A.realValue (2 * ((k + 1 : ℕ) : ℝ))
      (A.realProduct (k + 1) (by push_cast; linarith) b u) =
      fun y => A.realValue (2 * ((k + 1 : ℕ) : ℝ)) b y *
        A.realValue (2 * ((k + 1 : ℕ) : ℝ)) u y := by
    funext y
    exact A.realValue_product _ _ b u y
  rw [hfun]
  ring

lemma realResolvent_value (B : ∀ i, A.PatchCoefficients i) (α : ℝ) (hα0 : 0 < α)
    (hα : ∀ i, 1 ≤ α * (A.localInverse i).radius ^ 2)
    (he : A.errorBound B α ≤ 1 / 2) (u : A.realH (2 * (k : ℝ))) (x : M) :
    α * A.realValue (2 * ((k + 1 : ℕ) : ℝ)) (A.realResolvent B α hα0 hα he u) x -
      laplaceBeltrami g (A.realValue (2 * ((k + 1 : ℕ) : ℝ))
        (A.realResolvent B α hα0 hα he u)) x = A.realValue (2 * (k : ℝ)) u x := by
  change α * (A.representative _ (A.resolvent B α hα he u) x).re -
      laplaceBeltrami g (fun y => (A.representative _ (A.resolvent B α hα he u) y).re) x =
        (A.representative (2 * (k : ℝ)) u.val x).re
  have h := congrArg Complex.re (A.resolvent_equation B α hα he u x)
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, complexLaplaceBeltrami, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero,
    add_zero, Function.comp_def] using h

def realOfSmooth (s : ℝ) (ht : Module.finrank ℝ E < 2 * s)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) : A.realH s :=
  ⟨A.ofSmooth s ⟨fun x => (f x : ℂ), Complex.ofRealCLM.contMDiff.comp hf⟩,
    fun x => by erw [congrFun (A.ofSmooth_representative s ht _) x]; rfl⟩

omit [T2Space M] in
lemma realOfSmooth_value (s : ℝ) (ht : Module.finrank ℝ E < 2 * s)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    A.realValue s (A.realOfSmooth s ht f hf) x = f x := by
  dsimp only [realOfSmooth, realValue]
  erw [congrFun (A.ofSmooth_representative s ht _) x]
  rfl

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open scoped Manifold BoundedContinuousFunction ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def ChartJetBound (N : ℕ) (f : M → ℂ) (C : ℝ) : Prop :=
  ∀ (i : A.t) (j : ℕ), j ≤ N → ∀ y : E,
    ‖iteratedFDeriv ℝ j (chartLocalize (E := E) (A.p i) (A.η i) f) y‖ ≤ C

omit [T2Space M] in
lemma chart_jet_representative_bound {s : ℝ} (ht : Module.finrank ℝ E < 2 * s)
    (n : ℕ) (hn : Module.finrank ℝ E < 2 * (s - n))
    (u : A.H s) (i : A.t) (y : E) :
    ‖iteratedFDeriv ℝ n (chartLocalize (E := E) (A.p i) (A.η i) (A.representative s u)) y‖ ≤
      (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ n * ‖momentBesselLp n hn‖ * ‖u‖ := by
  have he : chartLocalize (E := E) (A.p i) (A.η i) (A.representative s u) =
      sobolevRepresentative ht (u.val i) := by
    ext x
    exact (manifoldSobolevRepresentative_localize A.p A.η
      (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η A.sum_η ht u i x).symm
  rw [he]
  apply (sobolevRepresentative_jet_bound ht n hn (u.val i) y).trans
  gcongr
  exact norm_le_pi_norm u.val i

omit [T2Space M] in

theorem exists_chart_jet_constant {s : ℝ} (N : ℕ)
    (hN : Module.finrank ℝ E < 2 * (s - N)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : A.H s,
      A.ChartJetBound N (A.representative s u) (C * ‖u‖) := by
  have ht : Module.finrank ℝ E < 2 * s := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hn (j : Fin (N + 1)) : Module.finrank ℝ E < 2 * (s - (j : ℕ)) := by
    have hj : (j : ℕ) ≤ N := by omega
    have hj' : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
    linarith
  let D (j : Fin (N + 1)) : ℝ :=
    (2 * Real.pi * ‖innerSL ℝ (E := E)‖) ^ (j : ℕ) * ‖momentBesselLp (j : ℕ) (hn j)‖
  have hD (j : Fin (N + 1)) : 0 ≤ D j := by
    apply mul_nonneg _ (norm_nonneg _)
    exact pow_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)
      (innerSL ℝ (E := E)).opNorm_nonneg) _
  refine ⟨1 + ∑ j, D j, by positivity, ?_⟩
  intro u i j hj y
  let a : Fin (N + 1) := ⟨j, by omega⟩
  have hb := A.chart_jet_representative_bound ht j (hn a) u i y
  have hDC : D a ≤ 1 + ∑ j, D j := by
    have := Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ a)
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_right hDC (norm_nonneg _))

end CompactMetricAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set MeasureTheory
open scoped LineDeriv SchwartzMap ContDiff Manifold ENNReal
section CompactL2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_L2_compact_bound (f : 𝓢(E, ℂ)) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport f ⊆ K) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖f.toLp 2 volume‖ ≤ C * (volume K).toReal ^ (1 / 2 : ℝ) := by
  have he : eLpNorm f 2 volume ≤
      ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) := by
    calc
      eLpNorm f 2 volume ≤ eLpNorm (K.indicator (fun _ : E => (C : ℂ))) 2 volume := by
        apply eLpNorm_mono f.continuous.aestronglyMeasurable
        intro x
        by_cases hx : x ∈ K
        · simpa only [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hC] using hb x
        · have hz : f x = 0 := by
            by_contra hn
            exact hx (hsupp (subset_tsupport _ hn))
          simp only [Set.indicator_of_notMem hx, hz, norm_zero, le_refl]
      _ = ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) := by
        rw [eLpNorm_indicator_const hK.measurableSet.nullMeasurableSet (by norm_num) (by norm_num)]
        simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hC, ENNReal.toReal_ofNat]
  rw [SchwartzMap.norm_toLp]
  have hfinite : ENNReal.ofReal C * volume K ^ (1 / 2 : ℝ) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hK.measure_lt_top.ne)
  have ht := ENNReal.toReal_mono hfinite he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, ENNReal.toReal_rpow] using ht

lemma schwartz_word_bound_of_jets (f : 𝓢(E, ℂ)) (K : Set E) (hK : IsCompact K)
    (hsupp : tsupport f ⊆ K) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j, j ≤ n → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    SchwartzWordBound n f (C * (volume K).toReal ^ (1 / 2 : ℝ)) := by
  intro j hj w
  apply schwartz_L2_compact_bound _ K hK
    ((SchwartzMap.tsupport_iteratedLineDerivOp_subset _ f).trans hsupp) C hC
  intro x
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  calc
    ‖(iteratedFDeriv ℝ j f x) (fun a => stdOrthonormalBasis ℝ E (w a))‖ ≤
        ‖iteratedFDeriv ℝ j f x‖ * ∏ a, ‖stdOrthonormalBasis ℝ E (w a)‖ :=
      (iteratedFDeriv ℝ j f x).le_opNorm _
    _ = ‖iteratedFDeriv ℝ j f x‖ := by simp
    _ ≤ C := hb j hj x
end CompactL2
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
theorem exists_jet_sobolev_constant (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (f : ManifoldSmoothFunctions E M) (C : ℝ), 0 ≤ C →
      A.ChartJetBound (2 * n) f C → ‖A.ofSmooth (2 * (n : ℝ)) f‖ ≤ D * C := by
  classical
  let K (i : A.t) := (chartAt E (A.p i)) '' tsupport (A.η i)
  have hK (i : A.t) : IsCompact (K i) :=
    isCompact_chartSupport (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _) (A.chart_η i)
  let L : ℝ := (1 + ((2 * Real.pi) ^ 2 : ℝ)⁻¹ * Module.finrank ℝ E) ^ n
  let V (i : A.t) : ℝ := (volume (K i)).toReal ^ (1 / 2 : ℝ)
  have hL : 0 ≤ L := by positivity
  have hV (i : A.t) : 0 ≤ V i := Real.rpow_nonneg (ENNReal.toReal_nonneg) _
  refine ⟨1 + L * ∑ i, V i, by positivity, ?_⟩
  intro f C hC hf
  change ‖(A.ofSmooth (2 * (n : ℝ)) f).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  let v := chartSchwartzLinear (A.p i) (A.η i) (HasCompactSupport.of_compactSpace _)
    (A.chart_η i) (A.smooth_η i) f
  change ‖schwartzToSobolev (2 * (n : ℝ)) v‖ ≤ _
  have hb : SchwartzWordBound (2 * n) v (C * V i) := by
    refine schwartz_word_bound_of_jets v (K i) (hK i) ?_ (2 * n) C hC ?_
    · exact closure_minimal (support_chartLocalize (E := E) (A.p i) (A.η i) f) (hK i).isClosed
    · intro j hj x
      exact hf i j hj x
  have hv := sobolev_even_le_word_bound n v (C * V i) hb
  have hvi : V i ≤ ∑ i, V i := Finset.single_le_sum (fun j _ => hV j) (Finset.mem_univ i)
  calc
    ‖schwartzToSobolev (2 * (n : ℝ)) v‖ ≤ L * (C * V i) := hv
    _ = (L * V i) * C := by ring
    _ ≤ (1 + L * ∑ i, V i) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact (mul_le_mul_of_nonneg_left hvi hL).trans (by linarith)

end CompactMetricAtlas

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]
omit [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [T2Space M] in
lemma chart_derivative_ne_zero_transfer {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (p q x : M) (hpx : x ∈ (chartAt E p).source) (hqx : x ∈ (chartAt E q).source)
    (hd : fderiv ℝ (u ∘ (chartAt E q).symm) ((chartAt E q) x) ≠ 0) :
    fderiv ℝ (u ∘ (chartAt E p).symm) ((chartAt E p) x) ≠ 0 := by
  intro hz
  apply hd
  apply ContinuousLinearMap.ext
  intro v
  rw [← (Module.finBasis ℝ E).sum_repr v]
  simp only [map_sum,map_smul]
  have hi (i) := fderiv_inChart_change_C2 hu p q ((chartAt E q).map_source hqx)
    (by simpa only [(chartAt E q).left_inv hqx] using hpx) i
  have hi0 (i) : fderiv ℝ (u ∘ (chartAt E q).symm) ((chartAt E q) x)
      (Module.finBasis ℝ E i) = 0 := by
    rw [hi]
    simp only [chartTransition,Function.comp_apply,(chartAt E q).left_inv hqx,hz,zero_apply,
      zero_mul,Finset.sum_const_zero]
  simp only [hi0,smul_zero,Finset.sum_const_zero,zero_apply]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
variable (A : CompactMetricAtlas g k hs)
omit [T2Space M] in
lemma localization_real_germ (i : A.t) {x : M} (hx : x ∈ tsupport (A.η i))
    (u : A.realH (2*((k+1:ℕ):ℝ)))
    (ht : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ))) :
    (fun y => (sobolevRepresentative ht (A.cutoffLocalization (A.p i) (A.χ i)
      (A.chart_χ i) (A.smooth_χ i) (k+1) u) y).re) =ᶠ[𝓝 ((chartAt E (A.p i)) x)]
      A.realValue (2*((k+1:ℕ):ℝ)) u ∘ (chartAt E (A.p i)).symm := by
  have hc := chartLocalize_eventually_eq (A.p i) (A.χ i)
    (A.representative (2*((k+1:ℕ):ℝ)) u) (A.chart_η i hx)
    ((A.one_χ i).filter_mono (nhds_le_nhdsSet hx))
  filter_upwards [hc] with y hy
  rw [A.cutoffLocalization_representative]
  exact congrArg Complex.re hy

abbrev highIndex (_A : CompactMetricAtlas g k hs) : ℝ := 2*((k+1:ℕ):ℝ)
omit [CompactSpace M] [T2Space M] in
lemma highIndex_bound : Module.finrank ℝ E < 2*A.highIndex := by
  have h := hs
  dsimp [highIndex]; push_cast; linarith
omit [CompactSpace M] [T2Space M] in
lemma highIndex_bound_one : Module.finrank ℝ E < 2*(A.highIndex-1) := by
  have h := hs
  dsimp [highIndex]; push_cast; linarith

def localizedRealValue (i : A.t) (v : A.realH A.highIndex) (y : E) : ℝ :=
  (sobolevRepresentative A.highIndex_bound (A.cutoffLocalization (A.p i) (A.χ i)
    (A.chart_χ i) (A.smooth_χ i) (k+1) v) y).re

def localizedFirstJet (i : A.t) (v : A.realH A.highIndex) (y : E) : ℝ × (E →L[ℝ] ℝ) :=
  (A.localizedRealValue i v y,fderiv ℝ (A.localizedRealValue i v) y)

omit [T2Space M] in
lemma localizedFirstJet_continuous (i : A.t) :
    Continuous (fun z : A.realH A.highIndex × E => A.localizedFirstJet i z.1 z.2) := by
  let L : A.realH A.highIndex →L[ℝ] FourierSobolevSpace E ℂ A.highIndex :=
    A.cutoffLocalization (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) (k+1) ∘L
      (A.realH A.highIndex).subtypeL
  have h := (continuous_real_sobolev_firstJet A.highIndex_bound_one A.highIndex_bound).comp
    ((L.continuous.comp continuous_fst).prodMk continuous_snd)
  convert h using 1
  rfl

omit [T2Space M] in
lemma localizedFirstJet_ne_zero (i : A.t) (u : A.realH A.highIndex)
    (hreg : ∀ x, A.realValue A.highIndex u x = 0 →
      fderiv ℝ (A.realValue A.highIndex u ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0)
    {x : M} (hx : x ∈ tsupport (A.η i)) :
    A.localizedFirstJet i u ((chartAt E (A.p i)) x) ≠ 0 := by
  have hg := A.localization_real_germ i hx u A.highIndex_bound
  intro hz
  have hf : A.realValue A.highIndex u x = 0 := by
    have hh := congrArg Prod.fst hz
    change A.localizedRealValue i u ((chartAt E (A.p i)) x) = 0 at hh
    rw [localizedRealValue,hg.eq_of_nhds,Function.comp_apply,
      (chartAt E (A.p i)).left_inv (A.chart_η i hx)] at hh
    exact hh
  apply chart_derivative_ne_zero_transfer (A.realValue_C2 u) (A.p i) x x
    (A.chart_η i hx) (mem_chart_source E x) (hreg x hf)
  rw [← hg.fderiv_eq]
  exact congrArg Prod.snd hz

omit [T2Space M] in
lemma eventually_localizedFirstJet_ne_zero (i : A.t) (u : A.realH A.highIndex)
    (hreg : ∀ x, A.realValue A.highIndex u x = 0 →
      fderiv ℝ (A.realValue A.highIndex u ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0) :
    ∀ᶠ v in 𝓝 u, ∀ y ∈ (chartAt E (A.p i)) '' tsupport (A.η i),
      A.localizedFirstJet i v y ≠ 0 := by
  have hK : IsCompact ((chartAt E (A.p i)) '' tsupport (A.η i)) :=
    (isClosed_tsupport (A.η i)).isCompact.image_of_continuousOn
      ((chartAt E (A.p i)).continuousOn.mono (A.chart_η i))
  apply hK.eventually_forall_of_forall_eventually
  rintro y ⟨x,hx,rfl⟩
  have hc : ContinuousAt (fun z : A.realH A.highIndex × E => A.localizedFirstJet i z.1 z.2)
      (u,(chartAt E (A.p i)) x) := (A.localizedFirstJet_continuous i).continuousAt
  exact hc.eventually (isOpen_ne.mem_nhds (A.localizedFirstJet_ne_zero i u hreg hx))

omit [T2Space M] in
lemma regular_of_localizedFirstJet (v : A.realH A.highIndex)
    (hv : ∀ i, ∀ y ∈ (chartAt E (A.p i)) '' tsupport (A.η i),
      A.localizedFirstJet i v y ≠ 0) :
    ∀ x, A.realValue A.highIndex v x = 0 →
      fderiv ℝ (A.realValue A.highIndex v ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0 := by
  classical
  intro x hx
  obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ i, A.η i x) ≠ 0 from (A.sum_η x).trans_ne one_ne_zero)
  have his : x ∈ tsupport (A.η i) := subset_tsupport _ hi
  have hg := A.localization_real_germ i his v A.highIndex_bound
  have hn : fderiv ℝ (A.realValue A.highIndex v ∘ (chartAt E (A.p i)).symm)
      ((chartAt E (A.p i)) x) ≠ 0 := by
    intro hz
    apply hv i _ ⟨x,his,rfl⟩
    apply Prod.ext
    · change A.localizedRealValue i v ((chartAt E (A.p i)) x) = 0
      rw [localizedRealValue,hg.eq_of_nhds,Function.comp_apply,
        (chartAt E (A.p i)).left_inv (A.chart_η i his)]
      exact hx
    · exact hg.fderiv_eq.trans hz
  exact chart_derivative_ne_zero_transfer (A.realValue_C2 v) x (A.p i) x
    (mem_chart_source E x) (A.chart_η i his) hn

omit [T2Space M] in
theorem eventually_regular_realValue (u : A.realH A.highIndex)
    (hreg : ∀ x, A.realValue A.highIndex u x = 0 →
      fderiv ℝ (A.realValue A.highIndex u ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0) :
    ∀ᶠ v in 𝓝 u, ∀ x, A.realValue A.highIndex v x = 0 →
      fderiv ℝ (A.realValue A.highIndex v ∘ (chartAt E x).symm) ((chartAt E x) x) ≠ 0 := by
  filter_upwards [Filter.eventually_all.mpr (fun i => A.eventually_localizedFirstJet_ne_zero i u hreg)] with v hv
  exact A.regular_of_localizedFirstJet v hv
end CompactMetricAtlas

end YauCounterexamples
end

end OAI
