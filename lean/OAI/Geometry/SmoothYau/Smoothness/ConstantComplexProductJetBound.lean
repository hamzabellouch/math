import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.LocalIntegrationParts
import OAI.Geometry.SmoothYau.Smoothness.LpNormTwoBounds
import OAI.Geometry.SmoothYau.Spectrum.SmoothExtension

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
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def chartLocalize (p : M) (η u : M → ℂ) (y : E) : ℂ := by
  classical
  exact if y ∈ (chartAt E p).target then η ((chartAt E p).symm y) * u ((chartAt E p).symm y) else 0

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma chartLocalize_eq (p : M) (η u : M → ℂ) {y : E} (hy : y ∈ (chartAt E p).target) :
    chartLocalize (E := E) p η u y = η ((chartAt E p).symm y) * u ((chartAt E p).symm y) := ite_eq_left hy

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma support_chartLocalize (p : M) (η u : M → ℂ) :
    support (chartLocalize (E := E) p η u) ⊆ (chartAt E p) '' tsupport η := by
  intro y hy
  by_cases hy' : y ∈ (chartAt E p).target
  · refine ⟨(chartAt E p).symm y, ?_, (chartAt E p).right_inv hy'⟩
    apply subset_tsupport
    intro hzero
    apply hy
    simp only [chartLocalize, ite_eq_left hy', hzero, zero_mul]
  · exact False.elim (hy (by simp only [chartLocalize, ite_eq_right hy']))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma isCompact_chartSupport (p : M) (η : M → ℂ)
    (hη : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    IsCompact ((chartAt E p) '' tsupport η) :=
  hη.image_of_continuousOn ((chartAt E p).continuousOn.mono hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma hasCompactSupport_chartLocalize (p : M) (η u : M → ℂ)
    (hη : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    HasCompactSupport (chartLocalize (E := E) p η u) :=
  (isCompact_chartSupport (E := E) p η hη hs).of_isClosed_subset isClosed_closure
    (closure_minimal (support_chartLocalize (E := E) p η u) (isCompact_chartSupport (E := E) p η hη hs).isClosed)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_chartLocalize_subset (p : M) (η u : M → ℂ)
    (hη : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    tsupport (chartLocalize (E := E) p η u) ⊆ (chartAt E p).target := by
  exact (closure_minimal (support_chartLocalize (E := E) p η u)
    (isCompact_chartSupport (E := E) p η hη hs).isClosed).trans
    (image_subset_iff.mpr fun x hx => (chartAt E p).map_source (hs hx))

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiff_chartLocalize (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u) :
    ContDiff ℝ ∞ (chartLocalize (E := E) p η u) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro y hy
  have hyt := tsupport_chartLocalize_subset (E := E) p η u hηc hs hy
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E p).symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hyt
  rw [contMDiffAt_iff_contDiffAt]
  have ha : ContDiffAt ℝ ∞ (η ∘ (chartAt E p).symm) y :=
    contMDiffAt_iff_contDiffAt.mp (hη.contMDiffAt.comp y hc)
  have hb : ContDiffAt ℝ ∞ (u ∘ (chartAt E p).symm) y :=
    contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y hc)
  apply (ha.mul hb).congr_of_eventuallyEq
  filter_upwards [(chartAt E p).open_target.mem_nhds hyt] with z hz
  exact chartLocalize_eq (E := E) p η u hz

def chartSchwartz (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u) : 𝓢(E, ℂ) :=
  (hasCompactSupport_chartLocalize (E := E) p η u hηc hs).toSchwartzMap
    (contDiff_chartLocalize (E := E) p η u hηc hs hη hu)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma chartSchwartz_apply (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u) (x : M)
    (hx : x ∈ (chartAt E p).source) :
    chartSchwartz (E := E) p η u hηc hs hη hu (chartAt E p x) = η x * u x := by
  change chartLocalize (E := E) p η u _ = _
  rw [chartLocalize_eq (E := E) p η u ((chartAt E p).map_source hx), (chartAt E p).left_inv hx]


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
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]

abbrev ManifoldSmoothFunctions (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯

def smoothToBounded : ManifoldSmoothFunctions E M →ₗ[ℝ] M →ᵇ ℂ where
  toFun u := BoundedContinuousFunction.mkOfCompact ⟨u, u.contMDiff.continuous⟩
  map_add' u v := by ext x; rfl
  map_smul' c u := by ext x; rfl

def chartSchwartzLinear (p : M) (η : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η) :
    ManifoldSmoothFunctions E M →ₗ[ℝ] 𝓢(E, ℂ) where
  toFun u := chartSchwartz p η u hηc hs hη u.contMDiff
  map_add' u v := by
    ext y
    change chartLocalize (E := E) p η (u + v) y =
      chartLocalize (E := E) p η u y + chartLocalize (E := E) p η v y
    simp only [chartLocalize, Pi.add_apply]
    split_ifs <;> simp [mul_add]
  map_smul' c u := by
    ext y
    change chartLocalize (E := E) p η (c • u) y = c • chartLocalize (E := E) p η u y
    simp only [chartLocalize, Pi.smul_apply]
    split_ifs <;> simp [mul_left_comm]

variable {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

def atlasSobolevLocalization (s : ℝ) : ManifoldSmoothFunctions E M →ₗ[ℝ]
    (ι → FourierSobolevSpace E ℂ s) :=
  LinearMap.pi fun i =>
    ((schwartzToSobolev s).restrictScalars ℝ).toLinearMap.comp
      (chartSchwartzLinear (p i) (η i) (hηc i) (hηs i) (hηm i))

def manifoldSobolevSubmodule (s : ℝ) : Submodule ℝ (ι → FourierSobolevSpace E ℂ s) :=
  (atlasSobolevLocalization p η hηc hηs hηm s).range.topologicalClosure

abbrev ManifoldSobolev (s : ℝ) := manifoldSobolevSubmodule p η hηc hηs hηm s

instance manifoldSobolev_completeSpace (s : ℝ) :
    CompleteSpace (ManifoldSobolev p η hηc hηs hηm s) :=
  (atlasSobolevLocalization p η hηc hηs hηm s).range.isClosed_topologicalClosure.completeSpace_coe

def smoothToManifoldSobolev (s : ℝ) : ManifoldSmoothFunctions E M →ₗ[ℝ]
    ManifoldSobolev p η hηc hηs hηm s :=
  (atlasSobolevLocalization p η hηc hηs hηm s).codRestrict _ fun u =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)

omit [CompactSpace M] [Fintype ι] in
lemma denseRange_smoothToManifoldSobolev (s : ℝ) :
    DenseRange (smoothToManifoldSobolev p η hηc hηs hηm s) := by
  rw [DenseRange, Subtype.dense_iff]
  change closure ((atlasSobolevLocalization p η hηc hηs hηm s).range : Set (ι → FourierSobolevSpace E ℂ s)) ⊆ _
  apply closure_mono
  rintro y ⟨u, rfl⟩
  exact ⟨smoothToManifoldSobolev p η hηc hηs hηm s u, ⟨u, rfl⟩, rfl⟩


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
open Set Function Filter
open scoped Topology Manifold ContDiff SchwartzMap
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M]
  {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

lemma manifold_sobolev_sup_bound (hηone : ∀ x, ∑ i, η i x = 1)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) (u : ManifoldSmoothFunctions E M) :
    ‖smoothToBounded u‖ ≤ ((Fintype.card ι : ℝ) * ‖sobolevRepresentative (E := E) hs‖) *
      ‖smoothToManifoldSobolev p η hηc hηs hηm s u‖ := by
  classical
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖u x‖ ≤ _
  have hterm (i : ι) : ‖η i x * u x‖ ≤ ‖sobolevRepresentative (E := E) hs‖ *
      ‖smoothToManifoldSobolev p η hηc hηs hηm s u‖ := by
    by_cases hx : x ∈ (chartAt E (p i)).source
    · rw [← chartSchwartz_apply (p i) (η i) u (hηc i) (hηs i) (hηm i) u.contMDiff x hx]
      let v := atlasSobolevLocalization p η hηc hηs hηm s u
      have hv : (sobolevRepresentative hs (v i)) (chartAt E (p i) x) =
          chartSchwartz (p i) (η i) u (hηc i) (hηs i) (hηm i) u.contMDiff (chartAt E (p i) x) := by
        rw [show v i = schwartzToSobolev s
          (chartSchwartz (p i) (η i) u (hηc i) (hηs i) (hηm i) u.contMDiff) from rfl,
          sobolevRepresentative_schwartz]
        rfl
      rw [← hv]
      calc
        _ ≤ ‖sobolevRepresentative hs (v i)‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
        _ ≤ ‖sobolevRepresentative (E := E) hs‖ * ‖v i‖ := (sobolevRepresentative hs).le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (norm_nonneg _)
    · have hzero : η i x = 0 := by
        by_contra hn
        exact hx (hηs i (subset_tsupport (η i) hn))
      simp only [hzero, zero_mul, norm_zero]
      positivity
  have hsum : u x = ∑ i, η i x * u x := by rw [← Finset.sum_mul, hηone x, one_mul]
  rw [hsum]
  calc
    _ ≤ ∑ i, ‖η i x * u x‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, ‖sobolevRepresentative (E := E) hs‖ *
        ‖smoothToManifoldSobolev p η hηc hηs hηm s u‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

def manifoldSobolevRepresentative (s : ℝ) :
    ManifoldSobolev p η hηc hηs hηm s →L[ℝ] M →ᵇ ℂ :=
  smoothToBounded.extendOfNorm (smoothToManifoldSobolev p η hηc hηs hηm s)

lemma manifoldSobolevRepresentative_smooth (hηone : ∀ x, ∑ i, η i x = 1)
    {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) (u : ManifoldSmoothFunctions E M) :
    manifoldSobolevRepresentative p η hηc hηs hηm s
      (smoothToManifoldSobolev p η hηc hηs hηm s u) = smoothToBounded u :=
  LinearMap.extendOfNorm_eq (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s)
    ⟨_, manifold_sobolev_sup_bound p η hηc hηs hηm hηone hs⟩ u


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
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def chartLift (p : M) (χ : M → ℂ) (f : E → ℂ) (x : M) : ℂ := χ x * f (chartAt E p x)

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contMDiff_chartLift (p : M) (χ : M → ℂ)
    (hχs : tsupport χ ⊆ (chartAt E p).source)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (chartLift (E := E) p χ f) := by
  apply contMDiff_of_tsupport
  intro x hx
  have hxs : x ∈ (chartAt E p).source := hχs (tsupport_mul_subset_left hx)
  exact ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.contMDiffAt.comp x hχ.contMDiffAt).clm_apply
    ((contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hxs))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in

lemma tsupport_chartLocalize_image (p : M) (η u : M → ℂ)
    (hηc : HasCompactSupport η) (hs : tsupport η ⊆ (chartAt E p).source) :
    tsupport (chartLocalize (E := E) p η u) ⊆ (chartAt E p) '' tsupport η :=
  closure_minimal (support_chartLocalize p η u)
    (isCompact_chartSupport p η hηc hs).isClosed

omit [FiniteDimensional ℝ E] [T2Space M] in

lemma contDiffOn_chartTransition (p q : M) :
    ContDiffOn ℝ ∞ ((chartAt E p).symm.trans (chartAt E q))
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  have hy' : y ∈ (chartAt E p).target ∧ (chartAt E p).symm y ∈ (chartAt E q).source := hy
  exact (contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy'.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy'.1))).contDiffWithinAt

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma chart_overlap_cutoff_support (p q : M) (η χ : M → ℂ)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ (chartAt E p).source)
    (hχs : tsupport χ ⊆ (chartAt E q).source) :
    tsupport (chartLocalize (E := E) p (η * χ) (fun _ => 1)) ⊆
      ((chartAt E p).symm.trans (chartAt E q)).source := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_chartLocalize_image p (η * χ) (fun _ => 1)
    (hηc.mul_right (f' := χ)) (tsupport_mul_subset_left.trans hηs) hy
  have hxp := hηs (tsupport_mul_subset_left hx)
  refine ⟨(chartAt E p).map_source hxp, ?_⟩
  change (chartAt E p).symm (chartAt E p x) ∈ (chartAt E q).source
  rw [(chartAt E p).left_inv hxp]
  exact hχs (tsupport_mul_subset_right hx)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
lemma chartLocalize_chartLift (p q : M) (η χ : M → ℂ) (f : E → ℂ) (y : E) :
    chartLocalize (E := E) p η (chartLift (E := E) q χ f) y =
      chartLocalize (E := E) p (η * χ) (fun _ => 1) y *
        f (((chartAt E p).symm.trans (chartAt E q)) y) := by
  classical
  by_cases hy : y ∈ (chartAt E p).target
  · simp only [chartLocalize_eq p _ _ hy, chartLift, Pi.mul_apply, mul_one,
      OpenPartialHomeomorph.trans_apply, mul_assoc]
  · simp only [chartLocalize, ite_eq_right hy, zero_mul]


open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] {ι : Type*} [Fintype ι]
variable (p : ι → M) (η : ι → M → ℂ)
    (hηc : ∀ i, HasCompactSupport (η i))
    (hηs : ∀ i, tsupport (η i) ⊆ (chartAt E (p i)).source)
    (hηm : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (η i))

omit [CompactSpace M] in
lemma norm_smoothToManifoldSobolev_mono (s t : ℝ) (h : t ≤ s)
    (f : ManifoldSmoothFunctions E M) :
    ‖smoothToManifoldSobolev p η hηc hηs hηm t f‖ ≤
      ‖smoothToManifoldSobolev p η hηc hηs hηm s f‖ := by
  change ‖(smoothToManifoldSobolev p η hηc hηs hηm t f).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change ‖schwartzToSobolev t (chartSchwartz (p i) (η i) f (hηc i) (hηs i) (hηm i) f.contMDiff)‖ ≤ _
  exact (norm_schwartzToSobolev_mono s t h _).trans
    (norm_le_pi_norm (smoothToManifoldSobolev p η hηc hηs hηm s f).val i)

def manifoldSobolevInclusion (s t : ℝ) :
    ManifoldSobolev p η hηc hηs hηm s →L[ℝ] ManifoldSobolev p η hηc hηs hηm t :=
  (smoothToManifoldSobolev p η hηc hηs hηm t).extendOfNorm
    (smoothToManifoldSobolev p η hηc hηs hηm s)

omit [CompactSpace M] in
lemma manifoldSobolevInclusion_smooth (s t : ℝ) (h : t ≤ s)
    (f : ManifoldSmoothFunctions E M) :
    manifoldSobolevInclusion p η hηc hηs hηm s t
      (smoothToManifoldSobolev p η hηc hηs hηm s f) =
      smoothToManifoldSobolev p η hηc hηs hηm t f := by
  apply LinearMap.extendOfNorm_eq (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s)
  refine ⟨1, fun u => ?_⟩
  simpa only [one_mul] using norm_smoothToManifoldSobolev_mono p η hηc hηs hηm s t h u

omit [CompactSpace M] in
lemma norm_manifoldSobolevInclusion_le (s t : ℝ) (h : t ≤ s) :
    ‖manifoldSobolevInclusion p η hηc hηs hηm s t‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le
    (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s) zero_le_one
  intro u
  simpa only [one_mul] using norm_smoothToManifoldSobolev_mono p η hηc hηs hηm s t h u

lemma manifoldSobolevInclusion_representative (hηone : ∀ x, ∑ i, η i x = 1)
    (s t : ℝ) (h : t ≤ s) (ht : Module.finrank ℝ E < 2 * t)
    (u : ManifoldSobolev p η hηc hηs hηm s) :
    manifoldSobolevRepresentative p η hηc hηs hηm t
        (manifoldSobolevInclusion p η hηc hηs hηm s t u) =
      manifoldSobolevRepresentative p η hηc hηs hηm s u := by
  have hs : Module.finrank ℝ E < 2 * s := by linarith
  refine (denseRange_smoothToManifoldSobolev p η hηc hηs hηm s).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact (manifoldSobolevRepresentative p η hηc hηs hηm t).continuous.comp
        (manifoldSobolevInclusion p η hηc hηs hηm s t).continuous
    · exact (manifoldSobolevRepresentative p η hηc hηs hηm s).continuous
  · intro f
    rw [manifoldSobolevInclusion_smooth p η hηc hηs hηm s t h,
      manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone ht,
      manifoldSobolevRepresentative_smooth p η hηc hηs hηm hηone hs]



end

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

lemma constant_complex_product_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) (h : ℕ) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ‖iteratedFDeriv ℝ h (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  calc
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (h-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top h)))
    _ ≤ ∑ i ∈ Finset.range (h+1), (h.choose i : ℝ)*F*G := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfj i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _) hF) (hgj (h-i) (Nat.sub_le _ _))
          (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hG
    _ = 2^h*F*G := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose h

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem localized_real_chart_jet_bound (p : M) (η : M → ℂ)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ (chartAt E p).source)
    (hη : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ η) (N : ℕ) :
    ∃ C > 0, ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f →
      ∀ R : ℝ, 0 ≤ R →
      (∀ y ∈ (chartAt E p) '' tsupport η, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (f ∘ (chartAt E p).symm) y‖ ≤ R) →
      ∀ y : E, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (chartLocalize (E:=E) p η (fun x => (f x : ℂ))) y‖ ≤ C*R := by
  let K := (chartAt E p) '' tsupport η
  have hK : IsCompact K := isCompact_chartSupport (E:=E) p η hηc hηs
  let e := chartLocalize (E:=E) p η (fun _ => (1 : ℂ))
  have he : ContDiff ℝ ∞ e := contDiff_chartLocalize p η _ hηc hηs hη contMDiff_const
  obtain ⟨B,hB,hBj⟩ := compact_derivative_bound hK he N
  refine ⟨2^N*B,by positivity,?_⟩
  intro f hf R hR hfj y j hj
  let fL := chartLocalize (E:=E) p η (fun x => (f x : ℂ))
  have hsupp : tsupport fL ⊆ K :=
    closure_minimal (support_chartLocalize (E:=E) p η _) hK.isClosed
  by_cases hy : y ∈ K
  · have hyt : y ∈ (chartAt E p).target := by
      obtain ⟨x,hx,rfl⟩ := hy
      exact (chartAt E p).map_source (hηs hx)
    have hfc : ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm) (chartAt E p).target :=
      fun z hz => (contDiffAt_inChart hf p hz).contDiffWithinAt
    obtain ⟨F,hF,hFe⟩ := smooth_extension_at (chartAt E p).open_target hyt hfc
    have hfLe : fL =ᶠ[𝓝 y] (fun z => e z*(F z : ℂ)) := by
      filter_upwards [(chartAt E p).open_target.mem_nhds hyt,hFe] with z hz hFz
      simp only [fL,e,chartLocalize_eq p η _ hz,mul_one]
      rw [← hFz]
      rfl
    rw [(hfLe.iteratedFDeriv ℝ j).self_of_nhds]
    have hFj (l : ℕ) (hl : l ≤ j) :
        ‖iteratedFDeriv ℝ l (fun z => (F z : ℂ)) y‖ ≤ R := by
      change ‖iteratedFDeriv ℝ l (Complex.ofRealLI ∘ F) y‖ ≤ R
      rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hF.contDiffAt
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top l))),
        ← (hFe.iteratedFDeriv ℝ l).self_of_nhds]
      exact hfj y hy l (hl.trans hj)
    apply (constant_complex_product_jet_bound he (Complex.ofRealCLM.contDiff.comp hF)
      y j (zero_le_one.trans hB) hR
      (fun l hl => hBj l (hl.trans hj) y hy) hFj).trans
    gcongr; norm_num
  · have hn : y ∉ tsupport (iteratedFDeriv ℝ j fL) :=
      fun h => hy (hsupp (tsupport_iteratedFDeriv_subset j h))
    rw [image_eq_zero_of_notMem_tsupport hn,norm_zero]
    positivity


end YauCounterexamples
end

end OAI
