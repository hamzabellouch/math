import Mathlib
import OAI.Geometry.SmoothYau.Estimates.LocalIntegrationPartsC1
import OAI.Geometry.SmoothYau.Limits.IntegrableCompactTsupport
import OAI.Geometry.SmoothYau.Smoothness.ContDiffMetricFluxC1

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
section GradientPairCalculus
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_symm (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x = coordinateGradientPair g v u x := by
  have hs (i j : CoordIndex E) : (metricCoefficients g x ((chartAt E x) x))⁻¹ j i =
      (metricCoefficients g x ((chartAt E x) x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x ((chartAt E x).map_source (mem_chart_source E x))).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  unfold coordinateGradientPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]
  ring

lemma coordinateGradientPair_zero_off_support (g : SmoothMetric E M) (u v : M → ℝ)
    {x : M} (hx : x ∉ tsupport u) : coordinateGradientPair g u v x = 0 := by
  have hzero : u =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have hc : Tendsto (chartAt E x).symm (𝓝 ((chartAt E x) x)) (𝓝 x) := by
    have hh := (chartAt E x).continuousOn_symm.continuousAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source (mem_chart_source E x)))
    simpa only [ContinuousAt, (chartAt E x).left_inv (mem_chart_source E x)] using hh
  have he : (u ∘ (chartAt E x).symm) =ᶠ[𝓝 ((chartAt E x) x)] (fun _ => (0 : ℝ)) :=
    hzero.comp_tendsto hc
  simp only [coordinateGradientPair, he.fderiv_eq, fderiv_const_apply, _root_.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero]

lemma tsupport_coordinateGradientPair_left (g : SmoothMetric E M) (u v : M → ℝ) :
    tsupport (coordinateGradientPair g u v) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (coordinateGradientPair_zero_off_support g u v hn)

lemma coordinateGradientPair_fintype_sum {ι : Type*} [Fintype ι]
    (g : SmoothMetric E M) (f : ι → M → ℝ)
    (hf : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f a)) (v : M → ℝ) (x : M) :
    coordinateGradientPair g (fun y => ∑ a, f a y) v x =
      ∑ a, coordinateGradientPair g (f a) v x := by
  have hd : fderiv ℝ ((fun y => ∑ a, f a y) ∘ (chartAt E x).symm) ((chartAt E x) x) =
      ∑ a, fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) :=
    fderiv_fun_sum (fun a _ => (contDiffAt_inChart (hf a) x
      ((chartAt E x).map_source (mem_chart_source E x))).differentiableAt (by simp))
  simp only [coordinateGradientPair, hd, _root_.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a : ι, ∑ j, (metricCoefficients g x ((chartAt E x) x))⁻¹ i j *
        fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i) *
        fderiv ℝ (v ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm
end GradientPairCalculus

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
   [CompactSpace M]
namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

def mean (f : M → ℝ) : ℝ :=
  ∑ i : A.t, metricChartIntegral g (i : M) (fun x => A.ρ i x * f x)

lemma mean_eq_integral (f : M → ℝ) (hf : Continuous f) :
    A.mean g f = A.integralCLM g (BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩) := rfl

lemma mean_fintype_sum {ι : Type*} [Fintype ι] (f : ι → M → ℝ)
    (hf : ∀ i, Continuous (f i)) : A.mean g (fun x => ∑ i, f i x) = ∑ i, A.mean g (f i) := by
  let F (i : ι) : M →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f i,hf i⟩
  have he : (fun x => ∑ i, f i x) = (⇑(∑ i, F i)) := by funext x; simp [F]
  rw [he]
  change A.integralCLM g (∑ i, F i) = _
  rw [map_sum]
  rfl

lemma mean_eq_chart (p : M) (f : M → ℝ) (hf : Continuous f)
    (hs : tsupport f ⊆ (chartAt E p).source) : A.mean g f = metricChartIntegral g p f :=
  A.integral_eq_chart g p (BoundedContinuousFunction.mkOfCompact ⟨f,hf⟩) hs

theorem green {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) :
    A.mean g (fun x => u x * laplaceBeltrami g v x) =
      -A.mean g (coordinateGradientPair g u v) := by
  let f (i : A.t) (x : M) := A.ρ i x * u x
  have hf (i : A.t) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (f i) := (A.ρ i).property.mul hu
  have hs (i : A.t) : tsupport (f i) ⊆ (chartAt E (i : M)).source :=
    tsupport_mul_subset_left.trans (A.subordinate i)
  have hsum : (fun x => ∑ i : A.t, f i x) = u := by
    funext x
    dsimp only [f]
    rw [← Finset.sum_mul]
    have hρ : ∑ i : A.t, A.ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using A.ρ.sum_eq_one (mem_univ x)
    rw [hρ, one_mul]
  calc
    _ = ∑ i : A.t, metricChartIntegral g (i : M) (fun x => f i x * laplaceBeltrami g v x) := by
      unfold mean
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext x
      dsimp [f]
      ring
    _ = -(∑ i : A.t, metricChartIntegral g (i : M) (coordinateGradientPair g (f i) v)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact metricChartIntegral_green g _ (hf i) hv (HasCompactSupport.of_compactSpace _) (hs i)
    _ = -(∑ i : A.t, A.mean g (coordinateGradientPair g (f i) v)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (A.mean_eq_chart g (i : M) _ (contMDiff_coordinateGradientPair (hf i) hv g).continuous
        ((tsupport_coordinateGradientPair_left g (f i) v).trans (hs i))).symm
    _ = -A.mean g (coordinateGradientPair g u v) := by
      rw [← A.mean_fintype_sum g _ (fun i => (contMDiff_coordinateGradientPair (hf i) hv g).continuous)]
      congr 2
      funext x
      rw [← coordinateGradientPair_fintype_sum g f hf v x, hsum]

theorem laplacian_symmetric {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) :
    A.mean g (fun x => u x * laplaceBeltrami g v x) =
      A.mean g (fun x => laplaceBeltrami g u x * v x) := by
  rw [A.green g hu hv]
  have he : coordinateGradientPair g u v = coordinateGradientPair g v u :=
    funext (coordinateGradientPair_symm g u v)
  rw [he, ← A.green g hv hu]
  congr 1
  funext x
  ring
end MetricIntegralAtlas

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [T2Space M] in

theorem metricChartIntegral_green_C2 (g : SmoothMetric E M) (p : M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v)
    (huc : HasCompactSupport u) (hus : tsupport u ⊆ (chartAt E p).source) :
    metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      -metricChartIntegral g p (coordinateGradientPair g u v) := by
  let f := realChartLocalize (E := E) p u
  let O := (chartAt E p).target
  let b := Module.finBasis ℝ E
  have hf : ContDiff ℝ 2 f := contDiff_realChartLocalize_C2 p u huc hus hu
  have hfc : HasCompactSupport f := hasCompactSupport_realChartLocalize p u huc hus
  have hfs : tsupport f ⊆ O := tsupport_realChartLocalize_subset p u huc hus
  have hflux (i : CoordIndex E) : ContDiffOn ℝ 1 (fun y => metricFlux g v p y i) O :=
    fun y hy => (contDiffAt_metricFlux_C1 hv g p hy i).contDiffWithinAt
  have hdf (i : CoordIndex E) : ContDiff ℝ 1 (fun y => fderiv ℝ f y (b i)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hFi (i : CoordIndex E) : IntegrableOn (fun y => f y *
      fderiv ℝ (fun z => metricFlux g v p z i) y (b i)) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · apply hf.continuous.continuousOn.mul
      intro y hy
      exact (((contDiffAt_metricFlux_C1 hv g p hy i).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const).continuousAt.continuousWithinAt
    · exact hfc.mul_right
    · exact tsupport_mul_subset_left.trans hfs
  have hGi (i : CoordIndex E) : IntegrableOn (fun y => fderiv ℝ f y (b i) * metricFlux g v p y i) O := by
    apply integrableOn_compact_tsupport (chartAt E p).open_target
    · exact (hdf i).continuous.continuousOn.mul (hflux i).continuousOn
    · exact (hfc.fderiv_apply ℝ (b i)).mul_right
    · exact tsupport_mul_subset_left.trans ((tsupport_fderiv_apply_subset ℝ (b i)).trans hfs)
  have hleft : metricChartIntegral g p (fun x => u x * laplaceBeltrami g v x) =
      ∫ y in O, ∑ i, f y * fderiv ℝ (fun z => metricFlux g v p z i) y (b i) := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [laplaceBeltrami_inChart_C2 hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    simp only [localLaplacian, ← Finset.mul_sum]
    rw [show f y = u ((chartAt E p).symm y) from realChartLocalize_eq p u hy]
    have hd : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
      (Real.sqrt_pos.2 (metricCoefficients_posDef g p hy).det_pos).ne'
    dsimp only [b]
    field_simp
  have hright : metricChartIntegral g p (coordinateGradientPair g u v) =
      ∫ y in O, ∑ i, fderiv ℝ f y (b i) * metricFlux g v p y i := by
    apply setIntegral_congr_fun (chartAt E p).open_target.measurableSet
    intro y hy
    dsimp only
    rw [coordinateGradientPair_inChart_C2 hu hv g p _ ((chartAt E p).map_target hy),
      (chartAt E p).right_inv hy]
    dsimp only [f]
    rw [realChartLocalize_fderiv p u hy]
    simp only [localGradientPair, metricFlux, Matrix.mulVec, dotProduct, Finset.mul_sum, b]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  rw [hleft, hright, integral_finsetSum _ (fun i _ => hFi i),
    integral_finsetSum _ (fun i _ => hGi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact local_integration_by_parts_C1 (chartAt E p).open_target (hf.of_le (by norm_num)) hfc hfs (hflux i) (b i)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_fintype_sum_C2 {ι : Type*} [Fintype ι]
    (g : SmoothMetric E M) (f : ι → M → ℝ)
    (hf : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (f a)) (v : M → ℝ) (x : M) :
    coordinateGradientPair g (fun y => ∑ a, f a y) v x =
      ∑ a, coordinateGradientPair g (f a) v x := by
  have hd : fderiv ℝ ((fun y => ∑ a, f a y) ∘ (chartAt E x).symm) ((chartAt E x) x) =
      ∑ a, fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) :=
    fderiv_fun_sum (fun a _ => (contDiffAt_inChart_C2 (hf a) x
      ((chartAt E x).map_source (mem_chart_source E x))).differentiableAt (by simp))
  simp only [coordinateGradientPair, hd, _root_.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a : ι, ∑ j, (metricCoefficients g x ((chartAt E x) x))⁻¹ i j *
        fderiv ℝ (f a ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i) *
        fderiv ℝ (v ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
   [CompactSpace M]
namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

theorem green_C2 {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) :
    A.mean g (fun x => u x * laplaceBeltrami g v x) =
      -A.mean g (coordinateGradientPair g u v) := by
  let f (i : A.t) (x : M) := A.ρ i x * u x
  have hf (i : A.t) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (f i) := ((A.ρ i).property.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).mul hu
  have hs (i : A.t) : tsupport (f i) ⊆ (chartAt E (i : M)).source :=
    tsupport_mul_subset_left.trans (A.subordinate i)
  have hsum : (fun x => ∑ i : A.t, f i x) = u := by
    funext x
    dsimp only [f]
    rw [← Finset.sum_mul]
    have hρ : ∑ i : A.t, A.ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using A.ρ.sum_eq_one (mem_univ x)
    rw [hρ, one_mul]
  calc
    _ = ∑ i : A.t, metricChartIntegral g (i : M) (fun x => f i x * laplaceBeltrami g v x) := by
      unfold mean
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext x
      dsimp [f]
      ring
    _ = -(∑ i : A.t, metricChartIntegral g (i : M) (coordinateGradientPair g (f i) v)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact metricChartIntegral_green_C2 g _ (hf i) hv (HasCompactSupport.of_compactSpace _) (hs i)
    _ = -(∑ i : A.t, A.mean g (coordinateGradientPair g (f i) v)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (A.mean_eq_chart g (i : M) _ (contMDiff_coordinateGradientPair_C1 (hf i) hv g).continuous
        ((tsupport_coordinateGradientPair_left g (f i) v).trans (hs i))).symm
    _ = -A.mean g (coordinateGradientPair g u v) := by
      rw [← A.mean_fintype_sum g _ (fun i => (contMDiff_coordinateGradientPair_C1 (hf i) hv g).continuous)]
      congr 2
      funext x
      rw [← coordinateGradientPair_fintype_sum_C2 g f hf v x, hsum]

theorem laplacian_symmetric_C2 {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) :
    A.mean g (fun x => u x * laplaceBeltrami g v x) =
      A.mean g (fun x => laplaceBeltrami g u x * v x) := by
  rw [A.green_C2 g hu hv]
  have he : coordinateGradientPair g u v = coordinateGradientPair g v u :=
    funext (coordinateGradientPair_symm g u v)
  rw [he, ← A.green_C2 g hv hu]
  congr 1
  funext x
  ring
end MetricIntegralAtlas

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
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma coordinateGradientPair_scalar_correction {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => 1 - f y * u y) u x =
      - f x * coordinateGradientPair g u u x - u x * coordinateGradientPair g f u x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have hf' := (contDiffAt_inChart hf x hx).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu x hx).differentiableAt (by simp)
  have he : ((fun y => 1 - f y * u y) ∘ c.symm) =
      fun y => 1 - (f ∘ c.symm) y * (u ∘ c.symm) y := rfl
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ ((fun y => 1 - f y * u y) ∘ c.symm) (c x) _ * _) = _
  rw [he]
  erw [fderiv_fun_sub (f := fun _ => (1 : ℝ))
    (g := fun y => (f ∘ c.symm) y * (u ∘ c.symm) y)
    (differentiableAt_const _) (hf'.mul hu'),
    fderiv_fun_mul hf' hu', fderiv_const]
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul, Function.comp_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [c]
  simp only [_root_.zero_apply, (chartAt E x).left_inv (mem_chart_source E x)]
  ring

lemma contMDiff_weightedLaplacian {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (weightedLaplacian g b u) := by
  have he : weightedLaplacian g b u = fun x =>
      b x * laplaceBeltrami g u x + coordinateGradientPair g b u x := by
    funext x
    exact weightedLaplacian_expansion (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) g x
  rw [he]
  exact (hb.mul (contMDiff_laplaceBeltrami hu g)).add
    (contMDiff_coordinateGradientPair hb hu g)

def intrinsicCorrectionD (g : SmoothMetric E M) (n : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  n ^ 2 * u x ^ 2 + coordinateGradientPair g u u x

def intrinsicCorrectionF (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  (laplaceBeltrami g u x + Λ * u x) / intrinsicCorrectionD g n u x

def intrinsicCorrectionB (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  1 - intrinsicCorrectionF g n Λ u x * u x

def intrinsicCorrectionS (g : SmoothMetric E M) (n Λ : ℝ) (u : M → ℝ) (x : M) : ℝ :=
  1 - Λ⁻¹ * (n ^ 2 * intrinsicCorrectionF g n Λ u x * u x -
    weightedLaplacian g (intrinsicCorrectionF g n Λ u) u x)

lemma contMDiff_intrinsicCorrectionF {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionF g n Λ u) := by
  exact ((contMDiff_laplaceBeltrami hu g).add (contMDiff_const.mul hu)).div₀
    ((contMDiff_const.mul (hu.pow 2)).add (contMDiff_coordinateGradientPair hu hu g)) hD

theorem intrinsic_scalar_correction {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) (n Λ : ℝ)
    (hΛ : Λ ≠ 0) (hD : ∀ x, intrinsicCorrectionD g n u x ≠ 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionB g n Λ u) ∧
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionS g n Λ u) ∧
    ∀ x, weightedLaplacian g (intrinsicCorrectionB g n Λ u) u x +
      Λ * intrinsicCorrectionS g n Λ u x * u x = 0 := by
  let f := intrinsicCorrectionF g n Λ u
  have hf := contMDiff_intrinsicCorrectionF hu g n Λ hD
  have hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionB g n Λ u) :=
    contMDiff_const.sub (hf.mul hu)
  have hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (intrinsicCorrectionS g n Λ u) :=
    contMDiff_const.sub (contMDiff_const.mul
      (((contMDiff_const.mul hf).mul hu).sub (contMDiff_weightedLaplacian hf hu g)))
  refine ⟨hb, hs, fun x => ?_⟩
  rw [weightedLaplacian_expansion (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  change (1 - f x * u x) * laplaceBeltrami g u x +
    coordinateGradientPair g (fun y => 1 - f y * u y) u x +
    Λ * (1 - Λ⁻¹ * (n ^ 2 * f x * u x - weightedLaplacian g f u x)) * u x = 0
  rw [coordinateGradientPair_scalar_correction hf hu,
    weightedLaplacian_expansion (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  have hprod : f x * (n ^ 2 * u x ^ 2 + coordinateGradientPair g u u x) =
      laplaceBeltrami g u x + Λ * u x := div_mul_cancel₀ _ (hD x)
  field_simp
  nlinarith [hprod]

lemma coordinateGradientPair_mul_left {f u : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (v : M → ℝ) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => f y * u y) v x =
      f x * coordinateGradientPair g u v x + u x * coordinateGradientPair g f v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have hf' := (contDiffAt_inChart hf x hx).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu x hx).differentiableAt (by simp)
  have he : ((fun y => f y * u y) ∘ c.symm) =
      fun y => (f ∘ c.symm) y * (u ∘ c.symm) y := rfl
  unfold coordinateGradientPair
  change (∑ i, ∑ j, _ * fderiv ℝ ((fun y => f y * u y) ∘ c.symm) (c x) _ * _) = _
  rw [he]
  erw [fderiv_fun_mul hf' hu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    Function.comp_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [c]
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  ring

lemma intrinsic_conjugation_product {b v w : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g (fun y => b y * v y ^ 2) w x =
      v x * weightedLaplacian g b (fun y => v y * w y) x -
        (v x * w x) * weightedLaplacian g b v x := by
  have hb2 := hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv2 := hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hw2 := hw.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h₁ := weightedLaplacian_expansion (hb2.mul (hv2.pow 2)) hw2 g x
  have h₂ := weightedLaplacian_expansion hb2 (hv2.mul hw2) g x
  have h₃ := weightedLaplacian_expansion hb2 hv2 g x
  have h₄ := laplaceBeltrami_mul hv2 hw2 g x
  change laplaceBeltrami g (v * w) x = _ at h₄
  have h₅ := coordinateGradientPair_mul_left hb (hv.pow 2) w g x
  change coordinateGradientPair g (b * fun y => v y ^ 2) w x = _ at h₅
  have h₆ := coordinateGradientPair_mul_left hv hv w g x
  change coordinateGradientPair g (v * v) w x = _ at h₆
  have he : (fun y => v y ^ 2) = v * v := by funext y; simp only [Pi.mul_apply]; ring
  have h₇ := coordinateGradientPair_mul_left hv hw b g x
  change coordinateGradientPair g (v * w) b x = _ at h₇
  have h₈ := coordinateGradientPair_symm g b (v * w) x
  have h₉ := coordinateGradientPair_symm g w b x
  have h₁₀ := coordinateGradientPair_symm g v b x
  change weightedLaplacian g (b * fun y => v y ^ 2) w x =
    v x * weightedLaplacian g b (v * w) x -
      (v x * w x) * weightedLaplacian g b v x
  rw [h₁, h₂, h₃, h₄, h₅, h₈, h₇, h₉, h₁₀]
  rw [he]
  rw [h₆]
  simp only [Pi.mul_apply]
  ring

theorem intrinsic_conjugated_equation {b s U v : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ U)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M)
    {Λ : ℝ} (hΛ : Λ ≠ 0) (hv0 : ∀ x, v x ≠ 0)
    (hweighted : ∀ x, weightedLaplacian g b U x + Λ * s x * U x = 0) :
    ∀ x, weightedLaplacian g (fun y => b y * v y ^ 2) (fun y => U y / v y) x +
      Λ * (s x * v x ^ 2 + Λ⁻¹ * v x * weightedLaplacian g b v x) * (U x / v x) = 0 := by
  intro x
  have hw := hU.div₀ hv hv0
  have he : (fun y => v y * (U y / v y)) = U := by
    funext y
    field_simp [hv0 y]
  erw [intrinsic_conjugation_product hb hv hw, he]
  simp only [Pi.div_apply]
  calc
    _ = v x * (weightedLaplacian g b U x + Λ * s x * U x) := by
      field_simp [hv0 x, hΛ]
      ring
    _ = 0 := by rw [hweighted x, mul_zero]

theorem conformal_exactification {b s U v : M → ℝ}
    (hd : Module.finrank ℝ E = 3)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (hU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ U)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M)
    {Λ : ℝ} (hΛ : Λ ≠ 0) (hb0 : ∀ x, 0 < b x) (hv0 : ∀ x, 0 < v x)
    (hweighted : ∀ x, weightedLaplacian g b U x + Λ * s x * U x = 0)
    (hfactor : ∀ x, weightedLaplacian g b v x = Λ * b x ^ 3 * v x ^ 5 - Λ * s x * v x) :
    ∃ ĝ : SmoothMetric E M, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ x, -laplaceBeltrami ĝ u x = Λ * u x) ∧
      (∀ x, u x = U x / v x) ∧ (∀ x, u x = 0 ↔ U x = 0) := by
  let q := fun x => b x * v x ^ 2
  have hq : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ q := hb.mul (hv.pow 2)
  have hq0 : ∀ x, 0 < q x := fun x => mul_pos (hb0 x) (sq_pos_of_pos (hv0 x))
  let u := fun x => U x / v x
  refine ⟨conformalMetric g q hq hq0, u, hU.div₀ hv (fun x => (hv0 x).ne'), ?_,
    fun _ => rfl, fun x => ?_⟩
  · intro x
    have he := intrinsic_conjugated_equation hb hU hv g hΛ (fun x => (hv0 x).ne') hweighted x
    rw [hfactor x] at he
    rw [conformalMetric_laplacian_three hd]
    dsimp only [q, u] at he ⊢
    have hbn := (hb0 x).ne'
    have hvn := (hv0 x).ne'
    field_simp at he ⊢
    nlinarith [he]
  · change U x / v x = 0 ↔ U x = 0
    simp [(hv0 x).ne']



end YauCounterexamples
end

end OAI
