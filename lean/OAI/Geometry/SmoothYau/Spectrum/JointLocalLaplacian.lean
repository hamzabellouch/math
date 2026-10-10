import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.JointMetricDet
import OAI.Geometry.SmoothYau.Smoothness.ZeroJetProd

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma differentiableAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    DifferentiableAt ℝ (metricFlux g u p) y := by
  apply differentiableAt_pi.mpr
  intro i
  have hd := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  apply hd.mul
  apply DifferentiableAt.fun_sum
  intro j _
  have ha := ((contDiffOn_metricInverse g p i j).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hu' := ((contDiffAt_inChart hu p hy).fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiableAt one_ne_zero
  exact ha.mul (hu'.clm_apply (differentiableAt_const _))

lemma localLaplacian_change {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localLaplacian g u q y = localLaplacian g u p (chartTransition p q y) := by
  classical
  have he (i : CoordIndex E) : (fun z => metricFlux g u q z i) =ᶠ[𝓝 y]
      (fun z => ∑ k, |(coordinateTransitionMatrix p q z).det| *
        (coordinateTransitionMatrix p q z)⁻¹ i k * metricFlux g u p (chartTransition p q z) k) := by
    filter_upwards [chart_overlap_nhds p q hy hp] with z hz
    exact metricFlux_change hu g p q hz.1 hz.2 i
  have hJ : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  have hi := piola_divergence_abs ((contDiffAt_chartTransition p q hy hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (differentiableAt_metricFlux hu g p ((chartAt E p).map_source hp))
    (Module.finBasis ℝ E) hJ
  change (∑ i, fderiv ℝ (fun z => ∑ k, |(coordinateTransitionMatrix p q z).det| *
    (coordinateTransitionMatrix p q z)⁻¹ i k * metricFlux g u p (chartTransition p q z) k) y
      (Module.finBasis ℝ E i)) = _ at hi
  simp only [localLaplacian, (he _).fderiv_eq]
  rw [hi, metricDensity_change g p q hy hp]
  have hn := abs_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  change (|(coordinateTransitionMatrix p q y).det| * _)⁻¹ *
    (|(coordinateTransitionMatrix p q y).det| * _) = _
  field_simp

lemma laplaceBeltrami_inChart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p x : M) (hx : x ∈ (chartAt E p).source) :
    laplaceBeltrami g u x = localLaplacian g u p (chartAt E p x) := by
  change localLaplacian g u x (chartAt E x x) = _
  have he := localLaplacian_change hu g p x ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  simpa only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)] using he

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma contDiffAt_metricFlux {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    ContDiffAt ℝ ∞ (fun z => metricFlux g u p z i) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  apply hd.mul
  apply ContDiffAt.sum
  intro j _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hv := (contDiffAt_inChart hu p hy).fderiv_right (m := ∞) (by simp)
  exact ha.mul (hv.clm_apply contDiffAt_const)

lemma contDiffAt_localLaplacian {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (localLaplacian g u p) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_metricFlux hu g p hy i).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma contMDiff_laplaceBeltrami {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (laplaceBeltrami g u) := by
  intro x
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  apply (contDiffAt_localLaplacian hu g x hx).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_target.mem_nhds hx] with y hy
  have he := laplaceBeltrami_inChart hu g x ((chartAt E x).symm y) ((chartAt E x).map_target hy)
  simpa only [Function.comp_apply, (chartAt E x).right_inv hy] using he

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp [Euclidean]⟩

variable (g : SmoothMetric (Euclidean n) (Sphere n))
variable (hg : ∀ (p : Sphere n) (v w : TangentSpace 𝓘(ℝ,Euclidean n) p),
  g.inner p v w = (inner ℝ : Euclidean (n+1) → Euclidean (n+1) → ℝ)
    (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean (n+1))
      (fun q : Sphere n => (q : Euclidean (n+1))) p v)
    (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean (n+1))
      (fun q : Sphere n => (q : Euclidean (n+1))) p w))

include hg

lemma round_metricCoefficients (p : Sphere n) (y : Euclidean n) (i j : CoordIndex (Euclidean n)) :
    metricCoefficients g p y i j =
      inner ℝ (fderiv ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p)) y (Module.finBasis ℝ (Euclidean n) i))
        (fderiv ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p)) y (Module.finBasis ℝ (Euclidean n) j)) := by
  rw [metricCoefficients,hg]
  simp only [coordinateVector,sphere_coordinate_embedding]

lemma round_metricCoefficients_zero (p : Sphere n) :
    metricCoefficients g p 0 = Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)) := by
  ext i j
  rw [round_metricCoefficients g hg,(roundChart_first _ _).fderiv]
  exact (sphereFrame p).inner_map_map _ _

lemma round_metricCoefficients_first (p : Sphere n) (i j : CoordIndex (Euclidean n)) :
    HasFDerivAt (fun y => metricCoefficients g p y i j) (0 : Euclidean n →L[ℝ] ℝ) 0 := by
  simp_rw [round_metricCoefficients g hg]
  exact roundChart_metric_first _ _ (sphereFrame_orthogonal p) _ _

lemma round_metricFirstCoefficient_zero (p : Sphere n) (j : CoordIndex (Euclidean n)) :
    metricFirstCoefficient g p j 0 = 0 := by
  have hn : (metricCoefficients g p 0).det ≠ 0 :=
    (metricCoefficients_det_pos g p (by rw [sphere_chart_target]; trivial)).ne'
  have hh := fun i => (zero_jet_density_inverse (metricCoefficients g p)
    (round_metricCoefficients_first g hg p) hn i j).fderiv
  simp only [metricFirstCoefficient,hh,_root_.zero_apply,Finset.sum_const_zero,mul_zero]

theorem round_laplace_at_center (u : Sphere n → ℝ)
    (hu : ContMDiff 𝓘(ℝ,Euclidean n) 𝓘(ℝ,ℝ) ∞ u) (p : Sphere n) :
    laplaceBeltrami g u p = ∑ i, ∑ j,
      (Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (u ∘ (chartAt (Euclidean n) p).symm) y
        (Module.finBasis ℝ (Euclidean n) j)) 0 (Module.finBasis ℝ (Euclidean n) i) := by
  rw [laplaceBeltrami_inChart hu g p p (mem_chart_source _ _),sphere_chart_center,
    localLaplacian_expansion hu g p (by rw [sphere_chart_target]; trivial)]
  simp only [round_metricCoefficients_zero g hg,round_metricFirstCoefficient_zero g hg,
    zero_mul,Finset.sum_const_zero,add_zero]



end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

def roundPower (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) : ℝ :=
  ((planarLinear a b (p : Euclidean (d+1)))^k).re

lemma roundPower_smooth (a b : Euclidean (d+1)) (k : ℕ) :
    ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (roundPower a b k) := by
  have hc : ContDiff ℝ ∞ (fun x : Euclidean (d+1) => (planarLinear a b x)^k) :=
    (planarLinear a b).contDiff.pow k
  exact (Complex.reCLM.contDiff.comp hc).contMDiff.comp contMDiff_coe_sphere

lemma complex_inverse_gram_trace :
    ∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
      (inner ℝ (Module.finBasis ℝ (Euclidean d) j) (Module.finBasis ℝ (Euclidean d) i) : ℂ) = (d:ℂ) := by
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum,real_inner_comm
    (Module.finBasis ℝ (Euclidean d) _) (Module.finBasis ℝ (Euclidean d) _)]
  rw [inverse_gram_trace]
  simp [Euclidean]

lemma roundPower_complex_hessian_trace (a b : Euclidean (d+1)) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d) :
    ∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
      ((k:ℂ) * ((k:ℂ)-1) * (planarLinear a b p)^(k-2) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) i)) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) j)) -
        (k:ℂ) * (planarLinear a b p)^k *
          (inner ℝ (Module.finBasis ℝ (Euclidean d) j) (Module.finBasis ℝ (Euclidean d) i) : ℂ)) =
      -(k:ℂ) * ((k:ℂ)+(d:ℂ)-1) * (planarLinear a b p)^k := by
  let z := planarLinear a b (p : Euclidean (d+1))
  calc
    _ = (k:ℂ) * ((k:ℂ)-1) * z^(k-2) *
        (∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) j)) *
          planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean d) i))) -
        (k:ℂ) * z^k * (∑ i, ∑ j,
          ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)))⁻¹ i j : ℂ) *
          (inner ℝ (Module.finBasis ℝ (Euclidean d) j) (Module.finBasis ℝ (Euclidean d) i) : ℂ)) := by
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [z]
      ring
    _ = -(k:ℂ) * ((k:ℂ)+(d:ℂ)-1) * z^k := by
      rw [sphere_planar_contraction p a b ha hb hab,complex_inverse_gram_trace]
      have hp : z^(k-2) * z^2 = z^k := by rw [← pow_add,Nat.sub_add_cancel hk]
      change (k:ℂ) * ((k:ℂ)-1) * z^(k-2) * -(z^2) - (k:ℂ) * z^k * (d:ℂ) = _
      rw [mul_neg, mul_assoc ((k:ℂ) * ((k:ℂ)-1)), hp]
      ring

variable (g : SmoothMetric (Euclidean d) (Sphere d))
variable (hg : ∀ (p : Sphere d) (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
  g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
    (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
      (fun q : Sphere d => (q : Euclidean (d+1))) p v)
    (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
      (fun q : Sphere d => (q : Euclidean (d+1))) p w))

include hg

theorem roundPower_eigen (a b : Euclidean (d+1)) (k : ℕ) (hk : 2 ≤ k)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) (p : Sphere d) :
    -laplaceBeltrami g (roundPower a b k) p =
      (k:ℝ) * ((k:ℝ)+(d:ℝ)-1) * roundPower a b k p := by
  rw [round_laplace_at_center g hg _ (roundPower_smooth a b k)]
  have hc : roundPower a b k ∘ (chartAt (Euclidean d) p).symm =
      fun z => ((planarLinear a b (roundChart (p : Euclidean (d+1)) (sphereFrame p) z))^k).re := by
    funext z
    simp only [roundPower,Function.comp_apply]
    rw [← sphere_chart_symm]
  simp_rw [hc,roundLinearPower_real_second _ k hk]
  have ht := congrArg Complex.re (roundPower_complex_hessian_trace a b k hk ha hb hab p)
  simp only [Complex.re_sum,Complex.re_ofReal_mul] at ht
  rw [ht]
  have hcast : -(k:ℂ) * ((k:ℂ)+(d:ℂ)-1) =
      ((-(k:ℝ) * ((k:ℝ)+(d:ℝ)-1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast,Complex.re_ofReal_mul]
  dsimp [roundPower]
  ring


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


theorem laplaceBeltrami_chart_metric (g : SmoothMetric E M) (ĝ : SmoothMetric E E)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) {u : M → ℝ} {f : E → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hg : ∀ᶠ z in 𝓝 y, ∀ v w : E, ĝ.inner z v w = g.inner ((chartAt E p).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z w))
    (hf : u ∘ (chartAt E p).symm =ᶠ[𝓝 y] f) :
    laplaceBeltrami g u ((chartAt E p).symm y) = laplaceBeltrami ĝ f y := by
  rw [laplaceBeltrami_inChart hu g p _ ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]
  have ha : metricCoefficients ĝ y =ᶠ[𝓝 y] metricCoefficients g p := by
    filter_upwards [hg] with z hz
    ext i j
    rw [metricCoefficients_self]
    exact hz _ _
  have hflux : ∀ i, (fun z => metricFlux g u p z i) =ᶠ[𝓝 y]
      (fun z => metricFlux ĝ f y z i) := by
    intro i
    filter_upwards [ha, hf.fderiv (𝕜 := ℝ)] with z hz hdz
    simp only [metricFlux, hz, hdz, chartAt_self_eq, OpenPartialHomeomorph.refl_symm]
    rfl
  change localLaplacian g u p y = localLaplacian ĝ f y y
  simp only [localLaplacian, ← ha.eq_of_nhds]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(hflux i).fderiv_eq]

theorem laplaceBeltrami_manifoldChartPush [T2Space M]
    (g : SmoothMetric E M) (ĝ : SmoothMetric E E) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt E p).target)
    (hg : ∀ᶠ z in 𝓝 y, ∀ v w : E, ĝ.inner z v w = g.inner ((chartAt E p).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm z w)) :
    laplaceBeltrami g (manifoldChartPush p f) ((chartAt E p).symm y) =
      laplaceBeltrami ĝ f y := by
  apply laplaceBeltrami_chart_metric g ĝ p hy (contMDiff_manifoldChartPush p hf hc hs) hg
  filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
  exact manifoldChartPush_apply p f hz

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
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
section MetricLocality
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_metric_congr_nhds (g g' : SmoothMetric E M) (u : M → ℝ) {x : M}
    (he : ∀ᶠ z in 𝓝 x, ∀ v w : TangentSpace 𝓘(ℝ,E) z, g.inner z v w = g'.inner z v w) :
    laplaceBeltrami g u x = laplaceBeltrami g' u x := by
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source E x)] using (c.continuousAt_symm hx).tendsto
  have hc : metricCoefficients g x =ᶠ[𝓝 (c x)] metricCoefficients g' x := by
    filter_upwards [ht.eventually he] with y hy
    funext i j
    exact hy _ _
  have hf (i : CoordIndex E) : (fun y => metricFlux g u x y i) =ᶠ[𝓝 (c x)]
      (fun y => metricFlux g' u x y i) := by
    filter_upwards [hc] with y hy
    simp only [metricFlux,hy]
  change (Real.sqrt (metricCoefficients g x (c x)).det)⁻¹ *
    ∑ i, fderiv ℝ (fun y => metricFlux g u x y i) (c x) (Module.finBasis ℝ E i) = _
  rw [hc.self_of_nhds]
  simp_rw [(hf _).fderiv_eq]
  rfl
end MetricLocality

variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_residual_tsupport
    (g g₀ : SmoothMetric (Euclidean d) (Sphere d))
    (hg₀ : ∀ (p : Sphere d) (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g₀.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
          (fun q : Sphere d => (q : Euclidean (d+1))) p w))
    {K : Set (Sphere d)} (hK : IsClosed K)
    (hext : ∀ p ∉ K, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) p, g.inner p v w = g₀.inner p v w)
    (a b : Euclidean (d+1)) (n : ℕ) (hn : 2 ≤ n)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    tsupport (fun z => laplaceBeltrami g (roundPower a b n) z +
      (n:ℝ)*((n:ℝ)+(d:ℝ)-1)*roundPower a b n z) ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hzK
  have hagree : ∀ᶠ p in 𝓝 z, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) p,
      g.inner p v w = g₀.inner p v w := by
    filter_upwards [hK.isOpen_compl.mem_nhds hzK] with p hp
    exact hext p hp
  have hl := laplaceBeltrami_metric_congr_nhds g g₀ (roundPower a b n) hagree
  have hr := roundPower_eigen g₀ hg₀ a b n hn ha hb hab z
  exact hz (by dsimp only; linarith)

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction
section JointLocalLaplacian
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
include hq hu
lemma joint_localLaplacian (t : ℝ) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => localLaplacian (q z.1) u p z.2) (t,y) := by
  classical
  have hv := contDiffAt_inChart hu p hy
  have hd (j : CoordIndex E) :=
    (hv.fderiv_right (m := ∞) (by simp)).clm_apply (contDiffAt_const (c := Module.finBasis ℝ E j))
  have hdd (i j : CoordIndex E) :=
    ((hd j).fderiv_right (m := ∞) (by simp)).clm_apply (contDiffAt_const (c := Module.finBasis ℝ E i))
  have hh : ContDiffAt ℝ ∞ (fun z : ℝ × E =>
      (∑ i, ∑ j, (metricCoefficients (q z.1) p z.2)⁻¹ i j *
        fderiv ℝ (fun y => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)) z.2
          (Module.finBasis ℝ E i)) + ∑ j, metricFirstCoefficient (q z.1) p j z.2 *
        fderiv ℝ (u ∘ (chartAt E p).symm) z.2 (Module.finBasis ℝ E j)) (t,y) := by
    apply ContDiffAt.add
    · apply ContDiffAt.sum
      intro i _
      apply ContDiffAt.sum
      intro j _
      apply (joint_metricInverse q p (hq p) t hy i j).mul
      simpa only [Function.comp_def] using (hdd i j).comp (t,y) contDiffAt_snd
    · apply ContDiffAt.sum
      intro j _
      apply (joint_metricFirstCoefficient q p (hq p) t hy j).mul
      simpa only [Function.comp_def] using (hd j).comp (t,y) contDiffAt_snd
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually ((chartAt E p).open_target.mem_nhds hy)] with z hz
  exact localLaplacian_expansion hu (q z.1) p hz

lemma joint_laplaceBeltrami_chart (t : ℝ) (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => laplaceBeltrami (q z.1) u ((chartAt E p).symm z.2)) (t,y) := by
  apply (joint_localLaplacian q hq hu t p hy).congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually ((chartAt E p).open_target.mem_nhds hy)] with z hz
  rw [laplaceBeltrami_inChart hu (q z.1) p _ ((chartAt E p).map_target hz),
    (chartAt E p).right_inv hz]
end JointLocalLaplacian

section JointPartialTime
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma contDiffAt_partial_time_deriv {f : ℝ × E → F} {t : ℝ} {y : E}
    (hf : ContDiffAt ℝ ∞ f (t,y)) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => deriv (fun r => f (r,z.2)) z.1) (t,y) := by
  have hh : ContDiffAt ℝ ∞ (fun w : (ℝ × E) × ℝ => f (w.2,w.1.2)) ((t,y),t) := by
    simpa only [Function.comp_def] using hf.comp ((t,y),t)
      (show ContDiffAt ℝ ∞ (fun w : (ℝ × E) × ℝ => (w.2,w.1.2)) ((t,y),t) from
        contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact (hh.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const
end JointPartialTime
section ChartContinuity
variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace F]
omit [NormedSpace ℝ E] in
lemma continuous_joint_of_chart (f : ℝ → M → F)
    (hf : ∀ t p, ContinuousAt (fun z : ℝ × E => f z.1 ((chartAt E p).symm z.2)) (t,chartAt E p p)) :
    Continuous (fun z : ℝ × M => f z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t,p⟩
  have hc : ContinuousAt (fun z : ℝ × M => (z.1,chartAt E p z.2)) (t,p) :=
    continuousAt_fst.prodMk (((chartAt E p).continuousAt (mem_chart_source E p)).comp continuousAt_snd)
  apply ((hf t p).comp (f := fun z : ℝ × M => (z.1,chartAt E p z.2)) (x := (t,p)) hc).congr
  filter_upwards [continuous_snd.continuousAt.eventually ((chartAt E p).open_source.mem_nhds (mem_chart_source E p))] with z hz
  simp only [Function.comp_apply,(chartAt E p).left_inv hz]
end ChartContinuity

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
variable (q : ℝ → SmoothMetric E M)
variable (hq : ∀ p t y, y ∈ (chartAt E p).target → ∀ i j,
  ContDiffAt ℝ ∞ (fun z : ℝ × E => metricCoefficients (q z.1) p z.2 i j) (t,y))
variable {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
include hq hu
lemma continuous_joint_laplaceBeltrami :
    Continuous (fun z : ℝ × M => laplaceBeltrami (q z.1) u z.2) := by
  apply continuous_joint_of_chart (E := E) (fun t x => laplaceBeltrami (q t) u x)
  intro t p
  exact (joint_laplaceBeltrami_chart q hq hu t p ((chartAt E p).map_source (mem_chart_source E p))).continuousAt

lemma continuous_joint_laplaceBeltrami_time_deriv :
    Continuous (fun z : ℝ × M => deriv (fun t => laplaceBeltrami (q t) u z.2) z.1) := by
  apply continuous_joint_of_chart (E := E) (fun t x => deriv (fun r => laplaceBeltrami (q r) u x) t)
  intro t p
  exact (contDiffAt_partial_time_deriv (joint_laplaceBeltrami_chart q hq hu t p
    ((chartAt E p).map_source (mem_chart_source E p)))).continuousAt

lemma hasDerivAt_laplaceBeltrami_time (t : ℝ) (p : M) :
    HasDerivAt (fun r => laplaceBeltrami (q r) u p)
      (deriv (fun r => laplaceBeltrami (q r) u p) t) t := by
  have hh := (joint_laplaceBeltrami_chart q hq hu t p ((chartAt E p).map_source (mem_chart_source E p))).comp t
    (show ContDiffAt ℝ ∞ (fun r : ℝ => (r,chartAt E p p)) t from contDiffAt_id.prodMk contDiffAt_const)
  have hf : ContDiffAt ℝ ∞ (fun r => laplaceBeltrami (q r) u p) t := by
    simpa only [Function.comp_def, (chartAt E p).left_inv (mem_chart_source E p)] using hh
  exact (hf.differentiableAt (by simp)).hasDerivAt

end YauCounterexamples
end

end OAI
