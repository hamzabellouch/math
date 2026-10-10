import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ScalarPredPowerWeightBound
import OAI.Geometry.SmoothYau.Geometry.MetricDetChange
import OAI.Geometry.SmoothYau.Smoothness.FlowInitialFderiv

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

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_chartTransition (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    ContDiffAt ℝ ∞ (chartTransition p q) y := by
  exact contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hy))

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_inChart {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (u ∘ (chartAt E p).symm) y :=
  contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma chart_overlap_nhds (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    ∀ᶠ z in 𝓝 y, z ∈ (chartAt E q).target ∧
      (chartAt E q).symm z ∈ (chartAt E p).source := by
  have hc := (chartAt E q).continuousAt_symm hy
  filter_upwards [(chartAt E q).open_target.mem_nhds hy,
    hc.eventually ((chartAt E p).open_source.mem_nhds hp)] with z hz hz'
  exact ⟨hz, hz'⟩

lemma fderiv_inChart_change {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) (i : CoordIndex E) :
    fderiv ℝ (u ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i) =
      ∑ k, fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y)
        (Module.finBasis ℝ E k) * coordinateTransitionMatrix p q y k i := by
  have he : (u ∘ (chartAt E q).symm) =ᶠ[𝓝 y]
      ((u ∘ (chartAt E p).symm) ∘ chartTransition p q) := by
    filter_upwards [chart_overlap_nhds p q hy hp] with z hz
    simp only [Function.comp_apply, chartTransition, (chartAt E p).left_inv hz.2]
  rw [he.fderiv_eq]
  have hf := (contDiffAt_chartTransition p q hy hp).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart hu p ((chartAt E p).map_source hp)).differentiableAt (by simp)
  rw [fderiv_comp y hu' hf, ContinuousLinearMap.comp_apply,
    ← (Module.finBasis ℝ E).sum_repr (fderiv ℝ (chartTransition p q) y (Module.finBasis ℝ E i))]
  simp only [map_sum, map_smul, smul_eq_mul, coordinateTransitionMatrix,
    LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro k _
  ring

def metricFlux (g : SmoothMetric E M) (u : M → ℝ) (p : M) (y : E) (i : CoordIndex E) : ℝ :=
  Real.sqrt (metricCoefficients g p y).det *
    ∑ j, (metricCoefficients g p y)⁻¹ i j *
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j)

def localLaplacian (g : SmoothMetric E M) (u : M → ℝ) (p : M) (y : E) : ℝ :=
  (Real.sqrt (metricCoefficients g p y).det)⁻¹ *
    ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (Module.finBasis ℝ E i)

lemma metricInverse_change_left (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    (metricCoefficients g q y)⁻¹ * (coordinateTransitionMatrix p q y).transpose =
      (coordinateTransitionMatrix p q y)⁻¹ *
        (metricCoefficients g p (chartTransition p q y))⁻¹ := by
  have hd : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  rw [← metricInverse_change g p q hy hp, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

lemma metricFlux_change {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (g : SmoothMetric E M) (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) (i : CoordIndex E) :
    metricFlux g u q y i = ∑ k, |(coordinateTransitionMatrix p q y).det| *
      (coordinateTransitionMatrix p q y)⁻¹ i k * metricFlux g u p (chartTransition p q y) k := by
  classical
  let d : CoordIndex E → ℝ := fun j =>
    fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E j)
  have hh := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A.mulVec d i)
    (metricInverse_change_left g p q hy hp)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hh
  simp only [metricFlux, fderiv_inChart_change hu p q hy hp,
    metricDensity_change g p q hy hp]
  have hs : (∑ j, (metricCoefficients g q y)⁻¹ i j *
      ∑ k, d k * coordinateTransitionMatrix p q y k j) =
      ∑ k, (coordinateTransitionMatrix p q y)⁻¹ i k *
        ∑ j, (metricCoefficients g p (chartTransition p q y))⁻¹ k j * d j := by
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hh
  change (_ * _) * (∑ j, (metricCoefficients g q y)⁻¹ i j *
    ∑ k, d k * coordinateTransitionMatrix p q y k j) = _
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [d]
  ring

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

def metricFirstCoefficient (g : SmoothMetric E M) (p : M) (j : CoordIndex E) (y : E) : ℝ :=
  (Real.sqrt (metricCoefficients g p y).det)⁻¹ * ∑ i,
    fderiv ℝ (fun z => Real.sqrt (metricCoefficients g p z).det *
      (metricCoefficients g p z)⁻¹ i j) y (Module.finBasis ℝ E i)

lemma contDiffAt_metricFirstCoefficient (g : SmoothMetric E M) (p : M) (j : CoordIndex E)
    {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ ∞ (metricFirstCoefficient g p j) y := by
  have hd := (contDiffOn_metricDensity g p).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  have hn : Real.sqrt (metricCoefficients g p y).det ≠ 0 :=
    (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  apply (hd.inv hn).mul
  apply ContDiffAt.sum
  intro i _
  have ha := (contDiffOn_metricInverse g p i j).contDiffAt ((chartAt E p).open_target.mem_nhds hy)
  exact ((hd.mul ha).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

lemma localLaplacian_expansion {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localLaplacian g u p y =
      (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j *
        fderiv ℝ (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y
          (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g p j y *
        fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) := by
  classical
  let ρ := fun z => Real.sqrt (metricCoefficients g p z).det
  let A := metricCoefficients g p
  let v := u ∘ (chartAt E p).symm
  let b := Module.finBasis ℝ E
  have hρ : DifferentiableAt ℝ ρ y := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hA (i j : CoordIndex E) : DifferentiableAt ℝ (fun z => (A z)⁻¹ i j) y :=
    ((contDiffOn_metricInverse g p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((contDiffAt_inChart hu p hy).fderiv_right (m := 1) (by rw [one_add_one_eq_two]; exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiableAt one_ne_zero
  have he (i : CoordIndex E) : (fun z => metricFlux g u p z i) =
      fun z => ∑ j, (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j) := by
    funext z
    simp only [metricFlux, ρ, A, v, b, Finset.mul_sum, mul_assoc]
  have hder (i : CoordIndex E) : fderiv ℝ (fun z => metricFlux g u p z i) y (b i) =
      ∑ j, ((ρ y * (A y)⁻¹ i j) * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) +
        fderiv ℝ v y (b j) * fderiv ℝ (fun z => ρ z * (A z)⁻¹ i j) y (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun z => ρ z * (A z)⁻¹ i j)
      (d := fun z => fderiv ℝ v z (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change (ρ y)⁻¹ * ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (b i) = _
  simp_rw [hder, Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hn : ρ y ≠ 0 := (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  have hmain : (∑ i, (ρ y)⁻¹ * ∑ j, ρ y * (A y)⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i)) =
      ∑ i, ∑ j, (A y)⁻¹ i j * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [metricFirstCoefficient, ρ, A, b, v, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

def roundPlanarChart (a b : Euclidean (d+1)) (p : Sphere d) : Euclidean d → ℂ :=
  fun y => planarLinear a b ((chartAt (Euclidean d) p).symm y : Euclidean (d+1))

lemma roundPlanarChart_smooth (a b : Euclidean (d+1)) (p : Sphere d) :
    ContDiffOn ℝ ∞ (roundPlanarChart a b p) (chartAt (Euclidean d) p).target := by
  have hs : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℂ) ∞
      (fun q : Sphere d => planarLinear a b (q : Euclidean (d+1))) :=
    (planarLinear a b).contDiff.contMDiff.comp contMDiff_coe_sphere
  intro y hy
  exact (contMDiffAt_iff_contDiffAt.mp (hs.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))).contDiffWithinAt

lemma sphere_wave_weight_C1 (a b : Euclidean (d+1)) (φ : Sphere d → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ φ) {n : ℕ} (hn : 2 ≤ n) :
    ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) 1
      (fun p : Sphere d => Real.exp ((n:ℝ)*φ p)+‖planarLinear a b p‖^n) := by
  have hnR : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hs : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℂ) 1
      (fun q : Sphere d => planarLinear a b (q : Euclidean (d+1))) :=
    (planarLinear a b).contDiff.contMDiff.comp contMDiff_coe_sphere
  have hp : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) 1
      (fun p : Sphere d => ‖planarLinear a b p‖^n) := by
    simpa only [Function.comp_def,Real.rpow_natCast] using (contDiff_norm_rpow hnR).contMDiff.comp hs
  exact (Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul (hφ.of_le (by simp)))).add hp

theorem sphere_wave_weight_control (a b : Euclidean (d+1)) (φ : Sphere d → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ φ) (p : Sphere d)
    {K : Set (Euclidean d)} (hK : IsCompact K)
    (hKO : K ⊆ (chartAt (Euclidean d) p).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) 1
        (fun x : Sphere d => Real.exp ((n:ℝ)*φ x)+‖planarLinear a b x‖^n) ∧
      (∀ x : Sphere d, 0 < Real.exp ((n:ℝ)*φ x)+‖planarLinear a b x‖^n) ∧
      ∀ y ∈ K, ‖fderiv ℝ ((fun x : Sphere d => Real.exp ((n:ℝ)*φ x)+‖planarLinear a b x‖^n) ∘
        (chartAt (Euclidean d) p).symm) y‖ ≤ C*(n:ℝ)*
        (Real.exp ((n:ℝ)*φ ((chartAt (Euclidean d) p).symm y))+‖roundPlanarChart a b p y‖^n) := by
  have hφ' : ContDiffOn ℝ 1 (φ ∘ (chartAt (Euclidean d) p).symm)
      (chartAt (Euclidean d) p).target := by
    intro y hy
    exact ((contDiffAt_inChart hφ p hy).of_le (by simp)).contDiffWithinAt
  obtain ⟨C,hC,hall⟩ := positive_wave_weight_on_control (roundPlanarChart a b p)
    (φ ∘ (chartAt (Euclidean d) p).symm) (chartAt (Euclidean d) p).open_target
    ((roundPlanarChart_smooth a b p).of_le (by simp)) hφ' hK hKO
  refine ⟨C,hC,?_⟩
  intro n hn
  refine ⟨sphere_wave_weight_C1 a b φ hφ hn,?_,?_⟩
  · intro x
    exact add_pos_of_pos_of_nonneg (Real.exp_pos _) (pow_nonneg (norm_nonneg _) _)
  · intro y hy
    exact (hall n hn).2.2 y hy

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold ContDiff Matrix.Norms.Elementwise
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_smooth_metric_coefficients_at (g : SmoothMetric E M) (p : M) :
    ∃ (a : CoordIndex E → CoordIndex E → E → ℝ) (c : CoordIndex E → E → ℝ),
      (∀ i j, ContDiff ℝ ∞ (a i j)) ∧ (∀ i, ContDiff ℝ ∞ (c i)) ∧
      Matrix.PosDef (fun i j => a i j ((chartAt E p) p)) ∧
      ∃ δ : ℝ, 0 < δ ∧ Metric.ball ((chartAt E p) p) δ ⊆ (chartAt E p).target ∧
        (∀ y ∈ Metric.ball ((chartAt E p) p) δ,
          (∀ i j, a i j y = (metricCoefficients g p y)⁻¹ i j) ∧
          (∀ i, c i y = metricFirstCoefficient g p i y)) := by
  let φ : E → Matrix (CoordIndex E) (CoordIndex E) ℝ × (CoordIndex E → ℝ) :=
    fun y => ((metricCoefficients g p y)⁻¹, fun i => metricFirstCoefficient g p i y)
  have hp : (chartAt E p) p ∈ (chartAt E p).target :=
    (chartAt E p).map_source (mem_chart_source E p)
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        contDiffOn_metricInverse g p i j))
    · exact contDiffOn_pi.mpr (fun i y hy =>
        (contDiffAt_metricFirstCoefficient g p i hy).contDiffWithinAt)
  obtain ⟨ψ, hψ, he⟩ := smooth_extension_near_compact (isCompact_singleton)
    (chartAt E p).open_target (singleton_subset_iff.mpr hp) hφ
  have he' : φ =ᶠ[𝓝 ((chartAt E p) p)] ψ :=
    he.filter_mono (nhds_le_nhdsSet (mem_singleton _))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp
    (he'.and ((chartAt E p).open_target.mem_nhds hp))
  refine ⟨fun i j y => (ψ y).1 i j, fun i y => (ψ y).2 i,
    fun i j => contDiff_pi.mp (contDiff_pi.mp hψ.fst i) j,
    fun i => contDiff_pi.mp hψ.snd i, ?_, δ, hδ, ?_, ?_⟩
  · have h0 := congrArg Prod.fst he'.self_of_nhds
    change Matrix.PosDef ((ψ ((chartAt E p) p)).1)
    rw [← h0]
    exact (metricCoefficients_posDef g p hp).inv
  · intro y hy
    exact (hd hy).2
  · intro y hy
    have hh := (hd hy).1
    exact ⟨fun i j => congrFun (congrFun (congrArg Prod.fst hh.symm) i) j,
      fun i => congrFun (congrArg Prod.snd hh.symm) i⟩

theorem exists_smooth_metric_coefficients_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ (chartAt E p).target) :
    ∃ (a : CoordIndex E → CoordIndex E → E → ℝ) (c : CoordIndex E → E → ℝ),
      (∀ i j, ContDiff ℝ ∞ (a i j)) ∧ (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ y ∈ K, (∀ i j, a i j y = (metricCoefficients g p y)⁻¹ i j) ∧
        (∀ i, c i y = metricFirstCoefficient g p i y)) := by
  let φ : E → Matrix (CoordIndex E) (CoordIndex E) ℝ × (CoordIndex E → ℝ) :=
    fun y => ((metricCoefficients g p y)⁻¹, fun i => metricFirstCoefficient g p i y)
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target := by
    apply ContDiffOn.prodMk
    · exact contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j =>
        contDiffOn_metricInverse g p i j))
    · exact contDiffOn_pi.mpr (fun i y hy =>
        (contDiffAt_metricFirstCoefficient g p i hy).contDiffWithinAt)
  obtain ⟨ψ, hψ, he⟩ := smooth_extension_near_compact hK (chartAt E p).open_target hKs hφ
  refine ⟨fun i j y => (ψ y).1 i j, fun i y => (ψ y).2 i,
    fun i j => contDiff_pi.mp (contDiff_pi.mp hψ.fst i) j,
    fun i => contDiff_pi.mp hψ.snd i, ?_⟩
  intro y hy
  have hh := he.self_of_nhdsSet hy
  exact ⟨fun i j => congrFun (congrFun (congrArg Prod.fst hh.symm) i) j,
    fun i => congrFun (congrArg Prod.snd hh.symm) i⟩


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
section LocalIBP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma local_integration_by_parts {O : Set E} (hO : IsOpen O)
    {f F : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ O) (hF : ContDiffOn ℝ ∞ F O) (v : E) :
    (∫ x in O, f x * fderiv ℝ F x v) = -(∫ x in O, fderiv ℝ f x v * F x) := by
  obtain ⟨H, hH, he⟩ := smooth_extension_near_compact hfc hO hfs hF
  have he' (x : E) (hx : x ∈ tsupport f) : F =ᶠ[𝓝 x] H :=
    he.filter_mono (nhds_le_nhdsSet hx)
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  have hdH := (hH.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := v))
  have h1 (x : E) : f x * fderiv ℝ F x v = f x * fderiv ℝ H x v := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).fderiv_eq]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have h2 (x : E) : fderiv ℝ f x v * F x = fderiv ℝ f x v * H x := by
    by_cases hx : x ∈ tsupport f
    · rw [(he' x hx).eq_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  simp_rw [h1, h2]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (mt (@hfs x) hx), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [fderiv_of_notMem_tsupport ℝ (mt (@hfs x) hx)]; simp)]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hdf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport
      ((hfc.fderiv_apply ℝ v).mul_right))
    (hf.continuous.mul hdH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (hf.continuous.mul hH.continuous |>.integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hH.differentiable (by simp)).differentiableAt)
end LocalIBP

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

def realChartLocalize (p : M) (u : M → ℝ) (y : E) : ℝ := by
  classical
  exact if y ∈ (chartAt E p).target then u ((chartAt E p).symm y) else 0

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma realChartLocalize_eq (p : M) (u : M → ℝ) {y : E} (hy : y ∈ (chartAt E p).target) :
    realChartLocalize (E := E) p u y = u ((chartAt E p).symm y) := ite_eq_left hy

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma support_realChartLocalize (p : M) (u : M → ℝ) :
    support (realChartLocalize (E := E) p u) ⊆ (chartAt E p) '' tsupport u := by
  intro y hy
  by_cases hy' : y ∈ (chartAt E p).target
  · refine ⟨(chartAt E p).symm y, ?_, (chartAt E p).right_inv hy'⟩
    apply subset_tsupport
    change u ((chartAt E p).symm y) ≠ 0
    change realChartLocalize (E := E) p u y ≠ 0 at hy
    simpa only [realChartLocalize, ite_eq_left hy'] using hy
  · exact False.elim (hy (by simp only [realChartLocalize, ite_eq_right hy']))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma isCompact_realChartSupport (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    IsCompact ((chartAt E p) '' tsupport u) :=
  hc.image_of_continuousOn ((chartAt E p).continuousOn.mono hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    tsupport (realChartLocalize (E := E) p u) ⊆ (chartAt E p) '' tsupport u :=
  closure_minimal (support_realChartLocalize p u) (isCompact_realChartSupport p u hc hs).isClosed

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma hasCompactSupport_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    HasCompactSupport (realChartLocalize (E := E) p u) :=
  (isCompact_realChartSupport p u hc hs).of_isClosed_subset isClosed_closure
    (tsupport_realChartLocalize p u hc hs)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedSpace ℝ E] [T2Space M] in
lemma tsupport_realChartLocalize_subset (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source) :
    tsupport (realChartLocalize (E := E) p u) ⊆ (chartAt E p).target :=
  (tsupport_realChartLocalize p u hc hs).trans
    (image_subset_iff.mpr fun _ hx => (chartAt E p).map_source (hs hx))

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma contDiff_realChartLocalize (p : M) (u : M → ℝ)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ (chartAt E p).source)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞ (realChartLocalize (E := E) p u) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro y hy
  have hyt := tsupport_realChartLocalize_subset (E := E) p u hc hs hy
  have hh := contDiffAt_inChart hu p hyt
  rw [contMDiffAt_iff_contDiffAt]
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chartAt E p).open_target.mem_nhds hyt] with z hz
  exact realChartLocalize_eq p u hz

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma realChartLocalize_fderiv (p : M) (u : M → ℝ) {y : E}
    (hy : y ∈ (chartAt E p).target) :
    fderiv ℝ (realChartLocalize (E := E) p u) y = fderiv ℝ (u ∘ (chartAt E p).symm) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(chartAt E p).open_target.mem_nhds hy] with z hz
  exact realChartLocalize_eq p u hz


end YauCounterexamples
end

end OAI
