import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ConformalMetric
import OAI.Geometry.SmoothYau.Smoothness.ConstantComplexProductJetBound
import OAI.Geometry.SmoothYau.Smoothness.SecondDerivNonposLocalMax
import OAI.Geometry.SmoothYau.Smoothness.SobolevRepresentativeOrderCongr
import OAI.Geometry.SmoothYau.Spectrum.BilinearCoordinateMatrixPosDef

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_neg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    laplaceBeltrami g (-u) x = -laplaceBeltrami g u x := by
  unfold laplaceBeltrami
  simp only [Function.comp_def, Pi.neg_apply, fderiv_fun_neg, _root_.neg_apply,
    mul_neg, Finset.sum_neg_distrib]

theorem laplaceBeltrami_nonpos_at_localMax (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) {x : M} (hm : IsLocalMax u x) :
    laplaceBeltrami g u x ≤ 0 := by
  classical
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hInv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  let f := u ∘ c.symm
  have hf : ContDiffAt ℝ ∞ f (c x) := contDiffAt_inChart hu x hx
  have hm' : IsLocalMax f (c x) := by
    have h : IsLocalMax u (c.symm (c x)) := by rw [hInv]; exact hm
    exact h.comp_continuous (c.symm.continuousAt hx)
  change localLaplacian g u x (c x) ≤ 0
  rw [localLaplacian_expansion hu g x hx]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
    fderiv ℝ (fun y => fderiv ℝ f y (Module.finBasis ℝ E j)) (c x) (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g x j (c x) * fderiv ℝ f (c x) (Module.finBasis ℝ E j) ≤ 0
  simp only [hm'.fderiv_eq_zero, _root_.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact localMax_hessian_contraction
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hm'
    (Module.finBasis ℝ E) (metricCoefficients_posDef g x hx).inv.posSemidef

theorem laplaceBeltrami_nonneg_at_localMin (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) {x : M} (hm : IsLocalMin u x) :
    0 ≤ laplaceBeltrami g u x := by
  have h := laplaceBeltrami_nonpos_at_localMax g hu.neg hm.neg
  change laplaceBeltrami g (-u) x ≤ 0 at h
  rw [laplaceBeltrami_neg] at h
  linarith

theorem positive_shift_kernel_eq_zero [CompactSpace M] (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (he : ∀ x, α * u x - laplaceBeltrami g u x = 0) : u = 0 := by
  ext y
  obtain ⟨x, _, hmax⟩ := isCompact_univ.exists_isMaxOn (show (univ : Set M).Nonempty from ⟨y, mem_univ _⟩)
    hu.continuous.continuousOn
  have hl := laplaceBeltrami_nonpos_at_localMax g hu (hmax.isLocalMax (univ_mem))
  have hx : u x ≤ 0 := by nlinarith [he x]
  obtain ⟨z, _, hmin⟩ := isCompact_univ.exists_isMinOn (show (univ : Set M).Nonempty from ⟨y, mem_univ _⟩)
    hu.continuous.continuousOn
  have hl' := laplaceBeltrami_nonneg_at_localMin g hu (hmin.isLocalMin (univ_mem))
  have hz : 0 ≤ u z := (mul_nonneg_iff_of_pos_left hα).mp (by linarith [he z])
  exact le_antisymm ((hmax (mem_univ y)).trans hx) (hz.trans (hmin (mem_univ y)))


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
omit [FiniteDimensional ℝ E] in
lemma contDiffAt_inChart_C2 {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) y :=
  contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))

lemma fderiv_inChart_change_C2 {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
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
  have hu' := (contDiffAt_inChart_C2 hu p ((chartAt E p).map_source hp)).differentiableAt (by simp)
  rw [fderiv_comp y hu' hf, ContinuousLinearMap.comp_apply,
    ← (Module.finBasis ℝ E).sum_repr (fderiv ℝ (chartTransition p q) y (Module.finBasis ℝ E i))]
  simp only [map_sum, map_smul, smul_eq_mul, coordinateTransitionMatrix,
    LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma metricFlux_change_C2 {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
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
  simp only [metricFlux, fderiv_inChart_change_C2 hu p q hy hp,
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

lemma differentiableAt_metricFlux_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
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
  have hu' := ((contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact ha.mul (hu'.clm_apply (differentiableAt_const _))

lemma localLaplacian_change_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localLaplacian g u q y = localLaplacian g u p (chartTransition p q y) := by
  classical
  have he (i : CoordIndex E) : (fun z => metricFlux g u q z i) =ᶠ[𝓝 y]
      (fun z => ∑ k, |(coordinateTransitionMatrix p q z).det| *
        (coordinateTransitionMatrix p q z)⁻¹ i k * metricFlux g u p (chartTransition p q z) k) := by
    filter_upwards [chart_overlap_nhds p q hy hp] with z hz
    exact metricFlux_change_C2 hu g p q hz.1 hz.2 i
  have hJ : IsUnit (coordinateTransitionMatrix p q y).det :=
    isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)
  have hi := piola_divergence_abs ((contDiffAt_chartTransition p q hy hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (differentiableAt_metricFlux_C2 hu g p ((chartAt E p).map_source hp))
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

lemma laplaceBeltrami_inChart_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p x : M) (hx : x ∈ (chartAt E p).source) :
    laplaceBeltrami g u x = localLaplacian g u p (chartAt E p x) := by
  change localLaplacian g u x (chartAt E x x) = _
  have he := localLaplacian_change_C2 hu g p x ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  simpa only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)] using he

lemma localLaplacian_expansion_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
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
    ((contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
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

theorem laplaceBeltrami_nonpos_at_localMax_C2 (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) {x : M} (hm : IsLocalMax u x) :
    laplaceBeltrami g u x ≤ 0 := by
  classical
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hInv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  let f := u ∘ c.symm
  have hf : ContDiffAt ℝ 2 f (c x) := contDiffAt_inChart_C2 hu x hx
  have hm' : IsLocalMax f (c x) := by
    have h : IsLocalMax u (c.symm (c x)) := by rw [hInv]; exact hm
    exact h.comp_continuous (c.symm.continuousAt hx)
  change localLaplacian g u x (c x) ≤ 0
  rw [localLaplacian_expansion_C2 hu g x hx]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
    fderiv ℝ (fun y => fderiv ℝ f y (Module.finBasis ℝ E j)) (c x) (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g x j (c x) * fderiv ℝ f (c x) (Module.finBasis ℝ E j) ≤ 0
  simp only [hm'.fderiv_eq_zero, _root_.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact localMax_hessian_contraction
    hf hm'
    (Module.finBasis ℝ E) (metricCoefficients_posDef g x hx).inv.posSemidef

theorem laplaceBeltrami_nonneg_at_localMin_C2 (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) {x : M} (hm : IsLocalMin u x) :
    0 ≤ laplaceBeltrami g u x := by
  have h := laplaceBeltrami_nonpos_at_localMax_C2 g hu.neg hm.neg
  change laplaceBeltrami g (-u) x ≤ 0 at h
  rw [laplaceBeltrami_neg] at h
  linarith

theorem positive_shift_kernel_eq_zero_C2 [CompactSpace M] (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (he : ∀ x, α * u x - laplaceBeltrami g u x = 0) : u = 0 := by
  ext y
  obtain ⟨x, _, hmax⟩ := isCompact_univ.exists_isMaxOn (show (univ : Set M).Nonempty from ⟨y, mem_univ _⟩)
    hu.continuous.continuousOn
  have hl := laplaceBeltrami_nonpos_at_localMax_C2 g hu (hmax.isLocalMax (univ_mem))
  have hx : u x ≤ 0 := by nlinarith [he x]
  obtain ⟨z, _, hmin⟩ := isCompact_univ.exists_isMinOn (show (univ : Set M).Nonempty from ⟨y, mem_univ _⟩)
    hu.continuous.continuousOn
  have hl' := laplaceBeltrami_nonneg_at_localMin_C2 g hu (hmin.isLocalMin (univ_mem))
  have hz : 0 ≤ u z := (mul_nonneg_iff_of_pos_left hα).mp (by linarith [he z])
  exact le_antisymm ((hmax (mem_univ y)).trans hx) (hz.trans (hmin (mem_univ y)))


open Set Function Filter
open scoped Topology ContDiff

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open Set Function Filter
open scoped Topology ContDiff
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma complexLaplaceBeltrami_inChart {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u) (g : SmoothMetric E M)
    (p : M) {x : M} (hx : x ∈ (chartAt E p).source) :
    complexLaplaceBeltrami g u x =
      euclideanElliptic (Module.finBasis ℝ E)
        (fun i j y => (metricCoefficients g p y)⁻¹ i j)
        (metricFirstCoefficient g p) (u ∘ (chartAt E p).symm) ((chartAt E p) x) := by
  have hur : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (Complex.re ∘ u) :=
    Complex.reCLM.contMDiff.comp hu
  have hui : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (Complex.im ∘ u) :=
    Complex.imCLM.contMDiff.comp hu
  have hf : ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) ((chartAt E p) x) :=
    contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp _
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)
        ((chartAt E p).map_source hx)))
  have hfd := hf.differentiableAt (by norm_num)
  apply Complex.ext
  · change laplaceBeltrami g (Complex.re ∘ u) x = _
    rw [laplaceBeltrami_inChart_C2 hur g p x hx, localLaplacian_expansion_C2 hur g p
      ((chartAt E p).map_source hx)]
    simp only [euclideanElliptic, Complex.add_re, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.reCLM hf _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.reCLM hfd _
  · change laplaceBeltrami g (Complex.im ∘ u) x = _
    rw [laplaceBeltrami_inChart_C2 hui g p x hx, localLaplacian_expansion_C2 hui g p
      ((chartAt E p).map_source hx)]
    simp only [euclideanElliptic, Complex.add_im, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact clm_second_fderiv Complex.imCLM hf _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact clm_fderiv_apply Complex.imCLM hfd _

lemma complex_positive_shift_kernel_eq_zero [CompactSpace M] (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, (α : ℂ) * u x - complexLaplaceBeltrami g u x = 0) : u = 0 := by
  have hr : Complex.re ∘ u = 0 := positive_shift_kernel_eq_zero_C2 g hα
    (Complex.reCLM.contMDiff.comp hu) (fun x => by
      have h := congrArg Complex.re (he x)
      simpa [complexLaplaceBeltrami] using h)
  have hi : Complex.im ∘ u = 0 := positive_shift_kernel_eq_zero_C2 g hα
    (Complex.imCLM.contMDiff.comp hu) (fun x => by
      have h := congrArg Complex.im (he x)
      simpa [complexLaplaceBeltrami] using h)
  funext x
  apply Complex.ext
  · exact congrFun hr x
  · exact congrFun hi x


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_complex_inChart {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u) (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) :
    ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) ((chartAt E p) x) :=
  contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp _
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)
      ((chartAt E p).map_source hx)))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma contMDiff_const_mul_complex {u : M → ℂ}
    {n : ℕ∞ω} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n u) (c : ℂ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) n (fun x => c * u x) :=
  ((ContinuousLinearMap.mul ℝ ℂ) c).contMDiff.comp hu

lemma complexLaplaceBeltrami_add {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v) (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (fun y => u y + v y) x =
      complexLaplaceBeltrami g u x + complexLaplaceBeltrami g v x := by
  erw [complexLaplaceBeltrami_inChart (hu.add hv) g x (mem_chart_source E x),
    complexLaplaceBeltrami_inChart hu g x (mem_chart_source E x),
    complexLaplaceBeltrami_inChart hv g x (mem_chart_source E x)]
  exact euclideanElliptic_add_at _ _ _ (contDiffAt_complex_inChart hu x (mem_chart_source E x))
    (contDiffAt_complex_inChart hv x (mem_chart_source E x))

lemma complexLaplaceBeltrami_const_mul {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u) (c : ℂ) (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (fun y => c * u y) x = c * complexLaplaceBeltrami g u x := by
  erw [complexLaplaceBeltrami_inChart (contMDiff_const_mul_complex hu c) g x
      (mem_chart_source E x), complexLaplaceBeltrami_inChart hu g x (mem_chart_source E x)]
  exact euclideanElliptic_const_mul_at _ _ _ c
    (contDiffAt_complex_inChart hu x (mem_chart_source E x))

lemma complexLaplaceBeltrami_zero (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g 0 x = 0 := by
  erw [complexLaplaceBeltrami_inChart contMDiff_const g x (mem_chart_source E x)]
  exact euclideanElliptic_zero _ _ _ _

lemma complexLaplaceBeltrami_congr {u v : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 v) (g : SmoothMetric E M) {x : M}
    (h : u =ᶠ[𝓝 x] v) : complexLaplaceBeltrami g u x = complexLaplaceBeltrami g v x := by
  erw [complexLaplaceBeltrami_inChart hu g x (mem_chart_source E x),
    complexLaplaceBeltrami_inChart hv g x (mem_chart_source E x)]
  apply euclideanElliptic_congr
  have ht := ((chartAt E x).continuousAt_symm ((chartAt E x).map_source
    (mem_chart_source E x))).tendsto
  rw [(chartAt E x).left_inv (mem_chart_source E x)] at ht
  exact h.comp_tendsto ht

lemma complexLaplaceBeltrami_sum {ι : Type*} (t : Finset ι) (u : ι → M → ℂ)
    (hu : ∀ i ∈ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 (u i))
    (g : SmoothMetric E M) (x : M) :
    complexLaplaceBeltrami g (fun y => ∑ i ∈ t, u i y) x =
      ∑ i ∈ t, complexLaplaceBeltrami g (u i) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      (show complexLaplaceBeltrami g (fun _ : M => (0 : ℂ)) x = 0 from
        complexLaplaceBeltrami_zero g x)
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    rw [complexLaplaceBeltrami_add (hu _ (Finset.mem_insert_self _ _))
      (ContMDiff.sum (fun j hj => hu j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))]

omit [FiniteDimensional ℝ E] in
lemma contMDiff_chartLift_order (q : M) (ξ : M → ℂ)
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

lemma complexLaplaceBeltrami_chartLift [T2Space M] (g : SmoothMetric E M)
    (p : M) (χ : M → ℂ) (hχs : tsupport χ ⊆ (chartAt E p).source)
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ) {u : E → ℂ}
    (hu : ContDiff ℝ 2 u) {x : M} (hx : x ∈ (chartAt E p).source) :
    complexLaplaceBeltrami g (chartLift (E := E) p χ u) x =
      euclideanElliptic (Module.finBasis ℝ E)
        (fun i j y => (metricCoefficients g p y)⁻¹ i j) (metricFirstCoefficient g p)
        (fun y => chartLocalize (E := E) p χ 1 y * u y) ((chartAt E p) x) := by
  erw [complexLaplaceBeltrami_inChart (contMDiff_chartLift_order p χ hχs hχ 2 hu) g p hx]
  apply euclideanElliptic_congr
  filter_upwards [(chartAt E p).open_target.mem_nhds ((chartAt E p).map_source hx)] with y hy
  simp only [Function.comp_apply, chartLift, chartLocalize_eq p χ 1 hy, Pi.one_apply,
    mul_one, (chartAt E p).right_inv hy]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
section ProductCalculus
variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕜]
lemma second_fderiv_mul_at {u v : E → 𝕜} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have hdv' : DifferentiableAt ℝ (fun y => fderiv ℝ v y b) x :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =ᶠ[𝓝 x]
      (fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y hy hz
    rw [fderiv_fun_mul (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he.fderiv_eq]
  erw [fderiv_fun_add (hdu.mul hdv') (hdv.mul hdu'),
    fderiv_fun_mul hdu hdv', fderiv_fun_mul hdv hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring
end ProductCalculus
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def coordinateGradientPair (g : SmoothMetric E M) (u v : M → ℝ) (x : M) : ℝ :=
  ∑ i, ∑ j, (metricCoefficients g x ((chartAt E x) x))⁻¹ i j *
    fderiv ℝ (u ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E i) *
    fderiv ℝ (v ∘ (chartAt E x).symm) ((chartAt E x) x) (Module.finBasis ℝ E j)

lemma laplaceBeltrami_mul {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y * v y) x =
      u x * laplaceBeltrami g v x + v x * laplaceBeltrami g u x +
        2 * coordinateGradientPair g u v x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hv' := contDiffAt_inChart_C2 hv x hx
  change localLaplacian g _ x (c x) = _
  have huv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 (fun y => u y * v y) := hu.mul hv
  rw [localLaplacian_expansion_C2 huv g x hx]
  change _ = u x * localLaplacian g v x (c x) +
    v x * localLaplacian g u x (c x) + 2 * coordinateGradientPair g u v x
  rw [localLaplacian_expansion_C2 hu g x hx, localLaplacian_expansion_C2 hv g x hx]
  have hs (i j : CoordIndex E) : (metricCoefficients g x (c x))⁻¹ j i =
      (metricCoefficients g x (c x))⁻¹ i j := by
    have h := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A i j)
      (metricCoefficients_posDef g x hx).inv.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hcross : (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i)) =
      coordinateGradientPair g u v x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) y (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) *
        fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) = _
  have hd1 (j : CoordIndex E) :
      fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z) (c x) (b j) =
        u x * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
        v x * fderiv ℝ (u ∘ c.symm) (c x) (b j) := by
    erw [fderiv_fun_mul (hu'.differentiableAt (by norm_num))
      (hv'.differentiableAt (by norm_num))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun y => fderiv ℝ (fun z => (u ∘ c.symm) z * (v ∘ c.symm) z)
        y (b j)) (c x) (b i) =
      u x * fderiv ℝ (fun y => fderiv ℝ (v ∘ c.symm) y (b j)) (c x) (b i) +
      v x * fderiv ℝ (fun y => fderiv ℝ (u ∘ c.symm) y (b j)) (c x) (b i) +
      fderiv ℝ (u ∘ c.symm) (c x) (b i) * fderiv ℝ (v ∘ c.symm) (c x) (b j) +
      fderiv ℝ (u ∘ c.symm) (c x) (b j) * fderiv ℝ (v ∘ c.symm) (c x) (b i) := by
    have he := second_fderiv_mul_at hu' hv' (b i) (b j)
    dsimp only [c] at hinv he ⊢
    simpa only [Function.comp_apply, hinv] using he
  simp_rw [hd2, hd1]
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, hcross]
  unfold coordinateGradientPair
  dsimp only [c, b]
  simp only [← Finset.mul_sum, mul_assoc, mul_left_comm]
  ring

lemma weightedLaplacian_expansion {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b u x = b x * laplaceBeltrami g u x + coordinateGradientPair g b u x := by
  let c := chartAt E x
  let a := metricCoefficients g x
  let ρ := fun y => Real.sqrt (Matrix.det (a y))
  let e := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hb' := contDiffAt_inChart_C2 hb x hx
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hρ := Real.sqrt_pos.mpr (metricCoefficients_det_pos g x hx)
  have hρd := ((contDiffOn_metricDensity g x).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)
  have hflux (i : CoordIndex E) : DifferentiableAt ℝ
      (fun y => ρ y * ∑ j, (a y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (e j)) (c x) := by
    apply hρd.mul
    apply DifferentiableAt.fun_sum
    intro j _
    apply (((contDiffOn_metricInverse g x i j).contDiffAt ((chartAt E x).open_target.mem_nhds hx)).differentiableAt (by simp)).mul
    exact ((hu'.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  change (ρ (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) = _
  have hd (i : CoordIndex E) : fderiv ℝ
      (fun y => (b ∘ c.symm) y * (ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j))) (c x) (e i) =
      b x * fderiv ℝ (fun y => ρ y * ∑ j, (a y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (e j)) (c x) (e i) +
      (ρ (c x) * ∑ j, (a (c x))⁻¹ i j * fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i) := by
    erw [fderiv_fun_mul (hb'.differentiableAt (by norm_num)) (hflux i)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, Function.comp_apply]
    dsimp only [c] at hinv ⊢
    rw [hinv]
  simp_rw [hd, Finset.sum_add_distrib]
  change (ρ (c x))⁻¹ * ((∑ i, b x * _) +
    ∑ i, (ρ (c x) * ∑ j, (a (c x))⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) (c x) (e j)) *
        fderiv ℝ (b ∘ c.symm) (c x) (e i)) = _
  unfold laplaceBeltrami coordinateGradientPair
  dsimp only
  simp only [Finset.mul_sum, mul_add, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [ρ, a, c, e] at hρ ⊢
    field_simp [ne_of_gt hρ]

lemma weightedLaplacian_product_formula {b u : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b u x =
      (laplaceBeltrami g (fun y => b y * u y) x + b x * laplaceBeltrami g u x -
        u x * laplaceBeltrami g b x) / 2 := by
  rw [weightedLaplacian_expansion hb hu, laplaceBeltrami_mul hb hu]
  ring


end

open Set Filter Manifold
open scoped Topology ContDiff
section ScalarComposition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma scalar_comp_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ F (u x)) (hu : DifferentiableAt ℝ u x) (v : E) :
    fderiv ℝ (F ∘ u) x v = deriv F (u x) * fderiv ℝ u x v := by
  rw [fderiv_comp x hF hu, ContinuousLinearMap.comp_apply]
  exact fderiv_eq_deriv_mul
lemma scalar_comp_second_directional {F : ℝ → ℝ} {u : E → ℝ} {x : E}
    (hF : ContDiffAt ℝ 2 F (u x)) (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (F ∘ u) y b) x a =
      deriv (deriv F) (u x) * fderiv ℝ u x a * fderiv ℝ u x b +
      deriv F (u x) * fderiv ℝ (fun y => fderiv ℝ u y b) x a := by
  have hdu := hu.differentiableAt (by norm_num)
  have hF' : DifferentiableAt ℝ (deriv F) (u x) :=
    by
      simpa only [fderiv_apply_one_eq_deriv] using
        ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
          (differentiableAt_const (1 : ℝ))
  have hdu' : DifferentiableAt ℝ (fun y => fderiv ℝ u y b) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const b)
  have he : (fun y => fderiv ℝ (F ∘ u) y b) =ᶠ[𝓝 x]
      (fun y => deriv F (u y) * fderiv ℝ u y b) := by
    filter_upwards [hu.eventually (by norm_num),
      (hdu.continuousAt.preimage_mem_nhds (hF.eventually (by norm_num)))] with y hy hFy
    change ContDiffAt ℝ 2 F (u y) at hFy
    exact scalar_comp_directional (hFy.differentiableAt (by norm_num))
      (hy.differentiableAt (by norm_num)) b
  rw [he.fderiv_eq]
  erw [fderiv_fun_mul (hF'.comp x hdu) hdu']
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hfder := scalar_comp_directional hF' hdu a
  change fderiv ℝ (deriv F ∘ u) x a = _ at hfder
  rw [hfder]
  simp only [Function.comp_apply]
  ring
end ScalarComposition
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
lemma localLaplacian_expansion_at {u : M → ℝ}
    (g : SmoothMetric E M) (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (hu : ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) y) :
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
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
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

theorem laplaceBeltrami_comp_at {F : ℝ → ℝ} {u : M → ℝ}
    (g : SmoothMetric E M) (x : M) (hF : ContDiffAt ℝ 2 F (u x))
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u) :
    laplaceBeltrami g (F ∘ u) x = deriv F (u x) * laplaceBeltrami g u x +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x := by
  let c := chartAt E x
  let b := Module.finBasis ℝ E
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hinv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hu' := contDiffAt_inChart_C2 hu x hx
  have hF' : ContDiffAt ℝ 2 F ((u ∘ c.symm) (c x)) := by
    simpa only [Function.comp_apply,hinv] using hF
  have hFu : ContDiffAt ℝ 2 ((F ∘ u) ∘ c.symm) (c x) := hF'.comp (c x) hu'
  change localLaplacian g (F ∘ u) x (c x) =
    deriv F (u x) * localLaplacian g u x (c x) +
      deriv (deriv F) (u x) * coordinateGradientPair g u u x
  rw [localLaplacian_expansion_at g x hx hFu, localLaplacian_expansion_C2 hu g x hx]
  have hd1 (i : CoordIndex E) :
      fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b i) =
      deriv F (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) := by
    change fderiv ℝ (F ∘ (u ∘ c.symm)) (c x) (b i) = _
    rw [scalar_comp_directional (hF'.differentiableAt (by norm_num))
      (hu'.differentiableAt (by norm_num)), Function.comp_apply, hinv]
  have hd2 (i j : CoordIndex E) :
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i) =
      deriv (deriv F) (u x) * fderiv ℝ (u ∘ c.symm) (c x) (b i) *
        fderiv ℝ (u ∘ c.symm) (c x) (b j) +
      deriv F (u x) * fderiv ℝ (fun z => fderiv ℝ (u ∘ c.symm) z (b j)) (c x) (b i) := by
    change fderiv ℝ (fun z => fderiv ℝ (F ∘ (u ∘ c.symm)) z (b j)) (c x) (b i) = _
    rw [scalar_comp_second_directional hF' hu', Function.comp_apply,hinv]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ ((F ∘ u) ∘ c.symm) z (b j)) (c x) (b i)) +
      ∑ j, metricFirstCoefficient g x j (c x) * fderiv ℝ ((F ∘ u) ∘ c.symm) (c x) (b j) = _
  simp_rw [hd1,hd2,mul_add,Finset.sum_add_distrib]
  unfold coordinateGradientPair
  simp only [Finset.mul_sum]
  simp only [mul_left_comm,mul_comm]
  ring



end YauCounterexamples
end

end OAI
