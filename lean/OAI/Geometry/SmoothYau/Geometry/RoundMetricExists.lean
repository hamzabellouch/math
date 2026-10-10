import Mathlib
import OAI.Geometry.SmoothYau.Limits.RealMatrixCauchy
import OAI.Geometry.SmoothYau.Spectrum.JointLocalLaplacian

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
open Set Filter Manifold
open scoped Topology ContDiff Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def localGradientPair (g : SmoothMetric E M) (u v : M → ℝ) (p : M) (y : E) : ℝ :=
  (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)) ⬝ᵥ
    (metricCoefficients g p y)⁻¹ *ᵥ
      (fun j => fderiv ℝ (v ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j))

lemma localGradientPair_change {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (g : SmoothMetric E M) (p q : M) {y : E}
    (hy : y ∈ (chartAt E q).target) (hp : (chartAt E q).symm y ∈ (chartAt E p).source) :
    localGradientPair g u v q y = localGradientPair g u v p (chartTransition p q y) := by
  let J := coordinateTransitionMatrix p q y
  let du : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  let dv : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (v ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E i)
  have hu' : (fun i => fderiv ℝ (u ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ du := by
    ext i
    rw [fderiv_inChart_change hu p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,du, mul_comm]
  have hv' : (fun i => fderiv ℝ (v ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i)) =
      Jᵀ *ᵥ dv := by
    ext i
    rw [fderiv_inChart_change hv p q hy hp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, J,dv, mul_comm]
  have hid : J * ((metricCoefficients g q y)⁻¹ * Jᵀ) =
      (metricCoefficients g p (chartTransition p q y))⁻¹ := by
    rw [metricInverse_change_left g p q hy hp, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (coordinateTransitionMatrix_det_ne_zero g p q hy hp)),
      Matrix.one_mul]
  unfold localGradientPair
  rw [hu', hv', Matrix.mulVec_mulVec]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hid, dotProduct_comm]

lemma coordinateGradientPair_inChart {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v)
    (g : SmoothMetric E M) (p x : M) (hx : x ∈ (chartAt E p).source) :
    coordinateGradientPair g u v x = localGradientPair g u v p ((chartAt E p) x) := by
  have he := localGradientPair_change hu hv g p x
    ((chartAt E x).map_source (mem_chart_source E x))
    (by simpa only [(chartAt E x).left_inv (mem_chart_source E x)] using hx)
  have hbase : coordinateGradientPair g u v x =
      localGradientPair g u v x ((chartAt E x) x) := by
    simp only [coordinateGradientPair, localGradientPair, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hbase, he]
  simp only [chartTransition, Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)]

lemma contMDiff_coordinateGradientPair {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v) (g : SmoothMetric E M) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (coordinateGradientPair g u v) := by
  have he : coordinateGradientPair g u v = fun x => (2 : ℝ)⁻¹ *
      (laplaceBeltrami g (fun y => u y * v y) x -
        u x * laplaceBeltrami g v x - v x * laplaceBeltrami g u x) := by
    funext x
    rw [laplaceBeltrami_mul (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    ring
  rw [he]
  exact contMDiff_const.mul (((contMDiff_laplaceBeltrami (hu.mul hv) g).sub
    (hu.mul (contMDiff_laplaceBeltrami hv g))).sub (hv.mul (contMDiff_laplaceBeltrami hu g)))

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
section Pullback
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def pullbackInner {T : Type*} [AddCommGroup T] [Module ℝ T] [TopologicalSpace T]
    (D : T →L[ℝ] F) : T →L[ℝ] T →L[ℝ] ℝ :=
  (D.precomp ℝ).comp ((innerSL ℝ).comp D)

omit [FiniteDimensional ℝ E] in
@[simp] theorem pullbackInner_apply (D : E →L[ℝ] F) (v w : E) :
    pullbackInner D v w = inner ℝ (D v) (D w) := rfl

theorem pullbackInner_bounded (D : E →L[ℝ] F) (hD : Function.Injective D) :
    Bornology.IsVonNBounded ℝ {v : E | pullbackInner D v v < 1} := by
  obtain ⟨K, _, hK⟩ := D.toLinearMap.injective_iff_antilipschitz.mp hD
  rw [NormedSpace.isVonNBounded_iff ℝ]
  apply (hK.isBounded_preimage (Metric.isBounded_ball (x := (0 : F)) (r := 1))).subset
  intro v hv
  change dist (D v) 0 < 1
  rw [dist_zero_right]
  rw [← sq_lt_one_iff₀ (norm_nonneg (D v)), ← real_inner_self_eq_norm_sq]
  exact hv

omit [FiniteDimensional ℝ E] in
theorem contMDiff_pullbackInner (f : M → F)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (pullbackInner (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))) := by
  intro x₀
  rw [contMDiffAt_section x₀]
  have hd := (hf x₀).mfderiv_const (m := ∞) (by simp)
  let L : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun _ : M => L) x₀ := contMDiffAt_const
  have h := hd.clm_precomp (F₃ := ℝ) |>.clm_comp (hc.clm_comp hd)
  apply h.congr_of_eventuallyEq
  have hn := (trivializationAt (E →L[ℝ] ℝ)
      (fun x => TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt (E →L[ℝ] ℝ) _ x₀)
  filter_upwards [hn] with x hx
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.comp_apply]
  simp [pullbackInner, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, TangentBundle.continuousLinearMapAt_model_space]
  rw [Trivialization.coe_linearMapAt_of_mem _ hx]
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  rfl

def inducedMetric (f : M → F) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hDf : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    SmoothMetric E M where
  inner x := pullbackInner (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.mpr (by
    intro h
    apply hv
    apply hDf x
    rw [map_zero]
    exact h)
  isVonNBounded x := pullbackInner_bounded (E := E) _ (hDf x)
  contMDiff := contMDiff_pullbackInner f hf

end Pullback
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma metric_inner_nonneg (g : SmoothMetric E M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) : 0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

def scalarDifferential (u : M → ℝ) (x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x

lemma scalarDifferential_coordinateVector {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) (i : CoordIndex E) :
    scalarDifferential u ((chartAt E p).symm y) (coordinateVector p y i) =
      fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i) := by
  have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy
      (n := ∞)).mdifferentiableAt (by simp)
  have he := mfderiv_comp y (hu.mdifferentiable (by simp) _) hc
  rw [mfderiv_eq_fderiv] at he
  exact (congrArg (fun T => T (Module.finBasis ℝ E i)) he).symm

lemma chart_metric_quadratic (g : SmoothMetric E M) (p : M) (y : E) (z : CoordIndex E → ℝ) :
    g.inner ((chartAt E p).symm y)
      (∑ i, z i • coordinateVector p y i) (∑ i, z i • coordinateVector p y i) =
      z ⬝ᵥ ((metricCoefficients g p y) *ᵥ z) := by
  classical
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [metricCoefficients]
  rw [g.symm _ (coordinateVector p y j)]
  ring

lemma scalarDifferential_dual_bound_chart {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target)
    (v : TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y)) :
    (scalarDifferential u ((chartAt E p).symm y) v) ^ 2 ≤
      localGradientPair g u u p y * g.inner ((chartAt E p).symm y) v v := by
  classical
  have he : (chartAt E p).MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableOn (by simp)⟩
  obtain ⟨w, rfl⟩ := he.symm.mfderiv_surjective hy v
  let D : E →L[ℝ] TangentSpace 𝓘(ℝ, E) ((chartAt E p).symm y) :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
  let wE : E := w
  let z := (Module.finBasis ℝ E).equivFun wE
  have hw : wE = ∑ i, z i • Module.finBasis ℝ E i := by
    symm
    exact (Module.finBasis ℝ E).sum_repr wE
  change (scalarDifferential u _ (D wE)) ^ 2 ≤
    localGradientPair g u u p y * g.inner _ (D wE) (D wE)
  rw [hw, map_sum]
  simp only [map_smul]
  change (scalarDifferential u _ (∑ i, z i • coordinateVector p y i)) ^ 2 ≤ _
  erw [chart_metric_quadratic]
  simp only [map_sum, map_smul, smul_eq_mul, scalarDifferential_coordinateVector hu p hy]
  let du : CoordIndex E → ℝ := fun i =>
    fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)
  have hc := real_dual_matrix_cauchy (metricCoefficients_posDef g p hy) du z
  simpa only [localGradientPair, dotProduct, mul_comm, du] using hc

lemma scalarDifferential_dual_bound {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    (scalarDifferential u x v) ^ 2 ≤
      coordinateGradientPair g u u x * g.inner x v v := by
  have hx := mem_chart_source E x
  have hy := (chartAt E x).map_source hx
  have he := (chartAt E x).left_inv hx
  have H := scalarDifferential_dual_bound_chart hu g x hy
  rw [coordinateGradientPair_inChart hu hu g x x hx]
  apply (congrArg (fun z : M => (scalarDifferential u z v) ^ 2 ≤
    localGradientPair g u u x ((chartAt E x) x) * g.inner z v v) he).mp
  exact H v

lemma rankOne_coercive (a b F G D : ℝ) (hG : 0 ≤ G) (hD : D ^ 2 ≤ F * G) :
    min a (a + b * F) * G ≤ a * G + b * D ^ 2 := by
  by_cases hb : 0 ≤ b
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hG).trans
      (le_add_of_nonneg_right (mul_nonneg hb (sq_nonneg D)))
  · have hb' : b ≤ 0 := le_of_not_ge hb
    have h := mul_le_mul_of_nonpos_left hD hb'
    have hm := mul_le_mul_of_nonneg_right (min_le_right a (a + b * F)) hG
    nlinarith

def rankOneMetric (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (F : M → ℝ)
    (ha0 : ∀ x, 0 < a x) (hab0 : ∀ x, 0 < a x + b x * F x)
    (hdual : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      (scalarDifferential u x v) ^ 2 ≤ F x * g.inner x v v) :
    SmoothMetric E M where
  inner x := a x • g.inner x + b x • pullbackInner (scalarDifferential u x)
  symm x v w := by
    change a x * g.inner x v w + b x * inner ℝ (scalarDifferential u x v) (scalarDifferential u x w) =
      a x * g.inner x w v + b x * inner ℝ (scalarDifferential u x w) (scalarDifferential u x v)
    rw [g.symm, real_inner_comm (scalarDifferential u x v) (scalarDifferential u x w)]
  pos x v hv := by
    have hδ : 0 < min (a x) (a x + b x * F x) := lt_min (ha0 x) (hab0 x)
    have h := rankOne_coercive (a x) (b x) (F x) (g.inner x v v)
      (scalarDifferential u x v) (metric_inner_nonneg g x v) (hdual x v)
    change 0 < a x * g.inner x v v + b x * (scalarDifferential u x v * scalarDifferential u x v)
    simpa only [pow_two] using (mul_pos hδ (g.pos x v hv)).trans_le h
  isVonNBounded x := by
    let δ := min (a x) (a x + b x * F x)
    have hδ : 0 < δ := lt_min (ha0 x) (hab0 x)
    have hsq : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    apply ((g.isVonNBounded x).image ((Real.sqrt δ)⁻¹ •
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x))).subset
    intro v hv
    refine ⟨Real.sqrt δ • v, ?_, ?_⟩
    · change g.inner x (Real.sqrt δ • v) (Real.sqrt δ • v) < 1
      have h := rankOne_coercive (a x) (b x) (F x) (g.inner x v v)
        (scalarDifferential u x v) (metric_inner_nonneg g x v) (hdual x v)
      have hv' : a x * g.inner x v v + b x * (scalarDifferential u x v) ^ 2 < 1 := by
        change a x * g.inner x v v + b x * (scalarDifferential u x v * scalarDifferential u x v) < 1 at hv
        simpa only [pow_two] using hv
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sq_sqrt hδ.le]
      exact h.trans_lt hv'
    · simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
      exact inv_smul_smul₀ (ne_of_gt hsq) v
  contMDiff := (ha.smul_section g.contMDiff).add_section
    (hb.smul_section (contMDiff_pullbackInner u hu))

def differentialMetric (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x) : SmoothMetric E M :=
  rankOneMetric g u hu a b ha hb (coordinateGradientPair g u u) ha0 hab0
    (scalarDifferential_dual_bound hu g)

lemma differentialMetric_coefficients (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    metricCoefficients (differentialMetric g u hu a b ha hb ha0 hab0) p y =
      a ((chartAt E p).symm y) • metricCoefficients g p y +
      b ((chartAt E p).symm y) • Matrix.vecMulVec
        (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i))
        (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)) := by
  ext i j
  simp only [metricCoefficients, differentialMetric, rankOneMetric]
  change a ((chartAt E p).symm y) * g.inner _ (coordinateVector p y i) (coordinateVector p y j) +
      b ((chartAt E p).symm y) * inner ℝ
        (scalarDifferential u _ (coordinateVector p y i)) (scalarDifferential u _ (coordinateVector p y j)) =
    a ((chartAt E p).symm y) * g.inner _ (coordinateVector p y i) (coordinateVector p y j) +
      b ((chartAt E p).symm y) *
        (fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i) *
          fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j))
  rw [scalarDifferential_coordinateVector hu p hy, scalarDifferential_coordinateVector hu p hy]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma localGradientPair_eq_global {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localGradientPair g u u p y = coordinateGradientPair g u u ((chartAt E p).symm y) := by
  rw [coordinateGradientPair_inChart hu hu g p ((chartAt E p).symm y) ((chartAt E p).map_target hy),
    (chartAt E p).right_inv hy]

lemma differentialMetric_density_three (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b d : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (hd0 : ∀ x, 0 ≤ d x)
    (hdet : ∀ x, a x ^ 2 * (a x + b x * coordinateGradientPair g u u x) = d x ^ 2)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    Real.sqrt (Matrix.det (metricCoefficients
      (differentialMetric g u hu a b ha hb ha0 hab0) p y)) =
      d ((chartAt E p).symm y) * Real.sqrt (Matrix.det (metricCoefficients g p y)) := by
  rw [differentialMetric_coefficients g u hu a b ha hb ha0 hab0 p hy,
    det_rank_one_three (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne')
      (by simpa only [CoordIndex, Fintype.card_fin] using hd) _ (ha0 _).ne']
  change Real.sqrt ((a _ ^ 2 * (a _ + b _ * localGradientPair g u u p y)) * _) = _
  rw [localGradientPair_eq_global hu g p hy, hdet, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (hd0 _)]

lemma differentialMetric_flux (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    (metricCoefficients (differentialMetric g u hu a b ha hb ha0 hab0) p y)⁻¹ *ᵥ
      (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i)) =
      (a ((chartAt E p).symm y) + b ((chartAt E p).symm y) *
        coordinateGradientPair g u u ((chartAt E p).symm y))⁻¹ •
      ((metricCoefficients g p y)⁻¹ *ᵥ
        (fun i => fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E i))) := by
  have hB := isUnit_iff_ne_zero.mpr
    (metricCoefficients_det_pos (differentialMetric g u hu a b ha hb ha0 hab0) p hy).ne'
  rw [differentialMetric_coefficients g u hu a b ha hb ha0 hab0 p hy] at hB ⊢
  have he := localGradientPair_eq_global hu g p hy
  dsimp only [localGradientPair] at he
  rw [rank_one_inverse_direction
    (isUnit_iff_ne_zero.mpr (metricCoefficients_det_pos g p hy).ne') _ _ _ hB
      (by rw [he]; exact (hab0 _).ne'), he]

theorem differentialMetric_laplacian_three (hn : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (a b d q : M → ℝ)
    (ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b)
    (ha0 : ∀ x, 0 < a x)
    (hab0 : ∀ x, 0 < a x + b x * coordinateGradientPair g u u x)
    (hd0 : ∀ x, 0 < d x)
    (hdet : ∀ x, a x ^ 2 * (a x + b x * coordinateGradientPair g u u x) = d x ^ 2)
    (hflux : ∀ x, d x / (a x + b x * coordinateGradientPair g u u x) = q x)
    (x : M) :
    laplaceBeltrami (differentialMetric g u hu a b ha hb ha0 hab0) u x =
      (d x)⁻¹ * weightedLaplacian g q u x := by
  let c := chartAt E x
  let ĝ := differentialMetric g u hu a b ha hb ha0 hab0
  have hx : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hy : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have he (i : CoordIndex E) :
      (fun y => Real.sqrt (Matrix.det (metricCoefficients ĝ x y)) *
        ∑ j, (metricCoefficients ĝ x y)⁻¹ i j *
          fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j)) =ᶠ[𝓝 (c x)]
      (fun y => q (c.symm y) * (Real.sqrt (Matrix.det (metricCoefficients g x y)) *
        ∑ j, (metricCoefficients g x y)⁻¹ i j *
          fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) := by
    filter_upwards [c.open_target.mem_nhds hy] with y hyt
    change Real.sqrt (Matrix.det (metricCoefficients ĝ x y)) *
      ((metricCoefficients ĝ x y)⁻¹ *ᵥ
        (fun j => fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) i = _
    rw [differentialMetric_density_three hn g u hu a b d ha hb ha0 hab0
        (fun z => (hd0 z).le) hdet x hyt,
      differentialMetric_flux g u hu a b ha hb ha0 hab0 x hyt]
    simp only [Pi.smul_apply, smul_eq_mul]
    change d (c.symm y) * _ * ((a _ + b _ * coordinateGradientPair g u u _)⁻¹ * _) = _
    rw [show d (c.symm y) * Real.sqrt (Matrix.det (metricCoefficients g x y)) *
        ((a (c.symm y) + b (c.symm y) * coordinateGradientPair g u u (c.symm y))⁻¹ *
          ((metricCoefficients g x y)⁻¹ *ᵥ
            (fun j => fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) i) =
        (d (c.symm y) / (a (c.symm y) + b (c.symm y) *
          coordinateGradientPair g u u (c.symm y))) *
          (Real.sqrt (Matrix.det (metricCoefficients g x y)) *
            ((metricCoefficients g x y)⁻¹ *ᵥ
              (fun j => fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) i) by
      rw [div_eq_mul_inv]; ring]
    rw [hflux]
    rfl
  unfold laplaceBeltrami weightedLaplacian
  dsimp only
  conv_lhs => arg 2; arg 2; ext i; rw [(he i).fderiv_eq]
  rw [differentialMetric_density_three hn g u hu a b d ha hb ha0 hab0
    (fun z => (hd0 z).le) hdet x hy]
  dsimp only [c] at hx
  rw [hx, _root_.mul_inv_rev]
  ring

lemma compatible_sqrt {q d : ℝ} (hq : 0 < q) (he : d = q ^ 3) :
    d / q = Real.sqrt (d * q) := by
  rw [he, show q ^ 3 * q = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg q)]
  field_simp

theorem determinant_correction_coefficients (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (d q : M → ℝ)
    (hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ d)
    (hq : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ q)
    (hd0 : ∀ x, 0 < d x) (hq0 : ∀ x, 0 < q x)
    (hsupp : tsupport (fun x => d x - q x ^ 3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0}) :
    ∃ a b : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x, 0 < a x) ∧ (∀ x, 0 < a x + b x * coordinateGradientPair g u u x) ∧
      (∀ x, a x ^ 2 * (a x + b x * coordinateGradientPair g u u x) = d x ^ 2) ∧
      (∀ x, d x / (a x + b x * coordinateGradientPair g u u x) = q x) ∧
      (∀ x, d x = 1 → q x = 1 → a x = 1 ∧ b x = 0) := by
  let F := coordinateGradientPair g u u
  let a := fun x => Real.sqrt (d x * q x)
  let b := fun x => (d x / q x - a x) / F x
  have hF := contMDiff_coordinateGradientPair hu hu g
  have ha : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ a := by
    intro x
    exact (Real.contDiffAt_sqrt (mul_pos (hd0 x) (hq0 x)).ne').contMDiffAt.comp x
      ((hd x).mul (hq x))
  have ha0 : ∀ x, 0 < a x := fun x => Real.sqrt_pos.mpr (mul_pos (hd0 x) (hq0 x))
  have hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b := by
    intro x
    by_cases hx : F x = 0
    · have hn : x ∉ tsupport (fun x => d x - q x ^ 3) := by
        intro h
        exact hsupp h hx
      have he := notMem_tsupport_iff_eventuallyEq.mp hn
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      have hc := compatible_sqrt (hq0 y) (sub_eq_zero.mp hy)
      simp only [b, a, hc, sub_self, zero_div]
    · exact (((hd x).div₀ (hq x) (hq0 x).ne').sub (ha x)).div₀ (hF x) hx
  have hc : ∀ x, a x + b x * F x = d x / q x := by
    intro x
    by_cases hx : F x = 0
    · have hn : x ∉ tsupport (fun x => d x - q x ^ 3) := fun h => hsupp h hx
      have he := image_eq_zero_of_notMem_tsupport hn
      have hcompat := compatible_sqrt (hq0 x) (sub_eq_zero.mp he)
      dsimp only [b, a]
      rw [hx, mul_zero, add_zero]
      exact hcompat.symm
    · dsimp only [b]
      rw [div_mul_cancel₀ _ hx]
      ring
  refine ⟨a, b, ha, hb, ha0, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hc]
    exact div_pos (hd0 x) (hq0 x)
  · intro x
    rw [hc]
    dsimp only [a]
    rw [Real.sq_sqrt (mul_pos (hd0 x) (hq0 x)).le]
    field_simp [(hq0 x).ne', (hd0 x).ne']
  · intro x
    rw [hc]
    field_simp [(hq0 x).ne', (hd0 x).ne']
  · intro x hdx hqx
    simp [a, b, hdx, hqx]

theorem conductivity_metric_realization (hn : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ u) (d q : M → ℝ)
    (hd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ d)
    (hq : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ q)
    (hd0 : ∀ x, 0 < d x) (hq0 : ∀ x, 0 < q x)
    (hsupp : tsupport (fun x => d x - q x ^ 3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0}) :
    ∃ ĝ : SmoothMetric E M,
      (∀ x, laplaceBeltrami ĝ u x = (d x)⁻¹ * weightedLaplacian g q u x) ∧
      (∀ x, d x = 1 → q x = 1 → ∀ v w, ĝ.inner x v w = g.inner x v w) := by
  obtain ⟨a, b, ha, hb, ha0, hab0, hdet, hflux, hext⟩ :=
    determinant_correction_coefficients g u hu d q hd hq hd0 hq0 hsupp
  refine ⟨differentialMetric g u hu a b ha hb ha0 hab0,
    differentialMetric_laplacian_three hn g u hu a b d q ha hb ha0 hab0 hd0 hdet hflux, ?_⟩
  intro x hdx hqx v w
  obtain ⟨hax, hbx⟩ := hext x hdx hqx
  change a x * g.inner x v w + b x *
    inner ℝ (scalarDifferential u x v) (scalarDifferential u x w) = _
  rw [hax, hbx]
  simp


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal

theorem round_metric_exists : ∃ g : SmoothMetric (Euclidean 3) (Sphere 3), IsRound g := by
  let : Fact (Module.finrank ℝ (Euclidean 4) = 3 + 1) := ⟨by simp [Euclidean]⟩
  refine ⟨inducedMetric (fun y : Sphere 3 => (y : Euclidean 4))
    contMDiff_coe_sphere (fun x => ?_), ?_⟩
  · convert! injective_mvfderiv_subtypeVal_sphere x
  · intro x v w
    rfl



end YauCounterexamples
end

end OAI
