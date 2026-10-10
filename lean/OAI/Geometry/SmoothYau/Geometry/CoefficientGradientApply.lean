import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PhaseFormMatrix
import OAI.Geometry.SmoothYau.Smoothness.DistanceSquare
import OAI.Geometry.SmoothYau.Smoothness.ExistsFinitePatchPartition
import OAI.Geometry.SmoothYau.Smoothness.LocalIntegrationParts

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
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def metricChartIntegral (g : SmoothMetric E M) (p : M) (f : M → ℝ) : ℝ :=
  ∫ y in (chartAt E p).target, Real.sqrt (metricCoefficients g p y).det *
    f ((chartAt E p).symm y)

lemma metricChartIntegral_change (g : SmoothMetric E M) (p q : M) (f : M → ℝ)
    (hp : support f ⊆ (chartAt E p).source)
    (hq : support f ⊆ (chartAt E q).source) :
    metricChartIntegral g p f = metricChartIntegral g q f := by
  let e := (chartAt E q).symm.trans (chartAt E p)
  have hs : e.source ⊆ (chartAt E q).target := fun _ h => h.1
  have ht : e.target ⊆ (chartAt E p).target := fun _ h => h.1
  have hleft : metricChartIntegral g p f =
      ∫ y in e.target, Real.sqrt (metricCoefficients g p y).det * f ((chartAt E p).symm y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (chartAt E p).open_target.measurableSet ht
    intro y hy
    have hz : f ((chartAt E p).symm y) = 0 := by
      by_contra hh
      exact hy.2 ⟨hy.1, hq hh⟩
    rw [hz, mul_zero]
  have hright : metricChartIntegral g q f =
      ∫ y in e.source, Real.sqrt (metricCoefficients g q y).det * f ((chartAt E q).symm y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (chartAt E q).open_target.measurableSet hs
    intro y hy
    have hz : f ((chartAt E q).symm y) = 0 := by
      by_contra hh
      exact hy.2 ⟨hy.1, hp hh⟩
    rw [hz, mul_zero]
  rw [hleft, hright]
  have hd : ∀ y ∈ e.source, HasFDerivAt e (fderiv ℝ (chartTransition p q) y) y := by
    intro y hy
    exact ((contDiffAt_chartTransition p q hy.1 hy.2).differentiableAt (by simp)).hasFDerivAt
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro y hy
  dsimp only
  rw [metricDensity_change g p q hy.1 hy.2]
  have he : (chartAt E p).symm (e y) = (chartAt E q).symm y :=
    (chartAt E p).left_inv hy.2
  rw [he]
  change |(fderiv ℝ (chartTransition p q) y).toLinearMap.det| *
    (Real.sqrt (metricCoefficients g p (chartTransition p q y)).det * _) = _
  rw [coordinateTransitionMatrix, LinearMap.det_toMatrix]
  ring

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
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

lemma metricChart_integrable (g : SmoothMetric E M) (p : M) {f : M → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt E p).source) :
    IntegrableOn (fun y => Real.sqrt (metricCoefficients g p y).det *
      f ((chartAt E p).symm y)) (chartAt E p).target := by
  let K := (chartAt E p) '' tsupport f
  have hK : IsCompact K := hc.image_of_continuousOn ((chartAt E p).continuousOn.mono hs)
  have hKt : K ⊆ (chartAt E p).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (chartAt E p).map_source (hs hx)
  apply IntegrableOn.of_inter_support (chartAt E p).open_target.measurableSet
  apply (((contDiffOn_metricDensity g p).continuousOn.mono hKt).mul
    (hf.comp_continuousOn ((chartAt E p).continuousOn_symm.mono hKt))).integrableOn_compact hK |>.mono_set
  intro y hy
  refine ⟨(chartAt E p).symm y, ?_, (chartAt E p).right_inv hy.1⟩
  apply subset_tsupport
  intro hz
  exact hy.2 (by simp only [hz, mul_zero])

lemma metricChartIntegral_nonneg (g : SmoothMetric E M) (p : M) {f : M → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ metricChartIntegral g p f := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (Real.sqrt_nonneg _) (hf _)


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
  [T2Space M] [CompactSpace M]

section
-- Preserve the structural size when Lean generates the atlas SizeOf instance.
private local instance [SizeOf E] [SizeOf M] (t : Finset M) :
    SizeOf (SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ) :=
  @SmoothPartitionOfUnity._sizeOf_inst t E _ _ E _ 𝓘(ℝ, E) M _ _ univ _ _ _ _
    (fun _ => inferInstance)

structure MetricIntegralAtlas where
  t : Finset M
  ρ : SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ
  subordinate : ρ.IsSubordinate (fun i => (chartAt E (i : M)).source)
end

omit [MeasurableSpace E] [BorelSpace E] in
lemma nonempty_metricIntegralAtlas : Nonempty (MetricIntegralAtlas (E := E) (M := M)) := by
  obtain ⟨t, ρ, hρ⟩ := exists_finite_patch_partition (E := E)
    (fun p : M => (chartAt E p).source) (fun p => (chartAt E p).open_source) (mem_chart_source E)
  exact ⟨⟨t, ρ, hρ⟩⟩

namespace MetricIntegralAtlas
variable (A : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

omit [T2Space M] in
lemma local_integrable (i : A.t) (f : M →ᵇ ℝ) :
    IntegrableOn (fun y => Real.sqrt (metricCoefficients g (i : M) y).det *
      (A.ρ i ((chartAt E (i : M)).symm y) * f ((chartAt E (i : M)).symm y)))
      (chartAt E (i : M)).target :=
  metricChart_integrable g i ((A.ρ i).property.continuous.mul f.continuous)
    (HasCompactSupport.of_compactSpace _) (tsupport_mul_subset_left.trans (A.subordinate i))

def integral (f : M →ᵇ ℝ) : ℝ :=
  ∑ i : A.t, metricChartIntegral g (i : M) (fun x => A.ρ i x * f x)

omit [T2Space M] in
lemma integral_add (f h : M →ᵇ ℝ) : A.integral g (f + h) = A.integral g f + A.integral g h := by
  simp only [integral, metricChartIntegral, BoundedContinuousFunction.add_apply, mul_add,
    MeasureTheory.integral_add (A.local_integrable g _ f) (A.local_integrable g _ h), Finset.sum_add_distrib]

omit [T2Space M] [CompactSpace M] in
lemma integral_smul (c : ℝ) (f : M →ᵇ ℝ) : A.integral g (c • f) = c * A.integral g f := by
  simp only [integral, metricChartIntegral, BoundedContinuousFunction.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i : A.t, ∀ y, Real.sqrt (metricCoefficients g (i : M) y).det *
      (A.ρ i ((chartAt E (i : M)).symm y) * (c * f ((chartAt E (i : M)).symm y))) =
      c * (Real.sqrt (metricCoefficients g (i : M) y).det *
        (A.ρ i ((chartAt E (i : M)).symm y) * f ((chartAt E (i : M)).symm y))) by
    intros; ring]
  simp only [integral_const_mul, Finset.mul_sum]

omit [T2Space M] [CompactSpace M] in
lemma integral_nonneg {f : M →ᵇ ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ A.integral g f :=
  Finset.sum_nonneg fun i _ => metricChartIntegral_nonneg g i
    (fun x => mul_nonneg (A.ρ.nonneg i x) (hf x))

omit [T2Space M] in
lemma integral_mono {f h : M →ᵇ ℝ} (hfh : ∀ x, f x ≤ h x) : A.integral g f ≤ A.integral g h := by
  unfold integral
  apply Finset.sum_le_sum
  intro i _
  apply setIntegral_mono_on (A.local_integrable g i f) (A.local_integrable g i h)
    (chartAt E (i : M)).open_target.measurableSet
  intro y _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hfh _) (A.ρ.nonneg i _))
    (Real.sqrt_nonneg _)

omit [T2Space M] in
lemma integral_bound (f : M →ᵇ ℝ) : |A.integral g f| ≤ A.integral g 1 * ‖f‖ := by
  rw [abs_le]
  have h1 : A.integral g (‖f‖ • (1 : M →ᵇ ℝ)) = A.integral g 1 * ‖f‖ := by
    rw [A.integral_smul]; ring
  have h2 : A.integral g ((-‖f‖) • (1 : M →ᵇ ℝ)) = -(A.integral g 1 * ‖f‖) := by
    rw [A.integral_smul]; ring
  constructor
  · rw [← h2]
    apply A.integral_mono
    intro x
    simpa using (abs_le.mp ((Real.norm_eq_abs (f x)) ▸ f.norm_coe_le_norm x)).1
  · rw [← h1]
    apply A.integral_mono
    intro x
    simpa using (abs_le.mp ((Real.norm_eq_abs (f x)) ▸ f.norm_coe_le_norm x)).2

def integralCLM : (M →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := A.integral g
      map_add' := A.integral_add g
      map_smul' := fun c f => by simpa using A.integral_smul g c f }
    (A.integral g 1) (A.integral_bound g)

omit [T2Space M] in
lemma integral_eq_chart (q : M) (f : M →ᵇ ℝ)
    (hf : tsupport f ⊆ (chartAt E q).source) :
    A.integral g f = metricChartIntegral g q f := by
  classical
  have hc (i : A.t) : IntegrableOn (fun y => Real.sqrt (metricCoefficients g q y).det *
      (A.ρ i ((chartAt E q).symm y) * f ((chartAt E q).symm y))) (chartAt E q).target :=
    metricChart_integrable g q ((A.ρ i).property.continuous.mul f.continuous)
      (HasCompactSupport.of_compactSpace _) (tsupport_mul_subset_right.trans hf)
  unfold integral
  calc
    _ = ∑ i : A.t, metricChartIntegral g q (fun x => A.ρ i x * f x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply metricChartIntegral_change
      · exact (subset_tsupport _).trans (tsupport_mul_subset_left.trans (A.subordinate i))
      · exact (subset_tsupport _).trans (tsupport_mul_subset_right.trans hf)
    _ = ∫ y in (chartAt E q).target, ∑ i : A.t,
        Real.sqrt (metricCoefficients g q y).det * (A.ρ i ((chartAt E q).symm y) *
          f ((chartAt E q).symm y)) := (integral_finsetSum _ (fun i _ => hc i)).symm
    _ = metricChartIntegral g q f := by
      apply setIntegral_congr_fun (chartAt E q).open_target.measurableSet
      intro y _
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      have hρ : ∑ i : A.t, A.ρ i ((chartAt E q).symm y) = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using A.ρ.sum_eq_one (mem_univ ((chartAt E q).symm y))
      rw [hρ, one_mul]

omit [T2Space M] in
lemma integral_pos {f : M →ᵇ ℝ} (hf : ∀ x, 0 ≤ f x) (hx : ∃ x, 0 < f x) :
    0 < A.integral g f := by
  classical
  obtain ⟨x, hx⟩ := hx
  obtain ⟨i, hi⟩ := A.ρ.exists_pos_of_mem (mem_univ x)
  have hxi : x ∈ (chartAt E (i : M)).source := A.subordinate i (subset_tsupport _ hi.ne')
  let F : E → ℝ := fun y => Real.sqrt (metricCoefficients g (i : M) y).det *
    (A.ρ i ((chartAt E (i : M)).symm y) * f ((chartAt E (i : M)).symm y))
  have hFc : ContinuousOn F (chartAt E (i : M)).target :=
    (contDiffOn_metricDensity g i).continuousOn.mul
      (((A.ρ i).property.continuous.mul f.continuous).comp_continuousOn
        (chartAt E (i : M)).continuousOn_symm)
  have hFo : IsOpen ({y | 0 < F y} ∩ (chartAt E (i : M)).target) := by
    rw [Set.inter_comm]
    exact hFc.isOpen_inter_preimage (chartAt E (i : M)).open_target isOpen_Ioi
  have hFx : (chartAt E (i : M)) x ∈ {y | 0 < F y} ∩ (chartAt E (i : M)).target := by
    refine ⟨?_, (chartAt E (i : M)).map_source hxi⟩
    dsimp [F]
    rw [(chartAt E (i : M)).left_inv hxi]
    exact mul_pos (Real.sqrt_pos.2 (metricCoefficients_posDef g i
      ((chartAt E (i : M)).map_source hxi)).det_pos) (mul_pos hi hx)
  have hpos : 0 < metricChartIntegral g (i : M) (fun x => A.ρ i x * f x) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (fun y => mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (A.ρ.nonneg i _) (hf _))))
      (A.local_integrable g i f)).2
    apply lt_of_lt_of_le (hFo.measure_pos volume ⟨_, hFx⟩)
    exact measure_mono (fun y hy => ⟨hy.1.ne', hy.2⟩)
  change 0 < ∑ j : A.t, metricChartIntegral g (j : M) (fun x => A.ρ j x * f x)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum
    (fun (j : A.t) _ => metricChartIntegral_nonneg g j (fun x => mul_nonneg (A.ρ.nonneg j x) (hf x)))
    (Finset.mem_univ i))

end MetricIntegralAtlas

end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

lemma weightedPair_integrable (a : SmoothScalar E) (f g : EllipticTest K) :
    Integrable (fun x => a x * f x * g x) (volume : Measure E) := by
  simpa only [testMultiply_apply] using testPair_integrable K (testMultiply K a f) g

lemma weightedPair_integral (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K a f g = ∫ x, a x * f x * g x := by
  simp only [weightedPair, testPair, testMultiply_apply]

lemma weightedPair_le_of_bound (a : SmoothScalar E) (C : ℝ)
    (h : ∀ x ∈ K, a x ≤ C) (f : EllipticTest K) :
    weightedPair K a f f ≤ C * testPair K f f := by
  rw [weightedPair_integral, testPair, ← integral_const_mul]
  apply integral_mono (weightedPair_integrable K a f f)
    ((testPair_integrable K f f).const_mul C)
  intro x
  by_cases hx : x ∈ K
  · nlinarith [mul_le_mul_of_nonneg_right (h x hx) (mul_self_nonneg (f x))]
  · have hf := f.zero_on_compl hx
    simp [hf]

lemma weightedPair_lower_shift (a b : SmoothScalar E) (C μ : ℝ)
    (h : ∀ x ∈ K, μ ≤ 2 * a x - 2 * C * b x) (f : EllipticTest K) :
    μ * testPair K f f ≤ 2 * weightedPair K a f f - 2 * C * weightedPair K b f f := by
  have hint : Integrable (fun x => 2 * (a x * f x * f x) - 2 * C * (b x * f x * f x))
      (volume : Measure E) :=
    ((weightedPair_integrable K a f f).const_mul 2).sub
      ((weightedPair_integrable K b f f).const_mul (2*C))
  rw [weightedPair_integral, weightedPair_integral, testPair, ← integral_const_mul,
    ← integral_const_mul, ← integral_const_mul, ← integral_sub]
  · apply integral_mono ((testPair_integrable K f f).const_mul μ) hint
    intro x
    by_cases hx : x ∈ K
    · nlinarith [mul_le_mul_of_nonneg_right (h x hx) (mul_self_nonneg (f x))]
    · have hf := f.zero_on_compl hx
      simp [hf]
  · exact (weightedPair_integrable K a f f).const_mul 2
  · exact (weightedPair_integrable K b f f).const_mul (2*C)

def testGradientSquare (f : EllipticTest K) : ℝ :=
  ∑ i, testPair K (testDerivative K (e i) f) (testDerivative K (e i) f)

def carlemanGradient (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (f : EllipticTest K) : ℝ :=
  4 * (∑ i, ∑ j, ∑ k,
      weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f)) -
  2 * (∑ i, ∑ j, ∑ k,
      weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f))

lemma carleman_basic_bound (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (τ C : ℝ) (f : EllipticTest K) :
    τ * (carlemanGradient K e a X f + 2*C * testEnergy K e a f f) +
      τ^3 * (2 * weightedPair K (coefficientTransport e X p) f f -
        2*C * weightedPair K p f f) -
      τ * weightedPair K (coefficientElliptic e a (coefficientDivergence e X)) f f -
      C^2 * τ^2 * testPair K f f ≤
    testPair K (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f)
      (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f) := by
  have hshift := testPair_cauchy_shift K (carlemanSymmetric K e a p τ f) f (C*τ)
  have hskew := testPair_nonneg K (carlemanSkew K e X τ f)
  have hcomm := carleman_commutator K e a ha X p τ f
  change 2 * testPair K (carlemanSymmetric K e a p τ f) (carlemanSkew K e X τ f) =
    τ * (carlemanGradient K e a X f -
      weightedPair K (coefficientElliptic e a (coefficientDivergence e X)) f f) +
    2 * τ^3 * weightedPair K (coefficientTransport e X p) f f at hcomm
  have hS : testPair K (carlemanSymmetric K e a p τ f) f =
      -testEnergy K e a f f + τ^2 * weightedPair K p f f := by
    simp only [carlemanSymmetric, LinearMap.add_apply, LinearMap.smul_apply,
      testPair_add_left, testPair_smul_left, testElliptic_pair, weightedPair]
  rw [hS] at hshift
  simp only [testPair_add_left, testPair_add_right,
    testPair_comm K (carlemanSkew K e X τ f) (carlemanSymmetric K e a p τ f)]
  nlinarith only [hshift, hskew, hcomm]

lemma carleman_coercive_of_bounds (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (τ C μ M : ℝ) (hτ : 0 ≤ τ) (f : EllipticTest K)
    (hg : μ * testGradientSquare K e f ≤
      carlemanGradient K e a X f + 2*C * testEnergy K e a f f)
    (hm : ∀ x ∈ K, μ ≤ 2 * coefficientTransport e X p x - 2*C*p x)
    (hq : ∀ x ∈ K, coefficientElliptic e a (coefficientDivergence e X) x ≤ M)
    (ht : τ*M + C^2*τ^2 ≤ (μ/2)*τ^3) :
    τ*μ*testGradientSquare K e f + (μ/2)*τ^3*testPair K f f ≤
      testPair K (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f)
        (carlemanSymmetric K e a p τ f + carlemanSkew K e X τ f) := by
  have h := carleman_basic_bound K e a ha X p τ C f
  have hg' := mul_le_mul_of_nonneg_left hg hτ
  have hm' := mul_le_mul_of_nonneg_left
    (weightedPair_lower_shift K (coefficientTransport e X p) p C μ hm f) (pow_nonneg hτ 3)
  have hq' := mul_le_mul_of_nonneg_left
    (weightedPair_le_of_bound K (coefficientElliptic e a (coefficientDivergence e X)) M hq f) hτ
  have ht' := mul_le_mul_of_nonneg_right ht (testPair_nonneg K f)
  nlinarith only [h, hg', hm', hq', ht']


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι]

def pointwiseQuadratic (a : ι → ι → SmoothScalar E) (x : E) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j x * v i * v j

def testQuadratic (a : ι → ι → SmoothScalar E) (f : ι → EllipticTest K) : ℝ :=
  ∑ i, ∑ j, weightedPair K (a i j) (f i) (f j)

lemma testQuadratic_integrable (a : ι → ι → SmoothScalar E) (f : ι → EllipticTest K) :
    Integrable (fun x => pointwiseQuadratic a x (fun i => f i x)) (volume : Measure E) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact weightedPair_integrable K (a i j) (f i) (f j)

lemma testQuadratic_integral (a : ι → ι → SmoothScalar E) (f : ι → EllipticTest K) :
    testQuadratic K a f = ∫ x, pointwiseQuadratic a x (fun i => f i x) := by
  unfold testQuadratic pointwiseQuadratic
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    weightedPair_integrable K (a i j) (f i) (f j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => weightedPair_integrable K (a i j) (f i) (f j))]
  apply Finset.sum_congr rfl
  intro j _
  exact weightedPair_integral K (a i j) (f i) (f j)

lemma testQuadratic_lower_bound (a : ι → ι → SmoothScalar E) (μ : ℝ)
    (h : ∀ x ∈ K, ∀ v : ι → ℝ, μ * ∑ i, v i * v i ≤ pointwiseQuadratic a x v)
    (f : ι → EllipticTest K) :
    μ * ∑ i, testPair K (f i) (f i) ≤ testQuadratic K a f := by
  have hi : Integrable (fun x => ∑ i, f i x * f i x) (volume : Measure E) :=
    integrable_finsetSum _ fun i _ => testPair_integrable K (f i) (f i)
  rw [testQuadratic_integral]
  have he : (∑ i, testPair K (f i) (f i)) = ∫ x, ∑ i, f i x * f i x := by
    simp only [testPair]
    rw [integral_finsetSum _ (fun i _ => testPair_integrable K (f i) (f i))]
  rw [he, ← integral_const_mul]
  apply integral_mono (hi.const_mul μ) (testQuadratic_integrable K a f)
  intro x
  by_cases hx : x ∈ K
  · exact h x hx (fun i => f i x)
  · have hf (i : ι) : f i x = 0 := (f i).zero_on_compl hx
    simp only [hf, mul_zero, Finset.sum_const_zero, pointwiseQuadratic, le_refl]

variable (e : ι → E)

def carlemanMatrix (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C : ℝ) : ι → ι → SmoothScalar E := fun j k =>
  (4 : ℝ) • (∑ i, a i j * SmoothScalar.directional (e i) (X k)) -
    (2 : ℝ) • (∑ l, X l * SmoothScalar.directional (e l) (a k j)) + (2*C) • a k j

lemma weightedPair_neg_coeff (a : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (-a) f g = -weightedPair K a f g := by
  simp only [weightedPair_integral]
  change (∫ point, -a point * f point * g point) = -(∫ point, a point * f point * g point)
  simp only [neg_mul, integral_neg]
lemma weightedPair_sub_coeff (a b : SmoothScalar E) (f g : EllipticTest K) :
    weightedPair K (a-b) f g = weightedPair K a f g - weightedPair K b f g := by
  simp only [sub_eq_add_neg, weightedPair_add_coeff, weightedPair_neg_coeff]

lemma carlemanMatrix_quadratic (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C : ℝ) (f : EllipticTest K) :
    testQuadratic K (carlemanMatrix e a X C) (fun i => testDerivative K (e i) f) =
      carlemanGradient K e a X f + 2*C * testEnergy K e a f f := by
  simp only [testQuadratic, carlemanMatrix, weightedPair_add_coeff, weightedPair_sub_coeff,
    weightedPair_smul_coeff, weightedPair_sum_coeff, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, carlemanGradient, testEnergy,
    show ∀ a g h, testPair K (testMultiply K a g) h = weightedPair K a g h from fun _ _ _ => rfl]
  have h1 : (∑ j, ∑ k, ∑ i, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f)) =
      ∑ i, ∑ j, ∑ k, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
        (testDerivative K (e j) f) (testDerivative K (e k) f) := by
    calc
      _ = ∑ j, ∑ i, ∑ k, weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
          (testDerivative K (e j) f) (testDerivative K (e k) f) :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have h2 : (∑ j, ∑ i, ∑ k, weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) =
      ∑ i, ∑ j, ∑ k, weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f) := Finset.sum_comm
  rw [h1, h2, Finset.sum_comm (f := fun j i => weightedPair K (a i j)
    (testDerivative K (e j) f) (testDerivative K (e i) f))]

lemma carleman_gradient_bound (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C μ : ℝ)
    (h : ∀ x ∈ K, ∀ v : ι → ℝ,
      μ * ∑ i, v i * v i ≤ pointwiseQuadratic (carlemanMatrix e a X C) x v)
    (f : EllipticTest K) :
    μ * testGradientSquare K e f ≤ carlemanGradient K e a X f + 2*C * testEnergy K e a f f := by
  rw [← carlemanMatrix_quadratic]
  exact testQuadratic_lower_bound K _ μ h _


end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

lemma coefficientGradient_apply (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (i : ι) (x : E) :
    coefficientGradient e a φ i x = ∑ j, a i j x * SmoothScalar.directional (e j) φ x := by
  simp only [coefficientGradient, SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]

lemma coefficientNorm_quadratic (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (x : E) :
    coefficientNorm e a φ x = realQuadratic (fun i j => a i j x)
      (fun i => SmoothScalar.directional (e i) φ x) := by
  simp only [coefficientNorm, SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply,
    coefficientGradient_apply, realQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coefficientNorm_pos (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (x : E)
    (ha : Matrix.PosDef (fun i j => a i j x))
    (hφ : (fun i => SmoothScalar.directional (e i) φ x) ≠ 0) :
    0 < coefficientNorm e a φ x := by
  have h := ha.dotProduct_mulVec_pos hφ
  rw [coefficientNorm_quadratic]
  simpa only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum,
    mul_left_comm, mul_assoc, realQuadratic] using h

lemma carlemanMatrix_apply (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (C : ℝ) (j k : ι) (x : E) :
    carlemanMatrix e a X C j k x =
      4 * (∑ i, a i j x * SmoothScalar.directional (e i) (X k) x) -
        2 * (∑ l, X l x * SmoothScalar.directional (e l) (a k j) x) + 2*C*a k j x := by
  simp only [carlemanMatrix, Subalgebra.coe_add, Subalgebra.coe_sub, Subalgebra.coe_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]

lemma carlemanMatrix_convexify_at (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (H C : ℝ)
    (x : E) (hx : ψ x = 0) (j k : ι) :
    carlemanMatrix e a (coefficientGradient e a (convexifyPhase ψ H)) C j k x =
      carlemanMatrix e a (coefficientGradient e a ψ) C j k x +
        4*H*coefficientGradient e a ψ j x * coefficientGradient e a ψ k x := by
  simp only [carlemanMatrix_apply, phase_gradient_at e a ψ H x hx,
    phase_gradient_derivative_at e a ψ H x hx, mul_add, Finset.sum_add_distrib]
  have hs : (∑ i, a i j x * (H * SmoothScalar.directional (e i) ψ x *
        coefficientGradient e a ψ k x)) =
      H * coefficientGradient e a ψ j x * coefficientGradient e a ψ k x := by
    rw [coefficientGradient_apply e a ψ j x]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i j]
    ring
  rw [hs]
  ring

lemma carlemanMatrix_quadratic_convexify (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (H C : ℝ)
    (x : E) (hx : ψ x = 0) (v : ι → ℝ) :
    pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a (convexifyPhase ψ H)) C) x v =
      pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a ψ) C) x v +
        4*H*(∑ i, coefficientGradient e a ψ i x * v i)^2 := by
  simp only [pointwiseQuadratic, carlemanMatrix_convexify_at e a ha ψ H C x hx,
    add_mul, Finset.sum_add_distrib]
  congr 1
  rw [pow_two]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma carlemanMatrix_energy_shift (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (C : ℝ) (x : E) (v : ι → ℝ) :
    pointwiseQuadratic (carlemanMatrix e a X C) x v =
      pointwiseQuadratic (carlemanMatrix e a X 0) x v +
        2*C*realQuadratic (fun i j => a i j x) v := by
  have hh (i j : ι) : carlemanMatrix e a X C i j x =
      carlemanMatrix e a X 0 i j x + 2*C*a i j x := by
    simp only [carlemanMatrix_apply]
    rw [ha j i]
    ring
  simp only [pointwiseQuadratic, hh, add_mul, Finset.sum_add_distrib,
    realQuadratic, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma exists_carleman_energy_shift (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (ψ : SmoothScalar E) (x : E)
    (hx : ψ x = 0) (hpos : Matrix.PosDef (fun i j => a i j x)) :
    ∃ C > 0, ∀ H ≥ 0, ∀ v,
      2 * squareSum v ≤ pointwiseQuadratic
        (carlemanMatrix e a (coefficientGradient e a (convexifyPhase ψ H)) C) x v := by
  obtain ⟨κ, hκ, hκbound⟩ := matrix_positive_coercive (fun i j => a i j x) hpos
  let B := ∑ i, ∑ j, |carlemanMatrix e a (coefficientGradient e a ψ) 0 i j x|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  let C := (B+2)/(2*κ)
  have hC : 0 < C := div_pos (by linarith) (by positivity)
  have hCeq : 2*C*κ = B+2 := by dsimp [C]; field_simp
  refine ⟨C, hC, fun H hH v => ?_⟩
  rw [carlemanMatrix_quadratic_convexify e a ha ψ H C x hx,
    carlemanMatrix_energy_shift e a ha]
  have hbase := realQuadratic_abs_bound
    (fun i j => carlemanMatrix e a (coefficientGradient e a ψ) 0 i j x) v
  change |pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a ψ) 0) x v| ≤
    B * squareSum v at hbase
  have hl := (neg_le_abs (pointwiseQuadratic (carlemanMatrix e a (coefficientGradient e a ψ) 0) x v)).trans hbase
  have hp := mul_le_mul_of_nonneg_left (hκbound v) (by positivity : 0 ≤ 2*C)
  have hnormal : 0 ≤ 4*H*(∑ i, coefficientGradient e a ψ i x * v i)^2 := by positivity
  have heq : 2*C*(κ*squareSum v) = (B+2)*squareSum v := by rw [← mul_assoc, hCeq]
  rw [heq] at hp
  nlinarith only [hl, hp, hnormal]



end YauCounterexamples
end

end OAI
