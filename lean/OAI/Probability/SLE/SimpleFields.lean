import Mathlib
import OAI.Probability.SLE.ItoIsometry

namespace OAI

/-! Simple Fields for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianIto TaylorMeshes
lemma stoppedDyadicIndex_bounds {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (t : ℝ≥0) :
    t ≤ dyadicTime T n (stoppedDyadicIndex T n t) ∧
    dyadicTime T n (stoppedDyadicIndex T n t) ≤ t + T / (2 : ℝ≥0)^n := by
  have hd : 0 < T / (2 : ℝ≥0)^n := by positivity
  constructor
  · apply (div_le_iff₀ hd).mp
    exact Nat.le_ceil _
  · change (Nat.ceil (t / (T / (2 : ℝ≥0)^n)) : ℝ≥0) * (T / (2 : ℝ≥0)^n) ≤ _
    calc
      _ ≤ (t / (T / (2 : ℝ≥0)^n) + 1) * (T / (2 : ℝ≥0)^n) :=
        mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ _ from zero_le)).le hd.le
      _ = _ := by rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul]

lemma stoppedDyadicIndex_tendsto {T : ℝ≥0} (hT : 0 < T) (t : ℝ≥0) :
    Tendsto (fun n => mesh T n (stoppedDyadicIndex T n t)) atTop (𝓝 (t : ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using (tendsto_const_nhds (x := (t : ℝ))).add (mesh_step_tendsto T))
  · intro n
    simpa only [← coe_dyadicTime] using
      (show (t : ℝ) ≤ (dyadicTime T n (stoppedDyadicIndex T n t) : ℝ) by
        exact_mod_cast (stoppedDyadicIndex_bounds hT n t).1)
  · intro n
    have hh := (stoppedDyadicIndex_bounds hT n t).2
    simpa only [← coe_dyadicTime, NNReal.coe_add, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
      using (show (dyadicTime T n (stoppedDyadicIndex T n t) : ℝ) ≤
        ((t + T / (2 : ℝ≥0)^n : ℝ≥0) : ℝ) by exact_mod_cast hh)

lemma stopping_before_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime f (fun ω => (τ ω : WithTop ℝ≥0))) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | t < τ ω} := by
  simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using (hτ.measurableSet_le t).compl

lemma stopped_coefficient_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime f (fun ω => (τ ω : WithTop ℝ≥0))) (t : ℝ≥0)
    {C : Ω → ℝ} (hC : Measurable[f t] C) :
    Measurable[f t] (fun ω => if t < τ ω then C ω else 0) := by
  classical
  exact hC.ite (stopping_before_measurable hτ t) measurable_const

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes TimeField

lemma prefix_mask_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) {k N : ℕ} (hk : k ≤ N) :
    (∑ i ∈ Finset.range N, if i < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  classical
  calc
    _ = ∑ i ∈ Finset.range k, if i < k then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i hi hni
      simp only [Finset.mem_range] at hni
      simp [hni]
    _ = _ := Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.mp hi)

noncomputable def stoppedFieldSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (F : Ω → ℝ → ℝ → ℝ) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), (if dyadicTime T n i < τ ω then
    deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω) else 0) *
      (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)

lemma stoppedFieldSum_eq_prefix {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ≥0}
    (hT : 0 < T) (F : Ω → ℝ → ℝ → ℝ) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (n : ℕ) (ω : Ω) :
    stoppedFieldSum B T F τ n ω =
      ∑ i ∈ Finset.range (stoppedDyadicIndex T n (τ ω)),
        deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω) *
          (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω) := by
  unfold stoppedFieldSum
  simp_rw [← lt_stoppedDyadicIndex hT, ite_mul, zero_mul]
  exact prefix_mask_sum _ (stoppedDyadicIndex_le hT n (hτ ω))

 

theorem stopped_fieldSum_tendsto {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ s, Measurable (B s))
    (T : ℝ≥0) (F V : Ω → ℝ → ℝ → ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbτ : ∀ ω, τ ω ≤ T)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) T)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => F ω t (B t.toNNReal ω)) (Icc 0 T))
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)]
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)))
    (hC2 : ∀ n i, MemLp
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P,
      |iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)| ≤ K₂) :
    ∀ᵐ ω ∂P, Tendsto (fun n => stoppedFieldSum B T F τ n ω) atTop
      (𝓝 (F ω (τ ω) (B (τ ω) ω) - F ω 0 (B 0 ω) -
        (∫ t in (0 : ℝ)..(τ ω : ℝ), V ω t (B t.toNNReal ω)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ),
          iteratedDeriv 2 (F ω t) (B t.toNNReal ω))) := by
  classical
  rcases eq_or_lt_of_le (zero_le : 0 ≤ T) with hT | hT
  · subst T
    have hτ0 (ω : Ω) : τ ω = 0 := le_antisymm (hbτ ω) zero_le
    simp [stoppedFieldSum, dyadicTime, hτ0]
  let C (n i : ℕ) (ω : Ω) := if dyadicTime T n i < τ ω then
    iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω) else 0
  have hs (n i : ℕ) : MeasurableSet[pastSigma B (dyadicTime T n i)]
      {ω | dyadicTime T n i < τ ω} := by
    have he := stopping_before_measurable hτ (dyadicTime T n i)
    exact (le_of_eq (Filtration.natural_eq_comap B (fun t => (hm t).stronglyMeasurable) _)) _ he
  have hCp (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (C n i) :=
    (hC n i).ite (hs n i) measurable_const
  have hC2p (n i : ℕ) : MemLp (C n i) 2 P := by
    have hma := (hCp n i).mono
      (le_trans (le_of_eq (Filtration.natural_eq_comap B
        (fun t => (hm t).stronglyMeasurable) _).symm) (Filtration.le _ _)) le_rfl
    apply MemLp.of_bound hma.aestronglyMeasurable K₂
    filter_upwards [hbound n i] with ω hω
    dsimp only [C]
    split_ifs <;> simpa only [Real.norm_eq_abs, abs_zero] using (by assumption : _ ≤ K₂)
  have hbp (n i : ℕ) : ∀ᵐ ω ∂P, |C n i ω| ≤ K₂ := by
    filter_upwards [hbound n i] with ω hω
    dsimp only [C]
    split_ifs <;> simp_all
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T C hCp hC2p K₂ hK₂ hbp
  filter_upwards [hB.cont, quadraticSum_tendsto hB T, he, hreg, hcont] with ω hcω hQω heω hrω hfω
  let b : ℝ → ℝ := fun t => B t.toNNReal ω
  let k : ℕ → ℕ := fun n => stoppedDyadicIndex T n (τ ω)
  have hk (n : ℕ) : k n ≤ 2^n := stoppedDyadicIndex_le hT n (hbτ ω)
  have hS : (τ ω : ℝ) ∈ Icc (0 : ℝ) T := ⟨(τ ω).coe_nonneg, by exact_mod_cast hbτ ω⟩
  have hlim : Tendsto (fun n => mesh T n (k n)) atTop (𝓝 (τ ω : ℝ)) := stoppedDyadicIndex_tendsto hT _
  have hb : Continuous b := hcω.comp continuous_real_toNNReal
  have hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1))-b (mesh T n i))^2) atTop (𝓝 (T : ℝ)) := by
    simpa only [b, mesh_toNNReal, quadraticSum] using hQω
  obtain ⟨K₃, hK₃, h₃⟩ := hrω.third_bound
  have hr := mesh_prefix_remainder_tendsto
    (f := fun n i => F ω (mesh T n i)) (fun _ _ => hrω.smooth _) T.coe_nonneg
    hb.continuousOn hK₃ (fun _ _ x => h₃ _ x) k hk hQ
  have hriem := mesh_prefix_riemann_tendsto T.coe_nonneg hrω.second_cont k hk hS hlim
  have htime := mesh_prefix_time_increment_tendsto (b := b) T.coe_nonneg hrω.time_cont
    hrω.time_deriv hrω.drift_cont k hk hS hlim
  let Q (n : ℕ) := ∑ i ∈ Finset.range (k n),
    iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
      (b (mesh T n (i+1))-b (mesh T n i))^2
  have hQweighted : Tendsto Q atTop
      (𝓝 (∫ t in (0 : ℝ)..(τ ω : ℝ), iteratedDeriv 2 (F ω t) (b t))) := by
    have heq (n : ℕ) : Q n = dyadicQuadraticError B T C n ω +
        ∑ i ∈ Finset.range (k n), iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
          ((T : ℝ) / (2 : ℝ)^n) := by
      have hmask : dyadicQuadraticError B T C n ω =
          ∑ i ∈ Finset.range (k n),
          iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
            ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ) / (2 : ℝ)^n) := by
        simp only [dyadicQuadraticError, C, b, mesh_toNNReal]
        simp_rw [← lt_stoppedDyadicIndex hT, ite_mul, zero_mul]
        exact prefix_mask_sum _ (hk n)
      rw [hmask, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simpa only [b, ← heq, zero_add] using heω.add hriem
  have hTel (n : ℕ) : ∑ i ∈ Finset.range (k n),
      (F ω (mesh T n (i+1)) (b (mesh T n (i+1))) - F ω (mesh T n i) (b (mesh T n i))) =
        F ω (mesh T n (k n)) (b (mesh T n (k n))) - F ω 0 (B 0 ω) := by
    rw [Finset.sum_range_sub (fun i => F ω (mesh T n i) (b (mesh T n i))) (k n), mesh_zero]
    simp only [b, Real.toNNReal_zero]
  have hIdentity (n : ℕ) : stoppedFieldSum B T F τ n ω =
      F ω (mesh T n (k n)) (b (mesh T n (k n))) - F ω 0 (B 0 ω) -
        (∑ i ∈ Finset.range (k n),
          (F ω (mesh T n (i+1)) (b (mesh T n (i+1))) -
            F ω (mesh T n i) (b (mesh T n (i+1))))) - (1/2 : ℝ) * Q n -
        ∑ i ∈ Finset.range (k n), remainder₂ (F ω (mesh T n i))
          (b (mesh T n i)) (b (mesh T n (i+1))) := by
    rw [← hTel n]
    simp only [Q, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [stoppedFieldSum_eq_prefix B hT F τ hbτ]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [remainder₂, iteratedDeriv_succ, iteratedDeriv_zero, b, mesh_toNNReal]
    ring
  have hend := (hfω _ hS).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall fun n => mesh_mem T T.coe_nonneg n (k n) (hk n)⟩)
  have ht := (((hend.sub_const (F ω 0 (B 0 ω))).sub htime).sub
    (hQweighted.const_mul (1/2 : ℝ))).sub hr
  simpa only [Function.comp_apply, b, Real.toNNReal_coe, ← hIdentity, sub_zero] using ht

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

theorem ClippedLogSolution.compact_stopped_field_ito
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (φ : (ℂ × ℝ) × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbτ : ∀ ω, τ ω ≤ T) :
    ∀ᵐ ω ∂P, Tendsto (fun n => stoppedFieldSum B T (fun ω t x => φ (c.Q t ω, x)) τ n ω) atTop
      (𝓝 (φ (c.Q (τ ω) ω, B (τ ω) ω) - φ (c.Q 0 ω, B 0 ω) -
        (∫ t in (0 : ℝ)..(τ ω : ℝ), fderiv ℝ φ (c.Q t ω, B t.toNNReal ω) (c.velocity t ω, 0)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ),
          iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t.toNNReal ω))) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz (spatialPartial φ 2)
    (spatialPartial_smooth φ hφ 2) (spatialPartial_compact φ hφc 2)
  have hb (t : ℝ≥0) (ω : Ω) :
      |iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t ω)| ≤ K := by
    simpa only [← spatialPartial_eq_iteratedDeriv φ hφ, Real.norm_eq_abs] using hK (c.Q t ω, B t ω)
  have hma (t : ℝ≥0) := c.partial_adapted φ hφ 2 t
  have hp (t : ℝ≥0) : MemLp
      (fun ω => iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t ω)) 2 P := by
    exact MemLp.of_bound ((hma t).mono (Filtration.le _ _) le_rfl).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb t ω)
  apply stopped_fieldSum_tendsto hB hm T (fun ω t x => φ (c.Q t ω, x))
    (fun ω t x => fderiv ℝ φ (c.Q t ω, x) (c.velocity t ω, 0)) τ hτ hbτ
    (Eventually.of_forall (c.compact_field_regular hBc φ hφ hφc T))
    (Eventually.of_forall fun ω =>
      (hφ.continuous.comp ((c.lipschitz ω).continuous.prodMk
        ((hBc ω).comp continuous_real_toNNReal))).continuousOn)
    (fun n i => ?_) (fun n i => ?_) K K.coe_nonneg (fun n i => ?_)
  · have hx := (hma (dyadicTime T n i)).mono
      (le_of_eq (natural_eq_pastSigma (B := B) (hm := hm) (dyadicTime T n i))) le_rfl
    simpa only [mesh_eq_dyadicTime] using hx
  · simpa only [mesh_eq_dyadicTime] using hp (dyadicTime T n i)
  · exact Eventually.of_forall fun ω => by
      simpa only [mesh_eq_dyadicTime] using hb (dyadicTime T n i) ω

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

lemma deriv_fiber_fderiv (φ : (ℂ × ℝ) × ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (q : ℂ × ℝ) (x : ℝ) :
    deriv (fun y => φ (q, y)) x = fderiv ℝ φ (q, x) (0, 1) := by
  exact ((hφ (q, x)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_const x q).prodMk (hasDerivAt_id x))).deriv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

 
noncomputable def greenLogCoefficient (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  greenLogDensity κ q x * (greenExponent κ * Real.sqrt κ *
    (q.1.re - Real.sqrt κ * x) / greenLogNormSq κ q x)

 

theorem ClippedLogSolution.stopped_green_ito
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (R : ℝ) (hR : 0 ≤ R)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbτ : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (if dyadicTime T n i < τ ω then
        greenLogCoefficient κ (c.Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω)
      else 0) * (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) atTop
      (𝓝 (greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) - greenLogDensity κ q₀ 0)) := by
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_green_field κ R hR
  have hφ1 (q : ℂ × ℝ) (x : ℝ) (hq : ‖(q, x)‖ ≤ R) :
      deriv (fun y => φ (q, y)) x = greenLogCoefficient κ q x := by
    rw [deriv_fiber_fderiv φ (hφ.differentiable (by simp)), hφD q x hq,
      ← deriv_fiber_fderiv _ ((greenLogDensity_contDiff κ).differentiable (by simp))]
    exact (greenLogDensity_spatial_derivative κ q x).deriv
  have hrep := c.compact_stopped_field_ito hB hBc φ hφ hφc T τ hτ hbτ
  filter_upwards [hrep, hB.eval_zero_ae_eq_zero] with ω hrepω hB0
  have heq (n : ℕ) : stoppedFieldSum B T (fun ω t x => φ (c.Q t ω, x)) τ n ω =
      ∑ i ∈ Finset.range (2^n),
        (if dyadicTime T n i < τ ω then
          greenLogCoefficient κ (c.Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω)
        else 0) * (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mesh_eq_dyadicTime]
    split_ifs with ht
    · rw [hφ1 _ _ (hinside ω _ ht.le).1]
    · rfl
  let V (t : ℝ) := fderiv ℝ φ (c.Q t ω, B t.toNNReal ω) (c.velocity t ω, 0)
  let D (t : ℝ) := iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t.toNNReal ω)
  have hpair : Continuous (fun t : ℝ => (c.Q t ω, B t.toNNReal ω)) :=
    (c.lipschitz ω).continuous.prodMk ((hBc ω).comp continuous_real_toNNReal)
  have hVc : Continuous V := ((hφ.continuous_fderiv (by simp)).comp hpair).clm_apply
    ((c.velocity_continuous hBc ω).prodMk continuous_const)
  have hDc : Continuous D := by
    simpa only [Function.comp_def, spatialPartial_eq_iteratedDeriv φ hφ] using
      (spatialPartial_smooth φ hφ 2).continuous.comp hpair
  have hz : (∫ t in (0 : ℝ)..(τ ω : ℝ), V t) +
      (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ), D t = 0 := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hVc.intervalIntegrable _ _) ((hDc.const_mul _).intervalIntegrable _ _)]
    calc
      _ = ∫ t in (0 : ℝ)..(τ ω : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (τ ω).coe_nonneg] at ht
        have htn : t.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2
        obtain ⟨hball, hlo, hhi⟩ := hinside ω t.toNNReal htn
        rw [Real.coe_toNNReal _ ht.1] at hball hlo hhi
        exact compact_green_drift_zero κ hκ hκ8 lo hi hle φ _ _
          (hφD _ _ hball) (hφ2 _ _ hball) ⟨hlo, hhi⟩
      _ = 0 := by simp
  have hend := hφeq _ _ (hinside ω (τ ω) le_rfl).1
  have hstart := hφeq _ _ (hinside ω 0 zero_le).1
  simp only [NNReal.coe_zero, c.initial ω, hB0] at hstart
  have hval : φ (c.Q (τ ω) ω, B (τ ω) ω) - φ (c.Q 0 ω, B 0 ω) -
      (∫ t in (0 : ℝ)..(τ ω : ℝ), V t) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ), D t =
        greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) - greenLogDensity κ q₀ 0 := by
    rw [hend, c.initial ω, hB0, hstart]
    linarith
  simpa only [heq, ← hval, V, D] using hrepω

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

lemma stopped_energy_tendsto {T : ℝ≥0} {S : ℝ≥0} (hS : S ≤ T)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (if dyadicTime T n i < S then f (dyadicTime T n i) else 0) *
        ((dyadicTime T n (i+1) : ℝ) - dyadicTime T n i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..(S : ℝ), f t)) := by
  classical
  rcases eq_or_lt_of_le (zero_le : 0 ≤ T) with hT | hT
  · subst T
    have hS0 : S = 0 := le_antisymm hS zero_le
    simp [hS0, dyadicTime]
  · have hh := mesh_prefix_riemann_tendsto T.coe_nonneg hf
      (fun n => stoppedDyadicIndex T n S)
      (fun n => stoppedDyadicIndex_le hT n hS)
      (show (S : ℝ) ∈ Icc (0 : ℝ) T from ⟨S.coe_nonneg, by exact_mod_cast hS⟩)
      (stoppedDyadicIndex_tendsto hT S)
    have heq (n : ℕ) : (∑ i ∈ Finset.range (2^n),
        (if dyadicTime T n i < S then f (dyadicTime T n i) else 0) *
          ((dyadicTime T n (i+1) : ℝ) - dyadicTime T n i)) =
        ∑ i ∈ Finset.range (stoppedDyadicIndex T n S), f (mesh T n i) *
          ((T : ℝ) / (2 : ℝ)^n) := by
      simp_rw [dyadicTime_step, ← lt_stoppedDyadicIndex hT, ite_mul, zero_mul]
      rw [SLEExactGauge.prefix_mask_sum _ (stoppedDyadicIndex_le hT n hS)]
      simp only [mesh_eq_dyadicTime]
    simpa only [heq] using hh

end SLEExactGauge

 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge

lemma gaussian_exponential_lintegral (v : ℝ≥0) (c : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c * x)) ∂gaussianReal 0 v) =
      ENNReal.ofReal (Real.exp ((v : ℝ) * c ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal c)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  congr 1
  simpa only [mgf, zero_mul, zero_add] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) c

lemma gaussian_compensated_exponential (v : ℝ≥0) (a c : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (a + c * x - (v : ℝ) * c ^ 2 / 2)) ∂gaussianReal 0 v) =
      ENNReal.ofReal (Real.exp a) := by
  have he (x : ℝ) : Real.exp (a + c * x - (v : ℝ) * c ^ 2 / 2) =
      Real.exp (a - (v : ℝ) * c ^ 2 / 2) * Real.exp (c * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop), gaussian_exponential_lintegral,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

 

lemma independent_gaussian_exponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ × ℝ} {Y : Ω → ℝ} {v : ℝ≥0}
    (hX : Measurable X) (hY : HasLaw Y (gaussianReal 0 v) μ)
    (hi : IndepFun X Y μ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω).1 + (X ω).2 * Y ω -
      (v : ℝ) * (X ω).2 ^ 2 / 2)) ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω).1) ∂μ := by
  let f (p : (ℝ × ℝ) × ℝ) := ENNReal.ofReal
    (Real.exp (p.1.1 + p.1.2 * p.2 - (v : ℝ) * p.1.2 ^ 2 / 2))
  have hf : Measurable f := by unfold f; fun_prop
  have hmap : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (gaussianReal 0 v) := by
    rw [IndepFun.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable hi, hY.map_eq]
  calc
    _ = ∫⁻ p, f p ∂μ.map (fun ω => (X ω, Y ω)) :=
      (lintegral_map' hf.aemeasurable (hX.aemeasurable.prodMk hY.aemeasurable)).symm
    _ = ∫⁻ p, ∫⁻ x, f (p, x) ∂gaussianReal 0 v ∂μ.map X := by
      rw [hmap, lintegral_prod f hf.aemeasurable]
    _ = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) ∂μ.map X :=
      lintegral_congr fun p => gaussian_compensated_exponential v p.1 p.2
    _ = _ := lintegral_map' (by fun_prop) hX.aemeasurable

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def driverPredictableSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, C i ω * (B (t (i+1)) ω - B (t i) ω)

noncomputable def driverPredictableEnergy {Ω : Type*} (t : ℕ → ℝ≥0)
    (C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, C i ω ^ 2 * ((t (i+1) : ℝ) - t i)

lemma driverPredictableSum_measurable_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t i)] (C i))
    (n : ℕ) : Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t n)]
      (driverPredictableSum B t C n) := by
  have hB := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted
  apply Finset.measurable_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  exact ((hC i).mono (Filtration.mono _ (ht hin.le)) le_rfl).mul
    ((hB.measurable_le (ht (Nat.succ_le_iff.mpr hin))).sub (hB.measurable_le (ht hin.le)))

lemma driverPredictableEnergy_measurable_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t i)] (C i))
    (n : ℕ) : Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t n)]
      (driverPredictableEnergy t C n) := by
  apply Finset.measurable_sum
  intro i hi
  exact (((hC i).mono (Filtration.mono _ (ht (Finset.mem_range.mp hi).le)) le_rfl).pow_const 2).mul_const _

 

theorem driverPredictable_exponential
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t i)] (C i))
    (θ : ℝ) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * driverPredictableSum B t C n ω -
      θ ^ 2 * driverPredictableEnergy t C n ω / 2)) ∂P) = 1 := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  induction n with
  | zero => simp [driverPredictableSum, driverPredictableEnergy]
  | succ n hprev =>
    let a (ω : Ω) := θ * driverPredictableSum B t C n ω -
      θ ^ 2 * driverPredictableEnergy t C n ω / 2
    let X (ω : Ω) : ℝ × ℝ := (a ω, θ * C n ω)
    let Y (ω : Ω) := B (t (n+1)) ω - B (t n) ω
    let v := t (n+1) - t n
    have hXp : Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t n)] X :=
      (((driverPredictableSum_measurable_past B hm t ht C hC n).const_mul θ).sub
        (((driverPredictableEnergy_measurable_past B hm t ht C hC n).const_mul (θ^2)).div_const 2)).prodMk
          ((hC n).const_mul θ)
    have hX : Measurable X := hXp.mono (Filtration.le _ _) le_rfl
    have hY : HasLaw Y (gaussianReal 0 v) P := by
      simpa only [Y, v, add_tsub_cancel_of_le (ht (Nat.le_succ n))] using
        (hB.toIsPreBrownianReal.shift (t n)).hasLaw_eval v
    have hi : IndepFun X Y P := by
      rw [IndepFun_iff_Indep]
      have hb := brownian_increment_indep_natural hB hm (t n) v
      dsimp only [v] at hb
      rw [add_tsub_cancel_of_le (ht (Nat.le_succ n))] at hb
      exact indep_of_indep_of_le hb hXp.comap_le le_rfl
    have hvc : (v : ℝ) = (t (n+1) : ℝ) - t n :=
      NNReal.coe_sub (ht (Nat.le_succ n))
    have he (ω : Ω) : θ * driverPredictableSum B t C (n+1) ω -
        θ ^ 2 * driverPredictableEnergy t C (n+1) ω / 2 =
        (X ω).1 + (X ω).2 * Y ω - (v : ℝ) * (X ω).2 ^ 2 / 2 := by
      simp only [driverPredictableSum, driverPredictableEnergy, Finset.sum_range_succ,
        X, a, Y, hvc]
      ring
    simp_rw [he]
    rw [independent_gaussian_exponential hX hY hi]
    exact hprev

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

 

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

lemma greenLogCoefficient_eq_deriv (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    greenLogCoefficient κ q x = deriv (greenLogDensity κ q) x :=
  (greenLogDensity_spatial_derivative κ q x).deriv.symm

lemma greenLogCoefficient_continuous (κ : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => greenLogCoefficient κ p.1 p.2) := by
  have hc := (spatialPartial_smooth
    (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) (greenLogDensity_contDiff κ) 1).continuous
  convert hc using 1
  funext p
  rw [spatialPartial_eq_iteratedDeriv _ (greenLogDensity_contDiff κ), iteratedDeriv_one]
  exact greenLogCoefficient_eq_deriv κ p.1 p.2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

lemma ClippedLogSolution.green_coefficient_adapted
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (t : ℝ≥0) :
    Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) t]
      (fun ω => greenLogCoefficient κ (c.Q t ω) (B t ω)) := by
  simpa only [iteratedDeriv_one, greenLogCoefficient_eq_deriv] using
    c.partial_adapted (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2)
      (greenLogDensity_contDiff κ) 1 t

 

theorem ClippedLogSolution.stopped_green_exponential
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (R : ℝ) (hR : 0 ≤ R)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbτ : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi)
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) - greenLogDensity κ q₀ 0) -
        θ ^ 2 * (∫ t in (0 : ℝ)..(τ ω : ℝ),
          (greenLogCoefficient κ (c.Q t ω) (B t.toNNReal ω)) ^ 2) / 2)) ∂P) ≤ 1 := by
  classical
  let C (n i : ℕ) (ω : Ω) := if dyadicTime T n i < τ ω then
    greenLogCoefficient κ (c.Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0
  have hCa (n i : ℕ) : Measurable[Filtration.natural B
      (fun s => (hm s).stronglyMeasurable) (dyadicTime T n i)] (C n i) :=
    (c.green_coefficient_adapted _).ite (stopping_before_measurable hτ _) measurable_const
  let X (n : ℕ) := driverPredictableSum B (dyadicTime T n) (C n) (2^n)
  let E (n : ℕ) := driverPredictableEnergy (dyadicTime T n) (C n) (2^n)
  have hXm (n : ℕ) : Measurable (X n) :=
    (driverPredictableSum_measurable_past B hm _ (dyadicTime_mono T n) _ (hCa n) _).mono
      (Filtration.le _ _) le_rfl
  have hEm (n : ℕ) : Measurable (E n) :=
    (driverPredictableEnergy_measurable_past B hm _ (dyadicTime_mono T n) _ (hCa n) _).mono
      (Filtration.le _ _) le_rfl
  have hx := c.stopped_green_ito hB hBc hκ hκ8 R hR T τ hτ hbτ hinside
  have he : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop
      (𝓝 (∫ t in (0 : ℝ)..(τ ω : ℝ),
        (greenLogCoefficient κ (c.Q t ω) (B t.toNNReal ω)) ^ 2)) := by
    apply Eventually.of_forall
    intro ω
    have hc : Continuous (fun t : ℝ => greenLogCoefficient κ (c.Q t ω) (B t.toNNReal ω)) :=
      (greenLogCoefficient_continuous κ).comp
        ((c.lipschitz ω).continuous.prodMk ((hBc ω).comp continuous_real_toNNReal))
    have hl := stopped_energy_tendsto (hbτ ω) (hc.pow 2).continuousOn
    simpa only [E, driverPredictableEnergy, C, ite_pow, zero_pow (by decide : 2 ≠ 0),
      Pi.pow_apply, Real.toNNReal_coe] using hl
  exact compensated_exponential_limit_energy X E _ _ θ
    (fun n => (((hXm n).const_mul θ).sub (((hEm n).const_mul (θ^2)).div_const 2)).exp.ennreal_ofReal.aemeasurable)
    hx he (fun n => (driverPredictable_exponential hB hm _ (dyadicTime_mono T n) _ (hCa n) θ _).le)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi}

 

lemma clipped_family_initial_continuous
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (t : ℝ≥0) (ω : Ω) : Continuous (fun q => (c q).Q t ω) := by
  obtain ⟨L, K, hb, hl⟩ := clippedLogLoewnerField_bounds lo hi hle
  let D : ℝ≥0 := ⟨Real.exp ((K : ℝ) * (t : ℝ)), (Real.exp_pos _).le⟩
  apply (show LipschitzWith D (fun q => (c q).Q t ω) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  have hd (x : ℂ × ℝ) (s : ℝ) (hs : s ∈ Ico (0 : ℝ) (t : ℝ)) :
      HasDerivWithinAt (fun v => (c x).Q v ω)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * B s.toNNReal ω) ((c x).Q s ω)) (Ici s) s :=
    ((c x).derivative ω s hs.1).mono (Ici_subset_Ici.mpr hs.1)
  have hh := dist_le_of_trajectories_ODE
    (fun s => hl (Real.sqrt κ * B s.toNNReal ω))
    ((c q).lipschitz ω).continuous.continuousOn (hd q)
    ((c q').lipschitz ω).continuous.continuousOn (hd q')
    (show dist ((c q).Q 0 ω) ((c q').Q 0 ω) ≤ dist q q' by rw [(c q).initial, (c q').initial])
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  change dist ((c q).Q t ω) ((c q').Q t ω) ≤ Real.exp ((K : ℝ) * (t : ℝ)) * dist q q'
  simpa only [sub_zero, mul_comm] using hh

lemma clipped_family_past_measurable
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q) (t : ℝ≥0) :
    @Measurable ((ℂ × ℝ) × Ω) (ℂ × ℝ)
      ((inferInstance : MeasurableSpace (ℂ × ℝ)).prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))
      (inferInstance : MeasurableSpace (ℂ × ℝ)) (fun p => (c p.1).Q t p.2) := by
  have hc := clipped_family_initial_continuous c t
  have ha (q : ℂ × ℝ) := (c q).adapted t
  let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) t
  exact measurable_uncurry_of_continuous_of_measurable hc ha

lemma clipped_family_joint_measurable
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q) :
    Measurable (fun p : ℝ≥0 × ((ℂ × ℝ) × Ω) => (c p.2.1).Q p.1 p.2.2) := by
  change Measurable (Function.uncurry (fun (t : ℝ≥0) (p : (ℂ × ℝ) × Ω) => (c p.1).Q t p.2))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro p
    exact ((c p.1).lipschitz p.2).continuous.comp NNReal.continuous_coe
  · intro t
    have h := clipped_family_past_measurable c t
    exact h.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (Filtration.le _ _))) le_rfl

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
open L2Limit

end SLEExactGauge
end
end
end
end
end

end OAI
