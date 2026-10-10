import Mathlib
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI

/-! Integral Limits for chordal SLE. -/

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
namespace SLEExactGauge.BrownianPredictable
lemma predictableTerm_square_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hCa : ∀ i, AEMeasurable (C i) P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i)) (i : ℕ) :
    (∫ ω, (C i ω * φ i (B (t (i+1)) ω - B (t i) ω)) ^ 2 ∂P) =
      (∫ ω, C i ω ^ 2 ∂P) * (∫ x, φ i x ^ 2 ∂gaussianReal 0 (t (i+1)-t i)) := by
  simpa only [mul_pow] using past_mul_feature_integral hB (ht (Nat.le_succ i))
    ((hC i).pow_const 2) ((hCa i).pow_const 2) (fun x => φ i x ^ 2) ((hφ i).pow_const 2)

 

theorem predictableFeatureSum_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ2 : ∀ i, MemLp (φ i) 2 (gaussianReal 0 (t (i+1)-t i)))
    (hφ0 : ∀ i, (∫ x, φ i x ∂gaussianReal 0 (t (i+1)-t i)) = 0) (n : ℕ) :
    (∫ ω, predictableFeatureSum B t C φ n ω ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, (∫ ω, C i ω ^ 2 ∂P) *
        (∫ x, φ i x ^ 2 ∂gaussianReal 0 (t (i+1)-t i)) := by
  let Y : ℕ → Ω → ℝ := fun i ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω)
  have hY (i : ℕ) : MemLp (Y i) 2 P :=
    predictableTerm_memLp_two hB t ht C hC hC2 φ hφ hφ2 i
  have hY0 (i : ℕ) : (∫ ω, Y i ω ∂P) = 0 :=
    predictableTerm_integral hB t ht C hC (fun i => (hC2 i).aemeasurable) φ hφ hφ0 i
  have hsum : MemLp (predictableFeatureSum B t C φ n) 2 P :=
    memLp_finsetSum _ (fun i _ => hY i)
  have hsum0 : (∫ ω, predictableFeatureSum B t C φ n ω ∂P) = 0 := by
    unfold predictableFeatureSum
    rw [integral_finsetSum _ (fun i _ => (hY i).integrable (by norm_num))]
    exact Finset.sum_eq_zero (fun i _ => hY0 i)
  have hv : (∫ ω, predictableFeatureSum B t C φ n ω ^ 2 ∂P) =
      variance (predictableFeatureSum B t C φ n) P := by
    rw [variance_eq_sub hsum, hsum0]
    simp
  rw [hv]
  change variance (fun ω => ∑ i ∈ Finset.range n, Y i ω) P = _
  rw [variance_fun_sum' (fun i _ => hY i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single_of_mem i hi (fun j _ hji => ?_)]
  · rw [covariance_self (hY i).aemeasurable, variance_eq_sub (hY i), hY0]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
    exact predictableTerm_square_integral hB t ht C hC
      (fun i => (hC2 i).aemeasurable) φ hφ i
  · exact predictableTerm_covariance_zero hB t ht C hC hC2 φ hφ hφ2 hφ0 hji.symm

lemma centeredSquare_gaussian_memLp (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2 - (v : ℝ)) 2 (gaussianReal 0 v) :=
  (gaussian_square_memLp v).sub (memLp_const _)

lemma centeredSquare_gaussian_mean (v : ℝ≥0) :
    (∫ x : ℝ, x^2 - (v : ℝ) ∂gaussianReal 0 v) = 0 := by
  rw [integral_sub ((gaussian_square_memLp v).integrable (by norm_num)) (integrable_const _),
    gaussian_second_moment]
  simp

lemma centeredSquare_gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, (x^2 - (v : ℝ))^2 ∂gaussianReal 0 v) = 2 * (v : ℝ)^2 := by
  have hv := variance_eq_integral (gaussian_square_memLp v).aemeasurable
  rw [gaussian_second_moment, gaussian_square_variance] at hv
  exact hv.symm

 
theorem brownian_predictableSum_isometry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, C i ω * (B (t (i+1)) ω - B (t i) ω))^2 ∂P) =
      ∑ i ∈ Finset.range n, (∫ ω, C i ω ^ 2 ∂P) * ((t (i+1) : ℝ) - t i) := by
  have hi := predictableFeatureSum_second_moment hB t ht C hC hC2
    (fun _ x => x) (fun _ => measurable_id)
    (fun _ => memLp_id_gaussianReal' 2 (by norm_num))
    (fun _ => by simp) n
  simpa only [predictableFeatureSum, gaussian_second_moment,
    NNReal.coe_sub (ht (Nat.le_succ _))] using hi

 

theorem brownian_predictableQuadraticError_isometry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, C i ω *
      ((B (t (i+1)) ω - B (t i) ω)^2 - ((t (i+1) : ℝ) - t i)))^2 ∂P) =
      ∑ i ∈ Finset.range n, (∫ ω, C i ω ^ 2 ∂P) *
        (2 * ((t (i+1) : ℝ) - t i)^2) := by
  have hi := predictableFeatureSum_second_moment hB t ht C hC hC2
    (fun i x => x^2 - (t (i+1)-t i : ℝ≥0)) (fun _ => by fun_prop)
    (fun _ => centeredSquare_gaussian_memLp _)
    (fun _ => centeredSquare_gaussian_mean _) n
  simp only [predictableFeatureSum] at hi
  simp_rw [centeredSquare_gaussian_second_moment] at hi
  simpa only [NNReal.coe_sub (ht (Nat.le_succ _))] using hi

 
def dyadicTime (T : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  (i : ℝ≥0) * (T / (2 : ℝ≥0)^n)

lemma dyadicTime_mono (T : ℝ≥0) (n : ℕ) : Monotone (dyadicTime T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

lemma dyadicTime_step (T : ℝ≥0) (n i : ℕ) :
    (dyadicTime T n (i+1) : ℝ) - dyadicTime T n i = (T : ℝ) / (2 : ℝ)^n := by
  simp only [dyadicTime]
  push_cast
  ring

 

def dyadicQuadraticError {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (C : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), C n i ω *
    ((B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)^2 -
      (T : ℝ) / (2 : ℝ)^n)

lemma dyadicQuadraticError_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (n : ℕ) :
    MemLp (dyadicQuadraticError B T C n) 2 P := by
  apply memLp_finsetSum
  intro i hi
  have hh := predictableTerm_memLp_two hB (dyadicTime T n) (dyadicTime_mono T n)
    (C n) (hC n) (hC2 n)
    (fun i x => x^2 - (dyadicTime T n (i+1) - dyadicTime T n i : ℝ≥0))
    (fun _ => by fun_prop) (fun _ => centeredSquare_gaussian_memLp _) i
  simpa only [NNReal.coe_sub (dyadicTime_mono T n (Nat.le_succ _)),
    dyadicTime_step] using hh

lemma dyadicQuadraticError_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (n : ℕ) :
    (∫ ω, dyadicQuadraticError B T C n ω ∂P) = 0 := by
  have hterm (i : ℕ) := predictableTerm_memLp_two hB (dyadicTime T n)
    (dyadicTime_mono T n) (C n) (hC n) (hC2 n)
    (fun i x => x^2 - (dyadicTime T n (i+1) - dyadicTime T n i : ℝ≥0))
    (fun _ => by fun_prop) (fun _ => centeredSquare_gaussian_memLp _) i
  simp only [NNReal.coe_sub (dyadicTime_mono T n (Nat.le_succ _)),
    dyadicTime_step] at hterm
  unfold dyadicQuadraticError
  rw [integral_finsetSum _ (fun i _ => (hterm i).integrable (by norm_num))]
  apply Finset.sum_eq_zero
  intro i hi
  have hh := predictableTerm_integral hB (dyadicTime T n) (dyadicTime_mono T n)
    (C n) (hC n) (fun i => (hC2 n i).aemeasurable)
    (fun i x => x^2 - (dyadicTime T n (i+1) - dyadicTime T n i : ℝ≥0))
    (fun _ => by fun_prop) (fun _ => centeredSquare_gaussian_mean _) i
  simpa only [NNReal.coe_sub (dyadicTime_mono T n (Nat.le_succ _)),
    dyadicTime_step] using hh

lemma dyadicQuadraticError_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (K : ℝ) (hK : 0 ≤ K)
    (hCK : ∀ n i, ∀ᵐ ω ∂P, |C n i ω| ≤ K) (n : ℕ) :
    (∫ ω, dyadicQuadraticError B T C n ω ^ 2 ∂P) ≤
      2 * K^2 * (T : ℝ)^2 * (1/2 : ℝ)^n := by
  have hi := brownian_predictableQuadraticError_isometry hB (dyadicTime T n)
    (dyadicTime_mono T n) (C n) (hC n) (hC2 n) (2^n)
  simp only [dyadicTime_step] at hi
  change (∫ ω, dyadicQuadraticError B T C n ω ^ 2 ∂P) = _ at hi
  rw [hi]
  calc
    _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * (2 * ((T : ℝ) / (2 : ℝ)^n)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        (∫ ω, C n i ω ^ 2 ∂P) ≤ ∫ _ : Ω, K^2 ∂P := by
          apply integral_mono_ae (hC2 n i).integrable_sq (integrable_const _)
          filter_upwards [hCK n i] with ω hω
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hω
        _ = K^2 := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      rw [one_div_pow]
      field_simp

 

theorem brownian_dyadic_weighted_quadraticError_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (K : ℝ) (hK : 0 ≤ K)
    (hCK : ∀ n i, ∀ᵐ ω ∂P, |C n i ω| ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n => dyadicQuadraticError B T C n ω) atTop (𝓝 0) := by
  have hv (n : ℕ) : variance (dyadicQuadraticError B T C n) P ≤
      2 * K^2 * (T : ℝ)^2 * (1/2 : ℝ)^n := by
    rw [variance_eq_sub (dyadicQuadraticError_memLp hB T C hC hC2 n),
      dyadicQuadraticError_integral hB T C hC hC2 n]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
    exact dyadicQuadraticError_second_moment_le hB T C hC hC2 K hK hCK n
  have htail (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
      P {ω | ε ≤ |dyadicQuadraticError B T C n ω|} ≤
        ENNReal.ofReal ((2 * K^2 * (T : ℝ)^2 / ε^2) * (1/2 : ℝ)^n) := by
    have hh := meas_ge_le_variance_div_sq (dyadicQuadraticError_memLp hB T C hC hC2 n) hε
    rw [dyadicQuadraticError_integral hB T C hC hC2 n] at hh
    simp only [sub_zero] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (2 * K^2 * (T : ℝ)^2 * (1/2 : ℝ)^n) / ε^2 := by gcongr; exact hv n
      _ = _ := by ring
  have hevent (k : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      |dyadicQuadraticError B T C n ω| < 1 / ((k : ℝ) + 1) := by
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hs : (∑' n, P {ω | ε ≤ |dyadicQuadraticError B T C n ω|}) ≠ ∞ := by
      exact ne_top_of_le_ne_top
        ((summable_geometric_two.mul_left (2 * K^2 * (T : ℝ)^2 / ε^2)).tsum_ofReal_ne_top)
        (ENNReal.tsum_le_tsum (htail ε hε))
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hs
  filter_upwards [ae_all_iff.2 hevent] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω k)
  exact ⟨N, fun n hn => by simpa only [Real.dist_eq, sub_zero] using (hN n hn).trans hk⟩

end SLEExactGauge.BrownianPredictable

 

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.L2Limit

lemma eLpNorm_two_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) :
    eLpNorm X 2 P = (ENNReal.ofReal (∫ ω, X ω ^ 2 ∂P)) ^ (1/2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num) hX.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  have heq (ω : Ω) : ‖X ω‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (X ω ^ 2) := by
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (Eventually.of_forall fun ω => sq_nonneg _)]

lemma uniformIntegrable_one_of_eLpNorm_two_bounded {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEStronglyMeasurable (X i) P) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (X i) 2 P ≤ C) : UniformIntegrable X 1 P := by
  refine ⟨unifIntegrable_iff.mpr ?_, C, ?_⟩
  · intro bound hbound
    obtain ⟨small, hsmall, hsmall_bound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hbound
    let ε : ℝ := small
    have hε : 0 < ε := by exact_mod_cast hsmall
    let d : ℝ≥0 := ⟨ε / ((C : ℝ)+1), div_nonneg hε.le (by positivity)⟩
    have hd : 0 < (d : ℝ) := div_pos hε (by positivity)
    refine ⟨ENNReal.ofReal ((d : ℝ)^2), ENNReal.ofReal_pos.mpr (sq_pos_of_pos hd),
      fun i s hμs => ?_⟩
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hXm i).restrict
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one] at hb
    rw [Measure.restrict_apply_univ] at hb
    have hp : (P s) ^ (1/2 : ℝ) ≤ (d : ℝ≥0∞) := by
      calc
        _ ≤ (ENNReal.ofReal ((d : ℝ)^2)) ^ (1/2 : ℝ) :=
          ENNReal.rpow_le_rpow hμs (by norm_num)
        _ = _ := by
          rw [ENNReal.ofReal_pow d.coe_nonneg]
          simp only [ENNReal.ofReal_coe_nnreal]
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
    calc
      _ ≤ eLpNorm (X i) 2 (P.restrict s) * (P s) ^ (1/2 : ℝ) := hb
      _ ≤ C * (d : ℝ≥0∞) := mul_le_mul
        ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i)) hp (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
        simp only [NNReal.coe_mul]
        apply ENNReal.ofReal_le_ofReal
        change (C : ℝ) * (ε / ((C : ℝ)+1)) ≤ ε
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
      _ ≤ bound := by
        simpa only [ε, ENNReal.ofReal_coe_nnreal] using hsmall_bound.le
  · intro i
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hXm i)
    simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hb.trans (by simpa using hC i)

 

theorem integral_tendsto_of_ae_of_square_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (A : ℝ)
    (hA : ∀ n, (∫ ω, X n ω ^ 2 ∂P) ≤ A)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable Y P ∧ Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω, Y ω ∂P)) := by
  let C : ℝ≥0∞ := (ENNReal.ofReal A) ^ (1/2 : ℝ)
  have hCt : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hC (n : ℕ) : eLpNorm (X n) 2 P ≤ C.toNNReal := by
    rw [ENNReal.coe_toNNReal hCt, eLpNorm_two_eq_integral_sq (hX n)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hA n)) (by norm_num)
  have hui := uniformIntegrable_one_of_eLpNorm_two_bounded
    (fun n => (hX n).aestronglyMeasurable) C.toNNReal hC
  have hY := hui.memLp_of_ae_tendsto hXY
  have hL1 := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num) (fun n => (hX n).aestronglyMeasurable) hY hui.unifIntegrable hXY
  exact ⟨memLp_one_iff_integrable.1 hY,
    tendsto_integral_of_L1' Y
      (Eventually.of_forall fun n => (hX n).integrable (by norm_num)) hL1⟩

end SLEExactGauge.L2Limit

namespace SLEExactGauge.PredictableLimit
open BrownianPredictable L2Limit

def dyadicDriverSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (C : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), C n i ω *
    (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)

lemma dyadicDriverSum_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (n : ℕ) :
    MemLp (dyadicDriverSum B T C n) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact predictableTerm_memLp_two hB (dyadicTime T n) (dyadicTime_mono T n)
    (C n) (hC n) (hC2 n) (fun _ x => x) (fun _ => measurable_id)
    (fun _ => memLp_id_gaussianReal' 2 (by norm_num)) i

lemma dyadicDriverSum_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (n : ℕ) :
    (∫ ω, dyadicDriverSum B T C n ω ∂P) = 0 := by
  unfold dyadicDriverSum
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun i _ => predictableTerm_integral hB
      (dyadicTime T n) (dyadicTime_mono T n) (C n) (hC n)
      (fun i => (hC2 n i).aemeasurable) (fun _ x => x) (fun _ => measurable_id)
      (fun _ => by simp) i
  · intro i hi
    exact (predictableTerm_memLp_two hB (dyadicTime T n) (dyadicTime_mono T n)
      (C n) (hC n) (hC2 n) (fun _ x => x) (fun _ => measurable_id)
      (fun _ => memLp_id_gaussianReal' 2 (by norm_num)) i).integrable (by norm_num)

lemma dyadicDriverSum_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (K : ℝ) (hK : 0 ≤ K)
    (hCK : ∀ n i, ∀ᵐ ω ∂P, |C n i ω| ≤ K) (n : ℕ) :
    (∫ ω, dyadicDriverSum B T C n ω ^ 2 ∂P) ≤ K^2 * T := by
  have hi := brownian_predictableSum_isometry hB (dyadicTime T n)
    (dyadicTime_mono T n) (C n) (hC n) (hC2 n) (2^n)
  simp only [dyadicTime_step] at hi
  change (∫ ω, dyadicDriverSum B T C n ω ^ 2 ∂P) = _ at hi
  rw [hi]
  calc
    _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * ((T : ℝ) / (2 : ℝ)^n) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        (∫ ω, C n i ω ^ 2 ∂P) ≤ ∫ _ : Ω, K^2 ∂P := by
          apply integral_mono_ae (hC2 n i).integrable_sq (integrable_const _)
          filter_upwards [hCK n i] with ω hω
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hω
        _ = K^2 := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp

 

theorem limit_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (K : ℝ) (hK : 0 ≤ K)
    (hCK : ∀ n i, ∀ᵐ ω ∂P, |C n i ω| ≤ K)
    (Y : Ω → ℝ)
    (hY : ∀ᵐ ω ∂P, Tendsto (fun n => dyadicDriverSum B T C n ω) atTop (𝓝 (Y ω))) :
    Integrable Y P ∧ (∫ ω, Y ω ∂P) = 0 := by
  obtain ⟨hYi, ht⟩ := integral_tendsto_of_ae_of_square_bound
    (dyadicDriverSum_memLp hB T C hC hC2)
    (K^2*T) (dyadicDriverSum_second_moment_le hB T C hC hC2 K hK hCK) hY
  simp only [dyadicDriverSum_integral hB T C hC hC2] at ht
  exact ⟨hYi, tendsto_nhds_unique ht tendsto_const_nhds⟩

end SLEExactGauge.PredictableLimit

 

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.TaylorMeshes

 
def remainder₂ (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f y - f x - deriv f x * (y-x) - deriv (deriv f) x / 2 * (y-x)^2

lemma quadratic_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (x y K : ℝ) (_hK : 0 ≤ K)
    (h3 : ∀ z ∈ uIcc x y, |iteratedDeriv 3 f z| ≤ K) :
    |remainder₂ f x y| ≤ K * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y
    simp [remainder₂]
  have ht (k : ℕ) (hk : k ≤ 2) :
      iteratedDerivWithin k f (uIcc x y) x = iteratedDeriv k f x := by
    apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
    · exact (hf.of_le (by exact_mod_cast (le_trans hk (by decide : 2 ≤ 3)))).contDiffAt
    · exact left_mem_uIcc
  have hpoly : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + deriv (deriv f) x / 2 * (y-x)^2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, ht, iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxy hf.contDiffOn
  rw [hpoly] at heq
  have hr : remainder₂ f x y = iteratedDeriv 3 f z * (y-x)^3 / 6 := by
    dsimp [remainder₂]
    norm_num at heq
    linarith
  rw [hr, abs_div, abs_mul, abs_pow]
  norm_num
  gcongr
  exact h3 z (Ioo_subset_Icc_self hz)

 

lemma sum_remainder₂_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (x : ℕ → ℝ) (n : ℕ) (K δ : ℝ) (hK : 0 ≤ K) (_hδ : 0 ≤ δ)
    (h3 : ∀ i < n, ∀ z ∈ uIcc (x i) (x (i+1)), |iteratedDeriv 3 f z| ≤ K)
    (hstep : ∀ i < n, |x (i+1)-x i| ≤ δ) :
    |∑ i ∈ Finset.range n, remainder₂ f (x i) (x (i+1))| ≤
      K * δ / 6 * ∑ i ∈ Finset.range n, (x (i+1)-x i)^2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |remainder₂ f (x i) (x (i+1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, K * δ / 6 * (x (i+1)-x i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.1 hi
      calc
        _ ≤ K * |x (i+1)-x i|^3 / 6 := quadratic_taylor_bound hf _ _ K hK (h3 i hi')
        _ = K / 6 * |x (i+1)-x i| * (x (i+1)-x i)^2 := by
          rw [show |x (i+1)-x i|^3 = |x (i+1)-x i| * |x (i+1)-x i|^2 by ring,
            sq_abs]
          ring
        _ ≤ K / 6 * δ * (x (i+1)-x i)^2 := by gcongr; exact hstep i hi'
        _ = _ := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm

 
def mesh (T : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * (T / (2 : ℝ)^n)

lemma mesh_zero (T : ℝ) (n : ℕ) : mesh T n 0 = 0 := by simp [mesh]
lemma mesh_end (T : ℝ) (n : ℕ) : mesh T n (2^n) = T := by
  simp only [mesh, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
lemma mesh_step (T : ℝ) (n i : ℕ) : mesh T n (i+1) - mesh T n i = T / (2 : ℝ)^n := by
  simp only [mesh, Nat.cast_add, Nat.cast_one]
  ring
lemma mesh_mono (T : ℝ) (hT : 0 ≤ T) (n : ℕ) : Monotone (mesh T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
lemma mesh_mem (T : ℝ) (hT : 0 ≤ T) (n i : ℕ) (hi : i ≤ 2^n) : mesh T n i ∈ Icc 0 T := by
  constructor
  · exact (mesh_zero T n) ▸ mesh_mono T hT n (Nat.zero_le i)
  · exact (mesh_mono T hT n hi).trans_eq (mesh_end T n)

lemma mesh_step_tendsto (T : ℝ) :
    Tendsto (fun n : ℕ => T / (2 : ℝ)^n) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv, inv_pow] using
    (tendsto_const_nhds (x := T)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num))

 

lemma mesh_increments_small {b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hb : ContinuousOn b (Icc 0 T)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ i < 2^n, |b (mesh T n (i+1)) - b (mesh T n i)| < δ := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hb
  obtain ⟨ε, hε, huε⟩ := Metric.uniformContinuousOn_iff.1 hu δ hδ
  have hn := (mesh_step_tendsto T).eventually (gt_mem_nhds hε)
  filter_upwards [hn] with n hn
  intro i hi
  apply huε (mesh T n (i+1)) (mesh_mem T hT n (i+1) hi)
    (mesh T n i) (mesh_mem T hT n i (Nat.le_of_lt hi))
  rw [Real.dist_eq, mesh_step, abs_of_nonneg (div_nonneg hT (by positivity))]
  exact hn

 

lemma mesh_taylor_remainder_tendsto {f b : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {T V K : ℝ} (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T)) (hK : 0 ≤ K)
    (h3 : ∀ x : ℝ, |iteratedDeriv 3 f x| ≤ K)
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1)) - b (mesh T n i))^2) atTop (𝓝 V)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      remainder₂ f (b (mesh T n i)) (b (mesh T n (i+1)))) atTop (𝓝 0) := by
  have hV : 0 ≤ V := ge_of_tendsto hQ (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / ((K+1)*(V+1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by linarith) (by linarith))
  have hs := mesh_increments_small hT hb hδ
  have hq := hQ.eventually (gt_mem_nhds (show V < V+1 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.and hq)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hs, hq⟩
  have hr := sum_remainder₂_bound hf (fun i => b (mesh T n i)) (2^n) K δ hK hδ.le
    (fun _ _ z _ => h3 z) (fun i hi => (hs i hi).le)
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (2^n),
        (b (mesh T n (i+1)) - b (mesh T n i))^2 := hr
    _ ≤ K * δ / 6 * (V+1) := mul_le_mul_of_nonneg_left hq.le (by positivity)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (K+1)*(V+1) := mul_pos (by linarith) (by linarith)
      have hid : K * (ε / ((K+1)*(V+1))) / 6 * (V+1) = ε * (K / (6*(K+1))) := by
        field_simp
      rw [hid]
      have hk : K / (6*(K+1)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hk hε

 
lemma mesh_riemann_tendsto {h : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hh : ContinuousOn h (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      h (mesh T n i) * (T / (2 : ℝ)^n)) atTop (𝓝 (∫ t in (0 : ℝ)..T, h t)) := by
  have hint (n i : ℕ) (hi : i < 2^n) :
      IntervalIntegrable h volume (mesh T n i) (mesh T n (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (mesh_mono T hT n (Nat.le_succ i))]
    apply hh.mono
    exact Icc_subset_Icc (mesh_mem T hT n i hi.le).1
      (mesh_mem T hT n (i+1) hi).2
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hh
  apply Metric.tendsto_atTop.2
  intro ε hε
  let ζ : ℝ := ε / (T+1)
  have hζ : 0 < ζ := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
  have hn := (mesh_step_tendsto T).eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hn
  refine ⟨N, fun n hn => ?_⟩
  have hnδ := hN n hn
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hint n i hi)
  rw [mesh_zero, mesh_end] at hsum
  have heach (i : ℕ) (hi : i < 2^n) :
      |h (mesh T n i) * (T / (2 : ℝ)^n) -
        ∫ t in mesh T n i..mesh T n (i+1), h t| ≤ ζ * (T / (2 : ℝ)^n) := by
    have heq : h (mesh T n i) * (T / (2 : ℝ)^n) =
        ∫ _ : ℝ in mesh T n i..mesh T n (i+1), h (mesh T n i) := by
      rw [intervalIntegral.integral_const, mesh_step, smul_eq_mul, mul_comm]
    rw [heq, ← intervalIntegral.integral_sub intervalIntegrable_const (hint n i hi)]
    have hbound : ∀ t ∈ uIoc (mesh T n i) (mesh T n (i+1)),
        ‖h (mesh T n i) - h t‖ ≤ ζ := by
      intro t ht
      rw [uIoc_of_le (mesh_mono T hT n (Nat.le_succ i))] at ht
      have htT : t ∈ Icc 0 T := ⟨(mesh_mem T hT n i hi.le).1.trans ht.1.le,
        ht.2.trans (mesh_mem T hT n (i+1) hi).2⟩
      have hdist : dist (mesh T n i) t < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 ht.1.le)]
        have hstep := mesh_step T n i
        have ht' : t ≤ mesh T n (i+1) := ht.2
        linarith
      simpa only [Real.norm_eq_abs, Real.dist_eq] using
        (hmod _ (mesh_mem T hT n i hi.le) _ htT hdist).le
    have hbound' := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, mesh_step, abs_of_nonneg (div_nonneg hT (by positivity))] at hbound'
    exact hbound'
  rw [Real.dist_eq, ← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (2^n),
        |h (mesh T n i) * (T / (2 : ℝ)^n) -
          ∫ t in mesh T n i..mesh T n (i+1), h t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (2^n), ζ * (T / (2 : ℝ)^n) :=
      Finset.sum_le_sum (fun i hi => heach i (Finset.mem_range.1 hi))
    _ = ζ * T := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    _ < ε := by
      dsimp [ζ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
      nlinarith

end SLEExactGauge.TaylorMeshes

namespace SLEExactGauge.TimeField
open TaylorMeshes

lemma sum_family_remainder₂_bound {f : ℕ → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 3 (f i))
    (x : ℕ → ℝ) (n : ℕ) (K δ : ℝ) (hK : 0 ≤ K) (_hδ : 0 ≤ δ)
    (h3 : ∀ i < n, ∀ z ∈ uIcc (x i) (x (i+1)), |iteratedDeriv 3 (f i) z| ≤ K)
    (hstep : ∀ i < n, |x (i+1)-x i| ≤ δ) :
    |∑ i ∈ Finset.range n, remainder₂ (f i) (x i) (x (i+1))| ≤
      K * δ / 6 * ∑ i ∈ Finset.range n, (x (i+1)-x i)^2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |remainder₂ (f i) (x i) (x (i+1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, K * δ / 6 * (x (i+1)-x i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.1 hi
      calc
        _ ≤ K * |x (i+1)-x i|^3 / 6 := quadratic_taylor_bound (hf i) _ _ K hK (h3 i hi')
        _ = K / 6 * |x (i+1)-x i| * (x (i+1)-x i)^2 := by
          rw [show |x (i+1)-x i|^3 = |x (i+1)-x i| * |x (i+1)-x i|^2 by ring,
            sq_abs]
          ring
        _ ≤ K / 6 * δ * (x (i+1)-x i)^2 := by gcongr; exact hstep i hi'
        _ = _ := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm

end SLEExactGauge.TimeField
end
end
end
end
end

end OAI
