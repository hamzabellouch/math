import Mathlib
import OAI.Probability.SLE.SimpleFields

namespace OAI

/-! Exponential Martingales for chordal SLE. -/

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
open L2Limit
lemma finite_uniformIntegrable_one_of_eLpNorm_two_bounded {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEStronglyMeasurable (X i) P) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (X i) 2 P ≤ C) : UniformIntegrable X 1 P := by
  let D : ℝ≥0∞ := C * (P univ) ^ (1/2 : ℝ)
  have hDt : D ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top P univ))
  refine ⟨unifIntegrable_iff.mpr ?_, D.toNNReal, ?_⟩
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
    rw [ENNReal.coe_toNNReal hDt]
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one] at hb
    exact hb.trans (mul_le_mul (hC i) le_rfl bot_le bot_le)

theorem finite_L1_tendsto_of_square_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (A : ℝ)
    (hA : ∀ n, (∫ ω, X n ω ^ 2 ∂P) ≤ A)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable Y P ∧ Tendsto (fun n => eLpNorm (X n - Y) 1 P) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := (ENNReal.ofReal A) ^ (1/2 : ℝ)
  have hCt : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hC (n : ℕ) : eLpNorm (X n) 2 P ≤ C.toNNReal := by
    rw [ENNReal.coe_toNNReal hCt, eLpNorm_two_eq_integral_sq (hX n)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hA n)) (by norm_num)
  have hui := finite_uniformIntegrable_one_of_eLpNorm_two_bounded
    (fun n => (hX n).aestronglyMeasurable) C.toNNReal hC
  have hY := hui.memLp_of_ae_tendsto hXY
  exact ⟨memLp_one_iff_integrable.1 hY,
    tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      (by norm_num) (fun n => (hX n).aestronglyMeasurable) hY hui.unifIntegrable hXY⟩

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma product_memLp_two_of_section_square_bound
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν] [SFinite P]
    {X : Z × Ω → ℝ} (hX : Measurable X)
    (hX2 : ∀ z, MemLp (fun ω => X (z, ω)) 2 P)
    (V : ℝ) (hV : ∀ z, (∫ ω, X (z, ω)^2 ∂P) ≤ V) :
    MemLp X 2 (ν.prod P) ∧
      (∫ p, X p ^ 2 ∂(ν.prod P)) ≤ V * (ν univ).toReal := by
  have hm : StronglyMeasurable (fun z => ∫ ω, X (z, ω)^2 ∂P) :=
    (hX.pow_const 2).stronglyMeasurable.integral_prod_right'
  have hn (z : Z) : 0 ≤ ∫ ω, X (z, ω)^2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hi : Integrable (fun z => ∫ ω, X (z, ω)^2 ∂P) ν := by
    apply Integrable.of_bound hm.aestronglyMeasurable V
    exact Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hn z)]; exact hV z
  have hisq : Integrable (fun p => X p ^ 2) (ν.prod P) := by
    apply (integrable_prod_iff (hX.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun z => (hX2 z).integrable_sq, ?_⟩
    simpa only [Real.norm_eq_abs, abs_sq] using hi
  refine ⟨(memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr hisq, ?_⟩
  rw [integral_prod _ hisq]
  calc
    _ ≤ ∫ _z, V ∂ν := integral_mono hi (integrable_const _) hV
    _ = _ := by simp [mul_comm, Measure.real]

lemma area_eLpNorm_one_le_product
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [SFinite ν] [SFinite P]
    {X Y : Z × Ω → ℝ} (hX : Integrable X (ν.prod P)) (hY : Integrable Y (ν.prod P)) :
    eLpNorm (fun ω => (∫ z, X (z, ω) ∂ν) - ∫ z, Y (z, ω) ∂ν) 1 P ≤
      eLpNorm (X - Y) 1 (ν.prod P) := by
  rw [eLpNorm_one_eq_lintegral_enorm
    (f := fun ω => (∫ z, X (z, ω) ∂ν) - ∫ z, Y (z, ω) ∂ν)
    (hX.integral_prod_right.sub hY.integral_prod_right).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm (hX.sub hY).aestronglyMeasurable]
  calc
    _ ≤ ∫⁻ ω, ∫⁻ z, ‖X (z, ω) - Y (z, ω)‖ₑ ∂ν ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hX.prod_left_ae, hY.prod_left_ae] with ω hx hy
      rw [← integral_sub hx hy]
      exact enorm_integral_le_lintegral_enorm _
    _ = _ := by
      rw [← lintegral_lintegral_swap (hX.sub hY).aestronglyMeasurable.enorm]
      exact (lintegral_prod _ (hX.sub hY).aestronglyMeasurable.enorm).symm

 

theorem area_L1_tendsto_of_square_bound
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν] [IsProbabilityMeasure P]
    {X : ℕ → Z × Ω → ℝ} {Y : Z × Ω → ℝ}
    (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y)
    (hX2 : ∀ n z, MemLp (fun ω => X n (z, ω)) 2 P)
    (V : ℝ) (hV : ∀ n z, (∫ ω, X n (z, ω)^2 ∂P) ≤ V)
    (hXY : ∀ z, ∀ᵐ ω ∂P, Tendsto (fun n => X n (z, ω)) atTop (𝓝 (Y (z, ω)))) :
    Integrable Y (ν.prod P) ∧ Tendsto (fun n =>
      eLpNorm (fun ω => (∫ z, X n (z, ω) ∂ν) - ∫ z, Y (z, ω) ∂ν) 1 P) atTop (𝓝 0) := by
  have hb (n : ℕ) := product_memLp_two_of_section_square_bound (ν := ν) (P := P) (hXm n) (hX2 n) V (hV n)
  have hc : ∀ᵐ p ∂(ν.prod P), Tendsto (fun n => X n p) atTop (𝓝 (Y p)) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hXm hYm)).mpr (Eventually.of_forall hXY)
  obtain ⟨hi, ht⟩ := finite_L1_tendsto_of_square_bound (fun n => (hb n).1)
    (V * (ν univ).toReal) (fun n => (hb n).2) hc
  refine ⟨hi, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => bot_le) (fun n => area_eLpNorm_one_le_product ((hb n).1.integrable (by norm_num)) hi)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
open BrownianPredictable PredictableLimit

lemma area_driver_sum {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} [IsFiniteMeasure ν]
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (C : ℕ → Z × Ω → ℝ)
    (hC : ∀ i, Measurable (C i)) (K : ℝ) (hb : ∀ i z ω, |C i (z, ω)| ≤ K)
    (n : ℕ) (ω : Ω) :
    (∫ z, driverPredictableSum B t (fun i ω => C i (z, ω)) n ω ∂ν) =
      driverPredictableSum B t (fun i ω => ∫ z, C i (z, ω) ∂ν) n ω := by
  have hi (i : ℕ) : Integrable (fun z => C i (z, ω)) ν :=
    Integrable.of_bound ((hC i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable K
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb i z ω)
  simp only [driverPredictableSum]
  rw [integral_finsetSum _ (fun i _ => (hi i).mul_const _)]
  exact Finset.sum_congr rfl fun i hi => integral_mul_const _ _

 

theorem brownian_area_sum_L1_limit
    {Z Ω : Type*} [MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (T : ℝ≥0) (C : ℕ → ℕ → Z × Ω → ℝ)
    (hCm : ∀ n i, Measurable (C n i))
    (hCa : ∀ n i z, Measurable[Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)] (fun ω => C n i (z, ω)))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n i z ω, |C n i (z, ω)| ≤ K)
    (Y : Z × Ω → ℝ) (hYm : Measurable Y)
    (hlim : ∀ z, ∀ᵐ ω ∂P, Tendsto
      (fun n => driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z, ω)) (2^n) ω)
      atTop (𝓝 (Y (z, ω)))) :
    Integrable Y (ν.prod P) ∧ Tendsto (fun n =>
      eLpNorm (fun ω => driverPredictableSum B (dyadicTime T n)
        (fun i ω => ∫ z, C n i (z, ω) ∂ν) (2^n) ω - ∫ z, Y (z, ω) ∂ν) 1 P)
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let X (n : ℕ) (p : Z × Ω) :=
    driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (p.1, ω)) (2^n) p.2
  have hCp (n i : ℕ) (z : Z) : Measurable[pastSigma B (dyadicTime T n i)]
      (fun ω => C n i (z, ω)) := by
    exact (hCa n i z).mono
      (le_of_eq (Filtration.natural_eq_comap B (fun t => (hm t).stronglyMeasurable) _)) le_rfl
  have hC2 (n i : ℕ) (z : Z) : MemLp (fun ω => C n i (z, ω)) 2 P :=
    MemLp.of_bound ((hCm n i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb n i z ω)
  have hXm (n : ℕ) : Measurable (X n) := by
    apply Finset.measurable_sum
    intro i hi
    exact (hCm n i).mul (((hm _).comp measurable_snd).sub ((hm _).comp measurable_snd))
  have hX2 (n : ℕ) (z : Z) : MemLp (fun ω => X n (z, ω)) 2 P := by
    exact dyadicDriverSum_memLp hB T (fun n i ω => C n i (z, ω))
      (fun n i => hCp n i z) (fun n i => hC2 n i z) n
  have hV (n : ℕ) (z : Z) : (∫ ω, X n (z, ω)^2 ∂P) ≤ K^2 * (T : ℝ) := by
    change (∫ ω, (∑ i ∈ Finset.range (2^n), C n i (z, ω) *
      (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) ^ 2 ∂P) ≤ _
    rw [brownian_predictableSum_isometry hB _ (dyadicTime_mono T n) _
      (fun i => hCp n i z) (fun i => hC2 n i z)]
    calc
      _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * ((T : ℝ) / (2 : ℝ)^n) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [dyadicTime_step]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          _ ≤ ∫ _ω, K^2 ∂P := integral_mono (hC2 n i z).integrable_sq (integrable_const _) fun ω =>
            by
              have hh := (sq_le_sq₀ (abs_nonneg (C n i (z, ω))) hK).mpr (hb n i z ω)
              simpa only [sq_abs] using hh
          _ = K^2 := by simp
      _ = K^2 * (T : ℝ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
  obtain ⟨hi, ht⟩ := area_L1_tendsto_of_square_bound (ν := ν) hXm hYm hX2 _ hV hlim
  refine ⟨hi, ?_⟩
  have he (n : ℕ) (ω : Ω) : (∫ z, X n (z, ω) ∂ν) =
      driverPredictableSum B (dyadicTime T n) (fun i ω => ∫ z, C n i (z, ω) ∂ν) (2^n) ω :=
    area_driver_sum B _ _ (hCm n) K (hb n) _ ω
  simpa only [he] using ht

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
open BrownianPredictable PredictableLimit

 

theorem brownian_area_exponential_limit
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (T : ℝ≥0) (C : ℕ → ℕ → Z × Ω → ℝ)
    (hCm : ∀ n i, Measurable (C n i))
    (hCa : ∀ n i, @Measurable (Z × Ω) ℝ
      (mZ.prod (Filtration.natural B (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)))
      (borel ℝ) (C n i))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n i z ω, |C n i (z, ω)| ≤ K)
    (Y : Z × Ω → ℝ) (hYm : Measurable Y)
    (hlim : ∀ z, ∀ᵐ ω ∂P, Tendsto
      (fun n => driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z, ω)) (2^n) ω)
      atTop (𝓝 (Y (z, ω))))
    (Q : Ω → ℝ)
    (hE : ∀ᵐ ω ∂P, Tendsto (fun n => driverPredictableEnergy (dyadicTime T n)
      (fun i ω => ∫ z, C n i (z, ω) ∂ν) (2^n) ω) atTop (𝓝 (Q ω)))
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, Y (z, ω) ∂ν) - θ^2 * Q ω / 2)) ∂P) ≤ 1 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let D (n i : ℕ) (ω : Ω) := ∫ z, C n i (z, ω) ∂ν
  have hDa (n i : ℕ) : Measurable[Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)] (D n i) := by
    let : MeasurableSpace Ω := Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)
    exact (hCa n i).stronglyMeasurable.integral_prod_left'.measurable
  let X (n : ℕ) := driverPredictableSum B (dyadicTime T n) (D n) (2^n)
  let E (n : ℕ) := driverPredictableEnergy (dyadicTime T n) (D n) (2^n)
  have hXm (n : ℕ) : Measurable (X n) :=
    (driverPredictableSum_measurable_past B hm _ (dyadicTime_mono T n) _ (hDa n) _).mono
      (Filtration.le _ _) le_rfl
  have hEm (n : ℕ) : Measurable (E n) :=
    (driverPredictableEnergy_measurable_past B hm _ (dyadicTime_mono T n) _ (hDa n) _).mono
      (Filtration.le _ _) le_rfl
  have hca (n i : ℕ) (z : Z) : Measurable[Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)] (fun ω => C n i (z, ω)) :=
    (hCa n i).comp (measurable_const.prodMk measurable_id)
  obtain ⟨hi, ht⟩ := brownian_area_sum_L1_limit (ν := ν) (P := P) hB hm T C hCm hca K hK hb Y hYm hlim
  have hY : Measurable (fun ω => ∫ z, Y (z, ω) ∂ν) :=
    hYm.stronglyMeasurable.integral_prod_left'.measurable
  have hc : TendstoInMeasure P X atTop (fun ω => ∫ z, Y (z, ω) ∂ν) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) ht
  obtain ⟨ns, hns, hs⟩ := hc.exists_seq_tendsto_ae
  apply compensated_exponential_limit_energy (fun n => X (ns n)) (fun n => E (ns n))
    (fun ω => ∫ z, Y (z, ω) ∂ν) Q θ
    (fun n => (((hXm _).const_mul θ).sub (((hEm _).const_mul (θ^2)).div_const 2)).exp.ennreal_ofReal.aemeasurable)
    hs
  · filter_upwards [hE] with ω he
    exact he.comp hns.tendsto_atTop
  · intro n
    exact (driverPredictable_exponential hB hm _ (dyadicTime_mono T (ns n)) _ (hDa _) θ _).le

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

noncomputable def areaPrefixSample {Z : Type*} (f : ℝ × Z → ℝ) (τ : Z → ℝ≥0)
    (T : ℝ≥0) (n i : ℕ) (z : Z) : ℝ :=
  if dyadicTime T n i < τ z then f (dyadicTime T n i, z) else 0

lemma areaPrefixSample_measurable {Z : Type*} [MeasurableSpace Z]
    {f : ℝ × Z → ℝ} (hf : Measurable f) {τ : Z → ℝ≥0} (hτ : Measurable τ)
    (T : ℝ≥0) (n i : ℕ) : Measurable (areaPrefixSample f τ T n i) :=
  (hf.comp (measurable_const.prodMk measurable_id)).ite
    (measurableSet_lt measurable_const hτ) measurable_const

lemma areaPrefixSample_bound {Z : Type*} {f : ℝ × Z → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K)
    (τ : Z → ℝ≥0) (T : ℝ≥0) (n i : ℕ) (z : Z) :
    |areaPrefixSample f τ T n i z| ≤ K := by
  unfold areaPrefixSample
  split_ifs
  · exact hb _ _
  · simpa using hK

lemma prefix_pair_energy_tendsto {Z : Type*} (f : ℝ × Z → ℝ)
    (hf : ∀ z, Continuous (fun t => f (t,z)))
    (τ : Z → ℝ≥0) (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T) (z w : Z) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (areaPrefixSample f τ T n i z * areaPrefixSample f τ T n i w) *
        ((T : ℝ) / (2 : ℝ)^n)) atTop
      (𝓝 (∫ t in (0 : ℝ)..(min (τ z) (τ w) : ℝ≥0), f (t,z) * f (t,w))) := by
  have hh := stopped_energy_tendsto ((min_le_left (τ z) (τ w)).trans (hτ z))
    ((hf z).mul (hf w)).continuousOn
  simp only [Pi.mul_apply] at hh
  convert hh using 1
  ext n
  apply Finset.sum_congr rfl
  intro i hi
  rw [dyadicTime_step]
  simp only [areaPrefixSample, lt_min_iff]
  split_ifs <;> simp_all

lemma prefix_pair_energy_bound {Z : Type*} {f : ℝ × Z → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K)
    (τ : Z → ℝ≥0) (T : ℝ≥0) (n : ℕ) (z w : Z) :
    |∑ i ∈ Finset.range (2^n),
      (areaPrefixSample f τ T n i z * areaPrefixSample f τ T n i w) *
        ((T : ℝ) / (2 : ℝ)^n)| ≤ K^2 * (T : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (2^n),
        |(areaPrefixSample f τ T n i z * areaPrefixSample f τ T n i w) *
          ((T : ℝ) / (2 : ℝ)^n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * ((T : ℝ) / (2 : ℝ)^n) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ) / (2 : ℝ)^n), abs_mul, pow_two]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (areaPrefixSample_bound hK hb τ T n i z)
          (areaPrefixSample_bound hK hb τ T n i w) (abs_nonneg _) hK) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

 

theorem area_prefix_energy_tendsto {Z : Type*} [MeasurableSpace Z]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {f : ℝ × Z → ℝ} (hfm : Measurable f) (hfc : ∀ z, Continuous (fun t => f (t,z)))
    {τ : Z → ℝ≥0} (hτm : Measurable τ) (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (∫ z, areaPrefixSample f τ T n i z ∂ν)^2 * ((T : ℝ) / (2 : ℝ)^n)) atTop
      (𝓝 (∫ p : Z × Z, (∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
        f (t,p.1) * f (t,p.2)) ∂(ν.prod ν))) := by
  let H (n : ℕ) (p : Z × Z) := ∑ i ∈ Finset.range (2^n),
    (areaPrefixSample f τ T n i p.1 * areaPrefixSample f τ T n i p.2) *
      ((T : ℝ) / (2 : ℝ)^n)
  have hC (n i : ℕ) := areaPrefixSample_measurable hfm hτm T n i
  have hH (n : ℕ) : Measurable (H n) := by
    apply Finset.measurable_sum
    intro i hi
    exact (((hC n i).comp measurable_fst).mul ((hC n i).comp measurable_snd)).mul_const _
  have hbH (n : ℕ) (p : Z × Z) : ‖H n p‖ ≤ K^2 * (T : ℝ) := by
    rw [Real.norm_eq_abs]
    exact prefix_pair_energy_bound hK hb τ T n p.1 p.2
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ν.prod ν) (fun _ => K^2 * (T : ℝ))
    (fun n => (hH n).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall (hbH n))
    (Eventually.of_forall fun p : Z × Z => prefix_pair_energy_tendsto f hfc τ T hτ p.1 p.2)
  have he (n : ℕ) : (∫ p, H n p ∂(ν.prod ν)) =
      ∑ i ∈ Finset.range (2^n), (∫ z, areaPrefixSample f τ T n i z ∂ν)^2 *
        ((T : ℝ) / (2 : ℝ)^n) := by
    have hi (i : ℕ) : Integrable (areaPrefixSample f τ T n i) ν :=
      Integrable.of_bound (hC n i).aestronglyMeasurable K
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact areaPrefixSample_bound hK hb τ T n i z)
    rw [show H n = (fun p : Z × Z => ∑ i ∈ Finset.range (2^n),
      (areaPrefixSample f τ T n i p.1 * areaPrefixSample f τ T n i p.2) *
        ((T : ℝ) / (2 : ℝ)^n)) from rfl]
    rw [integral_finsetSum _ (fun i _ => ((hi i).mul_prod (hi i)).mul_const _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const, integral_prod_mul, pow_two]
  simpa only [he] using ht

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma interval_integral_prefix_lt {S T : ℝ≥0} (hST : S ≤ T) (f : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..(T : ℝ), if t < (S : ℝ) then f t else 0) =
      ∫ t in (0 : ℝ)..(S : ℝ), f t := by
  calc
    _ = ∫ t in (0 : ℝ)..(T : ℝ), indicator {t : ℝ | t ≤ S} f t := by
      apply intervalIntegral.integral_congr_ae
      have hn : ∀ᵐ t : ℝ, t ≠ (S : ℝ) := by simp [ae_iff]
      filter_upwards [hn] with t ht
      intro _
      simp only [Set.indicator, Set.mem_ofPred_eq, le_iff_lt_or_eq, ht, or_false]
    _ = _ := intervalIntegral.integral_indicator ⟨S.coe_nonneg, by exact_mod_cast hST⟩

 

theorem area_prefix_energy_identity {Z : Type*} [MeasurableSpace Z]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {f : ℝ × Z → ℝ} (hfm : Measurable f)
    {τ : Z → ℝ≥0} (hτm : Measurable τ) (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K) :
    (∫ p : Z × Z, (∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
        f (t,p.1) * f (t,p.2)) ∂(ν.prod ν)) =
      ∫ t in (0 : ℝ)..(T : ℝ), (∫ z, if t < (τ z : ℝ) then f (t,z) else 0 ∂ν)^2 := by
  let g (p : ℝ × (Z × Z)) := if p.1 < (min (τ p.2.1) (τ p.2.2) : ℝ≥0) then
    f (p.1,p.2.1) * f (p.1,p.2.2) else 0
  have htm : Measurable (fun p : ℝ × (Z × Z) => (min (τ p.2.1) (τ p.2.2) : ℝ)) :=
    NNReal.continuous_coe.measurable.comp (((hτm.comp (measurable_fst.comp measurable_snd))).min
      (hτm.comp (measurable_snd.comp measurable_snd)))
  have hgm : Measurable g :=
    ((hfm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hfm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).ite
        (measurableSet_lt measurable_fst htm) measurable_const
  have hgb (p : ℝ × (Z × Z)) : ‖g p‖ ≤ K^2 := by
    rw [Real.norm_eq_abs]
    dsimp only [g]
    split_ifs
    · rw [abs_mul, pow_two]
      exact mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) hK
    · simpa using sq_nonneg K
  have hgi : Integrable g ((volume.restrict (Ioc 0 (T : ℝ))).prod (ν.prod ν)) :=
    Integrable.of_bound hgm.aestronglyMeasurable (K^2) (Eventually.of_forall hgb)
  have hp (p : Z × Z) : (∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
      f (t,p.1) * f (t,p.2)) = ∫ t in Ioc (0 : ℝ) T, g (t,p) := by
    rw [← intervalIntegral.integral_of_le T.coe_nonneg]
    exact (interval_integral_prefix_lt ((min_le_left _ _).trans (hτ p.1)) _).symm
  have hg (t : ℝ) : (∫ p : Z × Z, g (t,p) ∂(ν.prod ν)) =
      (∫ z, if t < (τ z : ℝ) then f (t,z) else 0 ∂ν)^2 := by
    calc
      _ = ∫ p : Z × Z, (if t < (τ p.1 : ℝ) then f (t,p.1) else 0) *
          (if t < (τ p.2 : ℝ) then f (t,p.2) else 0) ∂(ν.prod ν) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro p
        simp only [g, NNReal.coe_min, lt_min_iff]
        split_ifs <;> simp_all
      _ = _ := by
        simpa only [pow_two] using (integral_prod_mul (μ := ν) (ν := ν)
          (fun z => if t < (τ z : ℝ) then f (t,z) else 0)
          (fun z => if t < (τ z : ℝ) then f (t,z) else 0))
  simp_rw [hp]
  rw [← integral_integral_swap hgi]
  simp only [hg, intervalIntegral.integral_of_le T.coe_nonneg]

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable

noncomputable def areaWindowSample {Z : Type*} (f : ℝ × Z → ℝ)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n i : ℕ) (z : Z) : ℝ :=
  if σ z ≤ dyadicTime T n i ∧ dyadicTime T n i < τ z then f (dyadicTime T n i,z) else 0

lemma areaWindowSample_measurable {Z : Type*} [MeasurableSpace Z]
    {f : ℝ × Z → ℝ} (hf : Measurable f) {σ τ : Z → ℝ≥0}
    (hσ : Measurable σ) (hτ : Measurable τ) (T : ℝ≥0) (n i : ℕ) :
    Measurable (areaWindowSample f σ τ T n i) :=
  (hf.comp (measurable_const.prodMk measurable_id)).ite
    ((measurableSet_le hσ measurable_const).inter (measurableSet_lt measurable_const (NNReal.continuous_coe.measurable.comp hτ))) measurable_const

lemma areaWindowSample_bound {Z : Type*} {f : ℝ × Z → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n i : ℕ) (z : Z) :
    |areaWindowSample f σ τ T n i z| ≤ K := by
  unfold areaWindowSample
  split_ifs
  · exact hb _ _
  · simpa using hK

lemma window_pair_eq_prefix_difference {Z : Type*} (f : ℝ × Z → ℝ)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n i : ℕ) (z w : Z) :
    areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w =
      (if dyadicTime T n i < min (τ z) (τ w) then
        f (dyadicTime T n i,z) * f (dyadicTime T n i,w) else 0) -
      (if dyadicTime T n i < min (min (τ z) (τ w)) (max (σ z) (σ w)) then
        f (dyadicTime T n i,z) * f (dyadicTime T n i,w) else 0) := by
  simp only [areaWindowSample, lt_min_iff, lt_max_iff]
  by_cases hz : σ z ≤ dyadicTime T n i
  · by_cases hw : σ w ≤ dyadicTime T n i
    · simp [hz, hw, not_lt.mpr hz, not_lt.mpr hw]
      split_ifs <;> simp_all
    · simp only [hw, false_and, ite_false, mul_zero]
      have ht := lt_of_not_ge hw
      simp [ht, sub_self]
  · simp only [hz, false_and, ite_false, zero_mul]
    have ht := lt_of_not_ge hz
    simp [ht, sub_self]

lemma window_pair_energy_tendsto {Z : Type*} (f : ℝ × Z → ℝ)
    (hf : ∀ z, Continuous (fun t => f (t,z)))
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T) (z w : Z) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w) *
        ((T : ℝ) / (2 : ℝ)^n)) atTop
      (𝓝 ((∫ t in (0 : ℝ)..(min (τ z) (τ w) : ℝ≥0), f (t,z) * f (t,w)) -
        ∫ t in (0 : ℝ)..(min (min (τ z) (τ w)) (max (σ z) (σ w)) : ℝ≥0), f (t,z) * f (t,w))) := by
  have hH := stopped_energy_tendsto ((min_le_left (τ z) (τ w)).trans (hτ z))
    ((hf z).mul (hf w)).continuousOn
  have hL := stopped_energy_tendsto
    ((min_le_left (min (τ z) (τ w)) (max (σ z) (σ w))).trans ((min_le_left (τ z) (τ w)).trans (hτ z)))
    ((hf z).mul (hf w)).continuousOn
  simp only [Pi.mul_apply] at hH hL
  convert hH.sub hL using 1
  ext n
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [window_pair_eq_prefix_difference, dyadicTime_step, sub_mul]

lemma window_pair_energy_bound {Z : Type*} {f : ℝ × Z → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n : ℕ) (z w : Z) :
    |∑ i ∈ Finset.range (2^n),
      (areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w) *
        ((T : ℝ) / (2 : ℝ)^n)| ≤ K^2 * (T : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (2^n),
        |(areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w) *
          ((T : ℝ) / (2 : ℝ)^n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * ((T : ℝ) / (2 : ℝ)^n) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ) / (2 : ℝ)^n), abs_mul, pow_two]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (areaWindowSample_bound hK hb σ τ T n i z)
          (areaWindowSample_bound hK hb σ τ T n i w) (abs_nonneg _) hK) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

lemma area_window_pair_energy_tendsto {Z : Type*} [MeasurableSpace Z]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {f : ℝ × Z → ℝ} (hfm : Measurable f) (hfc : ∀ z, Continuous (fun t => f (t,z)))
    {σ τ : Z → ℝ≥0} (hσm : Measurable σ) (hτm : Measurable τ) (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (∫ z, areaWindowSample f σ τ T n i z ∂ν)^2 * ((T : ℝ) / (2 : ℝ)^n)) atTop
      (𝓝 (∫ p : Z × Z, ((∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
        f (t,p.1) * f (t,p.2)) - ∫ t in (0 : ℝ)..
          (min (min (τ p.1) (τ p.2)) (max (σ p.1) (σ p.2)) : ℝ≥0), f (t,p.1) * f (t,p.2)) ∂(ν.prod ν))) := by
  let H (n : ℕ) (p : Z × Z) := ∑ i ∈ Finset.range (2^n),
    (areaWindowSample f σ τ T n i p.1 * areaWindowSample f σ τ T n i p.2) *
      ((T : ℝ) / (2 : ℝ)^n)
  have hC (n i : ℕ) := areaWindowSample_measurable hfm hσm hτm T n i
  have hH (n : ℕ) : Measurable (H n) := by
    apply Finset.measurable_sum
    intro i hi
    exact (((hC n i).comp measurable_fst).mul ((hC n i).comp measurable_snd)).mul_const _
  have hbH (n : ℕ) (p : Z × Z) : ‖H n p‖ ≤ K^2 * (T : ℝ) := by
    rw [Real.norm_eq_abs]
    exact window_pair_energy_bound hK hb σ τ T n p.1 p.2
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ν.prod ν) (fun _ => K^2 * (T : ℝ))
    (fun n => (hH n).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall (hbH n))
    (Eventually.of_forall fun p : Z × Z => window_pair_energy_tendsto f hfc σ τ T hτ p.1 p.2)
  have he (n : ℕ) : (∫ p, H n p ∂(ν.prod ν)) =
      ∑ i ∈ Finset.range (2^n), (∫ z, areaWindowSample f σ τ T n i z ∂ν)^2 *
        ((T : ℝ) / (2 : ℝ)^n) := by
    have hi (i : ℕ) : Integrable (areaWindowSample f σ τ T n i) ν :=
      Integrable.of_bound (hC n i).aestronglyMeasurable K
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact areaWindowSample_bound hK hb σ τ T n i z)
    change (∫ p : Z × Z, ∑ i ∈ Finset.range (2^n),
      (areaWindowSample f σ τ T n i p.1 * areaWindowSample f σ τ T n i p.2) *
        ((T : ℝ) / (2 : ℝ)^n) ∂(ν.prod ν)) = _
    rw [integral_finsetSum _ (fun i _ => ((hi i).mul_prod (hi i)).mul_const _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const, integral_prod_mul, pow_two]
  simpa only [he] using ht

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma real_window_pair_eq (f : ℝ → ℝ) (a b c d t : ℝ) :
    (if a ≤ t ∧ t < b ∧ c ≤ t ∧ t < d then f t else 0) =
      (if t < min b d then f t else 0) -
      (if t < min (min b d) (max a c) then f t else 0) := by
  simp only [lt_min_iff, lt_max_iff]
  by_cases ha : a ≤ t
  · by_cases hc : c ≤ t
    · simp [ha, hc, not_lt.mpr ha, not_lt.mpr hc]
    · simp only [hc, false_and, and_false, ite_false]
      have ht := lt_of_not_ge hc
      simp [ht]
  · simp only [ha, false_and, ite_false]
    have ht := lt_of_not_ge ha
    simp [ht]

 

theorem area_window_energy_identity {Z : Type*} [MeasurableSpace Z]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {f : ℝ × Z → ℝ} (hfm : Measurable f)
    {σ τ : Z → ℝ≥0} (hσm : Measurable σ) (hτm : Measurable τ)
    (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K) :
    (∫ p : Z × Z, ((∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
        f (t,p.1) * f (t,p.2)) - ∫ t in (0 : ℝ)..
          (min (min (τ p.1) (τ p.2)) (max (σ p.1) (σ p.2)) : ℝ≥0), f (t,p.1) * f (t,p.2)) ∂(ν.prod ν)) =
      ∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0 ∂ν)^2 := by
  let g (p : ℝ × (Z × Z)) := if (σ p.2.1 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2.1 : ℝ) ∧
      (σ p.2.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2.2 : ℝ) then f (p.1,p.2.1) * f (p.1,p.2.2) else 0
  have htm (v : Z → ℝ≥0) (hv : Measurable v) : Measurable (fun z => (v z : ℝ)) :=
    NNReal.continuous_coe.measurable.comp hv
  have hgm : Measurable g :=
    ((hfm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hfm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).ite
        ((measurableSet_le ((htm σ hσm).comp (measurable_fst.comp measurable_snd)) measurable_fst).inter
          ((measurableSet_lt measurable_fst ((htm τ hτm).comp (measurable_fst.comp measurable_snd))).inter
            ((measurableSet_le ((htm σ hσm).comp (measurable_snd.comp measurable_snd)) measurable_fst).inter
              (measurableSet_lt measurable_fst ((htm τ hτm).comp (measurable_snd.comp measurable_snd)))))) measurable_const
  have hgb (p : ℝ × (Z × Z)) : ‖g p‖ ≤ K^2 := by
    rw [Real.norm_eq_abs]
    dsimp only [g]
    split_ifs
    · rw [abs_mul, pow_two]
      exact mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) hK
    · simpa using sq_nonneg K
  have hgi : Integrable g ((volume.restrict (Ioc 0 (T : ℝ))).prod (ν.prod ν)) :=
    Integrable.of_bound hgm.aestronglyMeasurable (K^2) (Eventually.of_forall hgb)
  have hp (p : Z × Z) : ((∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
      f (t,p.1) * f (t,p.2)) - ∫ t in (0 : ℝ)..
        (min (min (τ p.1) (τ p.2)) (max (σ p.1) (σ p.2)) : ℝ≥0), f (t,p.1) * f (t,p.2)) =
        ∫ t in Ioc (0 : ℝ) T, g (t,p) := by
    let H := min (τ p.1) (τ p.2)
    let L := min H (max (σ p.1) (σ p.2))
    have hHT : H ≤ T := (min_le_left _ _).trans (hτ p.1)
    have hLT : L ≤ T := (min_le_left _ _).trans hHT
    have hi (S : ℝ≥0) : IntervalIntegrable
        (fun t : ℝ => if t < (S : ℝ) then f (t,p.1) * f (t,p.2) else 0) volume 0 T := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le T.coe_nonneg).mpr
      apply Integrable.of_bound (μ := volume.restrict (Icc (0 : ℝ) T)) ?_ (K^2) ?_
      · exact (((hfm.comp (measurable_id.prodMk measurable_const)).mul
          (hfm.comp (measurable_id.prodMk measurable_const))).ite
            (measurableSet_lt measurable_id measurable_const) measurable_const).aestronglyMeasurable
      · apply Eventually.of_forall
        intro t
        rw [Real.norm_eq_abs]
        split_ifs
        · rw [abs_mul, pow_two]
          exact mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) hK
        · simpa using sq_nonneg K
    rw [← interval_integral_prefix_lt hHT, ← interval_integral_prefix_lt hLT,
      ← intervalIntegral.integral_sub (hi H) (hi L), ← intervalIntegral.integral_of_le T.coe_nonneg]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [g, H, L]
    simpa only [NNReal.coe_min, NNReal.coe_max] using
      (real_window_pair_eq (fun t => f (t,p.1) * f (t,p.2)) (σ p.1) (τ p.1) (σ p.2) (τ p.2) t).symm
  have hg (t : ℝ) : (∫ p : Z × Z, g (t,p) ∂(ν.prod ν)) =
      (∫ z, if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0 ∂ν)^2 := by
    calc
      _ = ∫ p : Z × Z,
          (if (σ p.1 : ℝ) ≤ t ∧ t < (τ p.1 : ℝ) then f (t,p.1) else 0) *
          (if (σ p.2 : ℝ) ≤ t ∧ t < (τ p.2 : ℝ) then f (t,p.2) else 0) ∂(ν.prod ν) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro p
        dsimp only [g]
        split_ifs <;> simp_all
      _ = _ := by
        simpa only [pow_two] using (integral_prod_mul (μ := ν) (ν := ν)
          (fun z => if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0)
          (fun z => if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0))
  simp_rw [hp]
  rw [← integral_integral_swap hgi]
  simp only [hg, intervalIntegral.integral_of_le T.coe_nonneg]

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField

 

end SLEExactGauge
end
end
end
end
end

end OAI
