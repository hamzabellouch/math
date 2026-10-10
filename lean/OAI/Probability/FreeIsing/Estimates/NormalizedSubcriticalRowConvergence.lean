import OAI.Probability.FreeIsing.Estimates.NormalizedPositiveWindowRow

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedInfiniteTimeEnergy

open PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
  (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
  (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
  (hmB : ∀ i t, Measurable (B i t))
  (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))

include hb in
omit [MeasurableSpace Ω] in
lemma finiteRow_abs_le_distance (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) (w : TreeVertex d)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
    |finiteRow beta D v B w q| ≤ Real.tanh beta ^ reducedWordDistance v.1 w.1 := by
  classical
  by_cases hw : w ∈ D
  · simp only [finiteRow, observedRow, ite_eq_left hw]
    have h := TreePathResponse.response_mem_Icc hb
      (PlantedSymmetry.observation q.1
        (q.2.1, fun i => B i q.1.toNNReal (q.2.2 i))) hD
      (⟨v, hv⟩ : D) (⟨w, hw⟩ : D)
    rw [abs_of_nonneg h.1]
    exact h.2
  · simp only [finiteRow, observedRow, ite_eq_right hw, abs_zero]
    exact pow_nonneg (tanh_nonneg_of_beta_nonneg hb) _

include hμ hb hB hjoint in

theorem integral_finiteRow_sq_timeMeasure_le_bare
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) (w : TreeVertex d)
    (τ : Measure ℝ) [IsFiniteMeasure τ] :
    (∫ q, finiteRow beta D v B w q ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) ≤
      τ.real univ * (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hle : (∫ q, finiteRow beta D v B w q ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) ≤
      ∫ _q, (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1
        ∂τ.prod (μ.prod (Measure.infinitePi ν)) := by
    apply integral_mono (integrable_finiteRow_sq hμ hb ν hB hjoint D hD v hv w τ)
      (integrable_const _)
    intro q
    have h := finiteRow_abs_le_distance (B := B) hb D hD v hv w q
    have hpow : (Real.tanh beta ^ reducedWordDistance v.1 w.1) ^ 2 =
        (Real.tanh beta ^ 2) ^ reducedWordDistance v.1 w.1 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [← hpow]
    nlinarith [sq_abs (finiteRow beta D v B w q), abs_nonneg (finiteRow beta D v B w q)]
  simpa only [integral_const, smul_eq_mul, Measure.real, ← univ_prod_univ,
    Measure.prod_prod, measure_univ, mul_one] using hle

include hμ hb hB hmB hjoint

theorem finiteRow_strict_timeMeasure_error_bound
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (τ : Measure ℝ) [IsFiniteMeasure τ]
    (hτ : ∀ᵐ t ∂τ, 0 ≤ t) (w : TreeVertex d) (n : ℕ) :
    Integrable (fun q => (finiteRow beta (D n) v B w q -
      infiniteRow beta v B w q) ^ 2) (τ.prod (μ.prod (Measure.infinitePi ν))) ∧
    (∫ q, (finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) ≤
      (4 * τ.real univ) * (Real.tanh beta ^ 2) ^
        reducedWordDistance v.1 w.1 := by
  let P := τ.prod (μ.prod (Measure.infinitePi ν))
  let X := fun k => finiteRow beta (D k) v B w
  let Y := infiniteRow beta v B w
  let K := τ.real univ * (Real.tanh beta ^ 2) ^
    reducedWordDistance v.1 w.1
  have hXm (k : ℕ) : AEStronglyMeasurable (X k) P :=
    (measurable_finiteRow beta (D k) v hjoint w).aestronglyMeasurable
  have hYm : AEStronglyMeasurable Y P :=
    (measurable_infiniteRow beta v hjoint w).aestronglyMeasurable
  have hXi (k : ℕ) : Integrable (fun q => X k q ^ 2) P :=
    integrable_finiteRow_sq hμ hb ν hB hjoint (D k) (hconn k) v (hv k) w τ
  have hXb (k : ℕ) : (∫ q, X k q ^ 2 ∂P) ≤ K :=
    integral_finiteRow_sq_timeMeasure_le_bare hμ hb ν hB hjoint
      (D k) (hconn k) v (hv k) w τ
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity)
      (pow_nonneg (sq_nonneg _) _)
  have hY : Integrable (fun q => Y q ^ 2) P ∧ (∫ q, Y q ^ 2 ∂P) ≤ K :=
    integrable_sq_and_integral_le_of_tendsto_ae P hXm hYm hK
      (finiteRow_tendsto_ae_timeMeasure hμ hb ν hB hmB hjoint D hD hconn hex v hv w τ
        hτ)
      (Eventually.of_forall fun k => ⟨hXi k, hXb k⟩)
  have hEi : Integrable (fun q => (X n q - Y q) ^ 2) P :=
    (((memLp_two_iff_integrable_sq (hXm n)).mpr (hXi n)).sub
      ((memLp_two_iff_integrable_sq hYm).mpr hY.1)).integrable_sq
  refine ⟨hEi, ?_⟩
  have hle : (∫ q, (X n q - Y q) ^ 2 ∂P) ≤
      ∫ q, 2 * X n q ^ 2 + 2 * Y q ^ 2 ∂P := by
    apply integral_mono hEi (((hXi n).const_mul 2).add (hY.1.const_mul 2))
    intro q
    change (X n q - Y q) ^ 2 ≤ 2 * X n q ^ 2 + 2 * Y q ^ 2
    nlinarith [sq_nonneg (X n q + Y q)]
  rw [integral_add ((hXi n).const_mul 2) (hY.1.const_mul 2),
    integral_const_mul, integral_const_mul] at hle
  change (∫ q, (X n q - Y q) ^ 2 ∂P) ≤ _
  have : (∫ q, (X n q - Y q) ^ 2 ∂P) ≤ 4 * K := by
    linarith [hXb n, hY.2]
  simpa only [K, mul_assoc] using this

theorem finiteRow_strict_timeMeasure_row_meanSquare
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (τ : Measure ℝ) [IsFiniteMeasure τ]
    (hτ : ∀ᵐ t ∂τ, 0 ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) :
    (∀ n, Summable (fun w => ∫ q,
      (finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν)))) ∧
    Tendsto (fun n => ∑' w, ∫ q,
      (finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  have hs := (summable_geometric_intrinsic v
    (sq_nonneg _) hcrit).mul_left (4 * τ.real univ)
  have hbound := fun n w => (finiteRow_strict_timeMeasure_error_bound hμ hb ν hB hmB hjoint
    D hD hconn hex v hv τ hτ w n).2
  refine ⟨fun n => Summable.of_nonneg_of_le
    (fun w => integral_nonneg (fun q => sq_nonneg _)) (hbound n) hs, ?_⟩
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (fun w => finiteRow_timeMeasure_meanSquare hμ hb ν hB hmB hjoint
      D hD hconn hex v hv w τ hτ)
    (Eventually.of_forall fun n w => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun q => sq_nonneg _))]
      exact hbound n w)
  simpa only [tsum_zero] using hlim

theorem finiteRow_strict_timeMeasure_row_lintegral_tendsto
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (τ : Measure ℝ) [IsFiniteMeasure τ]
    (hτ : ∀ᵐ t ∂τ, 0 ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) :
    Tendsto (fun n => ∫⁻ q, ∑' w, ENNReal.ofReal
      ((finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2)
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  have hrow := finiteRow_strict_timeMeasure_row_meanSquare hμ hb ν hB hmB hjoint
    D hD hconn hex v hv τ hτ hcrit
  have heq (n : ℕ) : (∫⁻ q, ∑' w, ENNReal.ofReal
      ((finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2)
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) =
      ENNReal.ofReal (∑' w, ∫ q,
        (finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi ν))) := by
    have hm (w : TreeVertex d) : AEMeasurable
        (fun q => ENNReal.ofReal ((finiteRow beta (D n) v B w q -
          infiniteRow beta v B w q) ^ 2))
        (τ.prod (μ.prod (Measure.infinitePi ν))) :=
      (((measurable_finiteRow beta (D n) v hjoint w).sub
        (measurable_infiniteRow beta v hjoint w)).pow_const 2).ennreal_ofReal.aemeasurable
    rw [lintegral_tsum hm]
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun w => integral_nonneg (fun q => sq_nonneg _)) (hrow.1 n)]
    apply tsum_congr
    intro w
    exact (ofReal_integral_eq_lintegral_ofReal
      (finiteRow_strict_timeMeasure_error_bound hμ hb ν hB hmB hjoint
        D hD hconn hex v hv τ hτ w n).1
      (Eventually.of_forall fun q => sq_nonneg _)).symm
  simp_rw [heq]
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hrow.2

theorem finiteRow_strict_timeMeasure_row_integral_tendsto
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (τ : Measure ℝ) [IsFiniteMeasure τ]
    (hτ : ∀ᵐ t ∂τ, 0 ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) :
    (∀ n, (∀ᵐ q ∂τ.prod (μ.prod (Measure.infinitePi ν)),
      Summable (fun w => (finiteRow beta (D n) v B w q -
        infiniteRow beta v B w q) ^ 2)) ∧
      Integrable (fun q => ∑' w, (finiteRow beta (D n) v B w q -
        infiniteRow beta v B w q) ^ 2) (τ.prod (μ.prod (Measure.infinitePi ν)))) ∧
    Tendsto (fun n => ∫ q, ∑' w,
      (finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  have hrow := finiteRow_strict_timeMeasure_row_meanSquare hμ hb ν hB hmB hjoint
    D hD hconn hex v hv τ hτ hcrit
  have hvalid := fun n => DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun w => (finiteRow_strict_timeMeasure_error_bound hμ hb ν hB hmB hjoint
      D hD hconn hex v hv τ hτ w n).1) (hrow.1 n)
  refine ⟨hvalid, ?_⟩
  have heq (n : ℕ) : (∫ q, ∑' w,
      (finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) =
      ∑' w, ∫ q, (finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν)) := by
    exact (DiscrepancyEnergy.hasSum_integral_sq_row
      (fun w => ((measurable_finiteRow beta (D n) v hjoint w).sub
        (measurable_infiniteRow beta v hjoint w)).aestronglyMeasurable)
      (hvalid n).1 (hvalid n).2).tsum_eq.symm
  simp_rw [heq]
  exact hrow.2

theorem finiteRow_strict_fullWindow_row_lintegral_tendsto
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1) (T : ℝ) :
    Tendsto (fun n => ∫⁻ q, ∑' w, ENNReal.ofReal
      ((finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  apply finiteRow_strict_timeMeasure_row_lintegral_tendsto hμ hb ν hB hmB hjoint
    D hD hconn hex v hv (volume.restrict (Ioc 0 T)) _ hcrit
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ht.1.le

end Problem367.NormalizedInfiniteTimeEnergy

end

end OAI
