import OAI.Probability.FreeIsing.Estimates.NormalizedCriticalRowConvergence
import OAI.Probability.FreeIsing.Estimates.NormalizedSubcriticalRowConvergence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedInfiniteTimeEnergy

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem finiteRow_threshold_row_lintegral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hthreshold : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (T : ℝ) :
    Tendsto (fun n => ∫⁻ q, ∑' w, ENNReal.ofReal
      ((finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν)))
      atTop (𝓝 0) := by
  obtain hstrict | hcritical := lt_or_eq_of_le hthreshold
  · exact finiteRow_strict_fullWindow_row_lintegral_tendsto hμ hb ν hB hmB hjoint
      D hD hconn hex v hv hstrict T
  · exact finiteRow_critical_row_lintegral_tendsto hd hμ hb hcritical ν hB hmB hjoint
      D hD hconn hex v hv T

theorem finiteRow_threshold_row_integral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hthreshold : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))
    let E := fun n w q => finiteRow beta (D n) v B w q - infiniteRow beta v B w q
    (∀ n, (∀ᵐ q ∂P, Summable (fun w => E n w q ^ 2)) ∧
      Integrable (fun q => ∑' w, E n w q ^ 2) P ∧
      HasSum (fun w => ∫ q, E n w q ^ 2 ∂P) (∫ q, ∑' w, E n w q ^ 2 ∂P)) ∧
    Tendsto (fun n => ∫ q, ∑' w, E n w q ^ 2 ∂P) atTop (𝓝 0) := by
  let P := (volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))
  let E := fun n w q => finiteRow beta (D n) v B w q - infiniteRow beta v B w q
  have hvalid (n : ℕ) := rowError_integrable hμ hb ν hB hmB hjoint
    (D n) (hconn n) v (hv n) hT
  refine ⟨hvalid, ?_⟩
  have heq (n : ℕ) : (∫ q, ∑' w, E n w q ^ 2 ∂P) =
      (∫⁻ q, ∑' w, ENNReal.ofReal (E n w q ^ 2) ∂P).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun q => tsum_nonneg fun w => sq_nonneg (E n w q))
      (hvalid n).2.1.aestronglyMeasurable]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(hvalid n).1] with q hq
    exact ENNReal.ofReal_tsum_of_nonneg (fun w => sq_nonneg _) hq
  have hlim := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
    (finiteRow_threshold_row_lintegral_tendsto hd hμ hb hthreshold ν hB hmB hjoint
      D hD hconn hex v hv T)
  change Tendsto (fun n => ∫ q, ∑' w, E n w q ^ 2 ∂P) atTop (𝓝 0)
  simp_rw [heq]
  exact hlim

end Problem367.NormalizedInfiniteTimeEnergy

end

end OAI
