import OAI.Probability.FreeIsing.Critical.NormalizedEnergy
import OAI.Probability.FreeIsing.Estimates.NormalizedPositiveWindowRow
import OAI.Probability.FreeIsing.Trees.RowEnergyCutoff

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedInfiniteTimeEnergy

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem lintegral_finiteRow_le
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ q, ∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤
      ENNReal.ofReal (2 * ((d : ℝ) * beta + T + Real.sqrt T)) := by
  let := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let r : D := ⟨v, hv⟩
  have hm : Measurable (fun q => ∑' w,
      ENNReal.ofReal (finiteRow beta D v B w q ^ 2)) :=
    Measurable.tsum fun w =>
      ((measurable_finiteRow beta D v hjoint w).pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hm.aemeasurable]
  have heq (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
      (∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2)) =
        ENNReal.ofReal (∑ w : D,
          finiteIsingBrownianNormalizedCovariance beta D r w B q.1 q.2 ^ 2) :=
    tsum_finiteRow_sq beta D r B q
  simp only [heq]
  exact hμ.lintegral_finiteIsingBrownianNormalizedEnergy_le hb ν hB hmB D hD r hT

theorem lintegral_rowError_ne_top
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ q, ∑' w, ENNReal.ofReal
      ((finiteRow beta D v B w q - infiniteRow beta v B w q) ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≠ ⊤ := by
  have hf := lintegral_finiteRow_le hμ hb ν hB hmB hjoint D hD v hv hT
  have hi := lintegral_infiniteRow_le hμ hb ν hB hmB hjoint v hT
  have he := (RowEnergyCutoff.lintegral_tsum_sq_sub_le
    ((volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν)))
    (fun w => measurable_finiteRow beta D v hjoint w)
    (fun w => measurable_infiniteRow beta v hjoint w)).trans
    (add_le_add (mul_le_mul_right hf 2) (mul_le_mul_right hi 2))
  exact ne_top_of_le_ne_top (by finiteness) he

theorem rowError_integrable
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) {T : ℝ} (hT : 0 ≤ T) :
    let P := (volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))
    let E := fun w q => finiteRow beta D v B w q - infiniteRow beta v B w q
    (∀ᵐ q ∂P, Summable (fun w => E w q ^ 2)) ∧
      Integrable (fun q => ∑' w, E w q ^ 2) P ∧
      HasSum (fun w => ∫ q, E w q ^ 2 ∂P) (∫ q, ∑' w, E w q ^ 2 ∂P) := by
  let P := (volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))
  let E := fun w q => finiteRow beta D v B w q - infiniteRow beta v B w q
  have hm (w : TreeVertex d) : Measurable (E w) :=
    (measurable_finiteRow beta D v hjoint w).sub (measurable_infiniteRow beta v hjoint w)
  have hf : (∑' w, ∫⁻ q, ENNReal.ofReal (E w q ^ 2) ∂P) ≠ ⊤ := by
    rw [← lintegral_tsum (fun w => ((hm w).pow_const 2).ennreal_ofReal.aemeasurable)]
    exact lintegral_rowError_ne_top hμ hb ν hB hmB hjoint D hD v hv hT
  have hs := ae_summable_sq_of_tsum_lintegral_sq_ne_top P
    (fun w => (hm w).aestronglyMeasurable) hf
  have hi := integrable_tsum_sq_of_tsum_lintegral_sq_ne_top P
    (fun w => (hm w).aestronglyMeasurable) hf
  exact ⟨hs, hi, DiscrepancyEnergy.hasSum_integral_sq_row
    (fun w => (hm w).aestronglyMeasurable) hs hi⟩

theorem lintegral_finiteRow_le_criticalEnvelope
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) (T : ℝ≥0) (hT : (T : ℝ) ≤ 1) :
    (∫⁻ q, ∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν))) ≤
      ENNReal.ofReal (criticalEntropyEnvelope d beta T) := by
  let := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let r : D := ⟨v, hv⟩
  have hm : Measurable (fun q => ∑' w,
      ENNReal.ofReal (finiteRow beta D v B w q ^ 2)) :=
    Measurable.tsum fun w =>
      ((measurable_finiteRow beta D v hjoint w).pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hm.aemeasurable]
  have heq (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
      (∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2)) =
        ENNReal.ofReal (∑ w : D,
          finiteIsingBrownianNormalizedCovariance beta D r w B q.1 q.2 ^ 2) :=
    tsum_finiteRow_sq beta D r B q
  simp only [heq]
  exact (hμ.lintegral_finiteIsingBrownianNormalizedEnergy_le_entropy hb ν hB hmB
    D hD r T.property).trans (ENNReal.ofReal_le_ofReal
      (hμ.finiteIsingBrownianEntropy_le_criticalEnvelope hd hb hcritical ν hB hmB
        D hD r T hT))

theorem lintegral_rowError_le_criticalEnvelope
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) (T : ℝ≥0) (hT : (T : ℝ) ≤ 1) :
    (∫⁻ q, ∑' w, ENNReal.ofReal
      ((finiteRow beta D v B w q - infiniteRow beta v B w q) ^ 2)
      ∂(volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν))) ≤
      4 * ENNReal.ofReal (criticalEntropyEnvelope d beta T) := by
  have hf := lintegral_finiteRow_le_criticalEnvelope hd hμ hb hcritical ν hB hmB hjoint
    D hD v hv T hT
  have hi := lintegral_infiniteRow_le_criticalEnvelope hd hμ hb hcritical ν hB hmB hjoint
    v T hT
  refine (RowEnergyCutoff.lintegral_tsum_sq_sub_le
    ((volume.restrict (Ioc 0 (T : ℝ))).prod (μ.prod (Measure.infinitePi ν)))
    (fun w => measurable_finiteRow beta D v hjoint w)
    (fun w => measurable_infiniteRow beta v hjoint w)).trans ?_
  calc
    _ ≤ 2 * ENNReal.ofReal (criticalEntropyEnvelope d beta T) +
        2 * ENNReal.ofReal (criticalEntropyEnvelope d beta T) :=
      add_le_add (mul_le_mul_right hf 2) (mul_le_mul_right hi 2)
    _ = _ := by ring

theorem finiteRow_critical_row_lintegral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
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
  let := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hK : Tendsto (fun δ : ℝ =>
      (4 : ℝ≥0∞) * ENNReal.ofReal (criticalEntropyEnvelope d beta δ))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ =>
        (4 : ℝ≥0∞) * ENNReal.ofReal (criticalEntropyEnvelope d beta δ)) :=
      (ENNReal.continuous_const_mul (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).comp
        (ENNReal.continuous_ofReal.comp (continuous_criticalEntropyEnvelope d beta))
    simpa using hc.tendsto (0 : ℝ)
  apply RowEnergyCutoff.tendsto_zero_of_cutoff
    (L := fun δ n => ∫⁻ q, ∑' w, ENNReal.ofReal
      ((finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2)
      ∂(volume.restrict (Ioc δ T)).prod (μ.prod (Measure.infinitePi ν))) hK
  · intro δ hδ hδone n
    have hm : Measurable (fun q => ∑' w, ENNReal.ofReal
        ((finiteRow beta (D n) v B w q - infiniteRow beta v B w q) ^ 2)) :=
      Measurable.tsum fun w => (((measurable_finiteRow beta (D n) v hjoint w).sub
        (measurable_infiniteRow beta v hjoint w)).pow_const 2).ennreal_ofReal
    exact (RowEnergyCutoff.lintegral_Ioc_prod_le_add
      (μ.prod (Measure.infinitePi ν)) hm δ T).trans
      (add_le_add (lintegral_rowError_le_criticalEnvelope hd hμ hb hcritical ν hB hmB hjoint
        (D n) (hconn n) v (hv n) ⟨δ, hδ.le⟩ hδone) le_rfl)
  · intro δ hδ
    exact finiteRow_positiveWindow_row_lintegral_tendsto hμ hb ν hB hmB hjoint
      D hD hconn hex v hv hcritical.le hδ T

theorem finiteRow_critical_row_integral_tendsto
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
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
    (finiteRow_critical_row_lintegral_tendsto hd hμ hb hcritical ν hB hmB hjoint
      D hD hconn hex v hv T)
  change Tendsto (fun n => ∫ q, ∑' w, E n w q ^ 2 ∂P) atTop (𝓝 0)
  simp_rw [heq]
  exact hlim

end Problem367.NormalizedInfiniteTimeEnergy

end

end OAI
