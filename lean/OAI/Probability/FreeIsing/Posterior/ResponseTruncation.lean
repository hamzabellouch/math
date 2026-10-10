import OAI.Probability.FreeIsing.Energy.NormalizedResponseEnergy
import OAI.Probability.FreeIsing.Posterior.VarianceTruncation
import OAI.Probability.FreeIsing.Stochastic.StrictBrownianResponseEnergy

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367

theorem capped_mul_sq_le {a R c : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) :
    (min a R * c) ^ 2 ≤ (a * c) ^ 2 ∧
      (a * c - min a R * c) ^ 2 ≤ (a * c) ^ 2 := by
  have hm0 : 0 ≤ min a R := le_min ha hR
  have hma : min a R ≤ a := min_le_left _ _
  have hmin : (min a R) ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hm0 ha).mpr hma
  have hdiff : (a - min a R) ^ 2 ≤ a ^ 2 := by nlinarith
  constructor
  · simpa only [mul_pow] using mul_le_mul_of_nonneg_right hmin (sq_nonneg c)
  · calc
      (a * c - min a R * c) ^ 2 = (a - min a R) ^ 2 * c ^ 2 := by ring
      _ ≤ a ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_right hdiff (sq_nonneg c)
      _ = (a * c) ^ 2 := by ring

theorem summable_capped_mul_error_sq {ι : Type*} {a R : ℝ} {C : ι → ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hs : Summable (fun i => (a * C i) ^ 2)) :
    Summable (fun i => (a * C i - min a R * C i) ^ 2) ∧
      (∑' i, (a * C i - min a R * C i) ^ 2) ≤ ∑' i, (a * C i) ^ 2 := by
  have hb (i : ι) := (capped_mul_sq_le (c := C i) ha hR).2
  have he := Summable.of_nonneg_of_le (fun i => sq_nonneg _) hb hs
  exact ⟨he, Summable.tsum_le_tsum hb he hs⟩

theorem integrable_capped_mul_error_row
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → ℝ} {C : ι → Ω → ℝ}
    (hA : Measurable A) (hC : ∀ i, Measurable (C i))
    (hpos : ∀ᵐ ω ∂P, 0 ≤ A ω)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((A ω * C i ω) ^ 2) ∂P) ≠ ⊤)
    {R : ℝ} (hR : 0 ≤ R) :
    (∀ᵐ ω ∂P, Summable (fun i => (A ω * C i ω - min (A ω) R * C i ω) ^ 2)) ∧
    Integrable (fun ω => ∑' i, (A ω * C i ω - min (A ω) R * C i ω) ^ 2) P := by
  have hnorm (i : ι) : AEStronglyMeasurable (fun ω => A ω * C i ω) P :=
    (hA.mul (hC i)).aestronglyMeasurable
  have hs := ae_summable_sq_of_tsum_lintegral_sq_ne_top P hnorm henergy
  have hi := integrable_tsum_sq_of_tsum_lintegral_sq_ne_top P hnorm henergy
  have hb : ∀ᵐ ω ∂P,
      Summable (fun i => (A ω * C i ω - min (A ω) R * C i ω) ^ 2) ∧
      (∑' i, (A ω * C i ω - min (A ω) R * C i ω) ^ 2) ≤
        ∑' i, (A ω * C i ω) ^ 2 := by
    filter_upwards [hpos, hs] with ω hω hsω
    exact summable_capped_mul_error_sq hω hR hsω
  refine ⟨hb.mono (fun _ h => h.1), hi.mono' ?_ ?_⟩
  · exact (Measurable.tsum (fun i => ((hA.mul (hC i)).sub
      ((hA.min measurable_const).mul (hC i))).pow_const 2)).aestronglyMeasurable
  · filter_upwards [hb] with ω hω
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
    exact hω.2

theorem tendsto_integral_capped_mul_error_row
    {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → ℝ} {C : ι → Ω → ℝ}
    (hA : Measurable A) (hC : ∀ i, Measurable (C i))
    (hpos : ∀ᵐ ω ∂P, 0 ≤ A ω)
    (henergy : (∑' i, ∫⁻ ω, ENNReal.ofReal ((A ω * C i ω) ^ 2) ∂P) ≠ ⊤) :
    Tendsto (fun n : ℕ => ∫ ω, ∑' i,
      (A ω * C i ω - min (A ω) ((n : ℝ) + 1) * C i ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hnorm (i : ι) : AEStronglyMeasurable (fun ω => A ω * C i ω) P :=
    (hA.mul (hC i)).aestronglyMeasurable
  have hs := ae_summable_sq_of_tsum_lintegral_sq_ne_top P hnorm henergy
  have hi := integrable_tsum_sq_of_tsum_lintegral_sq_ne_top P hnorm henergy
  have hlim := tendsto_integral_of_dominated_convergence
    (fun ω => ∑' i, (A ω * C i ω) ^ 2)
    (f := fun _ : Ω => (0 : ℝ))
    (F := fun n : ℕ => fun ω => ∑' i : ι,
      (A ω * C i ω - min (A ω) ((n : ℝ) + 1) * C i ω) ^ 2)
    (fun n => (Measurable.tsum (fun i => ((hA.mul (hC i)).sub
      ((hA.min measurable_const).mul (hC i))).pow_const 2)).aestronglyMeasurable)
    hi ?_ ?_
  · simpa using hlim
  · intro n
    filter_upwards [hpos, hs] with ω hω hsω
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => sq_nonneg _))]
    exact (summable_capped_mul_error_sq hω (by positivity) hsω).2
  · apply ae_of_all
    intro ω
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt (A ω)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcap : A ω ≤ (n : ℝ) + 1 := by
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    simp only [min_eq_left hcap, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), tsum_zero]

def cappedGibbsResponse {d : ℕ} (beta R : ℝ) (u v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  inverseVarianceCap R (infiniteGibbsSpinMean beta u y) *
    infiniteGibbsCovariance beta u v y

theorem measurable_cappedGibbsResponse {d : ℕ} (beta R : ℝ) (u v : TreeVertex d) :
    Measurable (cappedGibbsResponse beta R u v) :=
  ((measurable_inverseVarianceCap R).comp
    (measurable_infiniteGibbsSpinMean beta u)).mul
      (measurable_infiniteGibbsCovariance beta u v)

theorem cappedGibbsResponse_abs_le {d : ℕ} (beta : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (u v : TreeVertex d) (y : TreeVertex d → ℝ) :
    |cappedGibbsResponse beta R u v y| ≤ 2 * R := by
  have hc := inverseVarianceCap_bounds hR (infiniteGibbsSpinMean_abs_le_one beta u y)
  rw [cappedGibbsResponse, abs_mul, abs_of_nonneg hc.1]
  calc
    _ ≤ R * 2 := mul_le_mul hc.2 (infiniteGibbsCovariance_abs_le_two beta u v y)
      (abs_nonneg _) hR
    _ = _ := by ring

theorem isStronglyProgressive_cappedGibbsResponse
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta R : ℝ) (u v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t ω => cappedGibbsResponse beta R u v (fun i => X i t ω)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_cappedGibbsResponse beta R u v).comp
    (Measurable.of_eval (fun i => (hX i t).measurable))).stronglyMeasurable

theorem cappedGibbsResponse_meanSquare_of_energy
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (beta : ℝ) (u : TreeVertex d) (Y : Ω → TreeVertex d → ℝ)
    (hY : Measurable Y)
    (henergy : (∑' v, ∫⁻ ω,
      ENNReal.ofReal (infiniteGibbsResponse beta u v (Y ω) ^ 2) ∂P) ≠ ⊤) :
    (∀ R : ℝ, 0 ≤ R →
      (∀ᵐ ω ∂P, Summable (fun v =>
        (infiniteGibbsResponse beta u v (Y ω) - cappedGibbsResponse beta R u v (Y ω)) ^ 2)) ∧
      Integrable (fun ω => ∑' v,
        (infiniteGibbsResponse beta u v (Y ω) - cappedGibbsResponse beta R u v (Y ω)) ^ 2) P) ∧
    Tendsto (fun n : ℕ => ∫ ω, ∑' v,
      (infiniteGibbsResponse beta u v (Y ω) -
        cappedGibbsResponse beta ((n : ℝ) + 1) u v (Y ω)) ^ 2 ∂P) atTop (𝓝 0) := by
  let A := fun ω => (1 - infiniteGibbsSpinMean beta u (Y ω) ^ 2)⁻¹
  let C := fun v ω => infiniteGibbsCovariance beta u v (Y ω)
  have hA : Measurable A :=
    ((measurable_const.sub (((measurable_infiniteGibbsSpinMean beta u).comp hY).pow_const 2))).inv
  have hC (v : TreeVertex d) : Measurable (C v) :=
    (measurable_infiniteGibbsCovariance beta u v).comp hY
  have hpos : ∀ᵐ ω ∂P, 0 ≤ A ω := by
    apply ae_of_all
    intro ω
    exact inv_nonneg.mpr (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr
      (infiniteGibbsSpinMean_abs_le_one beta u (Y ω))))
  have henergy' : (∑' v, ∫⁻ ω, ENNReal.ofReal ((A ω * C v ω) ^ 2) ∂P) ≠ ⊤ := by
    simpa only [A, C, infiniteGibbsResponse, div_eq_mul_inv, mul_comm] using henergy
  constructor
  · intro R hR
    simpa only [A, C, infiniteGibbsResponse, cappedGibbsResponse,
      inverseVarianceCap, div_eq_mul_inv, mul_comm] using
      integrable_capped_mul_error_row hA hC hpos henergy' hR
  · simpa only [A, C, infiniteGibbsResponse, cappedGibbsResponse,
      inverseVarianceCap, div_eq_mul_inv, mul_comm] using
      tendsto_integral_capped_mul_error_row hA hC hpos henergy'

theorem HasFreeIsingLaw.cappedGibbsResponse_meanSquare_time_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hjoint : ∀ i, Measurable (Function.uncurry (B i)))
    (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] (u : TreeVertex d) :
    let Y := fun z : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      fun i => (z.1 : ℝ) * spinSign (z.2.1 i) + B i z.1 (z.2.2 i)
    let P := ρ.prod (μ.prod (Measure.infinitePi ν))
    (∀ R : ℝ, 0 ≤ R →
      (∀ᵐ z ∂P, Summable (fun v =>
        (infiniteGibbsResponse beta u v (Y z) - cappedGibbsResponse beta R u v (Y z)) ^ 2)) ∧
      Integrable (fun z => ∑' v,
        (infiniteGibbsResponse beta u v (Y z) - cappedGibbsResponse beta R u v (Y z)) ^ 2) P) ∧
    Tendsto (fun n : ℕ => ∫ z, ∑' v,
      (infiniteGibbsResponse beta u v (Y z) -
        cappedGibbsResponse beta ((n : ℝ) + 1) u v (Y z)) ^ 2 ∂P) atTop (𝓝 0) := by
  dsimp only
  apply cappedGibbsResponse_meanSquare_of_energy
  · apply Measurable.of_eval
    intro i
    exact ((measurable_subtype_coe.comp measurable_fst).mul
      ((measurable_of_finite spinSign).comp
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
      ((hjoint i).comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
  · have hmB (i : TreeVertex d) (t : ℝ≥0) : Measurable (B i t) :=
      (hjoint i).comp (measurable_const.prodMk measurable_id)
    have he := (hμ.lintegral_infiniteGibbsResponseRow_time_lt_top_of_strict
      hbeta hstrict ν hB hmB ρ u).2
    rw [lintegral_tsum] at he
    · exact he.ne
    · intro v
      apply Measurable.aemeasurable
      apply Measurable.ennreal_ofReal
      apply Measurable.pow_const
      apply (measurable_infiniteGibbsResponse beta u v).comp
      apply Measurable.of_eval
      intro i
      exact ((measurable_subtype_coe.comp measurable_fst).mul
        ((measurable_of_finite spinSign).comp
          ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
        ((hjoint i).comp (measurable_fst.prodMk
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))

end Problem367

end

end OAI
