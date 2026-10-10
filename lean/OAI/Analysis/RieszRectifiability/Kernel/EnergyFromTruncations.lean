import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

theorem nonnegative_integrable_of_exhaustion {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hmono : Monotone s)
    (hcover : Function.support f ⊆ ⋃ k, s k)
    (hI : ∀ k, IntegrableOn f (s k) μ) (B : ℝ)
    (hB : ∀ k, (∫ x in s k, f x ∂μ) ≤ B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hpos
  have hfull : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (f x) ∂μ := by
    rw [← lintegral_indicator (MeasurableSet.iUnion hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ⋃ k, s k
    · rw [indicator_of_mem hx]
    · have hfx : f x = 0 := by
        by_contra h
        exact hx (hcover h)
      rw [indicator_of_notMem hx, hfx, ENNReal.ofReal_zero]
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [hfull, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    apply iSup_le
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k) (Filter.Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have hfin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp hfin
  refine ⟨hint, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg hpos).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hbound

theorem fractionalEnergy_integrable_of_truncated_bounds {X : Type*}
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (ρ : Measure (X × X)) (m : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hI : ∀ ε : ℝ, 0 < ε → IntegrableOn
      (fun q : X × X => fractionalPairEnergy m w q.1 q.2) {q | ε < dist q.1 q.2} ρ)
    (B : ℝ) (hB : ∀ ε : ℝ, 0 < ε →
      (∫ q in {q : X × X | ε < dist q.1 q.2}, fractionalPairEnergy m w q.1 q.2 ∂ρ) ≤ B) :
    Integrable (fun q : X × X => fractionalPairEnergy m w q.1 q.2) ρ ∧
      (∫ q : X × X, fractionalPairEnergy m w q.1 q.2 ∂ρ) ≤ B := by
  apply nonnegative_integrable_of_exhaustion ρ
    (fun q : X × X => fractionalPairEnergy m w q.1 q.2)
    (by unfold fractionalPairEnergy; fun_prop)
    (fun q => fractionalPairEnergy_nonneg m w q.1 q.2)
    (fun k : ℕ => {q : X × X | (1 / 2 : ℝ) ^ k < dist q.1 q.2})
    (fun _ => measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable)
    _ _ (fun k => hI _ (by positivity)) B (fun k => hB _ (by positivity))
  · intro k l hkl q hq
    have hp : (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl
    exact lt_of_le_of_lt hp hq
  · intro q hq
    have hne : q.1 ≠ q.2 := by
      intro h
      apply hq
      simp only [fractionalPairEnergy, h, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hne)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact mem_iUnion.mpr ⟨k, hk⟩

theorem pairwise_square_product_integrable {X : Type*}
    [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ) :
    Integrable (fun q : X × X => (w q.1 - w q.2) ^ 2) (μ.prod μ) := by
  have hdom := ((hL2.integrable_sq.comp_fst μ).add (hL2.integrable_sq.comp_snd μ)).const_mul 2
  apply hdom.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (w q.1 - w q.2) ^ 2 ≤ 2 * (w q.1 ^ 2 + w q.2 ^ 2)
  nlinarith [sq_nonneg (w q.1 + w q.2)]

theorem truncated_fractionalEnergy_integrable {X : Type*}
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] (m : ℕ)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun q : X × X => fractionalPairEnergy m w q.1 q.2)
      {q | ε < dist q.1 q.2} (μ.prod μ) := by
  have hs : MeasurableSet {q : X × X | ε < dist q.1 q.2} :=
    measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable
  have hm : Measurable (fun q : X × X => fractionalPairEnergy m w q.1 q.2) := by
    unfold fractionalPairEnergy
    fun_prop
  apply ((pairwise_square_product_integrable μ w hw hL2).const_mul ((ε ^ (m + 1))⁻¹)).restrict.mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs] with q hq
  rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _)]
  have hpow : (dist q.1 q.2 ^ (m + 1))⁻¹ ≤ (ε ^ (m + 1))⁻¹ := by
    simpa only [one_div] using! one_div_le_one_div_of_le (pow_pos hε (m + 1))
      (pow_le_pow_left₀ hε.le hq.le (m + 1))
  simpa only [fractionalPairEnergy, div_eq_mul_inv, mul_comm] using!
    mul_le_mul_of_nonneg_left hpow (sq_nonneg (w q.1 - w q.2))

theorem fractionalEnergy_integrable_of_uniform_bound {X : Type*}
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] (m : ℕ)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (B : ℝ) (hB : ∀ ε : ℝ, 0 < ε →
      (∫ q in {q : X × X | ε < dist q.1 q.2}, fractionalPairEnergy m w q.1 q.2
        ∂μ.prod μ) ≤ B) :
    Integrable (fun q : X × X => fractionalPairEnergy m w q.1 q.2) (μ.prod μ) ∧
      (∫ q : X × X, fractionalPairEnergy m w q.1 q.2 ∂μ.prod μ) ≤ B :=
  fractionalEnergy_integrable_of_truncated_bounds (μ.prod μ) m w hw
    (truncated_fractionalEnergy_integrable μ m w hw hL2) B hB

end

end RieszRectifiability

end OAI
