import OAI.Probability.FreeIsing.Estimates.DependentWeight
import OAI.Probability.FreeIsing.Trees.CutLevelConcentration

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ActualCutWeightedAverage

def average {d n : ℕ} {A : Type*}
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (I : Finset (TreeShell d n))
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ℝ :=
  (∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) / (I.card : ℝ)

theorem integral_mul_le
    {d : ℕ} {theta : ℝ} {A Ω : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    {ρ : Measure Ω} [IsFiniteMeasure ρ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ C M : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4)
    {weight g : Ω → ℝ}
    {G : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → ℝ}
    (hLaw : IdentDistrib g G ρ (μ.prod (Measure.infinitePi ν)))
    (hweight : Integrable weight ρ) (hg : Measurable g)
    (hw0 : ∀ᵐ x ∂ρ, 0 ≤ weight x) (hwM : ∀ᵐ x ∂ρ, weight x ≤ M)
    (hg0 : ∀ᵐ x ∂ρ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂ρ, g x ≤ 1)
    (hdom : ∀ᵐ z ∂μ.prod (Measure.infinitePi ν), G z ≤ C * average F I z) :
    (∫ x, weight x * g x ∂ρ) ≤
      (C * τ) * (∫ x, weight x ∂ρ) +
        M * Real.exp (-(I.card : ℝ) * τ ^ 2 / 2) := by
  have htail : ρ {x | C * τ < g x} =
      (μ.prod (Measure.infinitePi ν)) {z | C * τ < G z} :=
    hLaw.measure_mem_eq measurableSet_Ioi
  have hsubset : (μ.prod (Measure.infinitePi ν)) {z | C * τ < G z} ≤
      (μ.prod (Measure.infinitePi ν)) {z | τ ≤ average F I z} := by
    apply measure_mono_ae
    filter_upwards [hdom] with z hz
    intro hzg
    by_contra hza
    exact (not_lt_of_ge (hz.trans
      (mul_le_mul_of_nonneg_left (lt_of_not_ge hza).le hC))) hzg
  have hprob := hμ.measure_cutLevel_average_ge_le h0 h1 n ν F hF hbound I hI hτ hmean
  have hprob' : ρ {x | C * τ < g x} ≤
      ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
    rw [htail]
    exact hsubset.trans hprob
  apply DependentWeight.integral_mul_le_of_tail_probability hweight hg
    (mul_nonneg hC hτ) hM hw0 hwM hg0 hg1
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob').trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

theorem integral_mul_le_double_exp
    {d : ℕ} {theta : ℝ} {A Ω : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    {ρ : Measure Ω} [IsFiniteMeasure ρ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {b ℓ q C M : ℝ}
    (hb : 0 < b) (hℓ : 0 ≤ ℓ) (hq : q ≤ Real.log b / 8)
    (hcard : b ^ (ℓ / 2 - 1) ≤ (I.card : ℝ)) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤
        Real.exp (-q * ℓ) / 4)
    {weight g : Ω → ℝ}
    {G : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → ℝ}
    (hLaw : IdentDistrib g G ρ (μ.prod (Measure.infinitePi ν)))
    (hweight : Integrable weight ρ) (hg : Measurable g)
    (hw0 : ∀ᵐ x ∂ρ, 0 ≤ weight x) (hwM : ∀ᵐ x ∂ρ, weight x ≤ M)
    (hg0 : ∀ᵐ x ∂ρ, 0 ≤ g x) (hg1 : ∀ᵐ x ∂ρ, g x ≤ 1)
    (hdom : ∀ᵐ z ∂μ.prod (Measure.infinitePi ν), G z ≤ C * average F I z) :
    (∫ x, weight x * g x ∂ρ) ≤
      (C * Real.exp (-q * ℓ)) * (∫ x, weight x ∂ρ) +
        M * Real.exp (-(b ^ (ℓ / 4)) / (2 * b)) := by
  exact (integral_mul_le hμ h0 h1 n ν F hF hbound I hI (Real.exp_pos _).le
    hC hM hmean hLaw hweight hg hw0 hwM hg0 hg1 hdom).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (BoundedAverageConcentration.exponential_card_bound hb hℓ hq hcard) hM))

end Problem367.ActualCutWeightedAverage

end

end OAI
