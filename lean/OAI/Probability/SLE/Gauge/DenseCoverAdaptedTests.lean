import OAI.Probability.SLE.Gauge.DenseVisitNumerics

namespace OAI

/-! Adapted dense-visit tests at the manuscript's actual logarithmic
multiplicity and linear index window.  This proves the failure calculation
without independence between the tests. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem complement_inter_bound_of_success_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {B E : Set Ω} (hE : MeasurableSet E) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsuccess : ENNReal.ofReal p * μ B ≤ μ (B ∩ E)) :
    μ (B ∩ Eᶜ) ≤ ENNReal.ofReal (1 - p) * μ B := by
  have he := congrArg ENNReal.toReal (measure_sdiff_add_inter (μ := μ) B hE)
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at he
  have hs := ENNReal.toReal_mono (measure_ne_top _ _) hsuccess
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] at hs
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]
  rw [Set.sdiff_eq] at he
  nlinarith

/-- The exact finite window can start at any filtration index. -/
theorem adapted_failures_Icc_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (F : Filtration ℕ mΩ) (failure : ℕ → Set Ω)
    (hmeas : ∀ j, MeasurableSet[F (j + 1)] (failure j))
    (q : ℝ≥0∞)
    (hstep : ∀ j (B : Set Ω), MeasurableSet[F j] B →
      μ (B ∩ failure j) ≤ q * μ B)
    (a b : ℕ) (hab : a ≤ b) :
    μ (⋂ j ∈ Finset.Icc a b, failure j) ≤ q ^ (b + 1 - a) * μ univ := by
  let F' : Filtration ℕ mΩ :=
    ⟨fun j => F (a + j), fun _ _ h => F.mono (Nat.add_le_add_left h a),
      fun j => F.le (a + j)⟩
  have hh := adapted_failures_bound μ F' (fun j => failure (a + j))
    (fun j => by simpa only [F', Nat.add_assoc] using hmeas (a + j)) q
    (fun j B hB => hstep (a + j) B hB) (b + 1 - a)
  have he : (⋂ j ∈ Finset.range (b + 1 - a), failure (a + j)) =
      ⋂ j ∈ Finset.Icc a b, failure j := by
    ext ω
    simp only [mem_iInter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro h j hj
      have heq : a + (j - a) = j := by omega
      simpa only [heq] using h (j - a) (by omega)
    · intro h j hj
      exact h (a + j) ⟨by omega, by omega⟩
  rwa [he] at hh

/-- Conditional success bounds at the actual scale yield the stretched
exponential bound for failure of every test in the cover window. -/
theorem cover_window_failure_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ mΩ) (success : ℕ → Set Ω)
    (hmeas : ∀ j, MeasurableSet[F (j + 1)] (success j))
    (n : ℕ) (hn : 1 ≤ n)
    (hstep : ∀ j (B : Set Ω), MeasurableSet[F j] B →
      ENNReal.ofReal (1 / Real.sqrt (n : ℝ)) * μ B ≤ μ (B ∩ success j)) :
    μ (⋂ j ∈ coverTestWindow n, (success j)ᶜ) ≤
      ENNReal.ofReal (Real.exp (-Real.sqrt (n : ℝ) / 4)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnR
  have hspos : 0 < Real.sqrt (n : ℝ) := zero_lt_one.trans_le hs1
  have hp : 1 / Real.sqrt (n : ℝ) ≤ 1 := (div_le_one hspos).mpr hs1
  have hb := adapted_failures_Icc_bound μ F (fun j => (success j)ᶜ)
    (fun j => (hmeas j).compl) (ENNReal.ofReal (1 - 1 / Real.sqrt (n : ℝ)))
    (fun j B hB => complement_inter_bound_of_success_lower μ
      (F.le (j + 1) _ (hmeas j)) (one_div_nonneg.mpr hspos.le) hp (hstep j B hB))
    (n / 3) (2 * n / 3) (by omega)
  rw [measure_univ, mul_one] at hb
  change μ (⋂ j ∈ coverTestWindow n, (success j)ᶜ) ≤ _ at hb
  have hcard : (coverTestWindow n).card = 2 * n / 3 + 1 - n / 3 := by
    simp only [coverTestWindow, Nat.card_Icc]
  rw [← hcard] at hb
  refine hb.trans ?_
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr hp)]
  exact ENNReal.ofReal_le_ofReal
    (failure_window_le_stretchedExp hnR (coverTestWindow n).card
      (coverTestWindow_card_real_lower n))

theorem denseVisit_cover_window_failure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ mΩ) (success : ℕ → ℕ → Set Ω)
    (hmeas : ∀ n j, MeasurableSet[F n (j + 1)] (success n j))
    {a C c : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 < c)
    (hsmall : C * c ^ 2 ≤ 1 / 4)
    (hstep : ∀ n j (B : Set Ω), MeasurableSet[F n j] B →
      ENNReal.ofReal (a * Real.exp (-C * (coverMultiplicity c n : ℝ) ^ 2)) * μ B ≤
        μ (B ∩ success n j)) :
    ∀ᶠ n : ℕ in atTop,
      μ (⋂ j ∈ coverTestWindow n, (success n j)ᶜ) ≤
        ENNReal.ofReal (Real.exp (-Real.sqrt (n : ℝ) / 4)) := by
  filter_upwards [denseVisit_probability_eventually_lower ha hC hc hsmall,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  apply cover_window_failure_bound μ (F n) (success n) (hmeas n) n hn1
  intro j B hB
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hn) le_rfl).trans (hstep n j B hB)

end SLEExactGauge

end

end OAI
