import OAI.Probability.SLE.SausageSeedAll

namespace OAI

/-!
The last probabilistic transfer in the ribbon step: a finite deterministic
list of retained time intervals permits subtracting one unconditional
small-sausage exception from the varying passage events. The sausage
estimate is never conditioned on passage.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- The finite-list subtraction step of `rc:step`. Passage may select a
different deterministic interval on each sample and at each mesh. -/
theorem ribbon_passage_mass_of_eventually_finite_intervals
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : ∀ J ∈ I, J.1 < J.2)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n))
    (physicalMass : ℕ → Ω → ℝ≥0∞) (passage : ℕ → Ω → Prop)
    (c : ℝ) (hc : 0 < c)
    (htransfer : ∀ᶠ n in atTop, ∀ ω, ω ∈ G n → passage n ω ∧
      ∃ J ∈ I, ENNReal.ofReal c *
        sourceSausageMass κ (γ ω) J.1 J.2 (v n) ≤ physicalMass n ω) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 2) ≤
        P {ω | ω ∈ G n ∧ passage n ω ∧ ENNReal.ofReal a ≤ physicalMass n ω} := by
  obtain ⟨b, e₀, hb, he₀, hsmall⟩ := sourceSmallSausageMain_proved
    Ω inferInstance P inferInstance κ hκ hκ8 γ hSLE I hI (q / 2) (by positivity)
  refine ⟨c * b, mul_pos hc hb, ?_⟩
  have hevent : ∀ᶠ n in atTop, v n < e₀ :=
    (tendsto_order.mp hlim).2 e₀ he₀
  filter_upwards [hevent, hG, htransfer] with n hn hGn htransfern
  let bad : Set Ω := {ω | ∃ J ∈ I,
    sourceSausageMass κ (γ ω) J.1 J.2 (v n) < ENNReal.ofReal b}
  let good : Set Ω := {ω | ω ∈ G n ∧ passage n ω ∧
    ENNReal.ofReal (c * b) ≤ physicalMass n ω}
  have hbad : P bad < ENNReal.ofReal (q / 2) := hsmall (v n) (hv n) hn
  have hcover : G n ⊆ good ∪ bad := by
    intro ω hω
    by_cases hbadω : ω ∈ bad
    · exact Or.inr hbadω
    · obtain ⟨hpassage, J, hJI, hmass⟩ := htransfern ω hω
      left
      refine ⟨hω, hpassage, ?_⟩
      have hsausage : ENNReal.ofReal b ≤ sourceSausageMass κ (γ ω) J.1 J.2 (v n) := by
        by_contra h
        exact hbadω ⟨J, hJI, lt_of_not_ge h⟩
      rw [ENNReal.ofReal_mul hc.le]
      exact (mul_le_mul' le_rfl hsausage).trans hmass
  change ENNReal.ofReal (q / 2) ≤ P good
  by_contra hgood
  have hhalf : ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) =
      ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hlt : P good + P bad < ENNReal.ofReal q := by
    rw [← hhalf]
    exact ENNReal.add_lt_add (lt_of_not_ge hgood) hbad
  exact (not_lt_of_ge hGn)
    (((measure_mono hcover).trans (measure_union_le good bad)).trans_lt hlt)

/-- A version with transfer and probability bounds at every index. -/
theorem ribbon_passage_mass_of_finite_intervals
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : ∀ J ∈ I, J.1 < J.2)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ n, ENNReal.ofReal q ≤ P (G n))
    (physicalMass : ℕ → Ω → ℝ≥0∞) (passage : ℕ → Ω → Prop)
    (c : ℝ) (hc : 0 < c)
    (htransfer : ∀ n ω, ω ∈ G n → passage n ω ∧
      ∃ J ∈ I, ENNReal.ofReal c *
        sourceSausageMass κ (γ ω) J.1 J.2 (v n) ≤ physicalMass n ω) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 2) ≤
        P {ω | ω ∈ G n ∧ passage n ω ∧ ENNReal.ofReal a ≤ physicalMass n ω} :=
  ribbon_passage_mass_of_eventually_finite_intervals P κ hκ hκ8 γ hSLE I hI
    v hv hlim G q hq (Eventually.of_forall hG) physicalMass passage c hc
    (Eventually.of_forall htransfer)

/-- The same finite-list transfer with passage already included in `G n`. -/
theorem ribbon_mass_of_finite_intervals
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : ∀ J ∈ I, J.1 < J.2)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ n, ENNReal.ofReal q ≤ P (G n))
    (physicalMass : ℕ → Ω → ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (htransfer : ∀ n ω, ω ∈ G n →
      ∃ J ∈ I, ENNReal.ofReal c *
        sourceSausageMass κ (γ ω) J.1 J.2 (v n) ≤ physicalMass n ω) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 2) ≤
        P {ω | ω ∈ G n ∧ ENNReal.ofReal a ≤ physicalMass n ω} := by
  obtain ⟨a, ha, hevent⟩ := ribbon_passage_mass_of_finite_intervals
    P κ hκ hκ8 γ hSLE I hI v hv hlim G q hq hG physicalMass
    (fun _ _ => True) c hc (fun n ω hω => ⟨trivial, htransfer n ω hω⟩)
  refine ⟨a, ha, ?_⟩
  simpa only [true_and] using hevent

end SLEExactGauge

end

end OAI
