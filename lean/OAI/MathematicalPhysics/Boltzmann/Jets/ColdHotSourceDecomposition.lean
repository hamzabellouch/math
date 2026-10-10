import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotRegularity

namespace OAI

/-! # Exact separation of the hot source and the pure cold gain defect -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X] [Countable I]

theorem cold_gain_defect_identity {q b R : ℝ}
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i))
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    let C : X × Velocity → ℝ := fun z => ∑' i, c i z
    source q b 0 C p-(∑' i, coldSource q b 0 C (c i) p) =
      gain q b C p-∑' i, gain q b (c i) p := by
  intro C
  have hcs (z) : Summable (fun i => c i z) :=
    summable_of_sum_le (fun i => (hc i z).1) (fun s => hSum s z)
  have hCB (z) : 0 ≤ C z ∧ C z ≤ R :=
    ⟨tsum_nonneg (fun i => (hc i z).1),
      (Real.tsum_le_of_sum_le (fun i => (hc i z).1) (fun s => hSum s z)).trans (hF z)⟩
  have hCS (s : Finset I) (z) : ∑ i ∈ s, c i z ≤ C z :=
    (hcs z).sum_le_tsum s (fun i _ => (hc i z).1)
  rw [hot_source_identity 0 hcm (Measurable.tsum hcm) hc hCB hCS]
  have hz : C p-∑' i, c i p = 0 := sub_self _
  rw [hz,mul_zero,add_zero]

theorem hot_cold_source_decomposition {q b R : ℝ} (L : ℝ)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    let C : X × Velocity → ℝ := fun z => ∑' i, c i z
    source q b L F p-(∑' i, coldSource q b L F (c i) p)-L*(F p-C p) =
      (gain q b F p-gain q b C p)-frequency q b F p*(F p-C p)+
        (source q b 0 C p-∑' i, coldSource q b 0 C (c i) p) := by
  intro C
  rw [cold_gain_defect_identity hcm hc (fun z => (hF z).2) hSum,
    hot_source_identity L hcm hFm hc hF hSum]
  change (gain q b F p-∑' i, gain q b (c i) p)+
      (L-frequency q b F p)*(F p-C p)-L*(F p-C p) = _
  ring

end BoltzmannNonuniqueness.HotRepresentative

end

end OAI
