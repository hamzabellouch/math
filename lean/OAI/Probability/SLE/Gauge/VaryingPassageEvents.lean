import Mathlib

namespace OAI

/-!
The `rc:varying-good-events` step of the ribbon argument. Positivity of a
conditional passage probability on one event gives a fixed lower probability
after intersecting with varying early-containment events. No uniform
conditional passage bound is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

theorem varying_passage_events_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (E C : Set Ω) (G : ℕ → Set Ω)
    (hE : MeasurableSet[m] E) (hC : MeasurableSet[mΩ] C)
    (hG : ∀ n, MeasurableSet[m] (G n)) (hEpos : 0 < P E)
    (hpassage : ∀ᵐ ω ∂P, ω ∈ E → 0 < P⁻[C.indicator (fun _ => 1) | m] ω)
    (hmissing : ∀ n, P (E \ G n) ≤ P E / 2) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ ∀ n, q₂ ≤ P (E ∩ G n ∩ C) := by
  let : MeasurableSpace Ω := mΩ
  let q : Ω → ℝ≥0∞ := P⁻[C.indicator (fun _ => 1) | m]
  have hqm : Measurable[m] q := measurable_condLExp m P _
  have hqmΩ : Measurable q := hqm.mono hm le_rfl
  let b : ℕ → ℝ≥0∞ := fun n => (1 / 2 : ℝ≥0∞) ^ n
  let S : ℕ → Set Ω := fun n => E ∩ {ω | q ω < b n}
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    (hm E hE).inter (measurableSet_lt hqmΩ measurable_const)
  have hSanti : Antitone S := by
    intro n k hnk ω hω
    exact ⟨hω.1, hω.2.trans_le
      (pow_le_pow_right_of_le_one' (by norm_num : (1 / 2 : ℝ≥0∞) ≤ 1) hnk)⟩
  have hblim : Tendsto b atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hinter : P (⋂ n, S n) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hpassage] with ω hω
    intro hmem
    have hEω : ω ∈ E := (mem_iInter.mp hmem 0).1
    have hle : q ω ≤ 0 := ge_of_tendsto hblim
      (Eventually.of_forall fun n => ((mem_iInter.mp hmem n).2).le)
    exact (not_le_of_gt (hω hEω)) hle
  have hsmalllim : Tendsto (fun n => P (S n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hinter] using
      tendsto_measure_iInter_atTop (fun n => (hSm n).nullMeasurableSet)
        hSanti ⟨0, measure_ne_top P _⟩
  have hquarter : 0 < P E / 4 := ENNReal.div_pos hEpos.ne' (by norm_num)
  obtain ⟨N, hN⟩ :=
    (hsmalllim.eventually (gt_mem_nhds hquarter)).exists
  let q₁ : ℝ≥0∞ := b N
  have hq₁ : 0 < q₁ := by
    exact ENNReal.pow_pos (ENNReal.div_pos one_ne_zero (by norm_num)) N
  refine ⟨q₁ * (P E / 4), ENNReal.mul_pos hq₁.ne' hquarter.ne', ?_⟩
  intro n
  let A : Set Ω := E ∩ G n
  let B : Set Ω := A ∩ {ω | q₁ ≤ q ω}
  have hAm : MeasurableSet[m] A := hE.inter (hG n)
  have hBm : MeasurableSet[m] B :=
    hAm.inter (measurableSet_le measurable_const hqm)
  have hcover : E ⊆ B ∪ (E \ G n) ∪ S N := by
    intro ω hω
    by_cases hωG : ω ∈ G n
    · by_cases hωq : q₁ ≤ q ω
      · exact Or.inl (Or.inl ⟨⟨hω, hωG⟩, hωq⟩)
      · exact Or.inr ⟨hω, lt_of_not_ge hωq⟩
    · exact Or.inl (Or.inr ⟨hω, hωG⟩)
  have hcovermeasure : P E ≤ P B + P (E \ G n) + P (S N) :=
    (measure_mono hcover).trans
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  have hBmass : P E / 4 ≤ P B := by
    have hcR := ENNReal.toReal_mono (by finiteness) hcovermeasure
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)] at hcR
    have hmR := ENNReal.toReal_mono (by finiteness) (hmissing n)
    have hsR := ENNReal.toReal_mono (by finiteness) hN.le
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat] at hmR hsR
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
    linarith
  calc
    q₁ * (P E / 4) ≤ q₁ * P B := mul_le_mul' le_rfl hBmass
    _ = ∫⁻ _ in B, q₁ ∂P := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ ω in B, q ω ∂P :=
      setLIntegral_mono' (hm B hBm) (fun _ hω => hω.2)
    _ ≤ ∫⁻ ω in A, q ω ∂P := lintegral_mono_set inter_subset_left
    _ = ∫⁻ ω in A, C.indicator (fun _ => 1) ω ∂P :=
      setLIntegral_condLExp hm P _ hAm
    _ = P (E ∩ G n ∩ C) := by
      rw [setLIntegral_indicator hC, setLIntegral_const, one_mul]
      congr 1
      exact inter_comm C A

end SLEExactGauge

end

end OAI
