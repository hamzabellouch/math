import OAI.Probability.SLE.Stochastic.ProgressiveStoppedTime
import OAI.Probability.SLE.Gauge.ExtendedExperimentStop

namespace OAI

/-! Threshold tests on the finite part of an extended stopping time belong
  to its stopped past. No terminal mass is tested on the infinite event. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal ENNReal

namespace SLEExactGauge

def finiteStoppedThreshold {Ω : Type*} (X : ℝ≥0 → Ω → ℝ≥0∞)
    (S : Ω → WithTop ℝ≥0) (b : ℝ≥0∞) : Set Ω :=
  {ω | S ω<⊤ ∧ b≤X ((S ω).untopD 0) ω}

lemma finiteStoppedThreshold_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    (X : ℝ≥0 → Ω → ℝ≥0∞) (hX : IsProgressive ℱ X)
    (S : Ω → WithTop ℝ≥0) (hS : IsStoppingTime ℱ S) (b : ℝ≥0∞) :
    MeasurableSet[hS.measurableSpace] (finiteStoppedThreshold X S b) := by
  have hE (H : ℝ≥0) : MeasurableSet[ℱ H]
      ({ω | b≤X (cutoffStop S H ω) ω} ∩ {ω | S ω≤(H:WithTop ℝ≥0)}) := by
    have hm := _root_.OAI.MeasureTheory.IsProgressive.bounded_stopped_measurable hX (cutoffStop S H)
      (cutoffStop_stopping ℱ S hS H) H (fun ω => by
        have h := min_le_right (S ω) (H:WithTop ℝ≥0)
        rw [← cutoffStop_coe S H ω] at h
        exact WithTop.coe_le_coe.mp h)
    exact (measurableSet_le measurable_const hm).inter (hS H)
  have he (H : ℝ≥0) : finiteStoppedThreshold X S b ∩ {ω | S ω≤(H:WithTop ℝ≥0)} =
      {ω | b≤X (cutoffStop S H ω) ω} ∩ {ω | S ω≤(H:WithTop ℝ≥0)} := by
    ext ω
    simp only [finiteStoppedThreshold,mem_inter_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨_,hb⟩,hH⟩
      exact ⟨by rwa [cutoffStop_eq_on_success S H ω hH],hH⟩
    · rintro ⟨hb,hH⟩
      exact ⟨⟨lt_of_le_of_lt hH (WithTop.coe_lt_top _),
        by rwa [cutoffStop_eq_on_success S H ω hH] at hb⟩,hH⟩
  constructor
  · have hunion : finiteStoppedThreshold X S b = ⋃ n : ℕ,
        finiteStoppedThreshold X S b ∩ {ω | S ω≤((n:ℝ≥0):WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_iUnion,mem_inter_iff,mem_ofPred_eq]
      constructor
      · intro hω
        lift S ω to ℝ≥0 using hω.1.ne with t ht
        obtain ⟨n,hn⟩ := exists_nat_ge (t:ℝ)
        exact ⟨n,hω,by exact_mod_cast hn⟩
      · rintro ⟨_,hω,_⟩
        exact hω
    rw [hunion]
    exact MeasurableSet.iUnion (fun n => le_iSup ℱ (n:ℝ≥0) _ (by rw [he]; exact hE _))
  · intro H
    rw [he]
    exact hE H

end SLEExactGauge

end

end OAI
