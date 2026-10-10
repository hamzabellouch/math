import OAI.Probability.SLE.Loewner.TargetCutoffMeasurability

namespace OAI

/-! A measurable compact minimum gives the exact countable survival
criterion, and therefore measurability of the prescribed uncut flow. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

def cutoffMinimum (κ : ℝ) (j : ℕ) (b : Driver) (z : ℂ) (T : ℝ≥0) : ℝ≥0∞ :=
  ⨅ r : unitInterval, ENNReal.ofReal (cutoffFlow κ b j z ((T : ℝ)*r)).im

lemma cutoffMinimum_eq (κ : ℝ) (j : ℕ) (b : Driver) (z : ℂ) (T : ℝ≥0) :
    cutoffMinimum κ j b z T =
      ENNReal.ofReal (sInf ((fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 (T : ℝ))) := by
  have hrange : Set.range (fun r : unitInterval => (T : ℝ)*r) = Icc 0 (T : ℝ) := by
    ext u
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨mul_nonneg T.coe_nonneg r.2.1,
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left r.2.2 T.coe_nonneg⟩
    · intro hu
      by_cases hT : (T : ℝ)=0
      · refine ⟨0,?_⟩
        have hu0 : u=0 := le_antisymm (by simpa only [hT] using hu.2) hu.1
        simp only [hT,zero_mul,hu0]
      · have hT0 : 0 < (T : ℝ) := lt_of_le_of_ne T.coe_nonneg (Ne.symm hT)
        refine ⟨⟨u/T,div_nonneg hu.1 T.coe_nonneg,(div_le_one hT0).mpr hu.2⟩,?_⟩
        field_simp [hT]
  have himage : Set.range (fun r : unitInterval =>
      (cutoffFlow κ b j z ((T : ℝ)*r)).im) =
      (fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 (T : ℝ) := by
    rw [← hrange]
    exact Set.range_comp (fun u : ℝ => (cutoffFlow κ b j z u).im)
      (fun r : unitInterval => (T : ℝ)*r)
  unfold cutoffMinimum
  rw [← ENNReal.ofReal_iInf]
  congr 1
  change sInf _ = sInf _
  rw [himage]

lemma measurable_cutoffMinimum (κ : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => cutoffMinimum κ j q.2.1 q.2.2 q.1) := by
  have hm : Measurable (⨅ r : unitInterval, fun q : ℝ≥0 × (Driver × ℂ) =>
      ENNReal.ofReal (cutoffFlow κ q.2.1 j q.2.2 ((q.1 : ℝ)*r)).im) := by
    apply measurable_iInf_of_upperSemicontinuous
    · intro r
      let s : ℝ≥0 := ⟨(r : ℝ),r.2.1⟩
      have hm := (measurable_cutoffFlow κ j hj).comp
        ((measurable_fst.mul_const s).prodMk measurable_snd)
      exact (Complex.measurable_im.comp hm).ennreal_ofReal
    · intro q
      have hc : Continuous (fun r : unitInterval => cutoffFlow κ q.2.1 j q.2.2
          ((q.1 : ℝ)*r)) :=
        (cutoffFlow_continuousOn κ q.2.1 j hj q.2.2).comp_continuous
          (continuous_const.mul continuous_subtype_val)
          (fun r => mul_nonneg q.1.coe_nonneg r.2.1)
      exact (ENNReal.continuous_ofReal.comp (Complex.continuous_im.comp hc)).upperSemicontinuous
  change Measurable (fun q : ℝ≥0 × (Driver × ℂ) =>
    (⨅ r : unitInterval, fun p : ℝ≥0 × (Driver × ℂ) =>
      ENNReal.ofReal (cutoffFlow κ p.2.1 j p.2.2 ((p.1 : ℝ)*r)).im) q) at hm
  simpa only [iInf_apply,cutoffMinimum] using hm

lemma cutoff_survival_iff_minimum (κ : ℝ) (j : ℕ) (_hj : 1 ≤ j)
    (b : Driver) (z : ℂ) (T : ℝ≥0) :
    (j : ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 (T : ℝ)) ↔
      ENNReal.ofReal ((j : ℝ)⁻¹) < cutoffMinimum κ j b z T := by
  rw [cutoffMinimum_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg j))).symm

lemma measurableSet_cutoff_survival (κ : ℝ) (j : ℕ) :
    MeasurableSet {q : ℝ≥0 × (Driver × ℂ) | 1 ≤ j ∧
      (j : ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ q.2.1 j q.2.2 u).im) ''
        Icc 0 (q.1 : ℝ))} := by
  by_cases hj : 1 ≤ j
  · have he : {q : ℝ≥0 × (Driver × ℂ) | 1 ≤ j ∧
        (j : ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ q.2.1 j q.2.2 u).im) ''
          Icc 0 (q.1 : ℝ))} =
        {q | ENNReal.ofReal ((j : ℝ)⁻¹) < cutoffMinimum κ j q.2.1 q.2.2 q.1} := by
      ext q
      simp only [mem_ofPred_eq,and_iff_right hj,cutoff_survival_iff_minimum κ j hj]
    rw [he]
    exact measurableSet_lt measurable_const (measurable_cutoffMinimum κ j hj)
  · simp only [hj,false_and,ofPred_false,MeasurableSet.empty]

lemma measurableSet_surviving (κ : ℝ) :
    MeasurableSet {q : ℝ≥0 × (Driver × ℂ) | Surviving κ q.2.1 q.2.2 q.1} := by
  change MeasurableSet {q : ℝ≥0 × (Driver × ℂ) | ∃ j : ℕ, 1 ≤ j ∧
    (j : ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ q.2.1 j q.2.2 u).im) '' Icc 0 (q.1 : ℝ))}
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion (measurableSet_cutoff_survival κ)

lemma measurable_flow (κ : ℝ) :
    Measurable (fun q : ℝ≥0 × (Driver × ℂ) => flow κ q.2.1 q.2.2 q.1) := by
  let S : Set (ℝ≥0 × (Driver × ℂ)) := {q | Surviving κ q.2.1 q.2.2 q.1}
  let f (j : ℕ) (q : S) : ℂ :=
    if 1 ≤ j then cutoffFlow κ q.1.2.1 j q.1.2.2 q.1.1 else 0
  have hf (j : ℕ) : Measurable (f j) := by
    by_cases hj : 1 ≤ j
    · simpa only [f,ite_eq_left hj,Function.comp_def] using
        (measurable_cutoffFlow κ j hj).comp measurable_subtype_coe
    · simp only [f,ite_eq_right hj]
      exact measurable_const
  have hp (j : ℕ) : MeasurableSet {q : S | 1 ≤ j ∧
      (j : ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ q.1.2.1 j q.1.2.2 u).im) ''
        Icc 0 (q.1.1 : ℝ))} :=
    measurable_subtype_coe (measurableSet_cutoff_survival κ j)
  have hm := (Measurable.find hf hp (fun q : S => q.2)).dite
    (g := fun _ : (Sᶜ : Set (ℝ≥0 × (Driver × ℂ))) => (0 : ℂ))
      measurable_const (measurableSet_surviving κ)
  convert hm using 1
  funext q
  by_cases hq : Surviving κ q.2.1 q.2.2 q.1
  · simp only [flow,S,mem_ofPred_eq,dite_eq_left hq,f,ite_eq_left (Nat.find_spec hq).1]
  · simp only [flow,S,mem_ofPred_eq,dite_eq_right hq]

lemma surviving_flow_eq_of_driver_prefix (κ : ℝ) (b c : Driver) (z : ℂ)
    (T : ℝ) (hT : 0 ≤ T)
    (he : ∀ s ∈ Icc 0 T, driverValue b s = driverValue c s) :
    (Surviving κ b z T ↔ Surviving κ c z T) ∧ flow κ b z T = flow κ c z T := by
  have hp (j : ℕ) :
      (1 ≤ j ∧ (j : ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 T)) ↔
      (1 ≤ j ∧ (j : ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ c j z u).im) '' Icc 0 T)) := by
    by_cases hj : 1 ≤ j
    · have hi : (fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 T =
          (fun u : ℝ => (cutoffFlow κ c j z u).im) '' Icc 0 T := by
        apply image_congr
        intro u hu
        rw [cutoffFlow_eq_of_driver_prefix κ b c j hj z T hT he u hu]
      rw [hi]
    · simp only [hj,false_and]
  have hs : Surviving κ b z T ↔ Surviving κ c z T := exists_congr hp
  refine ⟨hs,?_⟩
  by_cases hb : Surviving κ b z T
  · have hc := hs.mp hb
    have hn : Nat.find hb = Nat.find hc := Nat.find_congr' (fun {j} => hp j)
    rw [flow,dite_eq_left hb,flow,dite_eq_left hc,← hn]
    exact cutoffFlow_eq_of_driver_prefix κ b c (Nat.find hb) (Nat.find_spec hb).1
      z T hT he T ⟨hT,le_rfl⟩
  · have hc : ¬Surviving κ c z T := fun hc => hb (hs.mpr hc)
    simp only [flow,dite_eq_right hb,dite_eq_right hc]

lemma surviving_flow_stopDriver (κ : ℝ) (b : Driver) (z : ℂ) (T t : ℝ≥0)
    (ht : t ≤ T) :
    (Surviving κ (stopDriver b T) z t ↔ Surviving κ b z t) ∧
      flow κ (stopDriver b T) z t = flow κ b z t := by
  apply surviving_flow_eq_of_driver_prefix κ _ _ z t t.coe_nonneg
  intro s hs
  simp only [driverValue,stopDriver_apply,
    min_eq_left (Real.toNNReal_le_iff_le_coe.mpr (hs.2.trans (show (t : ℝ) ≤ T from ht)))]

end SLEExactGauge.Target

end

end OAI
