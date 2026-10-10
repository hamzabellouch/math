import OAI.Probability.SLE.Loewner.ActualRadiusStopsRegular
import OAI.Probability.SLE.Angle.ActualAngleWarmup

namespace OAI

/-! The good-angle event at an actual radius level belongs to that literal
stopping time's past. Infinite stopping times are excluded explicitly.
Measurability follows by finite cutoff exhaustion of the stopped chart. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

/-- The stopped marked state at a finite extended stopping time. -/
def extendedMarkedGood {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (σ : Ω → WithTop ℝ≥0) (z : ℂ) (s : ℝ) : Set Ω :=
  {ω | σ ω ≠ ⊤ ∧ ω ∈ stoppedMarkedGood κ B γ G (fun ω => (σ ω).untopD 0) z s}

lemma stoppedMarkedGood_time_congr
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (τ₁ τ₂ : Ω → ℝ≥0) (z : ℂ) (s : ℝ) (ω : Ω) (he : τ₁ ω = τ₂ ω) :
    ω ∈ stoppedMarkedGood κ B γ G τ₁ z s ↔
      ω ∈ stoppedMarkedGood κ B γ G τ₂ z s := by
  classical
  exact Iff.of_eq (congrArg (fun t : ℝ≥0 => z ∈ survivingDomain (γ ω) t ∧
    s ≤ (unitMarkedState ((if z ∈ survivingDomain (γ ω) t then G ω t z else 0) -
      (Real.sqrt κ * B t ω : ℝ))).im) he)

lemma extendedMarkedGood_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (σ : Ω → WithTop ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) σ)
    (z : ℂ) (s : ℝ) :
    MeasurableSet[hσ.measurableSpace] (extendedMarkedGood κ B γ G σ z s) := by
  let E (n : ℕ) := stoppedMarkedGood κ B γ G (cutoffStop σ (n : ℝ≥0)) z s ∩
    {ω | σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}
  have hE (n : ℕ) : MeasurableSet[hσ.measurableSpace] (E n) := by
    have hcut := cutoffStop_stopping _ σ hσ (n : ℝ≥0)
    have hpast := hcut.measurableSpace_mono hσ (fun ω =>
      (le_of_eq (cutoffStop_coe σ (n : ℝ≥0) ω)).trans (min_le_left _ _))
    exact (hpast _ (source_stoppedMarkedGood_measurable B hm hc κ γ G F hw
      (cutoffStop σ (n : ℝ≥0)) hcut z s)).inter (hσ.measurableSet_le' (n : ℝ≥0))
  have he : extendedMarkedGood κ B γ G σ z s = ⋃ n, E n := by
    ext ω
    constructor
    · rintro ⟨hf, hg⟩
      lift σ ω to ℝ≥0 using hf with t ht
      obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
      have hle : σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
        rw [← ht]
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast hn)
      apply mem_iUnion.mpr
      refine ⟨n, ?_, hle⟩
      exact (stoppedMarkedGood_time_congr κ B γ G (cutoffStop σ (n : ℝ≥0))
        (fun ω => (σ ω).untopD 0) z s ω (cutoffStop_eq_on_success σ _ ω hle)).mpr hg
    · intro hg
      obtain ⟨n, hn, hle⟩ := mem_iUnion.mp hg
      refine ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hle, ?_⟩
      exact (stoppedMarkedGood_time_congr κ B γ G (cutoffStop σ (n : ℝ≥0))
        (fun ω => (σ ω).untopD 0) z s ω (cutoffStop_eq_on_success σ _ ω hle)).mp hn
  rw [he]
  exact MeasurableSet.iUnion hE

lemma extendedMarkedGood_eq_actual_angle
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (σ : Ω → WithTop ℝ≥0) (z : ℂ) (s : ℝ) :
    extendedMarkedGood κ B γ G σ z s =
      {ω | σ ω ≠ ⊤ ∧ z ∈ survivingDomain (γ ω) ((σ ω).untopD 0) ∧
        s ≤ Real.sin (Complex.arg (G ω ((σ ω).untopD 0) z -
          (Real.sqrt κ * B ((σ ω).untopD 0) ω : ℝ)))} := by
  ext ω
  change (σ ω ≠ ⊤ ∧ z ∈ survivingDomain (γ ω) ((σ ω).untopD 0) ∧ _) ↔ _
  simp only [mem_ofPred_eq]
  by_cases hl : z ∈ survivingDomain (γ ω) ((σ ω).untopD 0)
  · rw [stoppedMarkedUnit_im_on_live B κ γ G (fun ω => (σ ω).untopD 0) z ω hl]
  · simp only [hl, false_and, and_false]

lemma canonical_good_angle_eq_extendedMarkedGood
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (u s : ℝ) (hu : 0 ≤ u) :
    {ω | canonicalRadiusLevel κ (u, z, sourceDriverPath B hc ω) < ∞ ∧
      s ≤ canonicalStoppedSine κ (u, z, sourceDriverPath B hc ω)} =
      extendedMarkedGood κ B γ G
        (fun ω => (radiusLevelTime (γ ω) (G ω) z u : WithTop ℝ≥0)) z s := by
  rw [canonical_good_angle_source_eq κ B hc γ G F hw z u s hu]
  rw [extendedMarkedGood_eq_actual_angle κ B γ G
    (fun ω => (radiusLevelTime (γ ω) (G ω) z u : WithTop ℝ≥0)) z s]
  ext ω
  simp only [mem_ofPred_eq]
  by_cases hf : radiusLevelTime (γ ω) (G ω) z u < ∞
  · obtain ⟨T, hT, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top (γ ω) (G ω) z u hf
    have he := radiusLevelTime_eq_of_live_level ((hc ω).const_mul _) (hw ω) z u T hT hR
    rw [he]
    change ((T : ℝ≥0∞) < ∞ ∧
      s ≤ Real.sin (Complex.arg (G ω (T : ℝ≥0∞).toNNReal z -
        (Real.sqrt κ * B (T : ℝ≥0∞).toNNReal ω : ℝ)))) ↔
      ((T : WithTop ℝ≥0) ≠ ⊤ ∧ z ∈ survivingDomain (γ ω) ((T : WithTop ℝ≥0).untopD 0) ∧
        s ≤ Real.sin (Complex.arg (G ω ((T : WithTop ℝ≥0).untopD 0) z -
          (Real.sqrt κ * B ((T : WithTop ℝ≥0).untopD 0) ω : ℝ))))
    simp only [ENNReal.coe_lt_top, ENNReal.toNNReal_coe,
      WithTop.untopD_coe, hT, true_and]
    constructor
    · intro hs
      exact ⟨WithTop.coe_ne_top, hs⟩
    · exact fun h => h.2
  · have he : radiusLevelTime (γ ω) (G ω) z u = ∞ := not_lt_top_iff.mp hf
    simp only [he, lt_self_iff_false, false_and]
    constructor
    · exact False.elim
    · intro h
      exact h.1 rfl

/-- The jointly measurable canonical angle event also belongs to the
literal actual radius stop's past. -/
theorem canonical_good_angle_measurable_at_radius
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u s : ℝ) (hu : 0 ≤ u) :
    MeasurableSet[(actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8
      γ G F hw z hz u hu).measurableSpace]
      {ω | canonicalRadiusLevel κ (u, z, sourceDriverPath B hc ω) < ∞ ∧
        s ≤ canonicalStoppedSine κ (u, z, sourceDriverPath B hc ω)} := by
  rw [canonical_good_angle_eq_extendedMarkedGood κ B hc γ G F hw z u s hu]
  exact extendedMarkedGood_measurable B hm hc κ γ G F hw _
    (actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u hu) z s

/-- The same stopped-past measurability for the literal geometric angle. -/
theorem actual_good_angle_measurable_at_radius
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u s : ℝ) (hu : 0 ≤ u) :
    MeasurableSet[(actual_radiusLevelTime_stopping hB hm hBm hc hB0 κ hκ hκ8
      γ G F hw z hz u hu).measurableSpace]
      {ω | radiusLevelTime (γ ω) (G ω) z u < ∞ ∧
        s ≤ Real.sin (Complex.arg (G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z -
          (Real.sqrt κ * B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω : ℝ)))} := by
  rw [← canonical_good_angle_source_eq κ B hc γ G F hw z u s hu]
  exact canonical_good_angle_measurable_at_radius hB hm hBm hc hB0 κ hκ hκ8 γ G F hw z hz u s hu

end SLEExactGauge

end

end OAI
