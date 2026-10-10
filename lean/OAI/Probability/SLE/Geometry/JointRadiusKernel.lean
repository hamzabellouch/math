import OAI.Probability.SLE.Loewner.ActualRadiusStops
import OAI.Probability.SLE.ChartMeasurability
import OAI.Probability.SLE.InverseMoments

namespace OAI

/-! Jointly measurable geometric radius and radius-level kernels, constructed
from the clipped Loewner equations. Agreement holds simultaneously at every
marked point and nonnegative radius level on each actual capacity witness. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Classical
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma fullRadius_strictAnti_on_live
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) {s t : ℝ≥0} (hst : s < t)
    (ht : z ∈ survivingDomain γ t) :
    fullRadius G t z < fullRadius G s z := by
  have hs := survivingDomain_antitone γ hst.le ht
  have hc := hw.radius_clock_strictMonoOn hU z t ht
    (show (s : ℝ) ∈ Icc 0 (t : ℝ) from ⟨s.coe_nonneg, by exact_mod_cast hst.le⟩)
    (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.coe_nonneg, le_rfl⟩)
    (by exact_mod_cast hst)
  simp only [Real.toNNReal_coe] at hc
  rw [fullRadius_eq_logClock hU hw z t ht, fullRadius_eq_logClock hU hw z s hs,
    logRadiusClock_logCoordinates hU hw z t ht,
    logRadiusClock_logCoordinates hU hw z s hs]
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (neg_lt_neg hc))
    (mul_pos (by norm_num) ht.1.1)

lemma radiusLevelTime_lt_of_live_radius_lt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0)
    (ht : z ∈ survivingDomain γ t)
    (hR : fullRadius G t z < (2 * z.im) * Real.exp (-u)) :
    radiusLevelTime γ G z u < (t : ℝ≥0∞) := by
  obtain ⟨s, hs, hsR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u
    (radiusLevelTime_finite_of_live_radius_lt hU hw z u hu t ht hR)
  have hst : s < t := by
    by_contra hn
    have hts := le_of_not_gt hn
    rcases hts.eq_or_lt with he | he
    · subst s
      exact (lt_irrefl _ (hsR ▸ hR))
    · have hh := fullRadius_strictAnti_on_live hU hw z he hs
      rw [hsR] at hh
      exact (not_lt_of_ge hh.le) hR
  rw [radiusLevelTime_eq_of_live_level hU hw z u s hs hsR]
  exact_mod_cast hst

/-- A radius level is before `x` exactly when a time in one fixed countable
dense set is before `x`, still live, and strictly beyond that radius level. -/
lemma radiusLevelTime_lt_iff_dense
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (x : ℝ≥0∞) :
    radiusLevelTime γ G z u < x ↔ ∃ n : ℕ,
      (denseSeq ℝ≥0 n : ℝ≥0∞) < x ∧
      z ∈ survivingDomain γ (denseSeq ℝ≥0 n) ∧
      fullRadius G (denseSeq ℝ≥0 n) z < (2 * z.im) * Real.exp (-u) := by
  constructor
  · intro hx
    obtain ⟨T, hT, hTR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u
      (hx.trans_le le_top)
    have hTx : (T : ℝ≥0∞) < x := by
      rwa [radiusLevelTime_eq_of_live_level hU hw z u T hT hTR] at hx
    let V : Set ℝ≥0 := {q | z ∈ survivingDomain γ q ∧ (q : ℝ≥0∞) < x}
    have hVo : IsOpen V := by
      have hLive : IsOpen {q : ℝ≥0 | z ∈ survivingDomain γ q} :=
        source_survival_open.preimage
        (((continuous_const : Continuous (fun _ : ℝ≥0 =>
          (⟨γ, hw.1⟩ : C(ℝ≥0, ℂ)))).prodMk continuous_id).prodMk continuous_const)
      exact hLive.inter (isOpen_lt ENNReal.continuous_coe continuous_const)
    obtain ⟨b, hTb, hb⟩ := exists_Ico_subset_of_mem_nhds
      (hVo.mem_nhds (show T ∈ V from ⟨hT, hTx⟩)) (exists_gt T)
    obtain ⟨n, hn⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo
      (nonempty_Ioo.mpr hTb)
    have hV := hb (show denseSeq ℝ≥0 n ∈ Ico T b from ⟨hn.1.le, hn.2⟩)
    refine ⟨n, hV.2, hV.1, ?_⟩
    have hr := fullRadius_strictAnti_on_live hU hw z hn.1 hV.1
    rwa [hTR] at hr
  · rintro ⟨n, hnx, hn, hnR⟩
    exact (radiusLevelTime_lt_of_live_radius_lt hU hw z u hu _ hn hnR).trans hnx

namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

def jointLive (p : ℝ≥0 × (ℂ × Ω)) : Prop := ∃ n : ℕ, c.valid n p.1 p.2.1 p.2.2

lemma jointLive_measurable : MeasurableSet {p | c.jointLive p} := by
  simpa only [jointLive, ofPred_exists] using
    MeasurableSet.iUnion (fun n => c.valid_measurable n)

lemma jointLive_iff {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F) (t : ℝ≥0) (z : ℂ) :
    c.jointLive (t, z, ω) ↔ z ∈ survivingDomain γ t := by
  constructor
  · rintro ⟨n, hn⟩
    exact c.live_of_valid ω hUc hw n t z hn
  · intro hz
    obtain ⟨n, hn⟩ := (c.eventually_valid_agrees ω hUc hw t z hz).exists
    exact ⟨n, hn.1⟩

def radiusApprox (n : ℕ) (p : ℝ≥0 × (ℂ × Ω)) : ℝ :=
  if c.valid n p.1 p.2.1 p.2.2 then
    (2 * p.2.1.im) * Real.exp (-logRadiusClock (Real.log p.2.1.im) (c.Q n p.1 p.2))
  else 0

lemma radiusApprox_measurable (n : ℕ) : Measurable (c.radiusApprox n) := by
  have hz : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => p.2.1.im) :=
    Complex.measurable_im.comp (measurable_fst.comp measurable_snd)
  have hQ := (c.measurable n).comp
    ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  apply Measurable.ite (c.valid_measurable n) _ measurable_const
  exact (hz.const_mul 2).mul (Real.continuous_exp.measurable.comp
    (((Real.measurable_log.comp hz).sub (Complex.measurable_im.comp hQ.fst)).add hQ.snd).neg)

def jointRadius (p : ℝ≥0 × (ℂ × Ω)) : ℝ :=
  limUnder atTop (fun n => c.radiusApprox n p)

lemma jointRadius_measurable : Measurable c.jointRadius :=
  (StronglyMeasurable.limUnder (fun n =>
    (c.radiusApprox_measurable n).stronglyMeasurable)).measurable

lemma jointRadius_eq {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F) (t : ℝ≥0) (z : ℂ) :
    c.jointRadius (t, z, ω) =
      if z ∈ survivingDomain γ t then fullRadius G t z else 0 := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  by_cases hz : z ∈ survivingDomain γ t
  · filter_upwards [c.eventually_valid_agrees ω hUc hw t z hz] with n hn
    rw [radiusApprox, ite_eq_left hn.1, hn.2, ite_eq_left hz]
    exact (fullRadius_eq_logClock hUc hw z t hz).symm
  · filter_upwards [] with n
    have hn : ¬ c.valid n t z ω := fun hv => hz (c.live_of_valid ω hUc hw n t z hv)
    simp only [radiusApprox, ite_eq_right hn, ite_eq_right hz]

def jointRadiusLevel (p : ℝ × (ℂ × Ω)) : ℝ≥0∞ :=
  ⨅ n : ℕ, if c.jointLive (denseSeq ℝ≥0 n, p.2) ∧
    c.jointRadius (denseSeq ℝ≥0 n, p.2) < (2 * p.2.1.im) * Real.exp (-p.1)
    then (denseSeq ℝ≥0 n : ℝ≥0∞) else ∞

lemma jointRadiusLevel_measurable : Measurable c.jointRadiusLevel := by
  apply Measurable.iInf
  intro n
  have hp : Measurable (fun p : ℝ × (ℂ × Ω) => (denseSeq ℝ≥0 n, p.2)) :=
    measurable_const.prodMk measurable_snd
  have hz : Measurable (fun p : ℝ × (ℂ × Ω) => p.2.1.im) :=
    Complex.measurable_im.comp (measurable_fst.comp measurable_snd)
  exact Measurable.ite ((c.jointLive_measurable.preimage hp).inter
    (measurableSet_lt (c.jointRadius_measurable.comp hp)
      ((hz.const_mul 2).mul (Real.continuous_exp.measurable.comp measurable_fst.neg))))
    measurable_const measurable_const

lemma jointRadiusLevel_eq {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (u : ℝ) (hu : 0 ≤ u) (z : ℂ) :
    c.jointRadiusLevel (u, z, ω) = radiusLevelTime γ G z u := by
  apply eq_of_forall_gt_iff
  intro x
  rw [jointRadiusLevel, iInf_lt_iff, radiusLevelTime_lt_iff_dense hUc hw z u hu x]
  apply exists_congr
  intro n
  have hLive := c.jointLive_iff ω hUc hw (denseSeq ℝ≥0 n) z
  have hRad := c.jointRadius_eq ω hUc hw (denseSeq ℝ≥0 n) z
  by_cases hz : z ∈ survivingDomain γ (denseSeq ℝ≥0 n)
  · rw [ite_eq_left hz] at hRad
    by_cases hr : fullRadius G (denseSeq ℝ≥0 n) z < (2 * z.im) * Real.exp (-u)
    · simp [hLive, hz, hRad, hr]
    · simp [hLive, hz, hRad, hr]
  · simp [hLive, hz]

end SpatialClippedFamily

/-- The kernels agree on one probability-one set simultaneously for all
points, all times, and every nonnegative radius level. Consequently random
measurable marked states may be substituted without changing that null set. -/
theorem exists_joint_radius_and_level
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (U : ℝ≥0 → Ω → ℝ)
    (hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω)) :
    ∃ R : ℝ≥0 × (ℂ × Ω) → ℝ, ∃ τ : ℝ × (ℂ × Ω) → ℝ≥0∞,
      Measurable R ∧ Measurable τ ∧ ∀ᵐ ω ∂P,
        (∀ t z, R (t, z, ω) =
          if z ∈ survivingDomain (γ ω) t then fullRadius (G ω) t z else 0) ∧
        (∀ u, 0 ≤ u → ∀ z, τ (u, z, ω) = radiusLevelTime (γ ω) (G ω) z u) := by
  let c := spatialClippedFamily U hUm hUc
  refine ⟨c.jointRadius, c.jointRadiusLevel, c.jointRadius_measurable,
    c.jointRadiusLevel_measurable, ?_⟩
  filter_upwards [hw] with ω hω
  exact ⟨fun t z => c.jointRadius_eq ω (hUc ω) hω t z,
    fun u hu z => c.jointRadiusLevel_eq ω (hUc ω) hω u hu z⟩

end SLEExactGauge

end

end OAI
