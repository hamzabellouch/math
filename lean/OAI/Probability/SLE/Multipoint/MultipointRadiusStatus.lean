import OAI.Probability.SLE.Loewner.ActualRadiusStops
import OAI.Probability.SLE.Multipoint.MultipointLogClockTransport
import OAI.Probability.SLE.Multipoint.MultipointRadiusSwitches

namespace OAI

/-! The literal radius stop is the inverse of the actual increasing radius
clock. Horizon truncation preserves all threshold tests strictly before
its cutoff, including equality at a crossed threshold. -/

noncomputable section
open Set
open scoped NNReal ENNReal

namespace SLEExactGauge

lemma radiusLevelTime_le_iff_clock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) (ht : z ∈ survivingDomain γ t) :
    radiusLevelTime γ G z u ≤ (t : ℝ≥0∞) ↔
      u ≤ logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) := by
  constructor
  · intro hτ
    obtain ⟨s,hs,hsR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u
      (hτ.trans_lt ENNReal.coe_lt_top)
    have hst : s ≤ t := by
      rw [radiusLevelTime_eq_of_live_level hU hw z u s hs hsR] at hτ
      exact_mod_cast hτ
    have hmono := (hw.radius_clock_strictMonoOn hU z t ht).monotoneOn
      (show (s : ℝ) ∈ Icc 0 (t : ℝ) from ⟨s.coe_nonneg,by exact_mod_cast hst⟩)
      (show (t : ℝ) ∈ Icc 0 (t : ℝ) from ⟨t.coe_nonneg,le_rfl⟩)
      (by exact_mod_cast hst)
    have hsclock := (fullRadius_level_iff_logClock hU hw z s hs u).mp hsR
    rw [Real.toNNReal_coe, Real.toNNReal_coe,
      ← logRadiusClock_logCoordinates hU hw z s hs,
      ← logRadiusClock_logCoordinates hU hw z t ht, hsclock] at hmono
    exact hmono
  · intro hc
    have htR := (fullRadius_level_iff_logClock hU hw z t ht
      (logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t))).mpr rfl
    obtain ⟨s,hst,hs,hsR⟩ := live_radius_level_before hU hw z hu hc t ht htR
    rw [radiusLevelTime_eq_of_live_level hU hw z u s hs hsR]
    exact_mod_cast hst

lemma radiusLevelTime_eq_iff_clock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (t : ℝ≥0) (ht : z ∈ survivingDomain γ t) :
    radiusLevelTime γ G z u = (t : ℝ≥0∞) ↔
      logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) = u := by
  constructor
  · intro hτ
    obtain ⟨s,hs,hsR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u
      (by rw [hτ]; exact ENNReal.coe_lt_top)
    have hst : s = t := by
      rw [radiusLevelTime_eq_of_live_level hU hw z u s hs hsR] at hτ
      exact_mod_cast hτ
    subst s
    exact (fullRadius_level_iff_logClock hU hw z t ht u).mp hsR
  · intro hc
    exact radiusLevelTime_eq_of_live_level hU hw z u t ht
      ((fullRadius_level_iff_logClock hU hw z t ht u).mpr hc)

lemma radiusLevelTime_lt_iff_clock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) (ht : z ∈ survivingDomain γ t) :
    radiusLevelTime γ G z u < (t : ℝ≥0∞) ↔
      u < logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) := by
  rw [lt_iff_le_and_ne, radiusLevelTime_le_iff_clock hU hw z u hu t ht]
  constructor
  · rintro ⟨hle,hne⟩
    apply lt_of_le_of_ne hle
    intro he
    exact hne ((radiusLevelTime_eq_iff_clock hU hw z u t ht).mpr he.symm)
  · intro h
    refine ⟨h.le, ?_⟩
    intro he
    exact h.ne' ((radiusLevelTime_eq_iff_clock hU hw z u t ht).mp he)

lemma cutoffStop_reached_before_horizon {Ω : Type*}
    (τ : Ω → WithTop ℝ≥0) (H t : ℝ≥0) (ht : t ≤ H) (ω : Ω) :
    cutoffStop τ (H+1) ω ≤ t ↔ τ ω ≤ (t : WithTop ℝ≥0) := by
  have hHt : ¬ ((H+1 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
    exact_mod_cast (not_le_of_gt (lt_of_le_of_lt ht (lt_add_one H)))
  rw [← WithTop.coe_le_coe, cutoffStop_coe, min_le_iff]
  exact or_iff_left hHt

lemma cutoffStop_strictly_reached_before_horizon {Ω : Type*}
    (τ : Ω → WithTop ℝ≥0) (H t : ℝ≥0) (ht : t ≤ H) (ω : Ω) :
    cutoffStop τ (H+1) ω < t ↔ τ ω < (t : WithTop ℝ≥0) := by
  have hHt : ¬ ((H+1 : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0) := by
    exact_mod_cast (not_lt_of_ge (le_of_lt (lt_of_le_of_lt ht (lt_add_one H))))
  rw [← WithTop.coe_lt_coe, cutoffStop_coe, min_lt_iff]
  exact or_iff_left hHt

lemma cutoffStop_eq_before_horizon {Ω : Type*}
    (τ : Ω → WithTop ℝ≥0) (H t : ℝ≥0) (ht : t ≤ H) (ω : Ω) :
    cutoffStop τ (H+1) ω = t ↔ τ ω = (t : WithTop ℝ≥0) := by
  rw [eq_iff_le_not_lt, cutoffStop_reached_before_horizon τ H t ht ω,
    cutoffStop_strictly_reached_before_horizon τ H t ht ω, eq_iff_le_not_lt]

namespace Multipoint

def sourceClockLevel (κ : ℝ) (z : ℂ) (u : ℝ) : ℝ := κ/4*(u-Real.log z.im)

lemma cutoff_radius_reached_iff
    {Ω : Type*} {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    {κ : ℝ} (hκ : 0 < κ) (z : ℂ) (u : ℝ) (hu : 0 ≤ u)
    (H t : ℝ≥0) (htH : t ≤ H) (ht : z ∈ survivingDomain γ t) (ω : Ω) :
    cutoffStop (fun _ : Ω => (radiusLevelTime γ G z u : WithTop ℝ≥0)) (H+1) ω ≤ t ↔
      sourceClockLevel κ z u ≤ logFactorClock κ (logLoewnerCoordinates G z t) := by
  have hc : (radiusLevelTime γ G z u : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) ↔
      u ≤ logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) := by
    constructor
    · intro h
      apply (radiusLevelTime_le_iff_clock hU hw z u hu t ht).mp
      exact_mod_cast h
    · intro h
      have h' := (radiusLevelTime_le_iff_clock hU hw z u hu t ht).mpr h
      exact_mod_cast h'
  have hs : (u ≤ logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t)) ↔
      sourceClockLevel κ z u ≤ logFactorClock κ (logLoewnerCoordinates G z t) := by
    rw [logFactorClock_eq_logRadiusClock κ (Real.log z.im)]
    unfold sourceClockLevel
    rw [mul_le_mul_iff_right₀ (div_pos hκ (by norm_num)), sub_le_sub_iff_right]
  exact (cutoffStop_reached_before_horizon
    (fun _ : Ω => (radiusLevelTime γ G z u : WithTop ℝ≥0)) H t htH ω).trans (hc.trans hs)

lemma cutoff_radius_strictly_reached_iff
    {Ω : Type*} {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    {κ : ℝ} (hκ : 0 < κ) (z : ℂ) (u : ℝ) (hu : 0 ≤ u)
    (H t : ℝ≥0) (htH : t ≤ H) (ht : z ∈ survivingDomain γ t) (ω : Ω) :
    cutoffStop (fun _ : Ω => (radiusLevelTime γ G z u : WithTop ℝ≥0)) (H+1) ω < t ↔
      sourceClockLevel κ z u < logFactorClock κ (logLoewnerCoordinates G z t) := by
  have hc : (radiusLevelTime γ G z u : WithTop ℝ≥0) < (t : WithTop ℝ≥0) ↔
      u < logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) := by
    constructor
    · intro h
      apply (radiusLevelTime_lt_iff_clock hU hw z u hu t ht).mp
      exact_mod_cast h
    · intro h
      have h' := (radiusLevelTime_lt_iff_clock hU hw z u hu t ht).mpr h
      exact_mod_cast h'
  have hs : (u < logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t)) ↔
      sourceClockLevel κ z u < logFactorClock κ (logLoewnerCoordinates G z t) := by
    rw [logFactorClock_eq_logRadiusClock κ (Real.log z.im)]
    unfold sourceClockLevel
    rw [mul_lt_mul_iff_right₀ (div_pos hκ (by norm_num)), sub_lt_sub_iff_right]
  exact (cutoffStop_strictly_reached_before_horizon
    (fun _ : Ω => (radiusLevelTime γ G z u : WithTop ℝ≥0)) H t htH ω).trans (hc.trans hs)

lemma cutoff_radius_eq_iff
    {Ω : Type*} {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    {κ : ℝ} (hκ : 0 < κ) (z : ℂ) (u : ℝ)
    (H t : ℝ≥0) (htH : t ≤ H) (ht : z ∈ survivingDomain γ t) (ω : Ω) :
    cutoffStop (fun _ : Ω => (radiusLevelTime γ G z u : WithTop ℝ≥0)) (H+1) ω = t ↔
      logFactorClock κ (logLoewnerCoordinates G z t) = sourceClockLevel κ z u := by
  have hc : (radiusLevelTime γ G z u : WithTop ℝ≥0) = (t : WithTop ℝ≥0) ↔
      logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) = u := by
    constructor
    · intro h
      apply (radiusLevelTime_eq_iff_clock hU hw z u t ht).mp
      exact_mod_cast h
    · intro h
      have h' := (radiusLevelTime_eq_iff_clock hU hw z u t ht).mpr h
      exact_mod_cast h'
  have hs : (logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) = u) ↔
      logFactorClock κ (logLoewnerCoordinates G z t) = sourceClockLevel κ z u := by
    rw [logFactorClock_eq_logRadiusClock κ (Real.log z.im)]
    unfold sourceClockLevel
    rw [mul_right_inj' (div_pos hκ (by norm_num)).ne', sub_left_inj]
  exact (cutoffStop_eq_before_horizon
    (fun _ : Ω => (radiusLevelTime γ G z u : WithTop ℝ≥0)) H t htH ω).trans (hc.trans hs)

/-- The three concrete radius switches give exactly the source branch
thresholds, also after truncation at `H + 1`. -/
theorem cutoff_radius_factor_thresholds
    {Ω : Type*} {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    {κ : ℝ} (hκ : 0 < κ) (z : ℂ) (u₀ u₂ : ℝ) (h₀ : 0 ≤ u₀) (h₂ : 0 ≤ u₂)
    (H t : ℝ≥0) (htH : t ≤ H) (ht : z ∈ survivingDomain γ t) (ω : Ω) :
    let τ := fun u => cutoffStop (fun _ : Ω => (radiusLevelTime γ G z u : WithTop ℝ≥0)) (H+1) ω
    let v := logFactorClock κ (logLoewnerCoordinates G z t)-sourceClockLevel κ z u₀
    let V := κ/4*(u₂-u₀)
    (τ u₀ ≤ t ↔ 0 ≤ v) ∧
    (τ ((u₀+u₂)/2) ≤ t ↔ V/2 ≤ v) ∧
    (τ u₂ ≤ t ↔ V ≤ v) ∧
    (τ u₀ = t → v = 0) ∧
    (τ ((u₀+u₂)/2) = t → v = V/2) ∧
    (τ u₂ = t → v = V) := by
  dsimp only
  have hm : 0 ≤ (u₀+u₂)/2 := by positivity
  have hstart := cutoff_radius_reached_iff hU hw hκ z u₀ h₀ H t htH ht ω
  have hmid := cutoff_radius_reached_iff hU hw hκ z ((u₀+u₂)/2) hm H t htH ht ω
  have hend := cutoff_radius_reached_iff hU hw hκ z u₂ h₂ H t htH ht ω
  have hmidlevel : sourceClockLevel κ z ((u₀+u₂)/2) =
      sourceClockLevel κ z u₀ + (κ/4*(u₂-u₀))/2 := by
    unfold sourceClockLevel
    ring
  have hendlevel : sourceClockLevel κ z u₂ =
      sourceClockLevel κ z u₀ + κ/4*(u₂-u₀) := by
    unfold sourceClockLevel
    ring
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact hstart.trans (sub_nonneg.symm)
  · rw [hmid,hmidlevel]
    constructor <;> intro h <;> linarith
  · rw [hend,hendlevel]
    constructor <;> intro h <;> linarith
  · intro h
    have he := (cutoff_radius_eq_iff hU hw hκ z u₀ H t htH ht ω).mp h
    exact sub_eq_zero.mpr he
  · intro h
    have he := (cutoff_radius_eq_iff hU hw hκ z ((u₀+u₂)/2) H t htH ht ω).mp h
    rw [hmidlevel] at he
    linarith
  · intro h
    have he := (cutoff_radius_eq_iff hU hw hκ z u₂ H t htH ht ω).mp h
    rw [hendlevel] at he
    linarith

end Multipoint

/-- At the activation clock chosen from the physical initial radius, the
physical conformal radius is exactly the prescribed activation radius. -/
theorem IsCapacityTwoWitness.physical_radius_at_activation
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (J : ℂ → ℂ) (z : ℂ) (R b : ℝ) (hR : 0 < R) (hb : 0 < b)
    (hRdef : R = 2*z.im*‖deriv J z‖)
    (t : ℝ≥0) (ht : z ∈ survivingDomain γ t)
    (hclock : logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) =
      Real.log (R/b)) :
    physicalConformalRadius J G t z = b := by
  have hradius := (fullRadius_level_iff_logClock hU hw z t ht (Real.log (R/b))).mpr hclock
  have hexp : Real.exp (-Real.log (R/b)) = b/R := by
    rw [Real.exp_neg, Real.exp_log (div_pos hR hb)]
    field_simp [hR.ne',hb.ne']
  have hcoef : ‖deriv J z‖*(2*z.im) = R := by rw [hRdef]; ring
  unfold physicalConformalRadius
  rw [hradius,hexp,← mul_assoc,hcoef]
  field_simp [hR.ne']

end SLEExactGauge

end

end OAI
