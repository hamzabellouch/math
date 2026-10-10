import OAI.Probability.SLE.Angle.TargetClockIdentification
import OAI.Probability.SLE.Geometry.JointRadiusKernel

namespace OAI

/-! The strict rational infimum in the prescribed construction is the
actual geometric radius stop, with the source time normalization. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

private lemma clock_gt_iff_radius_lt
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ ℓ : ℝ) (T : ℝ≥0) (hz : diskMapInv θ 0 ∈ survivingDomain γ T) :
    ℓ < clock κ θ b 0 (κ*T) ↔ fullRadius G T (diskMapInv θ 0) <
      (2*(diskMapInv θ 0).im)*Real.exp (-(4*ℓ/κ)) := by
  let z := diskMapInv θ 0
  let L := Real.log ((2*z.im)/fullRadius G T z)
  have hz0 := survivingDomain_antitone γ (show 0 ≤ T from zero_le) hz
  have hy : 0 < 2*z.im := mul_pos (by norm_num) hz.1.1
  have he : clock κ θ b 0 (κ*T)=κ*(L/4) := by
    rw [clock_eq_activeRadiusClock κ hκ b U hUc γ G F hw hU θ 0 T hz]
    simp only [Multipoint.activeRadiusClock,Real.toNNReal_coe]
    change κ*((Real.log ((2*z.im)/fullRadius G T z)-
      Real.log ((2*z.im)/fullRadius G 0 z))/4)=κ*(L/4)
    rw [hw.fullRadius_initial hUc z hz0,div_self hy.ne',Real.log_one,sub_zero]
  rw [he,fullRadius_eq_logClock hUc hw z T hz,
    logRadiusClock_logCoordinates hUc hw z T hz,mul_lt_mul_iff_right₀ hy,Real.exp_lt_exp]
  change ℓ < κ*(L/4) ↔ -L < -(4*ℓ/κ)
  rw [neg_lt_neg_iff,div_lt_iff₀ hκ]
  constructor <;> intro h <;> nlinarith

lemma levelTime_eq_radiusLevelTime
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    levelTime κ θ b ℓ=ENNReal.ofReal κ * radiusLevelTime γ G (diskMapInv θ 0) (4*ℓ/κ) := by
  let z := diskMapInv θ 0
  let u := 4*ℓ/κ
  let τ := radiusLevelTime γ G z u
  have hu : 0 ≤ u := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have hκe : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.mpr hκ).ne'
  have hscale (t : ℝ≥0) : ENNReal.ofReal (κ*(t:ℝ))=ENNReal.ofReal κ*(t:ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul hκ.le,ENNReal.ofReal_coe_nnreal]
  unfold levelTime
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · rintro r ⟨q,hq,rfl,hqLive,hqClock⟩
    have hq0 : 0 ≤ (q:ℝ)/κ := div_nonneg (Rat.cast_nonneg.mpr hq.le) hκ.le
    let t : ℝ≥0 := NNReal.mk ((q:ℝ)/κ) hq0
    have ht : (t:ℝ)=(q:ℝ)/κ := rfl
    have htime : κ*(t:ℝ)=(q:ℝ) := by rw [ht,mul_div_cancel₀ _ hκ.ne']
    have htlive : z ∈ survivingDomain γ t := by
      have hh := (surviving_iff_witness_real_time κ hκ b U γ G F hw hU (q:ℝ)
        (Rat.cast_nonneg.mpr hq.le) z).1 hqLive
      simpa only [← ht,Real.toNNReal_coe] using hh
    have hR : fullRadius G t z < (2*z.im)*Real.exp (-u) := by
      apply (clock_gt_iff_radius_lt κ hκ b U hUc γ G F hw hU θ ℓ t htlive).1
      simpa only [htime] using hqClock
    have hτt : τ < (t:ℝ≥0∞) := radiusLevelTime_lt_of_live_radius_lt hUc hw z u hu t htlive hR
    calc
      ENNReal.ofReal κ*τ ≤ ENNReal.ofReal κ*(t:ℝ≥0∞) :=
        mul_le_mul_of_nonneg_left hτt.le (show (0:ℝ≥0∞) ≤ ENNReal.ofReal κ from zero_le)
      _ = ENNReal.ofReal (q:ℝ) := by rw [← hscale t,htime]
  · intro w hwlt
    change ENNReal.ofReal κ*τ<w at hwlt
    have hτfinite : τ < ∞ := by
      by_contra hn
      have htop : τ=∞ := top_le_iff.mp (not_lt.mp hn)
      rw [htop,ENNReal.mul_top hκe] at hwlt
      exact not_lt_of_ge le_top hwlt
    obtain ⟨T,hT,hTR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u hτfinite
    have hτT : τ=(T:ℝ≥0∞) := radiusLevelTime_eq_of_live_level hUc hw z u T hT hTR
    have hTw : ENNReal.ofReal (κ*(T:ℝ))<w := by rwa [hτT,← hscale T] at hwlt
    let V : Set ℝ≥0 := {t | z ∈ survivingDomain γ t ∧ ENNReal.ofReal (κ*(t:ℝ))<w}
    have hVo : IsOpen V := by
      have hLive : IsOpen {t : ℝ≥0 | z ∈ survivingDomain γ t} :=
        source_survival_open.preimage
          (((continuous_const : Continuous (fun _ : ℝ≥0 =>
            (⟨γ,hw.1⟩ : C(ℝ≥0,ℂ)))).prodMk continuous_id).prodMk continuous_const)
      have hc : Continuous (fun t : ℝ≥0 => ENNReal.ofReal (κ*(t:ℝ))) :=
        ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_subtype_val)
      exact hLive.inter (isOpen_lt hc continuous_const)
    obtain ⟨t,hTt,htV⟩ := exists_Ico_subset_of_mem_nhds
      (hVo.mem_nhds (show T ∈ V from ⟨hT,hTw⟩)) (exists_gt T)
    have hTtR : κ*(T:ℝ)<κ*(t:ℝ) := mul_lt_mul_of_pos_left (by exact_mod_cast hTt) hκ
    obtain ⟨q,hTq,hqt⟩ := exists_rat_btwn hTtR
    have hqpos : (0:ℚ)<q := by
      have hh := (mul_nonneg hκ.le T.coe_nonneg).trans_lt hTq
      exact_mod_cast hh
    have hq0 : 0 ≤ (q:ℝ)/κ := div_nonneg (Rat.cast_nonneg.mpr hqpos.le) hκ.le
    let s : ℝ≥0 := NNReal.mk ((q:ℝ)/κ) hq0
    have hs : (s:ℝ)=(q:ℝ)/κ := rfl
    have hTs : T<s := by
      apply NNReal.coe_lt_coe.mp
      rw [hs,lt_div_iff₀ hκ]
      simpa only [mul_comm] using hTq
    have hst : s<t := by
      apply NNReal.coe_lt_coe.mp
      rw [hs,div_lt_iff₀ hκ]
      simpa only [mul_comm] using hqt
    have hVs := htV ⟨hTs.le,hst⟩
    have hsTime : κ*(s:ℝ)=(q:ℝ) := by rw [hs,mul_div_cancel₀ _ hκ.ne']
    have hR : fullRadius G s z < (2*z.im)*Real.exp (-u) := by
      have hh := fullRadius_strictAnti_on_live hUc hw z hTs hVs.1
      rwa [hTR] at hh
    have hqClock : ℓ < clock κ θ b 0 (q:ℝ) := by
      rw [← hsTime]
      exact (clock_gt_iff_radius_lt κ hκ b U hUc γ G F hw hU θ ℓ s hVs.1).2 hR
    refine ⟨ENNReal.ofReal (q:ℝ),⟨q,hqpos,rfl,?_,hqClock⟩,?_⟩
    · rw [← hsTime]
      exact (surviving_iff_witness κ hκ b U γ G F hw hU s z).2 hVs.1
    · simpa only [hsTime] using hVs.2

lemma levelTime_toReal
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (U : ℝ≥0 → ℝ) (hUc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (levelTime κ θ b ℓ).toReal=κ*(radiusLevelTime γ G (diskMapInv θ 0) (4*ℓ/κ)).toReal := by
  rw [levelTime_eq_radiusLevelTime κ hκ b U hUc γ G F hw hU θ ℓ hℓ,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hκ.le]

lemma measurable_levelTime_of_radius_kernel
    {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (hκ : 0 < κ) (b : Ω → Driver) (U : Ω → ℝ≥0 → ℝ)
    (hUc : ∀ ω, Continuous (U ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (U ω) (γ ω) (G ω) (F ω))
    (hU : ∀ ω (s : ℝ), 0 ≤ s → U ω s.toNNReal=driverValue (b ω) (κ*s))
    (θ ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hm : Measurable (fun ω => radiusLevelTime (γ ω) (G ω) (diskMapInv θ 0) (4*ℓ/κ))) :
    Measurable (fun ω => levelTime κ θ (b ω) ℓ) := by
  have he : (fun ω => levelTime κ θ (b ω) ℓ)=
      (fun ω => ENNReal.ofReal κ*radiusLevelTime (γ ω) (G ω) (diskMapInv θ 0) (4*ℓ/κ)) :=
    funext (fun ω => levelTime_eq_radiusLevelTime κ hκ (b ω) (U ω) (hUc ω)
      (γ ω) (G ω) (F ω) (hw ω) (hU ω) θ ℓ hℓ)
  rw [he]
  exact measurable_const.mul hm

end SLEExactGauge.Target

end

end OAI
