import Mathlib
import OAI.Probability.SLELocalization.FiniteTimeMass
import OAI.Probability.SLELocalization.MeshExponents
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Retained First Moment estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteClock

lemma finiteCenteredPhysicalTime_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (Y s ε : ℝ) (hY : 0 < Y) (hs : 0 < s) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, z ∈ halfPlane → z.im ≤ Y →
      s ≤ (z.im/‖z‖)^(8/κ-1) → ∀ u : ℝ, 1 ≤ u →
      finiteCenteredMeasure κ P B γ g z u
        {sample | ENNReal.ofReal T < firstLiveRadiusStop (γ sample) (g sample) z u} <
        ENNReal.ofReal ε := by
  obtain ⟨C,hC,hbound⟩ := radiusApproachBound κ hκ
  let C' := C+s⁻¹
  have hC' : 0 < C' := by dsimp only [C']; positivity
  have hr : Real.exp (-(8/κ-1)/8) < 1 := Real.exp_lt_one_iff.2 (by have := exponent_pos hκ; linarith)
  let D := C'*Real.exp (codimension κ)/(1-Real.exp (-(8/κ-1)/8))
  have hD : 0 < D := by dsimp only [D]; positivity
  obtain ⟨δ,hδ,hsmall⟩ := exists_small_floor (exponent_pos hκ) hD hε
  refine ⟨Y^2/(2*δ^4),by positivity,?_⟩
  intro z hz hzy hzs u hu
  have hS : 0 < (z.im/‖z‖)^(8/κ-1) := hs.trans_le hzs
  have hrad (n : ℕ) : P {sample | firstLiveRadiusStop (γ sample) (g sample) z n ≠ (⊤ : ℝ≥0∞)} ≤
      ENNReal.ofReal (C'*Real.exp (-codimension κ*n)*(z.im/‖z‖)^(8/κ-1)) := by
    cases n with
    | zero =>
      simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]
      apply (prob_le_one).trans
      apply ENNReal.one_le_ofReal.2
      have hmul := mul_le_mul_of_nonneg_left hzs (inv_nonneg.2 hs.le)
      rw [inv_mul_cancel₀ hs.ne'] at hmul
      dsimp only [C']
      rw [add_mul]
      linarith [mul_pos hC hS]
    | succ n =>
      simp only [Nat.cast_add,Nat.cast_one]
      apply (hbound P B hB γ g f hγ hmaps z hz (n+1) (by norm_num)).trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (inv_nonneg.2 hs.le))
          (Real.exp_pos _).le) hS.le
  have hbad : finiteCenteredMeasure κ P B γ g z u (bad κ B γ g z δ u) ≤
      ENNReal.ofReal (D*δ^(8/κ-1)) := by
    apply (measure_iUnion_le _).trans
    apply (ENNReal.tsum_le_tsum (fun n => block_bound κ hκ B hB γ g f hγ hmaps z hz C' hC' hrad δ hδ u n)).trans_eq
    exact geometric_blocks κ C' δ hκ hC' hδ
  have hu0 : 0 < u := by linarith
  let Q := finiteCenteredMeasure κ P B γ g z u
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hhit : ∀ᵐ sample ∂Q, firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞) := by
    change ∀ᵐ sample ∂P.withDensity _,_
    rw [ae_withDensity_iff' ((finiteStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz u hu0).div_const _)]
    exact Filter.Eventually.of_forall (fun sample hn ht => hn (by simp only [finiteStoppedDensity,ht,ite_true,ENNReal.zero_div]))
  have hsub : {sample | ENNReal.ofReal (Y^2/(2*δ^4)) <
      firstLiveRadiusStop (γ sample) (g sample) z u} ≤ᵐ[Q] bad κ B γ g z δ u := by
    filter_upwards [hQP.ae_le hmaps,hQP.ae_le hB.cont,hhit] with sample hm hc hh hx
    by_contra hn
    have hg : ∀ q : ℚ, 0 < (q:ℝ) → (q:ℝ) ≤ u →
        finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z q ∉ Ioo 0 (threshold κ z δ q) := by
      intro q hq hqu hbad
      exact hn (mem_bad_of_rational κ B γ g z δ u q hq hqu hbad)
    have ht := good_physical_clock (κ := κ) (B := fun t => B t sample) (γ := γ sample)
      (g := g sample) (f := f sample) hκ hm hc hz hδ hu0 hh hg
    have hy : 0 < z.im := hz
    have htY : z.im^2/(2*δ^4) ≤ Y^2/(2*δ^4) :=
      div_le_div_of_nonneg_right (sq_le_sq₀ hy.le hY.le |>.2 hzy) (by positivity)
    exact not_lt_of_ge (ht.trans (ENNReal.ofReal_le_ofReal htY)) hx
  exact (measure_mono_ae hsub).trans_lt
    (hbad.trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.2 hsmall))

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma uniformFiniteTimePhysicalDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (Y s : ℝ) (hY : 0 < Y) (hs : 0 < s) :
    ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, z ∈ halfPlane → z.im ≤ Y →
      s ≤ (z.im/‖z‖)^(8/κ-1) → ∀ e : ℝ, 0 < e → e < z.im →
      ENNReal.ofReal (((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))/2) ≤
        ∫⁻ sample in {sample | firstLiveDistanceStop (γ sample) z e ≤ ENNReal.ofReal T},
          physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e ∂P := by
  classical
  obtain ⟨T,hT,hclock⟩ := finiteCenteredPhysicalTime_uniform κ hκ B hB γ g f hγ hmaps
    Y s (1/2) hY hs (by norm_num)
  refine ⟨T,hT,?_⟩
  intro z hz hzy hzs e he hes
  let m := (2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)
  let M := ENNReal.ofReal m
  have hm : 0 < m := localizationInitialGreen_pos κ hz
  have hM0 : M ≠ 0 := (ENNReal.ofReal_pos.2 hm).ne'
  have hMtop : M ≠ ⊤ := ENNReal.ofReal_ne_top
  let S : ℝ≥0 := ⟨T,hT.le⟩
  have hS : (S : ℝ≥0∞) = ENNReal.ofReal T := by
    change (S : ℝ≥0∞) = ENNReal.ofReal (S : ℝ)
    exact ENNReal.ofReal_coe_nnreal.symm
  let E := PhysicalPast.avoids κ B z e S
  let A := {sample | firstLiveDistanceStop (γ sample) z e ≤ (S:ℝ≥0∞)}
  let D := fun sample => physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e
  have hE : NullMeasurableSet E P := PhysicalPast.avoids_nullMeasurable κ hB z e S
  have hA : NullMeasurableSet A P := physical_early_nullMeasurable κ hκ B hB γ g f hmaps z hz e he hes S
  have hD : AEMeasurable D P := physicalStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz e he hes
  obtain ⟨u,hu,hr⟩ : ∃ u : ℝ, 1 < u ∧ (2*z.im)*Real.exp (-u) < e/4 := by
    have hl : Tendsto (fun u : ℝ => (2*z.im)*Real.exp (-u)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
    exact ((eventually_gt_atTop 1).and (hl.eventually (gt_mem_nhds (by linarith : 0 < e/4)))).exists
  have hu0 : 0 < u := by linarith
  let Q := finiteCenteredMeasure κ P B γ g z u
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hhit : ∀ᵐ sample ∂Q, firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞) := by
    change ∀ᵐ sample ∂P.withDensity _,_
    rw [ae_withDensity_iff' ((finiteStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz u hu0).div_const _)]
    exact Filter.Eventually.of_forall (fun sample hn ht => hn (by simp only [finiteStoppedDensity,ht,ite_true,ENNReal.zero_div]))
  have hsub : E ≤ᵐ[Q] {sample | (S:ℝ≥0∞) < firstLiveRadiusStop (γ sample) (g sample) z u} := by
    filter_upwards [hQP.ae_le hmaps,hQP.ae_le hB.cont,hhit] with sample hmaps hc hhit hmem
    have hpr := physical_before_deep_radius hmaps
      ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) he hes hr hhit
    have hfp : firstLiveDistanceStop (γ sample) z e ≠ (⊤ : ℝ≥0∞) := ne_top_of_lt hpr
    exact ((physical_avoidance_at_finite_hit κ B sample hmaps hc z e S hfp).1 hmem).trans hpr
  have hQE : Q E ≤ ENNReal.ofReal (1/2) := by
    apply (measure_mono_ae hsub).trans
    simpa only [hS] using (hclock z hz hzy hzs u hu.le).le
  have hid : (∫⁻ sample in E, D sample ∂P) = M*Q E := by
    rw [physical_radial_avoidance_identity κ hκ B hB γ g f hmaps z hz u hu0 e he hes hr S]
    rw [show Q E = ∫⁻ sample in E, finiteStoppedDensity κ (fun t => B t sample)
        (γ sample) (g sample) z u / M ∂P from withDensity_apply₀ _ hE]
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hM0),← mul_assoc,ENNReal.mul_inv_cancel hM0 hMtop,one_mul]
  have hhalf : M*ENNReal.ofReal (1/2) = ENNReal.ofReal (m/2) := by
    rw [← ENNReal.ofReal_mul hm.le]
    congr 1
    ring
  have htail : (∫⁻ sample in E, D sample ∂P) ≤ ENNReal.ofReal (m/2) := by
    rw [hid,← hhalf]
    exact mul_le_mul' le_rfl hQE
  have hi : Eᶜ.indicator D =ᵐ[P] A.indicator D := by
    filter_upwards [hmaps,hB.cont] with sample hm hc
    by_cases hh : firstLiveDistanceStop (γ sample) z e = (⊤ : ℝ≥0∞)
    · have hd : D sample = 0 := by simp only [D,physicalStoppedDensity,hh,ite_true]
      simp only [Set.indicator_apply,hd,ite_self]
    · have hv := physical_avoidance_at_finite_hit κ B sample hm hc z e S hh
      have hae : sample ∈ Eᶜ ↔ sample ∈ A := by
        simpa only [E,A,mem_compl_iff,mem_ofPred_eq,not_lt] using hv.not
      simp only [Set.indicator_apply,hae]
  have hall : (∫⁻ sample in E, D sample ∂P)+(∫⁻ sample in A, D sample ∂P) = M := by
    rw [← lintegral_indicator₀ hA,← lintegral_congr_ae hi,← lintegral_indicator₀ hE,
      ← lintegral_add_left' (hD.indicator₀ hE)]
    have hp : (fun sample => E.indicator D sample+Eᶜ.indicator D sample) = D := by
      funext sample
      by_cases hs : sample∈E <;> simp [hs]
    rw [hp]
    exact physicalDistanceStoppedDensity κ hκ B hB γ g f hγ hmaps z hz e he hes
  have hdouble : M = ENNReal.ofReal (m/2)+ENNReal.ofReal (m/2) := by
    change ENNReal.ofReal m = _
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ m/2) (by positivity : 0 ≤ m/2)]
    congr 1
    ring
  have hlow : ENNReal.ofReal (m/2) ≤ ∫⁻ sample in A, D sample ∂P := by
    apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
    rw [← hdouble,← hall]
    exact add_le_add htail le_rfl
  simpa only [A,D,m,hS] using hlow

lemma compact_initial_bounds (κ : ℝ) {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hhalf : K ⊆ halfPlane) :
    ∃ e₀ Y s m : ℝ, 0 < e₀ ∧ 0 < Y ∧ 0 < s ∧ 0 < m ∧ ∀ z ∈ K,
      e₀ ≤ z.im ∧ z.im ≤ Y ∧ s ≤ (z.im/‖z‖)^(8/κ-1) ∧
        m ≤ ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))/2 := by
  have hy (z : ℂ) (hz : z ∈ K) : 0 < z.im := hhalf hz
  have hn (z : ℂ) (hz : z ∈ K) : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 (by
    intro he
    simpa only [he,Complex.zero_im,lt_self_iff_false] using hy z hz)
  have hsin : ContinuousOn (fun z : ℂ => z.im/‖z‖) K :=
    Complex.continuous_im.continuousOn.div continuous_norm.continuousOn hn
  have hsp := hsin.rpow_const (p := 8/κ-1) (fun z hz => Or.inl (FiniteTilt.initial_sine_pos (hhalf hz)).ne')
  have hr : ContinuousOn (fun z : ℂ => (2*z.im)^(-codimension κ)) K :=
    (continuous_const.mul Complex.continuous_im).continuousOn.rpow_const
      (fun z hz => Or.inl (mul_pos (by norm_num) (hy z hz)).ne')
  have hm := (hr.mul hsp).div_const 2
  obtain ⟨z₀,hz₀,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨z₁,hz₁,hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_im.continuousOn
  obtain ⟨z₂,hz₂,hsmin⟩ := hK.exists_isMinOn hne hsp
  obtain ⟨z₃,hz₃,hmmin⟩ := hK.exists_isMinOn hne hm
  refine ⟨z₀.im,z₁.im,(z₂.im/‖z₂‖)^(8/κ-1),
    ((2*z₃.im)^(-codimension κ)*(z₃.im/‖z₃‖)^(8/κ-1))/2,
    hy z₀ hz₀,hy z₁ hz₁,Real.rpow_pos_of_pos (FiniteTilt.initial_sine_pos (hhalf hz₂)) _,
    div_pos (localizationInitialGreen_pos κ (hhalf hz₃)) (by norm_num),?_⟩
  intro z hz
  exact ⟨hmin hz,hmax hz,hsmin hz,hmmin hz⟩

theorem retainedPositiveFirstMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hK : Metric.closedBall c r ⊆ halfPlane) :
    ∃ T e₀ m₀ : ℝ, 0 < T ∧ 0 < e₀ ∧ 0 < m₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
      ENNReal.ofReal m₀ ≤ ∫⁻ sample, ∫⁻ z in Metric.closedBall c r,
        (if firstLiveDistanceStop (γ sample) z e ≤ ENNReal.ofReal T then
          physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e else 0)
        ∂volume ∂P := by
  classical
  let K := Metric.closedBall c r
  have hKm : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
  obtain ⟨e₀,Y,s,m,he₀,hY,hs,hm,hbd⟩ := compact_initial_bounds κ
    (isCompact_closedBall c r) ⟨c,Metric.mem_closedBall_self hr.le⟩ hK
  obtain ⟨T,hT,hfirst⟩ := uniformFiniteTimePhysicalDensity κ hκ B hB γ g f hγ hmaps Y s hY hs
  have hvol : 0 < (volume K).toReal := ENNReal.toReal_pos
    (Metric.measure_closedBall_pos volume c hr).ne' measure_closedBall_lt_top.ne
  refine ⟨T,e₀,m*(volume K).toReal,hT,he₀,mul_pos hm hvol,?_⟩
  intro e he hee
  obtain ⟨W,hW,hWe⟩ := jointFiniteTimePhysicalDensity κ hκ B hB γ g f hγ hmaps T hT e he
  have hwfirst (z : ℂ) (hz : z ∈ K) : ENNReal.ofReal m ≤ ∫⁻ sample, W (sample,z) ∂P := by
    have hes : e < z.im := hee.trans_le (hbd z hz).1
    let S : ℝ≥0 := ⟨T,hT.le⟩
    have hS : (S : ℝ≥0∞) = ENNReal.ofReal T := ENNReal.ofReal_coe_nnreal.symm
    have hA : NullMeasurableSet {sample | firstLiveDistanceStop (γ sample) z e ≤ ENNReal.ofReal T} P := by
      simpa only [hS] using
        physical_early_nullMeasurable κ hκ B hB γ g f hmaps z (hK hz) e he hes S
    have hideq : (∫⁻ sample, W (sample,z) ∂P) =
        ∫⁻ sample in {sample | firstLiveDistanceStop (γ sample) z e ≤ ENNReal.ofReal T},
          physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e ∂P := by
      rw [← lintegral_indicator₀ hA]
      apply lintegral_congr_ae
      filter_upwards [hWe] with sample hw
      simpa only [Set.indicator_apply,Set.mem_ofPred_eq] using hw z
    rw [hideq]
    exact (ENNReal.ofReal_le_ofReal (hbd z hz).2.2.2).trans
      (hfirst z (hK hz) (hbd z hz).2.1 (hbd z hz).2.2.1 e he hes)
  have hmass : ENNReal.ofReal (m*(volume K).toReal) ≤
      ∫⁻ z in K, ∫⁻ sample, W (sample,z) ∂P ∂volume := by
    calc
      _ = ∫⁻ z in K, ENNReal.ofReal m ∂volume := by
        rw [lintegral_const,Measure.restrict_apply_univ,ENNReal.ofReal_mul hm.le,
          ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]
      _ ≤ _ := lintegral_mono_ae (ae_restrict_of_forall_mem hKm hwfirst)
  have hswap : (∫⁻ z in K, ∫⁻ sample, W (sample,z) ∂P ∂volume) =
      ∫⁻ sample, ∫⁻ z in K, W (sample,z) ∂volume ∂P := by
    exact (lintegral_lintegral_swap (μ := P) (ν := volume.restrict K)
      (f := fun sample z => W (sample,z)) hW.aemeasurable).symm
  rw [hswap] at hmass
  apply hmass.trans_eq
  apply lintegral_congr_ae
  filter_upwards [hWe] with sample hw
  exact lintegral_congr hw

end SLEExactGauge

end

end

end OAI
