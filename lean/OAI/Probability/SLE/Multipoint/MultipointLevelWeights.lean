import OAI.Probability.SLE.Multipoint.MultipointOrdinaryProbability
import OAI.Probability.SLE.FiniteStoppedLaw

namespace OAI

/-! From the multipoint probability bound to the product estimate for
actual stopped Green weights. The estimate is uniform in their levels. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma target_weight_capped {α b e : ℝ} (hb : 0 < b) (he : 0 < e) :
    e^(-α) * min 1 ((e/b)^α) ≤ b^(-α) := by
  calc
    _ ≤ e^(-α) * (e/b)^α :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.rpow_nonneg he.le _)
    _ = b^(-α) := by
      rw [Real.rpow_neg he.le,Real.rpow_neg hb.le,Real.div_rpow he.le hb.le]
      field_simp [(Real.rpow_pos_of_pos he α).ne']

lemma lintegral_ofReal_prod_le_event
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (E : Set Ω) (Y : ι → Ω → ℝ) (c : ι → ℝ)
    (hY0 : ∀ i ω, 0 ≤ Y i ω)
    (hY : ∀ ω ∈ E, ∀ i, Y i ω ≤ c i)
    (hzero : ∀ ω, ω ∉ E → ∃ i, Y i ω = 0) :
    (∫⁻ ω, ENNReal.ofReal (∏ i, Y i ω) ∂P) ≤ ENNReal.ofReal (∏ i, c i) * P E := by
  classical
  apply (lintegral_mono (fun ω => ?_)).trans (lintegral_indicator_const_le E _)
  by_cases hω : ω ∈ E
  · rw [indicator_of_mem hω]
    exact ENNReal.ofReal_le_ofReal (Finset.prod_le_prod₀ (fun i _ => hY0 i ω)
      (fun i _ => hY ω hω i))
  · obtain ⟨i,hi⟩ := hzero ω hω
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi,ENNReal.ofReal_zero]
    exact bot_le

lemma stoppedGreen_level_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (e : ℝ) (he : 0 < e) :
    stoppedGreen κ U γ G z (Real.log (2*z.im/e)) ≤ e^(-codimension κ) := by
  by_cases hf : radiusLevelTime γ G z (Real.log (2*z.im/e)) < ∞
  · obtain ⟨t,ht,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z _ hf
    have htarget : (2*z.im)*Real.exp (-Real.log (2*z.im/e)) = e := by
      rw [Real.exp_neg,Real.exp_log (div_pos (mul_pos (by norm_num) hz) he)]
      field_simp [he.ne',(show z.im ≠ 0 from ne_of_gt hz)]
    rw [stoppedGreen_eq_of_live_level hU hw κ z _ t ht hR,greenDensity,ite_eq_left ht,
      hR,htarget]
    have hsin : 0 ≤ Real.sin (Complex.arg (G t z - (U t : ℂ))) := by
      rw [Complex.sin_arg,Complex.sub_im,Complex.ofReal_im,sub_zero]
      exact div_nonneg (hw.imag_positive t z ht).le (norm_nonneg _)
    exact mul_le_of_le_one_right (Real.rpow_nonneg he.le _)
      (Real.rpow_le_one hsin (Real.sin_le_one _) (greenExponent_pos κ hκ hκ8).le)
  · simp only [stoppedGreen,ite_eq_right hf]
    exact Real.rpow_nonneg he.le _

theorem stoppedGreen_product_expectation_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane) (hne : Function.Injective z)
    (b e : ι → ℝ) (he : ∀ i, 0 < e i) (hb : ∀ i, 0 < b i)
    (hbR : ∀ i, b i ≤ 2*(z i).im)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (z i) (z j)) :
    (∫⁻ ω, ENNReal.ofReal (∏ i, stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
      (γ ω) (G ω) (z i) (Real.log (2*(z i).im/e i))) ∂P) ≤
      ENNReal.ofReal ((3 : ℝ)^(Fintype.card ι) *
        Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι)) *
        ∏ i, (b i)^(-codimension κ)) := by
  classical
  let E := {ω | ∀ i, radiusLevelTime (γ ω) (G ω) (z i) (Real.log (2*(z i).im/e i)) < ∞}
  let Y := fun i ω => stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
    (γ ω) (G ω) (z i) (Real.log (2*(z i).im/e i))
  let W := ∏ i, (e i)^(-codimension κ)
  let C := (3 : ℝ)^(Fintype.card ι) *
    Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset ι))
  have hW : 0 ≤ W := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (he i).le _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hint := lintegral_ofReal_prod_le_event P E Y (fun i => (e i)^(-codimension κ))
    (fun i ω => stoppedGreen_nonneg (hw ω) κ _ _)
    (fun ω _ i => stoppedGreen_level_bound (continuous_const.mul (hBc ω))
      (hw ω) hκ hκ8 (z i) (hz i) (e i) (he i)) (fun ω hω => by
      obtain ⟨i,hi⟩ := not_forall.mp hω
      exact ⟨i,by simp only [Y,stoppedGreen,ite_eq_right hi]⟩)
  have hprob := capped_physical_radius_multipoint_bound hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth (fun z : ℂ => z) differentiableOn_id (fun _ _ _ _ h => h)
    z hz hne (fun i => 2*(z i).im) b e he hb
    (fun i => by simpa only [deriv_id'',norm_one,mul_one] using hbR i)
    (fun i => by simp only [deriv_id'',norm_one,mul_one]) hsep
  have hsub : E ⊆ {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius (fun z : ℂ => z) (G ω) t (z i) ≤ e i} := by
    intro ω hω i
    obtain ⟨t,ht,hR⟩ := (physical_radius_eq_hit_iff_finite_level
      (continuous_const.mul (hBc ω)) (hw ω) (fun z : ℂ => z) (z i) (2*(z i).im) (e i)
      (mul_pos (by norm_num) (hz i)) (he i)
      (by simp only [deriv_id'',norm_one,mul_one])).mpr (hω i)
    exact ⟨t,ht,hR.le⟩
  have hα : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  have hp : W * (∏ i, min 1 ((e i/b i)^(1-κ/8))) ≤ ∏ i, (b i)^(-codimension κ) := by
    dsimp only [W]
    rw [← Finset.prod_mul_distrib,← hα]
    apply Finset.prod_le_prod₀
    · intro i _
      exact mul_nonneg (Real.rpow_nonneg (he i).le _) (le_min zero_le_one (Real.rpow_nonneg (div_nonneg (he i).le (hb i).le) _))
    · exact fun i _ => target_weight_capped (hb i) (he i)
  calc
    _ ≤ ENNReal.ofReal W * P E := hint
    _ ≤ ENNReal.ofReal W * ENNReal.ofReal (C * ∏ i, min 1 ((e i/b i)^(1-κ/8))) :=
      mul_le_mul' le_rfl ((measure_mono hsub).trans hprob)
    _ = ENNReal.ofReal (C * (W * ∏ i, min 1 ((e i/b i)^(1-κ/8)))) := by
      rw [← ENNReal.ofReal_mul hW]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp hC)

end SLEExactGauge.Multipoint

end

end OAI
