import OAI.Probability.SLE.Mass.LevelApproximants

namespace OAI

/-! A fixed additional approach event costs its target radius to the
codimension power, uniformly in the levels of the integrated weights. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma lintegral_indicator_ofReal_prod_le_event
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (E₀ E : Set Ω) (Y : ι → Ω → ℝ) (c : ι → ℝ)
    (hY0 : ∀ i ω, 0 ≤ Y i ω)
    (hY : ∀ ω ∈ E, ∀ i, Y i ω ≤ c i)
    (hzero : ∀ ω, ω ∈ E₀ → ω ∉ E → ∃ i, Y i ω = 0) :
    (∫⁻ ω, E₀.indicator (fun ω => ENNReal.ofReal (∏ i, Y i ω)) ω ∂P) ≤
      ENNReal.ofReal (∏ i, c i) * P E := by
  classical
  apply (lintegral_mono (fun ω => ?_)).trans (lintegral_indicator_const_le E _)
  by_cases hω₀ : ω ∈ E₀
  · rw [indicator_of_mem hω₀]
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      exact ENNReal.ofReal_le_ofReal (Finset.prod_le_prod₀ (fun i _ => hY0 i ω)
        (fun i _ => hY ω hω i))
    · obtain ⟨i,hi⟩ := hzero ω hω₀ hω
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi,ENNReal.ofReal_zero]
      exact bot_le
  · rw [indicator_of_notMem hω₀]
    exact bot_le

theorem stoppedGreen_centered_product_expectation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (m : ℕ)
    (z : Fin (m+1) → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (hne : Function.Injective z) (b e : Fin (m+1) → ℝ)
    (he : ∀ i, 0 < e i) (hb : ∀ i, 0 < b i)
    (hbR : ∀ i, b i ≤ 2*(z i).im)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (z i) (z j)) :
    (∫⁻ ω, {ω | ∃ t : ℝ≥0, z 0 ∈ survivingDomain (γ ω) t ∧
        physicalConformalRadius (fun z : ℂ => z) (G ω) t (z 0) ≤ e 0}.indicator
      (fun ω => ENNReal.ofReal (∏ i : Fin m, stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
        (γ ω) (G ω) (z i.succ) (Real.log (2*(z i.succ).im/e i.succ)))) ω ∂P) ≤
      ENNReal.ofReal ((3 : ℝ)^(m+1) *
        Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset (Fin (m+1)))) *
        (e 0)^(codimension κ) * ∏ i, (b i)^(-codimension κ)) := by
  classical
  let E₀ := {ω | ∃ t : ℝ≥0, z 0 ∈ survivingDomain (γ ω) t ∧
    physicalConformalRadius (fun z : ℂ => z) (G ω) t (z 0) ≤ e 0}
  let E := {ω | ω ∈ E₀ ∧ ∀ i : Fin m,
    radiusLevelTime (γ ω) (G ω) (z i.succ) (Real.log (2*(z i.succ).im/e i.succ)) < ∞}
  let Y := fun (i : Fin m) ω => stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
    (γ ω) (G ω) (z i.succ) (Real.log (2*(z i.succ).im/e i.succ))
  let W := ∏ i : Fin m, (e i.succ)^(-codimension κ)
  let C := (3 : ℝ)^(m+1) *
    Real.exp (uniformDiscountBudget κ (sourceBeta κ) (Finset.univ : Finset (Fin (m+1))))
  have hW : 0 ≤ W := Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (he i.succ).le _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hint := lintegral_indicator_ofReal_prod_le_event P E₀ E Y
    (fun i => (e i.succ)^(-codimension κ))
    (fun i ω => stoppedGreen_nonneg (hw ω) κ _ _)
    (fun ω _ i => stoppedGreen_level_bound (continuous_const.mul (hBc ω))
      (hw ω) hκ hκ8 (z i.succ) (hz i.succ) (e i.succ) (he i.succ)) (fun ω hω hn => by
      have hn' : ¬ ∀ i : Fin m,
          radiusLevelTime (γ ω) (G ω) (z i.succ) (Real.log (2*(z i.succ).im/e i.succ)) < ∞ :=
        fun hi => hn ⟨hω,hi⟩
      obtain ⟨i,hi⟩ := not_forall.mp hn'
      exact ⟨i,by simp only [Y,stoppedGreen,ite_eq_right hi]⟩)
  have hprob := capped_physical_radius_multipoint_bound hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth (fun z : ℂ => z) differentiableOn_id (fun _ _ _ _ h => h)
    z hz hne (fun i => 2*(z i).im) b e he hb
    (fun i => by simpa only [deriv_id'',norm_one,mul_one] using hbR i)
    (fun i => by simp only [deriv_id'',norm_one,mul_one]) hsep
  have hsub : E ⊆ {ω | ∀ i, ∃ t : ℝ≥0, z i ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius (fun z : ℂ => z) (G ω) t (z i) ≤ e i} := by
    intro ω hω
    refine Fin.cases hω.1 (fun i => ?_)
    obtain ⟨t,ht,hR⟩ := (physical_radius_eq_hit_iff_finite_level
      (continuous_const.mul (hBc ω)) (hw ω) (fun z : ℂ => z) (z i.succ)
      (2*(z i.succ).im) (e i.succ) (mul_pos (by norm_num) (hz i.succ)) (he i.succ)
      (by simp only [deriv_id'',norm_one,mul_one])).mpr (hω.2 i)
    exact ⟨t,ht,hR.le⟩
  have hα : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  have hp : W * (∏ i, min 1 ((e i/b i)^(1-κ/8))) ≤
      (e 0)^(codimension κ) * ∏ i, (b i)^(-codimension κ) := by
    rw [← hα,Fin.prod_univ_succ]
    have hroot : min 1 ((e 0/b 0)^codimension κ) ≤
        (e 0)^codimension κ * (b 0)^(-codimension κ) := by
      rw [Real.rpow_neg (hb 0).le,← div_eq_mul_inv,← Real.div_rpow (he 0).le (hb 0).le]
      exact min_le_right _ _
    have htail : W * (∏ i : Fin m, min 1 ((e i.succ/b i.succ)^codimension κ)) ≤
        ∏ i : Fin m, (b i.succ)^(-codimension κ) := by
      dsimp only [W]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (Real.rpow_nonneg (he i.succ).le _)
          (le_min zero_le_one (Real.rpow_nonneg (div_nonneg (he i.succ).le (hb i.succ).le) _))
      · exact fun i _ => target_weight_capped (hb i.succ) (he i.succ)
    calc
      _ = min 1 ((e 0/b 0)^codimension κ) *
          (W * ∏ i : Fin m, min 1 ((e i.succ/b i.succ)^codimension κ)) := by ring
      _ ≤ ((e 0)^codimension κ * (b 0)^(-codimension κ)) *
          ∏ i : Fin m, (b i.succ)^(-codimension κ) :=
        mul_le_mul hroot htail (mul_nonneg hW (Finset.prod_nonneg (fun i _ =>
          le_min zero_le_one (Real.rpow_nonneg (div_nonneg (he i.succ).le (hb i.succ).le) _))))
          (mul_nonneg (Real.rpow_nonneg (he 0).le _) (Real.rpow_nonneg (hb 0).le _))
      _ = _ := by rw [Fin.prod_univ_succ]; ring
  calc
    _ ≤ ENNReal.ofReal W * P E := hint
    _ ≤ ENNReal.ofReal W * ENNReal.ofReal (C * ∏ i, min 1 ((e i/b i)^(1-κ/8))) :=
      mul_le_mul' le_rfl ((measure_mono hsub).trans (by simpa only [Fintype.card_fin] using hprob))
    _ = ENNReal.ofReal (C * (W * ∏ i, min 1 ((e i/b i)^(1-κ/8)))) := by
      rw [← ENNReal.ofReal_mul hW]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      simpa only [C,mul_assoc] using (mul_le_mul_of_nonneg_left hp hC))

lemma measurableSet_physical_radius_hit
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (e : ℝ) (he : 0 < e) (heR : e ≤ 2*z.im) :
    MeasurableSet {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius (fun z : ℂ => z) (G ω) t z ≤ e} := by
  have hu : 0 ≤ Real.log (2*z.im/e) :=
    Real.log_nonneg ((one_le_div he).mpr heR)
  have hj : Measurable (fun q : Ω × ℂ =>
      radiusLevelTime (γ q.1) (G q.1) q.2 (Real.log (2*z.im/e))) :=
    actual_radiusLevel_joint_measurable hm hBc κ (Real.log (2*z.im/e)) hu γ G F hw
  have hp : Measurable (fun ω : Ω => (ω,z)) :=
    (measurable_id : Measurable (fun ω : Ω => ω)).prodMk
      (measurable_const : Measurable (fun _ : Ω => z))
  have hc := hj.comp hp
  have hmτ : Measurable (fun ω => radiusLevelTime (γ ω) (G ω) z (Real.log (2*z.im/e))) := by
    simpa only [Function.comp_def] using hc
  suffices hE : {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) t ∧
      physicalConformalRadius (fun z : ℂ => z) (G ω) t z ≤ e} =
      {ω | radiusLevelTime (γ ω) (G ω) z (Real.log (2*z.im/e)) < (⊤ : ℝ≥0∞)} by
    rw [hE]
    exact measurableSet_lt hmτ measurable_const
  ext ω
  exact physical_radius_hit_iff_finite_level (continuous_const.mul (hBc ω)) (hw ω)
    (fun z : ℂ => z) z (2*z.im) e (mul_pos (by norm_num) hz) he heR
    (by simp only [deriv_id'',norm_one,mul_one])

theorem stoppedGreen_centered_common_level_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (m : ℕ)
    (z : Fin (m+1) → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (hne : Function.Injective z) (b : Fin (m+1) → ℝ)
    (hb : ∀ i, 0 < b i) (hbR : ∀ i, b i ≤ 2*(z i).im)
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (z i) (z j))
    (e₀ : ℝ) (he₀ : 0 < e₀) (u : ℝ) :
    (∫⁻ ω, {ω | ∃ t : ℝ≥0, z 0 ∈ survivingDomain (γ ω) t ∧
        physicalConformalRadius (fun z : ℂ => z) (G ω) t (z 0) ≤ e₀}.indicator
      (fun ω => ENNReal.ofReal (∏ i : Fin m, stoppedGreen κ (fun t => Real.sqrt κ*B t ω)
        (γ ω) (G ω) (z i.succ) u)) ω ∂P) ≤
      ENNReal.ofReal (multipointConstant κ (m+1) *
        e₀^(codimension κ) * ∏ i, (b i)^(-codimension κ)) := by
  let e : Fin (m+1) → ℝ := Fin.cons e₀ (fun i => 2*(z i.succ).im*Real.exp (-u))
  have he : ∀ i, 0 < e i := by
    refine Fin.cases he₀ (fun i => ?_)
    exact mul_pos (mul_pos (by norm_num) (hz i.succ)) (Real.exp_pos _)
  have h := stoppedGreen_centered_product_expectation_bound hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth m z hz hne b e he hb hbR hsep
  simpa only [e,Fin.cons_zero,Fin.cons_succ,common_level_log_target _ (hz _) u,
    multipointConstant] using h

end SLEExactGauge.Multipoint

end

end OAI
