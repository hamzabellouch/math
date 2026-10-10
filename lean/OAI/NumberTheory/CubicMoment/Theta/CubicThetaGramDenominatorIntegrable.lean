import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramJointKernel

namespace OAI

/-! Absolute integrability of every actual denominator contribution.
The compact radial weight and the positive cutoff on the inverted weight
place the joint kernel inside one compact cylinder. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaGramJointKernel_integrableOn (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {c : ℂ} (hc : c≠0) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hV : ∀ t≤δ,V t=0) :
    IntegrableOn (cubicThetaGramJointKernel h k W V c) (univ ×ˢ Ioi ε) := by
  obtain ⟨B,hB⟩ := W.hasCompactSupport.isCompact.bddAbove_image continuous_id.continuousOn
  let R := Real.sqrt (B/(Complex.normSq c*δ))
  let K : Set (ℂ × ℝ) := Metric.closedBall 0 R ×ˢ Icc ε B
  have hK : IsCompact K := (isCompact_closedBall 0 R).prod isCompact_Icc
  have hcont : ContinuousOn (cubicThetaGramJointKernel h k W V c) K := by
    intro y hy
    exact (cubicThetaGramJointKernel_continuousAt h k W V hc (hε.trans_le hy.2.1)).continuousWithinAt
  have hib : IntegrableOn (cubicThetaGramJointKernel h k W V c) K :=
    hcont.integrableOn_compact hK
  apply hib.of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Ioi)
  rintro y ⟨hy,hyK⟩
  by_contra hf
  have hW : W y.2≠0 := by
    intro hz
    exact hf (by simp only [cubicThetaGramJointKernel,hz,star_zero,zero_div,zero_mul])
  have hker : cubicThetaGramInversionKernel h k V c y.1 y.2≠0 := by
    intro hz
    exact hf (by simp only [cubicThetaGramJointKernel,hz,mul_zero])
  have hyB : y.2≤B := hB ⟨y.2,subset_tsupport _ hW,rfl⟩
  have hy0 : 0<y.2 := hε.trans hy.2
  have hnorm : ‖y.1‖≤Real.sqrt (y.2/(Complex.normSq c*δ)) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      cubicThetaGramInversionKernel_support h k V hc hδ hy0 hV hker
  apply hyK
  refine ⟨?_,⟨hy.2.le,hyB⟩⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  exact hnorm.trans (Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right
    (mul_pos (Complex.normSq_pos.mpr hc) hδ)).mpr hyB))

lemma cubicThetaGramKernel_weight_integrable (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {c : ℂ} (hc : c≠0) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hV : ∀ t≤δ,V t=0) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*
      ∫ z,cubicThetaGramInversionKernel h k V c z v) (Ioi ε) := by
  have hi := cubicThetaGramJointKernel_integrableOn h k W V hc hε hδ hV
  change Integrable (cubicThetaGramJointKernel h k W V c)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioi ε)) at hi
  rw [←Measure.prod_restrict,Measure.restrict_univ] at hi
  apply hi.integral_prod_right.congr
  filter_upwards with v
  dsimp only [cubicThetaGramJointKernel]
  rw [integral_const_mul]

lemma cubicThetaGramDenominator_integrable (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    (c : Eisenstein) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hV : ∀ t≤δ,V t=0) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaGramKloostermanTerm h k V c v)
      (Ioi ε) := by
  unfold cubicThetaGramKloostermanTerm
  split_ifs with hc
  · have hcC : (c:ℂ)≠0 := fun he => hc.2 (Subtype.ext he)
    have hi := (cubicThetaGramKernel_weight_integrable h k W V hcC hε hδ hV).const_mul
      (cubicThetaKloostermanSum h k c hc.1)
    apply hi.congr
    filter_upwards with v
    ring
  · simpa only [mul_zero] using (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0:ℂ)) (Ioi ε))

end CubicFirstMoment

end

end OAI
