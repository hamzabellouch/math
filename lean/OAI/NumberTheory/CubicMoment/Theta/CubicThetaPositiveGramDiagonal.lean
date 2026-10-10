import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveProfileGram

namespace OAI

/-! The diagonal part of the literal finite-row Gram expansion. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveSeed_mul_strip (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hW : ∀ v≤ε,W v=0) (g : CubicThetaPoint → ℂ) :
    (∫ p,star (cubicThetaFourierStripSeed h W p)*g p ∂cubicThetaPointMeasure)=
      ∫ p in cubicThetaCuspStrip ε,
        star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*g p ∂cubicThetaPointMeasure := by
  have hz : ∀ p∉cubicThetaCuspStrip ε,star (cubicThetaFourierStripSeed h W p)*g p=0 := by
    intro p hp
    by_cases hc : p.val.1∈cubicThetaHorizontalCell
    · have hh : p.val.2≤ε := by
        by_contra hn
        exact hp ⟨lt_of_not_ge hn,hc⟩
      simp only [cubicThetaFourierStripSeed,ite_eq_left hc,hW _ hh,zero_mul,star_zero]
    · simp only [cubicThetaFourierStripSeed,ite_eq_right hc,star_zero,zero_mul]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable ε)
  intro p hp
  change ε<p.val.2 ∧ p.val.1∈cubicThetaHorizontalCell at hp
  simp only [cubicThetaFourierStripSeed,ite_eq_left hp.2]

theorem cubicThetaPositiveProfileGram_zeroRow (h k : Eisenstein)
    (W V : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    (∫ p,star (cubicThetaFourierStripSeed h W p)*
      cubicThetaFourierProfileTerm k cubicThetaZeroRow p.val V ∂cubicThetaPointMeasure)=
      ∫ v in Ioi ε,star (W v)*V v/(v:ℂ)^3*
        cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k) := by
  let f : ℂ × ℝ → ℂ := fun y =>
    star (W y.2*cubicThetaHorizontalCharacter h y.1)*
      (V y.2*cubicThetaHorizontalCharacter k y.1)
  have hi : IntegrableOn (fun p : CubicThetaPoint => f p.val)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply (cubicThetaPositiveProfileGram_row_integrable h k W V hε hW cubicThetaZeroRow).integrableOn.congr
    filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable ε)] with p hp
    rw [cubicThetaFourierProfileTerm_zeroRow k V p.property]
    change ε<p.val.2 ∧ p.val.1∈cubicThetaHorizontalCell at hp
    simp only [cubicThetaFourierStripSeed,ite_eq_left hp.2]
    rfl
  rw [cubicThetaPositiveSeed_mul_strip h W hW]
  have he : (∫ p in cubicThetaCuspStrip ε,
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*
        cubicThetaFourierProfileTerm k cubicThetaZeroRow p.val V ∂cubicThetaPointMeasure)=
      ∫ p in cubicThetaCuspStrip ε,f p.val ∂cubicThetaPointMeasure := by
    apply setIntegral_congr_fun (cubicThetaCuspStrip_measurable ε)
    intro p _
    dsimp only
    rw [cubicThetaFourierProfileTerm_zeroRow k V p.property]
  have hfub := cubicThetaPositiveCuspStrip_fubini hε.le f hi
  change (∫ p in cubicThetaCuspStrip ε,f p.val ∂cubicThetaPointMeasure)=_ at hfub
  rw [he,hfub]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  dsimp only [f]
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
