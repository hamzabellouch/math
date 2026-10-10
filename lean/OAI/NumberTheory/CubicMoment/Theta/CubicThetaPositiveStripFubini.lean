import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierStripUnfold
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStripFubini

namespace OAI

/-! Fubini and radial Fourier pairing at any positive cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveCuspStrip_fubini {ε : ℝ} (hε : 0≤ε) (f : ℂ × ℝ → ℂ)
    (hf : IntegrableOn (fun p => f (cubicThetaPointCoordinates p))
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure) :
    (∫ p in cubicThetaCuspStrip ε,f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ v in Ioi ε,∫ z in cubicThetaHorizontalCell,f (z,v)/(v:ℂ)^3 := by
  have hi := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable ε) f).mp hf
  rw [cubicThetaPointIntegral_complex_density (cubicThetaCuspStrip_measurable ε),
    cubicThetaCuspStrip_coordinates hε]
  rw [cubicThetaCuspStrip_coordinates hε] at hi
  change Integrable (fun y : ℂ × ℝ => f y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi
  rw [←Measure.prod_restrict] at hi
  change (∫ y : ℂ × ℝ,f y/(y.2:ℂ)^3 ∂
    ((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi ε))=_
  rw [←Measure.prod_restrict]
  exact integral_prod_symm _ hi

lemma cubicThetaFourierStripSeed_pair_on_strip (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (_hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    (∫ p,star (cubicThetaFourierStripSeed h W p)*F.val p ∂cubicThetaPointMeasure)=
      ∫ p in cubicThetaCuspStrip ε,
        star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val p ∂cubicThetaPointMeasure := by
  have hz : ∀ p∉cubicThetaCuspStrip ε,star (cubicThetaFourierStripSeed h W p)*F.val p=0 := by
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

lemma cubicThetaPositiveFourierPairing_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*F.val p)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
  apply (cubicThetaFourierStripSeed_pair_integrable h W hε hW F).integrableOn.congr
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable ε)] with p hp
  change ε<p.val.2 ∧ p.val.1∈cubicThetaHorizontalCell at hp
  simp only [cubicThetaFourierStripSeed,ite_eq_left hp.2]

theorem cubicThetaPositiveFourierProfile_pairing_radial (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    (∫ q,cubicThetaSectionPairing (cubicThetaPositiveFourierProfileSection h W hε hW) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v := by
  have hi := cubicThetaPositiveFourierPairing_integrable h W hε hW F
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  rw [cubicThetaPositiveFourierProfile_pairing_integral h W hε hW F,
    cubicThetaFourierStripSeed_pair_on_strip h W hε hW F]
  have he := cubicThetaPositiveCuspStrip_fubini hε.le
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*cubicThetaSectionFunction F y) hi'
  change (∫ p in cubicThetaCuspStrip ε,
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*cubicThetaSectionFunction F p.val
      ∂cubicThetaPointMeasure)=_ at he
  simp_rw [cubicThetaSectionFunction_coordinates] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  dsimp only [cubicThetaSectionFourierFunction,cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

lemma cubicThetaPositiveFourier_weight_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v)
      (Ioi ε) := by
  have hi := cubicThetaPositiveFourierPairing_integrable h W hε hW F
  have hi' : IntegrableOn (fun p : CubicThetaPoint =>
      star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*cubicThetaSectionFunction F p.val)
      (cubicThetaCuspStrip ε) cubicThetaPointMeasure := by
    apply hi.congr
    filter_upwards with p
    rw [cubicThetaSectionFunction_coordinates]
  have hi'' := (cubicThetaPointIntegrable_complex_density (cubicThetaCuspStrip_measurable ε)
    (fun y => star (W y.2*cubicThetaHorizontalCharacter h y.1)*cubicThetaSectionFunction F y)).mp hi'
  rw [cubicThetaCuspStrip_coordinates hε.le] at hi''
  change Integrable (fun y : ℂ × ℝ => star (W y.2*cubicThetaHorizontalCharacter h y.1)*
    cubicThetaSectionFunction F y/(y.2:ℂ)^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict _) at hi''
  rw [←Measure.prod_restrict] at hi''
  apply hi''.integral_prod_right.congr
  filter_upwards with v
  dsimp only [cubicThetaSectionFourierFunction,cubicThetaHorizontalFourierCoefficient]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
