import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripFubini
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialWeightScaling

namespace OAI

/-! All positive-cutoff Fourier profiles lie in the actual mass closure.
Their pairings are the full positive-height Fourier integrals. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPositiveRadialIntegral_zero_extension (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0≤ε) (hW : ∀ v≤ε,W v=0) (f : ℝ → ℂ) :
    (∫ v in Ioi ε,star (W v)/(v:ℂ)^3*f v)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*f v := by
  have he (a : ℝ) (ha : a≤ε) :
      (∫ v in Ioi a,star (W v)/(v:ℂ)^3*f v)=
        ∫ v : ℝ,star (W v)/(v:ℂ)^3*f v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hW v ((le_of_not_gt hv).trans ha),star_zero,zero_div,zero_mul]
  rw [he ε le_rfl,he 0 hε]

lemma cubicThetaPositiveRadialIntegral_integrable (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0≤ε) (hW : ∀ v≤ε,W v=0) (f : ℝ → ℂ)
    (hf : IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f v) (Ioi ε)) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*f v) (Ioi (0:ℝ)) := by
  let g : ℝ → ℂ := fun v => star (W v)/(v:ℂ)^3*f v
  have he : (Ioi (0:ℝ)).indicator g=(Ioi ε).indicator g := by
    funext v
    change (if 0<v then g v else 0)=(if ε<v then g v else 0)
    split_ifs with h0 he he
    · rfl
    · dsimp only [g]
      rw [hW v (le_of_not_gt he),star_zero,zero_div,zero_mul]
    · exact (h0 (lt_of_le_of_lt hε he)).elim
    · rfl
  rw [←integrable_indicator_iff measurableSet_Ioi] at hf ⊢
  change Integrable ((Ioi (0:ℝ)).indicator g)
  rw [he]
  exact hf

def cubicThetaPositiveFourierMass (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaAutomorphicL2 :=
  cubicThetaGlobalMassClosure (cubicThetaPositiveFourierProfileTest h W hε hW hsm)

lemma cubicThetaPositiveFourierMass_pairing_finite (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ))
    (F : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaPositiveFourierMass h W hε hW hsm) (cubicThetaFiniteMassClosure F)=
      ∫ v in Ioi (0:ℝ),star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v := by
  change inner ℂ (cubicThetaPositiveFourierProfileL2 h W hε hW) (F.property.2.1.toLp _)=_
  rw [cubicThetaPositiveFourierProfileL2,cubicThetaSectionPairing_L2,
    cubicThetaPositiveFourierProfile_pairing_radial h W hε hW F,
    cubicThetaPositiveRadialIntegral_zero_extension W hε.le hW]

lemma cubicThetaPositiveFourier_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    IntegrableOn (fun v => star (W v)/(v:ℂ)^3*cubicThetaSectionFourierFunction F h v)
      (Ioi (0:ℝ)) :=
  cubicThetaPositiveRadialIntegral_integrable W hε.le hW _
    (cubicThetaPositiveFourier_weight_integrable h W hε hW F)

lemma cubicThetaRadialWeightScale_positive_low {ε r : ℝ} (hr : 0<r)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤ε,W v=0) (v : ℝ) (hv : v≤ε/r) :
    cubicThetaRadialWeightScale r hr W v=0 := by
  apply hW
  change r*v≤ε
  have he := (le_div_iff₀ hr).mp hv
  simpa only [mul_comm] using he

end CubicFirstMoment

end

end OAI
