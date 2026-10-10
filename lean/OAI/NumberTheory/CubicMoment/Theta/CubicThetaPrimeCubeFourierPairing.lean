import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierRadialScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeEnergyOperator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeightMultiplier

namespace OAI

/-! Exact nonzero-frequency test duality for the actual Hecke operator. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeFourierPairing_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) (h : Eisenstein) (hh : ¬p∣h)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    inner ℂ (cubicThetaCuspFourierTest h W)
        (cubicThetaFiniteCuspRestriction (cubicThetaPrimeCubeHeckeFinite hp F))=
      inner ℂ (cubicThetaCuspFourierTest (p^3*h)
        (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
          (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) W))
        (cubicThetaFiniteCuspRestriction F)+
      (cubicThetaPrimeCubeUnitFourier hp 1 (p*h)/(norm p:ℂ))*
        inner ℂ (cubicThetaCuspFourierTest (p*h)
          (cubicThetaRadialWeightScale ‖(p:ℂ)‖
            (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) W))
          (cubicThetaFiniteCuspRestriction F) := by
  let r := ‖(p:ℂ)‖
  have hr0 : 0<r := norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))
  have hr : 1≤r := by
    have hq := one_le_norm hp.2.ne_zero
    change 1≤Complex.normSq (p:ℂ) at hq
    rw [Complex.normSq_eq_norm_sq] at hq
    nlinarith
  have hr3 : 1≤r^3 := one_le_pow₀ hr
  have hW1 : ∀ v≤2*r,W v=0 := by
    intro v hv
    apply hW
    change v≤2*r^3
    nlinarith [sq_nonneg (r-1)]
  have hs : Ioi (2:ℝ)⊆Ioi 0 := fun _ hv => lt_trans (by norm_num : (0:ℝ)<2) hv
  have hB := (cubicThetaSectionFourier_divide_integrable F (p^3*h) hr3 W hW).mono_set hs
  have hU := (cubicThetaSectionFourier_divide_integrable F (p*h) hr W hW1).mono_set hs
  have hfun : ∀ v,2<v →
      cubicThetaSectionFourierFunction (cubicThetaPrimeCubeHeckeFinite hp F) h v=
        (norm (p^3):ℂ)*cubicThetaSectionFourierFunction F (p^3*h) (v/r^3)+
        cubicThetaPrimeCubeUnitFourier hp 1 (p*h)*cubicThetaSectionFourierFunction F (p*h) (v/r) := by
    intro v hv
    have hv0 : 0<v := lt_trans (by norm_num) hv
    rw [cubicThetaSectionFourierFunction_eq _ _ _ hv0]
    change cubicThetaSectionFourier (cubicThetaPrimeCubeHecke hp F) v hv0 h=_
    rw [cubicThetaPrimeCubeHecke_fourier_primefree hp F v hv0 h hh,
      cubicThetaSectionFourierFunction_eq _ _ _ (div_pos hv0 (pow_pos hr0 3)),
      cubicThetaSectionFourierFunction_eq _ _ _ (div_pos hv0 hr0)]
  have hN3 : (norm (p^3):ℂ)=((r^3:ℝ):ℂ)^2 := by
    rw [cubicThetaPrimeCube_norm_power]
    dsimp only [r]
    push_cast
    ring
  have hN : (norm p:ℂ)=(r:ℂ)^2 := by
    change (Complex.normSq (p:ℂ):ℂ)=(r:ℂ)^2
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [cubicThetaSectionFourierPairing]
  calc
    _ = (norm (p^3):ℂ)*(∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
          cubicThetaSectionFourierFunction F (p^3*h) (v/r^3))+
        cubicThetaPrimeCubeUnitFourier hp 1 (p*h)*(∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
          cubicThetaSectionFourierFunction F (p*h) (v/r)) := by
      rw [←integral_const_mul,←integral_const_mul,←integral_add
        (hB.const_mul (norm (p^3):ℂ)) (hU.const_mul (cubicThetaPrimeCubeUnitFourier hp 1 (p*h)))]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [hfun v hv]
      ring
    _ = _ := by
      rw [cubicThetaSectionFourier_divide_pairing F (p^3*h) hr3 W hW,
        cubicThetaSectionFourier_divide_pairing F (p*h) hr W hW1,hN3,hN]
      have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr0.ne'
      push_cast
      field_simp
      rfl

theorem cubicThetaPrimeCubeFourierPairing_energy {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) (h : Eisenstein) (hh : ¬p∣h)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    inner ℂ (cubicThetaCuspFourierTest h W)
        (cubicThetaCuspRestriction (cubicThetaPrimeCubeHeckeEnergy hp u))=
      inner ℂ (cubicThetaCuspFourierTest (p^3*h)
        (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
          (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) W))
        (cubicThetaCuspRestriction u)+
      (cubicThetaPrimeCubeUnitFourier hp 1 (p*h)/(norm p:ℂ))*
        inner ℂ (cubicThetaCuspFourierTest (p*h)
          (cubicThetaRadialWeightScale ‖(p:ℂ)‖
            (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) W))
          (cubicThetaCuspRestriction u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (continuous_const.inner (cubicThetaCuspRestriction.continuous.comp
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous))
      ((continuous_const.inner cubicThetaCuspRestriction.continuous).add
        (continuous_const.mul (continuous_const.inner cubicThetaCuspRestriction.continuous)))) ?_
  intro F
  rw [cubicThetaPrimeCubeHeckeEnergy_finite]
  change inner ℂ (cubicThetaCuspFourierTest h W)
    (cubicThetaCuspRestriction (cubicThetaFiniteEnergyEmbedding (cubicThetaPrimeCubeHeckeFinite hp F)))=_
  rw [cubicThetaCuspRestriction_finiteEnergy,cubicThetaCuspRestriction_finiteEnergy]
  exact cubicThetaPrimeCubeFourierPairing_finite hp F h hh W hW

end CubicFirstMoment

end

end OAI
