import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialHeckeWeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeightMultiplier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeEnergyOperator

namespace OAI

/-! The exact compact radial test duality for the actual Hecke operator,
first on finite-energy sections and then by density. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_height_ge_one {p : Eisenstein} (hp : primaryPrime p) :
    1≤‖(p:ℂ)‖^3 := by
  have hn := one_le_norm hp.2.ne_zero
  change 1≤Complex.normSq (p:ℂ) at hn
  rw [Complex.normSq_eq_norm_sq] at hn
  have hnorm := _root_.norm_nonneg (p:ℂ)
  have h1 : 1≤‖(p:ℂ)‖ := by nlinarith
  exact one_le_pow₀ h1

lemma cubicThetaPrimeCubeRadialWeight_low {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3, W v=0) :
    ∀ v≤(2:ℝ), cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3) (by
      have := cubicThetaPrimeCube_height_ge_one hp; linarith) W v=0 :=
  cubicThetaRadialHeckeWeight_low (cubicThetaPrimeCube_height_ge_one hp) (by norm_num) W hW

lemma cubicThetaPrimeCubeRadialPairing_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(p:ℂ)‖^3, W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
        (cubicThetaFiniteCuspRestriction (cubicThetaPrimeCubeHeckeFinite hp F))=
      inner ℂ (cubicThetaCuspFourierTest 0
        (cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3) (by
          have := cubicThetaPrimeCube_height_ge_one hp; linarith) W))
        (cubicThetaFiniteCuspRestriction F) := by
  let r := ‖(p:ℂ)‖^3
  have hr1 : 1≤r := cubicThetaPrimeCube_height_ge_one hp
  have hr : 0<r := by linarith
  have hW2 : ∀ v≤(2:ℝ), W v=0 := by
    intro v hv
    apply hW
    change v≤2*r
    linarith
  let A := cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W
  let B := cubicThetaRadialWeightScale r hr W
  have hA : ∀ v≤(2:ℝ), A v=0 := by
    intro v hv
    change W (r⁻¹*v)=0
    apply hW
    change r⁻¹*v≤2*r
    rw [mul_comm,←div_eq_mul_inv,div_le_iff₀ hr]
    have : 1≤r*r := by nlinarith
    nlinarith
  have hB : ∀ v≤(2:ℝ), B v=0 := by
    intro v hv
    change W (r*v)=0
    apply hW
    change r*v≤2*r
    nlinarith
  have hiA := cubicThetaRadialIntegral_integrable_zero_extension A hA
    (cubicThetaSectionMean F) (cubicThetaSectionMean_weight_integrable F A)
  have hiB := cubicThetaRadialIntegral_integrable_zero_extension B hB
    (cubicThetaSectionMean F) (cubicThetaSectionMean_weight_integrable F B)
  have hiA' : IntegrableOn (fun v => star (W (v/r))/(v:ℂ)^3*cubicThetaSectionMean F v) (Ioi (0:ℝ)) := by
    simpa only [A,cubicThetaRadialWeightScale_apply,mul_comm r⁻¹,←div_eq_mul_inv] using hiA
  have hiB' : IntegrableOn (fun v => star (W (r*v))/(v:ℂ)^3*cubicThetaSectionMean F v) (Ioi (0:ℝ)) := hiB
  have hnorm : (norm (p^3):ℂ)=(r:ℂ)^2 := by
    rw [cubicThetaPrimeCube_norm_power]
    dsimp only [r]
    push_cast
    ring
  rw [cubicThetaSectionMeanPairing_hecke,cubicThetaSectionMeanPairing,hnorm]
  change (∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*
    (cubicThetaSectionMean F (r*v)+(r:ℂ)^2*cubicThetaSectionMean F (v/r)))=
    ∫ v in Ioi (2:ℝ),star (cubicThetaRadialHeckeWeight r hr W v)/(v:ℂ)^3*cubicThetaSectionMean F v
  rw [cubicThetaRadialIntegral_zero_extension W hW2,
    cubicThetaRadialIntegral_zero_extension _ (cubicThetaPrimeCubeRadialWeight_low hp W hW),
    cubicThetaRadialIntegral_hecke r hr W _ hiA' hiB',
    cubicThetaRadialHeckeWeight_integral r hr W _ hiA' hiB']

theorem cubicThetaPrimeCubeRadialPairing_energy {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaGlobalEnergySpace) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(p:ℂ)‖^3, W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
        (cubicThetaCuspRestriction (cubicThetaPrimeCubeHeckeEnergy hp u))=
      inner ℂ (cubicThetaCuspFourierTest 0
        (cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3) (by
          have := cubicThetaPrimeCube_height_ge_one hp; linarith) W))
        (cubicThetaCuspRestriction u) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (continuous_const.inner (cubicThetaCuspRestriction.continuous.comp
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous))
      (continuous_const.inner cubicThetaCuspRestriction.continuous)) ?_
  intro F
  rw [cubicThetaPrimeCubeHeckeEnergy_finite]
  change inner ℂ (cubicThetaCuspFourierTest 0 W)
    (cubicThetaCuspRestriction (cubicThetaFiniteEnergyEmbedding (cubicThetaPrimeCubeHeckeFinite hp F)))=_
  rw [cubicThetaCuspRestriction_finiteEnergy,cubicThetaCuspRestriction_finiteEnergy]
  exact cubicThetaPrimeCubeRadialPairing_finite hp F W hW

end CubicFirstMoment

end

end OAI
