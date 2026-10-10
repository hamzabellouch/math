import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootObservationProjection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCuspLift
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDilationL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierRadialScaling

namespace OAI

/-! Exact observation scaling under the once-cubic dilation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialIntegral_scaled_weight (r : ℝ) (hr : 1≤r)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*r,W v=0) (f : ℝ → ℂ) :
    (∫ v in Ioi (2:ℝ),star (cubicThetaRadialWeightScale r (lt_of_lt_of_le zero_lt_one hr) W v)/
      (v:ℂ)^3*f (r*v))=(r:ℂ)^2*∫ v in Ioi (2:ℝ),star (W v)/(v:ℂ)^3*f v := by
  have hr0 : 0<r := lt_of_lt_of_le zero_lt_one hr
  let V := cubicThetaRadialWeightScale r hr0 W
  have hV : ∀ v≤(2:ℝ),V v=0 := by
    intro v hv
    change W (r*v)=0
    exact hW _ (by nlinarith)
  have hW2 : ∀ v≤(2:ℝ),W v=0 := fun v hv => hW v (by linarith)
  rw [cubicThetaRadialIntegral_zero_extension V hV,
    cubicThetaRadialIntegral_zero_extension W hW2,cubicThetaRadialIntegral_dilate r hr0 V f]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v _
  change star (W (r*(v/r)))/(v:ℂ)^3*f v=star (W v)/(v:ℂ)^3*f v
  rw [mul_div_cancel₀ v hr0.ne']

lemma cubicThetaPrimeCube_height_one {p : Eisenstein} (hp : primaryPrime p) :
    1≤‖(p:ℂ)‖^3 := by
  have hn := one_le_norm hp.2.ne_zero
  change 1≤Complex.normSq (p:ℂ) at hn
  rw [Complex.normSq_eq_norm_sq] at hn
  have hr : 1≤‖(p:ℂ)‖ := by nlinarith [_root_.norm_nonneg (p:ℂ)]
  exact one_le_pow₀ hr

lemma cubicThetaPrimeCubeRootFinite_observation_dilation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0)
    (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootObservation hp (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W)
      (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F))=
      ((‖(p:ℂ)‖^3:ℝ):ℂ)^2*inner ℂ (cubicThetaCuspFourierTest h W)
        (cubicThetaFiniteCuspRestriction (cubicThetaSmoothToFiniteEnergy F)) := by
  rw [cubicThetaPrimeCubeRootFinite_observation_iterated,cubicThetaSectionFourierPairing]
  calc
    _ = ∫ v in Ioi (2:ℝ),star (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W v)/(v:ℂ)^3*
          cubicThetaSectionFourierFunction F h (‖(p:ℂ)‖^3*v) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      have hpos : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hv
      congr 1
      rw [cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos]
      change cubicThetaHorizontalFourierCoefficient (p^3*h) (fun z =>
        F.val.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) •
          cubicThetaHorizontalPoint v hpos z))=_
      rw [cubicThetaPrimeCubeDilation_fourier hp,←cubicThetaSectionFourierFunction_eq]
    _ = _ := cubicThetaRadialIntegral_scaled_weight (‖(p:ℂ)‖^3)
      (cubicThetaPrimeCube_height_one hp) W hW (cubicThetaSectionFourierFunction F h)

theorem cubicThetaPrimeCubeRoot_observation_dilation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0)
    (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeRootObservation hp (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W)
      (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalEnergyValueMap u))=
      ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
        ((‖(p:ℂ)‖^3:ℝ):ℂ)^2*inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspRestriction u) := by
  let L := (cubicThetaPrimeCubeRootObservation hp (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W)).comp
    ((cubicThetaPrimeCubeRootDilationL2 hp).toContinuousLinearMap.comp cubicThetaGlobalEnergyValueMap)
  let R := (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
    ((‖(p:ℂ)‖^3:ℝ):ℂ)^2) • (innerSL ℂ (cubicThetaCuspFourierTest h W)).comp cubicThetaCuspRestriction
  change L u=R u
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq L.continuous R.continuous) ?_
  intro F
  change cubicThetaPrimeCubeRootObservation hp (p^3*h) _
    (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F)))=_
  rw [cubicThetaGlobalEnergyValueMap_test,cubicThetaPrimeCubeRootDilationL2_smooth]
  change cubicThetaPrimeCubeRootObservation hp (p^3*h) _
    (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ) •
      cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootSmoothDilation hp F))=_
  rw [map_smul,cubicThetaPrimeCubeRootFinite_observation_dilation hp h W hW F]
  change _=(((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
    ((‖(p:ℂ)‖^3:ℝ):ℂ)^2)*inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction (cubicThetaGlobalEnergyTest F))
  rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaCuspRestriction_finiteEnergy]
  simp only [smul_eq_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
