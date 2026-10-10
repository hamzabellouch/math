import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCuspObservation

namespace OAI

/-! The finite Fourier support rule survives completion and all bounded
cusp observations. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFunction_fourier {p : Eisenstein}
    (F : cubicThetaPrimeCubeRootSections p) (h : Eisenstein) (v : ℝ) (hv : 0<v) :
    cubicThetaHorizontalFourierCoefficient h (fun z => cubicThetaPrimeCubeRootFunction F (z,v))=
      cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeRootHorizontal F v hv) := by
  congr 1
  funext z
  exact cubicThetaPrimeCubeRootFunction_apply F hv

lemma cubicThetaPrimeCubeRootFinite_observation_projection {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (F : cubicThetaPrimeCubeRootFiniteSections hp) :
    cubicThetaPrimeCubeRootObservation hp h W
      (cubicThetaPrimeCubeRootFiniteEmbedding hp (cubicThetaPrimeCubeRootFiniteFourier hp k F))=
    if Ideal.Quotient.mk (modulus (p^3)) h=k then
      cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFiniteEmbedding hp F) else 0 := by
  rw [cubicThetaPrimeCubeRootFinite_observation_iterated]
  by_cases hk : Ideal.Quotient.mk (modulus (p^3)) h=k
  · rw [ite_eq_left hk,cubicThetaPrimeCubeRootFinite_observation_iterated]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    have hpos : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hv
    rw [cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos,
      cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos,
      cubicThetaPrimeCubeRootFiniteFourier_horizontal,ite_eq_left hk]
  · rw [ite_eq_right hk]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro v hv
    have hpos : 0<v := lt_trans (by norm_num : (0:ℝ)<2) hv
    rw [cubicThetaPrimeCubeRootFunction_fourier _ _ _ hpos,
      cubicThetaPrimeCubeRootFiniteFourier_horizontal,ite_eq_right hk,mul_zero]

theorem cubicThetaPrimeCubeRoot_observation_projection {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (u : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootObservation hp h W (cubicThetaPrimeCubeRootFourierL2 hp k u)=
    if Ideal.Quotient.mk (modulus (p^3)) h=k then cubicThetaPrimeCubeRootObservation hp h W u else 0 := by
  refine (cubicThetaPrimeCubeRootFiniteEmbedding_dense hp).induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootObservation hp h W).continuous.comp
      (cubicThetaPrimeCubeRootFourierL2 hp k).continuous)
      (by split_ifs <;> fun_prop)) ?_
  intro F
  rw [cubicThetaPrimeCubeRootFourierL2_finite]
  exact cubicThetaPrimeCubeRootFinite_observation_projection hp k h W F

end CubicFirstMoment

end

end OAI
