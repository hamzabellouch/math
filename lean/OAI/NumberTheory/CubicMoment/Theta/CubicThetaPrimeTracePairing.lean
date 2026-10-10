import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyValue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaContractionPairing

namespace OAI

/-! The constructed finite-cover trace is adjoint to the normalized
lift, both for the energy and mass pairings on actual completed spaces. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeNormalizedTraceEnergy_mass_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaGlobalInclusion (cubicThetaPrimeNormalizedTraceEnergy hp F)‖≤
      ‖cubicThetaPrimeEnergyValue hp F‖ := by
  let d : ℝ := (cubicThetaPrimeCoverGroup hp).index
  have hd : 0<d := cubicThetaPrimeCoverDegree_pos hp
  have hc : ‖((Real.sqrt d)⁻¹:ℂ)‖^2*d=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,inv_pow,sq_abs,Real.sq_sqrt hd.le,
      inv_mul_cancel₀ hd.ne']
  apply _root_.le_of_sq_le_sq _ (_root_.norm_nonneg _)
  change ‖cubicThetaGlobalInclusion (((Real.sqrt d)⁻¹:ℂ) • cubicThetaPrimeRawTraceEnergy hp F)‖^2≤_
  rw [map_smul,norm_smul,mul_pow]
  calc
    _ ≤ ‖((Real.sqrt d)⁻¹:ℂ)‖^2*(d*‖cubicThetaPrimeEnergyValue hp F‖^2) :=
      mul_le_mul_of_nonneg_left (cubicThetaPrimeTraceFinite_value_norm_sq hp F) (sq_nonneg _)
    _ = _ := by rw [←mul_assoc,hc,one_mul]

theorem cubicThetaPrimeTraceEnergy_mass_bound {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) :
    ‖cubicThetaGlobalInclusion (cubicThetaPrimeTraceEnergy hp u)‖≤
      ‖cubicThetaPrimeEnergyInclusion hp u‖ := by
  refine (cubicThetaPrimeEnergyTest_dense hp).induction_on u
    (isClosed_le (cubicThetaGlobalInclusion.continuous.comp
      (cubicThetaPrimeTraceEnergy hp).continuous).norm
      (cubicThetaPrimeEnergyInclusion hp).continuous.norm) ?_
  intro F
  rw [cubicThetaPrimeTraceEnergy_finite,cubicThetaPrimeEnergyInclusion_test]
  exact cubicThetaPrimeNormalizedTraceEnergy_mass_bound hp F

theorem cubicThetaPrimeTraceEnergy_pairing {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaPrimeTraceEnergy hp u) v=
      inner ℂ u (cubicThetaPrimeLiftEnergy hp v) := by
  apply cubicTheta_inner_of_norm_shear _ _ _ _ ((cubicThetaPrimeLiftEnergy hp).norm_map v).symm
  intro c
  have h := cubicThetaPrimeTraceEnergy_bound hp (u+c • cubicThetaPrimeLiftEnergy hp v)
  simpa only [map_add,map_smul,cubicThetaPrimeTraceEnergy_lift] using h

theorem cubicThetaPrimeTraceEnergy_mass_pairing {p : Eisenstein} (hp : primaryPrime p)
    (u : cubicThetaPrimeEnergySpace hp) (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaPrimeTraceEnergy hp u)) (cubicThetaGlobalInclusion v)=
      inner ℂ (cubicThetaPrimeEnergyInclusion hp u)
        (cubicThetaPrimeEnergyInclusion hp (cubicThetaPrimeLiftEnergy hp v)) := by
  have hn : ‖cubicThetaGlobalInclusion v‖=
      ‖cubicThetaPrimeEnergyInclusion hp (cubicThetaPrimeLiftEnergy hp v)‖ := by
    change ‖cubicThetaGlobalEnergyValueMap v‖=
      ‖cubicThetaPrimeEnergyValueMap hp (cubicThetaPrimeLiftEnergy hp v)‖
    rw [cubicThetaPrimeLiftEnergy_value,(cubicThetaPrimeLiftL2 hp).norm_map]
  apply cubicTheta_inner_of_norm_shear _ _ _ _ hn
  intro c
  have h := cubicThetaPrimeTraceEnergy_mass_bound hp (u+c • cubicThetaPrimeLiftEnergy hp v)
  simpa only [map_add,map_smul,cubicThetaPrimeTraceEnergy_lift] using h

end CubicFirstMoment

end

end OAI
