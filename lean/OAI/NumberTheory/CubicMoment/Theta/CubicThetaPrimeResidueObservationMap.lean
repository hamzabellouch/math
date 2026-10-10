import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedResidueObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueTestWeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueObstruction

namespace OAI

/-! A concrete bounded observation map for the three critical local
coordinates of the actual spectral residue. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaFourierObservationCLM (h : Eisenstein) (W : C_c(ℝ,ℂ)) :
    cubicThetaGlobalEnergySpace →L[ℂ] ℂ :=
  (innerSL ℂ (cubicThetaCuspFourierTest h W)).comp cubicThetaCuspRestriction

def cubicThetaPrimeResidueObservationMap {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : cubicThetaGlobalEnergySpace →L[ℂ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi (fun i =>
    (norm (p^i.val):ℂ)⁻¹ • cubicThetaFourierObservationCLM (p^i.val*h)
      (cubicThetaRadialWeightScale ‖((p^i.val:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero i.val hp.2.ne_zero) (Subtype.ext he)))
        (cubicThetaPrimeResidueTestWeight hp)))

lemma cubicThetaPrimeResidueTestWeight_low_power {p : Eisenstein} (hp : primaryPrime p)
    (i : Fin 3) {v : ℝ} (hv : v≤2*‖((p^i.val:Eisenstein):ℂ)‖) :
    cubicThetaPrimeResidueTestWeight hp v=0 := by
  apply cubicThetaPrimeResidueTestWeight_low hp
  rw [Subalgebra.coe_pow,norm_pow] at hv
  have hr : 1≤‖(p:ℂ)‖ := by
    have hn := one_le_norm hp.2.ne_zero
    change 1≤Complex.normSq (p:ℂ) at hn
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [_root_.norm_nonneg (p:ℂ)]
  fin_cases i <;> norm_num at hv ⊢ <;> nlinarith

lemma cubicThetaPrimeCriticalScale_power (p : Eisenstein) (i : Fin 3) :
    (norm (p^i.val):ℂ)^(-(1/3:ℂ))=(cubicThetaPrimeCriticalScale p)^i.val := by
  fin_cases i
  · simp [norm_one_eq]
  · simp [cubicThetaPrimeCriticalScale]
  · change (norm (p^2):ℂ)^(-(1/3:ℂ))=(cubicThetaPrimeCriticalScale p)^2
    rw [pow_two,norm_mul_eq,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg p) (norm_nonneg p)]
    rw [pow_two]
    rfl

def cubicThetaPrimeResidueCommonFactor {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) : ℂ :=
  (Real.pi:ℂ)/Complex.Gamma (4/3)*
    cubicThetaFourierRadialTest h (cubicThetaPrimeResidueTestWeight hp) (4/3)

lemma cubicThetaPrimeResidueCommonFactor_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    {h : Eisenstein} (hh : h≠0) : cubicThetaPrimeResidueCommonFactor hp h≠0 := by
  apply mul_ne_zero
  · exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  · exact cubicThetaPrimeResidueTestWeight_radial_ne_zero hp hh

theorem cubicThetaPrimeResidueObservationMap_residue {p : Eisenstein} (hp : primaryPrime p)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaPrimeResidueObservationMap hp h (cubicThetaArithmeticResidueEnergy (4/3))=
      cubicThetaPrimeResidueCommonFactor hp h • cubicThetaPrimeResidueVector p h := by
  ext i
  change (norm (p^i.val):ℂ)⁻¹*inner ℂ _
    (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=_
  rw [cubicThetaNormalizedResidue_observation_mul (pow_ne_zero i.val hp.2.ne_zero) hh
    (cubicThetaPrimeResidueTestWeight hp)
    (fun _ hv => cubicThetaPrimeResidueTestWeight_low_power hp i hv),
    cubicThetaPrimeCriticalScale_power p i]
  have he : cubicThetaPrimeResidueVector p h i=
      (cubicThetaPrimeCriticalScale p)^i.val*cubicThetaArithmeticFourierResidue (p^i.val*h) (4/3) := by
    fin_cases i <;> simp [cubicThetaPrimeResidueVector]
  change cubicThetaPrimeResidueCommonFactor hp h*_=
    cubicThetaPrimeResidueCommonFactor hp h*cubicThetaPrimeResidueVector p h i
  rw [he]

end CubicFirstMoment

end

end OAI
