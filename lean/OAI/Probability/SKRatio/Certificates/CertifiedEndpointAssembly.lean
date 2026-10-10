import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarEnvelope
import OAI.Probability.SKRatio.Certificates.CertifiedFunctions

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma endpointK_zero_integral (β A C M Q : ℝ) : endpointK 0 =
    ∫ h, scalarFunction β A C M Q 8 h ∂fieldLaw (1/2) := by
  unfold endpointK
  norm_num only [zero_pow (by decide : (2:ℕ) ≠ 0),sub_zero]
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun h => by norm_num [scalarFunction]; ring)

lemma endpointK_one_integral (β A C M Q : ℝ) : endpointK 1 =
    ∫ h, scalarFunction β A C M Q 9 h ∂fieldLaw (1/2) := by
  unfold endpointK
  norm_num only [one_pow,sub_self,zero_add]
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun h => by norm_num [scalarFunction]; ring)

lemma endpointD_zero_integral (β A C M Q : ℝ) : endpointD 0 =
    ∫ h, scalarFunction β A C M Q 10 h ∂fieldLaw (1/2) := by
  unfold endpointD
  simp only [sub_zero]
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun h => by norm_num [scalarFunction]; ring)

lemma endpointD_prime_integral (β A C M Q : ℝ) : endpointDPrime =
    ∫ h, scalarFunction β A C M Q 11 h ∂fieldLaw (1/2) := by
  unfold endpointDPrime
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun h => by norm_num [scalarFunction]; ring)

lemma endpointD_one_integral (β A C M Q : ℝ) : endpointD 1 =
    ∫ h, scalarFunction β A C M Q 12 h ∂fieldLaw (1/2) := by
  unfold endpointD
  norm_num only [show (2:ℝ)-1=1 by norm_num]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro h
  have hd : 1-m h ≠ 0 := by linarith only [(m_bounds h).2]
  norm_num only [scalarFunction]
  rw [v_factor,w]
  field_simp
  ring

end SKRatio.Certificate

end

end OAI
