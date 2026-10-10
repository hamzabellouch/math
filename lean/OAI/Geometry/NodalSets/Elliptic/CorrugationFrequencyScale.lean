import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Geometry
open Filter Real
open scoped Topology
noncomputable section

def corrugationFrequency (k : ℕ) : ℝ := ((k:ℝ)+1)^8

def corrugationSubdivision (k : ℕ) : ℕ := (k+1)^2

def corrugationScale (L : ℝ) (k : ℕ) : ℝ := L/(corrugationSubdivision k:ℝ)

lemma corrugationScale_formula (L : ℝ) (k : ℕ) :
    corrugationScale L k = L/((k:ℝ)+1)^2 := by
  simp [corrugationScale,corrugationSubdivision]

lemma corrugationFrequency_positive (k : ℕ) : 0 < corrugationFrequency k := by
  unfold corrugationFrequency
  positivity

lemma corrugationSubdivision_positive (k : ℕ) : 0 < corrugationSubdivision k := by
  unfold corrugationSubdivision
  positivity

lemma corrugationScale_positive {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 < corrugationScale L k := by
  rw [corrugationScale_formula]
  positivity

lemma corrugationFrequency_eighth (k : ℕ) :
    (corrugationFrequency k)^((1:ℝ)/8) = (k:ℝ)+1 := by
  rw [corrugationFrequency,← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
  norm_num

lemma corrugationScale_exact (L : ℝ) (k : ℕ) :
    corrugationScale L k = L*(corrugationFrequency k)^(-(1:ℝ)/4) := by
  rw [corrugationScale_formula,corrugationFrequency,← Real.rpow_natCast ((k:ℝ)+1) 8,
    ← Real.rpow_mul (by positivity)]
  norm_num
  rw [div_eq_mul_inv]

lemma corrugation_scale_rate_identities {L : ℝ} (hL : L ≠ 0) (k : ℕ) :
    (corrugationScale L k)^2*(corrugationFrequency k)^((1:ℝ)/8) = L^2/((k:ℝ)+1)^3 ∧
    (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ = (L^2)⁻¹/((k:ℝ)+1)^4 ∧
    (corrugationFrequency k*corrugationScale L k)⁻¹ = L⁻¹/((k:ℝ)+1)^6 ∧
    corrugationFrequency k*corrugationScale L k = L*((k:ℝ)+1)^6 := by
  rw [corrugationFrequency_eighth,corrugationScale_formula,corrugationFrequency]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp

lemma corrugation_power_reciprocal_tendsto (C : ℝ) {p : ℕ} (hp : p ≠ 0) :
    Tendsto (fun k : ℕ ↦ C/((k:ℝ)+1)^p) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ ↦ (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hp' := (tendsto_pow_atTop hp).comp hk
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def,Pi.inv_apply] using hp'.inv_tendsto_atTop.const_mul C

lemma corrugationScale_tendsto (L : ℝ) :
    Tendsto (corrugationScale L) atTop (𝓝 0) := by
  change Tendsto (fun k ↦ corrugationScale L k) atTop (𝓝 0)
  simp_rw [corrugationScale_formula]
  exact corrugation_power_reciprocal_tendsto L (by norm_num)

lemma corrugation_frequency_scale_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun k ↦ corrugationFrequency k*corrugationScale L k) atTop atTop := by
  have hk : Tendsto (fun k : ℕ ↦ (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  simp_rw [(corrugation_scale_rate_identities hL.ne' _).2.2.2]
  exact ((tendsto_pow_atTop (by norm_num : (6:ℕ) ≠ 0)).comp hk).const_mul_atTop hL

end
end Yau.Geometry

end OAI
