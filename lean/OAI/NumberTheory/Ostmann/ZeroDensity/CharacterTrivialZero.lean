import Mathlib.NumberTheory.LSeries.Nonvanishing
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroReflection

namespace OAI

/-! # The residue at the origin in the primitive explicit formula -/

namespace Ostmann

open Filter
open scoped Topology Classical

theorem gammaReal_inverse_factor (s : ℂ) :
    (Complex.Gammaℝ s)⁻¹ = s * ((2 * (Real.pi : ℂ))⁻¹ * (Complex.Gammaℝ (s + 2))⁻¹) := by
  by_cases hs : s = 0
  · subst s
    simp [Complex.Gammaℝ_def, Complex.Gamma_zero]
  rw [Complex.Gammaℝ_add_two hs]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hs,
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem gammaReal_inverse_order_zero :
    analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 = 1 := by
  let H : ℂ → ℂ := fun s => (2 * (Real.pi : ℂ))⁻¹ * (Complex.Gammaℝ (s + 2))⁻¹
  have hH : AnalyticAt ℂ H 0 :=
    ((Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2)).const_mul _).analyticAt 0
  have hHne : H 0 ≠ 0 := by
    dsimp only [H]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
      (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)))
  have he : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) = (fun s => s) * H := by
    funext s
    exact gammaReal_inverse_factor s
  rw [he]
  change analyticOrderAt (id * H) 0 = 1
  rw [analyticOrderAt_mul analyticAt_id hH, hH.analyticOrderAt_eq_zero.mpr hHne, add_zero]
  simp

theorem PrimitiveComplexCharacter.completed_order_zero (χ : PrimitiveComplexCharacter) :
    analyticOrderAt χ.completed 0 = 0 := by
  rw [show (0 : ℂ) = 1 - 1 by ring, χ.completed_order_reflection]
  rw [← χ.inverse.L_order_eq_completed 1 (by norm_num)]
  apply (χ.inverse.L_analytic 1).analyticOrderAt_eq_zero.mpr
  let : NeZero χ.inverse.modulus := ⟨χ.inverse.positive.ne'⟩
  exact DirichletCharacter.LFunction_apply_one_ne_zero χ.inverse.nontrivial

theorem PrimitiveComplexCharacter.L_order_at_zero (χ : PrimitiveComplexCharacter) :
    analyticOrderAt χ.L 0 = if χ.character.Even then 1 else 0 := by
  classical
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : χ.modulus ≠ 1 := fun h => χ.nontrivial (DirichletCharacter.level_one' χ.character h)
  have he : χ.L = χ.completed * χ.gammaInverse := by
    funext s
    exact (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.character s (.inr hq)).trans
      (div_eq_mul_inv _ _)
  rw [he, analyticOrderAt_mul (χ.completed_analytic 0) (χ.gammaInverse_analytic 0),
    χ.completed_order_zero, zero_add]
  by_cases hχ : χ.character.Even
  · simp only [hχ, ↓reduceIte]
    change analyticOrderAt (fun s => (DirichletCharacter.gammaFactor χ.character s)⁻¹) 0 = 1
    simp_rw [hχ.gammaFactor_def]
    exact gammaReal_inverse_order_zero
  · simp only [hχ, ↓reduceIte]
    apply (χ.gammaInverse_analytic 0).analyticOrderAt_eq_zero.mpr
    simp [PrimitiveComplexCharacter.gammaInverse, DirichletCharacter.gammaFactor, hχ,
      Complex.Gammaℝ_one]

theorem PrimitiveComplexCharacter.L_multiplicity_at_zero (χ : PrimitiveComplexCharacter) :
    analyticOrderNatAt χ.L 0 = if χ.character (-1) = 1 then 1 else 0 := by
  classical
  unfold analyticOrderNatAt
  rw [χ.L_order_at_zero]
  split_ifs <;> simp_all [DirichletCharacter.Even]

end Ostmann

end OAI
