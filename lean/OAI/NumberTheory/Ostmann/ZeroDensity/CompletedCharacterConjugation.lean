import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexCharacterConjugation
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogDerivative

namespace OAI

/-! # The completed functional equation with conjugation -/

namespace Ostmann

open Complex Filter Set
open scoped ComplexConjugate Topology

theorem gammaReal_conjugate (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  have hpi : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  simp only [Complex.Gammaℝ_def, map_mul]
  have hg : Complex.Gamma (conj s / 2) = conj (Complex.Gamma (s / 2)) := by
    simpa only [map_div₀, map_ofNat] using Complex.Gamma_conj (s / 2)
  rw [hg]
  have hh := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) hpi
  simpa only [map_neg, map_div₀, map_ofNat, Complex.conj_ofReal] using
    congrArg (fun z : ℂ => z * conj (Complex.Gamma (s / 2))) hh

theorem character_even_inverse_iff {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (χ⁻¹).Even ↔ χ.Even := by
  change (χ⁻¹) (-1) = 1 ↔ χ (-1) = 1
  rw [← MulChar.star_eq_inv, MulChar.star_apply, RCLike.star_def]
  constructor
  · intro h
    have hh := congrArg conj h
    simpa only [Complex.conj_conj, map_one] using hh
  · intro h
    rw [h, map_one]

theorem PrimitiveComplexCharacter.gammaFactor_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    DirichletCharacter.gammaFactor χ.inverse.character (conj s) =
      conj (DirichletCharacter.gammaFactor χ.character s) := by
  change DirichletCharacter.gammaFactor (χ.character⁻¹) (conj s) = _
  by_cases he : χ.character.Even
  · simp only [DirichletCharacter.gammaFactor, (character_even_inverse_iff χ.character).mpr he,
      he, ite_true, gammaReal_conjugate]
  · have hi : ¬(χ.character⁻¹).Even := fun h => he ((character_even_inverse_iff χ.character).mp h)
    simpa only [DirichletCharacter.gammaFactor, he, hi, ite_false, map_add, map_one] using
      gammaReal_conjugate (s + 1)

theorem PrimitiveComplexCharacter.gammaInverse_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    χ.inverse.gammaInverse (conj s) = conj (χ.gammaInverse s) := by
  simp only [PrimitiveComplexCharacter.gammaInverse, χ.gammaFactor_inverse_conj, map_inv₀]

theorem PrimitiveComplexCharacter.completed_inverse_conj_right (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) : χ.inverse.completed (conj s) = conj (χ.completed s) := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hscne : conj s ≠ 0 := by intro h; apply hsne; simpa using congrArg conj h
  apply mul_right_cancel₀ (χ.inverse.gammaInverse_ne_zero (conj s) (by simpa using hs))
  calc
    _ = χ.inverse.L (conj s) := (χ.inverse.L_eq_completed_mul (conj s) hscne).symm
    _ = conj (χ.L s) := by
      have he := congrFun χ.inverse_L_eq_conjugate (conj s)
      simpa only [Function.comp_apply, Complex.conj_conj] using he
    _ = _ := by
      rw [χ.L_eq_completed_mul s hsne, map_mul, χ.gammaInverse_inverse_conj]

theorem PrimitiveComplexCharacter.inverse_completed_eq_conjugate (χ : PrimitiveComplexCharacter) :
    χ.inverse.completed = conj ∘ χ.completed ∘ conj := by
  have hd : Differentiable ℂ (conj ∘ χ.completed ∘ conj) := by
    intro z
    simpa only [Complex.conj_conj] using (χ.completed_analytic (conj z)).differentiableAt.conj_conj
  have hg := hd.differentiableOn.analyticOnNhd isOpen_univ
  have hf : AnalyticOnNhd ℂ χ.inverse.completed univ := fun z _ => χ.inverse.completed_analytic z
  apply hf.eq_of_eventuallyEq hg (z₀ := (2 : ℂ))
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (0 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  simpa only [Function.comp_apply, Complex.conj_conj] using
    χ.completed_inverse_conj_right (conj z) (by simpa using hz)

theorem PrimitiveComplexCharacter.completed_logDeriv_self_reflection
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.completed (1 - conj s) =
      -Complex.log (χ.modulus : ℂ) - conj (logDeriv χ.completed s) := by
  rw [χ.completed_logDeriv_reflection (conj s) (by simpa using hs),
    χ.inverse_completed_eq_conjugate, logDeriv_apply, deriv_conj_conj]
  simp only [Function.comp_apply, Complex.conj_conj, logDeriv_apply, map_div₀]

end Ostmann

end OAI
