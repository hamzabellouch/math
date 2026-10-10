import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaContour
import OAI.NumberTheory.Ostmann.Characters.CharacterLogDerivativeRight

namespace OAI

/-! # The functional equation at the level of logarithmic derivatives -/

namespace Ostmann

open Complex
open scoped Classical

theorem PrimitiveComplexCharacter.L_eq_completed_mul_all (χ : PrimitiveComplexCharacter) :
    χ.L = χ.completed * χ.gammaInverse := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : χ.modulus ≠ 1 := fun h => χ.nontrivial (DirichletCharacter.level_one' χ.character h)
  funext s
  exact (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.character s (.inr hq)).trans
    (div_eq_mul_inv _ _)

theorem PrimitiveComplexCharacter.logDeriv_L_eq_completed_add
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : χ.L s ≠ 0) :
    logDeriv χ.L s = logDeriv χ.completed s + logDeriv χ.gammaInverse s := by
  have he := congrFun χ.L_eq_completed_mul_all s
  change χ.L s = χ.completed s * χ.gammaInverse s at he
  have hne : χ.completed s ≠ 0 ∧ χ.gammaInverse s ≠ 0 :=
    mul_ne_zero_iff.mp (he ▸ hs)
  rw [χ.L_eq_completed_mul_all,
    logDeriv_mul s hne.1 hne.2 (χ.completed_analytic s).differentiableAt
      (χ.gammaInverse_analytic s).differentiableAt]

theorem PrimitiveComplexCharacter.completed_ne_zero_right
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) : χ.completed s ≠ 0 := by
  have h := χ.L_ne_zero_one_le_re s hs
  rw [χ.L_eq_completed_mul_all] at h
  exact (mul_ne_zero_iff.mp h).1

theorem PrimitiveComplexCharacter.completed_logDeriv_reflection
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.completed (1 - s) =
      -Complex.log (χ.modulus : ℂ) - logDeriv χ.inverse.completed s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let G : ℂ → ℂ := fun z => (χ.modulus : ℂ) ^ (z - 1 / 2) *
    DirichletCharacter.rootNumber χ.character
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hp := ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_cpow (.inl hq)
  simp only [id_eq, mul_one] at hp
  have hpne : (χ.modulus : ℂ) ^ (s - 1 / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hq)
  have hG : DifferentiableAt ℂ G s := hp.differentiableAt.mul_const _
  have hGne : G s ≠ 0 := mul_ne_zero hpne χ.rootNumber_ne_zero
  have hGlog : logDeriv G s = Complex.log (χ.modulus : ℂ) := by
    rw [show G = (fun z => (χ.modulus : ℂ) ^ (z - 1 / 2) *
      DirichletCharacter.rootNumber χ.character) from rfl,
      logDeriv_mul_const s _ χ.rootNumber_ne_zero, logDeriv_apply, hp.deriv]
    rw [mul_div_right_comm, div_self hpne, one_mul]
  have he : χ.completed ∘ (fun z => 1 - z) = G * χ.inverse.completed := by
    funext z
    exact χ.primitive.completedLFunction_one_sub z
  have hl := congrArg (fun f : ℂ → ℂ => logDeriv f s) he
  rw [logDeriv_comp (χ.completed_analytic (1 - s)).differentiableAt
      ((hasDerivAt_id s).const_sub 1).differentiableAt,
    logDeriv_mul s hGne (χ.inverse.completed_ne_zero_right s hs) hG
      (χ.inverse.completed_analytic s).differentiableAt, hGlog] at hl
  have hd : deriv (fun z : ℂ => 1 - z) s = -1 := by
    simp
  rw [hd] at hl
  linear_combination -hl

end Ostmann

end OAI
