import Mathlib.NumberTheory.MulChar.Lemmas
import OAI.NumberTheory.SiegelZeros.Structure.AffineAssembly

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W51

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem realCharacter_inv_eq_self (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ⁻¹ = χ := by
  have hs : star χ = χ := by
    ext a
    exact Complex.conj_eq_iff_im.mpr (hreal a)
  exact (MulChar.star_eq_inv χ).symm.trans hs

theorem normalizedCompletion_reflection (χ : DirichletCharacter ℂ q)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) (z : ℂ) :
    normalizedCompletion χ (1 - z) =
      DirichletCharacter.rootNumber χ * normalizedCompletion χ z := by
  simpa only [realCharacter_inv_eq_self χ hreal] using
    normalizedCompletion_one_sub χ hprimitive z

theorem analyticOrderAt_normalizedCompletion_reflection (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (z : ℂ) :
    analyticOrderAt (normalizedCompletion χ) (1 - z) =
      analyticOrderAt (normalizedCompletion χ) z := by
  have heq : normalizedCompletion χ ∘ (fun w : ℂ => 1 - w) =
      (fun _ : ℂ => DirichletCharacter.rootNumber χ) * normalizedCompletion χ := by
    funext w
    exact normalizedCompletion_reflection χ hprimitive hreal w
  have hslope : deriv (fun w : ℂ => 1 - w) z ≠ 0 := by
    have hd : HasDerivAt (fun w : ℂ => 1 - w) (-1) z :=
      (hasDerivAt_id z).const_sub (1 : ℂ)
    rw [hd.deriv]
    exact neg_ne_zero.mpr one_ne_zero
  rw [← analyticOrderAt_comp_of_deriv_ne_zero (f := normalizedCompletion χ)
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) z) hslope, heq,
    analyticOrderAt_mul analyticAt_const
      ((differentiable_normalizedCompletion χ hχ).analyticAt z),
    (analyticOrderAt_eq_zero (f := fun _ : ℂ => DirichletCharacter.rootNumber χ)
      (z₀ := z)).mpr (Or.inr (rootNumber_ne_zero χ hχ hprimitive)), zero_add]

def reflectionRootEquiv (χ : DirichletCharacter ℂ q)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    {z : ℂ // normalizedCompletion χ z = 0} ≃
      {z : ℂ // normalizedCompletion χ z = 0} where
  toFun r := ⟨1 - r.val, by rw [normalizedCompletion_reflection χ hprimitive hreal,
    r.property, mul_zero]⟩
  invFun r := ⟨1 - r.val, by rw [normalizedCompletion_reflection χ hprimitive hreal,
    r.property, mul_zero]⟩
  left_inv := by intro r; apply Subtype.ext; simp
  right_inv := by intro r; apply Subtype.ext; simp

def reflectionZeroIndexEquiv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    ZeroIndex χ ≃ ZeroIndex χ :=
  Equiv.sigmaCongr (reflectionRootEquiv χ hprimitive hreal) (fun r =>
    Equiv.cast (congrArg Fin
      (congrArg ENat.toNat
        (analyticOrderAt_normalizedCompletion_reflection χ hχ hprimitive hreal r.val)).symm))

theorem zeroValue_reflectionZeroIndex (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) (i : ZeroIndex χ) :
    zeroValue χ (reflectionZeroIndexEquiv χ hχ hprimitive hreal i) = 1 - zeroValue χ i := rfl

theorem real_zero_sum_at_one_eq_correction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    (∑' i : ZeroIndex χ, ((1 - zeroValue χ i)⁻¹).re) =
      ∑' i : ZeroIndex χ, ((zeroValue χ i)⁻¹).re := by
  simpa only [zeroValue_reflectionZeroIndex] using
    (reflectionZeroIndexEquiv χ hχ hprimitive hreal).tsum_eq
      (fun i : ZeroIndex χ => ((zeroValue χ i)⁻¹).re)

end SiegelZerosAwei.W51

end

end SiegelZeros

end OAI
