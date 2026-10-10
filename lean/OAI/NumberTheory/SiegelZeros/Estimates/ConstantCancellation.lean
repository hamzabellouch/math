import OAI.NumberTheory.SiegelZeros.EntireFunctions.ReflectionZeros

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W51

variable {q : ℕ} [NeZero q]

theorem normalizedCompletion_zero_ne (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) : normalizedCompletion χ 0 ≠ 0 := by
  intro hz
  have h := (normalizedCompletion_zero_mem_strip χ hχ hprimitive hz).1
  simp only [Complex.zero_re, lt_self_iff_false] at h

theorem actual_zero_sum_convergence (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) {z : ℂ} (hz : normalizedCompletion χ z ≠ 0) :
    Summable (fun i : ZeroIndex χ => (z - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹) ∧
    Summable (fun i : ZeroIndex χ => ((zeroValue χ i)⁻¹).re) ∧
    Summable (fun i : ZeroIndex χ => ((z - zeroValue χ i)⁻¹).re) := by
  obtain ⟨C, hC, hgrowth⟩ :=
    SiegelZerosAwei.Workers.W01.normalizedCompletion_order_one_growth χ hχ
  exact W03.actual_zero_sums_summable_of_growth χ hχ hprimitive hC.le hgrowth hz

theorem logDeriv_canonicalProduct (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) {z : ℂ} (hz : normalizedCompletion χ z ≠ 0) :
    logDeriv (canonicalProduct χ) z =
      ∑' i : ZeroIndex χ, ((z - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹) := by
  obtain ⟨C, hC, hgrowth⟩ :=
    SiegelZerosAwei.Workers.W01.normalizedCompletion_order_one_growth χ hχ
  exact W03.actual_canonicalProduct_logDeriv_of_growth χ hχ hprimitive hC.le hgrowth hz

theorem logDeriv_normalizedCompletion_one_eq_neg_zero
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) :
    logDeriv (normalizedCompletion χ) 1 = -logDeriv (normalizedCompletion χ) 0 := by
  have heq : normalizedCompletion χ ∘ (fun w : ℂ => 1 - w) =
      (fun w : ℂ => DirichletCharacter.rootNumber χ * normalizedCompletion χ w) := by
    funext w
    exact normalizedCompletion_reflection χ hprimitive hreal w
  have h := congrArg (fun f : ℂ → ℂ => logDeriv f 0) heq
  change logDeriv (normalizedCompletion χ ∘ (fun w : ℂ => 1 - w)) 0 =
    logDeriv (fun w : ℂ => DirichletCharacter.rootNumber χ * normalizedCompletion χ w) 0 at h
  have hd : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_sub (1 : ℂ)
  rw [logDeriv_comp (f := normalizedCompletion χ) (g := fun w : ℂ => 1 - w)
    (differentiable_normalizedCompletion χ hχ (1 - 0)) hd.differentiableAt,
    logDeriv_const_mul 0 _ (rootNumber_ne_zero χ hχ hprimitive)] at h
  have hneg : -logDeriv (normalizedCompletion χ) 1 = logDeriv (normalizedCompletion χ) 0 := by
    simpa only [hd.deriv, sub_zero, mul_neg_one] using h
  calc
    logDeriv (normalizedCompletion χ) 1 = -(-logDeriv (normalizedCompletion χ) 1) := by simp
    _ = -logDeriv (normalizedCompletion χ) 0 := congrArg Neg.neg hneg

theorem logDeriv_normalizedCompletion_of_affine
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (A B : ℂ)
    (haffine : ∀ z, normalizedCompletion χ z = Complex.exp (A + B * z) * canonicalProduct χ z)
    {z : ℂ} (hz : normalizedCompletion χ z ≠ 0) :
    logDeriv (normalizedCompletion χ) z = B +
      ∑' i : ZeroIndex χ, ((z - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹) := by
  have hd : HasDerivAt (fun w : ℂ => Complex.exp (A + B * w))
      (Complex.exp (A + B * z) * B) z := by
    convert (((hasDerivAt_id z).const_mul B).const_add A).cexp using 1 <;> simp
  have he : logDeriv (fun w : ℂ => Complex.exp (A + B * w)) z = B := by
    rw [logDeriv_apply, hd.deriv]
    field_simp [Complex.exp_ne_zero]
  have hfun : normalizedCompletion χ =
      (fun w => Complex.exp (A + B * w)) * canonicalProduct χ := funext haffine
  rw [hfun, logDeriv_mul (f := fun w : ℂ => Complex.exp (A + B * w))
    (g := canonicalProduct χ) z (Complex.exp_ne_zero (A + B * z))
    (canonicalProduct_ne_zero_of_normalizedCompletion_ne_zero χ hχ hprimitive hz)
    hd.differentiableAt (differentiable_canonicalProduct χ hχ hprimitive z),
    he, logDeriv_canonicalProduct χ hχ hprimitive hz]

theorem logDeriv_normalizedCompletion_zero_of_affine
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (A B : ℂ)
    (haffine : ∀ z, normalizedCompletion χ z = Complex.exp (A + B * z) * canonicalProduct χ z) :
    logDeriv (normalizedCompletion χ) 0 = B := by
  simpa using logDeriv_normalizedCompletion_of_affine χ hχ hprimitive A B haffine
    (normalizedCompletion_zero_ne χ hχ hprimitive)

theorem real_hadamard_constant_cancels
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (A B : ℂ)
    (haffine : ∀ z, normalizedCompletion χ z = Complex.exp (A + B * z) * canonicalProduct χ z) :
    B.re + (∑' i : ZeroIndex χ, ((zeroValue χ i)⁻¹).re) = 0 := by
  have hne : normalizedCompletion χ 1 ≠ 0 :=
    normalizedCompletion_ne_zero_of_one_le_re χ hχ (by simp)
  have hs := actual_zero_sum_convergence χ hχ hprimitive hne
  have hlog : logDeriv (normalizedCompletion χ) 1 = -B := by
    rw [logDeriv_normalizedCompletion_one_eq_neg_zero χ hχ hprimitive hreal,
      logDeriv_normalizedCompletion_zero_of_affine χ hχ hprimitive A B haffine]
  have h := congrArg Complex.re
    (logDeriv_normalizedCompletion_of_affine χ hχ hprimitive A B haffine hne)
  have hre : (∑' i : ZeroIndex χ, ((1 - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹)).re =
      ∑' i : ZeroIndex χ, ((1 - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹).re :=
    Complex.reCLM.map_tsum hs.1
  rw [hlog, Complex.neg_re, Complex.add_re, hre,
    W03.real_regularized_tsum (zeroValue χ) 1 hs.1 hs.2.1,
    real_zero_sum_at_one_eq_correction χ hχ hprimitive hreal] at h
  linarith

theorem real_logDeriv_normalizedCompletion_eq_zero_sum_of_affine
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (A B : ℂ)
    (haffine : ∀ z, normalizedCompletion χ z = Complex.exp (A + B * z) * canonicalProduct χ z)
    {z : ℂ} (hz : normalizedCompletion χ z ≠ 0) :
    (logDeriv (normalizedCompletion χ) z).re =
      ∑' i : ZeroIndex χ, ((z - zeroValue χ i)⁻¹).re := by
  have hs := actual_zero_sum_convergence χ hχ hprimitive hz
  have h := congrArg Complex.re
    (logDeriv_normalizedCompletion_of_affine χ hχ hprimitive A B haffine hz)
  have hre : (∑' i : ZeroIndex χ, ((z - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹)).re =
      ∑' i : ZeroIndex χ, ((z - zeroValue χ i)⁻¹ + (zeroValue χ i)⁻¹).re :=
    Complex.reCLM.map_tsum hs.1
  rw [Complex.add_re, hre, W03.real_regularized_tsum (zeroValue χ) z hs.1 hs.2.1] at h
  have hc := real_hadamard_constant_cancels χ hχ hprimitive hreal A B haffine
  linarith

end SiegelZerosAwei.W51

end

end SiegelZeros

end OAI
