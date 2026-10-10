import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroCountRate

namespace OAI

/-! # Reflection of actual character-zero multiplicities

The library functional equation for the completed L-function is combined
with the nonvanishing reciprocal Gamma factor inside the critical strip.
-/

namespace Ostmann

open Filter Set
open scoped Topology

noncomputable def PrimitiveComplexCharacter.inverse (χ : PrimitiveComplexCharacter) :
    PrimitiveComplexCharacter := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact {
    modulus := χ.modulus
    positive := χ.positive
    character := χ.character⁻¹
    primitive := by
      simpa only [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        using χ.primitive
    nontrivial := inv_ne_one.mpr χ.nontrivial }

@[simp] theorem PrimitiveComplexCharacter.inverse_modulus (χ : PrimitiveComplexCharacter) :
    χ.inverse.modulus = χ.modulus := rfl

noncomputable def PrimitiveComplexCharacter.completed (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  @DirichletCharacter.completedLFunction χ.modulus ⟨χ.positive.ne'⟩ χ.character

noncomputable def PrimitiveComplexCharacter.gammaInverse (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  fun s => (DirichletCharacter.gammaFactor χ.character s)⁻¹

theorem PrimitiveComplexCharacter.completed_analytic (χ : PrimitiveComplexCharacter) (z : ℂ) :
    AnalyticAt ℂ χ.completed z := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact (DirichletCharacter.differentiable_completedLFunction χ.nontrivial).analyticAt z

theorem PrimitiveComplexCharacter.gammaInverse_analytic (χ : PrimitiveComplexCharacter) (z : ℂ) :
    AnalyticAt ℂ χ.gammaInverse z := by
  classical
  unfold gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.differentiable_Gammaℝ_inv.analyticAt z
  · exact (Complex.differentiable_Gammaℝ_inv.comp
      (differentiable_id.add_const (1 : ℂ))).analyticAt z

theorem PrimitiveComplexCharacter.gammaInverse_ne_zero (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 0 < z.re) : χ.gammaInverse z ≠ 0 := by
  classical
  unfold gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  · apply inv_ne_zero
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using (show 0 < z.re + 1 by linarith))

theorem PrimitiveComplexCharacter.L_eq_completed_mul (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : z ≠ 0) : χ.L z = χ.completed z * χ.gammaInverse z := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.character z (.inl hz)).trans
    (div_eq_mul_inv _ _)

theorem PrimitiveComplexCharacter.L_order_eq_completed (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 0 < z.re) : analyticOrderAt χ.L z = analyticOrderAt χ.completed z := by
  have he : χ.L =ᶠ[𝓝 z] fun s => χ.completed s * χ.gammaInverse s := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with s hs
    apply χ.L_eq_completed_mul
    intro heq
    simp [heq] at hs
  rw [analyticOrderAt_congr he]
  rw [show (fun s => χ.completed s * χ.gammaInverse s) = χ.completed * χ.gammaInverse from rfl,
    analyticOrderAt_mul (χ.completed_analytic z) (χ.gammaInverse_analytic z),
    (χ.gammaInverse_analytic z).analyticOrderAt_eq_zero.mpr (χ.gammaInverse_ne_zero z hz), add_zero]

theorem PrimitiveComplexCharacter.rootNumber_ne_zero (χ : PrimitiveComplexCharacter) :
    @DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character ≠ 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  intro hz
  have he := χ.primitive.completedLFunction_one_sub (-1)
  rw [hz, mul_zero, zero_mul] at he
  norm_num at he
  have hL := χ.L_eq_completed_mul 2 (by norm_num)
  change χ.completed 2 = 0 at he
  rw [he, zero_mul] at hL
  have hlo := χ.L_lower_re_two (2 : ℂ) (by norm_num)
  rw [hL, norm_zero] at hlo
  norm_num at hlo

end Ostmann

end OAI
