import OAI.NumberTheory.Ostmann.QuadraticCenter.SignedQuadraticFrequency
import OAI.NumberTheory.Ostmann.QuadraticSieve.ComplexJacobiPrimitive
import OAI.NumberTheory.Ostmann.Arithmetic.CRTPhaseLift

namespace OAI

/-! # The exact square-root normalization in the quadratic Poisson formula -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform

noncomputable def jacobiGaussPhase (M : ℕ) [NeZero M] : ℂ :=
  gaussSum (jacobiComplex M) ZMod.stdAddChar / (Real.sqrt (M : ℝ) : ℂ)

theorem jacobiGaussPhase_norm (M : ℕ) [NeZero M]
    (hM : Squarefree M) (hodd : Odd M) : ‖jacobiGaussPhase M‖ = 1 := by
  have hp : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hh := primitive_gauss_norm_sq (jacobiComplex M)
    (jacobiComplex_squarefree_primitive M hM hodd)
  have hs : ‖gaussSum (jacobiComplex M) ZMod.stdAddChar‖ = Real.sqrt (M : ℝ) := by
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (M : ℝ),
      norm_nonneg (gaussSum (jacobiComplex M) ZMod.stdAddChar)]
  rw [jacobiGaussPhase, norm_div, hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hp).ne']

theorem poisson_sqrt_normalizer (d M : ℕ) [NeZero d] [NeZero M]
    (X : ℝ) (hX : 0 < X) :
    (X : ℂ) / M * (Real.sqrt (d : ℝ) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ) / (Real.sqrt (M : ℝ) : ℂ) *
        (Real.sqrt ((M : ℝ) / X * d) : ℂ)⁻¹ := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hxC : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  have hmC : (Real.sqrt (M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  have hdC : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  have hmc : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hx : (Real.sqrt X : ℂ) ^ 2 = X := by exact_mod_cast Real.sq_sqrt hX.le
  have hm : (Real.sqrt (M : ℝ) : ℂ) ^ 2 = M := by exact_mod_cast Real.sq_sqrt hM.le
  rw [Real.sqrt_mul (div_nonneg hM.le hX.le), Real.sqrt_div hM.le]
  push_cast
  field_simp
  rw [hx, hm, mul_comm]

/-- The scalar outside the signed frequency sum has modulus sqrt(X).
The translation is the actual CRT lift, not an independent phase parameter. -/
theorem normalized_jacobi_poisson {d M : ℕ} [NeZero d] [NeZero M]
    (hcop : d.Coprime M) (hM : Squarefree M) (hodd : Odd M)
    (f : ZMod d → ℂ) (t : ZMod M) (h₀ : ℕ)
    (hlift : (d : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, f (n : ZMod d) * (jacobiSym ((n : ℤ) - t.val) M : ℂ) *
        ψ ((n : ℝ) / X)) =
      (Real.sqrt X : ℂ) * jacobiGaussPhase M * (realJacobi d M : ℂ) *
        ((Real.sqrt ((M : ℝ) / X * d) : ℂ)⁻¹ *
          ∑' u : ℤ, integerQuadraticFrequency (densityFourier f)
            (-(M : ZMod d)⁻¹) ((h₀ : ℝ) + (t.val : ℝ) / M)
            (𝓕 ψ) ((M : ℝ) / X) M u) := by
  have hp := scaled_quadratic_character_poisson hcop f (jacobiComplex M)
    (jacobiComplex_squarefree_primitive M hM hodd) (jacobiComplex_isQuadratic M) t ψ X hX
  have ht (n : ℤ) : (jacobiComplex M) ((n : ZMod M) - t) =
      (jacobiSym (n - t.val) M : ℂ) := by
    rw [show (n : ZMod M) - t = ((n - t.val : ℤ) : ZMod M) by simp]
    exact jacobiComplex_intCast M _
  simp_rw [ht] at hp
  rw [hp]
  have hs : (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d : (0 : ℝ) < d)).ne'
  have he (u : ℤ) :
      𝓕 ψ ((u : ℝ) * X / (d * M : ℕ)) *
        additiveFourier f (-((M : ZMod d)⁻¹ * (u : ZMod d))) *
        ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (u : ZMod M))) *
        jacobiComplex M (d : ZMod M) * jacobiComplex M (u : ZMod M) =
      ((realJacobi d M : ℂ) * (Real.sqrt (d : ℝ) : ℂ)⁻¹) *
        integerQuadraticFrequency (densityFourier f) (-(M : ZMod d)⁻¹)
          ((h₀ : ℝ) + (t.val : ℝ) / M) (𝓕 ψ) ((M : ℝ) / X) M u := by
    have harg : (u : ℝ) * X / (d * M : ℕ) = u / ((M : ℝ) / X * d) := by
      have hm : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
      push_cast
      field_simp
    rw [crt_translation_phase hcop t (h₀ : ℤ) u hlift,
      jacobiComplex_natCast, jacobiComplex_intCast, harg]
    simp only [integerQuadraticFrequency, densityFourier, neg_mul, Int.cast_natCast,
      add_comm (h₀ : ℝ)]
    field_simp
  simp_rw [he]
  rw [tsum_mul_left]
  calc
    _ = ((X : ℂ) / M * (Real.sqrt (d : ℝ) : ℂ)⁻¹) *
        gaussSum (jacobiComplex M) ZMod.stdAddChar * (realJacobi d M : ℂ) *
        ∑' u : ℤ, integerQuadraticFrequency (densityFourier f) (-(M : ZMod d)⁻¹)
          ((h₀ : ℝ) + (t.val : ℝ) / M) (𝓕 ψ) ((M : ℝ) / X) M u := by ring
    _ = _ := by
      rw [poisson_sqrt_normalizer d M X hX]
      unfold jacobiGaussPhase
      ring

end Ostmann

end OAI
