import Mathlib.RingTheory.Coprime.Lemmas
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPairKernel
import OAI.NumberTheory.Ostmann.Arithmetic.ScaledPoisson

namespace OAI

/-! # Exact Poisson summation for a pair of quadratic coefficients

The squarefree kernel is primitive. The common-divisor coprimality factor
remains in the Fourier transform as the principal character modulo the gcd.
No prime or squarefree terms are discarded.
-/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem principal_character_intCast {d : ℕ} (m : ℤ) :
    (1 : DirichletCharacter ℂ d) (m : ZMod d) =
      if m.gcd d = 1 then 1 else 0 := by
  have hu : IsUnit (m : ZMod d) ↔ m.gcd d = 1 := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  split_ifs with hm
  · exact MulChar.one_apply (hu.mpr hm)
  · exact (1 : DirichletCharacter ℂ d).map_nonunit (fun h => hm (hu.mp h))

 theorem jacobi_pair_complex {n₁ n₂ : ℕ} (h₁ : Squarefree n₁)
    (h₂ : Squarefree n₂) [NeZero (quadraticPairKernel n₁ n₂)] (m : ℤ) :
    (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) =
      (1 : DirichletCharacter ℂ (n₁.gcd n₂)) (m : ZMod (n₁.gcd n₂)) *
      jacobiComplex (quadraticPairKernel n₁ n₂) (m : ZMod (quadraticPairKernel n₁ n₂)) := by
  rw [principal_character_intCast, jacobiComplex_intCast, ← Int.cast_mul,
    jacobi_pair_kernel h₁ h₂]
  split_ifs <;> simp

 theorem quadratic_pair_poisson {n₁ n₂ : ℕ} (h₁ : Squarefree n₁)
    (h₂ : Squarefree n₂) (ho₁ : Odd n₁) (ho₂ : Odd n₂)
    [NeZero (n₁.gcd n₂)] [NeZero (quadraticPairKernel n₁ n₂)]
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' m : ℤ, (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) * ψ ((m : ℝ) / X)) =
      (X : ℂ) / quadraticPairKernel n₁ n₂ *
      gaussSum (jacobiComplex (quadraticPairKernel n₁ n₂)) ZMod.stdAddChar *
      ∑' h : ℤ, 𝓕 ψ ((h : ℝ) * X / (n₁.gcd n₂ * quadraticPairKernel n₁ n₂ : ℕ)) *
        additiveFourier (1 : DirichletCharacter ℂ (n₁.gcd n₂))
          (-((quadraticPairKernel n₁ n₂ : ZMod (n₁.gcd n₂))⁻¹ * (h : ZMod (n₁.gcd n₂)))) *
        jacobiComplex (quadraticPairKernel n₁ n₂) (n₁.gcd n₂ : ZMod (quadraticPairKernel n₁ n₂)) *
        jacobiComplex (quadraticPairKernel n₁ n₂) (h : ZMod (quadraticPairKernel n₁ n₂)) := by
  simp_rw [jacobi_pair_complex h₁ h₂]
  have hp := scaled_quadratic_character_poisson
    (quadraticPairKernel_coprime_gcd h₁ h₂)
    (1 : DirichletCharacter ℂ (n₁.gcd n₂))
    (jacobiComplex (quadraticPairKernel n₁ n₂))
    (jacobiComplex_squarefree_primitive _ (quadraticPairKernel_squarefree h₁ h₂)
      (quadraticPairKernel_odd ho₁ ho₂))
    (jacobiComplex_isQuadratic _) 0 ψ X hX
  simpa only [sub_zero, zero_mul, AddChar.map_zero_eq_one, mul_one] using hp

end Ostmann

end OAI
