import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothed
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareRemoval

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

theorem jacobi_lattice_dilation (q d : ℕ) (hd : d ≠ 0) (M : ℝ)
    (W : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, (jacobiSym ((d : ℤ) * m) q : ℂ) *
      W ((((d : ℤ) * m : ℤ) : ℝ) / M)) =
      (jacobiSym (d : ℤ) q : ℂ) *
        ∑' m : ℤ, (jacobiSym m q : ℂ) * W ((m : ℝ) / (M / d)) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have harg : ((((d : ℤ) * m : ℤ) : ℝ) / M) = (m : ℝ) / (M / d) := by
    push_cast
    rw [div_div_eq_mul_div]
    ring
  rw [harg, jacobiSym.mul_left, Int.cast_mul]
  ring

theorem coprime_quadratic_poisson {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q)
    (k : ℕ) (hk : k ≠ 0) (M : ℝ) (hM : 0 < M) (W : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, if Nat.Coprime m.natAbs k then
      (jacobiSym m q : ℂ) * W ((m : ℝ) / M) else 0) =
      ∑ d ∈ k.divisors, (μ d : ℂ) * (jacobiSym (d : ℤ) q : ℂ) *
        (((M / d) / q : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
          ∑' h : ℤ, (jacobiSym h q : ℂ) * 𝓕 W ((h : ℝ) * (M / d) / q) := by
  have hsum : Summable (fun m : ℤ => (jacobiSym m q : ℂ) * W ((m : ℝ) / M)) := by
    simpa only [mul_comm] using
      summable_weighted_jacobi (schwartz_summable_scaled W M hM.ne') q
  rw [coprime_tsum_moebius _ hsum k hk]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
  rw [jacobi_lattice_dilation q d hdpos.ne' M W,
    quadratic_poisson hq hsq (M / d) (div_pos hM hdr) W]
  ring

theorem gcdReducedModulus_odd {n₁ n₂ : ℕ} (h₁ : Odd n₁) (h₂ : Odd n₂) :
    Odd (gcdReducedModulus n₁ n₂) := by
  apply (h₁.mul h₂).of_dvd_nat
  rw [mul_eq_gcd_sq_mul_reduced]
  exact dvd_mul_left _ _

theorem imprimitive_jacobi_lattice (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (W : ℤ → ℂ) :
    (∑' m : ℤ, (jacobiSym m (n₁ * n₂) : ℂ) * W m) =
      ∑' m : ℤ, if Nat.Coprime m.natAbs (n₁.gcd n₂) then
        (jacobiSym m (gcdReducedModulus n₁ n₂) : ℂ) * W m else 0 := by
  apply tsum_congr
  intro m
  rw [jacobi_gcd_denominator]
  have hcop : m.gcd (n₁.gcd n₂ : ℤ) = 1 ↔ Nat.Coprime m.natAbs (n₁.gcd n₂) := by
    simp only [Int.gcd_def, Int.natAbs_natCast, Nat.coprime_iff_gcd_eq_one]
  split_ifs with h h <;> simp_all

instance gcdReducedModulus_neZero (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    NeZero (gcdReducedModulus n₁ n₂) := by
  have h : (n₁.gcd n₂) ^ 2 * gcdReducedModulus n₁ n₂ ≠ 0 := by
    rw [← mul_eq_gcd_sq_mul_reduced]
    exact mul_ne_zero (NeZero.ne n₁) (NeZero.ne n₂)
  exact ⟨(mul_ne_zero_iff.mp h).2⟩

theorem odd_imprimitive_quadratic_poisson {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (ho₁ : Odd n₁) (ho₂ : Odd n₂) (hs₁ : Squarefree n₁) (hs₂ : Squarefree n₂)
    (M : ℝ) (hM : 0 < M) (W : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, if Odd m then
      (jacobiSym m (n₁ * n₂) : ℂ) * W ((m : ℝ) / M) else 0) =
      ∑ d ∈ (2 * n₁.gcd n₂).divisors,
        (μ d : ℂ) * (jacobiSym (d : ℤ) (gcdReducedModulus n₁ n₂) : ℂ) *
          (((M / d) / gcdReducedModulus n₁ n₂ : ℝ) : ℂ) *
            gaussSum (jacobiDirichletCharacter (gcdReducedModulus n₁ n₂)) ZMod.stdAddChar *
              ∑' h : ℤ, (jacobiSym h (gcdReducedModulus n₁ n₂) : ℂ) *
                𝓕 W ((h : ℝ) * (M / d) / gcdReducedModulus n₁ n₂) := by
  have hd : 2 * n₁.gcd n₂ ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.gcd_ne_zero_left (NeZero.ne n₁))
  rw [← coprime_quadratic_poisson (gcdReducedModulus_odd ho₁ ho₂)
    (gcdReducedModulus_squarefree hs₁ hs₂) (2 * n₁.gcd n₂) hd M hM W]
  apply tsum_congr
  intro m
  rw [jacobi_gcd_denominator]
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_two_right, Int.natAbs_odd,
    Int.gcd_def, Int.natAbs_natCast, Nat.coprime_iff_gcd_eq_one]
  split_ifs <;> simp_all

end Ostmann.QuadraticSieve

end OAI
