import Mathlib.Data.Nat.Factorization.Induction
import BernoulliRegular.GaussSum.QuadraticEndpoint
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussMultiplier

namespace OAI

/-! # The positive branch of the actual squarefree Jacobi Gauss sum

The prime case uses AINTLIB's quadratic Gauss-sum evaluation.
The passage to odd squarefree moduli uses the exact Chinese remainder formula.
-/

namespace Ostmann

open scoped Classical

theorem quadraticGaussMultiplier_prime {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    quadraticGaussMultiplier p = if p % 4 = 1 then 1 else Complex.I := by
  let : Fact p.Prime := ⟨hp⟩
  have hp₂ : p ≠ 2 := by intro hh; subst p; norm_num at ho
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  rw [quadraticGaussMultiplier, dite_eq_right hp.ne_zero, jacobiGaussPhase,
    jacobiComplex, jacobiCharacterInt_prime,
    BernoulliRegular.gaussSum_quadraticChar_stdAddChar p hp₂]
  split_ifs <;> simp [hs]

theorem quadraticGaussMultiplier_one : quadraticGaussMultiplier 1 = 1 := by
  simp [quadraticGaussMultiplier, jacobiGaussPhase, gaussSum, jacobiComplex,
    jacobiCharacterInt, jacobiResidue]
  change (ZMod.stdAddChar (N := 1)) (default : ZMod 1) = 1
  rw [Subsingleton.elim (default : ZMod 1) 0]
  exact (ZMod.stdAddChar (N := 1)).map_zero_eq_one

theorem quadraticGaussMultiplier_odd_squarefree {n : ℕ} (hn : Squarefree n) (ho : Odd n) :
    quadraticGaussMultiplier n = if n % 4 = 1 then 1 else Complex.I := by
  induction n using induction_on_primes with
  | zero => exact (hn.ne_zero rfl).elim
  | one => simpa using quadraticGaussMultiplier_one
  | prime_mul p n hp ih =>
    obtain ⟨hop, hon⟩ := Nat.odd_mul.mp ho
    have hpn : p.Coprime n := Nat.coprime_of_squarefree_mul hn
    rw [quadraticGaussMultiplier_mul hpn hn.of_mul_left hn.of_mul_right hop hon,
      quadraticGaussMultiplier_prime hp hop, ih hn.of_mul_right hon]
    have hpmod := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hop)
    have hnmod := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hon)
    rcases hpmod with hpmod | hpmod <;> rcases hnmod with hnmod | hnmod <;>
      simp [Nat.mul_mod, hpmod, hnmod]

end Ostmann

end OAI
