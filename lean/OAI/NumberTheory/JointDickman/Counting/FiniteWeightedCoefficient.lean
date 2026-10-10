import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightCountPrefix

namespace OAI

/-! # The actual coefficient with a fixed finite-prime weight -/
namespace JointDickman
open Finset
open scoped Classical

noncomputable def finiteWeightedCoefficient (f : ArithmeticFunction ℂ)
    (E : Finset ℕ) (w : ℕ → ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n*(finitePrimeWeight E w n:ℂ),by simp⟩

lemma finiteWeightedCoefficient_multiplicative (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (w : ℕ → ℝ) :
    (finiteWeightedCoefficient f E w).IsMultiplicative := by
  have hw := finitePrimeWeight_multiplicative hE w
  refine ⟨?_,?_⟩
  · change f 1*(finitePrimeWeight E w 1:ℂ)=1
    rw [hf.1,hw.1]
    simp
  · intro m n hcop
    change f (m*n)*(finitePrimeWeight E w (m*n):ℂ)=
      (f m*(finitePrimeWeight E w m:ℂ))*(f n*(finitePrimeWeight E w n:ℂ))
    rw [hf.2 hcop,hw.2 hcop,Complex.ofReal_mul]
    ring

lemma finiteWeightedCoefficient_norm (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {E : Finset ℕ} {w : ℕ → ℝ}
    (hw : ∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) (n : ℕ) :
    ‖finiteWeightedCoefficient f E w n‖ ≤ 1 := by
  change ‖f n*(finitePrimeWeight E w n:ℂ)‖ ≤ 1
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (finitePrimeWeight_bounds hw n).1]
  exact (mul_le_mul (hf n) (finitePrimeWeight_bounds hw n).2
    (finitePrimeWeight_bounds hw n).1 zero_le_one).trans_eq (mul_one 1)

lemma finitePrimeWeight_prime_outside {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime)
    (w : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (hpE : p ∉ E) :
    finitePrimeWeight E w p = 1 := by
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hp.ne_zero,ite_false]
  apply prod_eq_one
  intro q hq
  apply ite_eq_right
  intro hd
  have he : q=p := ((Nat.dvd_prime hp).mp hd).resolve_left (hE q hq).ne_one
  exact hpE (he ▸ hq)

lemma finiteWeightedCoefficient_prime_outside {f : ArithmeticFunction ℂ}
    {E : Finset ℕ} (hE : ∀ p ∈ E, p.Prime) (w : ℕ → ℝ)
    {p : ℕ} (hp : p.Prime) (hpE : p ∉ E) :
    finiteWeightedCoefficient f E w p = f p := by
  change f p*(finitePrimeWeight E w p:ℂ)=f p
  rw [finitePrimeWeight_prime_outside hE w hp hpE]
  simp

end JointDickman

end OAI
