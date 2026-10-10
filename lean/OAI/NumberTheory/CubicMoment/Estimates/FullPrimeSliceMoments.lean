import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSlice
import OAI.NumberTheory.CubicMoment.Estimates.DilatedNoncubeSieve
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicPrimeWeights

namespace OAI

/-! Shortened energies and all three sieve orientations for the literal
quotient coefficients β(fn). These are used for common-factor tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPrimeSliceSum (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (f e h v : Eisenstein) (ℓ : ℤ) (u : ℝ) : ℂ :=
  ∑ n ∈ fullPrimeSliceSupport R W X f e,
    fullPrimeCoefficient R W X (f*n)*theta ℓ n*mellinPhase u (norm n)*cubicSymbol n (v*h)

lemma fullPrime_slice_twisted_energy (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (f e v : Eisenstein) (ℓ : ℤ) (u : ℝ) :
    (∑ n ∈ fullPrimeSliceSupport R W X f e,
      ‖fullPrimeCoefficient R W X (f*n)*theta ℓ n*mellinPhase u (norm n)*cubicSymbol n v‖^2) ≤
    ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hp := (fullPrimeSliceSupport_bounds R W X f e hn).1
  rw [norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero hp),mellinPhase_norm,mul_one,mul_one]
  exact pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    (mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hp v)) 2

theorem logarithmic_full_slice_energy {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 0 ≤ X i) → (∏ i, X i) = L r → ∀ f e : Eisenstein,
      (∑ n ∈ fullPrimeSliceSupport R (W r) X f e, ‖fullPrimeCoefficient R (W r) X (f*n)‖^2) ≤
        C*(L r/norm f)*(1+Real.log (L r))^A := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let C := 18*R^n*((n^n:ℕ)*M^n)^2
  refine ⟨C,2*m*n,by dsimp [C]; positivity,?_⟩
  intro r X hL hX hprod f e
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hb := fullPrime_slice_energy (zero_le_one.trans hR) (W r) X
    (fun _ => M*(1+Real.log (L r))^m) hX
    (fun _ => mul_nonneg hM (pow_nonneg hz _)) (fun i x => hMb (r,i) x) f e
  apply hb.trans_eq
  rw [hprod,Finset.prod_const,Finset.card_univ,mul_pow,← pow_mul]
  dsimp only [C,n]
  rw [mul_pow,mul_pow,← pow_mul]
  have hm : m*(Fintype.card ι*2) = 2*m*Fintype.card ι := by ring
  rw [hm,pow_mul M (Fintype.card ι) 2]
  ring

end CubicFirstMoment

end

end OAI
