import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedLow
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSlice
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra

namespace OAI

/-! The mixed-term replacement for the literal logarithmic prime
convolution, including its norm phase. Coefficient size is derived from
the fixed number of prime factors and the actual weight family. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem logarithmic_prime_typeI_mixed
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {γ : Type*} {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    {δ : Type*} {V : δ → ℝ → ℂ} (hVw : UniformLogWeights V)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {B : ℝ} (hB : 1 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : γ) (Xi : ι → ℝ) (R₀ : ℝ)
      (w : Eisenstein → δ) (S : Finset Eisenstein) (t X R U : ℝ),
      1 ≤ L j → L j ≤ X → 2 ≤ X → B ≤ X → 1 ≤ R → 1 ≤ U →
      R*U = X → R ≤ X^(51/100:ℝ) →
      (∀ r ∈ S, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      (∀ r ∈ S, ∀ x : ℝ, B < x → V (w r) x = 0) →
      let β := fun r => fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r
      ‖∑ r ∈ S, β r*(typeIMixedGauss r (V (w r)) U-typeIMixedModel r (V (w r)) U)‖ ≤
        K*U^(-1/6:ℝ)*X^(5/6-1/100:ℝ) := by
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let D : ℝ := (n^n:ℕ)*M^n
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hM _)
  obtain ⟨K,hK,hbound⟩ := typeI_mixed_low_of_published hV hVw hGamma hB hD 0 (m*n)
  refine ⟨K,hK,?_⟩
  intro j Xi R₀ w S t X R U hL hLX hX hBX hR hU hRU hRhi hS hcut
  apply hbound w S _ X R U hX hBX hR hU hRU hRhi hS hcut
  intro r hr
  have hz : 0 ≤ 1+Real.log (L j) := by linarith [Real.log_nonneg hL]
  have hlog : 1+Real.log (L j) ≤ 1+Real.log X := by
    linarith [Real.log_le_log (zero_lt_one.trans_le hL) hLX]
  have hb := fullPrimeCoefficient_norm_bound R₀ (W j) Xi
    (fun _ => M*(1+Real.log (L j))^m)
    (fun _ => mul_nonneg hM (pow_nonneg hz _)) (fun i x => hMb (j,i) x) r
  calc
    ‖fullPrimeCoefficient R₀ (W j) Xi r*normTwist t r‖ =
        ‖fullPrimeCoefficient R₀ (W j) Xi r‖ := by rw [norm_mul,norm_normTwist,mul_one]
    _ ≤ D*(1+Real.log (L j))^(m*n) := by
      simpa only [D,n,Finset.prod_const,Finset.card_univ,mul_pow,←pow_mul,mul_assoc] using hb
    _ ≤ D*(1+Real.log X)^(m*n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hlog _) hD
    _ = D*((metaplecticPrimaryDivisors r).card:ℝ)^0*(1+Real.log X)^(m*n) := by simp

end CubicFirstMoment

end

end OAI
