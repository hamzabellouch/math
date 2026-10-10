import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductMoment
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.WeightedSquarefreeMean
import OAI.NumberTheory.CubicMoment.Estimates.HeightSquareRoot

namespace OAI

/-! Ordinary means for the squarefree product model of stopped coefficients.
The product and norm multiplicities are both retained in an explicit fixed
divisor moment, which costs a logarithm rather than a power of the length. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma divisor_model_coefficient_energy (S : Finset Eisenstein)
    (γ : Eisenstein → ℂ) {X M : ℝ} (hX : 0 < X) (_hM : 0 ≤ M)
    (hS : ∀ n ∈ S, X ≤ norm n)
    (hγ : ∀ n ∈ S, ‖γ n‖ ≤ M*(4:ℝ)^(primaryPrimeFactors n).card) :
    (∑ n ∈ S, (4:ℝ)^(primaryPrimeFactors n).card*
      ‖γ n*((norm n^(-1/6:ℝ):ℝ):ℂ)‖^2) ≤
      M^2*X^(-1/3:ℝ)*(∑ n ∈ S, (64:ℝ)^(primaryPrimeFactors n).card) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : 0 < norm n := hX.trans_le (hS n hn)
  have hp : (norm n^(-1/6:ℝ))^2 ≤ X^(-1/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hn0.le]
    norm_num
    exact Real.rpow_le_rpow_of_nonpos hX (hS n hn) (by norm_num)
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
  calc
    _ ≤ (4:ℝ)^(primaryPrimeFactors n).card*
        ((M*(4:ℝ)^(primaryPrimeFactors n).card)^2*X^(-1/3:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _) (hγ n hn) 2) hp
        (sq_nonneg _) (sq_nonneg _)
    _ = M^2*X^(-1/3:ℝ)*((4:ℝ)^(primaryPrimeFactors n).card)^3 := by ring
    _ = _ := by
      rw [←pow_mul, Nat.mul_comm, pow_mul]
      norm_num

theorem divisor_model_height_mean (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (γ : Eisenstein → ℂ) (N : ℕ) (X T M u : ℝ),
      Real.exp 1 ≤ (N:ℝ) → 0 < X → 0 < T → 0 ≤ M →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ X ≤ norm n ∧ norm n ≤ (N:ℝ)) →
      (∀ n ∈ S, ‖γ n‖ ≤ M*(4:ℝ)^(primaryPrimeFactors n).card) →
      dyadicHeightMean (fun t => ‖dispersionModel S γ (t+u)‖^2) T ≤
        K*M^2*(1+(N:ℝ)/T)*(N:ℝ)*X^(-1/3:ℝ)*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_fixed_divisor_moment hpnt 64 (by norm_num)
  refine ⟨2*(C+1)*K,d,by positivity,?_⟩
  intro S γ N X T M u hN hX hT hM hS hγ
  let v := fun n => γ n*((norm n^(-1/6:ℝ):ℝ):ℂ)*normTwist u n
  have hi : ∀ n ∈ S, normNat n ∈ Finset.Icc 1 N := by
    intro n hn
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS n hn).1)),?_⟩
    have hb := (hS n hn).2.2.2
    rw [←normNat_cast] at hb
    exact_mod_cast hb
  have he : (fun t => ‖dispersionModel S γ (t+u)‖^2) =
      (fun t => ‖eisensteinNormPolynomial S v t‖^2) := by
    funext t
    congr 2
    unfold dispersionModel eisensteinNormPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [v]
    rw [normTwist_eq_mellinPhase,normTwist_eq_mellinPhase,mellinPhase_add]
    ring
  rw [he]
  have hev : (∑ n ∈ S, (4:ℝ)^(primaryPrimeFactors n).card*‖v n‖^2) ≤
      M^2*X^(-1/3:ℝ)*(K*(N:ℝ)*(1+Real.log N)^d) := by
    have hv : ∀ n, ‖v n‖ = ‖γ n*((norm n^(-1/6:ℝ):ℝ):ℂ)‖ := by
      intro n
      simp only [v,norm_mul,norm_normTwist,mul_one]
    simp_rw [hv]
    exact (divisor_model_coefficient_energy S γ hX hM
      (fun n hn => (hS n hn).2.2.1) hγ).trans
      (mul_le_mul_of_nonneg_left (hmoment N S hN
        (fun n hn => ⟨(hS n hn).1,(hS n hn).2.1,(hS n hn).2.2.2⟩)) (by positivity))
  apply (squarefree_weighted_dyadic_mean hMV hC hT S v N
    (fun n hn => ⟨(hS n hn).1,(hS n hn).2.1⟩) hi).trans
  have hb := mul_le_mul_of_nonneg_left hev
    (show 0 ≤ 2*C*(1+(N:ℝ)/T) by positivity)
  have hl : 0 ≤ 1+Real.log N := by
    have hn1 : 1 ≤ (N:ℝ) :=
      (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 1)).trans hN
    linarith [Real.log_nonneg hn1]
  calc
    _ ≤ 2*C*(1+(N:ℝ)/T)*(M^2*X^(-1/3:ℝ)*(K*(N:ℝ)*(1+Real.log N)^d)) := hb
    _ = 2*C*K*(M^2*(1+(N:ℝ)/T)*(N:ℝ)*X^(-1/3:ℝ)*(1+Real.log N)^d) := by ring
    _ ≤ 2*(C+1)*K*(M^2*(1+(N:ℝ)/T)*(N:ℝ)*X^(-1/3:ℝ)*(1+Real.log N)^d) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
