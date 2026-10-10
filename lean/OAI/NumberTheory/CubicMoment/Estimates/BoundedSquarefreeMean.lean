import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeNormFiber
import OAI.NumberTheory.CubicMoment.Estimates.ArbitraryHeightMean

namespace OAI

/-! Ordinary height means with a logarithmic loss for bounded squarefree
coefficients. No maximum norm-fiber bound or small power of the length occurs. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma normPolynomial_dyadic_energy {C T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hT : 0 < T)
    (S : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) :
    dyadicHeightMean (fun t => ‖eisensteinNormPolynomial S v t‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff S v n‖^2) := by
  unfold dyadicHeightMean
  simp_rw [normPolynomial_collected S v Z hZ]
  have hp := hMV Z (normCollectedCoeff S v) T (2*T) (by linarith)
  have hn := hMV Z (normCollectedCoeff S v) (-2*T) (-T) (by linarith)
  apply (div_le_div_of_nonneg_right (add_le_add hp hn) hT.le).trans_eq
  field_simp
  ring

theorem bounded_squarefree_height_mean (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (Z : ℕ) (T M : ℝ), Real.exp 1 ≤ (Z:ℝ) → 0 < T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖v b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖eisensteinNormPolynomial S v t‖^2) T ≤
        K*M^2*(1+(Z:ℝ)/T)*(Z:ℝ)*(1+Real.log Z)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_divisor_second_moment hpnt
  refine ⟨2*(C+1)*K,d,by positivity,?_⟩
  intro S v Z T M hZ hT hM hS hv
  have hindex : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z := by
    intro b hb
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS b hb).1)),?_⟩
    have hnorm := (hS b hb).2.2
    rw [←normNat_cast b] at hnorm
    exact_mod_cast hnorm
  have henergy := (normCollectedCoeff_squarefree_energy S
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) v hM hv Z hindex).trans
    (mul_le_mul_of_nonneg_left (hmoment Z S hZ hS) (sq_nonneg M))
  have hb := normPolynomial_dyadic_energy hMV hT S v Z hindex
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ 2*C*(1+(Z:ℝ)/T) by positivity)
  have hx : 0 ≤ M^2*(1+(Z:ℝ)/T)*(Z:ℝ)*(1+Real.log Z)^d := by
    have hz1 : 1 ≤ (Z:ℝ) := (by linarith [Real.add_one_le_exp (1:ℝ)] : 1 ≤ Real.exp 1).trans hZ
    have hl : 0 ≤ 1+Real.log Z := by linarith [Real.log_nonneg hz1]
    positivity
  have he : 2*C*K ≤ 2*(C+1)*K := by nlinarith
  have hh' := mul_le_mul_of_nonneg_right he hx
  nlinarith only [hh,hh']

theorem bounded_squarefree_character_height (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (T M u : ℝ) (ℓ : ℤ), Real.exp 1 ≤ (Z:ℝ) → 0 < T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        K*M^2*(1+(Z:ℝ)/T)*(Z:ℝ)*(1+Real.log Z)^d*H.card := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_squarefree_height_mean hpnt hMV hC
  refine ⟨K,d,hK,?_⟩
  intro S H β Z T M u ℓ hZ hT hM hS hβ
  rw [dyadicHeightMean_sum H
    (fun h t => ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2)
    (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)]
  have hrow (h : Eisenstein) :
      dyadicHeightMean (fun t =>
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        K*M^2*(1+(Z:ℝ)/T)*(Z:ℝ)*(1+Real.log Z)^d := by
    let v := fun b => β b*cubicSymbol b h*theta ℓ b*mellinPhase u (norm b)
    have hv : ∀ b ∈ S, ‖v b‖ ≤ M := by
      intro b hb
      dsimp [v]
      rw [norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero (hS b hb).1),mellinPhase_norm,mul_one,mul_one]
      exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS b hb).1 h)).trans (hβ b hb)
    have he : (fun t => ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) =
        (fun t => ‖eisensteinNormPolynomial S v t‖^2) := by
      funext t
      congr 2
      unfold eisensteinNormPolynomial
      apply Finset.sum_congr rfl
      intro b _
      rw [mellinPhase_add]
      dsimp [v]
      ring
    rw [he]
    exact hbound S v Z T M hZ hT hM hS hv
  apply (Finset.sum_le_sum (fun h _ => hrow h)).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
