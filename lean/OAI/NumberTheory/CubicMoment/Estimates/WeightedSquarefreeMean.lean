import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeNormFiber
import OAI.NumberTheory.CubicMoment.Estimates.BoundedSquarefreeMean

namespace OAI

/-! A weighted norm-fiber mean. The divisor weight is retained explicitly
so coprimality rows can later be summed without a uniform-fiber loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma normCollectedCoeff_squarefree_weighted_energy (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) (v : Eisenstein → ℂ) (Z : ℕ)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) :
    (∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff S v n‖^2) ≤
      ∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖v b‖^2 := by
  have hf (n : ℕ) : ‖normCollectedCoeff S v n‖^2 ≤
      ∑ b ∈ S.filter (fun b => normNat b = n), (4:ℝ)^(primaryPrimeFactors b).card*‖v b‖^2 := by
    apply (norm_sum_sq_le_card_mul _ v).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hbs := (Finset.mem_filter.mp hb).1
    have he : S.filter (fun c => normNat c = n) = S.filter (fun c => normNat c = normNat b) := by
      rw [(Finset.mem_filter.mp hb).2]
    have hcard : ((S.filter (fun c => normNat c = n)).card:ℝ) ≤
        (4:ℝ)^(primaryPrimeFactors b).card := by
      rw [he]
      exact_mod_cast squarefree_norm_fiber_card S hS (hS b hbs).1 (hS b hbs).2
    exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  exact (Finset.sum_le_sum (fun n _ => hf n)).trans_eq
    (Finset.sum_fiberwise_of_maps_to hZ _)

lemma squarefree_weighted_meanSquare {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (S : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, ‖eisensteinNormPolynomial S v t‖^2) ≤
      C*(b-a+Z)*(∑ c ∈ S, (4:ℝ)^(primaryPrimeFactors c).card*‖v c‖^2) := by
  simp_rw [normPolynomial_collected S v Z hZ]
  exact (hMV Z (normCollectedCoeff S v) a b hab).trans
    (mul_le_mul_of_nonneg_left (normCollectedCoeff_squarefree_weighted_energy S hS v Z hZ)
      (mul_nonneg hC (by positivity)))

lemma squarefree_weighted_dyadic_mean {C T : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hT : 0 < T) (S : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) :
    dyadicHeightMean (fun t => ‖eisensteinNormPolynomial S v t‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖v b‖^2) := by
  exact (normPolynomial_dyadic_energy hMV hT S v Z hZ).trans
    (mul_le_mul_of_nonneg_left (normCollectedCoeff_squarefree_weighted_energy S hS v Z hZ)
      (by positivity))

lemma squarefree_weighted_character_height {C T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hT : 0 < T)
    (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) (u : ℝ) (ℓ : ℤ) :
    dyadicHeightMean (fun t => ∑ h ∈ H,
      ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*H.card := by
  have hindex : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z := by
    intro b hb
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS b hb).1)),?_⟩
    have hn := (hS b hb).2.2
    rw [←normNat_cast b] at hn
    exact_mod_cast hn
  rw [dyadicHeightMean_sum H
    (fun h t => ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2)
    (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)]
  have hrow (h : Eisenstein) :
      dyadicHeightMean (fun t =>
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) := by
    let v := fun b => β b*cubicSymbol b h*theta ℓ b*mellinPhase u (norm b)
    have hv : ∀ b ∈ S, ‖v b‖ ≤ ‖β b‖ := by
      intro b hb
      dsimp [v]
      rw [norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero (hS b hb).1),mellinPhase_norm,mul_one,mul_one]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS b hb).1 h)
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
    apply (squarefree_weighted_dyadic_mean hMV hC hT S v Z
      (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) hindex).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (_root_.norm_nonneg _) (hv b hb) 2) (by positivity)
  apply (Finset.sum_le_sum (fun h _ => hrow h)).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
