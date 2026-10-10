import OAI.NumberTheory.CubicMoment.Estimates.CoprimeDispersionPoisson
import OAI.NumberTheory.CubicMoment.Estimates.HeightPoissonTotal

namespace OAI

/-! Identify the complete nonzero dyadic Poisson series with the
original coprime portion of the dispersion Gram form. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coprimeDispersionGram_eq_poisson_series (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a ∧ a ≠ 1)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) {A : ℝ} (hA : 0 < A) :
    coprimeDispersionGram S β u V A =
      ∑' j : ℕ, finitePoissonContribution S (frequencyDyad j) β u V A := by
  let G := fun (a b h : Eisenstein) => if IsCoprime a b then
    (β a*normTwist u a)*star (β b*normTwist u b)*
      (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0
  let F := fun h => ∑ a ∈ S, ∑ b ∈ S, G a b h
  have hG (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S) : Summable (G a b) := by
    by_cases hab : IsCoprime a b
    · simpa only [G,ite_eq_left hab] using
        (summable_gramDualTerm (hS b hb).1 (hS a ha).1 V hV hV' hA).mul_left
          ((β a*normTwist u a)*star (β b*normTwist u b)*(A/(9*Real.sqrt (norm (b*a))):ℝ))
    · simp only [G,ite_eq_right hab]
      exact summable_zero
  have hF : Summable F := summable_sum (fun a ha => summable_sum (fun b hb => hG a b ha hb))
  have hF0 : F 0 = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hab : IsCoprime a b
    · have hne : b ≠ a := by
        intro hba
        exact (hS a ha).2.2 (primary_unit_eq_one (isCoprime_self.mp (hba ▸ hab)) (hS a ha).1)
      simp only [G,ite_eq_left hab,
        gramDualTerm_zero (hS b hb).1 (hS a ha).1 (hS b hb).2.1 (hS a ha).2.1 hab.symm hne V A,
        mul_zero]
    · simp only [G,ite_eq_right hab]
  have hb := hasSum_frequencyDyad F hF hF0
  change HasSum (fun j => finitePoissonContribution S (frequencyDyad j) β u V A) (∑' h, F h) at hb
  rw [hb.tsum_eq]
  rw [show (∑' h, F h) = ∑ a ∈ S, ∑ b ∈ S, ∑' h, G a b h from by
    dsimp only [F]
    rw [Summable.tsum_finsetSum (fun a ha => summable_sum (fun b hb => hG a b ha hb))]
    exact Finset.sum_congr rfl (fun a ha => Summable.tsum_finsetSum (fun b hb => hG a b ha hb))]
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [G,ite_eq_left hab,tsum_mul_left]
    rw [dispersion_pair_poisson (hS a ha).1 (hS b hb).1 (hS a ha).2.1 (hS b hb).2.1
      hab β u V hV hV' hA]
    simp only [star_mul]
    ring
  · simp only [G,ite_eq_right hab,tsum_zero]

end CubicFirstMoment

end

end OAI
