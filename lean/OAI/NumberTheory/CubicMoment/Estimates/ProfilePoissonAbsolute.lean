import OAI.NumberTheory.CubicMoment.Estimates.ProfilePoissonEntry
import OAI.NumberTheory.CubicGram.DyadicRecurrence

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment.ProfileControl

theorem finitePoissonContribution_absolute (P : PoissonProfileBudget) (m : ℕ) (hm : m ≤ 47)
    (A L D J : ℝ) (hA : 0 < A) (hL : 0 < L) (hLD : L ≤ D) (hJ : 0 ≤ J)
    (S H : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ L ≤ norm a ∧ norm a ≤ D)
    (hH : ∀ h ∈ H, J ≤ norm h) (β : Eisenstein → ℂ) (u : ℝ) :
    ‖finitePoissonContribution S H β u P.V A‖ ≤
      P.cost*(A/(9*L))*(H.card:ℝ)*(∑ a ∈ S, ‖β a‖)^2/(1+A*J/(27*D^2))^m := by
  let C := P.cost
  have hC : 0 < C := P.cost_pos
  have hentry := poisson_entry_decay P m hm
  let E := (A/(9*L))*C/(1+A*J/(27*D^2))^m
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpair (h a b : Eisenstein) (hh : h ∈ H) (ha : a ∈ S) (hb : b ∈ S) :
      ‖(if IsCoprime a b then
        (β a*normTwist u a)*star (β b*normTwist u b)*
          (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a P.V A h else 0)‖ ≤
        ‖β a‖*‖β b‖*E := by
    split_ifs
    · have heq : (β a*normTwist u a)*star (β b*normTwist u b)*
          (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a P.V A h =
        ((β a*normTwist u a)*star (β b*normTwist u b))*
          ((A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a P.V A h) := by ring
      rw [heq,norm_mul]
      simp only [norm_mul,norm_star,norm_normTwist,mul_one]
      have hp := hentry A L D J hA hL hLD hJ a b h (hS a ha).1 (hS b hb).1
        (hS a ha).2.1 (hS a ha).2.2 (hS b hb).2.1 (hS b hb).2.2 (hH h hh)
      simp only [norm_mul] at hp
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    · simp only [norm_zero]
      positivity
  unfold finitePoissonContribution
  calc
    _ ≤ ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, ‖β a‖*‖β b‖*E := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro h hh
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun b hb => hpair h a b hh ha hb)
    _ = _ := by
      simp only [← Finset.mul_sum,← Finset.sum_mul,Finset.sum_const,nsmul_eq_mul]
      dsimp [E]
      ring

end CubicFirstMoment.ProfileControl

end

end OAI
