import OAI.NumberTheory.CubicMoment.Estimates.DivisorPoissonRadial
import OAI.NumberTheory.CubicMoment.Estimates.PoissonAbsoluteDyad

namespace OAI

/-! The square-divisor character can be absorbed into the original
coefficient. Its norm never increases, including at noncoprime inputs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorTwistedCoefficient (d : Eisenstein) (β : Eisenstein → ℂ)
    (a : Eisenstein) : ℂ := β a*star (cubicSymbol a (d^2))

lemma divisorTwistedCoefficient_norm_le (d : Eisenstein) (β : Eisenstein → ℂ)
    {a : Eisenstein} (ha : primary a) :
    ‖divisorTwistedCoefficient d β a‖ ≤ ‖β a‖ := by
  rw [divisorTwistedCoefficient,norm_mul,norm_star]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one ha _)

theorem finiteDivisorPoissonContribution_twist (d : Eisenstein)
    (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    finiteDivisorPoissonContribution d S H β u W A =
      finitePoissonContribution S H (divisorTwistedCoefficient d β) u W (A/(norm d)^2) := by
  unfold finiteDivisorPoissonContribution finitePoissonContribution
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,divisorTwistedCoefficient,star_mul,star_star,mixedSymbol]
    ring
  · simp only [ite_eq_right hab]

theorem finiteDivisorPoissonContribution_absolute (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L D J : ℝ), 0 < A → 0 < L → L ≤ D → 0 ≤ J →
      ∀ (d : Eisenstein), d ≠ 0 → ∀ (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ L ≤ norm a ∧ norm a ≤ D) →
      (∀ h ∈ H, J ≤ norm h) → ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖finiteDivisorPoissonContribution d S H β u V A‖ ≤
        C*((A/(norm d)^2)/(9*L))*(H.card:ℝ)*(∑ a ∈ S, ‖β a‖)^2/
          (1+(A/(norm d)^2)*J/(27*D^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finitePoissonContribution_absolute V hV hV' m
  refine ⟨C,hC,?_⟩
  intro A L D J hA hL hLD hJ d hd S H hS hH β u
  have hdN := norm_pos_of_ne_zero hd
  rw [finiteDivisorPoissonContribution_twist]
  apply (hbound (A/(norm d)^2) L D J (by positivity) hL hLD hJ S H hS hH
    (divisorTwistedCoefficient d β) u).trans
  have he : (∑ a ∈ S, ‖divisorTwistedCoefficient d β a‖)^2 ≤ (∑ a ∈ S, ‖β a‖)^2 := by
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
    exact Finset.sum_le_sum (fun a ha => divisorTwistedCoefficient_norm_le d β (hS a ha).1)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)

end CubicFirstMoment

end

end OAI
