import OAI.NumberTheory.CubicMoment.Estimates.FiniteCharacterMass
import OAI.NumberTheory.CubicMoment.Estimates.DivisorRowEnergy
import OAI.NumberTheory.CubicMoment.Estimates.HeightCoprimeContinuity

namespace OAI

/-! The exact divisor mass behind the genuine coprimality kernel, with
arbitrary squarefree coefficients and both Fourier signs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorCharacterMass (S H U : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) : ℝ :=
  ∑ d ∈ U.powerset, finiteCharacterMass (S.filter (fun a => (∏ p ∈ d, p) ∣ a)) H β u

lemma divisorCharacterMass_continuous (S H U : Finset Eisenstein) (β : Eisenstein → ℂ) :
    Continuous (divisorCharacterMass S H U β) := by
  unfold divisorCharacterMass
  exact continuous_finsetSum _ (fun _ _ => finiteCharacterMass_continuous _ _ _)

lemma divisorCharacterMass_bound (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (u : ℝ) :
    ‖divisorCharacterMass S H U β u‖ ≤
      ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d, p) ∣ a)).card*
        ∑ a ∈ S.filter (fun a => (∏ p ∈ d, p) ∣ a), ‖β a‖^2 := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  exact finiteCharacterMass_bound _ _ _ (fun a ha => hS a (Finset.mem_filter.mp ha).1) u

lemma twistedCoprimeMellinMass_eq_divisor_mass (S H U : Finset Eisenstein)
    (β : Eisenstein → ℂ) (hS : ∀ a ∈ S, primary a) (u s : ℝ)
    {N : ℝ} (hN : 0 < N) :
    twistedCoprimeMellinMass S H U β (fun a => norm a/N) u s =
      (divisorCharacterMass S H U β (u+2*Real.pi*s)+
        divisorCharacterMass S H U β (u-2*Real.pi*s))/2 := by
  unfold twistedCoprimeMellinMass coprimeMellinMass divisorCharacterMass finiteCharacterMass
  rw [← Finset.sum_add_distrib,← Finset.sum_div]
  apply congrArg (fun x : ℝ => x/2)
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply Finset.sum_congr rfl
    intro h hh
    rw [finite_character_gram_row_norm _ β (fun a ha => hS a (Finset.mem_filter.mp ha).1) h u s hN]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [finite_character_gram_reverse_row_norm _ β (fun a ha => hS a (Finset.mem_filter.mp ha).1) h u s hN]

end CubicFirstMoment

end

end OAI
