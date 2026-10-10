import OAI.NumberTheory.CubicMoment.Estimates.SmallBMellin
import OAI.NumberTheory.CubicMoment.Estimates.GramStructuredRows
import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra

namespace OAI

/-! Arbitrary finite cubic-character rows and their exact Mellin twists. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def finiteCharacterMass (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) : ℝ :=
  ∑ h ∈ H, ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase u (norm a)‖^2

lemma finiteCharacterMass_nonneg (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) :
    0 ≤ finiteCharacterMass S H β u := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma finiteCharacterMass_continuous (S H : Finset Eisenstein) (β : Eisenstein → ℂ) :
    Continuous (finiteCharacterMass S H β) := by
  unfold finiteCharacterMass
  apply continuous_finsetSum
  intro h hh
  convert (continuous_finite_character_height S β h 0 0).norm.pow 2 using 1
  ext t
  simp only [Pi.pow_apply,theta_zero,mul_one,add_zero]

lemma finiteCharacterMass_bound (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (u : ℝ) :
    ‖finiteCharacterMass S H β u‖ ≤ (H.card:ℝ)*S.card*∑ a ∈ S, ‖β a‖^2 := by
  simpa only [finiteCharacterMass,theta_zero,mul_one] using
    finite_character_mass_bound S H β hS 0 u

lemma finite_character_gram_row_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (h : Eisenstein) (u s : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      star (gramMellinPhase s (norm a/N))*star (cubicSymbol a h)‖ =
    ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u+2*Real.pi*s) (norm a)‖ := by
  have he : (∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      star (gramMellinPhase s (norm a/N))*star (cubicSymbol a h)) =
      star (mellinPhase (-(2*Real.pi*s)) N*
        ∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u+2*Real.pi*s) (norm a)) := by
    rw [star_mul,star_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [gramMellinPhase_ratio s (norm_pos_of_ne_zero (primary_ne_zero (hS a ha))) hN,
      mellinPhase_add_height]
    simp only [star_mul]
    ring
  rw [he,norm_star,norm_mul,mellinPhase_norm,one_mul]

lemma finite_character_gram_reverse_row_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (h : Eisenstein) (u s : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      gramMellinPhase s (norm a/N)*star (cubicSymbol a h)‖ =
    ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u-2*Real.pi*s) (norm a)‖ := by
  have he := finite_character_gram_row_norm S β hS h u (-s) hN
  simpa only [gramMellinPhase_neg,star_star,mul_neg,← sub_eq_add_neg] using he

end CubicFirstMoment

end

end OAI
