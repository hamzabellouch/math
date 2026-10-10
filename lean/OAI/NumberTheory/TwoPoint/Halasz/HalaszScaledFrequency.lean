import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovMoment
import OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowOverlap

namespace OAI

/-! The symmetric character pairing in the double mean-value argument. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

noncomputable def halaszScaledFrequency {k : ℕ} (γ : Fin k → ℝ)
    (m : Fin k → ℤ) : Fin k → AddCircle (1:ℝ) :=
  fun j => ((γ j*(m j:ℝ):ℝ):AddCircle (1:ℝ))

lemma halasz_scaled_character_symm {k : ℕ} (γ : Fin k → ℝ) (m n : Fin k → ℤ) :
    halaszVinogradovCharacter m (halaszScaledFrequency γ n)=
      halaszVinogradovCharacter n (halaszScaledFrequency γ m) := by
  unfold halaszVinogradovCharacter halaszScaledFrequency
  apply prod_congr rfl
  intro j _
  rw [fourier_coe_apply,fourier_coe_apply]
  congr 1
  push_cast
  ring

lemma halasz_scaled_frequency_sub {k : ℕ} (γ : Fin k → ℝ) (m n : Fin k → ℤ) :
    halaszScaledFrequency γ m-halaszScaledFrequency γ n=
      halaszScaledFrequency γ (m-n) := by
  funext j
  simp only [halaszScaledFrequency,Pi.sub_apply,Int.cast_sub,← AddCircle.coe_sub,mul_sub]

lemma halasz_scaled_norm_abs (γ d : ℝ) :
    ‖((|γ| * d:ℝ):AddCircle (1:ℝ))‖=‖((γ*d:ℝ):AddCircle (1:ℝ))‖ := by
  rcases le_total 0 γ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,neg_mul,AddCircle.coe_neg,norm_neg]

lemma halasz_scaled_near_abs {k : ℕ} (γ δ : Fin k → ℝ) (m n : Fin k → ℤ) :
    HalaszWindowNear δ (halaszScaledFrequency γ m) (halaszScaledFrequency γ n) ↔
      HalaszWindowNear δ (halaszScaledFrequency (fun j => |γ j|) m)
        (halaszScaledFrequency (fun j => |γ j|) n) := by
  unfold HalaszWindowNear halaszScaledFrequency
  simp only [← AddCircle.coe_sub,← mul_sub,halasz_scaled_norm_abs]

lemma halasz_weighted_character_power {k M : ℕ} (s : ℕ) (a : Fin M → ℂ)
    (α : Fin k → AddCircle (1:ℝ)) :
    (∑ b : Fin M,a b*halaszVinogradovCharacter
      (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)) α)^s=
      ∑ x : Fin s → Fin M,(∏ i,a (x i))*
        halaszVinogradovCharacter (halaszVinogradovFrequency k x) α := by
  rw [Fintype.sum_pow]
  apply sum_congr rfl
  intro x _
  rw [prod_mul_distrib,← halasz_vinogradov_character_sum]
  congr 2
  ext j
  simp [halaszVinogradovFrequency]

lemma halasz_scaled_power {k M : ℕ} (s : ℕ) (γ : Fin k → ℝ)
    (a : Fin M → ℂ) (m : Fin k → ℤ) :
    (∑ b : Fin M,a b*halaszVinogradovCharacter m
      (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ))))^s=
      ∑ x : Fin s → Fin M,(∏ i,a (x i))*
        halaszVinogradovCharacter m
          (halaszScaledFrequency γ (halaszVinogradovFrequency k x)) := by
  simp_rw [halasz_scaled_character_symm γ m]
  rw [halasz_weighted_character_power]

end TwoPointCorrelations

end OAI
