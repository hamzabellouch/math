import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovDiagonal
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! Fourier orthogonality for the complete Vinogradov system, with
normalised Haar measure on its coefficient torus. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped ComplexConjugate

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

noncomputable def halaszVinogradovHaar (k : ℕ) : Measure (Fin k → AddCircle (1:ℝ)) :=
  Measure.pi (fun _ => AddCircle.haarAddCircle)

instance (k : ℕ) : IsProbabilityMeasure (halaszVinogradovHaar k) := by
  unfold halaszVinogradovHaar
  infer_instance

noncomputable def halaszVinogradovCharacter {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∏ j, fourier (m j) (α j)

lemma halasz_vinogradov_fourier_integral (n : ℤ) :
    (∫ x : AddCircle (1:ℝ), fourier n x ∂AddCircle.haarAddCircle) =
      if n=0 then (1:ℂ) else 0 := by
  by_cases hn : n=0
  · subst n
    simp
  · simp only [hn,ite_false]
    exact integral_eq_zero_of_add_right_eq_neg
      (fourier_add_half_inv_index hn (by norm_num))

theorem halasz_vinogradov_character_integral {k : ℕ} (m : Fin k → ℤ) :
    (∫ α, halaszVinogradovCharacter m α ∂halaszVinogradovHaar k) =
      if m=0 then (1:ℂ) else 0 := by
  unfold halaszVinogradovCharacter halaszVinogradovHaar
  rw [integral_fintype_prod_eq_prod]
  simp_rw [halasz_vinogradov_fourier_integral]
  by_cases hm : m=0
  · subst m
    simp
  · simp only [hm,ite_false]
    obtain ⟨j,hj⟩ : ∃ j, m j≠0 := by
      by_contra hn
      push Not at hn
      apply hm
      funext j
      exact hn j
    apply prod_eq_zero (mem_univ j)
    simp [hj]

lemma halasz_vinogradov_character_add {k : ℕ} (m n : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (m+n) α =
      halaszVinogradovCharacter m α*halaszVinogradovCharacter n α := by
  simp only [halaszVinogradovCharacter,Pi.add_apply,fourier_add,prod_mul_distrib]

lemma halasz_vinogradov_character_neg {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszVinogradovCharacter (-m) α = conj (halaszVinogradovCharacter m α) := by
  simp only [halaszVinogradovCharacter,Pi.neg_apply,fourier_neg,map_prod]

lemma halasz_vinogradov_character_continuous {k : ℕ} (m : Fin k → ℤ) :
    Continuous (halaszVinogradovCharacter m) := by
  unfold halaszVinogradovCharacter
  fun_prop

lemma halasz_vinogradov_character_integrable {k : ℕ} (m : Fin k → ℤ) :
    Integrable (halaszVinogradovCharacter m) (halaszVinogradovHaar k) := by
  exact (halasz_vinogradov_character_continuous m).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma halasz_vinogradov_character_inner {k : ℕ} (m n : Fin k → ℤ) :
    (∫ α, halaszVinogradovCharacter m α*conj (halaszVinogradovCharacter n α)
      ∂halaszVinogradovHaar k) = if m=n then (1:ℂ) else 0 := by
  simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
  rw [halasz_vinogradov_character_integral]
  simp only [← sub_eq_add_neg,sub_eq_zero]

end TwoPointCorrelations

end OAI
