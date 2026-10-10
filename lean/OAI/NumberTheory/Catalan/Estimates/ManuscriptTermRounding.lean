import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

section

namespace InternalCatalan

def manuscriptTermRoundStepRat : ℚ := 1 / (10 : ℚ) ^ 40

theorem manuscript_rat_mesh_enclosure (q δ : ℚ) (hδ : 0 < δ) :
    ∃ k : ℤ,
      (k : ℚ) * δ ≤ q ∧
      q ≤ ((k + 1 : ℤ) : ℚ) * δ ∧
      ((k + 1 : ℤ) : ℚ) * δ - (k : ℚ) * δ = δ ∧
      |q - (k : ℚ) * δ| ≤ δ ∧
      |q - ((k + 1 : ℤ) : ℚ) * δ| ≤ δ := by
  let k : ℤ := ⌊q / δ⌋
  have hflo : (k : ℚ) ≤ q / δ := Int.floor_le (q / δ)
  have hfhi : q / δ < ((k + 1 : ℤ) : ℚ) := by
    simpa only [Int.cast_add, Int.cast_one] using Int.lt_floor_add_one (q / δ)
  have hlo : (k : ℚ) * δ ≤ q := (le_div_iff₀ hδ).mp hflo
  have hhi : q < ((k + 1 : ℤ) : ℚ) * δ := (div_lt_iff₀ hδ).mp hfhi
  have hgap : ((k + 1 : ℤ) : ℚ) * δ - (k : ℚ) * δ = δ := by
    push_cast
    ring
  refine ⟨k, hlo, hhi.le, hgap, ?_, ?_⟩
  · rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hhi.le)]
    linarith

theorem manuscript_rat_term_rounding (q : ℚ) :
    ∃ k : ℤ,
      (k : ℚ) * manuscriptTermRoundStepRat ≤ q ∧
      q ≤ ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat ∧
      ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat -
        (k : ℚ) * manuscriptTermRoundStepRat = manuscriptTermRoundStepRat ∧
      |q - (k : ℚ) * manuscriptTermRoundStepRat| ≤ manuscriptTermRoundStepRat ∧
      |q - ((k + 1 : ℤ) : ℚ) * manuscriptTermRoundStepRat| ≤
        manuscriptTermRoundStepRat :=
  manuscript_rat_mesh_enclosure q manuscriptTermRoundStepRat
    (by norm_num [manuscriptTermRoundStepRat])

theorem manuscript_real_cast_term_rounding (q : ℚ) :
    ∃ k : ℤ,
      (k : ℝ) * (1 / (10 : ℝ) ^ 40) ≤ (q : ℝ) ∧
      (q : ℝ) ≤ ((k + 1 : ℤ) : ℝ) * (1 / (10 : ℝ) ^ 40) ∧
      ((k + 1 : ℤ) : ℝ) * (1 / (10 : ℝ) ^ 40) -
        (k : ℝ) * (1 / (10 : ℝ) ^ 40) = 1 / (10 : ℝ) ^ 40 ∧
      |(q : ℝ) - (k : ℝ) * (1 / (10 : ℝ) ^ 40)| ≤ 1 / (10 : ℝ) ^ 40 ∧
      |(q : ℝ) - ((k + 1 : ℤ) : ℝ) * (1 / (10 : ℝ) ^ 40)| ≤
        1 / (10 : ℝ) ^ 40 := by
  obtain ⟨k, hlo, hhi, hgap, hel, heu⟩ := manuscript_rat_term_rounding q
  unfold manuscriptTermRoundStepRat at hlo hhi hgap hel heu
  have hδcast : ((1 / (10 : ℚ) ^ 40 : ℚ) : ℝ) = 1 / (10 : ℝ) ^ 40 := by norm_num
  refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
  · have h := (Rat.cast_le (K := ℝ)).mpr hlo
    simpa only [Rat.cast_mul, Rat.cast_intCast, hδcast] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr hhi
    simpa only [Rat.cast_mul, Rat.cast_intCast, hδcast] using h
  · have h := (Rat.cast_inj (α := ℝ)).mpr hgap
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast, hδcast] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr hel
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast, hδcast] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr heu
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast, hδcast] using h

end InternalCatalan

end

end OAI
