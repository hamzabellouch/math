import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import OAI.NumberTheory.Ostmann.Characters.CharacterPartialSum

namespace OAI

/-! # Quantitative initial bounds for the continued character L-function

The elementary coefficient bounds and Möbius inverse give a uniform positive
lower bound on Re(s)=2, used as the center value in the zero-count argument.
-/

namespace Ostmann

open MeasureTheory Filter
open scoped Classical BigOperators

theorem lSeries_norm_bound_re_two (f : ℕ → ℂ)
    (hf : ∀ n : ℕ, n ≠ 0 → ‖f n‖ ≤ 1) (s : ℂ) (hs : s.re = 2) :
    ‖LSeries f s‖ ≤ Real.pi ^ 2 / 6 := by
  have hsum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re hf (by rw [hs]; norm_num)
  have hpoint (n : ℕ) : ‖LSeries.term f s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    rw [LSeries.norm_term_eq, hs, Real.rpow_two]
    split_ifs with hn
    · simp [hn]
    · exact div_le_div_of_nonneg_right (hf n hn) (sq_nonneg _)
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
      hsum.norm.tsum_le_tsum hpoint hasSum_zeta_two.summable
    _ = _ := hasSum_zeta_two.tsum_eq

theorem PrimitiveComplexCharacter.L_bound_re_two (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : s.re = 2) : ‖χ.L s‖ ≤ Real.pi ^ 2 / 6 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [PrimitiveComplexCharacter.L, DirichletCharacter.LFunction_eq_LSeries _ (by rw [hs]; norm_num)]
  exact lSeries_norm_bound_re_two _ (fun _ _ => χ.character.norm_le_one _) s hs

theorem PrimitiveComplexCharacter.L_lower_re_two (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : s.re = 2) : 1 / 3 ≤ ‖χ.L s‖ := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let f : ℕ → ℂ := fun n => χ.character (n : ZMod χ.modulus) * ArithmeticFunction.moebius n
  have hf (n : ℕ) (hn : n ≠ 0) : ‖f n‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul]
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    exact (mul_le_mul (χ.character.norm_le_one _) hm (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)
  have hb := lSeries_norm_bound_re_two f hf s hs
  have he : χ.L s * LSeries f s = 1 := by
    rw [PrimitiveComplexCharacter.L, DirichletCharacter.LFunction_eq_LSeries _ (by rw [hs]; norm_num)]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ.character (by rw [hs]; norm_num)
  have hn := congrArg norm he
  rw [norm_mul, norm_one] at hn
  have hpi : Real.pi ^ 2 / 6 ≤ 3 := by
    have h := Real.pi_lt_four
    nlinarith [Real.pi_pos]
  have hmul := mul_le_mul_of_nonneg_left (hb.trans hpi) (norm_nonneg (χ.L s))
  rw [hn] at hmul
  linarith

theorem PrimitiveComplexCharacter.partial_sum_bigO (χ : PrimitiveComplexCharacter) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ.character (n : ZMod χ.modulus)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (χ.modulus + 1 : ℝ)
  filter_upwards with N
  simpa using χ.prefix_Icc_bound N

theorem PrimitiveComplexCharacter.L_integral_right (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    χ.L s = s * ∫ t in Set.Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1)) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [PrimitiveComplexCharacter.L, DirichletCharacter.LFunction_eq_LSeries _ hs]
  apply LSeries_eq_mul_integral _ (r := 0) le_rfl (by linarith)
    (χ.character.LSeriesSummable_of_one_lt_re hs)
  simpa only [Real.rpow_zero] using χ.partial_sum_bigO

end Ostmann

end OAI
