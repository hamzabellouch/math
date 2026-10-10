import OAI.NumberTheory.EgyptianFractions.DyadicSum

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The dyadic pieces of a high residue level lie in the range where the
uniform reciprocal-phase estimate applies. -/
theorem deterministic_phase_window (S m D X U Z : ℝ)
    (hS : 0 ≤ S) (hSlarge : 10 * Real.log 2 ≤ S)
    (hm : m ≤ S) (hD : 255 ≤ D)
    (hXlower : Real.exp S ≤ X) (hXupper : X ≤ Real.exp (D * S / 4))
    (hUlower : Real.exp (-m / 10000) * X / 2 ≤ U) (hUupper : U ≤ X)
    (hZlower : Real.exp (D * S) ≤ |Z|)
    (hZupper : |Z| ≤ Real.exp ((2 * D + 102) * S)) :
    Real.exp (4 * S / 5) ≤ U ∧ U ^ 4 ≤ |Z| ∧ |Z| ≤ U ^ (3 * D) := by
  have hUexp : Real.exp (4 * S / 5) ≤ U := by
    calc
      Real.exp (4 * S / 5) ≤ Real.exp (S - m / 10000 - Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-m / 10000) * Real.exp S / 2 := by
        rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          show -m / 10000 = -(m / 10000) by ring, Real.exp_neg]
        ring
      _ ≤ Real.exp (-m / 10000) * X / 2 := by
        gcongr
      _ ≤ U := hUlower
  have hUpos : 0 < U := (Real.exp_pos _).trans_le hUexp
  have hlogU : 4 * S / 5 ≤ Real.log U := by
    calc
      4 * S / 5 = Real.log (Real.exp (4 * S / 5)) := (Real.log_exp _).symm
      _ ≤ Real.log U := Real.log_le_log (Real.exp_pos _) hUexp
  refine ⟨hUexp, ?_, ?_⟩
  · calc
      U ^ 4 ≤ (Real.exp (D * S / 4)) ^ 4 := by
        gcongr
        exact hUupper.trans hXupper
      _ = Real.exp (D * S) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ |Z| := hZlower
  · apply hZupper.trans
    rw [Real.rpow_def_of_pos hUpos]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogU (show 0 ≤ 3 * D by linarith),
      mul_nonneg (show 0 ≤ D - 255 by linarith) hS]

/-- A local power saving becomes a uniform exponential saving throughout the
high-level dyadic window. -/
theorem power_saving_le_exponential (S U A δ : ℝ)
    (hU : Real.exp (4 * S / 5) ≤ U) (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    A * U ^ (1 - δ) ≤ A * U * Real.exp (-(4 * δ * S / 5)) := by
  have hUpos : 0 < U := (Real.exp_pos _).trans_le hU
  have hlogU : 4 * S / 5 ≤ Real.log U := by
    calc
      4 * S / 5 = Real.log (Real.exp (4 * S / 5)) := (Real.log_exp _).symm
      _ ≤ Real.log U := Real.log_le_log (Real.exp_pos _) hU
  have hdecay : U ^ (-δ) ≤ Real.exp (-(4 * δ * S / 5)) := by
    rw [Real.rpow_def_of_pos hUpos]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogU hδ]
  calc
    A * U ^ (1 - δ) = A * U * U ^ (-δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hUpos, Real.rpow_one]
      ring
    _ ≤ A * U * Real.exp (-(4 * δ * S / 5)) :=
      mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA hUpos.le)

/-- The frequency occurring in an off-diagonal prime-subset pair has the
required exponential bounds. Distinctness, not primality, is needed here. -/
theorem deterministic_frequency_bounds (S m D C l : ℝ) (t t' : ℕ)
    (hS : 0 ≤ S) (hm : m ≤ S) (hlower : 1 ≤ l)
    (hlupper : l ≤ Real.exp (m / 2500))
    (hClower : Real.exp (D * S) ≤ C) (hCupper : C ≤ Real.exp (2 * D * S))
    (ht : (t : ℝ) ≤ Real.exp (101 * S))
    (ht' : (t' : ℝ) ≤ Real.exp (101 * S)) (hne : t ≠ t') :
    Real.exp (D * S) ≤ |l * C * ((t : ℝ) - t')| ∧
      |l * C * ((t : ℝ) - t')| ≤ Real.exp ((2 * D + 102) * S) := by
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hClower
  have hlpos : 0 < l := by linarith
  have hdiff : (1 : ℝ) ≤ |(t : ℝ) - t'| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (t : ℝ) + 1 ≤ t' := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith : (t : ℝ) - t' ≤ 0)]
      linarith
    · have hh : (t' : ℝ) + 1 ≤ t := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : 0 ≤ (t : ℝ) - t')]
      linarith
  have hdiffupper : |(t : ℝ) - t'| ≤ Real.exp (101 * S) := by
    apply abs_le.mpr
    constructor <;> linarith [show (0 : ℝ) ≤ t by positivity,
      show (0 : ℝ) ≤ t' by positivity]
  have hlupper' : l ≤ Real.exp S := hlupper.trans (Real.exp_le_exp.mpr (by linarith))
  rw [abs_mul, abs_of_pos (mul_pos hlpos hCpos)]
  constructor
  · calc
      Real.exp (D * S) ≤ C := hClower
      _ = 1 * C * 1 := by ring
      _ ≤ l * C * |(t : ℝ) - t'| := by gcongr
  · calc
      l * C * |(t : ℝ) - t'| ≤
          Real.exp S * Real.exp (2 * D * S) * Real.exp (101 * S) := by gcongr
      _ = Real.exp ((2 * D + 102) * S) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Summation over dyadic pieces preserves the uniform exponential saving. -/
theorem deterministic_phase_sum_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (Y X : ℕ) (S A δ : ℝ) (hY : 1 ≤ Y)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hYlarge : Real.exp (4 * S / 5) ≤ (Y : ℝ) / 2)
    (hlocal : ∀ U : ℕ, 0 < U → Y ≤ 2 * U → U ≤ X →
      ‖∑ n ∈ (Finset.Ico U (2 * U) ∩ Finset.Icc Y X), f n‖ ≤
        A * (U : ℝ) ^ (1 - δ)) :
    ‖∑ n ∈ Finset.Icc Y X, f n‖ ≤
      2 * A * (X : ℝ) * Real.exp (-(4 * δ * S / 5)) := by
  have hh := norm_sum_interval_le_of_local_intervals f Y X hY
    (A * Real.exp (-(4 * δ * S / 5))) (by positivity) (fun U hU hYU hUX => by
      have hYUr : (Y : ℝ) ≤ 2 * U := by exact_mod_cast hYU
      have hUexp : Real.exp (4 * S / 5) ≤ (U : ℝ) :=
        hYlarge.trans (by linarith)
      apply (hlocal U hU hYU hUX).trans
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (power_saving_le_exponential S U A δ hUexp hA hδ))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

end Problem337

end

end OAI
