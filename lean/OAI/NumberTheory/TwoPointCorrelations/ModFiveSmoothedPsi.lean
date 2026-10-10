import OAI.NumberTheory.TwoPointCorrelations.ModFivePerronSeries
import OAI.NumberTheory.TwoPointCorrelations.ModFivePositivity

namespace OAI

/-! The exact triangular Perron formula for the twisted von Mangoldt sums.
Nonintegral real cutoffs avoid the irrelevant boundary value of the scalar
kernel; later we use half-integral cutoffs to recover every integer sum.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset Erdos970
open scoped BigOperators Classical

noncomputable def modFiveSmoothedPsi (χ : DirichletCharacter ℂ 5) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊,
    modFiveMangoldtTwist χ n * ((1 - (n : ℝ) / x : ℝ) : ℂ)

theorem modFivePerron_finite_sum (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ))
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
  rw [modFivePerron_series_interchange a hx hσ ha]
  have hz : ∀ n ∉ Icc 1 ⌊x⌋₊,
      VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [VerticalIntegral', VerticalIntegral]
    · rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnlarge : ⌊x⌋₊ < n := by
        by_contra! h
        exact hn (mem_Icc.mpr ⟨hn1, h⟩)
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnlarge
      exact ite_eq_right (not_lt.mpr hxn.le)
  rw [tsum_eq_sum hz]
  apply sum_congr rfl
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
  have hnle : (n : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hx.le)
  have hnlt : (n : ℝ) < x := lt_of_le_of_ne hnle (hxnat n).symm
  rw [ite_eq_left hnlt]

theorem modFiveSmoothedPsi_perron (χ : DirichletCharacter ℂ 5) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (hxnat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    modFiveSmoothedPsi χ x =
      VerticalIntegral' (fun s =>
        (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
          modFivePerronKernel x s) σ := by
  have ha : LSeriesSummable (modFiveMangoldtTwist χ) (σ : ℂ) :=
    χ.LSeriesSummable_twist_vonMangoldt (by simpa using hσ)
  rw [modFiveSmoothedPsi, ← modFivePerron_finite_sum (modFiveMangoldtTwist χ) hx
    (by linarith) ha hxnat]
  simp only [VerticalIntegral', VerticalIntegral]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  rw [modFive_twisted_series_logderiv χ (by simpa using hσ)]

end TwoPointCorrelations

end OAI
