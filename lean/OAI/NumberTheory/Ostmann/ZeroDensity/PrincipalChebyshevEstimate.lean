import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszNearby
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszPositiveRecovery

namespace OAI

/-! # The quantitative principal Chebyshev estimate from positive unsmoothing -/

namespace Ostmann

open Filter

theorem principal_chebyshev_error : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
    |Chebyshev.psi X - X| ≤ 25 * X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, hdecay⟩ := principal_riesz_sqrt_decay
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hdecay
  refine ⟨d / 4, by positivity, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (max 4 (2 * X0)),
    ht.eventually (eventually_ge_atTop ((4 / d) * Real.log 2))] with X hXlarge hscale
  have hX : 4 ≤ X := (le_max_left _ _).trans hXlarge
  have hX0' : 2 * X0 ≤ X := (le_max_right _ _).trans hXlarge
  have hXp : 0 < X := by linarith
  dsimp only [Function.comp_apply] at hscale
  let y := Real.sqrt (Real.log X)
  let h := X * Real.exp (-(d / 4) * y)
  let E := 12 * X ^ 2 * Real.exp (-(d / 2) * y)
  let N := ⌈2 * X⌉₊
  have hN : 2 * X ≤ (N : ℝ) := Nat.le_ceil _
  have hh : 0 < h := by dsimp [h]; positivity
  have hlog : Real.log 2 ≤ (d / 4) * y := by
    have hm := mul_le_mul_of_nonneg_left hscale (show 0 ≤ d / 4 by positivity)
    have he : (d / 4) * ((4 / d) * Real.log 2) = Real.log 2 := by field_simp
    rw [he] at hm
    exact hm
  have hexp : Real.exp (-(d / 4) * y) ≤ 1 / 2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hhalf : h ≤ X / 2 := by
    have hm := mul_le_mul_of_nonneg_left hexp hXp.le
    dsimp [h]
    linarith
  have herr (Y : ℝ) (hlo : X / 2 ≤ Y) (hhi : Y ≤ 2 * X) :
      |finiteRieszSum (Finset.range (N + 1)) ArithmeticFunction.vonMangoldt Y - Y ^ 2 / 2| ≤ E := by
    exact principalRiesz_nearby_error N d X Y hd hX hlo hhi (hhi.trans hN)
      (hX0 Y (by linarith))
  have hzero := herr X (by linarith) (by linarith)
  have hplus := herr (X + h) (by linarith) (by linarith)
  have hminus := herr (X - h) (by linarith) (by linarith)
  have hrec := finiteRieszSum_quadratic_recovery (Finset.range (N + 1))
    ArithmeticFunction.vonMangoldt X h E hh
    (fun n _ => ArithmeticFunction.vonMangoldt_nonneg (n := n)) hzero hplus hminus
  rw [principal_finite_count_eq_psi N X hXp.le (by linarith)] at hrec
  have hexp2 : Real.exp (-(d / 2) * y) = (Real.exp (-(d / 4) * y)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hE : E = 12 * h ^ 2 := by
    dsimp [E, h]
    rw [hexp2]
    ring
  have hratio : 2 * E / h = 24 * h := by
    rw [hE]
    field_simp
    ring
  have hfinal : |Chebyshev.psi X - X| ≤ 25 * h := by
    rw [hratio] at hrec
    linarith
  simpa only [h, y, mul_assoc] using hfinal

end Ostmann

end OAI
