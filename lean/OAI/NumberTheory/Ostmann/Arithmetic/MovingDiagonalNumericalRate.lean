import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternInternalError
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantErrorRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalOuterWeight

namespace OAI

/-! # Numerical simplification of the original diagonal comparison -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem diagonalOuterMajorant_eventually (B D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ diagonal : Bool,
      2 * Real.exp 1 * diagonalOuterMajorant B D diagonal ≤
        Real.exp ((49 / 1000 : ℝ) * L) := by
  have ht : Tendsto (fun L : ℝ => Real.exp ((49 / 1000 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [ht.eventually_ge_atTop
    (max (2 * Real.exp 1 * diagonalOuterMajorant B D false)
      (2 * Real.exp 1 * diagonalOuterMajorant B D true))] with L hL diagonal
  cases diagonal
  · exact (le_max_left _ _).trans hL
  · exact (le_max_right _ _).trans hL

/-- The actual denominator and coefficient mass absorb all comparison costs.
The remaining main term `K` is the nonnegative leaf/split contribution. -/
theorem movingPattern_diagonal_pointwise_rate (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D Cprior Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
    (hCprior : 1 ≤ Cprior) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (c : ℕ) (E U α β amp lo hi rG K z : ℝ) (diagonal : Bool),
      let κE := (2 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c)
      let κ := (2 : ℝ) ^ c * (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - c)
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
      c ≤ 4 * n * 2 ^ n → 0 ≤ E → E ≤ Real.exp (Cprior * L) →
      1 ≤ U → Real.log U ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      0 ≤ α → α ≤ Real.exp (Cmass * L - Real.exp ((39 / 10000 : ℝ) * L)) →
      0 ≤ β → β ≤ Real.exp (Cmass * L - Real.exp ((1 / 100 : ℝ) * L)) →
      0 ≤ amp → amp ≤ 4 → lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ rG → 0 ≤ K →
      z ≤ (κE * U ^ c) * (Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) +
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L))) +
        diagonalOuterMajorant B D diagonal * ((2 * Real.exp 1 *
          (κE * (cost * movingInternalArithmeticError n c (2 ^ n * (r₀ + m + 4 * n + 4))
            (Real.exp (A * m)) U α β (Real.exp ((1 / 100 : ℝ) * L)) + K +
            (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
              2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))))) / rG) →
      z ≤ κ * (K + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        4 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) := by
  filter_upwards [movingPattern_internal_arithmetic_error_rate ψ n r₀ k A Wwin B D Cmass
      hA hWwin hCmass, movingPattern_giant_error_rate n Cprior hCprior,
    diagonalOuterMajorant_eventually B D, eventually_ge_atTop (0 : ℝ)]
    with L hinternal hgiant houter hL
  dsimp only
  intro p c E U α β amp lo hi rG K z diagonal hc hE hEup hU hUlog
    hα hαup hβ hβup hamp hampup hhi hwidth hp hrG hK hz
  let κE := (2 : ℝ) ^ c * E ^ (4 * n * 2 ^ n - c)
  let κ := (2 : ℝ) ^ c * (Real.exp (Cprior * L)) ^ (4 * n * 2 ^ n - c)
  let e₁ := Real.exp (-Real.exp ((125 / 100000 : ℝ) * L))
  let e₂ := Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))
  let err := ((amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) *
    (movingFourierVariationBudget ψ (Real.exp (A * spectatorBulkCount k L)) lo hi n *
      (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2) *
    movingInternalArithmeticError n c (2 ^ n * (r₀ + spectatorBulkCount k L + 4 * n + 4))
      (Real.exp (A * spectatorBulkCount k L)) U α β (Real.exp ((1 / 100 : ℝ) * L))
  have hint : err ≤ e₂ := hinternal p c U α β amp lo hi hc hU hUlog hα hαup hβ hβup
    hamp hampup hhi hwidth hp
  have hUup : U ≤ Real.exp (Real.exp ((12 / 1000 : ℝ) * L)) := by
    rw [← Real.exp_log (by linarith : 0 < U)]
    exact Real.exp_le_exp.mpr hUlog
  have hg := hgiant c hc E U hE hEup (by linarith) hUup
  have hκE : 0 ≤ κE := by dsimp only [κE]; positivity
  have hκmono : κE ≤ κ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE hEup _) (by positivity)
  have hκ : 1 ≤ κ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hL)))
  have hrG0 : 0 < rG := (Real.exp_pos _).trans_le hrG
  have hscale : diagonalOuterMajorant B D diagonal * (2 * Real.exp 1) / rG ≤ 1 := by
    apply (div_le_one hrG0).mpr
    nlinarith only [(houter diagonal).trans hrG]
  have herr0 : 0 ≤ err := by
    apply mul_nonneg (by positivity)
    exact movingInternalArithmeticError_nonneg n c _ _ U α β _
      (Real.one_le_exp_iff.mpr (mul_nonneg hA (Nat.cast_nonneg _))) hU hα hβ (Real.exp_nonneg _)
  have hb0 : 0 ≤ err + K + (e₁ + 2 * e₂) := by dsimp only [e₁, e₂]; positivity
  have hstep :
      diagonalOuterMajorant B D diagonal *
        ((2 * Real.exp 1 * (κE * (err + K + (e₁ + 2 * e₂)))) / rG) ≤
      κ * (K + e₁ + 3 * e₂) := by
    calc
      _ = (diagonalOuterMajorant B D diagonal * (2 * Real.exp 1) / rG) *
          (κE * (err + K + (e₁ + 2 * e₂))) := by ring
      _ ≤ κE * (err + K + (e₁ + 2 * e₂)) :=
        mul_le_of_le_one_left (mul_nonneg hκE hb0) hscale
      _ ≤ κE * (K + e₁ + 3 * e₂) :=
        mul_le_mul_of_nonneg_left (by linarith) hκE
      _ ≤ κ * (K + e₁ + 3 * e₂) :=
        mul_le_mul_of_nonneg_right hκmono (by dsimp only [e₁, e₂]; positivity)
  have hrest := add_le_add hg hstep
  have hh : z ≤ e₂ + κ * (K + e₁ + 3 * e₂) := hz.trans hrest
  have he₂ : e₂ ≤ κ * e₂ := le_mul_of_one_le_left (Real.exp_nonneg _) hκ
  change z ≤ κ * (K + e₁ + 4 * e₂)
  nlinarith only [hh, he₂]

end Ostmann

end OAI
