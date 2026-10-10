import OAI.NumberTheory.Ostmann.Construction.TailGoodPrimeCells
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # The selected small cells lie below the actual collision cutoff -/

namespace Ostmann
open Filter

theorem eventual_tail_cell_window (a C H : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X target : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      Real.exp ((1 / 100 : ℝ) * L) ≤ target →
      target ≤ Real.exp ((11 / 1000 : ℝ) * L) →
      H ≤ target ∧
      target + 64 * tailDefectBudget a C X + 2 ≤ Real.log (tailCollisionCutoff X : ℝ) ∧
      target + 64 * tailDefectBudget a C X + 1 ≤ Real.exp (L / 2) := by
  let D := 256 * C + 256 * Real.log 2 + 128 * Real.log 4 / a + Real.log 2 + 2
  let K := 1290 + |D|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg D]
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventual_tailCollisionCutoff 0)
  have ht (b : ℝ) (hb : 0 < b) : Tendsto (fun L : ℝ => Real.exp (b * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb)
  filter_upwards [arithmetic_exponent_absorption (11 / 1000) (4 / 100) 0 K (1 / 2) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_exponent_absorption (11 / 1000) (1 / 2) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    (ht (4 / 100) (by norm_num)).eventually (eventually_ge_atTop X₀),
    (ht (1 / 100) (by norm_num)).eventually (eventually_ge_atTop H),
    eventually_ge_atTop (1 : ℝ)] with L hgap hlarge hX0 hH hL
  intro X target hXlo hXhi htlo hthi
  have hcut := hX₀ X (hX0.trans hXlo)
  have hlogX : Real.log X ≤ L := by
    have h := Real.log_le_log (by linarith [hcut.1] : 0 < X) hXhi
    rwa [Real.log_exp] at h
  have htail := (tailCollisionCutoff_bounds X hcut.1 hcut.2.1).2.2
  have hlinear : 1285 * L + D ≤ K * L := by
    have hD := le_abs_self D
    have hDL := mul_le_mul_of_nonneg_left hL (abs_nonneg D)
    dsimp [K]
    nlinarith only [hD, hDL, hL]
  have hprod : Real.exp ((11 / 1000 : ℝ) * L) ≤
      K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    have hKL : 1 ≤ K * L := hL.trans (le_mul_of_one_le_left (by linarith) hK)
    exact le_mul_of_one_le_left (Real.exp_nonneg _) hKL
  have hbound : target + 64 * tailDefectBudget a C X + 2 +
      5 * Real.log X + Real.log 2 ≤ K * L + K * L * Real.exp ((11 / 1000 : ℝ) * L) := by
    calc
      _ = target + 1285 * Real.log X + D := by dsimp [tailDefectBudget, D]; ring
      _ ≤ Real.exp ((11 / 1000 : ℝ) * L) + 1285 * L + D := by linarith
      _ ≤ _ := by linarith only [hlinear, hprod]
  simp only [pow_one, zero_mul, Real.exp_zero] at hgap hlarge
  refine ⟨hH.trans htlo, ?_, ?_⟩
  · nlinarith only [hbound, hgap, htail, hXlo]
  · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hcut.1
    have hexp : Real.exp ((1 / 2 : ℝ) * L) = Real.exp (L / 2) := by congr 1; ring
    rw [hexp] at hlarge
    nlinarith only [hbound, hlarge, hlog2, hlogX0]

theorem eventual_selected_cell_upper (a C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X target : ℝ, 0 < X → X ≤ Real.exp L →
      target ≤ Real.exp ((105 / 10000 : ℝ) * L) →
      target + 64 * tailDefectBudget a C X + 2 ≤ Real.exp ((11 / 1000 : ℝ) * L) := by
  let D := 256 * C + 256 * Real.log 2 + 128 * Real.log 4 / a + 2
  let K := 1282 + |D|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg D]
  filter_upwards [arithmetic_exponent_absorption (105 / 10000) (11 / 1000) 0 K 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro X target hX hXhi htarget
  have hlogX : Real.log X ≤ L := by
    have h := Real.log_le_log hX hXhi
    rwa [Real.log_exp] at h
  have hlinear : 1280 * L + D ≤ K * L := by
    have hD := le_abs_self D
    have hDL := mul_le_mul_of_nonneg_left hL (abs_nonneg D)
    dsimp [K]
    nlinarith only [hD, hDL, hL]
  have hprod : Real.exp ((105 / 10000 : ℝ) * L) ≤
      K * L * Real.exp ((105 / 10000 : ℝ) * L) :=
    le_mul_of_one_le_left (Real.exp_nonneg _)
      (hL.trans (le_mul_of_one_le_left (by linarith) hK))
  have hbound : target + 64 * tailDefectBudget a C X + 2 ≤
      K * L + K * L * Real.exp ((105 / 10000 : ℝ) * L) := by
    calc
      _ = target + 1280 * Real.log X + D := by dsimp [D, tailDefectBudget]; ring
      _ ≤ Real.exp ((105 / 10000 : ℝ) * L) + 1280 * L + D := by linarith
      _ ≤ _ := by linarith only [hlinear, hprod]
  simp only [pow_one, one_mul, zero_mul, Real.exp_zero] at hrate
  linarith

end Ostmann

end OAI
