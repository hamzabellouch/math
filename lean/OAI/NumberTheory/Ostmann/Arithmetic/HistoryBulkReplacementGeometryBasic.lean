import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellActualErrorBudgetPrime
import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReplacementGeometry
open Conclusion ScaleBudget PrimeCellActualErrorBudget Filter

theorem log_nat_product_le (xs : List ℕ) (A : ℝ)
    (hpos : ∀ p ∈ xs, 0 < p) (hlog : ∀ p ∈ xs, Real.log (p : ℝ) ≤ A) :
    Real.log (xs.prod : ℝ) ≤ (xs.length : ℝ) * A := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (hpos p (by simp)).ne'
    have hx : (xs.prod : ℝ) ≠ 0 := by
      exact_mod_cast (List.prod_pos (fun q hq => hpos q (by simp [hq]))).ne'
    rw [List.prod_cons, Nat.cast_mul, Real.log_mul hp hx]
    have hh := ih (fun q hq => hpos q (by simp [hq]))
      (fun q hq => hlog q (by simp [hq]))
    have hpp := hlog p (by simp)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem eventually_bulk_log_budget (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      (bulkSize k L : ℝ) * (Real.exp ((1 / 1000 : ℝ) * L) + C) ≤
        Real.exp (bulk.μ * L) := by
  filter_upwards [eventually_poly_exp_le (bulkScale k * (1 + C)) 1
      bulk_spectator_gap (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (0 : ℝ)] with L hpoly hL
  have he : 1 ≤ Real.exp ((1 / 1000 : ℝ) * L) := Real.one_le_exp (by positivity)
  have hm := (bulkSize_bounds k hL).2
  have hb : Real.exp ((1 / 1000 : ℝ) * L) + C ≤
      (1 + C) * Real.exp ((1 / 1000 : ℝ) * L) := by nlinarith
  have hscale : 0 ≤ bulkScale k * L := by unfold bulkScale; positivity
  have hh := mul_le_mul hm hb (by positivity) hscale
  apply hh.trans
  simpa only [pow_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using hpoly

structure GeometryBounds (d L₀ : ℝ) (M : ℕ) (L : ℝ) : Prop where
  modulus_log : Real.log (M : ℝ) ≤ Real.exp (bulk.μ * L)
  at_lower : ∀ lower : ℝ, Real.exp ((1 / 250 : ℝ) * L) ≤ lower →
    Real.exp (bulk.a₀ * L) ≤ lower ∧ L₀ ≤ lower ∧
      (M : ℝ) < Real.exp lower ∧ (M : ℝ) ≤ Real.exp (d * lower^(1 / 3 : ℝ))

theorem eventually_geometryBounds {d : ℝ} (hd : 0 < d) (L₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ M : ℕ, 0 < M →
      Real.log (M : ℝ) ≤ Real.exp (bulk.μ * L) → GeometryBounds d L₀ M L := by
  filter_upwards [eventually_modulus_admissible bulk hd,
    eventually_poly_exp_le L₀ 0 (by norm_num : (0 : ℝ) < 1 / 250)
      (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)] with L hap hthreshold hL
  intro M hM hcap
  refine ⟨hcap, ?_⟩
  intro lower hlower
  have hscale : Real.exp (bulk.a₀ * L) ≤ lower := by
    apply le_trans _ hlower
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by norm_num [bulk]) (by linarith)
  have hthreshold' : L₀ ≤ Real.exp ((1 / 250 : ℝ) * L) := by
    simpa only [pow_zero, mul_one, zero_mul, Real.exp_zero, one_mul] using hthreshold
  have hlog : Real.log (M : ℝ) < lower := by
    apply lt_of_le_of_lt hcap
    apply lt_of_lt_of_le _ hlower
    apply Real.exp_lt_exp.mpr
    exact mul_lt_mul_of_pos_right (by norm_num [bulk]) (by linarith)
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  exact ⟨hscale, hthreshold'.trans hlower,
    by simpa only [Real.exp_log hMr] using Real.exp_lt_exp.mpr hlog,
    hap M lower hM hcap hscale⟩

end Ostmann.Arithmetic.HistoryBulkReplacementGeometry

end

end OAI
