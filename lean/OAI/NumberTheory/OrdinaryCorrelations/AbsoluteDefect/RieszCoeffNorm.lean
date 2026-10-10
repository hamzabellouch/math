import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CutoffSeriesEqSum
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogweightError

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryRieszPerron
open OrdinaryLogWeightRemoval

lemma riesz_coeff_norm (a : ℕ → ℂ) {X : ℝ} (hX : 0<X)
    (ha : ∀n, ‖a n‖≤1) (n : ℕ) (hn : n∈Finset.Icc 1 ⌊X⌋₊) :
    ‖a n*(1-(n:ℂ)/(X:ℂ))‖≤1 := by
  have hn0 : 0≤(n:ℝ)/X := div_nonneg (Nat.cast_nonneg n) hX.le
  have hn1 : (n:ℝ)/X≤1 := (div_le_one hX).2 ((Nat.le_floor_iff hX.le).1 (Finset.mem_Icc.mp hn).2)
  have he : (1:ℂ)-(n:ℂ)/(X:ℂ)=((1-(n:ℝ)/X:ℝ):ℂ) := by push_cast; rfl
  rw [norm_mul,he,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr hn1)]
  nlinarith [norm_nonneg (a n),ha n]

lemma riesz_logweight_error (a : ℕ → ℂ) {X R : ℝ} (hX : 1≤X) (hR : 1≤R)
    (ha : ∀n, ‖a n‖≤1) :
    ‖(Real.log X:ℂ)*cutoffSeries a X-cutoffSeries (LSeries.logMul a) X‖ ≤
      (X/R)*Real.log X+X*Real.log R := by
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  rw [cutoffSeries_eq_sum a hx,cutoffSeries_eq_sum (LSeries.logMul a) hx]
  have he (n : ℕ) (hn : n∈Finset.Icc 1 ⌊X⌋₊) :
      LSeries.logMul a n*(1-(n:ℂ)/(X:ℂ)) =
        (Real.log (n:ℝ):ℂ)*(a n*(1-(n:ℂ)/(X:ℂ))) := by
    dsimp [LSeries.logMul]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg n)]
    ring
  rw [Finset.sum_congr rfl he]
  exact logweight_error (fun n => a n*(1-(n:ℂ)/(X:ℂ))) hX hR (riesz_coeff_norm a hx ha)

lemma cutoff_norm_le_logcutoff_add (a : ℕ → ℂ) {X R : ℝ} (hX : 1≤X) (hR : 1≤R)
    (ha : ∀n, ‖a n‖≤1) :
    Real.log X*‖cutoffSeries a X‖ ≤ ‖cutoffSeries (LSeries.logMul a) X‖+
      ((X/R)*Real.log X+X*Real.log R) := by
  have hh : ‖(Real.log X:ℂ)*cutoffSeries a X‖ ≤
      ‖cutoffSeries (LSeries.logMul a) X‖ +
      ‖(Real.log X:ℂ)*cutoffSeries a X-cutoffSeries (LSeries.logMul a) X‖ := by
    calc
      _ = ‖cutoffSeries (LSeries.logMul a) X+
        ((Real.log X:ℂ)*cutoffSeries a X-cutoffSeries (LSeries.logMul a) X)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.log_nonneg hX)] at hh
  exact hh.trans (add_le_add le_rfl (riesz_logweight_error a hX hR ha))

end OrdinaryRieszPerron

end

end OAI
