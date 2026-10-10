import OAI.NumberTheory.TotientAsymptotic.FordInitialCount
import OAI.NumberTheory.TotientAsymptotic.NormalTerminalFactors
import OAI.NumberTheory.TotientAsymptotic.PartBelowProduct

namespace OAI

/-! Arithmetic and normality of the actual terminal cutoff states. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_terminal_equation {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    D*factorProduct (fordFactorState t (Y b))=
      (fordFactorState t (Y b)).remainder*(∏ j,(fordFactorState t (Y b)).right j) := by
  have hD : 0 < D := by rcases hp with ⟨_,_,_,_,_,_,_,hD,_,_,_,_⟩; omega
  have hDs : (largestPrimeFactor D:ℝ) ≤ Y b := by
    rcases hp with ⟨_,_,_,_,_,_,_,_,_,hDs,_,_⟩; exact hDs
  have he := congrArg (fun n => partBelow n (Y b)) h.2.2.1
  rw [partBelow_mul hD.ne' (ford_left_product_pos h).ne',
    partBelow_mul h.1.ne' (ford_right_product_pos h).ne',
    partBelow_all_of_largest_le hD.ne' hDs,
    partBelow_all_of_largest_le h.1.ne' h.2.2.2.2.1] at he
  simpa only [factorProduct,fordFactorState,shiftedProduct,
    partBelow_prod _ _ (fun j _ => (ford_shift_pos h j).1.ne'),
    partBelow_prod _ _ (fun j _ => (ford_shift_pos h j).2.ne')] using he

lemma ford_terminal_largest {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U) :
    (largestPrimeFactor (factorProduct (fordFactorState t (Y b))):ℝ) ≤ Y b := by
  have hY : 1 ≤ Y b := (ford_scale_bounds hp).1.le.trans (ford_cutoff_ge_S hp le_rfl)
  have hb : largestPrimeFactor (factorProduct (fordFactorState t (Y b))) ≤ ⌊Y b⌋₊ := by
    apply largestPrimeFactor_le_of_prime_divisors (Nat.le_floor (by simpa using hY))
    intro p hpp hpd _
    change p ∣ ∏ j,partBelow (t.left j-1) (Y b) at hpd
    obtain ⟨j,_,hjp⟩ := (hpp.prime.dvd_finsetProd_iff _).mp hpd
    have hm := (Nat.mem_primeFactorsList_iff_dvd (partBelow_pos _ _).ne' hpp).mpr hjp
    apply Nat.le_floor
    exact of_decide_eq_true (List.mem_filter.mp ((partBelow_factors _ _).mem_iff.mpr hm)).2
  exact (Nat.cast_le.mpr hb).trans (Nat.floor_le (by linarith))

lemma ford_terminal_omega {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    ((factorProduct (fordFactorState t (Y b))).primeFactorsList.length:ℝ) ≤ 4*(b:ℝ)*B (Y b) := by
  exact normal_terminal_product_omega t.left (fun j => (h.2.1 j).1)
    (ford_scale_bounds hp).1 (by linarith [(ford_scale_bounds hp).2])
    (ford_cutoff_ge_S hp le_rfl)

end TotientAsymptotic

end

end OAI
