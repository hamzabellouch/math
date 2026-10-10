import OAI.NumberTheory.TotientAsymptotic.PPTComparisonBridge
import OAI.NumberTheory.TotientAsymptotic.NormalTerminalFactors

namespace OAI

/-!
The factor-count cost of fixing the small left tail in the PPT application
of Ford's comparison lemma.  Normality bounds the count through the
terminal cutoff, rather than through the much larger size of the tail.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem ppt_small_tail_totient_omega {h : ℕ} (p : Fin h → ℕ) {S V : ℝ}
    (hp : ∀ i, IsNormalPrime S (p i)) (hinj : Function.Injective p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V)
    (hsmall : ∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) :
    (((∏ i, p i).totient).primeFactorsList.length : ℝ) ≤ 4*(h : ℝ)*B V := by
  have ht (i : Fin h) : partBelow (p i-1) V = p i-1 :=
    partBelow_all_of_largest_le
      (Nat.sub_pos_of_lt (hp i).1.one_lt).ne' (hsmall i)
  have hb := normal_terminal_product_omega p hp hS hBS hSV
  simpa only [ht, ppt_totient_primeProduct p (fun i => (hp i).1) hinj,
    shiftedProduct] using hb

/-- The seed contribution stays fixed; the tail contributes only through
its number of primes and the double logarithm of the terminal cutoff. -/
theorem ppt_small_tail_seed_omega {h d : ℕ} (p : Fin h → ℕ) {S V : ℝ}
    (hd : 0 < d) (hp : ∀ i, IsNormalPrime S (p i)) (hinj : Function.Injective p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V)
    (hsmall : ∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) :
    ((d*(∏ i, p i).totient).primeFactorsList.length : ℝ) ≤
      d.primeFactorsList.length + 4*(h : ℝ)*B V := by
  have hpos : 0 < (∏ i, p i).totient := Nat.totient_pos.mpr
    (Finset.prod_pos (fun i _ => (hp i).1.pos))
  rw [omega_count_mul hd.ne' hpos.ne', Nat.cast_add]
  have htail := ppt_small_tail_totient_omega p hp hinj hS hBS hSV hsmall
  linarith only [htail]

/-- Explicit additional cost of using `D=d*φ(a)` in the `l=0`
specialization of the comparison estimate. -/
theorem ppt_small_tail_comparison_cost {h d : ℕ} (b : ℕ) (p : Fin h → ℕ) {S V : ℝ}
    (hd : 0 < d) (hp : ∀ i, IsNormalPrime S (p i)) (hinj : Function.Injective p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSV : S ≤ V)
    (hsmall : ∀ i, (largestPrimeFactor (p i-1) : ℝ) ≤ V) :
    (b+1 : ℝ)^((d*(∏ i, p i).totient).primeFactorsList.length) ≤
      (b+1 : ℝ)^d.primeFactorsList.length *
        Real.exp (4*(h : ℝ)*B V*Real.log (b+1)) := by
  have hbase : (1 : ℝ) ≤ b+1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le b)
  have hpos : (0 : ℝ) < b+1 := by positivity
  have hΩ := ppt_small_tail_seed_omega p hd hp hinj hS hBS hSV hsmall
  calc
    _ ≤ (b+1 : ℝ)^((d.primeFactorsList.length : ℝ)+4*(h : ℝ)*B V) := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hbase hΩ
    _ = _ := by
      rw [Real.rpow_add hpos, Real.rpow_natCast, Real.rpow_def_of_pos hpos]
      congr 2
      ring

end TotientAsymptotic

end

end OAI
