import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import OAI.NumberTheory.Ostmann.ZeroDensity.RealZeroKernel

namespace OAI

/-! # Summing the zero-free comparison with a finite exceptional set -/

namespace Ostmann

open scoped BigOperators Classical

theorem realZeroKernel_le_inv {a y : ℝ} (ha : 0 < a) :
    realZeroKernel a y ≤ a⁻¹ := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  calc
    _ ≤ a / a ^ 2 := div_le_div_of_nonneg_left ha.le ha2 (by nlinarith [sq_nonneg y])
    _ = _ := by field_simp

theorem realZeroKernel_zero_free (ρ : ℂ) (s s₀ c δ C : ℝ)
    (hρ : 0 ≤ ρ.re ∧ ρ.re < 1) (hs : 1 < s) (hss : s ≤ s₀) (hs₀ : s₀ ≤ 2)
    (hc : 0 < c) (hC5 : 5 ≤ C) (hCc : 1 + c⁻¹ ≤ C)
    (hgap : s₀ - s ≤ δ) (hregion : ρ.im ^ 2 < 1 → c * δ ≤ s - ρ.re) :
    realZeroKernel (s - ρ.re) ρ.im ≤ C * realZeroKernel (s₀ - ρ.re) ρ.im := by
  have ha : 0 < s - ρ.re := by linarith [hρ.2]
  have hab : s - ρ.re ≤ s₀ - ρ.re := by linarith
  have hb : s₀ - ρ.re ≤ 2 := by linarith [hρ.1]
  have hn : 0 ≤ realZeroKernel (s₀ - ρ.re) ρ.im := realZeroKernel_nonneg (by linarith)
  by_cases hy : 1 ≤ ρ.im ^ 2
  · exact (realZeroKernel_high ha hab hb hy).trans (mul_le_mul_of_nonneg_right hC5 hn)
  · exact (realZeroKernel_gap ha hab hc (by linarith) (hregion (lt_of_not_ge hy))).trans
      (mul_le_mul_of_nonneg_right hCc hn)

/-- An arbitrary zero family may retain finitely many exceptions. The
comparison proves summability at s as well as the bound; summability at s
is not assumed. Multiplicities are represented by repeated indices. -/
theorem realZeroKernel_sum_bound {ι : Type*} (ρ : ι → ℂ) (E : Finset ι)
    (s s₀ c δ C : ℝ) (hρ : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re < 1)
    (hs : 1 < s) (hss : s ≤ s₀) (hs₀ : s₀ ≤ 2) (hc : 0 < c)
    (hC5 : 5 ≤ C) (hCc : 1 + c⁻¹ ≤ C) (hgap : s₀ - s ≤ δ)
    (hregion : ∀ i ∉ E, (ρ i).im ^ 2 < 1 → c * δ ≤ s - (ρ i).re)
    (hsum : Summable (fun i => realZeroKernel (s₀ - (ρ i).re) (ρ i).im)) :
    Summable (fun i => realZeroKernel (s - (ρ i).re) (ρ i).im) ∧
      (∑' i, realZeroKernel (s - (ρ i).re) (ρ i).im) ≤
        C * (∑' i, realZeroKernel (s₀ - (ρ i).re) (ρ i).im) +
          ∑ i ∈ E, (s - (ρ i).re)⁻¹ := by
  let e : ι → ℝ := fun i => if i ∈ E then (s - (ρ i).re)⁻¹ else 0
  have he : Summable e := summable_of_ne_finset_zero (s := E) (by
    intro i hi
    simp only [e, ite_eq_right hi])
  have hE : ∑' i, e i = ∑ i ∈ E, (s - (ρ i).re)⁻¹ := by
    rw [tsum_eq_sum (s := E) (by intro i hi; simp only [e, ite_eq_right hi])]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [e, ite_eq_left hi]
  have hmaj := (hsum.mul_left C).add he
  have hp (i : ι) : realZeroKernel (s - (ρ i).re) (ρ i).im ≤
      C * realZeroKernel (s₀ - (ρ i).re) (ρ i).im + e i := by
    have ha : 0 < s - (ρ i).re := by linarith [(hρ i).2]
    have hn : 0 ≤ C * realZeroKernel (s₀ - (ρ i).re) (ρ i).im := by
      apply mul_nonneg (by linarith)
      apply realZeroKernel_nonneg
      linarith [(hρ i).2]
    by_cases hi : i ∈ E
    · have hb := realZeroKernel_le_inv (y := (ρ i).im) ha
      simp only [e, ite_eq_left hi]
      linarith
    · simpa only [e, ite_eq_right hi, add_zero] using
        realZeroKernel_zero_free (ρ i) s s₀ c δ C (hρ i) hs hss hs₀ hc hC5 hCc hgap (hregion i hi)
  have hsnew : Summable (fun i => realZeroKernel (s - (ρ i).re) (ρ i).im) :=
    Summable.of_nonneg_of_le (fun i => realZeroKernel_nonneg (by linarith [(hρ i).2])) hp hmaj
  refine ⟨hsnew, ?_⟩
  have hb := hsnew.tsum_le_tsum hp hmaj
  rwa [Summable.tsum_add (hsum.mul_left C) he, hsum.tsum_mul_left, hE] at hb

end Ostmann

end OAI
