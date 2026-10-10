import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleDivisorGeometry

namespace OAI

/-! # The analytic zero count is a finite natural degree -/

open Set Function MeromorphicOn
namespace DefocusingNLS

noncomputable def countingDivisorPoints (V : ℝ) (f : ℂ → ℂ) : Finset ℂ :=
  ((divisor f (closedCountingRectangle V)).finiteSupport
    (isCompact_closedCountingRectangle V)).toFinset

@[simp] theorem mem_countingDivisorPoints (V : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    z ∈ countingDivisorPoints V f ↔ divisor f (closedCountingRectangle V) z ≠ 0 := by
  classical
  simp [countingDivisorPoints, Function.mem_support]

noncomputable def countingZeroDegree (V : ℝ) (f : ℂ → ℂ) : ℕ :=
  ∑ z ∈ countingDivisorPoints V f, (divisor f (closedCountingRectangle V) z).toNat

theorem countingDivisorPoints_subset (V : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0) :
    ∀ z ∈ countingDivisorPoints V f, z ∈ countingRectangle V := by
  intro z hz
  exact counting_divisor_support_interior V f hf hn ((mem_countingDivisorPoints V f z).mp hz)

theorem rectangleZeroCount_eq_degree (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0) :
    rectangleZeroCount V f = (countingZeroDegree V f : ℕ∞) := by
  classical
  have ho := rectangle_analyticOrder_ne_top V hV f hf hn
  unfold rectangleZeroCount
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := countingDivisorPoints V f)]
  · unfold countingZeroDegree
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro z hz
    have hm := countingDivisorPoints_subset V f hf hn z hz
    rw [indicator_of_mem hm]
    have hd := counting_divisor_eq_orderNat V hV f hf hn z (countingRectangle_subset_closed V hm)
    rw [hd, Int.toNat_natCast, Nat.cast_analyticOrderNatAt (ho z (countingRectangle_subset_closed V hm))]
  · intro z hz
    by_cases hm : z ∈ countingRectangle V
    · rw [indicator_of_mem hm]
      have hd : divisor f (closedCountingRectangle V) z = 0 := by
        simpa only [mem_countingDivisorPoints, not_not] using hz
      have he := counting_divisor_eq_orderNat V hV f hf hn z (countingRectangle_subset_closed V hm)
      have hn0 : analyticOrderNatAt f z = 0 := by exact_mod_cast (he.symm.trans hd)
      rw [← Nat.cast_analyticOrderNatAt (ho z (countingRectangle_subset_closed V hm)), hn0]
      rfl
    · simp [hm]

end DefocusingNLS

end OAI
