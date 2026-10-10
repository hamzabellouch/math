import OAI.Combinatorics.ProgressionColoring.FiniteGaps
import Mathlib.Data.Int.Basic

namespace OAI

namespace QuantitativeVanDerWaerden

/-- The endpoints of a residue fiber of size at least two differ by a positive
number of denominator steps, at least one for each intervening index. -/
theorem residue_fiber_span (J : Finset ℕ) (hJ : J.Nonempty) {h k : ℕ}
    (hh : 0 < h) (hcard : 2 ≤ J.card)
    (hcongr : ∀ a ∈ J, ∀ b ∈ J, (h : ℤ) ∣ (b : ℤ) - (a : ℤ))
    (hbound : ∀ j ∈ J, j < k) :
    ∃ c : ℕ, 0 < c ∧ J.card - 1 ≤ c ∧
      J.max' hJ - J.min' hJ = c * h ∧ c * h < k := by
  have hdiv : ∀ a ∈ J, ∀ b ∈ J, a ≤ b → h ∣ b - a := by
    intro a ha b hb hab
    apply Int.natCast_dvd_natCast.mp
    simpa only [Int.natCast_sub hab] using hcongr a ha b hb
  have hgap : ∀ a ∈ J, ∀ b ∈ J, a < b → h ≤ b - a := by
    intro a ha b hb hab
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hab) (hdiv a ha b hb hab.le)
  have hpacking := gap_mul_card_sub_one_le_span J hJ h hgap
  have hminmax : J.min' hJ ≤ J.max' hJ := J.min'_le _ (J.max'_mem hJ)
  obtain ⟨c, hc⟩ := hdiv _ (J.min'_mem hJ) _ (J.max'_mem hJ) hminmax
  have hcardc : J.card - 1 ≤ c := Nat.le_of_mul_le_mul_left (by rwa [hc] at hpacking) hh
  have hspan : J.max' hJ - J.min' hJ = c * h := hc.trans (Nat.mul_comm h c)
  refine ⟨c, by omega, hcardc, hspan, ?_⟩
  rw [← hspan]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (hbound _ (J.max'_mem hJ))

end QuantitativeVanDerWaerden

end OAI
