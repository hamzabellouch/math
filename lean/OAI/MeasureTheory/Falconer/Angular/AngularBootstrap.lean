import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Endpoint of the thin-tube bootstrap

This is the order-theoretic step in Proposition `prep:thin-upgrade`.
Its hypotheses describe the closed set of available exponents inside
`[k - 1, k - 1 / 2]`, with strict improvement below the endpoint.
-/

namespace Falconer
open Set

/-- A closed family of available exponents containing the integer starting
exponent and admitting a strict improvement below the desired endpoint
contains the half-integer endpoint. -/
theorem thin_tube_bootstrap_endpoint (k : ℕ) (A : Set ℝ)
    (hclosed : IsClosed A) (hstart : (k : ℝ) - 1 ∈ A)
    (hupper : ∀ q ∈ A, q ≤ (k : ℝ) - 1 / 2)
    (himprove : ∀ q ∈ A, q < (k : ℝ) - 1 / 2 → ∃ q' ∈ A, q < q') :
    (k : ℝ) - 1 / 2 ∈ A := by
  have hnonempty : A.Nonempty := ⟨_, hstart⟩
  have hbounded : BddAbove A := ⟨(k : ℝ) - 1 / 2, hupper⟩
  have hsup : sSup A ∈ A := hclosed.csSup_mem hnonempty hbounded
  have hsup_upper : sSup A ≤ (k : ℝ) - 1 / 2 := hupper _ hsup
  by_cases heq : sSup A = (k : ℝ) - 1 / 2
  · exact heq ▸ hsup
  · obtain ⟨q, hq, hlt⟩ := himprove _ hsup (lt_of_le_of_ne hsup_upper heq)
    exact False.elim ((not_lt_of_ge (le_csSup hbounded hq)) hlt)

/-- At resolution `R⁻¹`, increasing the cap exponent by at most `e` costs
only the allowed factor `R ^ e`. This is the quantitative inequality used
when closing the set of available exponents in `prep:thin-upgrade`. -/
theorem cap_exponent_loss_transfer {R u q q' e : ℝ}
    (hR : 1 ≤ R) (hu : R⁻¹ ≤ u) (hqq : q ≤ q') (hgap : q' - q ≤ e) :
    u ^ q ≤ R ^ e * u ^ q' := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hupos : 0 < u := (inv_pos.mpr hRpos).trans_le hu
  have hcompare : u ^ (q - q') ≤ R ^ e := by
    calc
      u ^ (q - q') ≤ (R⁻¹) ^ (q - q') :=
        Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hRpos) hu (sub_nonpos.mpr hqq)
      _ = R ^ (q' - q) := by
        rw [← Real.rpow_neg_eq_inv_rpow]
        congr 1
        ring
      _ ≤ R ^ e := Real.rpow_le_rpow_of_exponent_le hR hgap
  calc
    u ^ q = u ^ (q - q') * u ^ q' := by
      rw [← Real.rpow_add hupos]
      congr 1
      ring
    _ ≤ R ^ e * u ^ q' := mul_le_mul_of_nonneg_right hcompare (Real.rpow_nonneg hupos.le _)

end Falconer

end OAI
