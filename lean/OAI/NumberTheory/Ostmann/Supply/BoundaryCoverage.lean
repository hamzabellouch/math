import OAI.NumberTheory.Ostmann.Supply.BoundaryCoverageScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_natural_boundary_small (d : Decomposition) (E : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ) (U : ℝ),
      (n:ℝ) ≤ Real.exp (Real.exp ((9/10:ℝ)*L)) → Real.exp (-E*L) ≤ U →
      (boundaryPairCount d ((supplyRadius L)^2):ℝ) *
          ((supplyTruncation L+1:ℝ)^2*(n+1:ℝ)^(2*supplyTruncation L)) ≤
        η*U*(((supplyRadius L)^2:ℕ):ℝ)/Real.log (((supplyRadius L)^2:ℕ):ℝ) := by
  filter_upwards [supply_square_tendsto.eventually (eventually_boundary_weighted_scale d hη),
    eventually_boundary_weight_bound,eventually_boundary_inverse_main_bound E]
    with L hscale hweight hmain
  intro n U hn hU
  exact hscale _ U (by positivity) (hweight n hn) (hmain.trans hU)

theorem eventually_prime_coverage_upperWindows (d : Decomposition) (E : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (p : ℕ → ℕ) [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i)))
        (n : ℕ) (U : ℝ),
      (n:ℝ) ≤ Real.exp (Real.exp ((9/10:ℝ)*L)) → Real.exp (-E*L) ≤ U →
      (∑ q ∈ primesInInterval ((supplyRadius L)^2/2) ((supplyRadius L)^2),
        naturalKernelWeight p S n (supplyTruncation L) q) ≤
      (∑ a ∈ upperWindow d.A ((supplyRadius L)^2),
        ∑ b ∈ upperWindow d.B ((supplyRadius L)^2),
          naturalKernelWeight p S n (supplyTruncation L) (a+b)) +
        η*U*(((supplyRadius L)^2:ℕ):ℝ)/Real.log (((supplyRadius L)^2:ℕ):ℝ) := by
  filter_upwards [eventually_natural_boundary_small d E hη,
    supply_square_tendsto.eventually_ge_atTop (2*d.cutoff)] with L hsmall hcut
  intro p hp S n U hn hU
  have hc : d.cutoff ≤ (supplyRadius L)^2/2 := by omega
  have hcoverage := actual_weighted_coverage_boundary d ((supplyRadius L)^2) hc
    (naturalKernelWeight p S n (supplyTruncation L))
    ((supplyTruncation L+1:ℝ)^2*(n+1:ℝ)^(2*supplyTruncation L))
    (naturalKernelWeight_nonneg p S n (supplyTruncation L)) (by positivity)
    (naturalKernelWeight_le p S n (supplyTruncation L))
  exact hcoverage.trans (add_le_add le_rfl (hsmall n U hn hU))

end Ostmann.Supply

end

end OAI
