import OAI.Analysis.CircleDomains.LengthArea

namespace OAI

/-!
# Passing finite-hole flux estimates to the limit

The rigidity manuscript's finite-hole estimate bounds the flux with an
error of sixteen times the remaining mixed-radius sum. Square-summability
of the source and target radii makes this error tend to zero along arbitrary
finite subsets of the index type, giving `eq:limiting-flux`.
-/

open Filter
open scoped Topology

namespace CircleDomainRigidity

/-- The mixed-radius tail vanishes as the retained finite family exhausts
the holes. The hypotheses ensure that the total mixed-radius sum is the
actual convergent series. -/
theorem tendsto_mixed_radius_tail {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j => r j ^ 2)) (hs : Summable (fun j => s j ^ 2)) :
    Tendsto (fun F : Finset ι => ∑' j : {j // j ∉ F}, r j * s j)
      atTop (𝓝 0) := by
  have hsum := LengthArea.summable_mul_of_squares hr hs
  have hpartial : Tendsto (fun F : Finset ι => ∑ j ∈ F, r j * s j)
      atTop (𝓝 (∑' j, r j * s j)) := hsum.hasSum
  have htail : Tendsto
      (fun F : Finset ι => (∑' j, r j * s j) - ∑ j ∈ F, r j * s j)
      atTop (𝓝 ((∑' j, r j * s j) - ∑' j, r j * s j)) :=
    tendsto_const_nhds.sub hpartial
  convert htail using 1
  · funext F
    have hsplit := hsum.sum_add_tsum_subtype_compl F
    linarith
  · simp

/-- A uniform finite-hole flux estimate gives the limiting flux bound.
The coefficient `16` is the two-direction multiplicity bound appearing
immediately before `eq:limiting-flux` in the rigidity manuscript. -/
theorem limiting_flux_of_finite_hole_estimates {ι : Type*} {r s : ι → ℝ}
    {A I : ℝ} (hr : Summable (fun j => r j ^ 2))
    (hs : Summable (fun j => s j ^ 2))
    (hfinite : ∀ F : Finset ι, 2 * A ≤ 2 * I +
      2 * Real.pi * (∑ j ∈ F, r j * s j) +
      16 * (∑' j : {j // j ∉ F}, r j * s j)) :
    2 * A ≤ 2 * I + 2 * Real.pi * (∑' j, r j * s j) := by
  have hsum := LengthArea.summable_mul_of_squares hr hs
  have hpartial : Tendsto (fun F : Finset ι => ∑ j ∈ F, r j * s j)
      atTop (𝓝 (∑' j, r j * s j)) := hsum.hasSum
  have htail := tendsto_mixed_radius_tail hr hs
  have hlimit : Tendsto
      (fun F : Finset ι => 2 * I + 2 * Real.pi * (∑ j ∈ F, r j * s j) +
        16 * (∑' j : {j // j ∉ F}, r j * s j)) atTop
      (𝓝 (2 * I + 2 * Real.pi * (∑' j, r j * s j) + 16 * 0)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hpartial)).add
      (tendsto_const_nhds.mul htail)
  have hle := ge_of_tendsto hlimit (Filter.Eventually.of_forall hfinite)
  simpa using hle

end CircleDomainRigidity

end OAI
