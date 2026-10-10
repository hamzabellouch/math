import OAI.Analysis.CircleDomains.Uniformization.BandLimits
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace OAI

/-!
# Unique traces outside the countable band support

For a bounded real coordinate the interval band is the actual interval
between the lower and upper boundary limits. A zero band budget forces
these limits to agree and gives convergence from the physical domain.
Square summability of the budgets makes all exceptions countable.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

noncomputable def realBoundaryTrace {X : Type*} [TopologicalSpace X]
    (G : Set X) (f : X → ℝ) (x : X) : ℝ := liminf f (𝓝[G] x)

theorem tendsto_boundaryTrace_of_zero_band
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ} {M : ℝ}
    (hM : ∀ y ∈ G, |f y| ≤ M) {x : X} (hx : x ∈ closure G)
    (hband : limsup f (𝓝[G] x) - liminf f (𝓝[G] x) ≤ 0) :
    Tendsto f (𝓝[G] x) (𝓝 (realBoundaryTrace G f x)) := by
  let : NeBot (𝓝[G] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hbounds : ∀ᶠ y in 𝓝[G] x, -M ≤ f y ∧ f y ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact abs_le.mp (hM y hy)
  have hlower : IsBoundedUnder (· ≥ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_ge (hbounds.mono (fun _ hy => hy.1))
  have hupper : IsBoundedUnder (· ≤ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_le (hbounds.mono (fun _ hy => hy.2))
  have hle := liminf_le_limsup hupper hlower
  exact tendsto_of_liminf_eq_limsup rfl (by dsimp [realBoundaryTrace]; linarith)
    hupper hlower

theorem countable_band_support {X : Type*} {a : X → ℝ}
    (ha : Summable (fun x => a x ^ 2)) : {x | a x ≠ 0}.Countable := by
  simpa only [Function.support, ne_eq, sq_eq_zero_iff] using ha.countable_support

/-- The coordinate has a genuine limiting trace at every point of the
dust except for a countable set explicitly given by its nonzero budget. -/
theorem boundaryTrace_outside_countable_set
    {X : Type*} [TopologicalSpace X] {G B : Set X} {f a : X → ℝ} {M : ℝ}
    (hM : ∀ y ∈ G, |f y| ≤ M) (hB : B ⊆ closure G)
    (ha : Summable (fun x => a x ^ 2))
    (hband : ∀ x ∈ B, limsup f (𝓝[G] x) - liminf f (𝓝[G] x) ≤ a x) :
    ∃ S : Set X, S.Countable ∧ ∀ x ∈ B \ S,
      Tendsto f (𝓝[G] x) (𝓝 (realBoundaryTrace G f x)) := by
  refine ⟨{x | a x ≠ 0}, countable_band_support ha, ?_⟩
  intro x hx
  apply tendsto_boundaryTrace_of_zero_band hM (hB hx.1)
  have hxzero : a x = 0 := by simpa only [mem_ofPred_eq, not_not] using hx.2
  simpa only [hxzero] using hband x hx.1

end CircleDomainRigidity

end OAI
