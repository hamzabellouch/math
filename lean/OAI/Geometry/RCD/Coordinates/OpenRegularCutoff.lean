import OAI.Geometry.RCD.Coordinates.RegularCompactCutoff

namespace OAI

/-! # Interior regular cutoffs around compact sets -/

open Set Filter Metric MeasureTheory
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Every compact subset of an open set admits a compact Lipschitz plateau
with an actual L² weak Laplacian. Finite unions of the RCD ball cutoffs
supply the arbitrary shape without an additional analytic hypothesis. -/
theorem NoncollapsedRCD.exists_open_regular_cutoff {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {Ω S : Set X} (hΩ : IsOpen Ω) (hS : IsCompact S) (hsub : S ⊆ Ω) :
    letI := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    ∃ χ : RegularCompactCutoff (hausdorff n X) hX.quadratic,
      tsupport χ.weight ⊆ Ω ∧ ∀ x ∈ S, χ.weight x=1 := by
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  apply hS.induction_on (p := fun T => ∃ χ : RegularCompactCutoff μ hX.quadratic,
    tsupport χ.weight ⊆ Ω ∧ ∀ x ∈ T, χ.weight x=1)
  · refine ⟨RegularCompactCutoff.zero,?_,by simp⟩
    simp [RegularCompactCutoff.zero]
  · intro T U hTU hU
    obtain ⟨χ,hχ,hχ1⟩ := hU
    exact ⟨χ,hχ,fun x hx => hχ1 x (hTU hx)⟩
  · intro T U hT hU
    obtain ⟨χ,hχ,hχ1⟩ := hT
    obtain ⟨η,hη,hη1⟩ := hU
    refine ⟨χ.union η,(χ.union_support η).trans (union_subset hχ hη),?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact χ.union_one_left η (hχ1 x hx)
    · exact χ.union_one_right η (hη1 x hx)
  · intro x hx
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hΩ x (hsub hx)
    have hr : 0 < ε/3 := by positivity
    obtain ⟨C,-,⟨χ⟩⟩ := hX.goodCutoff_exists hn x hr
    let η : RegularCompactCutoff μ hX.quadratic := {
      weight := χ.weight
      lip := (C/(ε/3)).toNNReal
      lipschitz := χ.lipschitz
      compact := χ.hasCompactSupport μ hX.quadratic
      bounds := χ.bounds
      sobolev := χ.sobolev
      representative := χ.representative
      laplacian := χ.laplacian
      weak_laplacian := χ.weak_laplacian }
    refine ⟨ball x (ε/3),mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr),η,?_,χ.one⟩
    apply (χ.tsupport_subset μ hX.quadratic).trans
    intro y hy
    apply hball
    have hd : dist y x ≤ 2*(ε/3) := hy
    show dist y x < ε
    linarith

end RegularPointCoordinates

end

end OAI
