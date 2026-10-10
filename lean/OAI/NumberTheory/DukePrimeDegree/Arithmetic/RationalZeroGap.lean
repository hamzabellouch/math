import OAI.NumberTheory.DukePrimeDegree.Arithmetic.StarkZeros

namespace OAI

/-!
# The fixed rational-field zero gap

The final contradiction in odd-degree zero descent only needs a fixed
neighborhood of one where the rational completed zeta function is
nonzero. Continuity and its computed value at one supply that gap.
-/

open Filter Set
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.HeckeMellin

/-- The completed zeta function of the rational field is nonzero on a
fixed real interval ending at one. -/
theorem rational_completedXi_nonzero_near_one
    (σ : OrderedEmbeddings 1 ℚ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β ∈ Icc (1 - δ) 1,
      completedThetaXi σ (by simp : Module.finrank ℚ ℚ = 1) β ≠ 0 := by
  let f : ℂ → ℂ := completedThetaXi σ (by simp : Module.finrank ℚ ℚ = 1)
  have h1 : f 1 ≠ 0 := by
    exact dedekindXiZeros_ne_one_totallyReal σ (by simp)
  have hc : ContinuousAt (fun β : ℝ => f β) 1 :=
    (completedThetaXi_entire σ (by simp)).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_ne h1)
  refine ⟨ε / 2, by positivity, fun β hβ => ?_⟩
  apply he
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hβ.2)]
  linarith [hβ.1]

/-- A fixed rational-field zero gap contains every sufficiently narrow
discriminant-scaled interval used in Stark descent. -/
theorem rational_completedXi_nonzero_scaled
    (σ : OrderedEmbeddings 1 ℚ) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℝ, 4 ≤ L →
      ∀ β ∈ Icc (1 - a / L) 1,
        completedThetaXi σ (by simp : Module.finrank ℚ ℚ = 1) β ≠ 0 := by
  obtain ⟨a, ha, he⟩ := rational_completedXi_nonzero_near_one σ
  refine ⟨a, ha, fun L hL β hβ => he β ⟨?_, hβ.2⟩⟩
  have hdiv : a / L ≤ a := div_le_self ha.le (by linarith)
  linarith [hβ.1]

end DukePrimeDegree

end OAI
