import OAI.NumberTheory.JointDickman.Amplification.SubsetCardEntropy
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! # Uniform entropy estimates across regularity windows -/

namespace JointDickman
open Set

/-- Uniformity includes both endpoint cardinalities. The population stays
away from zero because the prefix scale g is fixed and positive. -/
theorem entropy_window_stability {g ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (τ x y r : ℝ), 0 ≤ τ → τ ≤ τ₀ →
      0 ≤ r → r ≤ 1/2 → |x-g/2| ≤ τ → |y-g*r| ≤ 3*τ →
      x*Real.binEntropy (y/x) ≤ (g/2)*Real.binEntropy (2*r)+ε := by
  let D : Set (ℝ × ℝ) := (Icc (g/4) (2*g)) ×ˢ (Icc (-g) (2*g))
  let F : ℝ × ℝ → ℝ := fun z => z.1*Real.binEntropy (z.2/z.1)
  have hcont : ContinuousOn F D := by
    intro z hz
    have hzne : z.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by linarith : 0 < g/4) hz.1.1)
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul continuousAt_fst
    apply Real.binEntropy_continuous.continuousAt.comp
    exact continuousAt_snd.div continuousAt_fst hzne
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let τ₀ := min (g/4) (δ/4)
  have hτ₀ : 0 < τ₀ := lt_min (by positivity) (by positivity)
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ x y r hτ hτsmall hr hr1 hx hy
  have hτg : τ ≤ g/4 := hτsmall.trans (min_le_left _ _)
  have hτδ : τ ≤ δ/4 := hτsmall.trans (min_le_right _ _)
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hz : (x,y) ∈ D := by
    change (g/4 ≤ x ∧ x ≤ 2*g) ∧ (-g ≤ y ∧ y ≤ 2*g)
    constructor
    · constructor <;> linarith
    · constructor <;> nlinarith
  have hw : (g/2,g*r) ∈ D := by
    change (g/4 ≤ g/2 ∧ g/2 ≤ 2*g) ∧ (-g ≤ g*r ∧ g*r ≤ 2*g)
    constructor
    · constructor <;> linarith
    · constructor <;> nlinarith
  have hd : dist (x,y) (g/2,g*r) < δ := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact max_lt (by linarith) (by linarith)
  have he := hclose (x,y) hz (g/2,g*r) hw hd
  have hratio : g*r/(g/2) = 2*r := by field_simp
  change |x*Real.binEntropy (y/x)-(g/2)*Real.binEntropy (g*r/(g/2))| < ε at he
  rw [hratio] at he
  linarith [(abs_lt.mp he).2]

end JointDickman

end OAI
