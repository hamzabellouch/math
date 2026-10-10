import OAI.NumberTheory.JointDickman.UnconditionalMain

namespace OAI

/-! # The joint Dickman law for consecutive integers -/

namespace JointDickmanPaper

open Filter JointDickman
open scoped Topology

/-- Theorem 1: ordinary natural density, with both thresholds based at `n`. -/
theorem joint_law (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (realDensity (fun n =>
      (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b))
      atTop (𝓝 (Erdos970.NumberTheoryLean.Dickman.rho (1 / a) *
        Erdos970.NumberTheoryLean.Dickman.rho (1 / b))) :=
  jointDickmanLaw_unconditional a b ha ha1 hb hb1

/-- Corollary 2: the increasing strict ordering has natural density one half. -/
theorem increasing_order :
    Tendsto (realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac))
      atTop (𝓝 (1 / 2)) :=
  increasingOrderLaw_unconditional

/-- The reverse strict ordering also has natural density one half. -/
theorem decreasing_order :
    Tendsto (realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac))
      atTop (𝓝 (1 / 2)) :=
  decreasingOrderLaw_unconditional

end JointDickmanPaper

end OAI
