import Mathlib

namespace OAI

/-! # The joint Dickman law for consecutive integers -/

namespace Erdos970.NumberTheoryLean.DelayConstruction

noncomputable def kernel (f : ℝ → ℝ) (t : ℝ) : ℝ := f (t - 1) / max 1 t

noncomputable def stepApprox (σ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u => 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t

noncomputable def delay (σ u : ℝ) : ℝ := stepApprox σ ⌈u⌉₊ u

end Erdos970.NumberTheoryLean.DelayConstruction

namespace Erdos970.NumberTheoryLean.Dickman

/-- The continuous delay-equation construction of the Dickman function. -/
noncomputable def rho : ℝ → ℝ := DelayConstruction.delay (-1)

end Erdos970.NumberTheoryLean.Dickman

namespace JointDickman

noncomputable def empiricalCount (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 2 N).filter P).card

/-- Ordinary natural density over `2 ≤ n ≤ X`, normalized by the real endpoint. -/
noncomputable def realDensity (P : ℕ → Prop) (X : ℝ) : ℝ :=
  (empiricalCount P ⌊X⌋₊ : ℝ) / X

end JointDickman

namespace JointDickmanPaper

open Filter JointDickman
open scoped Topology

/-- Theorem 1: ordinary natural density, with both thresholds based at `n`. -/
theorem joint_law (a b : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1) :
    Tendsto (realDensity (fun n =>
      (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧ ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b))
      atTop (𝓝 (Erdos970.NumberTheoryLean.Dickman.rho (1 / a) *
        Erdos970.NumberTheoryLean.Dickman.rho (1 / b))) := by
  sorry

/-- Corollary 2: the increasing strict ordering has natural density one half. -/
theorem increasing_order :
    Tendsto (realDensity (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac))
      atTop (𝓝 (1 / 2)) := by
  sorry

/-- The reverse strict ordering also has natural density one half. -/
theorem decreasing_order :
    Tendsto (realDensity (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac))
      atTop (𝓝 (1 / 2)) := by
  sorry

end JointDickmanPaper

end OAI
