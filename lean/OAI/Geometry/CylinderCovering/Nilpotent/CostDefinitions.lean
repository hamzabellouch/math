import OAI.Geometry.CylinderCovering.Nilpotent.BasicDefinitions

namespace OAI

noncomputable section

namespace CylinderCovering.Nilpotent

def speedSq (p : ℝ) : ℝ := v p ^ 2 + 2 * w p ^ 2
def integrand (k p : ℝ) : ℝ :=
  height k p ^ 2 / (2 * Real.sqrt (1 + k ^ 2 * speedSq p))
def I (k : ℝ) : ℝ := ∫ p in (-1 : ℝ)..1, integrand k p
def quadraticCoefficient (p : ℝ) : ℝ := a p / 2 - speedSq p / 16

def CostSavingStatement : Prop :=
  (∫ p in (-1 : ℝ)..1, a p) = 1 / 15 ∧
  (∫ p in (-1 : ℝ)..1, speedSq p) = 17 / 30 ∧
  Asymptotics.IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun k : ℝ => I k - (1 / 4 - k ^ 2 / 480)) (fun k : ℝ => k ^ 3) ∧
  (∀ k : ℝ, 0 ≤ k → k ≤ 1 →
    |I k - (1 / 4 - k ^ 2 / 480)| ≤ 4 * k ^ 3) ∧
  (∀ k : ℝ, 0 < k → k < 1 / 1920 → I k < 1 / 4) ∧
  ∀ᶠ k : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), I k < 1 / 4

end CylinderCovering.Nilpotent

end

end OAI
