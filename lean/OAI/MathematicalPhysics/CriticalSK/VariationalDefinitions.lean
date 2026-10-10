import OAI.MathematicalPhysics.CriticalSK.Main

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

def continuousMixingAt {n : ℕ} (W : Disorder n) (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ ε}

def discreteMixingAt {n : ℕ} (W : Disorder n) (ε : ℝ) : ℕ :=
  sInf {k : ℕ | ∀ x, discreteDistance W k x ≤ ε}

def entropy {n : ℕ} (W : Disorder n) (g : Spin n → ℝ) : ℝ :=
  mean W (fun x => g x * Real.log (g x)) - mean W g * Real.log (mean W g)

def relaxationTime {n : ℕ} (W : Disorder n) : ℝ :=
  sSup {r : ℝ | ∃ f : Spin n → ℝ, 0 < variance W f ∧
    r = variance W f / dirichlet W f}

def logSobolevConstant {n : ℕ} (W : Disorder n) : ℝ :=
  sSup {r : ℝ | ∃ f : Spin n → ℝ, 0 < entropy W (fun x => f x ^ 2) ∧
    r = entropy W (fun x => f x ^ 2) / dirichlet W f}

def ExponentInProbability (X : (n : ℕ) → Disorder n → ℝ) (a : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Tendsto (fun n : ℕ => (disorderLaw n).real
      {W | (n : ℝ) ^ (a - δ) ≤ X n W ∧ X n W ≤ (n : ℝ) ^ (a + δ)})
      atTop (𝓝 1)

end CriticalSK
end

end OAI
