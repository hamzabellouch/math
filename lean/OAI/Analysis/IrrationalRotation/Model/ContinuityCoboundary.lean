import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Basic.Real.Basic

namespace OAI

noncomputable section

namespace InvariantProjection.Continuity

variable {X : Type*}

def backwardSum (σ : X ≃ X) (v : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∑ r ∈ Finset.range n, v ((σ.symm : X → X)^[r + 1] x)

def relocated (σ : X ≃ X) (h : X → ℝ) (φ : ℕ → X → ℝ)
    (H : ℕ) (x : X) : ℝ :=
  ∑ n ∈ Finset.range (H + 1),
    h ((σ.symm : X → X)^[n] x) * φ n ((σ.symm : X → X)^[n] x)

def relocationTransfer (σ : X ≃ X) (h : X → ℝ) (φ : ℕ → X → ℝ)
    (H : ℕ) (x : X) : ℝ :=
  ∑ n ∈ Finset.range (H + 1), backwardSum σ (fun y => h y * φ n y) n x

def backwardAverage (σ : X ≃ X) (v : X → ℝ) (W : ℕ) (x : X) : ℝ :=
  (W : ℝ)⁻¹ * backwardSum σ v W x

def backgroundTransfer (σ : X ≃ X) (v : X → ℝ) (W : ℕ) (x : X) : ℝ :=
  (W : ℝ)⁻¹ * ∑ n ∈ Finset.range W, backwardSum σ v (n + 1) x

end InvariantProjection.Continuity

end

end OAI
