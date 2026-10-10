import OAI.Analysis.IrrationalRotation.Analysis.ContinuityCoboundary
import OAI.Analysis.IrrationalRotation.Model.ParameterSmoothing

namespace OAI

namespace InvariantProjection.Continuity

variable {X I : Type*}

theorem backwardSum_finset_sum (σ : X ≃ X) (s : Finset I)
    (v : I → X → ℝ) (n : ℕ) (x : X) :
    backwardSum σ (fun y => ∑ i ∈ s, v i y) n x =
      ∑ i ∈ s, backwardSum σ (v i) n x := by
  simp only [backwardSum]
  exact Finset.sum_comm

theorem relocated_finset_sum (σ : X ≃ X) (s : Finset I)
    (h : I → X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ) (x : X) :
    relocated σ (fun y => ∑ i ∈ s, h i y) φ H x =
      ∑ i ∈ s, relocated σ (h i) φ H x := by
  simp only [relocated, Finset.sum_mul]
  exact Finset.sum_comm

theorem relocationTransfer_finset_sum (σ : X ≃ X) (s : Finset I)
    (h : I → X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ) (x : X) :
    relocationTransfer σ (fun y => ∑ i ∈ s, h i y) φ H x =
      ∑ i ∈ s, relocationTransfer σ (h i) φ H x := by
  simp only [relocationTransfer, backwardSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_comm

end InvariantProjection.Continuity

namespace Invariant233.CircleParameterData

open InvariantProjection.Continuity

theorem relocatedBlock_eq_sum_coordinates (p : CircleParameterData) (θ : ℝ)
    (j : ℕ) (x : Circle) :
    p.relocatedBlock θ j x = ∑ i ∈ p.block j,
      relocated (Equiv.addRight (θ : Circle))
        (fun y => circleSmoothedDrop (p.C j) (p.alpha θ i) (p.alpha θ i / 4)
          ((p.q i : ℤ) • y))
        (fun n y => p.partition j n y) (p.height j) x := by
  exact relocated_finset_sum _ _ _ _ _ _

theorem relocatedBlockTransfer_eq_sum_coordinates (p : CircleParameterData) (θ : ℝ)
    (j : ℕ) (x : Circle) :
    p.relocatedBlockTransfer θ j x = ∑ i ∈ p.block j,
      relocationTransfer (Equiv.addRight (θ : Circle))
        (fun y => circleSmoothedDrop (p.C j) (p.alpha θ i) (p.alpha θ i / 4)
          ((p.q i : ℤ) • y))
        (fun n y => p.partition j n y) (p.height j) x := by
  exact relocationTransfer_finset_sum _ _ _ _ _ _

end Invariant233.CircleParameterData

end OAI
