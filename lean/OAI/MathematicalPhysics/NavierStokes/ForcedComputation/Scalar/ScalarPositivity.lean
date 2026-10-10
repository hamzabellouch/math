import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMaximumPrinciple

namespace OAI

/-! Positivity from the scalar maximum principle. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set

theorem TorusScalarSolution.nonnegative {T ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : TorusScalarSolution T ν a h w w₀) (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (hh : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) (h₀ : ∀ x, 0 ≤ w₀ x) :
    ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ w t x := by
  let d : ℝ → Plane → ℝ := fun t x => -(scalarGenerator ν (a t) (w t) x + h t x)
  have hm := scalar_maximum_principle (w := fun t x => -w t x) (d := d) (a := a)
    hT hν hw.smooth.continuousOn.neg
    (fun t ht x n => by dsimp; rw [hw.periodic t ht x n])
    (fun t ht => (hw.slice_smooth ht).neg)
    (fun t ht x => (hw.equation t ⟨ht.1.le, ht.2⟩ x).neg)
    (fun t ht x => by
      dsimp only [d]
      rw [scalarGenerator_neg]
      linarith [hh t ⟨ht.1.le, ht.2⟩ x])
    (fun x => by simpa only [hw.initial, neg_nonpos] using h₀ x)
  exact fun t ht x => neg_nonpos.mp (hm t ht x)

end ForcedComputation.VelocityDetector

end

end OAI
