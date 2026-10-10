import OAI.Geometry.Immersion.ClosedSurface.QuadraticMean

namespace OAI

/-! Exact recombination of phase targets split by a finite partition. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.QuadraticMean

lemma realMode_sum {n : ℕ} {ι : Type*} [Fintype ι] (θ : ℝ) (A : ι → CVec n) :
    realMode θ (∑ i, A i) = ∑ i, realMode θ (A i) := by
  funext k
  simp [realMode,realPart,Finset.mul_sum]

lemma displacement_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : Base → ℝ) (A : ι → Base → CVec n) :
    displacement τ φ (fun x => ∑ i, A i x) = fun x => ∑ i, displacement τ φ (A i) x := by
  funext x
  exact realMode_sum (φ x / τ) (fun i => A i x)

end ClosedSurfaceR4.QuadraticMean

end

end OAI
