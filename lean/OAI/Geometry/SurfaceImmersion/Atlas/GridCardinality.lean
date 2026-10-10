import OAI.Geometry.SurfaceImmersion.Atlas.GridRestoredGeometry

namespace OAI

/-! Explicit polynomial growth of the variable grid and its quadratic labels. -/
noncomputable section
open scoped BigOperators ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma gridPhaseIndex_card (s : A.centers → Finset Index) :
    (Fintype.card (A.GridPhaseIndex s) : ℝ) = 3*∑ i : A.centers, ((s i).card : ℝ) := by
  classical
  simp only [GridPhaseIndex,Fintype.card_sigma,Fintype.card_prod,Fintype.card_coe,
    Fintype.card_fin,Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gridPhaseIndex_quadratic_bound (s : A.centers → Finset Index) {D x : ℝ}
    (hD : 0 ≤ D) (hx : 1 ≤ x)
    (hcard : (∑ i : A.centers, ((s i).card : ℝ)) ≤ D*x^12) :
    (Fintype.card (A.GridPhaseIndex s) : ℝ)+
      2*(Fintype.card (A.GridPhaseIndex s) : ℝ)^2 ≤ (3*D+18*D^2)*x^24 := by
  have hcount : (Fintype.card (A.GridPhaseIndex s) : ℝ) ≤ 3*D*x^12 := by
    rw [A.gridPhaseIndex_card]
    nlinarith
  have hn : 0 ≤ (Fintype.card (A.GridPhaseIndex s) : ℝ) := Nat.cast_nonneg _
  have hp : x^12 ≤ x^24 := pow_le_pow_right₀ hx (by omega)
  calc
    _ ≤ 3*D*x^12+2*(3*D*x^12)^2 := by gcongr
    _ = 3*D*x^12+18*D^2*x^24 := by ring
    _ ≤ (3*D+18*D^2)*x^24 := by nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
