import OAI.Geometry.SurfaceImmersion.Geometry.GlobalInputRecurrence

namespace OAI

/-! A slow two-jet profile gives a uniform fast weighted budget, including
the low derivatives that are obscured by the shifted budget alone. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma weighted_of_shifted_two {F : M → V} {z s C : ℝ} {m : ℕ}
    (hz : 0 ≤ z) (hzs : z ≤ s) (hs1 : s ≤ 1)
    (hb : A.ShiftedBound 2 m s C F) : A.WeightedBound z m C F := by
  intro i j hj x _
  rw [iteratedFDerivWithin_univ]
  have hp : z^j ≤ s^(j-2) :=
    (pow_le_pow_left₀ hz hzs j).trans
      (pow_le_pow_of_le_one (hz.trans hzs) hs1 (Nat.sub_le j 2))
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
    (hb i j (by omega) x)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
