import OAI.Geometry.SurfaceImmersion.Correction.GlobalShiftedSmoothing
import OAI.Geometry.SurfaceImmersion.Geometry.ShiftedScaleGain

namespace OAI

/-! The inherited-map part of the all-order correction recurrence. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Shrinking the scale gains one ratio in every positive weighted order. -/
theorem shifted_shrink_with_prefix {q m : ℕ} {t τ P C : ℝ} {f : M → V}
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C) f :=
  fun i => (hb i).shrink_with_prefix (hc i) ht hτ hτt hP hC

/-- The new map keeps the old low-derivative baseline; its inherited high
orders contract, and the actual increment contributes its own budget. -/
theorem shifted_map_recurrence {q m : ℕ} {t τ P C D : ℝ} {f u : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f)
    (hu : ContMDiff planeModel 𝓘(ℝ, V) ∞ u)
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (hd : A.ShiftedBound q m τ D u)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C + D) (f + u) := by
  have hsh := A.shifted_shrink_with_prefix hb hc ht hτ hτt hP hC
  intro i
  rw [localize_add]
  exact (hsh i).add
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hu) hτ (hd i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
