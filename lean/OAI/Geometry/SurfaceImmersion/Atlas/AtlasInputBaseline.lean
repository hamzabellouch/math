import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds

namespace OAI

/-! A fixed C2 neighborhood supplies the scale-independent input baseline. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem shifted_zero_bound_of_near {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      ∀ b : ℝ, A.WeightedBound 1 2 b (G-F) →
      ∀ t : ℝ, A.ShiftedBound 2 0 t (P+b) G := by
  obtain ⟨P,hP,hbase⟩ := A.exists_shifted_bound 2 0 hF
  have hbase' : A.WeightedBound 1 2 P F := by
    intro i j hj x _
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hbase i j (by omega) x
  refine ⟨P,hP,?_⟩
  intro G hG b hnear t
  have hsum := A.weightedBound_add (hG.sub hF) hF zero_le_one hnear hbase'
  change A.WeightedBound 1 2 (b+P) ((G-F)+F) at hsum
  have he : (G-F)+F = G := by abel
  rw [he] at hsum
  intro i j hj x
  have hj2 : j ≤ 2 := by omega
  have hh := hsum i j hj2 x (mem_univ x)
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,
    Nat.sub_eq_zero_of_le hj2,pow_zero,add_comm] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
