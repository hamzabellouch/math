import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadDifferential
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoefficientCoordinates

namespace OAI

/-! Fixed atlas seminorms control ordinary values and first derivatives on
all the original compact chart supports. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem coordinate_C1_bound {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ F : M → V, ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      B.WeightedBound 1 1 D F → ∀ i p, p ∈ tsupport (B.weight i) →
        ‖F p‖ ≤ E ∧ ‖fderiv ℝ (F ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ E := by
  classical
  choose R hR hread using fun i : B.centers => B.vectorChartRead_bound (V := V) i 1
  let E := 1+(∑ i, R i)*D
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hR i)
  have hE : 1 ≤ E := by
    dsimp only [E]
    linarith [mul_nonneg hsum hD]
  refine ⟨E,hE,?_⟩
  intro F hF hb i p hp
  have h := hread i F 1 D zero_lt_one le_rfl hD hF hb
  have hi : R i*D ≤ E := by
    have hh := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hR j) (Finset.mem_univ i)) hD
    dsimp only [E]
    linarith
  have hv := (h.norm_le (mem_univ (chart (i : M) p))).trans hi
  rw [B.vectorChartRead_on_support i F ⟨p,hp,rfl⟩,
    (chart (i : M)).left_inv (B.weight_support i hp)] at hv
  refine ⟨hv,?_⟩
  have hd := h.deriv_le zero_lt_one le_rfl (mem_univ (chart (i : M) p))
  simp only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] at hd
  rw [B.vectorChartRead_fderiv i hF ⟨p,hp,rfl⟩] at hd
  exact hd.trans hi

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
