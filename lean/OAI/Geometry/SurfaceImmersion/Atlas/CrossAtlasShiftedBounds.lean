import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasBounds
import OAI.Geometry.SurfaceImmersion.Correction.GlobalShiftedSmoothing

namespace OAI

/-! Changing the fixed atlas preserves the unweighted derivative prefix. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem shiftedBound_change_atlas (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound q m s C F → B.ShiftedBound q m s (D*C) F := by
  classical
  choose D hD hd using fun j : ℕ => A.weightedBound_change_atlas (V := V) B j
  refine ⟨∑ j ∈ Finset.range (q+m+1), D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb i j hj x
  have hpow : 0 < s^(j-q) := pow_pos hs _
  have hh := hd j F 1 (C/s^(j-q)) zero_lt_one le_rfl (div_nonneg hC hpow.le) hF
    (fun k => (hb k).prefix hs hs1 hC hj)
  have hi := hh i j le_rfl x (mem_univ x)
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ] at hi
  calc
    _ ≤ s^(j-q)*(D j*(C/s^(j-q))) := mul_le_mul_of_nonneg_left hi hpow.le
    _ = D j*C := by field_simp
    _ ≤ (∑ k ∈ Finset.range (q+m+1),D k)*C :=
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
