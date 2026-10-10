import OAI.Geometry.SurfaceImmersion.Geometry.RealJetPrefixBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasFiniteCancellation

namespace OAI

/-! Weighted two-jet estimates in a fixed phase chart from the global input norm. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phaseChart_twoJet_bound (i : A.centers)
    {T : SmallModes.Base → SmallModes.Base} (hT : ContDiff ℝ ∞ T)
    (K : Compacts SmallModes.Base) {U : Set SmallModes.Base}
    (hU : IsOpen U) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : M → Space) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel spaceModel ∞ F →
      A.ShiftedBound 2 m s C F →
      WeightedEstimates.WeightedBound U s m (D*C)
        (realTwoJet ((spaceCoordinates ∘ A.vectorPlaneRead i F) ∘ T)) := by
  obtain ⟨B,hB,hb⟩ := A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  obtain ⟨E,hE,he⟩ := compact_realTwoJet_comp_prefix_bound hT K hU hUK m
  let L : ℝ := ‖spaceCoordinates.toContinuousLinearMap‖*B
  let D : ℝ := 1+E*L
  have hL : 0 ≤ L := mul_nonneg (norm_nonneg _) hB
  have hD : 1 ≤ D := le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans hE) hL)
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hp
  have hlocal := A.vectorPlaneRead_smooth i hF
  have hprefix (j : ℕ) (hj : j ≤ m+2) :
      WeightedEstimates.WeightedBound univ 1 j (L*C/s^(j-2))
        (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    have hh := (hb F s C hs hs1 hC hF hp j (by omega)).linear
      uniqueDiffOn_univ zero_le_one hlocal.contDiffOn spaceCoordinates.toContinuousLinearMap
    simpa only [L,mul_div_assoc,mul_assoc,ContinuousLinearEquiv.coe_coe] using hh
  have hh := he (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (spaceCoordinates.contDiff.comp hlocal) s (L*C) hs hs1 (mul_nonneg hL hC) hprefix
  apply hh.mono_const
  calc
    E*(L*C) = (E*L)*C := (mul_assoc _ _ _).symm
    _ ≤ D*C := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
