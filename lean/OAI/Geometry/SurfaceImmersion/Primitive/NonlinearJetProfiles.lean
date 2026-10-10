import OAI.Geometry.SurfaceImmersion.Primitive.AtlasJetProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.CompactCompositionPrefix

namespace OAI

/-! Actual slow-map jet bounds in a fixed nonlinear phase chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem nonlinear_jet_profiles (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base}
    (hT : ContDiff ℝ ∞ T) {S : Set JetPolynomial.Base} (hS : IsOpen S)
    (hSc : IsCompact (closure S)) (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ (Q : Set LowJet) (B : ℕ → ℝ), IsCompact Q ∧ (∀ m, 1 ≤ B m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      MapsTo (lowJet (A.jetChartMap i G ∘ T)) S Q ∧
      ∀ m, WeightedEstimates.WeightedBound S s m (B m) (lowJet (A.jetChartMap i G ∘ T)) := by
  choose E hE he using fun m => A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  choose D hD hd using fun m => compact_composition_prefix hT hS hSc m
  let C := fun m => D m * (‖spaceCoordinates.toContinuousLinearMap‖ * E m * R m)
  have hC (m) : 0 ≤ C m := mul_nonneg (zero_le_one.trans (hD m))
    (mul_nonneg (mul_nonneg (norm_nonneg _) (hE m)) (hR m))
  have hpref (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
      (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
      (hb : ∀ m, A.ShiftedBound 2 m s (R m) G) (m j) (hj : j ≤ m+2) :
      WeightedEstimates.WeightedBound S 1 j (C m/(s:ℝ)^(j-2)) (A.jetChartMap i G ∘ T) := by
    apply hd m (A.jetChartMap i G) s (‖spaceCoordinates.toContinuousLinearMap‖ * E m * R m)
      hs (mul_nonneg (mul_nonneg (norm_nonneg _) (hE m)) (hR m))
      (A.jetChartMap_smooth i hG) ?_ j hj
    intro k hk
    have hh := (he m G s (R m) hs hs1 (hR m) hG (hb m) k (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    have hc := weightedBound_comp_isometry planeCoordinateIsometry
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) hh
    have heq : (spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry =
        A.jetChartMap i G := by
      funext x
      have hx := congrFun (A.jetChartMap_plane i G) (planeCoordinateIsometry x)
      simpa only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hx.symm
    change WeightedEstimates.WeightedBound univ 1 k _
      ((spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry) at hc
    rw [heq] at hc
    simpa only [mul_div_assoc,mul_assoc] using hc
  let K : TopologicalSpace.Compacts JetPolynomial.Base := ⟨closure S,hSc⟩
  obtain ⟨Q,hQ,hmaps⟩ := bounded_lowJet_range hS K subset_closure (hC 0)
  choose J hJ hj using fun m => bounded_lowJet_prefix hS K subset_closure m
  refine ⟨Q,fun m => J m+C m,hQ,fun m => (hJ m).trans (le_add_of_nonneg_right (hC m)),?_⟩
  intro G hG s hs hs1 hb
  refine ⟨?_,fun m => hj m _ ((A.jetChartMap_smooth i hG).comp hT) s (C m) hs hs1 (hC m)
    (hpref G hG s hs hs1 hb m)⟩
  apply hmaps _ ((A.jetChartMap_smooth i hG).comp hT)
  simpa only [Nat.sub_self,pow_zero,div_one] using hpref G hG s hs hs1 hb 0 2 (by omega)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
