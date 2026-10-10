import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseStability
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetCompactRange

namespace OAI

/-! Compact jet ranges and coefficient bounds derived from the actual atlas input norms. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_jet_profiles
    (U : A.centers → Set JetPolynomial.Base) (hU : ∀ i, IsOpen (U i))
    (KU : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hUK : ∀ i, U i ⊆ KU i)
    (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ (Q : A.centers → Set LowJet) (B : A.centers → ℕ → ℝ),
      (∀ i, IsCompact (Q i)) ∧ (∀ i m, 1 ≤ B i m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      (∀ i, MapsTo (lowJet (A.jetChartMap i G)) (U i) (Q i)) ∧
      ∀ i m, WeightedEstimates.WeightedBound (U i) s m (B i m) (lowJet (A.jetChartMap i G)) := by
  classical
  choose E hE he using fun i m => A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  let C := fun i m => ‖spaceCoordinates.toContinuousLinearMap‖ * E i m * R m
  have hC (i m) : 0 ≤ C i m := mul_nonneg
    (mul_nonneg (norm_nonneg _) (hE i m)) (hR m)
  have hpref (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
      (s : ℝ≥0) (hs : 0 < (s:ℝ)) (hs1 : s ≤ 1)
      (hb : ∀ m, A.ShiftedBound 2 m s (R m) G) (i m j) (hj : j ≤ m+2) :
      WeightedEstimates.WeightedBound (U i) 1 j (C i m/(s:ℝ)^(j-2)) (A.jetChartMap i G) := by
    have hh := (he i m G s (R m) hs hs1 (hR m) hG (hb m) j (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    have hc := weightedBound_comp_isometry planeCoordinateIsometry
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) hh
    have heq : (spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry =
        A.jetChartMap i G := by
      funext x
      have hx := congrFun (A.jetChartMap_plane i G) (planeCoordinateIsometry x)
      simpa only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hx.symm
    change WeightedEstimates.WeightedBound univ 1 j _
      ((spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry) at hc
    rw [heq] at hc
    have hb' : WeightedEstimates.WeightedBound univ 1 j (C i m/(s:ℝ)^(j-2)) (A.jetChartMap i G) := by
      simpa only [C,mul_div_assoc,mul_assoc] using hc
    exact hb'.restrict_open (hU i)
  choose Q hQ hmaps using fun i => bounded_lowJet_range (hU i) (KU i) (hUK i) (hC i 0)
  choose D hD hd using fun i m => bounded_lowJet_prefix (hU i) (KU i) (hUK i) m
  refine ⟨Q,fun i m => D i m+C i m,hQ,fun i m => (hD i m).trans
    (le_add_of_nonneg_right (hC i m)),?_⟩
  intro G hG s hs hs1 hb
  constructor
  · intro i
    apply hmaps i _ (A.jetChartMap_smooth i hG)
    simpa only [Nat.sub_self,pow_zero,div_one] using hpref G hG s hs hs1 hb i 0 2 (by omega)
  · intro i m
    exact hd i m (A.jetChartMap i G) (A.jetChartMap_smooth i hG) s (C i m)
      hs hs1 (hC i m) (hpref G hG s hs hs1 hb i m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
