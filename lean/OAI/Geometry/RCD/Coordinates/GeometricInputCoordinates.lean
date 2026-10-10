import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction
import OAI.Geometry.RCD.Coordinates.ScalarBochnerCoordinates
import OAI.Geometry.RCD.Metric.LowerCurvatureVolume

namespace OAI

/-! # Coordinates under local geometric estimates

For K > 0 the same metric measure space is RCD(0,n). The local estimates
transfer to that curvature bound because their curvature side conditions
are automatic.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_geometric_inputs {K : ℝ} {n : ℕ}
    (hn : 2≤n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      LocalPoissonHarmonicCompactnessInput hX →
      LocalInitialSplittingInput hX → LocalTransformationInput hX →
      LocalFlatSplittingInput hX → LocalVolumeRigidityInput hX →
      LocalHarmonicMomentCompactnessInput hX → LocalMeasuredCoordinateInput hX →
      HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  let := hX.hausdorff_regular
  dsimp only
  intro p hp hvol hc hi ht hs hr hh hm
  by_cases hK : K ≤ 0
  · exact regular_coordinates_of_scalar_bochner hn hX hp hvol
      (hX.scalarBochner_nonpositive K n hn hK p) hc hi ht hs hr hh hm
  · have hK0 : 0 ≤ K := (lt_of_not_ge hK).le
    let h0 := hX.zero_of_nonneg_curvature hn hK0
    have hc0 : LocalPoissonHarmonicCompactnessInput h0 := by
      intro hn S hS q r ε hrad _ heps hepslim u V w f hmeas hrep hwharm hnorm henergy hf hquad
      obtain ⟨a,ha,model,hmodel⟩ := hc hn S hS q r ε hrad (fun k =>
        le_trans (by norm_num : (-1:ℝ) ≤ 0) (mul_nonneg hK0 (sq_nonneg (r k))))
        heps hepslim u V w f hmeas hrep hwharm hnorm henergy hf hquad
      exact ⟨a,ha,model,⟨hmodel.moments,hmodel.tests⟩⟩
    have hi0 : LocalInitialSplittingInput h0 := by
      intro hn β hβ
      obtain ⟨ε,hε,happly⟩ := hi hn β hβ
      refine ⟨ε,hε,?_⟩
      intro q r hrad _
      exact happly q r hrad ((neg_nonpos.mpr hε.le).trans (mul_nonneg hK0 (sq_nonneg r)))
    have ht0 : LocalTransformationInput h0 := by
      intro hn β η hβ hη
      obtain ⟨δ,hδ,happly⟩ := ht hn β η hβ hη
      refine ⟨δ,hδ,?_⟩
      intro q r hrad _
      exact happly q r hrad ((neg_nonpos.mpr hδ.le).trans (mul_nonneg hK0 (sq_nonneg r)))
    have hs0 : LocalFlatSplittingInput h0 := by
      intro hn τ hτ
      obtain ⟨δ,ε,hδ,hε,happly⟩ := hs hn τ hτ
      refine ⟨δ,ε,hδ,hε,?_⟩
      intro q r hrad _
      exact happly q r hrad ((neg_nonpos.mpr hε.le).trans (mul_nonneg hK0 (sq_nonneg r)))
    have hr0 : LocalVolumeRigidityInput h0 := by
      intro hn ε hε
      obtain ⟨δ,hδ,happly⟩ := hr hn ε hε
      refine ⟨δ,hδ,?_⟩
      intro q r hrad _
      exact happly q r hrad ((neg_nonpos.mpr hδ.le).trans (mul_nonneg hK0 (sq_nonneg r)))
    have hh0 : LocalHarmonicMomentCompactnessInput h0 := by
      intro S hS q r ε hrad _
      exact hh S hS q r ε hrad (fun k =>
        le_trans (by norm_num : (-1:ℝ) ≤ 0) (mul_nonneg hK0 (sq_nonneg (r k))))
    have hm0 : LocalMeasuredCoordinateInput h0 := by
      intro hn S ε hS hε
      obtain ⟨δ,hδ,happly⟩ := hm hn S ε hS hε
      refine ⟨δ,hδ,?_⟩
      intro q r hrad _
      exact happly q r hrad ((neg_nonpos.mpr hδ.le).trans (mul_nonneg hK0 (sq_nonneg r)))
    exact regular_coordinates_of_scalar_bochner hn h0 hp hvol
      (h0.scalarBochner_nonpositive 0 n hn le_rfl p) hc0 hi0 ht0 hs0 hr0 hh0 hm0

end RegularPointCoordinates

end

end OAI
