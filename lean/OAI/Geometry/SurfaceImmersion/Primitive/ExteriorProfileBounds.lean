import OAI.Geometry.SurfaceImmersion.Geometry.ExteriorApproximation
import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileFrame

namespace OAI

/-! The exterior C2 estimate controls all five unscaled boundary profiles. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes

lemma realBoundaryProfile_sub {F G : RField 4} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (z : ℝ) (p : Base) :
    realBoundaryProfile (G-F) z p = realBoundaryProfile G z p-realBoundaryProfile F z p := by
  have hd (v : Base) : coordDeriv v (G-F) = coordDeriv v G-coordDeriv v F := by
    funext y
    change (fderiv ℝ (G-F) y) v = _
    rw [fderiv_sub (hG.differentiable (by simp) y) (hF.differentiable (by simp) y)]
    rfl
  have hdd (v w : Base) : coordDeriv v (coordDeriv w (G-F)) =
      coordDeriv v (coordDeriv w G)-coordDeriv v (coordDeriv w F) := by
    rw [hd]
    funext y
    change (fderiv ℝ (coordDeriv w G-coordDeriv w F) y) v = _
    rw [fderiv_sub ((contDiff_real_coordDeriv hG w).differentiable (by simp) y)
      ((contDiff_real_coordDeriv hF w).differentiable (by simp) y)]
    rfl
  funext i
  fin_cases i
  · exact congrFun (hd dx) p
  · exact congrFun (hd dy) p
  · exact congrFun (hdd dy dy) p
  · exact congrFun (hdd dx dy) p
  · change z • coordDeriv dx (coordDeriv dx (G-F)) p =
      z • coordDeriv dx (coordDeriv dx G) p-z • coordDeriv dx (coordDeriv dx F) p
    rw [congrFun (hdd dx dx) p,Pi.sub_apply,smul_sub]

lemma realBoundaryProfile_one_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k F p‖ ≤ C) :
    ‖realBoundaryProfile F 1 p‖ ≤ C := by
  have h1 : ‖fderiv ℝ F p‖ ≤ C := by simpa only [norm_iteratedFDeriv_one] using hb 1 (by omega)
  have h2 : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C := by
    rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact hb 2 (by omega)
  have hv (v : Base) (hv : ‖v‖ ≤ 1) : ‖coordDeriv v F p‖ ≤ C := by
    exact ((fderiv ℝ F p).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by simpa using h1))
  have hvw (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
      ‖coordDeriv v (coordDeriv w F) p‖ ≤ C := by
    rw [real_second_coordDeriv ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p)]
    exact ((fderiv ℝ (fderiv ℝ F) p v).le_opNorm w).trans
      ((mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans (by
        simpa only [mul_one] using ((fderiv ℝ (fderiv ℝ F) p).le_opNorm v).trans
          ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by simpa using h2))))
  have hx : ‖dx‖ ≤ 1 := by simp [dx]
  have hy : ‖dy‖ ≤ 1 := by simp [dy]
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  fin_cases i
  · exact hv dx hx
  · exact hv dy hy
  · exact hvw dy dy hy hy
  · exact hvw dx dy hx hy
  · change ‖(1 : ℝ) • coordDeriv dx (coordDeriv dx F) p‖ ≤ C
    simpa only [one_smul] using hvw dx dx hx hx

end ClosedSurfaceR4.GeometryPreservation
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_profile_bound (j : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight j), A.outer j =ᶠ[𝓝 x] (fun _ => 1)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ p ∈ tsupport (A.weight j), V =ᶠ[𝓝 p] G →
      ‖realBoundaryProfile (spaceCoordinates ∘ A.vectorPlaneRead j W) 1
        (planeCoordinateIsometry (chart (j : M) p))-
        realBoundaryProfile (spaceCoordinates ∘ A.vectorPlaneRead j F) 1
        (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hbound⟩ := A.exterior_read_C2_bound j houter
  refine ⟨D,hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV p hp he
  have hF' := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth j hF)
  have hW' := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth j hW)
  rw [← realBoundaryProfile_sub hF' hW']
  have heq : (spaceCoordinates ∘ A.vectorPlaneRead j W)-(spaceCoordinates ∘ A.vectorPlaneRead j F) =
      spaceCoordinates ∘ A.vectorPlaneRead j (W-F) := by
    rw [A.vectorPlaneRead_sub]
    funext y
    exact (map_sub spaceCoordinates _ _).symm
  rw [heq]
  exact realBoundaryProfile_one_bound
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth j (hW.sub hF))) _
    (mul_nonneg hD (add_nonneg hb hc)) (hbound F G V W hF hG hV hW b c hb hc hGF hWV p hp he)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
