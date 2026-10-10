import OAI.MeasureTheory.Falconer.Radial.GraphTorusRadial
import OAI.MeasureTheory.Falconer.Graphs.GraphPolarAnnulus

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphPlaneAngle (η : Plane) : ℝ :=
  (polarCoord (graphPlaneEquiv.symm η)).2

def graphGlobalSlice (a b z : ℝ) : Set Plane :=
  graphPlaneEquiv '' (polarCoord.symm ''
    graphPolarRectangle (2*a/Real.sqrt (1+z^2)) (2*b/Real.sqrt (1+z^2)))

theorem graphPlaneEquiv_symm_radius (η : Plane) :
    (polarCoord (graphPlaneEquiv.symm η)).1 = ‖η‖ := by
  rw [← graphPlaneEquiv_norm, MeasurableEquiv.apply_symm_apply]

theorem sourceArcLength_pair_graph_plane_interval
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (‖η‖*Real.sqrt (1+z^2)/2)
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z)) := by
  rw [sourceArcLength_pair_graph_radial_interval hF hab]
  apply integral_congr_ae
  filter_upwards with z
  have hs : 0 < Real.sqrt (1+z^2) := by positivity
  let f : ℝ × ℝ → ℂ := fun p => F (p.1*Real.sqrt (1+z^2)/2)
    (sourceUnitDirection (p.2+Real.arctan z))
    (sourceUnitDirection (p.2-Real.arctan z))
  have hf : Continuous f := hF.comp
    (((continuous_fst.mul continuous_const).div_const 2).prodMk
      ((continuous_sourceUnitDirection.comp (continuous_snd.add continuous_const)).prodMk
        (continuous_sourceUnitDirection.comp (continuous_snd.sub continuous_const))))
  have he := graph_plane_rectangle_integral f hf
    (by positivity : 0 < 2*a/Real.sqrt (1+z^2))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab (by norm_num)) hs.le)
  rw [← he, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with η
  dsimp only [f, graphPlaneAngle]
  rw [graphPlaneEquiv_symm_radius, smul_smul, mul_inv_rev]

theorem sourceArcLength_pair_graph_plane_rotated
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (axis : ℝ) :
    (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (‖η‖*Real.sqrt (1+z^2)/2)
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis)) := by
  let G : ℝ → UnitCircle → UnitCircle → ℂ := fun t u v => F t u (sourceCircleRotate axis v)
  have hg : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => G p.1 p.2.1 p.2.2) :=
    hF.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((sourceCircleRotate_isometry axis).continuous.comp (continuous_snd.comp continuous_snd))))
  have he : (∫ t in a..b, ∫ u, ∫ v, F t u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ t in a..b, ∫ u, ∫ v, G t u v ∂sourceArcLength ∂sourceArcLength := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact (sourceArcLength_pair_rotate_right (F := F t) axis
      (hF.comp (continuous_const.prodMk continuous_id)).measurable).symm
  rw [he, sourceArcLength_pair_graph_plane_interval hg ha hab]
  simp only [G, sourceCircleRotate_comp]

theorem sourceArcLength_pair_graph_plane_normalized
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r in (R*a)..(R*b), ∫ u, ∫ v, F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (R*(‖η‖*Real.sqrt (1+z^2)/2))
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis)) := by
  rw [graph_radial_interval_normalization _ hR]
  exact sourceArcLength_pair_graph_plane_rotated
    (F := fun t u v => F (R*t) u v)
    (hF.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)) ha hab axis

end PlanarFalconer

end OAI
