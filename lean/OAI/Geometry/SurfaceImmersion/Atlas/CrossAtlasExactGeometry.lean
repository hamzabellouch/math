import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasBounds
import OAI.Geometry.SurfaceImmersion.Geometry.ExactFastFamily
import OAI.Geometry.SurfaceImmersion.Geometry.UniformFastNormalMargin
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasImmersionGeometry

namespace OAI

/-! Exact limits retain the geometric hypotheses needed for the next primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes JetPolynomial JetPolynomial.Perturbation
local instance crossExactGeometricFastFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossExactGeometricFastFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance crossExactGeometricFastDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance crossExactGeometricFastDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance crossExactGeometricFastSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossExactGeometricFastSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exact_geometric_metric_with_property_in_atlas [T2Space M] (B₀ : SmoothingAtlas M) (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c b V₀ : ℝ) (hc : 0 < c) (hb : 0 < b) (hV₀ : 0 ≤ V₀)
    (property : ℝ → (M → Space) → Prop)
    (hfamily : A.GeometricFastFamilyWithProperty g R c b V₀ property)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F ∧ property z F ∧
      IsSmoothIsometricImmersion M g G ∧ Nonempty (MetricGoodPhaseData g G) ∧
      B₀.WeightedBound 1 2 (z^8) (G-F) := by
  obtain ⟨B,hB,hall⟩ := A.exact_metric_with_property g houter R c b V₀ hc hb hV₀ property hfamily
  obtain ⟨η,hη,hη1,hnormal⟩ := uniform_fast_normal_margin R c B b hc (zero_le_one.trans hB) hb
  obtain ⟨D,hD,hball⟩ := A.readJetBall_radius
  obtain ⟨E,hE,hchange⟩ := A.weightedBound_change_atlas (V := Space) B₀ 2
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hK : 0 < D+E+1 := by positivity
  obtain ⟨z,hz,hzcap,hz1,F,G,hF,hproperty,hG,hclose,hread,hgeom⟩ :=
    hall (min η ζ) (lt_min hη hζ) (D+E+1) hK
  have hzη := hzcap.trans_le (min_le_left _ _)
  have hzζ := hzcap.trans_le (min_le_right _ _)
  have hcloseA : A.WeightedBound 1 2 (z^8/D) (G-F) := fun i =>
    (hclose i).mono_const (div_le_div_of_nonneg_left (pow_nonneg hz.le _) hDpos (by linarith))
  have hclose' : A.WeightedBound 1 2 ((z^2)^4/D) (G-F) := by
    convert hcloseA using 1; ring
  have hjet := hball (z^2) F G hF hG.1 hclose'
  have hsη : z^2 ≤ η := (show z^2 ≤ z from by
    simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 (by norm_num : 1 ≤ 2)).trans hzη.le
  have hlocal := fun i x hx => hnormal (z^2) (pow_pos hz 2) hsη
    (spaceCoordinates ∘ A.vectorPlaneRead i F) (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) (hread i) x
    (hgeom i x hx).1 (hgeom i x hx).2.1 (hgeom i x hx).2.2
    (hjet.2 i x hx).1 (hjet.2 i x hx).2
  have hgeometry := A.geometry_of_chartwise_good hG.1 houter (by
    intro p
    obtain ⟨i,hi⟩ : ∃ i : A.centers, A.weight i p ≠ 0 := by
      by_contra! hz
      have hh := A.partition p
      simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hh
      norm_num at hh
    have hp : p ∈ tsupport (A.weight i) := subset_tsupport _ hi
    have hx : planeCoordinateIsometry (chart (i : M) p) ∈
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
      ⟨chart (i : M) p,⟨p,hp,rfl⟩,rfl⟩
    obtain ⟨hI,hN⟩ := hlocal i _ hx
    have hNZ : realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p)) ≠ 0 :=
      norm_pos_iff.mp ((half_pos hb).trans_le hN)
    obtain ⟨ξ,Q,_,_,hgood,_⟩ := PhaseGeometry.positive_good_phase_data hNZ
      (H₀ := ![(1:ℝ),0,1]) (by simp) (by simp)
    exact ⟨i,hp,hI,ξ 0,hgood 0⟩)
  refine ⟨z,hz,hzζ,hz1,F,G,hF,hproperty,hG,
    MetricGoodPhaseData.nonempty g hG.1 hgeometry.1 hgeometry.2,?_⟩
  have hbclose := hchange (G-F) 1 (z^8/(D+E+1)) zero_lt_one le_rfl
    (div_nonneg (pow_nonneg hz.le _) hK.le) (hG.1.sub hF) hclose
  intro i
  apply (hbclose i).mono_const
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hK).mpr
  nlinarith [pow_nonneg hz.le 8]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
