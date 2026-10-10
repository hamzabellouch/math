import OAI.Geometry.SurfaceImmersion.Geometry.CompactPositiveTensorBound
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasBackgroundLowerBound
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledInitialMap

namespace OAI

/-! One scalar makes every immersion with the fixed atlas budget short.
The scale is selected before any finite boundary-intersection set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_induced_metric_upper_bound (g : SmoothMetric M) {C : ℝ} (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
      A.WeightedBound 1 1 C F → ∀ (p : M) (v : TangentSpace planeModel p),
        inducedForm F p v v ≤ D*g.inner p v v := by
  classical
  obtain ⟨T,B,hT,hpos,hdet,_,hmem,_,_⟩ := A.metric_plane_read_bounds g
  obtain ⟨c,hc,hcoercive⟩ := PhaseMean.compact_positive_tensor_lower_bound hT (by
    intro H hH
    exact (tensor_positive_iff H).mpr ⟨hpos H hH,hdet H hH⟩)
  choose R hR hread using fun i : A.centers => A.vectorChartRead_bound (V := Space) i 1
  let R0 : ℝ := ∑ i : A.centers, R i
  have hR0 : 0 ≤ R0 := Finset.sum_nonneg (fun i _ => hR i)
  let D := (R0*C)^2/c
  have hD : 0 ≤ D := div_nonneg (sq_nonneg _) hc.le
  refine ⟨D,hD,?_⟩
  intro F hF hb p v
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  have hp : p ∈ tsupport (A.weight i) := subset_tsupport _ (A.weightCore_nonzero i hi)
  let u := surfaceDifferential (chart (i : M)) p v
  have hlower : c*‖u‖^2 ≤ g.inner p v v := by
    have hm := hcoercive (A.tensorPlaneRead i g.inner
      (planeCoordinateIsometry (chart (i : M) p)))
      (hmem i _ ⟨chart (i : M) p,⟨p,hp,rfl⟩,rfl⟩) (planeCoordinateIsometry u)
    have hs : p ∈ (coordinateChart (i : M)).source := by
      simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
    rw [A.tensorPlaneRead_metric_on_weight g i hp] at hm
    have he := coordinateMetric_pullback_chart g (i : M) hs v v
    rw [A.coordinateChart_differential i (A.weight_support i hp)] at he
    change PhaseMean.evaluate _ (planeCoordinateIsometry u) (planeCoordinateIsometry u) = _ at he
    rw [he,planeCoordinateIsometry.norm_map] at hm
    exact hm
  have hdr := hread i F 1 C zero_lt_one le_rfl hC hF hb
  have hdn := hdr 1 le_rfl (chart (i : M) p) (mem_univ _)
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ,norm_iteratedFDeriv_one] at hdn
  have hRi : R i ≤ R0 := Finset.single_le_sum (fun j _ => hR j) (Finset.mem_univ i)
  have hdiff : ‖surfaceDifferential F p v‖ ≤ (R0*C)*‖u‖ := by
    rw [A.vectorChartRead_differential i hF hp]
    change ‖fderiv ℝ (A.vectorChartRead i F) (chart (i : M) p) u‖ ≤ _
    exact ((fderiv ℝ (A.vectorChartRead i F) (chart (i : M) p)).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hdn.trans (mul_le_mul_of_nonneg_right hRi hC)) (norm_nonneg u))
  have hsq : ‖surfaceDifferential F p v‖^2 ≤ (R0*C)^2*‖u‖^2 := by
    nlinarith [norm_nonneg (surfaceDifferential F p v),mul_nonneg (mul_nonneg hR0 hC) (norm_nonneg u)]
  calc
    inducedForm F p v v = ‖surfaceDifferential F p v‖^2 := real_inner_self_eq_norm_sq _
    _ ≤ (R0*C)^2*‖u‖^2 := hsq
    _ = D*(c*‖u‖^2) := by dsimp [D]; field_simp
    _ ≤ D*g.inner p v v := mul_le_mul_of_nonneg_left hlower hD

theorem uniform_initial_short_scale (g : SmoothMetric M) {C : ℝ} (hC : 0 ≤ C) :
    ∃ r : ℝ, 0 < r ∧ ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
      A.WeightedBound 1 1 C F → ∀ (p : M) (v : TangentSpace planeModel p),
        inducedForm (r • F) p v v ≤ (1/2 : ℝ)*g.inner p v v := by
  obtain ⟨D,hD,hbound⟩ := A.uniform_induced_metric_upper_bound g hC
  let r := Real.sqrt (1/(2*(D+1)))
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r^2 = 1/(2*(D+1)) := Real.sq_sqrt (by positivity)
  have hsmall : r^2*D ≤ (1/2 : ℝ) := by
    rw [hr2,div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ (by positivity : 0 < 2*(D+1))).2
    nlinarith
  refine ⟨r,hr,?_⟩
  intro F hF hb p v
  have he := congrArg (fun T : ∀ p : M, CovariantTwoTensor p => T p v v)
    (inducedTensor_const_smul hF r)
  change inducedForm (r • F) p v v = r^2*inducedForm F p v v at he
  rw [he]
  have hg : 0 ≤ g.inner p v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos p v hv).le
  exact (mul_le_mul_of_nonneg_left (hbound F hF hb p v) (sq_nonneg r)).trans
    (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsmall hg)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
