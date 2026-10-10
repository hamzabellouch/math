import OAI.Geometry.SurfaceImmersion.Geometry.CompactPositiveMetricJets
import OAI.Geometry.SurfaceImmersion.Geometry.UniformMetricPathBounds

namespace OAI

/-! Uniform compact first-jet families of actual atlas metric readings.
The constants depend on a fixed lower metric bound and C1 budget. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorPlaneRead_metric_lower (g h : SmoothMetric M) (c : ℝ)
    (hlower : ∀ p v, c*g.inner p v v ≤ h.inner p v v)
    (i : A.centers) {x : SmallModes.Base}
    (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (v : SmallModes.Base) :
    c*evaluate (A.tensorPlaneRead i g.inner x) v v ≤
      evaluate (A.tensorPlaneRead i h.inner x) v v := by
  rw [A.tensorPlaneRead_metric g i hx,A.tensorPlaneRead_metric h i hx,
    coordinateMetric_evaluate,coordinateMetric_evaluate]
  exact hlower (coordinateInverse (i : M) x)
    (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse (i : M)) x v)

theorem compact_metric_jet_family (g : SmoothMetric M) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ J : Set MetricFirstJet, IsCompact J ∧
      (∀ j ∈ J, metricJetDet j ≠ 0) ∧
      ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
        (∀ p v, c*g.inner p v v ≤ h.inner p v v) →
        ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
          (A.tensorPlaneRead i h.inner x,fderiv ℝ (A.tensorPlaneRead i h.inner) x) ∈ J := by
  classical
  obtain ⟨T,B,hT,hpos,hdet,_,hmem,_,_⟩ := A.metric_plane_read_bounds g
  obtain ⟨d,hd,hdlower⟩ := compact_positive_tensor_lower_bound hT (by
    intro H hH
    exact (tensor_positive_iff H).mpr ⟨hpos H hH,hdet H hH⟩)
  choose E hE hread using fun i : A.centers => A.tensorPlaneRead_bound i 1
  let R : ℝ := (∑ i, E i)*C
  let J := positiveMetricJetRegion (c*d) R
  refine ⟨J,positiveMetricJetRegion_compact _ _,
    fun j hj => positiveMetricJetRegion_det (mul_pos hc hd) hj,?_⟩
  intro h hbound hlower i x hx
  have hb := hread i h.inner 1 C zero_lt_one le_rfl hC h.contMDiff hbound
  have hEi : E i ≤ ∑ k, E k :=
    Finset.single_le_sum (fun k _ => hE k) (Finset.mem_univ i)
  have hv : ‖A.tensorPlaneRead i h.inner x‖ ≤ R :=
    (hb.norm_le (mem_univ x)).trans (mul_le_mul_of_nonneg_right hEi hC)
  have hderiv : ‖fderiv ℝ (A.tensorPlaneRead i h.inner) x‖ ≤ R := by
    have hb' := hb.deriv_le zero_lt_one (le_refl 1) (mem_univ x)
    simp only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] at hb'
    exact hb'.trans (mul_le_mul_of_nonneg_right hEi hC)
  refine ⟨max_le hv hderiv,?_⟩
  intro v
  calc
    (c*d)*‖v‖^2 = c*(d*‖v‖^2) := by ring
    _ ≤ c*evaluate (A.tensorPlaneRead i g.inner x) v v :=
      mul_le_mul_of_nonneg_left (hdlower _ (hmem i x hx) v) hc.le
    _ ≤ evaluate (A.tensorPlaneRead i h.inner x) v v :=
      A.tensorPlaneRead_metric_lower g h c hlower i hx v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
