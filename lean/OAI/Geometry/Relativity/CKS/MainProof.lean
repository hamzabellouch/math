import OAI.Geometry.Relativity.CKS.SchwarzschildIntrinsicEquality
import OAI.Geometry.Relativity.CKS.Transfer
import OAI.Geometry.Relativity.CKS.MainDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular
open CKSSchwarzschild

def InteriorSurface.schwarzschildImmersion {m : ℝ} (hm : 0 < m)
    {T : Type v} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]
    (D : InteriorSurface (smoothMetric hm) (tensorInner m) (schwarzschildAtlas hm) T) :
    IntrinsicInteriorImmersion m T where
  map := D.map
  smooth := D.smooth
  immersion := D.immersion
  interior := D.interior
  normal := D.normal
  normal_unit := D.normal_unit
  normal_orthogonal := D.normal_orthogonal

lemma schwarzschild_no_additional_horizons {m : ℝ} (hm : 0 < m) :
    NoAdditionalHorizons.{0,v} (smoothMetric hm) (tensorInner m)
      (cksData hm).chart (schwarzschildAtlas hm) := by
  intro T _ _ _ _ _ _ _ D _ h
  apply no_intrinsic_closed_apparent_horizon hm (D.schwarzschildImmersion hm)
  intro p
  exact InteriorSurface.ComponentwiseApparent.pointwise D h p

lemma schwarzschild_attainment {m : ℝ} (hm : 0 < m) :
    SchwarzschildAttainment.{v} m hm := by
  have h := schwarzschild_equality_example hm
  refine ⟨{
    smooth_tensor := h.smooth_tensor
    symmetric_tensor := h.symmetric_tensor
    orientable := h.orientable
    boundary_compact := h.boundary_compact
    boundary_nonempty := h.boundary_nonempty
    complete := h.complete
    dec := h.dec
    timelike := h.timelike
    boundary_connected := h.boundary_connected
    boundary_marginal := schwarzschildMarginal hm
    positive_area := h.positive_area
    no_horizons := schwarzschild_no_additional_horizons hm },
    h.horizon_regular,?_,h.full_cut_area,h.equality⟩
  rw [bondiMass,h.bondi]
  simpa using Real.sqrt_sq hm.le

theorem conditional_connected_horizon
    (hAF : WeakAFExteriorInequality.{u}) :
    (∀ (N : Type u) [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
      [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]
      (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
      (d : CKSData g K) (A : CoefficientAtlas g K),
      MainHypotheses.{u,v} g K d A →
      Real.sqrt (minimumEnclosingArea g / (16*Real.pi)) ≤ bondiMass d) ∧
    (∀ (m : ℝ) (hm : 0 < m), SchwarzschildAttainment.{v} m hm) := by
  constructor
  · intro N _ _ _ _ _ _ g K d A h
    exact transfer_inequality hAF g K h.smooth_tensor h.symmetric_tensor h.orientable
      h.boundary_compact h.boundary_nonempty h.complete h.dec d h.timelike h.boundary_marginal
  · intro m hm
    exact schwarzschild_attainment hm

end CKSMain

end

end OAI
