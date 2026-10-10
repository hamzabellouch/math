import OAI.Geometry.Relativity.CKS.SurfaceVolumeGlobalLower
import OAI.Geometry.Relativity.CKS.CutAreaDefinitions

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [SecondCountableTopology N]

theorem area_finite (g : SmoothMetric (N := N)) (D : OuterDomain N) : area g D < ⊤ := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  exact isCompact_univ.measure_lt_top

theorem area_lower (g G : SmoothMetric (N := N)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x v, c * g.inner x v v ≤ G.inner x v v) (D : OuterDomain N) :
    ENNReal.ofReal c * area g D ≤ area G D := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  have h := CKSSurfaceVolume.riemannianVolume_lower
    (cutMetric g D).toContinuousRiemannianMetric (cutMetric G D).toContinuousRiemannianMetric hc
    (CKSInducedArea.inducedMetric_lower g G (cutInclusion D) (cutInclusion_smooth D)
      (cutInclusion_derivative_injective D) hlow)
  exact h univ

theorem minEnclosingArea_lower (g G : SmoothMetric (N := N)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x v, c * g.inner x v v ≤ G.inner x v v) :
    ENNReal.ofReal c * minEnclosingArea g ≤ minEnclosingArea G := by
  unfold minEnclosingArea
  apply le_iInf
  intro D
  exact (mul_le_mul' le_rfl (iInf_le _ D)).trans (area_lower g G hc hlow D)

theorem minEnclosingArea_finite [ConnectedSpace N]
    (g : SmoothMetric (N := N)) (hS : IsCompact (I3.boundary N)) : minEnclosingArea g < ⊤ := by
  let D := CKSGeometricCuts.identityOuterDomain hS
  exact (iInf_le (area g) D).trans_lt (area_finite g D)

end CKSFullCutArea

end

end OAI
