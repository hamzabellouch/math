import OAI.Geometry.Immersion.ClosedSurface.MetricPatches
import OAI.Geometry.Immersion.ClosedSurface.JacobianBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def coordinateChart (p : M) : OpenPartialHomeomorph M SmallModes.Base :=
  (chartAt Plane p).trans planeCoordinates.toHomeomorph.toOpenPartialHomeomorph

lemma coordinateChart_source (p : M) :
    (coordinateChart p).source = (chartAt Plane p).source := by
  simp [coordinateChart]

lemma coordinateChart_apply (p q : M) : coordinateChart p q = chartCoordinates p q := rfl

lemma coordinateChart_symm_apply (p : M) (x : SmallModes.Base) :
    (coordinateChart p).symm x = coordinateInverse p x := by
  simp [coordinateChart,coordinateInverse,planeModel]

lemma coordinateChart_target (p : M) :
    (coordinateChart p).target = coordinateDomain p := by
  simp [coordinateChart,coordinateDomain,planeModel]

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

lemma coordinateChart_symm_smoothOn (p : M) :
    ContMDiffOn 𝓘(ℝ,SmallModes.Base) planeModel ∞ (coordinateChart p).symm (coordinateChart p).target := by
  have he : ((coordinateChart p).symm : SmallModes.Base → M) = coordinateInverse p := by
    funext x; exact coordinateChart_symm_apply p x
  rw [he,coordinateChart_target]
  exact coordinateInverse_smoothOn p



def coordinateTransition (q p : M) : OpenPartialHomeomorph SmallModes.Base SmallModes.Base :=
  (coordinateChart p).symm.trans (coordinateChart q)

lemma coordinateTransition_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p) (coordinateTransition q p).source := by
  apply ContMDiffOn.contDiffOn
  exact (coordinateChart_smoothOn q).comp
    ((coordinateChart_symm_smoothOn p).mono (fun x hx => hx.1)) (fun x hx => hx.2)

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_symm (q p : M) :
    (coordinateTransition q p).symm = coordinateTransition p q := by
  simp [coordinateTransition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

lemma coordinateTransition_symm_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p).symm (coordinateTransition q p).target := by
  have h := coordinateTransition_smoothOn p q
  rw [← coordinateTransition_symm q p] at h
  exact h



theorem coordinateTransition_compact_bounds (q p : M) {K : Set SmallModes.Base}
    (hK : IsCompact K) (hKs : K ⊆ (coordinateTransition q p).source) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ x ∈ K, d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)| ∧
        ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ C := by
  let e := coordinateTransition q p
  exact compact_chart_jacobian_bounds e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun x hx => e.left_inv hx) hK hKs

end ClosedSurfaceR4

end

end OAI
