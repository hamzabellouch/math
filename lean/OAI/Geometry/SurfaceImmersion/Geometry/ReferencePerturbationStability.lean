import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceMetricStability
import OAI.Geometry.SurfaceImmersion.Geometry.ActualOperatorTolerance
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseTolerance

namespace OAI

/-! Genuine independent circular phase and cutoff choices preserve the
fixed reference inverse margins for all sufficiently close starting maps. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
local instance perturbationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance perturbationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance perturbationDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance perturbationDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance perturbationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance perturbationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

def perturbedPhases (ell : d.B.centers → Fin 3 → Base) :=
  d.B.curvedAtlasPhase (d.B.centeredPhaseFamily ell d.L)

 theorem circular_operator_metric_stability {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ phaseTol weightTol mapTol : ℝ, 0 < phaseTol ∧ 0 < weightTol ∧ 0 < mapTol ∧
      ∀ (ell : d.B.centers → Fin 3 → Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < phaseTol) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < weightTol) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mapTol (G-F) →
      (∀ p, (d.B.primitiveFullOperator d.basis psi (d.perturbedPhases ell) p).IsInvertible) ∧
      ∀ (a : d.B.centers × Fin 3) p, p ∈ tsupport (d.B.weight a.1) →
        0 < d.B.primitiveCoefficientField d.basis a p
          ((d.B.primitiveFullOperator d.basis psi (d.perturbedPhases ell) p).inverse
            ((g.inner-inducedTensor (r • G)) p)) := by
  obtain ⟨eta,heta,hstable⟩ := d.operator_stability
  obtain ⟨delta,hdelta,hoperator⟩ := d.B.primitive_operator_tolerance d.basis
    (fun a _p hp => d.basis_smooth a.1 hp a.2) d.globalPhases
    (fun a => d.B.curvedAtlasPhase_smooth d.localPhases
      (fun _ _ => centeredConvexPhase_smooth _ _ _) a) heta
  obtain ⟨D,hD,hphase⟩ := d.B.circularPhase_frame_bound
  obtain ⟨mapTol,hmapTol,hmetric⟩ := d.metric_frame_tolerance hF r href heta
  have hDpos : 0 < D+1 := by linarith
  refine ⟨delta/(D+1),delta,mapTol,div_pos hdelta hDpos,hdelta,hmapTol,?_⟩
  intro ell psi hell hs hw G hG hGF
  apply hstable _ _
  · intro i p hp
    have hdiff : ∀ (j : d.B.centers) (a : d.B.centers × Fin 3) p, p ∈ tsupport (d.B.weight j) →
        p ∈ tsupport (d.B.weight a.1) →
        ‖d.B.covectorFrame j p (d.B.primitivePhaseCovector (d.perturbedPhases ell) a p)-
          d.B.covectorFrame j p (d.B.primitivePhaseCovector d.globalPhases a p)‖ < delta := by
      intro j a p hp _ha
      change ‖d.B.covectorFrame j p
          (mfderiv planeModel 𝓘(ℝ) (d.B.circularPhase a.1 (ell a.1 a.2) (d.L a.1)) p)-
        d.B.covectorFrame j p
          (mfderiv planeModel 𝓘(ℝ) (d.B.circularPhase a.1 ((d.P a.1).ξ a.2) (d.L a.1)) p)‖ < delta
      have hbound := hphase a.1 j p hp (ell a.1 a.2) ((d.P a.1).ξ a.2) (d.L a.1)
      have ht := (lt_div_iff₀ hDpos).mp (hell a.1 a.2)
      have hn := norm_nonneg (ell a.1 a.2-(d.P a.1).ξ a.2)
      exact hbound.trans_lt (by nlinarith)
    have hh := hoperator psi (d.perturbedPhases ell) hs hw hdiff i p hp
    have hid : d.B.tensorOperatorFrame i p
        (d.B.primitiveFullOperator d.basis (fun a => d.B.weight a.1) d.globalPhases p) =
        ContinuousLinearMap.id ℝ TensorFiber := by
      rw [d.operator_identity]
      apply ContinuousLinearMap.ext
      intro H
      change (d.B.tensorTriv i).continuousLinearMapAt ℝ p
        ((d.B.tensorTriv i).symmL ℝ p H) = H
      exact (d.B.tensorTriv i).continuousLinearMapAt_symmL
        (d.B.tensorTriv_domain i (d.B.weight_support i hp)) H
    rw [hid] at hh
    exact hh
  · exact hmetric G hG hGF

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
