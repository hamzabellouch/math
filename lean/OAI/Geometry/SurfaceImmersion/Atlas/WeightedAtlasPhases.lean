import OAI.Geometry.SurfaceImmersion.Atlas.GlobalPhaseGerms
import OAI.Geometry.SurfaceImmersion.Correction.ManifoldSmoothingLinearity

namespace OAI

/-! Frequency scaling of the actual smooth global atlas phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4

lemma phaseLinear_smul (c : ℝ) (ξ : SmallModes.Base) :
    phaseLinear (c • ξ) = c • phaseLinear ξ := by
  apply ContinuousLinearMap.ext
  intro x
  change phaseLinear (c • ξ) x = c * phaseLinear ξ x
  simp only [phaseLinear_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

namespace FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma linearAtlasPhase_smooth (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.linearAtlasPhase Q w a) :=
  restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
    ((phaseLinear (w a.1 a.2 • (Q a.1).ξ a.2)).contDiff.comp planeCoordinateIsometry.contDiff)

lemma linearAtlasPhase_smul_unit (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) :
    A.linearAtlasPhase Q w a = w a.1 a.2 • A.linearAtlasPhase Q (fun _ _ => 1) a := by
  unfold linearAtlasPhase
  simp only [one_smul]
  have he : phaseLinear (w a.1 a.2 • (Q a.1).ξ a.2) ∘ planeCoordinateIsometry =
      w a.1 a.2 • (phaseLinear ((Q a.1).ξ a.2) ∘ planeCoordinateIsometry) := by
    funext x
    rw [phaseLinear_smul]
    rfl
  rw [he,restore_smul]

lemma vectorPlaneRead_real_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : A.centers) (c : ℝ) (F : M → V) :
    A.vectorPlaneRead k (c • F) = c • A.vectorPlaneRead k F := by
  funext x
  change localize (k : M) (A.outer k) (c • F) (planeCoordinateIsometry.symm x) = _
  rw [localize_smul]
  rfl

variable [CompactSpace M]

/-- Frequency weights scale the read phase derivative everywhere, not
just on the compact supports used to establish good geometry. -/
lemma linearAtlasPhase_read_derivative_smul_unit (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) (k : A.centers)
    (x : SmallModes.Base) :
    phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) x =
      w a.1 a.2 •
        phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q (fun _ _ => 1) a)) x := by
  rw [A.linearAtlasPhase_smul_unit Q w a,A.vectorPlaneRead_real_smul]
  exact phaseDerivative_const_smul
    ((A.vectorPlaneRead_smooth k (A.linearAtlasPhase_smooth Q (fun _ _ => 1) a)).differentiable
      (by simp) x) _

end SmoothingAtlas
end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
