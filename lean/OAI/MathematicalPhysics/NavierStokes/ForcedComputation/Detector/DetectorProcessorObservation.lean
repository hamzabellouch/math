import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorObservation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorProcessorGeometry

namespace OAI

/-! The scalar threshold for the compiled planar processor is exactly
halting, using integer-phase entry and all-phase nonhalting clearance. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

attribute [local irreducible] Recorder.Planar.normalizedHamiltonian planarSlice
  euclideanFlowBound detectorDrift detectorSource detectorReference

theorem detector_processor_observation (hK : TorusHeatInput)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ω Ψ : ℝ → ℝ → Plane → Plane}
    (hP : Recorder.Planar.ProcessorProperties I hI Ω Ψ)
    (hv : PlanarVariations (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ω y.1 (-y.1) y.2))
    {w : ℝ → Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1
      (detectorDrift (planarSlice (Recorder.Planar.normalizedHamiltonian I hI))
        detectorBumpDerivativeBound (euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI)))
      (detectorSource detectorBumpDerivativeBound
        (euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI))) w (fun _ => 0))
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) :
    (∃ t, 0 ≤ t ∧ ∃ x ∈ Recorder.Planar.observer, 1 / 2 < w t x) ↔ Alternating.Halts I := by
  let V := planarSlice (Recorder.Planar.normalizedHamiltonian I hI)
  let L := euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI)
  have hL : 0 < L := Nat.lt_of_lt_of_le (by norm_num) hP.euclidean_bounds.1.1
  have h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ) :=
    fun s x => (hP.euclidean_bounds.1.2.1 s x).1
  have h₂ : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ) :=
    fun s x => (hP.euclidean_bounds.1.2.1 s x).2
  have hVs (s : ℝ) : ContDiff ℝ ∞ (V s) :=
    hP.torus_smooth.comp (show ContDiff ℝ ∞ (fun x : Plane => (s, x)) from
      contDiff_const.prodMk contDiff_id)
  have hlap (n : ℕ) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ)
      (2 * (duration detectorBumpDerivativeBound L n : ℝ))) (x : Plane) :
      |scalarLaplacian (detectorReference Ω detectorBumpDerivativeBound L n
        (2 * ((n : ℝ) + 1) + t)) x| ≤ (laplacianBound detectorBumpDerivativeBound L n : ℝ) :=
    detectorReference_laplacian_bound hv
      hVs hback L hL h₁ h₂ n _ x
  constructor
  · rintro ⟨t, ht, x, hx, hobs⟩
    by_contra hno
    have hlow := detector_negative_all_time hK hP.torus_transition hv hP.torus_smooth
      hP.torus_spatial_periodic hP.torus_solenoidal hback detectorBumpDerivativeBound L h₁
      hs hw hlap (fun s hs' y hy => processor_nonhalting_clearance I hI hP hno s hs' y hy)
      ht hx
    exact (not_lt_of_ge hobs.le) hlow
  · intro hhalt
    obtain ⟨n, hlo, hhi, _, _⟩ := hP.halt_clearance hhalt
    have hx : Ω 0 n ![1 / 4, 1 / 4] ∈ Recorder.Planar.observer := by
      change (1 / 32 : ℝ) < _ ∧ _ < (1 / 8 : ℝ)
      constructor <;> linarith
    obtain ⟨t, ht, hh⟩ := detectorBurst_detects hP.torus_transition hP.torus_spatial_periodic
      hback detectorBumpDerivativeBound L n hs hw (hlap n) (detector_old_mass_margin L).le
      (detector_scalar_at_start_bound hK hP.torus_smooth hP.torus_spatial_periodic
        hP.torus_solenoidal detectorBumpDerivativeBound L hs hw n)
      (Nat.cast_nonneg n) (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    exact ⟨t, ht, _, hx, hh⟩

end ForcedComputation.VelocityDetector

end

end OAI
