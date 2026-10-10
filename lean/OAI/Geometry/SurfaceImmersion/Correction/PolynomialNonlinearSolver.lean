import OAI.Geometry.SurfaceImmersion.Correction.PolynomialNonlinearPhaseFrame
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverFromBounds

namespace OAI

/-! Actual finite metric-mode solvers in nonlinear phase charts, with all
coefficient and coordinate budgets specified polynomially. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

theorem polynomial_nonlinear_unperturbed_solver :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
      (_he : ContDiff ℝ ∞ e) (_hi : ContDiff ℝ ∞ e.symm),
      (∀ x, (e x).1 = coordinatePhase φ x) →
      (modeSupport K : Set SmallModes.Base) ⊆ e.source →
      (∀ x ∈ e.source, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ e.source, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (phaseDerivative (coordinatePhase φ) x)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m,
        (∀ j ≤ m+3, WeightedBound e.source 1 j (B m/(s : ℝ)^(j-2))
          (G ∘ planeCoordinateIsometry.symm)) ∧
        (∀ j, 1 ≤ j → j ≤ m+3 → ∀ x ∈ e.source,
          ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B m) ∧
        (∀ x ∈ e.source, ‖(coordDet (fderiv ℝ e x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ e.source, |coordDet (fderiv ℝ e x)| ≤ B m) ∧
        (∀ x ∈ e.source, ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ e.source, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ B m)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = e ∧ (∀ m, c.C m = A m*(B m)^(p m)) ∧
        (∀ m, c.D m = 0) ∧ (∀ m, c.J m = B m) := by
  classical
  choose p A hA hframe using fun m => polynomial_nonlinear_phase_frame_bound (m+1)
  refine ⟨p,A,hA,?_⟩
  intro G hG K φ hφ e he hi hphase hKe hImm hgood τ s hs hs1 B hB hb
  have hF : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  have hφ' : ContDiff ℝ ∞ (coordinatePhase φ) := hφ.comp planeCoordinateIsometry.symm.contDiff
  have hdom := realModeDomain_smooth_phase_chart hF hφ' e he hi hphase hImm hgood
  have hc (m : ℕ) : SmallModes.ReconstructionCoefficientBound
      (fun x => complexify (G (planeCoordinateIsometry.symm (e.symm x))))
      e.target s (m+1) (A m*(B m)^(p m)) := by
    obtain ⟨hFj,hej,hei,hed,hgram,hnormal⟩ := hb m
    have hh := (hframe m _ _ e hF hφ' he hi hphase s (B m) hs hs1 (hB m)
      (fun j hj => hFj j (by omega))
      (fun j hj hjm x hx => hej j hj (by omega) x hx)
      hei hed hImm hgood hgram hnormal).1
    exact hh
  have hC (m : ℕ) : 0 ≤ A m*(B m)^(p m) :=
    mul_nonneg (zero_le_one.trans (hA m)) (pow_nonneg (zero_le_one.trans (hB m)) _)
  let c := unperturbedSolverOfBounds hG K hφ e he hi hKe (fun x _ => hphase x)
    hdom τ s (fun m => A m*(B m)^(p m)) B hC hB hc
      (fun m j hj hjm x hx => (hb m).2.1 j hj (by omega) x hx)
  exact ⟨c,rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
