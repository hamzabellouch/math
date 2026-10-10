import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverFromBounds
import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseDerivativeBounds

namespace OAI

/-! A linear-phase metric solver whose actual coefficient budgets are
polynomial in the supplied jet and denominator bounds. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

theorem polynomial_linear_unperturbed_solver :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {U : Set SmallModes.Base} (hU : IsOpen U)
      {ξ : SmallModes.Base} (hξ : ξ ≠ 0)
      {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (_hphase : coordinatePhase φ = phaseLinear ξ),
      (modeSupport K : Set SmallModes.Base) ⊆ U →
      (∀ x ∈ U, Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ U, Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x) ξ) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
        (∀ j ≤ m+3, WeightedBound U 1 j (B m/(s : ℝ)^(j-2))
          (G ∘ planeCoordinateIsometry.symm)) ∧
        (∀ x ∈ U, ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ U, ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        c.e = linearPhaseChart ξ hξ U hU ∧
        (∀ m, c.C m = A m*(B m)^(p m)) ∧
        (∀ m, c.D m = 0) ∧ (∀ m, c.J m = 1+2*B m) := by
  classical
  choose p A hA hframe using fun m => polynomial_phase_frame_bound (m+1)
  refine ⟨p,A,hA,?_⟩
  intro G hG K U hU ξ hξ φ hφ hphase hKU hImm hgood τ s hs hs1 B hB hb
  let e := linearPhaseChart ξ hξ U hU
  have hsmooth := linearPhaseChart_smooth ξ hξ U hU
  have hF : ContDiff ℝ ∞ (G ∘ planeCoordinateIsometry.symm) :=
    hG.comp planeCoordinateIsometry.symm.contDiff
  have hdom := linearPhaseChart_modeDomain hF hU hξ hImm hgood
  have hset : (phaseEquiv ξ hξ) '' U = (phaseEquiv ξ hξ).symm ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hy
    · intro hx
      exact ⟨(phaseEquiv ξ hξ).symm x,hx,(phaseEquiv ξ hξ).apply_symm_apply x⟩
  have hc (m : ℕ) : SmallModes.ReconstructionCoefficientBound
      (fun x => complexify (G (planeCoordinateIsometry.symm (e.symm x))))
      e.target s (m+1) (A m*(B m)^(p m)) := by
    obtain ⟨hξB,hiB,hpref,hgram,hnormal⟩ := hb m
    have hpref' : ∀ j ≤ (m+1)+2, WeightedBound U 1 j (B m/(s : ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm) := by
      intro j hj
      exact hpref j (by omega)
    have hh := (hframe m hF hU hξ hs hs1 (hB m) hξB hiB hpref' hImm hgood hgram hnormal).1
    simpa only [e, linearPhaseChart_target, linearPhaseChart_symm_apply, hset, Function.comp_def] using hh
  have hC (m : ℕ) : 0 ≤ A m*(B m)^(p m) :=
    mul_nonneg (zero_le_one.trans (hA m)) (pow_nonneg (zero_le_one.trans (hB m)) _)
  have hJ (m : ℕ) : 1 ≤ 1+2*B m := by linarith [hB m]
  have hj (m j : ℕ) (hj : 1 ≤ j) (_hjm : j ≤ m) (x : SmallModes.Base)
      (hx : x ∈ e.source) : ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ 1+2*B m := by
    exact (linearPhaseChart_derivative_bound hξ hU hj hx).trans (by linarith [(hb m).1])
  let c := unperturbedSolverOfBounds hG K hφ e hsmooth.1 hsmooth.2 hKU
    (fun x _ => by rw [hphase]; rfl) hdom τ s (fun m => A m*(B m)^(p m))
      (fun m => 1+2*B m) hC hJ hc hj
  exact ⟨c,rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
