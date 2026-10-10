import OAI.Geometry.RCD.Sobolev.CorrectionInteriorEnergy

namespace OAI

/-! # The weak radial equation controls the interior fit energy -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Weak radial cancellation and its actual Dirichlet correction upgrade
an L2 fit to an interior gradient fit. The source is the same shifted
Hessian budget already used for the radial value estimates. -/
theorem radial_interior_energy_from_fit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hgradient : LocalHarmonicL2GradientInput hX)
    (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (f a : SobolevSpace (hausdorff n X) hX.quadratic)
        (G : LocalHessianPairing (hausdorff n X) hX.quadratic (ball p R) f a),
      ∀ {c P D : ℝ},
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p R) f c →
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) a →
      0 ≤ P → 0 ≤ D →
      (∀ φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p R),
        ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic φ.val‖ ^ 2 ≤
          P * energyForm (hausdorff n X) hX.quadratic φ.val φ.val) →
      ∀ b : ℝ,
      (∀ φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p R),
        (G.hessian φ - b * energyForm (hausdorff n X) hX.quadratic a φ.val) ^ 2 ≤
          D * energyForm (hausdorff n X) hX.quadratic φ.val φ.val) →
      ∀ (F : SobolevSpace (hausdorff n X) hX.quadratic) {I : ℝ},
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) F →
      ‖SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R) (G.mixed - F)‖ ^ 2 ≤ I →
      (∫ x in ball p (R / 2), localGamma (hausdorff n X) hX.quadratic
        (G.mixed - F) (G.mixed - F) x ∂hausdorff n X) ≤
        8 * D + 4 * (C / R) ^ 2 * (I + 4 * P * D) := by
  obtain ⟨C, hC, henergy⟩ := correction_interior_energy hX hgradient hn hκ
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv f a G c P D hf ha hP hD hpoin b hbound F I hF hI
  obtain ⟨h, _hmem, hh, he, hv⟩ := G.exists_harmonic_correction (hausdorff n X) hX.quadratic
    measurableSet_ball hf ha b hP hD hpoin hbound
  have hb := henergy p R hR hcurv G.mixed h F hh hF he hI hv
  exact hb.trans_eq (by ring)

end RegularPointCoordinates

end

end OAI
