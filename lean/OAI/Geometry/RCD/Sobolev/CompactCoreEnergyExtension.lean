import OAI.Geometry.RCD.Metric.PositiveCoreAELimit
import OAI.Geometry.RCD.Sobolev.IntervalEnergyWeightLimit
import OAI.Geometry.RCD.Sobolev.BoundedWeightIntegralLimit

namespace OAI

/-! # Extending the energy inequality to all compact Lipschitz tests

The same Sobolev family is retained. Positivity and one uniform bound on
the test sequence allow dominated convergence in space and then time.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_core_energy_extension {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) [(hausdorff n X).Regular]
    (z : X) {r a b s t : ℝ} (hsub : Icc s t ⊆ Ioo a b)
    (u : Ioo a b → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : AEStronglyMeasurable u (volume.comap Subtype.val))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ q, ‖u q‖ ≤ C)
    (F G : X → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hcore : ∀ ψ : SobolevSpace (hausdorff n X) hX.quadratic,
      ψ ∈ compactLaplacianCore (hausdorff n X) hX.quadratic (ball z r) →
      ∀ B : ℝ≥0, (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ x| ≤ B) →
      (∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ x) →
      (∫ q in Icc s t, intervalExtension (fun τ => weightedGamma (hausdorff n X) hX.quadratic
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ) (u τ) (u τ)) q) ≤
      2*((∫ x in closedBall z r, SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ x*G x
        ∂hausdorff n X) - (∫ x in closedBall z r,
          SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ x*F x ∂hausdorff n X)))
    (φ : X → ℝ) {L B : ℝ≥0} (hφ : LipschitzWith L φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball z r) (hφ0 : ∀ x, 0 ≤ φ x) (hφB : ∀ x, |φ x| ≤ B) :
    (∫ q in Icc s t, intervalExtension (fun τ => weightedGamma (hausdorff n X) hX.quadratic
      φ (u τ) (u τ)) q) ≤
      2*((∫ x in closedBall z r, φ x*G x ∂hausdorff n X) -
        (∫ x in closedBall z r, φ x*F x ∂hausdorff n X)) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨v,hv,hvB,-,hvc⟩ := hX.positive_core_ae_limit hn isOpen_ball φ hφ hφc hφs hφ0 hφB
  let w : ℕ → X → ℝ := fun k => SobolevSpace.toLp μ Q (v k)
  have hw (k : ℕ) : AEStronglyMeasurable (w k) μ := Lp.aestronglyMeasurable _
  have hwb (k : ℕ) : ∀ᵐ x ∂μ, ‖w k x‖ ≤ B :=
    (hvB k).mono fun x hx => by simpa only [Real.norm_eq_abs] using hx.2
  have he := weighted_energy_interval_weight_tendsto μ Q w φ hw hwb hvc hsub u hu hC hb
  have hp (f : X → ℝ) (hf : Continuous f) :
      Tendsto (fun k => ∫ x in closedBall z r, w k x*f x ∂μ) atTop
        (𝓝 (∫ x in closedBall z r, φ x*f x ∂μ)) :=
    bounded_weight_integral_tendsto (μ.restrict (closedBall z r)) w φ
      (fun k => (hw k).restrict) (fun k => ae_restrict_of_ae (hwb k))
      (ae_restrict_of_ae hvc) f (hf.continuousOn.integrableOn_compact (isCompact_closedBall z r))
  apply le_of_tendsto_of_tendsto he (((hp G hG).sub (hp F hF)).const_mul 2)
  exact Eventually.of_forall fun k => hcore (v k) (hv k) B
    ((hvB k).mono fun _ hx => hx.2) ((hvB k).mono fun _ hx => hx.1)

end RegularPointCoordinates

end

end OAI
