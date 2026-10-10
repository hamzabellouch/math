import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.SupportedFractionalCutoff
import OAI.Analysis.RieszRectifiability.Kernel.ComplexExteriorIntegrability
import OAI.Analysis.RieszRectifiability.Nets.RenormalizedCrossCancellation

namespace OAI

/-!
# Truncated height pairing and its renormalized exterior term

For a compactly supported mean-zero Schwartz test, the weighted truncated
fractional pairing splits into a symmetric local pairing and a renormalized
exterior integral. Support separation removes the cutoff in cross terms, and
the weighted exterior hypothesis supplies the integrability needed for cancellation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter SchwartzMap

theorem compact_schwartz_truncated_height_pairing (p : ℕ)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (ε : ℝ) (hε : 0 < ε) (hsep : ε + H ≤ R)
    (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : IntegrableOn w (ball a R) volume)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hzero : (∫ x, g x) = 0)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H)
    (B : ℝ) (hB : 0 ≤ B) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) volume) :
    Integrable (fun x => w x • fractionalSchwartzTruncatedTest p ε g x) volume ∧
      (∫ x, w x • fractionalSchwartzTruncatedTest p ε g x) =
        (1 / 2 : ℝ) • (∫ q : Ambient (p + 1) × Ambient (p + 1),
          (w q.1 - w q.2) • (symmetricFractionalCutoffKernel (p + 1) ε q • (g q.1 - g q.2))
          ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R))) +
        ∫ q, complexRenormalizedNormalIntegrand (p + 1) w g a q
          ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R)ᶜ) := by
  let μ : Measure (Ambient (p + 1)) := volume
  let ν := μ.restrict (ball a R)
  let η := μ.restrict (ball a R)ᶜ
  let C := (volume (ball (0 : Ambient (p + 1)) 1)).toReal
  let k := symmetricFractionalCutoffKernel (d := p + 1) (p + 1) ε
  have hgrowth : GlobalUpperGrowth (p + 1) C μ := volume_global_upper_growth (p + 1)
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hgrowth a R hR
  have hgs := test_zero_outside_localization g a H R (by linarith) hnear
  have hgm : Measurable g := g.continuous.measurable
  have hgn : Integrable (fun x => ‖g x‖) ν := g.integrable.restrict.norm
  have hgnw : Integrable (fun x => ‖g x‖ * w x) ν :=
    hw.bdd_mul hgm.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [norm_norm] using! hgB x)
  have hzν : (∫ x, g x ∂ν) = 0 := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hgs).trans hzero
  have hD : Integrable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      w q.1 • (inverseDistancePow (p + 1 + 1) q.1 q.2 • g q.1)) (ν.prod η) := by
    simpa only [closedExterior_eq_compl_ball] using! direct_height_exterior_integrable
      (p + 1) C μ ν hgrowth w g hwm hgm hgnw a H R hR hHR (Eventually.of_forall hnear)
  have hN : Integrable (complexRenormalizedNormalIntegrand (p + 1) w g a) (ν.prod η) := by
    simpa only [closedExterior_eq_compl_ball] using! complex_renormalized_exterior_integrable
      (p + 1) C μ ν hgrowth w g hwm hgm hgn hgnw a H R hH hR hHR
      (Eventually.of_forall hnear) hweighted
  have hraw : ∀ᵐ y ∂η, Integrable (fun x => inverseDistancePow (p + 1 + 1) x y • g x) ν := by
    filter_upwards [ae_restrict_mem (μ := μ)
      (show MeasurableSet (ball a R)ᶜ from measurableSet_ball.compl)] with y hy
    have hy' : R ≤ dist a y := by
      rwa [← closedExterior_eq_compl_ball] at hy
    exact far_kernel_test_integrable_of_support ν g hgm g.integrable.restrict
      (p + 1) a y H R hR hHR (Eventually.of_forall hnear) hy'
  have hcross := renormalized_complex_cross_integral_identity (p + 1) ν η w g a
    g.integrable.restrict hzν hraw hD hN
  have hcut (x y : Ambient (p + 1)) (hy : y ∈ (ball a R)ᶜ) :
      k (x, y) • g x = inverseDistancePow (p + 1 + 1) x y • g x :=
    supported_fractional_cutoff_cross (p + 1) ε H R a x y g (hnear x)
      (by rwa [closedExterior_eq_compl_ball]) hsep
  have hcutswap (x y : Ambient (p + 1)) (hy : y ∈ (ball a R)ᶜ) :
      k (y, x) • g x = inverseDistancePow (p + 1 + 1) x y • g x :=
    supported_fractional_cutoff_cross_swap (p + 1) ε H R a x y g (hnear x)
      (by rwa [closedExterior_eq_compl_ball]) hsep
  have hDcut : Integrable (fun q : Ambient (p + 1) × Ambient (p + 1) =>
      w q.1 • (k q • g q.1)) (ν.prod η) := by
    apply hD.congr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (μ := μ) (show MeasurableSet (ball a R)ᶜ from measurableSet_ball.compl))] with q hq
    exact congrArg (fun z : ℂ => w q.1 • z) (hcut q.1 q.2 hq).symm
  have hOeq : (fun y => w y • (∫ x, k (y, x) • g x ∂ν)) =ᵐ[η]
      fun y => w y • (∫ x, inverseDistancePow (p + 1 + 1) x y • g x ∂ν) := by
    filter_upwards [ae_restrict_mem (μ := μ)
      (show MeasurableSet (ball a R)ᶜ from measurableSet_ball.compl)] with y hy
    apply congrArg (fun z : ℂ => w y • z)
    exact integral_congr_ae (Eventually.of_forall fun x => hcutswap x y hy)
  have hO := hcross.1.congr hOeq.symm
  have hL := bounded_kernel_height_integrable ν w hwm hw g hgm B hB hgB k
    (symmetricFractionalCutoffKernel_measurable (p + 1) ε) ((ε ^ (p + 1 + 1))⁻¹)
    (symmetricFractionalCutoffKernel_bound (p + 1) ε hε)
  have hdec := supported_height_kernel_integral_decomposition μ (ball a R) measurableSet_ball
    w g hgs k (fractional_cutoff_increment_integrable p ε hε g) hL hDcut hO
  have hpair := (finite_symmetric_height_kernel_pairing ν w hwm hw g hgm B hB hgB k
    (symmetricFractionalCutoffKernel_measurable (p + 1) ε) ((ε ^ (p + 1 + 1))⁻¹)
    (symmetricFractionalCutoffKernel_bound (p + 1) ε hε)
    (symmetricFractionalCutoffKernel_swap (p + 1) ε)).2
  have hDeq : (∫ x, w x • (∫ y, k (x, y) • g x ∂η) ∂ν) =
      ∫ x, w x • (∫ y, inverseDistancePow (p + 1 + 1) x y • g x ∂η) ∂ν := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    apply congrArg (fun z : ℂ => w x • z)
    apply setIntegral_congr_fun measurableSet_ball.compl
    intro y hy
    exact hcut x y hy
  have hAe : (fun x => w x • (∫ y, k (x, y) • (g x - g y) ∂μ)) =
      fun x => w x • fractionalSchwartzTruncatedTest p ε g x := by
    funext x
    exact congrArg (fun z : ℂ => w x • z) (fractional_cutoff_increment_integral p ε hε g x)
  rw [hAe] at hdec
  refine ⟨hdec.1, ?_⟩
  change (∫ x, w x • fractionalSchwartzTruncatedTest p ε g x ∂μ) =
    (1 / 2 : ℝ) • (∫ q, (w q.1 - w q.2) • (k q • (g q.1 - g q.2)) ∂ν.prod ν) +
      ∫ q, complexRenormalizedNormalIntegrand (p + 1) w g a q ∂ν.prod η
  rw [hdec.2, ← hpair, hDeq, integral_congr_ae hOeq, hcross.2]
  abel

end

end RieszRectifiability

end OAI
