import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.FinitePairingCancellation

namespace OAI

/-!
# Regional height pairings

The height pairing on a set combines the symmetric interior fractional bilinear
integral with a renormalized cross-region term. For affine normal heights and
mean-zero tests on a ball, cancellation of the far contribution identifies this
regional expression with the scalar Riesz pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

def heightRawCrossIntegrand {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  φ q.1 * (w q.1 - w q.2) * inverseDistancePow (m + 1) q.1 q.2

def heightPairingOn {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w φ : Ambient d → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
    ∂(μ.restrict s).prod (μ.restrict s)) +
  ∫ q, renormalizedNormalIntegrand m w φ a q ∂(μ.restrict s).prod (μ.restrict sᶜ)

theorem fractionalBilinear_swap {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) :
    fractionalBilinear m w φ q.swap.1 q.swap.2 = fractionalBilinear m w φ q.1 q.2 := by
  unfold fractionalBilinear
  dsimp only [Prod.swap]
  rw [dist_comm q.2 q.1]
  ring

theorem height_pairing_split {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (ν : Measure (Ambient d)) [SFinite ν] (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hφzero : ∀ x ∉ s, φ x = 0)
    (hF : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2) (ν.prod ν)) :
    Integrable (heightRawCrossIntegrand m w φ) ((ν.restrict s).prod (ν.restrict sᶜ)) ∧
      (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2 ∂ν.prod ν) =
        (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
          ∂(ν.restrict s).prod (ν.restrict s)) +
          ∫ q, heightRawCrossIntegrand m w φ q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
  have hcross : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have heq : (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      =ᵐ[(ν.restrict s).prod (ν.restrict sᶜ)] heightRawCrossIntegrand m w φ := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hy
    unfold fractionalBilinear heightRawCrossIntegrand inverseDistancePow
    rw [hφzero q.2 hy, sub_zero]
    ring
  have hsplit := integral_symmetric_pair_split ν s hs
    (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2) hF
    (fractionalBilinear_swap m w φ) (by
      intro x hx y hy
      simp only [fractionalBilinear, hφzero x hx, hφzero y hy, sub_self, mul_zero, zero_div])
  rw [integral_congr_ae heq] at hsplit
  refine ⟨(integrable_congr heq).mp hcross, ?_⟩
  linarith

theorem height_far_integral_eq_raw_of_mean_zero {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0) (a : Ambient d)
    (hk : Integrable (fun y => w y * inverseDistancePow (m + 1) a y) η)
    (hraw : Integrable (heightRawCrossIntegrand m w φ) (ν.prod η)) :
    Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod η) ∧
      (∫ q, renormalizedNormalIntegrand m w φ a q ∂ν.prod η) =
        ∫ q, heightRawCrossIntegrand m w φ q ∂ν.prod η := by
  have hcorrection := hφ.mul_prod hk
  have heq : renormalizedNormalIntegrand m w φ a = fun q => heightRawCrossIntegrand m w φ q +
      φ q.1 * (w q.2 * inverseDistancePow (m + 1) a q.2) := by
    funext q
    unfold renormalizedNormalIntegrand heightRawCrossIntegrand
    ring
  rw [heq]
  refine ⟨hraw.add hcorrection, ?_⟩
  rw [integral_add hraw hcorrection, integral_prod_mul φ
    (fun y => w y * inverseDistancePow (m + 1) a y), hzero, zero_mul, add_zero]

theorem finite_height_pairing_eq_renormalized {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (ν : Measure (Ambient d)) [SFinite ν] (a : Ambient d) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hφ : Integrable φ ν) (hφzero : ∀ x ∉ s, φ x = 0)
    (hzero : (∫ x in s, φ x ∂ν) = 0)
    (hk : IntegrableOn (fun y => w y * inverseDistancePow (m + 1) a y) sᶜ ν)
    (hF : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2) (ν.prod ν)) :
    Integrable (renormalizedNormalIntegrand m w φ a) ((ν.restrict s).prod (ν.restrict sᶜ)) ∧
      (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2 ∂ν.prod ν) =
        heightPairingOn m ν a s w φ := by
  obtain ⟨hraw, hsplit⟩ := height_pairing_split m w φ ν s hs hφzero hF
  obtain ⟨hfar, heq⟩ := height_far_integral_eq_raw_of_mean_zero m w φ (ν.restrict s) (ν.restrict sᶜ)
    hφ.restrict hzero a hk hraw
  refine ⟨hfar, hsplit.trans ?_⟩
  unfold heightPairingOn
  rw [heq]

theorem heightPairingOn_height_div {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s : Set (Ambient d)) (w φ : Ambient d → ℝ) (δ : ℝ) :
    heightPairingOn m μ a s (fun x => w x / δ) φ = heightPairingOn m μ a s w φ / δ := by
  have hF : (fun q : Ambient d × Ambient d => fractionalBilinear m (fun x => w x / δ) φ q.1 q.2) =
      fun q => fractionalBilinear m w φ q.1 q.2 / δ := by
    funext q
    unfold fractionalBilinear
    ring
  have hN : renormalizedNormalIntegrand m (fun x => w x / δ) φ a =
      fun q => renormalizedNormalIntegrand m w φ a q / δ := by
    funext q
    unfold renormalizedNormalIntegrand
    ring
  unfold heightPairingOn
  rw [hF, hN, integral_div, integral_div]
  ring

theorem heightPairingOn_ball_eq_rieszScalarPairing {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (w φ : Ambient d → ℝ)
    (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hφ : Integrable φ (μ.restrict (ball a R))) (hzero : (∫ x in ball a R, φ x ∂μ) = 0)
    (hN : Integrable (renormalizedNormalIntegrand m w φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    heightPairingOn m μ a (ball a R) w φ = rieszScalarPairing m μ a R e φ := by
  let := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hext := (riesz_far_integral_eq_normal m C μ (μ.restrict (ball a R)) hg e w φ hw
    a R hR hφ hzero hN).2
  unfold heightPairingOn rieszScalarPairing
  simp_rw [rieszInteriorIntegrand_eq_fractionalBilinear m e w φ hw]
  rw [← closedExterior_eq_compl_ball a R, hext]

end

end RieszRectifiability

end OAI
