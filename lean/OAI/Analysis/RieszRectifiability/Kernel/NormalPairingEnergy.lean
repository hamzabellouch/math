import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.RenormalizedFarPairing
import OAI.Analysis.RieszRectifiability.Kernel.BallLocalization
import OAI.Analysis.RieszRectifiability.Kernel.CutoffTestMoments
import OAI.Analysis.RieszRectifiability.Kernel.LocalLipschitzEnergy

namespace OAI

/-!
# Normal cutoff pairings and local energy

The normal pairing splits into a symmetric interaction inside a ball and a
renormalized exterior term. Bounds on the pairing, cutoff moments, and exterior
interaction control the local fractional energy together with its cutoff error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def normalCutoffPairing {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R : ℝ) (w χ : Ambient d → ℝ) : ℝ :=
  let ν := μ.restrict (ball a R)
  (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
    fractionalBilinear m w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂ν.prod ν) +
    ∫ q, renormalizedNormalIntegrand m w (fun x => χ x ^ 2 * w x) a q
      ∂ν.prod (μ.restrict (closedExterior a R))

def normalExteriorEstimate (m : ℕ) (C M H R δ Z : ℝ) : ℝ :=
  2 ^ (m + 1) * ((M * δ ^ 2) * (2 * (C * 2 ^ m / R))) +
    ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * ((M * δ) * Z)

def localCutoffErrorCoefficient (p : ℕ) (C : ℝ) (L : ℝ≥0) (R : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * (2 * R)))

theorem normalCutoffPairing_energy_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (K L : ℝ≥0) (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (H R : ℝ)
    (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hmass : C * R ^ (p + 1) ≤ M)
    (hsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) μ)
    (Z : ℝ) (hZ : (∫ y in closedExterior a R, |w y| * inverseDistancePow (p + 1 + 2) a y ∂μ) ≤ Z)
    (A : ℝ) (hsmall : |normalCutoffPairing (p + 1) μ a R w χ| ≤ A) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
        2 * (A + normalExteriorEstimate (p + 1) C M H R δ Z) +
          localCutoffErrorCoefficient p C L R * (M * δ ^ 2) := by
  let ν := μ.restrict (ball a R)
  let φ := fun x => χ x ^ 2 * w x
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hC := hg.1
  have hL2 := lipschitz_height_memLp_on_ball (p + 1) C μ hg w K hw a R hR
  have hmassν : ν.real univ ≤ M :=
    (ball_restriction_mass_bound (p + 1) C μ hg a R hR).trans hmass
  obtain ⟨hφ, hφw, hφ₁, hφ₂⟩ := squared_cutoff_test_moment_bounds ν w χ
    hw.continuous.measurable hχ.continuous.measurable hL2 hχbound M δ hM hδ hmassν hsecond
  have hφm : Measurable φ := (hχ.continuous.measurable.pow_const 2).mul hw.continuous.measurable
  have hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H := by
    apply Filter.Eventually.of_forall
    intro x hx
    apply hχsupport x
    intro hz
    exact hx (by simp only [φ, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul])
  obtain ⟨hExt, hExtBound⟩ := renormalized_far_pairing_integrable_and_bound (p + 1) C μ ν hg
    w φ hw.continuous.measurable hφm hφ hφw a H R hH hR hHR hnear hweighted Z hZ
  have hZ0 : 0 ≤ Z := (integral_nonneg fun y =>
    mul_nonneg (abs_nonneg (w y)) (inverseDistancePow_nonneg _ _ _)).trans hZ
  have hExtBound' : (∫ q, |renormalizedNormalIntegrand (p + 1) w φ a q|
      ∂ν.prod (μ.restrict (closedExterior a R))) ≤ normalExteriorEstimate (p + 1) C M H R δ Z := by
    apply hExtBound.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ₂ (by positivity)) (by positivity))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ₁ hZ0) (by positivity))
  have hExtAbs : |∫ q, renormalizedNormalIntegrand (p + 1) w φ a q
      ∂ν.prod (μ.restrict (closedExterior a R))| ≤ normalExteriorEstimate (p + 1) C M H R δ Z := by
    apply LE.le.trans _ hExtBound'
    simpa only [Real.norm_eq_abs] using! norm_integral_le_integral_norm
      (renormalizedNormalIntegrand (p + 1) w φ a)
  have hInner : (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) w φ q.1 q.2 ∂ν.prod ν) ≤
      2 * (A + normalExteriorEstimate (p + 1) C M H R δ Z) := by
    have hp := (le_abs_self (normalCutoffPairing (p + 1) μ a R w χ)).trans hsmall
    have hlow := (abs_le.mp hExtAbs).1
    change (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) w φ q.1 q.2 ∂ν.prod ν) +
      (∫ q, renormalizedNormalIntegrand (p + 1) w φ a q ∂ν.prod (μ.restrict (closedExterior a R))) ≤ A at hp
    linarith
  let W : ℝ≥0 := ⟨|w a| + (K : ℝ) * R, by positivity⟩
  have hLocal := localized_cutoff_energy_bound p C ν
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) (ball a R)
    (ae_restrict_mem measurableSet_ball) w χ hw.continuous.measurable hL2 K L W 1
    hw.lipschitzOnWith hχ (fun x hx => lipschitz_height_bound_on_ball w K hw a x R hx)
    (fun x _ => hχbound x) (2 * R) (by positivity) (ball_restriction_pair_diameter μ a R)
    (2 * (A + normalExteriorEstimate (p + 1) C M H R δ Z)) hInner
  refine ⟨hLocal.1, hLocal.2.trans ?_⟩
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond (by positivity))

end

end RieszRectifiability

end OAI
