import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.RieszPairingIdentification
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedEnergy

namespace OAI

/-!
The normal cutoff pairing is identified with a Riesz scalar pairing for a centered
Lipschitz height test, using local `L²` integrability and cutoff support control.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem normalCutoffPairing_eq_riesz_of_lipschitz {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (w χ : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (hcoord : ∀ x y, w x - w y = inner ℝ e (x - y))
    (hχm : Measurable χ) (hχbound : ∀ x, |χ x| ≤ 1)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0) :
    normalCutoffPairing m μ a R w χ =
      rieszScalarPairing m μ a R e (fun x => χ x ^ 2 * w x) := by
  let ν := μ.restrict (ball a R)
  let φ := fun x => χ x ^ 2 * w x
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w K hw a R hR
  have hφL2 := squared_cutoff_test_memLp ν w χ hw.continuous.measurable hχm hwL2 hχbound
  have hφ : Integrable φ ν := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν :=
    memLp_one_iff_integrable.mp (hφL2.mul hwL2)
  have hφm : Measurable φ := (hχm.pow_const 2).mul hw.continuous.measurable
  have hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H := by
    apply Filter.Eventually.of_forall
    intro x hx
    apply hχsupport x
    intro hz
    exact hx (by simp only [φ, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul])
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w K hw a R hR
  have hN := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφm hφ hφw a H R hH hR hHR hnear hweighted _ hZ).1
  exact normalCutoffPairing_eq_rieszScalarPairing m C μ hg e w χ hcoord a R hR hφ hzero hN

theorem normalized_energy_from_vector_pairing {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (e : Ambient d) (w χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hcoord : ∀ x y, w x - w y = inner ℝ e (x - y))
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (H R : ℝ)
    (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M δ b W A : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hW : |w a| ≤ W) (hA : 0 ≤ A) (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * b ^ k) ^ 2)
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0)
    (hsmall : |rieszScalarPairing (p + 1) μ a R e (fun x => χ x ^ 2 * w x)| ≤ A * δ ^ 2) :
    0 ≤ normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2)
        ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
        normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L := by
  have heq := normalCutoffPairing_eq_riesz_of_lipschitz (p + 1) C μ hg e w χ K hw hcoord
    hχ.continuous.measurable hχbound a H R hH hR hHR hχsupport hzero
  rw [← heq] at hsmall
  exact normalized_cutoff_energy_bound p C B μ hg hCB w χ K L hw hχ hχbound
    a H R hH hR hHR hχsupport M δ b W A hM hδ hb0 hb2 hW hA N hlast hmass hsecond hshell hsmall

end

end RieszRectifiability

end OAI
