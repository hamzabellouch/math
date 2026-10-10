import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.EulerStep

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma eulerStep_generator_eq {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    s*(eulerStep t s-t⁻¹*(eulerStep t s-1)) = eulerStep t s := by
  have hd := (eulerStep_denom_pos ht hs).ne'
  dsimp [eulerStep]
  field_simp
  ring

lemma cfc_eulerStep_eq {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) :
    R*(cfc (eulerStep t) R-(t⁻¹ : ℂ) • (cfc (eulerStep t) R-1)) = cfc (eulerStep t) R := by
  have hc : ContinuousOn (eulerStep t) (spectrum ℝ R) :=
    (eulerStep_continuousOn ht).mono fun _ hs => resolvent_spectrum_bounds hR hR1 hs
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  have hf : ContinuousOn (fun s => eulerStep t s-t⁻¹*(eulerStep t s-1)) (spectrum ℝ R) :=
    hc.sub (continuousOn_const.mul (hc.sub continuousOn_const))
  have he : cfc (fun s => s*(eulerStep t s-t⁻¹*(eulerStep t s-1))) R = cfc (eulerStep t) R :=
    cfc_congr fun s hs => eulerStep_generator_eq ht (resolvent_spectrum_bounds hR hR1 hs)
  rw [cfc_mul (fun s : ℝ => s) _ R continuous_id.continuousOn hf, hid,
    cfc_sub (eulerStep t) (fun s => t⁻¹*(eulerStep t s-1)) R hc (continuousOn_const.mul (hc.sub continuousOn_const))] at he
  have hsm : cfc (fun s => t⁻¹*(eulerStep t s-1)) R = t⁻¹ • cfc (fun s => eulerStep t s-1) R :=
    cfc_smul t⁻¹ _ _ (hc.sub continuousOn_const)
  rw [hsm, cfc_sub (eulerStep t) (fun _ => 1) R hc continuousOn_const,
    cfc_const 1 R hR.isSelfAdjoint, map_one] at he
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at he
  change R * (cfc (eulerStep t) R - Complex.ofReal (t⁻¹) • (cfc (eulerStep t) R - 1)) = _ at he
  simpa only [Complex.ofReal_inv] using he

lemma cfc_eulerApproximation_tendsto {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => (cfc (eulerStep (t/(2:ℝ)^n)) R)^(2^n:ℕ))
      atTop (𝓝 (resolventHeat R t)) := by
  have hsub : spectrum ℝ R ⊆ Icc (0:ℝ) 1 := fun _ hs => resolvent_spectrum_bounds hR hR1 hs
  have H := tendsto_cfc_fun ((eulerApproximation_uniform ht).mono hsub)
    (Filter.Eventually.of_forall (fun n =>
      ((eulerStep_continuousOn (by positivity : 0 < t/(2:ℝ)^n)).pow (2^n)).mono hsub))
  change Tendsto _ atTop (𝓝 (cfc (heatSymbol t) R))
  convert H using 1
  funext n
  exact (cfc_pow _ _ _ ((eulerStep_continuousOn (by positivity : 0 < t/(2:ℝ)^n)).mono hsub) hR.isSelfAdjoint).symm

end WeakHessianFunctional

end
end InlinedFile0

end OAI
