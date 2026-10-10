import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ComplexifyReal

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.scaled_resolvent_cfc {t : ℝ} (ht : 0 < t) :
    (hQ.scale ht).resolventLinear = realCfc m hQ.resolventLinear (eulerStep t) := by
  ext1 u
  change (hQ.scale ht).resolvent u = realCfc m hQ.resolventLinear (eulerStep t) u
  rw [hQ.scaled_resolvent_iff ht, hQ.isFormGenerator_iff]
  exact realCfc_eulerStep_eq m hQ.resolvent_positive hQ.resolvent_le_one ht u

lemma ClosedQuadraticEnergy.euler_tendsto_heat {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => (((hQ.scale (by positivity : 0 < t/(2:ℝ)^n)).resolventLinear)^(2^n:ℕ)) u)
      atTop (𝓝 (realHeat m hQ.resolventLinear t u)) := by
  have heq : ∀ n : ℕ,
      (hQ.scale (by positivity : 0 < t/(2:ℝ)^n)).resolventLinear =
        realCfc m hQ.resolventLinear (eulerStep (t/(2:ℝ)^n)) := by
    intro n
    exact hQ.scaled_resolvent_cfc m (by positivity)
  simp_rw [heq]
  exact realCfc_eulerApproximation_tendsto m hQ.resolvent_positive hQ.resolvent_le_one ht u

lemma ClosedQuadraticEnergy.resolvent_normal_fixed
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    (hηQ : ∀ f : Lp ℝ 2 m, Q (hη.compLp hη0 f) ≤ Q f) (u : Lp ℝ 2 m)
    (hu : hη.compLp hη0 u = u) : hη.compLp hη0 (hQ.resolvent u) = hQ.resolvent u := by
  let f := hQ.resolvent u
  let g := hη.compLp hη0 f
  have hn : ‖g-u‖ ≤ ‖f-u‖ := by
    simpa only [hu, NNReal.coe_one, one_mul] using hη.norm_compLp_sub_le hη0 f u
  have hj : proximalFunctional Q u g ≤ proximalFunctional Q u f := by
    apply add_le_add (hηQ f)
    apply ENNReal.ofReal_le_ofReal
    nlinarith [norm_nonneg (g-u), norm_nonneg (f-u)]
  exact hQ.minimizer_unique (fun v => hj.trans (hQ.resolvent_minimizes u v))
    (hQ.resolvent_minimizes u)

lemma ClosedQuadraticEnergy.heat_normal_fixed
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hη0 : η 0 = 0)
    (hηQ : ∀ f : Lp ℝ 2 m, Q (hη.compLp hη0 f) ≤ Q f) (u : Lp ℝ 2 m)
    (hu : hη.compLp hη0 u = u) {t : ℝ} (ht : 0 ≤ t) :
    hη.compLp hη0 (realHeat m hQ.resolventLinear t u) = realHeat m hQ.resolventLinear t u := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [realHeat_zero m hQ.resolvent_positive, one_apply_eq_self] using hu
  have hstep {s : ℝ} (hs : 0 < s) (v : Lp ℝ 2 m) (hv : hη.compLp hη0 v = v) :
      hη.compLp hη0 ((hQ.scale hs).resolventLinear v) = (hQ.scale hs).resolventLinear v :=
    (hQ.scale hs).resolvent_normal_fixed m hη hη0 (fun f => mul_le_mul_right (hηQ f) _) v hv
  have hpow {s : ℝ} (hs : 0 < s) (n : ℕ) :
      hη.compLp hη0 ((((hQ.scale hs).resolventLinear)^n) u) = (((hQ.scale hs).resolventLinear)^n) u := by
    induction n with
    | zero => exact hu
    | succ n ih =>
      simpa only [pow_succ', mul_apply_eq_comp] using hstep hs ((((hQ.scale hs).resolventLinear)^n) u) ih
  have H := hQ.euler_tendsto_heat m ht u
  have Hη := (hη.continuous_compLp hη0).continuousAt.tendsto.comp H
  have Hη' := H.congr' (Filter.Eventually.of_forall (fun n =>
    (hpow (by positivity : 0 < t/(2:ℝ)^n) (2^n)).symm))
  exact tendsto_nhds_unique Hη Hη'

end WeakHessianFunctional

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
