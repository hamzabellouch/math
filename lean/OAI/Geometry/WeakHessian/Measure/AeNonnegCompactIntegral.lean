import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactThickenedIndicator

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessianCalculus
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.SeparableSpace X] {m : Measure X}
lemma ae_nonneg_of_compact_integral {H : X → ℝ} (hH : Integrable H m)
    (hpos : ∀ s : Set X, IsCompact s → 0 ≤ ∫ x in s, H x ∂m) :
    ∀ᵐ x ∂m, 0 ≤ H x := by
  let ν := m.withDensity (fun x => ‖H x‖ₑ)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hH.hasFiniteIntegral.ne
  apply ae_nonneg_of_forall_setIntegral_nonneg hH
  intro s hs _hfin
  by_contra h
  have ha : 0 < -(∫ x in s, H x ∂m) := neg_pos.mpr (lt_of_not_ge h)
  obtain ⟨K,hKs,hK,hsmall⟩ := hs.exists_isCompact_sdiff_lt
    (measure_ne_top ν s) (ENNReal.ofReal_ne_zero_iff.mpr ha)
  have hnorm : ‖∫ x in s \ K, H x ∂m‖ₑ < ENNReal.ofReal (-(∫ x in s, H x ∂m)) := by
    apply (enorm_integral_le_lintegral_enorm H).trans_lt
    change (∫⁻ x in s \ K, ‖H x‖ₑ ∂m) < _
    simpa only [ν,withDensity_apply _ (hs.diff hK.measurableSet)] using hsmall
  rw [Real.enorm_eq_ofReal_abs] at hnorm
  have hn : |∫ x in s \ K, H x ∂m| < -(∫ x in s, H x ∂m) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)).mp hnorm
  rw [setIntegral_sdiff hK.measurableSet hH.integrableOn hKs] at hn
  have hkpos := hpos K hK
  linarith [neg_le_abs ((∫ x in s, H x ∂m)-(∫ x in K, H x ∂m))]

lemma ae_nonneg_of_integral_lipschitz_compact {H : X → ℝ} (hH : Integrable H m)
    (hpos : ∀ φ : X → ℝ, HasCompactSupport φ →
      (∃ L : ℝ≥0, LipschitzWith L φ) → (∀ x, 0 ≤ φ x) → (∀ x, φ x ≤ 1) →
      0 ≤ ∫ x, H x*φ x ∂m) : ∀ᵐ x ∂m, 0 ≤ H x := by
  apply ae_nonneg_of_compact_integral hH
  intro s hs
  let δ : ℕ → ℝ := fun n => 1/(n+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  let φ : ℕ → X → ℝ := fun n x => thickenedIndicator (hδ n) s x
  have hφ0 (n : ℕ) (x : X) : 0 ≤ φ n x := NNReal.coe_nonneg _
  have hφ1 (n : ℕ) (x : X) : φ n x ≤ 1 :=
    NNReal.coe_le_coe.mpr (thickenedIndicator_le_one (hδ n) s x)
  have hlimφ (x : X) : Tendsto (fun n => φ n x) atTop
      (𝓝 (s.indicator (fun _ => (1:ℝ)) x)) := by
    have h := tendsto_pi_nhds.mp
      (thickenedIndicator_tendsto_indicator_closure hδ tendsto_one_div_add_atTop_nhds_zero_nat s) x
    have h' := NNReal.continuous_coe.continuousAt.tendsto.comp h
    by_cases hx : x ∈ s <;> simpa [hs.isClosed.closure_eq,φ,hx,Function.comp_def] using h'
  have hlim := tendsto_integral_of_dominated_convergence (fun x => |H x|)
    (fun n => hH.aestronglyMeasurable.mul (lipschitz_thickenedIndicator (hδ n)).continuous.aestronglyMeasurable)
    (by simpa only [Real.norm_eq_abs] using hH.norm)
    (fun n => ae_of_all _ fun x => by
      change |H x*φ n x| ≤ |H x|
      rw [abs_mul,abs_of_nonneg (hφ0 n x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hφ1 n x))
    (ae_of_all _ fun x => tendsto_const_nhds.mul (hlimφ x))
  have heq : (fun x => H x*s.indicator (fun _ => (1:ℝ)) x) = s.indicator H := by
    funext x; by_cases hx : x ∈ s <;> simp [hx]
  rw [heq,integral_indicator hs.measurableSet] at hlim
  apply ge_of_tendsto' hlim
  intro n
  exact hpos (φ n) (compact_thickenedIndicator hs (hδ n))
    ⟨_,lipschitz_thickenedIndicator (hδ n)⟩ (hφ0 n) (hφ1 n)
end WeakHessianCalculus

end
end InlinedFile0

end OAI
