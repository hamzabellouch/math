import Mathlib
import OAI.Geometry.WeakHessian.Curvature.DecayWeight
import OAI.Geometry.WeakHessian.Measure.IntegrableFatouNonneg

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_mass_nonneg {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) m ∧ (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  have hsub := cheegerHeat_submass hfin o h u hu hi ht
  refine ⟨hsub.1,le_antisymm hsub.2 ?_⟩
  have hχ (n : ℕ) : ∀ᵐ x ∂m, |radialCutoff o n x| ≤ (1:ℝ) := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let us (n : ℕ) : Lp ℝ 2 m := boundedMulLp (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (hχ n) u
  have he (n : ℕ) : us n =ᵐ[m] fun x => u x*radialCutoff o n x := boundedMulLp_ae _ _ u
  have hs (n : ℕ) : ∀ᵐ x ∂m, (n:ℝ)+1 ≤ dist x o → us n x = 0 := by
    filter_upwards [he n] with x hx hdist
    rw [hx]
    have hz : radialCutoff o n x = 0 := by
      apply max_eq_left
      have H : 1 ≤ dist x o/((n:ℝ)+1) := (le_div_iff₀ (by positivity)).mpr (by simpa using hdist)
      linarith
    rw [hz,mul_zero]
  have hle (n : ℕ) : ∀ᵐ x ∂m, us n x ≤ u x := by
    filter_upwards [he n,hu] with x hx hpos
    rw [hx]
    exact mul_le_of_le_one_right hpos (radialCutoff_le_one o n x)
  have hmass (n : ℕ) := hcd.cheegerHeat_mass_supported hN hfull hfin o h (us n) (hs n) ht
  have hbound (n : ℕ) : (∫ x,u x*radialCutoff o n x ∂m) ≤ ∫ x,cheegerHeat h t u x ∂m := by
    rw [← integral_congr_ae (he n),← (hmass n).2]
    exact integral_mono_ae (hmass n).1 hsub.1 (cheegerHeat_order h ht (us n) u (hle n))
  exact le_of_tendsto (integral_radialCutoff_tendsto o hi) (Eventually.of_forall hbound)

lemma CurvatureDimension.cheegerHeat_probability {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {t : ℝ} (ht : 0 ≤ t) : IsProbabilityMeasure (densityMeasure m (cheegerHeat h t u)) := by
  have H := hcd.cheegerHeat_mass_nonneg hN hfull hfin o h u hu (integrable_of_integral_eq_one hmass) ht
  exact densityMeasure_probability_of_integrable _ (cheegerHeat_nonneg h ht u hu) H.1 (H.2.trans hmass)
end WeakHessian

end
end InlinedFile0

end OAI
