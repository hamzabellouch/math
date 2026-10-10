import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.MultiplicityMass
import OAI.Geometry.CAT0Fillings.Charts.Transitions
import OAI.Geometry.CAT0Fillings.Charts.ContainingCharts
import OAI.Geometry.CAT0Fillings.Charts.IntegerSeries

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma actionWeight_bound {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    ∃ M : ℝ, ∀ᵐ x ∂volume.restrict C.domain, ‖C.scalar b x * C.jacobian π x‖ ≤ M := by
  obtain ⟨M,hM⟩ := hab.1.2
  obtain ⟨B,hB⟩ := C.exists_jacobian_bound hab.2
  refine ⟨max M 0 * max B 0,?_⟩
  filter_upwards [hB,ae_restrict_mem C.borel] with x hx hxs
  rw [norm_mul]
  apply mul_le_mul
  · rw [C.scalar_eq hxs,Real.norm_eq_abs]
    exact (hM _).trans (le_max_left _ _)
  · exact hx.trans (le_max_left _ _)
  · exact norm_nonneg _
  · exact le_max_right _ _

noncomputable def sumMultiplicities (θ : ℕ → Euc k → ℤ)
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) (volume.restrict C.domain))
    (hS : Summable (fun i => ∫ x in C.domain, |(θ i x : ℝ)|)) : IntegerChart X k :=
  C.withMultiplicity (summedMultiplicity θ) (summedMultiplicity_integrable hθ hS)

lemma sumMultiplicities_action (θ : ℕ → Euc k → ℤ)
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) (volume.restrict C.domain))
    (hS : Summable (fun i => ∫ x in C.domain, |(θ i x : ℝ)|)) (b : X → ℝ) (π : Fin k → X → ℝ) :
    (C.sumMultiplicities θ hθ hS).action b π =
      ∑' i, (C.withMultiplicity (θ i) (hθ i)).action b π := by
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    change (∫ x in C.domain, (summedMultiplicity θ x : ℝ) * C.scalar b x * C.jacobian π x) =
      ∑' i, ∫ x in C.domain, (θ i x : ℝ) * C.scalar b x * C.jacobian π x
    simp_rw [mul_assoc]
    obtain ⟨M,hM⟩ := C.actionWeight_bound hab
    obtain ⟨K,hK⟩ := hab.1.1
    exact summedMultiplicity_integral_weight hθ hS
      ((C.measurable_scalar hK).aestronglyMeasurable.mul (C.jacobian_aestronglyMeasurable hab.2)) hM
  · simp only [action,ite_eq_right hab,tsum_zero]

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}

theorem exists_overlap_sum (D : IntegerChart X k) (C : ℕ → IntegerChart X k)
    (hCD : ∀ i, (C i).image ⊆ D.image) (hC : ∀ i, IsMetricCurrent (C i).action)
    (hS : Summable (fun i => mass (C i).action)) :
    ∃ E : IntegerChart X k, E.image = D.image ∧
      ∀ b π, E.action b π = ∑' i, (C i).action b π := by
  choose F hFD hparam hact him using fun i => (C i).exists_inCoordinates D (hCD i)
  let G (i : ℕ) : IntegerChart X k := (F i).extendOn D (hFD i)
  have hG i : (G i).action = (C i).action :=
    ((F i).extendOn_action D (hFD i) (hparam i)).trans (hact i)
  have hGcurrent i : IsMetricCurrent (G i).action := by rw [hG]; exact hC i
  obtain ⟨L,U,_,hU⟩ := D.bilipschitz
  let θ (i : ℕ) := (G i).multiplicity
  have hθ i : Integrable (fun x => (θ i x : ℝ)) (volume.restrict D.domain) := (G i).integrable
  have hl1 : Summable (fun i => ∫ x in D.domain, |(θ i x : ℝ)|) := by
    apply (hS.mul_left ((U : ℝ)^k)).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun _ => abs_nonneg _)
    · intro i
      have hbound := (G i).multiplicity_integral_le_mass (hGcurrent i) hU
      change (∫ x in D.domain, |(θ i x : ℝ)|) ≤ (U : ℝ)^k * mass (G i).action at hbound
      simpa only [hG] using hbound
  refine ⟨D.sumMultiplicities θ hθ hl1,rfl,?_⟩
  intro b π
  rw [D.sumMultiplicities_action θ hθ hl1]
  apply tsum_congr
  intro i
  change (G i).action b π = _
  rw [hG]

end IntegerChart
end CAT0Fillings

end

end OAI
