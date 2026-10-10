import Mathlib
import OAI.Geometry.IntegralFillings.Charts.DomainRestriction

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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)
noncomputable def withMultiplicity (θ : Euc k → ℤ)
    (hθ : Integrable (fun x => (θ x : ℝ)) (volume.restrict C.domain)) : IntegerChart X k :=
  {C with multiplicity := θ, integrable := hθ}

variable (hCD : C.domain ⊆ D.domain)
  (hparam : ∀ z : C.domain, C.param z = D.param ⟨z,hCD z.property⟩)

include hCD hparam in
lemma scalar_eqOn_containing (b : X → ℝ) : EqOn (C.scalar b) (D.scalar b) C.domain := by
  intro x hx
  rw [C.scalar_eq hx,D.scalar_eq (hCD hx),hparam ⟨x,hx⟩]

include hCD hparam in
lemma jacobian_eqOn_containing_ae {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    C.jacobian π =ᵐ[volume.restrict C.domain] D.jacobian π := by
  have hrow : ∀ i, ∀ᵐ x ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (π i)) C.domain x =
      fderivWithin ℝ (D.scalar (π i)) D.domain x := by
    intro i
    obtain ⟨K,hK⟩ := hπ i
    obtain ⟨L,U,hL,_⟩ := D.bilipschitz
    exact ae_fderivWithin_restrict_domain volume D.borel C.borel hCD
      (D.scalar_lipschitzOn hL hK) (C.scalar_eqOn_containing D hCD hparam (π i))
  filter_upwards [ae_all_iff.mpr hrow] with x hx
  unfold jacobian
  congr 1
  funext i j
  exact congrArg (fun A => A (EuclideanSpace.single j 1)) (hx i)

include hCD in
lemma indicatorMultiplicity_integrable :
    Integrable (fun x => ((C.domain.indicator C.multiplicity x : ℤ) : ℝ))
      (volume.restrict D.domain) := by
  have hI : IntegrableOn (fun x => (C.multiplicity x : ℝ)) C.domain
      (volume.restrict D.domain) := by
    simpa only [IntegrableOn,Measure.restrict_restrict C.borel,inter_eq_left.mpr hCD] using C.integrable
  apply ((integrable_indicator_iff C.borel).mpr hI).congr
  filter_upwards with x
  by_cases hx : x ∈ C.domain <;> simp [hx]

noncomputable def extendOn : IntegerChart X k :=
  D.withMultiplicity (C.domain.indicator C.multiplicity) (C.indicatorMultiplicity_integrable D hCD)

include hparam in
lemma extendOn_action : (C.extendOn D hCD).action = C.action := by
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    change (∫ x in D.domain, ((C.domain.indicator C.multiplicity x : ℤ) : ℝ) *
      D.scalar b x * D.jacobian π x) = _
    have heq : (fun x => ((C.domain.indicator C.multiplicity x : ℤ) : ℝ) *
        D.scalar b x * D.jacobian π x) =
        C.domain.indicator (fun x => (C.multiplicity x : ℝ) * D.scalar b x * D.jacobian π x) := by
      funext x
      by_cases hx : x ∈ C.domain <;> simp [hx]
    rw [heq,integral_indicator C.borel,Measure.restrict_restrict C.borel,inter_eq_left.mpr hCD]
    apply integral_congr_ae
    filter_upwards [C.jacobian_eqOn_containing_ae D hCD hparam hab.2,
      ae_restrict_mem C.borel] with x hx hxs
    rw [hx,C.scalar_eqOn_containing D hCD hparam b hxs]
  · simp only [action,ite_eq_right hab]

end IntegerChart
end SharpIntegralFillings

end

end OAI
