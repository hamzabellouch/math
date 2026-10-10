import Mathlib
import OAI.Geometry.IntegralFillings.Charts.MultiplicityRestriction
import OAI.Geometry.IntegralFillings.Currents.ActionSeries

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
attribute [local instance] Classical.propDecidable
open BorelCoefficients BorelRestriction MassMeasure

theorem integerRectifiable_restrict
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (hrect : IntegerRectifiable T) {E : Set X} (hE : MeasurableSet E) :
    IntegerRectifiable (restrictCurrent hT E) := by
  obtain ⟨C,hdis,hC,hsum,heq⟩ := hrect
  let D : ℕ → IntegerChart X k := fun i => (C i).restrictMultiplicity E hE
  have hD (i) : IsMetricCurrent (D i).action :=
    (C i).restrictMultiplicity_isMetricCurrent (hC i) hE
  refine ⟨D,hdis,hD,?_,?_⟩
  · apply hsum.of_nonneg_of_le (fun i => mass_nonneg (D i).action)
    exact fun i => (C i).restrictMultiplicity_mass_le (hC i) hE
  · let μ (i) := currentMassMeasure (hC i)
    have hμfin : ∀ i, IsFiniteMeasure (μ i) := fun i => inferInstance
    let := hμfin
    have hμsum : Summable (fun i => (μ i).real univ) := by
      simpa only [μ,currentMassMeasure_total] using hsum
    let := finite_sum_measure_of_summable_total μ hμsum
    have hμ (i) : Controls (C i).action (μ i) := currentMassMeasure_controls (hC i)
    intro b π
    by_cases hab : Admissible b π
    · rw [restrictCurrent_apply hT E hab,
        borelAction_independent (currentMassMeasure hT) hT
          (currentMassMeasure_controls hT) (controls_sum hμ heq)
          ((integrable_boundedLip _ hab.1).indicator hE)
          ((integrable_boundedLip _ hab.1).indicator hE) π hab.2,
        borelAction_sum μ hT hC hμ heq
          ((integrable_boundedLip _ hab.1).indicator hE) π hab.2]
      apply tsum_congr
      intro i
      change _ = ((C i).restrictMultiplicity E hE).action b π
      rw [(C i).restrictMultiplicity_action (hC i) hE,restrictCurrent_apply (hC i) E hab]
    · rw [(restrictCurrent_isMetricCurrent hT hE).offDomain b π hab]
      symm
      calc
        (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
          tsum_congr (fun i => (hD i).offDomain b π hab)
        _ = 0 := tsum_zero

end SharpIntegralFillings

namespace SharpIntegralFillings
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma ae_fderivWithin_restrict_domain (μ : Measure E) [μ.IsAddHaarMeasure]
    {s t : Set E} (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    {f g : E → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hgf : EqOn g f t) :
    ∀ᵐ x ∂μ.restrict t, fderivWithin ℝ g t x = fderivWithin ℝ f s x := by
  obtain ⟨F,hF,hfF⟩ := hf.extend_real
  have hgF : EqOn g F t := fun x hx => (hgf hx).trans (hfF (hts hx))
  filter_upwards [ae_fderivWithin_eq_fderiv_extension μ ht hF hgF,
    (ae_fderivWithin_eq_fderiv_extension μ hs hF hfF).filter_mono
      (ae_mono (Measure.restrict_mono hts le_rfl))] with x hx hy
  exact hx.trans hy.symm

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

noncomputable def restrictDomain {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) : IntegerChart X k where
  domain := t
  borel := ht
  bounded := C.bounded.subset hts
  param := fun z => C.param ⟨z,hts z.property⟩
  bilipschitz := by
    obtain ⟨K,J,hK,hJ⟩ := C.bilipschitz
    refine ⟨K,J,LipschitzWith.of_dist_le_mul (fun a b =>
      hK.dist_le_mul ⟨a,hts a.property⟩ ⟨b,hts b.property⟩),?_⟩
    exact AntilipschitzWith.of_le_mul_dist (fun a b =>
      hJ.le_mul_dist ⟨a,hts a.property⟩ ⟨b,hts b.property⟩)
  multiplicity := C.multiplicity
  integrable := C.integrable.mono_measure (Measure.restrict_mono hts le_rfl)

omit [MeasurableSpace X] [BorelSpace X] in
lemma restrictDomain_scalar {t : Set (Euc k)} (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (b : X → ℝ) : EqOn ((C.restrictDomain ht hts).scalar b) (C.scalar b) t := by
  classical
  intro x hx
  change (if hz : x ∈ t then b (C.param ⟨x,hts hz⟩) else 0) = C.scalar b x
  rw [dite_eq_left hx,scalar,dite_eq_left (hts hx)]

omit [MeasurableSpace X] [BorelSpace X] in
lemma restrictDomain_jacobian_ae {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    (C.restrictDomain ht hts).jacobian π =ᵐ[volume.restrict t] C.jacobian π := by
  have hderiv : ∀ᵐ x ∂volume.restrict t, ∀ i,
      fderivWithin ℝ ((C.restrictDomain ht hts).scalar (π i)) t x =
        fderivWithin ℝ (C.scalar (π i)) C.domain x := by
    rw [eventually_all]
    intro i
    obtain ⟨K,hK⟩ := hπ i
    obtain ⟨L,J,hL,_⟩ := C.bilipschitz
    exact ae_fderivWithin_restrict_domain volume C.borel ht hts
      (C.scalar_lipschitzOn hL hK) (C.restrictDomain_scalar ht hts (π i))
  filter_upwards [hderiv] with x hx
  unfold jacobian
  congr 1
  funext i j
  exact congrArg (fun l => l (EuclideanSpace.single j 1)) (hx i)

variable [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma paramExtended_mem_image_iff {t : Set (Euc k)} (hts : t ⊆ C.domain)
    {x : Euc k} (hx : x ∈ C.domain) :
    C.paramExtended x ∈ C.paramExtended '' t ↔ x ∈ t := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨K,J,_,hJ⟩ := C.bilipschitz
    have hxy' : C.param ⟨y,hts hy⟩ = C.param ⟨x,hx⟩ := by
      simpa only [paramExtended,dite_eq_left hx,dite_eq_left (hts hy)] using hxy
    have heq : y = x := congrArg Subtype.val (hJ.injective hxy')
    exact heq ▸ hy
  · exact fun h => ⟨x,h,rfl⟩

lemma restrictDomain_action {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) (hC : IsMetricCurrent C.action) :
    (C.restrictDomain ht hts).action =
      BorelRestriction.restrictCurrent hC (C.paramExtended '' t) := by
  classical
  let E := C.paramExtended '' t
  have hE : MeasurableSet E := C.measurableSet_paramExtended_image ht hts
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hadm : Admissible b π
  · rw [action,action,ite_eq_left hadm,ite_eq_left hadm]
    change (∫ z in t, (C.multiplicity z : ℝ)*(C.restrictDomain ht hts).scalar b z*
      (C.restrictDomain ht hts).jacobian π z) =
      ∫ z in C.domain, (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ)*
        C.scalar b z*C.jacobian π z
    calc
      _ = ∫ z in t, (C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z := by
        apply integral_congr_ae
        filter_upwards [C.restrictDomain_jacobian_ae ht hts hadm.2,ae_restrict_mem ht] with z hz hzt
        rw [hz,C.restrictDomain_scalar ht hts b hzt]
      _ = ∫ z in C.domain, t.indicator (fun z =>
          (C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z) z := by
        rw [integral_indicator ht,Measure.restrict_restrict ht,inter_eq_left.mpr hts]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem C.borel] with z hz
        have he : z ∈ C.paramExtended ⁻¹' E ↔ z ∈ t := C.paramExtended_mem_image_iff hts hz
        by_cases hzt : z ∈ t
        · simp only [indicator_of_mem hzt,indicator_of_mem (he.mpr hzt)]
        · simp only [indicator_of_notMem hzt,indicator_of_notMem (mt he.mp hzt),Int.cast_zero,zero_mul]
  · simp only [action,ite_eq_right hadm]

lemma restrictDomain_isMetricCurrent {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) (hC : IsMetricCurrent C.action) :
    IsMetricCurrent (C.restrictDomain ht hts).action := by
  rw [C.restrictDomain_action ht hts hC]
  exact BorelRestriction.restrictCurrent_isMetricCurrent hC
    (C.measurableSet_paramExtended_image ht hts)

lemma restrictDomain_mass {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) (hC : IsMetricCurrent C.action) :
    mass (C.restrictDomain ht hts).action =
      (MassMeasure.currentMassMeasure hC).real (C.paramExtended '' t) := by
  rw [C.restrictDomain_action ht hts hC,
    BorelRestriction.restriction_mass hC (C.measurableSet_paramExtended_image ht hts)]

end IntegerChart
end SharpIntegralFillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings

attribute [local instance] Classical.propDecidable

universe u

end SharpIntegralFillings

end

end OAI
