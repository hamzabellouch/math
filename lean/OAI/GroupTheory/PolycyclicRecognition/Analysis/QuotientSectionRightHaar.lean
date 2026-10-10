import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarProduct
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SkewMeasureFiber

namespace OAI

/-! # Right Haar measure in quotient-section coordinates

Right translations translate each kernel fiber on the right. Consequently
the product of right Haar measures gives a right-invariant measure without
assuming that conjugation preserves the kernel measure. In a unimodular
ambient group, Haar uniqueness then gives left invariance as well.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)

def quotientSectionRightCocycle (n : N) (q : Q) : π.ker :=
  ⟨s q * n * (s (q * π n))⁻¹, by simp [hs]⟩

theorem continuous_quotientSectionRightCocycle (n : N) :
    Continuous (quotientSectionRightCocycle π s hs n) := by
  exact ((s.continuous.mul continuous_const).mul
    (s.continuous.comp (continuous_id.mul continuous_const)).inv).subtype_mk _

omit [IsTopologicalGroup Q] in
theorem quotientSection_right_translation (n : N) (p : Q × π.ker) :
    quotientSectionHomeomorph π hπ s hs
      ((quotientSectionHomeomorph π hπ s hs).symm p * n) =
      (p.1 * π n, p.2 * quotientSectionRightCocycle π s hs n p.1) := by
  have hp : π p.2 = 1 := p.2.property
  apply Prod.ext
  · simp [quotientSectionHomeomorph, hp, hs]
  · apply Subtype.ext
    change ((p.2 : N) * s p.1) * n *
        (s (π (((p.2 : N) * s p.1) * n)))⁻¹ =
      (p.2 : N) * (s p.1 * n * (s (p.1 * π n))⁻¹)
    simp only [map_mul, hp, hs, one_mul]
    group

variable [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsMulRightInvariant] [μI.IsMulRightInvariant]

theorem quotientSection_right_skew_measurePreserving (n : N) :
    MeasurePreserving (fun p : Q × π.ker =>
      (p.1 * π n, p.2 * quotientSectionRightCocycle π s hs n p.1))
      (μQ.prod μI) (μQ.prod μI) := by
  apply (measurePreserving_mul_right μQ (π n)).skew_product
    (g := fun q i => i * quotientSectionRightCocycle π s hs n q)
  · exact (continuous_snd.mul
      ((continuous_quotientSectionRightCocycle π s hs n).comp continuous_fst)).measurable
  · exact Filter.Eventually.of_forall fun q => map_mul_right_eq_self μI _

theorem quotientSection_product_right_invariant (n : N) :
    MeasurePreserving (fun x : N => x * n)
      (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI))
      (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)) := by
  let e := quotientSectionHomeomorph π hπ s hs
  let T := fun p : Q × π.ker =>
    (p.1 * π n, p.2 * quotientSectionRightCocycle π s hs n p.1)
  have hT := quotientSection_right_skew_measurePreserving π s hs μQ μI n
  have hsem : Function.Semiconj e.symm T (fun x => x * n) := by
    intro p
    apply e.injective
    rw [e.apply_symm_apply]
    exact (quotientSection_right_translation π hπ s hs n p).symm
  exact (e.symm.measurable.measurePreserving (μQ.prod μI)).of_semiconj hT hsem
    (continuous_id.mul continuous_const).measurable

theorem quotientSection_product_isMulRightInvariant :
    (Measure.map (quotientSectionHomeomorph π hπ s hs).symm
      (μQ.prod μI)).IsMulRightInvariant :=
  ⟨fun n => (quotientSection_product_right_invariant π hπ s hs μQ μI n).map_eq⟩

variable [T2Space N] [LocallyCompactSpace N] [hNsc : SecondCountableTopology N]
  [IsFiniteMeasureOnCompacts μQ] [IsFiniteMeasureOnCompacts μI]

omit [T2Space N] in
theorem quotientSection_product_leftInvariant_of_unimodular
    (μ : Measure N) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    (Measure.map (quotientSectionHomeomorph π hπ s hs).symm
      (μQ.prod μI)).IsMulLeftInvariant := by
  let M := Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)
  let : IsFiniteMeasureOnCompacts M :=
    Measure.IsFiniteMeasureOnCompacts.map (μQ.prod μI)
      (quotientSectionHomeomorph π hπ s hs).symm
  let : M.IsMulRightInvariant := quotientSection_product_isMulRightInvariant π hπ s hs μQ μI
  obtain ⟨B, hB1, hB, hBfinite⟩ := μ.exists_isOpen_measure_lt_top (1 : N)
  have hBpos : μ B ≠ 0 := ne_of_gt (hB.measure_pos μ ⟨1, hB1⟩)
  have hM := rightInvariant_eq_div_smul M μ hBpos hBfinite.ne
  change M.IsMulLeftInvariant
  rw [hM]
  infer_instance

include hπ s hs hNsc in
omit [T2Space N] in
/-- Unimodularity of the ambient group and of the quotient forces
conjugation to preserve the kernel's right Haar measure. -/
theorem quotientKernelConjugate_preserves_of_unimodular
    [T2Space Q] [LocallyCompactSpace Q]
    [μQ.IsMulLeftInvariant] [μQ.IsOpenPosMeasure]
    (μ : Measure N) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (n : N) :
    MeasurePreserving (quotientKernelConjugate π n) μI μI := by
  let : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set N)
  let : BorelSpace π.ker := inferInstance
  let : MeasurableMul₂ π.ker := ⟨continuous_mul.measurable⟩
  let e := quotientSectionHomeomorph π hπ s hs
  let M := Measure.map e.symm (μQ.prod μI)
  let : M.IsMulLeftInvariant :=
    quotientSection_product_leftInvariant_of_unimodular π hπ s hs μQ μI μ
  let T := fun p : Q × π.ker =>
    (π n * p.1, quotientKernelConjugate π n p.2 * quotientSectionCocycle π s hs n p.1)
  have he : MeasurePreserving e M (μQ.prod μI) :=
    (e.symm.toMeasurableEquiv.measurable.measurePreserving (μQ.prod μI)).symm
  have hsem : Function.Semiconj e (fun x : N => n * x) T := by
    intro x
    have hh := quotientSection_left_translation π hπ s hs n (e x)
    simpa only [e, Homeomorph.symm_apply_apply] using hh
  have hc : Continuous (quotientKernelConjugate π n) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hT : Measurable T :=
    ((hπ.comp continuous_const).mul continuous_fst).prodMk
      ((hc.comp continuous_snd).mul
        ((continuous_quotientSectionCocycle π s hs n).comp continuous_fst)) |>.measurable
  have hskew : MeasurePreserving T (μQ.prod μI) (μQ.prod μI) :=
    he.of_semiconj (measurePreserving_mul_left M n) hsem hT
  obtain ⟨B, hB1, hB, hBfinite⟩ := μQ.exists_isOpen_measure_lt_top (1 : Q)
  exact measurePreserving_fiber_of_right_skew μQ μI (π n)
    (quotientKernelConjugate π n) hc.measurable (quotientSectionCocycle π s hs n)
    (continuous_quotientSectionCocycle π s hs n).measurable hskew
    hB.measurableSet (ne_of_gt (hB.measure_pos μQ ⟨1, hB1⟩)) hBfinite.ne

end PolycyclicRecognition

end

end OAI
