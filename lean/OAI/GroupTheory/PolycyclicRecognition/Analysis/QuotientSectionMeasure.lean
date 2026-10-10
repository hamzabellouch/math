import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientSectionCoordinates
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! # Product measure in quotient-section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]
  [μQ.IsMulLeftInvariant] [μI.IsMulRightInvariant]

/-- Conjugation invariance of the kernel measure and right invariance of
its translations make the coordinate skew action preserve product measure. -/
theorem quotientSection_skew_measurePreserving
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) μI μI) (n : N) :
    MeasurePreserving (fun p : Q × π.ker =>
      (π n * p.1, quotientKernelConjugate π n p.2 * quotientSectionCocycle π s hs n p.1))
      (μQ.prod μI) (μQ.prod μI) := by
  have hleft : MeasurePreserving (fun q : Q => π n * q) μQ μQ :=
    ⟨measurable_const.mul measurable_id, map_mul_left_eq_self μQ (π n)⟩
  apply hleft.skew_product (g := fun q i =>
    quotientKernelConjugate π n i * quotientSectionCocycle π s hs n q)
  · have hc : Continuous (quotientKernelConjugate π n) :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    exact ((hc.comp continuous_snd).mul
      ((continuous_quotientSectionCocycle π s hs n).comp continuous_fst)).measurable
  · apply Filter.Eventually.of_forall
    intro q
    have hright : MeasurePreserving (fun i : π.ker => i * quotientSectionCocycle π s hs n q) μI μI :=
      ⟨(continuous_id.mul continuous_const).measurable, map_mul_right_eq_self μI _⟩
    exact (hright.comp (hconj n)).map_eq

/-- Pushing product measure through the actual global section coordinates
gives a left-invariant measure on the original group. -/
theorem quotientSection_product_left_invariant
    (hconj : ∀ n : N, MeasurePreserving (quotientKernelConjugate π n) μI μI) (n : N) :
    MeasurePreserving (fun x : N => n * x)
      (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI))
      (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)) := by
  let e := quotientSectionHomeomorph π hπ s hs
  let T := fun p : Q × π.ker =>
    (π n * p.1, quotientKernelConjugate π n p.2 * quotientSectionCocycle π s hs n p.1)
  have hT := quotientSection_skew_measurePreserving π s hs μQ μI hconj n
  have hsem : Function.Semiconj e.symm T (fun x => n * x) := by
    intro p
    apply e.injective
    rw [e.apply_symm_apply]
    exact (quotientSection_left_translation π hπ s hs n p).symm
  exact (e.symm.measurable.measurePreserving (μQ.prod μI)).of_semiconj hT hsem
    (continuous_const.mul continuous_id).measurable

end PolycyclicRecognition

end

end OAI
