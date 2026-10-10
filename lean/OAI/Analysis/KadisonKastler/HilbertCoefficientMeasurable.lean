import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

namespace OAI

/-! # Measurability from countably many Hilbert coefficients

The coefficients against a countable dense family give a continuous
injection into a countable product of copies of `ℂ`. Lusin–Souslin makes
this map a measurable embedding. Thus measurability of the coefficients
implies strong measurability, without assuming a Pettis theorem.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {D H ι : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] {μ : Measure D}

/-- Countably many dense coefficient tests determine a measurable vector field. -/
theorem aestronglyMeasurable_of_dense_inner [Countable ι]
    (v : ι → H) (hv : DenseRange v) (f : D → H)
    (hf : ∀ i, AEStronglyMeasurable (fun x => inner ℂ (v i) (f x)) μ) :
    AEStronglyMeasurable f μ := by
  borelize H
  let T : H → (ι → ℂ) := fun ξ i => inner ℂ (v i) ξ
  have hT : Continuous T := continuous_pi fun i => continuous_const.inner continuous_id
  have hTi : Function.Injective T := by
    intro ξ η heq
    exact hv.eq_of_inner_right ℂ (fun i => congrFun heq i)
  have hTe : MeasurableEmbedding T := hT.measurableEmbedding hTi
  have hm : AEMeasurable (T ∘ f) μ :=
    AEMeasurable.of_eval fun i => (hf i).aemeasurable
  exact (hTe.aemeasurable_comp_iff.mp hm).aestronglyMeasurable

/-- The same criterion stated using a countable dense subset. -/
theorem aestronglyMeasurable_of_countable_dense_inner
    (s : Set H) (hs : s.Countable) (hd : Dense s) (f : D → H)
    (hf : ∀ η ∈ s, AEStronglyMeasurable (fun x => inner ℂ η (f x)) μ) :
    AEStronglyMeasurable f μ := by
  let : Countable s := hs.to_subtype
  have hd' : DenseRange (fun η : s => (η : H)) := by
    change Dense (Set.range (fun η : s => (η : H)))
    rw [Subtype.range_coe]
    exact hd
  apply aestronglyMeasurable_of_dense_inner (fun η : s => (η : H))
    hd' f
  intro η
  exact hf η η.property

/-- In a separable Hilbert space, measurable scalar coefficients imply
strong measurability of the vector field. -/
theorem aestronglyMeasurable_of_inner (f : D → H)
    (hf : ∀ η : H, AEStronglyMeasurable (fun x => inner ℂ η (f x)) μ) :
    AEStronglyMeasurable f μ := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  exact aestronglyMeasurable_of_dense_inner v hv f (fun n => hf (v n))

/-- Once a field has measurable evaluations, its adjoint does too.
This uses the scalar adjoint identity and the preceding coefficient test. -/
theorem operator_adjoint_eval_aestronglyMeasurable
    (T : D → H →L[ℂ] H)
    (hT : ∀ ξ, AEStronglyMeasurable (fun x => T x ξ) μ) (η : H) :
    AEStronglyMeasurable (fun x => star (T x) η) μ := by
  apply aestronglyMeasurable_of_inner
  intro ξ
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] using (hT ξ).inner_const (c := η)

/-- Testing both variables only on a countable dense family suffices to
make every evaluation of an operator field strongly measurable. -/
theorem operator_eval_aestronglyMeasurable_of_dense_coefficients [Countable ι]
    (v : ι → H) (hv : DenseRange v) (T : D → H →L[ℂ] H)
    (hT : ∀ i j, AEStronglyMeasurable (fun x => inner ℂ (v i) (T x (v j))) μ)
    (ξ : H) : AEStronglyMeasurable (fun x => T x ξ) μ := by
  apply aestronglyMeasurable_of_dense_inner v hv
  intro i
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp (hv ξ)
  choose j hj using hw
  have hvlim : Tendsto (fun n => v (j n)) atTop (𝓝 ξ) := by
    simpa only [hj] using hlim
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => hT i (j n))
  exact Eventually.of_forall fun x =>
    ((continuous_const.inner (T x).continuous).tendsto ξ).comp hvlim

/-- The two sets of measurable evaluations needed for the weak operator
field C-star algebra follow from the same countable coefficient data. -/
theorem operator_field_aestronglyMeasurable_of_dense_coefficients [Countable ι]
    (v : ι → H) (hv : DenseRange v) (T : D → H →L[ℂ] H)
    (hT : ∀ i j, AEStronglyMeasurable (fun x => inner ℂ (v i) (T x (v j))) μ) :
    ∀ ξ, AEStronglyMeasurable (fun x => T x ξ) μ ∧
      AEStronglyMeasurable (fun x => star (T x) ξ) μ := by
  have hm := operator_eval_aestronglyMeasurable_of_dense_coefficients v hv T hT
  exact fun ξ => ⟨hm ξ, operator_adjoint_eval_aestronglyMeasurable T hm ξ⟩

end

end KadisonKastler

end OAI
