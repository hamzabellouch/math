import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.Group.Action

namespace OAI

/-! # Conditional measures over an invariant measurable factor

Disintegrating the graph of an invariant measurable map gives a measurable
probability kernel with the original measure as barycenter. Uniqueness of
conditional kernels proves invariance of its components almost everywhere,
for each acting element. No ergodicity is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction G X] [MeasurableConstSMul G X] [StandardBorelSpace X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)

/-- The graph measure, with the factor in the first coordinate. -/
def factorGraphMeasure (_hf : Measurable f) : Measure (Y × X) := μ.map (fun x => (f x, x))

include hf

instance factorGraphMeasure_probability : IsProbabilityMeasure (factorGraphMeasure μ f hf) := by
  unfold factorGraphMeasure
  infer_instance

/-- The actual conditional probability kernel supplied by disintegration. -/
def factorConditionalKernel (hf : Measurable f) : Kernel Y X := (factorGraphMeasure μ f hf).condKernel

instance factorConditionalKernel_markov : IsMarkovKernel (factorConditionalKernel μ f hf) := by
  unfold factorConditionalKernel
  infer_instance

omit [StandardBorelSpace X] [Nonempty X] [IsProbabilityMeasure μ] in
theorem factorGraphMeasure_fst : (factorGraphMeasure μ f hf).fst = μ.map f := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  rw [factorGraphMeasure, Measure.fst, Measure.map_map measurable_fst hm]
  rfl

theorem factorConditionalKernel_disintegrate :
    μ.map f ⊗ₘ factorConditionalKernel μ f hf = factorGraphMeasure μ f hf := by
  rw [← factorGraphMeasure_fst μ f hf]
  unfold factorConditionalKernel
  exact (factorGraphMeasure μ f hf).disintegrate _

/-- Conditioning preserves the original measure as its setwise barycenter. -/
theorem factorConditionalKernel_barycenter (s : Set X) (hs : MeasurableSet s) :
    μ s = ∫⁻ x, factorConditionalKernel μ f hf (f x) s ∂μ := by
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  have h := congrArg (fun ν : Measure (Y × X) => ν (univ ×ˢ s))
    (factorConditionalKernel_disintegrate μ f hf)
  rw [Measure.compProd_apply_prod MeasurableSet.univ hs, setLIntegral_univ,
    factorGraphMeasure, Measure.map_apply hm
      (MeasurableSet.univ.prod hs)] at h
  have he : (fun x => (f x, x)) ⁻¹' (univ ×ˢ s) = s := by ext x; simp
  rw [he] at h
  rw [← h, lintegral_map (factorConditionalKernel μ f hf |>.measurable_coe hs) hf]

omit [StandardBorelSpace X] [Nonempty X] in
/-- An invariant factor makes the graph measure invariant in its second coordinate. -/
theorem factorGraphMeasure_map_smul [SMulInvariantMeasure G X μ]
    (hfi : ∀ (g : G) (s : Set Y), MeasurableSet s →
      ∀ x, f (g • x) ∈ s ↔ f x ∈ s) (g : G) :
    (factorGraphMeasure μ f hf).map (Prod.map id (g • ·)) = factorGraphMeasure μ f hf := by
  have hg : Measurable (fun x : X => g • x) := measurable_const_smul g
  have hm : Measurable (fun x => (f x, x)) := hf.prodMk measurable_id
  rw [factorGraphMeasure, Measure.map_map (measurable_id.prodMap hg) hm]
  apply Measure.ext_prod
  intro s t hs ht
  have hcomp : Measurable (Prod.map id (g • ·) ∘ (fun x => (f x, x))) :=
    (measurable_id.prodMap hg).comp hm
  rw [Measure.map_apply hcomp (hs.prod ht), Measure.map_apply hm (hs.prod ht)]
  have he : (Prod.map id (g • ·) ∘ (fun x => (f x, x))) ⁻¹' (s ×ˢ t) =
      (g • ·) ⁻¹' ((fun x => (f x, x)) ⁻¹' (s ×ˢ t)) := by
    ext x
    change (f x ∈ s ∧ g • x ∈ t) ↔ (f (g • x) ∈ s ∧ g • x ∈ t)
    rw [hfi g s hs x]
  rw [he, measure_preimage_smul μ g]

/-- Each fixed acting element preserves almost every conditional probability. -/
theorem factorConditionalKernel_map_smul_ae [SMulInvariantMeasure G X μ]
    (hfi : ∀ (g : G) (s : Set Y), MeasurableSet s →
      ∀ x, f (g • x) ∈ s ↔ f x ∈ s) (g : G) :
    ∀ᵐ y ∂μ.map f,
      (factorConditionalKernel μ f hf y).map (g • ·) = factorConditionalKernel μ f hf y := by
  have hg : Measurable (fun x : X => g • x) := measurable_const_smul g
  have hdis : factorGraphMeasure μ f hf = (factorGraphMeasure μ f hf).fst ⊗ₘ
      Kernel.map (factorConditionalKernel μ f hf) (g • ·) := by
    rw [factorGraphMeasure_fst μ f hf, Measure.compProd_map hg,
      factorConditionalKernel_disintegrate μ f hf, factorGraphMeasure_map_smul μ f hf hfi g]
  have h := eq_condKernel_of_measure_eq_compProd
    (Kernel.map (factorConditionalKernel μ f hf) (g • ·)) hdis
  rw [factorGraphMeasure_fst μ f hf] at h
  filter_upwards [h] with y hy
  simpa only [Kernel.map_apply _ hg, factorConditionalKernel] using hy

/-- A countable action has invariant conditional probabilities almost everywhere. -/
theorem factorConditionalKernel_invariant_ae [Countable G] [SMulInvariantMeasure G X μ]
    (hfi : ∀ (g : G) (s : Set Y), MeasurableSet s →
      ∀ x, f (g • x) ∈ s ↔ f x ∈ s) :
    ∀ᵐ y ∂μ.map f, SMulInvariantMeasure G X (factorConditionalKernel μ f hf y) := by
  have h := ae_all_iff.2 (factorConditionalKernel_map_smul_ae μ f hf hfi)
  filter_upwards [h] with y hy
  refine ⟨fun g s hs => ?_⟩
  rw [← Measure.map_apply (measurable_const_smul g) hs, hy g]

end PolycyclicRecognition

end

end OAI
