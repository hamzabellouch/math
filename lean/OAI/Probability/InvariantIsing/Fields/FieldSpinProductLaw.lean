import OAI.Probability.InvariantIsing.Core.ProductKernelSampling

namespace OAI

/-! Exact product law of the canonical terminal spins after all Gaussian
transitions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem fieldVectorTailSpinKernel_product (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : Fin N → ℝ) :
    fieldVectorTailSpinKernel N L hL z = Measure.pi (fun i => fieldTailSpinKernel L hL (z i)) := by
  induction L generalizing z with
  | nil => exact fieldSpinGibbs_eq_product z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    change (fieldVectorTailSpinKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2 _ hreg.1) z = _
    rw [Kernel.comp_apply]
    change fieldVectorTailSpinKernel N L ht ∘ₘ
      Measure.pi (fun i => fieldTransitionKernel av.1 av.2 _ hreg.1 (z i)) = _
    rw [product_kernel_comp_general (fieldTailSpinKernel L ht)
      (fieldVectorTailSpinKernel N L ht) (ih ht)]
    rfl

lemma paired_product_reorder {X : Type*} [MeasurableSpace X] (N : ℕ)
    (ν : Fin N → Measure X) [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.pi ν).prod (Measure.pi ν)).map
      (MeasurableEquiv.arrowProdEquivProdArrow X X (Fin N)).symm =
        Measure.pi (fun i => (ν i).prod (ν i)) :=
  (measurePreserving_arrowProdEquivProdArrow X X (Fin N) ν ν).symm.map_eq

end InvariantIsing

end

end OAI
