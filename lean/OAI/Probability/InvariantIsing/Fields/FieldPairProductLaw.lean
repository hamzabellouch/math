import OAI.Probability.InvariantIsing.Fields.FieldSpinProductLaw

namespace OAI

/-! Independence across sites of the full common-prefix two-spin law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldVectorSitePairKernel (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    Kernel (Fin N → ℝ) (Fin N → Bool × Bool) :=
  (fieldVectorPairSpinKernel N L hL i).map
    (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm

instance fieldVectorSitePairKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldVectorSitePairKernel N L hL i) := by
  unfold fieldVectorSitePairKernel
  exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable

theorem fieldVectorSitePairKernel_product (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) (z : Fin N → ℝ) :
    fieldVectorSitePairKernel N L hL i z = Measure.pi (fun j => fieldPairSpinKernel L hL i (z j)) := by
  induction L generalizing z with
  | nil =>
    rw [fieldVectorSitePairKernel, Kernel.map_apply _
      (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable]
    change ((fieldVectorSpinKernel N ×ₖ fieldVectorSpinKernel N) z).map _ = _
    rw [Kernel.prod_apply]
    change ((gibbsProbability _ (fieldEnergy z)).prod (gibbsProbability _ (fieldEnergy z))).map _ = _
    rw [fieldSpinGibbs_eq_product, paired_product_reorder]
    simp only [fieldPairSpinKernel, Kernel.prod_apply]
  | cons av L ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [fieldVectorSitePairKernel, Kernel.map_apply _
        (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable]
      change ((fieldVectorTailSpinKernel N (av :: L) hL ×ₖ
        fieldVectorTailSpinKernel N (av :: L) hL) z).map _ = _
      rw [Kernel.prod_apply, fieldVectorTailSpinKernel_product, paired_product_reorder]
      simp only [fieldPairSpinKernel, Fin.cases_zero, Kernel.prod_apply]
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      change ((fieldVectorPairSpinKernel N L ht k ∘ₖ
        fieldVectorTransitionKernel N av.1 av.2 _ hreg.1).map
        (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm) z = _
      rw [Kernel.map_comp, Kernel.comp_apply]
      change fieldVectorSitePairKernel N L ht k ∘ₘ
        Measure.pi (fun j => fieldTransitionKernel av.1 av.2 _ hreg.1 (z j)) = _
      rw [product_kernel_comp_general (fieldPairSpinKernel L ht k)
        (fieldVectorSitePairKernel N L ht k) (ih ht k)]
      rfl

end InvariantIsing

end

end OAI
