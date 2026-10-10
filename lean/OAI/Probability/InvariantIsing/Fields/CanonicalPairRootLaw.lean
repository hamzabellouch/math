import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairFactorization
import OAI.Probability.InvariantIsing.Fields.SpinPairSubGaussian

namespace OAI

/-! Exact independent-site factorization at the biased shared root. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

def biasedFieldLevelSpinPair (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) : Measure (Bool × Bool) :=
  fieldPairSpinKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
    (Fin.cast (by rw [scalarFieldIncrements_length]) i) ∘ₘ
      gaussianReal b (NNReal.mk (h.height 0) (h.nonneg 0))

instance biasedFieldLevelSpinPair_probability (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) :
    IsProbabilityMeasure (biasedFieldLevelSpinPair h b i) := by
  unfold biasedFieldLevelSpinPair
  infer_instance

lemma biasedFieldLevelSpinPair_mean (h : FieldStep) (b : ℝ) (i : Fin (h.depth + 1)) :
    (∫ p, spinPairSiteValue p ∂biasedFieldLevelSpinPair h b i) = magneticLevelAtBias h b i := by
  unfold biasedFieldLevelSpinPair
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
  simp only [Kernel.const_apply, spinPairSiteValue, fieldPairSpinKernel_mean]
  simp only [magneticLevelAtBias, fieldSpinTransition, zero_mul, tilted_const]

lemma restrictedLevelSpinPair_univ {N : ℕ} (hN : 0 < N) (h : FieldStep)
    (b : Fin N → ℝ) (i : Fin (h.depth + 1)) :
    restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i =
      fieldVectorPairSpinKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
        (Fin.cast (by rw [scalarFieldIncrements_length]) i) ∘ₘ
          Measure.pi (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0))) := by
  unfold restrictedLevelSpinPair
  rw [restrictedPairSpinKernel_univ]
  have hB : ∀ j < h.depth, 0 < chainExponent h.cut j :=
    fun j hj => ((chainExponent_admissible h.ordered_cut h.first h.last).1 j hj).1
  have he := fieldVectorPairSpinKernel_transport N (fieldStepIncrements h)
    (finiteFieldIncrements_positive h.depth (chainExponent h.cut) (fieldStepVariance h) hB)
    (scalarFieldIncrements_positive h) (Fin.cast (by simp) i)
    (Fin.cast (by rw [scalarFieldIncrements_length]) i) rfl
  rw [he]

lemma canonicalLevelSpinPair_product {N : ℕ} (hN : 0 < N) (h : FieldStep)
    (b : Fin N → ℝ) (i : Fin (h.depth + 1)) :
    (restrictedLevelSpinPair hN Finset.univ Finset.univ_nonempty h b i).map
      (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm =
        Measure.pi (fun j => biasedFieldLevelSpinPair h (b j) i) := by
  rw [restrictedLevelSpinPair_univ, Measure.map_comp _ _
    (MeasurableEquiv.arrowProdEquivProdArrow Bool Bool (Fin N)).symm.measurable]
  exact product_kernel_comp_general
    (fieldPairSpinKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h) _)
    (fieldVectorSitePairKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h) _)
    (fieldVectorSitePairKernel_product N _ _ _)
    (fun j => gaussianReal (b j) (NNReal.mk (h.height 0) (h.nonneg 0)))

end InvariantIsing

end

end OAI
