import OAI.Probability.InvariantIsing.Fields.FieldSpinSampling
import OAI.Probability.InvariantIsing.Fields.FieldMagnetization

namespace OAI

/-! Common-prefix sampling of two scalar Ising spins. After the split
the two tails are independent; before the split they use the same actual
tilted Gaussian transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldPairSpinKernel : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Fin (L.length + 1) → Kernel ℝ (Bool × Bool)
  | [], _, _ => scalarSpinKernel ×ₖ scalarSpinKernel
  | av :: L, hL, i =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    Fin.cases (fieldTailSpinKernel (av :: L) hL ×ₖ fieldTailSpinKernel (av :: L) hL)
      (fun j => fieldPairSpinKernel L ht j ∘ₖ
        fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          hreg.1) i

instance fieldPairSpinKernel_markov (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldPairSpinKernel L hL i) := by
  induction L with
  | nil => change IsMarkovKernel (scalarSpinKernel ×ₖ scalarSpinKernel); infer_instance
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (fieldTailSpinKernel (av :: L) hL ×ₖ
        fieldTailSpinKernel (av :: L) hL)
      infer_instance
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      let _ := ih ht j
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance

theorem fieldPairSpinKernel_mean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) (z : ℝ) :
    (∫ σ, spinValue σ.1 * spinValue σ.2 ∂fieldPairSpinKernel L hL i z) =
      fieldScalarSquares L (fun u => Real.log (Real.cosh u)) Real.tanh i z := by
  induction L generalizing z with
  | nil =>
    simp only [fieldPairSpinKernel, Kernel.prod_apply, integral_prod_mul,
      scalarSpinKernel_mean, fieldScalarSquares, pow_two]
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∫ σ, spinValue σ.1 * spinValue σ.2
        ∂(fieldTailSpinKernel (av :: L) hL ×ₖ fieldTailSpinKernel (av :: L) hL) z) = _
      rw [Kernel.prod_apply, integral_prod_mul, fieldTailSpinKernel_mean]
      rw [fieldScalarSquares_zero, pow_two]
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      change (∫ σ, spinValue σ.1 * spinValue σ.2
        ∂(fieldPairSpinKernel L ht j ∘ₖ
          fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun u => Real.log (Real.cosh u)))
            hreg.1) z) = _
      rw [Kernel.integral_comp (Integrable.of_finite)]
      simp_rw [ih ht]
      exact fieldTransitionKernel_integral av.1 av.2 _ hreg.1 hreg.2 _ z

/-- The field's root is shared by the two replicas. -/
def fieldLevelSpinPair (h : FieldStep) (i : Fin (h.depth + 1)) : Measure (Bool × Bool) :=
  fieldPairSpinKernel (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
    (Fin.cast (by rw [scalarFieldIncrements_length]) i) ∘ₘ
      gaussianReal 0 (NNReal.mk (h.height 0) (h.nonneg 0))

instance fieldLevelSpinPair_probability (h : FieldStep) (i : Fin (h.depth + 1)) :
    IsProbabilityMeasure (fieldLevelSpinPair h i) := by
  unfold fieldLevelSpinPair
  infer_instance

theorem fieldLevelSpinPair_mean (h : FieldStep) (i : Fin (h.depth + 1)) :
    (∫ σ, spinValue σ.1 * spinValue σ.2 ∂fieldLevelSpinPair h i) =
      fieldMagnetizationLevel h i := by
  unfold fieldLevelSpinPair
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
  simp only [Kernel.const_apply, fieldPairSpinKernel_mean]
  rfl

/-- The common-level spin test in the evaluated cavity law. -/
theorem fieldLevelSpinPair_test (h : FieldStep) (q : OverlapPath) (Φ : ℝ → ℝ) :
    (∫ s, ∫ σ, Φ (q s) * (spinValue σ.1 * spinValue σ.2)
      ∂fieldLevelSpinPair h (fieldLevelIndex h s) ∂pathMeasure) =
      ∫ s, Φ (q s) * fieldMagnetizationPath h s ∂pathMeasure := by
  apply integral_congr_ae
  filter_upwards [] with s
  rw [integral_const_mul, fieldLevelSpinPair_mean]
  rfl

/-- Sampling the spin pair leaves every common-level observable unchanged. -/
theorem fieldLevelSpinPair_level_test (h : FieldStep) (q : OverlapPath) (Φ : ℝ → ℝ) :
    (∫ s, ∫ _σ, Φ (q s) ∂fieldLevelSpinPair h (fieldLevelIndex h s) ∂pathMeasure) =
      ∫ s, Φ (q s) ∂pathMeasure := by
  simp only [integral_const, probReal_univ, one_smul]

end InvariantIsing

end

end OAI
