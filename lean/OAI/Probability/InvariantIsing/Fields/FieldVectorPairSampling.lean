import OAI.Probability.InvariantIsing.Fields.FieldVectorSampling
import OAI.Probability.InvariantIsing.Fields.FieldScalarSampling
import OAI.Probability.InvariantIsing.Fields.FieldCommonDepthLaw

namespace OAI

/-! Evaluation of the common-prefix vector Ising spin pair law, with the
actual cascade depth distribution and its independent root Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldVectorPairSpinKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Fin (L.length + 1) → Kernel (Fin N → ℝ) (Spin N × Spin N)
  | [], _, _ => fieldVectorSpinKernel N ×ₖ fieldVectorSpinKernel N
  | av :: L, hL, i =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    Fin.cases (fieldVectorTailSpinKernel N (av :: L) hL ×ₖ
        fieldVectorTailSpinKernel N (av :: L) hL)
      (fun j => fieldVectorPairSpinKernel N L ht j ∘ₖ
        fieldVectorTransitionKernel N av.1 av.2
          (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1) i

instance fieldVectorPairSpinKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldVectorPairSpinKernel N L hL i) := by
  induction L with
  | nil => change IsMarkovKernel (fieldVectorSpinKernel N ×ₖ fieldVectorSpinKernel N); infer_instance
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (fieldVectorTailSpinKernel N (av :: L) hL ×ₖ
        fieldVectorTailSpinKernel N (av :: L) hL)
      infer_instance
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      let _ := ih ht j
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance

theorem fieldVectorPairSpinKernel_coordinate_mean (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) (z : Fin N → ℝ) (j : Fin N) :
    (∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j) ∂fieldVectorPairSpinKernel N L hL i z) =
      fieldScalarSquares L (fun u => Real.log (Real.cosh u)) Real.tanh i (z j) := by
  induction L generalizing z with
  | nil =>
    change (∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j)
      ∂(fieldVectorSpinKernel N ×ₖ fieldVectorSpinKernel N) z) = _
    rw [Kernel.prod_apply, integral_prod_mul (fun σ : Spin N => spinValue (σ j))
      (fun σ : Spin N => spinValue (σ j))]
    change (∫ σ, spinValue (σ j) ∂gibbsProbability
      (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z)) *
      (∫ σ, spinValue (σ j) ∂gibbsProbability
        (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z)) = _
    rw [fieldSpinGibbs_coordinate_mean]
    simp [fieldScalarSquares, pow_two]
  | cons av L ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · change (∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j)
        ∂(fieldVectorTailSpinKernel N (av :: L) hL ×ₖ
          fieldVectorTailSpinKernel N (av :: L) hL) z) = _
      rw [Kernel.prod_apply, integral_prod_mul (fun σ : Spin N => spinValue (σ j))
        (fun σ : Spin N => spinValue (σ j)),
        fieldVectorTailSpinKernel_coordinate_mean,
        fieldScalarSquares_zero, pow_two]
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      have hsq := fieldScalarSquares_regular L ht measurable_logCosh logCosh_linearGrowth
        (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
        field_abs_tanh_le_one k
      change (∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j)
        ∂(fieldVectorPairSpinKernel N L ht k ∘ₖ
          fieldVectorTransitionKernel N av.1 av.2
            (fieldScalarValue L (fun u => Real.log (Real.cosh u))) hreg.1) z) = _
      rw [Kernel.integral_comp (Integrable.of_finite)]
      simp_rw [ih ht]
      exact fieldVectorTransitionKernel_coordinate av.1 av.2 _ hreg.1 hreg.2 _ hsq.1 z j

def fieldVectorLevelSpinPair (N : ℕ) (h : FieldStep) (i : Fin (h.depth + 1)) :
    Measure (Spin N × Spin N) :=
  fieldVectorPairSpinKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
    (Fin.cast (by rw [scalarFieldIncrements_length]) i) ∘ₘ
      (vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure (Fin N → ℝ))

instance fieldVectorLevelSpinPair_probability (N : ℕ) (h : FieldStep) (i : Fin (h.depth + 1)) :
    IsProbabilityMeasure (fieldVectorLevelSpinPair N h i) := by
  unfold fieldVectorLevelSpinPair
  infer_instance

theorem fieldVectorLevelSpinPair_coordinate_mean (N : ℕ) (h : FieldStep)
    (i : Fin (h.depth + 1)) (j : Fin N) :
    (∫ σ, spinValue (σ.1 j) * spinValue (σ.2 j) ∂fieldVectorLevelSpinPair N h i) =
      fieldMagnetizationLevel h i := by
  unfold fieldVectorLevelSpinPair
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (Integrable.of_finite)]
  simp only [Kernel.const_apply, fieldVectorPairSpinKernel_coordinate_mean]
  let i' : Fin ((scalarFieldIncrements h).length + 1) :=
    Fin.cast (by rw [scalarFieldIncrements_length]) i
  have hs := fieldScalarSquares_regular (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h) measurable_logCosh logCosh_linearGrowth
    (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
    field_abs_tanh_le_one i'
  change (∫ z : Fin N → ℝ,
    fieldScalarSquares (scalarFieldIncrements h) (fun u => Real.log (Real.cosh u)) Real.tanh i'
      (z j) ∂Measure.pi (fun _ => gaussianReal 0 (NNReal.mk (h.height 0) (h.nonneg 0)))) = _
  rw [integral_comp_eval hs.1.aestronglyMeasurable]
  rfl

theorem fieldVectorLevelSpinPair_cascade_test (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    (∫ α, ∫ σ, Φ (q (fieldCommonLevel h α)) * (spinValue (σ.1 j) * spinValue (σ.2 j))
      ∂fieldVectorLevelSpinPair N h (fieldCommonLevel h α)
      ∂cascadeReplicaLaw h.depth (chainExponent h.cut)) =
      ∫ s, Φ (q (fieldLevelIndex h s)) * fieldMagnetizationPath h s ∂pathMeasure := by
  simp_rw [integral_const_mul, fieldVectorLevelSpinPair_coordinate_mean]
  rw [fieldCommonLevel_integral h (fun i => Φ (q i) * fieldMagnetizationLevel h i)]
  rfl

theorem fieldVectorLevelSpinPair_centered_test (N : ℕ) (h : FieldStep)
    (q : Fin (h.depth + 1) → ℝ) (Φ : ℝ → ℝ) (j : Fin N) :
    (∫ α, ∫ σ, Φ (q (fieldCommonLevel h α)) *
        (spinValue (σ.1 j) * spinValue (σ.2 j) - q (fieldCommonLevel h α))
      ∂fieldVectorLevelSpinPair N h (fieldCommonLevel h α)
      ∂cascadeReplicaLaw h.depth (chainExponent h.cut)) =
      ∫ s, Φ (q (fieldLevelIndex h s)) *
        (fieldMagnetizationPath h s - q (fieldLevelIndex h s)) ∂pathMeasure := by
  simp_rw [integral_const_mul,
    integral_sub Integrable.of_finite (integrable_const _),
    fieldVectorLevelSpinPair_coordinate_mean, integral_const, probReal_univ, one_smul]
  rw [fieldCommonLevel_integral h (fun i => Φ (q i) * (fieldMagnetizationLevel h i - q i))]
  rfl

end InvariantIsing

end

end OAI
