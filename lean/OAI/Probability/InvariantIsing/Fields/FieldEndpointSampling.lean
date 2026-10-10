import OAI.Probability.InvariantIsing.Fields.FieldVectorPairSampling

namespace OAI

/-! Conditional Gaussian endpoint kernels before sampling the cavity spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_tanh_measurable : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp only [Real.tanh_eq]
  fun_prop

def fieldVectorTailEndpointKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel (Fin N → ℝ) (Fin N → ℝ)
  | [], _ => Kernel.id
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldVectorTailEndpointKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

instance fieldVectorTailEndpointKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    IsMarkovKernel (fieldVectorTailEndpointKernel N L hL) := by
  induction L with
  | nil => change IsMarkovKernel Kernel.id; infer_instance
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let _ := ih ht
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

lemma field_tanh_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f) :
    Integrable (fun x => Real.tanh (f x)) μ := by
  apply Integrable.of_bound (field_tanh_measurable.comp hf).aestronglyMeasurable 1
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using field_abs_tanh_le_one (f x)

theorem fieldVectorTailEndpointKernel_coordinate_mean (N : ℕ)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1)
    (z : Fin N → ℝ) (j : Fin N) :
    (∫ y, Real.tanh (y j) ∂fieldVectorTailEndpointKernel N L hL z) =
      fieldScalarMean L (fun u => Real.log (Real.cosh u)) Real.tanh (z j) := by
  induction L generalizing z with
  | nil =>
    simp only [fieldVectorTailEndpointKernel, Kernel.id_apply, integral_dirac, fieldScalarMean]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hmean := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      field_tanh_measurable field_abs_tanh_le_one
    change (∫ y, Real.tanh (y j) ∂(fieldVectorTailEndpointKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2
        (fieldScalarValue L (fun u => Real.log (Real.cosh u))) hreg.1) z) = _
    rw [Kernel.integral_comp (field_tanh_integrable _ _ (measurable_pi_apply j))]
    simp_rw [ih ht]
    exact fieldVectorTransitionKernel_coordinate av.1 av.2 _ hreg.1 hreg.2 _ hmean.1 z j

def fieldVectorPairEndpointKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Fin (L.length + 1) →
      Kernel (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))
  | [], _, _ => Kernel.id ×ₖ Kernel.id
  | av :: L, hL, i =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    Fin.cases (fieldVectorTailEndpointKernel N (av :: L) hL ×ₖ
        fieldVectorTailEndpointKernel N (av :: L) hL)
      (fun j => fieldVectorPairEndpointKernel N L ht j ∘ₖ
        fieldVectorTransitionKernel N av.1 av.2
          (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1) i

instance fieldVectorPairEndpointKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    IsMarkovKernel (fieldVectorPairEndpointKernel N L hL i) := by
  induction L with
  | nil => change IsMarkovKernel (Kernel.id ×ₖ Kernel.id); infer_instance
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change IsMarkovKernel (fieldVectorTailEndpointKernel N (av :: L) hL ×ₖ
        fieldVectorTailEndpointKernel N (av :: L) hL)
      infer_instance
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      let _ := ih ht j
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance

lemma field_tanh_pair_integrable (N : ℕ)
    (μ : Measure ((Fin N → ℝ) × (Fin N → ℝ))) [IsFiniteMeasure μ] (j : Fin N) :
    Integrable (fun p => Real.tanh (p.1 j) * Real.tanh (p.2 j)) μ := by
  apply Integrable.of_bound (by
    exact ((field_tanh_measurable.comp ((measurable_pi_apply j).comp measurable_fst)).mul
      (field_tanh_measurable.comp ((measurable_pi_apply j).comp measurable_snd))).aestronglyMeasurable) 1
  exact ae_of_all _ fun p => by
    simpa only [Real.norm_eq_abs, abs_mul, one_mul] using
      mul_le_mul (field_abs_tanh_le_one (p.1 j)) (field_abs_tanh_le_one (p.2 j))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem fieldVectorPairEndpointKernel_coordinate_mean (N : ℕ)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1)
    (i : Fin (L.length + 1)) (z : Fin N → ℝ) (j : Fin N) :
    (∫ y, Real.tanh (y.1 j) * Real.tanh (y.2 j)
      ∂fieldVectorPairEndpointKernel N L hL i z) =
      fieldScalarSquares L (fun u => Real.log (Real.cosh u)) Real.tanh i (z j) := by
  induction L generalizing z with
  | nil =>
    simp only [fieldVectorPairEndpointKernel, Kernel.prod_apply, Kernel.id_apply]
    rw [integral_prod_mul (fun y : Fin N → ℝ => Real.tanh (y j))
      (fun y : Fin N → ℝ => Real.tanh (y j))]
    simp only [integral_dirac, fieldScalarSquares, pow_two]
  | cons av L ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · change (∫ y, Real.tanh (y.1 j) * Real.tanh (y.2 j)
        ∂(fieldVectorTailEndpointKernel N (av :: L) hL ×ₖ
          fieldVectorTailEndpointKernel N (av :: L) hL) z) = _
      rw [Kernel.prod_apply, integral_prod_mul (fun y : Fin N → ℝ => Real.tanh (y j))
        (fun y : Fin N → ℝ => Real.tanh (y j)),
        fieldVectorTailEndpointKernel_coordinate_mean, fieldScalarSquares_zero, pow_two]
    · have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
      have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
      have hsq := fieldScalarSquares_regular L ht measurable_logCosh logCosh_linearGrowth
        field_tanh_measurable field_abs_tanh_le_one k
      change (∫ y, Real.tanh (y.1 j) * Real.tanh (y.2 j)
        ∂(fieldVectorPairEndpointKernel N L ht k ∘ₖ
          fieldVectorTransitionKernel N av.1 av.2
            (fieldScalarValue L (fun u => Real.log (Real.cosh u))) hreg.1) z) = _
      rw [Kernel.integral_comp (field_tanh_pair_integrable N _ j)]
      simp_rw [ih ht]
      exact fieldVectorTransitionKernel_coordinate av.1 av.2 _ hreg.1 hreg.2 _ hsq.1 z j

end InvariantIsing

end

end OAI
