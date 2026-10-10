import OAI.InformationTheory.Entanglement.FullQuantumConsumer
import OAI.InformationTheory.Entanglement.ProbeFactorization

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder MatrixOrder Kronecker
open scoped Matrix.Norms.L2Operator
open MeasureTheory Matrix ContinuousLinearMap ProbabilityTheory Filter
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
namespace PositiveMatrixMeasure
omit [DecidableEq n] in
lemma density_test_setIntegral (M : PositiveMatrixMeasure T n) {μ : Measure T}
    [IsFiniteMeasure μ] (hdom : M.traceMeasure ≪ μ) (E : Mat n)
    {s : Set T} (hs : MeasurableSet s) :
    (∫ t in s, (Matrix.trace (E*M.positiveDensity μ t)).re ∂μ)=
      (Matrix.trace (E*M.value s)).re := by
  apply integral_trace_of_entry_integrals
  · intro a c
    simp only [Matrix.mul_apply]
    exact (integrable_finsetSum _ fun k _ =>
      (M.positiveDensity_integrable hdom k c).const_mul (E a k)).integrableOn
  · intro a c
    simp only [Matrix.mul_apply]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul,M.positiveDensity_setIntegral hdom hs]
    · intro k hk
      exact ((M.positiveDensity_integrable hdom k c).const_mul (E a k)).integrableOn
end PositiveMatrixMeasure

theorem independent_tested_quantum_gap
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (t : Ω→T) (ht : Measurable t)
    {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hind : CondIndep (MeasurableSpace.comap t inferInstance) A B ht.comap_le ν)
    (a : Fin 2→Option (PositiveTestIndex n)→Set Ω)
    (q : Fin 2→Option (PositiveTestIndex m)→Set Ω)
    (ha : ∀ i r, MeasurableSet[A] (a i r)) (hq : ∀ j s, MeasurableSet[B] (q j s))
    (M : Fin 2→Fin 2→PositiveMatrixMeasure T (n×m))
    (hdom : ∀ i j, (M i j).traceMeasure ≪ (@Measure.map Ω T mΩ _ t ν))
    (hleft : ∀ i r s, MeasurableSet s →
      (∑ j, (Matrix.trace ((probePOVM r ⊗ₖ (1 : Mat m))*(M i j).value s)).re)=
        ν.real (a i r∩t⁻¹' s))
    (hright : ∀ j g s, MeasurableSet s →
      (∑ i, (Matrix.trace (((1 : Mat n) ⊗ₖ probePOVM g)*(M i j).value s)).re)=
        ν.real (q j g∩t⁻¹' s))
    (hjoint : ∀ i j r g s, MeasurableSet s →
      (Matrix.trace ((probePOVM r ⊗ₖ probePOVM g)*(M i j).value s)).re=
        ν.real ((a i r∩q j g)∩t⁻¹' s))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    {e : Type} [Fintype e] [DecidableEq e]
    (R : Mat (n×m)) (hR : Represented R) (i₀ : n×m)
    (v : e→H) (hv : Orthonormal ℂ v) (j₀ : e) (Z : Matrix e (n×m) ℂ)
    (hGram : Zᴴ*Z=Rᵀ)
    (hW1 : (∑ i, ∑ j, (Matrix.trace (((M i j).filter Z).value Set.univ)).re)=1)
    (σ : PositiveHilbertMeasure T H b) (hσ1 : σ.traceMeasure Set.univ=1) :
    ENNReal.ofReal (1/5) ≤ hilbertCQDistance b
      (fun i j => ((M i j).filter Z).hilbertEmbedding b v hv) σ := by
  let μ := (@Measure.map Ω T mΩ _ t ν)
  let D := fun i j => (M i j).positiveDensity μ
  let U : Fin 2→T→Mat n := fun i u => ∑ j, marginalLeft (D i j u)
  let V : Fin 2→T→Mat m := fun j u => ∑ i, marginalRight (D i j u)
  have hDi i j c d : Integrable (fun u => D i j u c d) μ :=
    (M i j).positiveDensity_integrable (hdom i j) c d
  have hDm i j : Measurable (D i j) := (M i j).positiveDensity_measurable μ
  have hDp i j u : (D i j u).PosSemidef := (M i j).positiveDensity_psd μ u
  have hUp i u : (U i u).PosSemidef :=
    Matrix.posSemidef_sum _ fun j _ => marginalLeft_psd (hDp i j u)
  have hVp j u : (V j u).PosSemidef :=
    Matrix.posSemidef_sum _ fun i _ => marginalRight_psd (hDp i j u)
  have hUm i : Measurable (U i) := by
    have hc : Continuous (marginalLeft : Mat (n×m)→Mat n) := by
      unfold marginalLeft; fun_prop
    exact Finset.measurable_sum _ fun j _ => hc.measurable.comp (hDm i j)
  have hVm j : Measurable (V j) := by
    have hc : Continuous (marginalRight : Mat (n×m)→Mat m) := by
      unfold marginalRight; fun_prop
    exact Finset.measurable_sum _ fun i _ => hc.measurable.comp (hDm i j)
  have hUi i c d : Integrable (fun u => U i u c d) μ := by
    simp only [U,Matrix.sum_apply,marginalLeft]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hDi i j (c,k) (d,k)
  have hVi j c d : Integrable (fun u => V j u c d) μ := by
    simp only [V,Matrix.sum_apply,marginalRight]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hDi i j (k,c) (k,d)
  have hUlaw i r s (hs : MeasurableSet s) :
      (∫ u in s, (Matrix.trace (probePOVM r*U i u)).re ∂μ)=ν.real (a i r∩t⁻¹' s) := by
    simp only [U,Matrix.mul_sum,Matrix.trace_sum,trace_test_left,Complex.re_sum]
    rw [integral_finsetSum]
    · rw [← hleft i r s hs]
      apply Finset.sum_congr rfl; intro j hj
      exact (M i j).density_test_setIntegral (hdom i j) _ hs
    · intro j hj
      exact (integrable_test_trace _ (hDi i j)).integrableOn
  have hVlaw j g s (hs : MeasurableSet s) :
      (∫ u in s, (Matrix.trace (probePOVM g*V j u)).re ∂μ)=ν.real (q j g∩t⁻¹' s) := by
    simp only [V,Matrix.mul_sum,Matrix.trace_sum,trace_test_right,Complex.re_sum]
    rw [integral_finsetSum]
    · rw [← hright j g s hs]
      apply Finset.sum_congr rfl; intro i hi
      exact (M i j).density_test_setIntegral (hdom i j) _ hs
    · intro i hi
      exact (integrable_test_trace _ (hDi i j)).integrableOn
  have hWlaw i j r g s (hs : MeasurableSet s) :
      (∫ u in s, (Matrix.trace ((probePOVM r ⊗ₖ probePOVM g)*D i j u)).re ∂μ)=
        ν.real ((a i r∩q j g)∩t⁻¹' s) := by
    rw [(M i j).density_test_setIntegral (hdom i j) _ hs]
    exact hjoint i j r g s hs
  have hp := probe_density_product ht hA hB hind a q ha hq U V D hUp hVp hDp
    hUm hVm hDm hUi hVi hDi hUlaw hVlaw hWlaw
  let X := fun i u => (U i u)ᵀ
  let Y := fun j u => (V j u)ᵀ
  have he i j u : (X i u ⊗ₖ Y j u)ᵀ=U i u ⊗ₖ V j u := rfl
  apply full_quantum_factorized_gap b R hR i₀ v hv j₀ Z hGram M μ X Y
  · intro i
    have hc : Continuous (Matrix.transpose : Mat n→Mat n) := by fun_prop
    exact hc.measurable.comp (hUm i)
  · intro j
    have hc : Continuous (Matrix.transpose : Mat m→Mat m) := by fun_prop
    exact hc.measurable.comp (hVm j)
  · intro i u; exact (hUp i u).transpose
  · intro j u; exact (hVp j u).transpose
  · intro i j c d
    apply (hDi i j c d).congr
    filter_upwards [hp] with u hu
    rw [he,hu i j]
  · intro i j s hs c d
    calc
      _=∫ u in s, D i j u c d ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hp] with u hu
        rw [he,hu i j]
      _=(M i j).value s c d := (M i j).positiveDensity_setIntegral (hdom i j) hs c d
  · exact hW1
  · exact hσ1

end SecretKey

end

end OAI
