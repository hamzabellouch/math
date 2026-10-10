import OAI.InformationTheory.Entanglement.ProbeDensity

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix MeasureTheory ProbabilityTheory Filter Set
namespace SecretKey
open ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
lemma trace_mul_psd_eq_real {E W : Mat n} (hE : E.PosSemidef) (hW : W.PosSemidef) :
    Matrix.trace (E*W)=((Matrix.trace (E*W)).re : ℂ) := by
  apply Complex.ext
  · rfl
  rw [Complex.ofReal_im]
  rw [← trace_filter hE]
  exact (Complex.nonneg_iff.mp (hW.mul_mul_conjTranspose_same _).trace_nonneg).2.symm
variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
omit [DecidableEq n] in
lemma integrable_test_trace (E : Mat n) {W : T → Mat n}
    (hW : ∀ a b, Integrable (fun t => W t a b) μ) :
    Integrable (fun t => (Matrix.trace (E*W t)).re) μ := by
  have h : Integrable (fun t => Matrix.trace (E*W t)) μ := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hW b a).const_mul _
  exact h.re
omit [DecidableEq n] in
lemma measurable_test_trace (E : Mat n) {W : T → Mat n} (hW : Measurable W) :
    Measurable (fun t => (Matrix.trace (E*W t)).re) := by
  have hc : Continuous (fun M : Mat n => (Matrix.trace (E*M)).re) := by fun_prop
  exact hc.measurable.comp hW
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable {ν : Measure Ω} [IsFiniteMeasure ν] {t : Ω → T}

theorem probe_density_product (ht : Measurable t)
    {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hind : CondIndep (MeasurableSpace.comap t inferInstance) A B ht.comap_le ν)
    (a : Fin 2 → Option (PositiveTestIndex n) → Set Ω)
    (b : Fin 2 → Option (PositiveTestIndex m) → Set Ω)
    (ha : ∀ i e, MeasurableSet[A] (a i e)) (hb : ∀ j g, MeasurableSet[B] (b j g))
    (U : Fin 2 → T → Mat n) (V : Fin 2 → T → Mat m)
    (W : Fin 2 → Fin 2 → T → Mat (n×m))
    (hUp : ∀ i u, (U i u).PosSemidef) (hVp : ∀ j u, (V j u).PosSemidef)
    (hWp : ∀ i j u, (W i j u).PosSemidef)
    (hUm : ∀ i, Measurable (U i)) (hVm : ∀ j, Measurable (V j))
    (hWm : ∀ i j, Measurable (W i j))
    (hUi : ∀ i a b, Integrable (fun u => U i u a b) (@Measure.map Ω T mΩ _ t ν))
    (hVi : ∀ j a b, Integrable (fun u => V j u a b) (@Measure.map Ω T mΩ _ t ν))
    (hWi : ∀ i j a b, Integrable (fun u => W i j u a b) (@Measure.map Ω T mΩ _ t ν))
    (hUlaw : ∀ i e s, MeasurableSet s →
      (∫ u in s, (Matrix.trace (probePOVM e*U i u)).re ∂(@Measure.map Ω T mΩ _ t ν))=
        ν.real (a i e∩t⁻¹' s))
    (hVlaw : ∀ j g s, MeasurableSet s →
      (∫ u in s, (Matrix.trace (probePOVM g*V j u)).re ∂(@Measure.map Ω T mΩ _ t ν))=
        ν.real (b j g∩t⁻¹' s))
    (hWlaw : ∀ i j e g s, MeasurableSet s →
      (∫ u in s, (Matrix.trace ((probePOVM e ⊗ₖ probePOVM g)*W i j u)).re
        ∂(@Measure.map Ω T mΩ _ t ν))=ν.real ((a i e∩b j g)∩t⁻¹' s)) :
    ∀ᵐ u ∂(@Measure.map Ω T mΩ _ t ν), ∀ i j, W i j u=U i u ⊗ₖ V j u := by
  have he (i j : Fin 2) (e : Option (PositiveTestIndex n)) (g : Option (PositiveTestIndex m)) :
      (fun u => (Matrix.trace ((probePOVM e ⊗ₖ probePOVM g)*W i j u)).re)=ᵐ[(@Measure.map Ω T mΩ _ t ν)]
        (fun u => (Matrix.trace (probePOVM e*U i u)).re*(Matrix.trace (probePOVM g*V j u)).re) := by
    exact independent_transcript_densities ht hA hB hind (ha i e) (hb j g)
      (measurable_test_trace _ (hUm i)) (measurable_test_trace _ (hVm j))
      (measurable_test_trace _ (hWm i j))
      (integrable_test_trace _ (hUi i)) (integrable_test_trace _ (hVi j))
      (integrable_test_trace _ (hWi i j)) (hUlaw i e) (hVlaw j g) (hWlaw i j e g)
  have hall := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
    ae_all_iff.mpr (fun e => ae_all_iff.mpr (he i j e))))
  filter_upwards [hall] with u hu
  intro i j
  apply tensor_product_of_probePOVM
  intro e g
  rw [trace_mul_psd_eq_real ((probePOVM_psd e).kronecker (probePOVM_psd g)) (hWp i j u),
    trace_mul_psd_eq_real (probePOVM_psd e) (hUp i u),
    trace_mul_psd_eq_real (probePOVM_psd g) (hVp j u),← Complex.ofReal_mul,hu i j e g]

end SecretKey

end

end OAI
