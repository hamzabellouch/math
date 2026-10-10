import OAI.InformationTheory.Entanglement.ArbitraryPurificationConsumer
import OAI.InformationTheory.Entanglement.ProbeRescaling

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal MeasureTheory InnerProductSpace ComplexOrder MatrixOrder Kronecker
open MeasureTheory Matrix ContinuousLinearMap ProbabilityTheory Filter
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
omit [DecidableEq n] in
lemma hilbertEmbed_smul_vectors {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (x : n→H) (d : ℂ) (A : Mat n) :
    hilbertEmbed (fun i => d • x i) A=hilbertEmbed x ((d*star d) • A) := by
  ext u
  rw [hilbertEmbed_apply,hilbertEmbed_apply]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  simp only [inner_smul_left,smul_smul,Matrix.smul_apply,smul_eq_mul]
  congr 1
  simp only [starRingEnd_apply]
  ring
omit [DecidableEq n] in
lemma hilbertEmbed_normalized_filter {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (x : n→H) (A : Mat n) :
    hilbertEmbed (fun i => (Real.sqrt (Fintype.card n : ℝ) : ℂ) • x i) A=
      hilbertEmbed x ((Fintype.card n : ℂ) • A) := by
  rw [hilbertEmbed_smul_vectors,Complex.star_def,Complex.conj_ofReal,
    FiniteInputInstrument.sqrt_card_mul]

theorem normalized_purification_tested_gap
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
    (R : Mat (n×m)) (hR : Represented R) (i₀ : n×m)
    (x : (n×m)→H) (hxGram : ∀ i j, inner ℂ (x i) (x j)=Rᵀ i j)
    (W : Fin 2→Fin 2→PositiveHilbertMeasure T H b)
    (hW : ∀ i j s, MeasurableSet s → (W i j).value s=
      hilbertEmbed (fun k => (Real.sqrt ((Fintype.card n : ℝ)*Fintype.card m) : ℂ) • x k)
        ((M i j).value s))
    (hW1 : (∑ i, ∑ j, hilbertTrace b ((W i j).value Set.univ))=1)
    (σ : PositiveHilbertMeasure T H b) (hσ1 : σ.traceMeasure Set.univ=1) :
    ENNReal.ofReal (1/5) ≤ hilbertCQDistance b W σ := by
  let c : ℝ≥0 := Fintype.card (n×m)
  let N := fun i j => (M i j).scale (c : ℝ) (NNReal.coe_nonneg c)
  apply arbitrary_purification_tested_gap (c•ν) t ht hA hB
    (condIndep_rescale ht.comap_le hA hB hind c) a q ha hq N
    ?_ ?_ ?_ ?_ b R hR i₀ x hxGram W ?_ hW1 σ hσ1
  · intro i j
    rw [Measure.map_smul c ht.aemeasurable]
    exact (M i j).scale_domination (hdom i j) c
  · intro i r s hs
    simp only [N,PositiveMatrixMeasure.scale_born,← Finset.mul_sum,
      hleft i r s hs,measureReal_nnreal_smul_apply]
  · intro j g s hs
    simp only [N,PositiveMatrixMeasure.scale_born,← Finset.mul_sum,
      hright j g s hs,measureReal_nnreal_smul_apply]
  · intro i j r g s hs
    simp only [N,PositiveMatrixMeasure.scale_born,hjoint i j r g s hs,
      measureReal_nnreal_smul_apply]
  · intro i j s hs
    rw [hW i j s hs]
    have he : (Real.sqrt ((Fintype.card n : ℝ)*Fintype.card m) : ℂ)=
        (Real.sqrt (Fintype.card (n×m) : ℝ) : ℂ) := by
      simp only [Fintype.card_prod,Nat.cast_mul]
    rw [he,hilbertEmbed_normalized_filter]
    rfl

end SecretKey

end

end OAI
