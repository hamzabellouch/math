import OAI.InformationTheory.Entanglement.TestedQuantumConsumer
import OAI.InformationTheory.Entanglement.PurificationExpansion

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder MatrixOrder Kronecker
open MeasureTheory Matrix ContinuousLinearMap ProbabilityTheory Filter
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem arbitrary_purification_tested_gap
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
    (hW : ∀ i j s, MeasurableSet s → (W i j).value s=hilbertEmbed x ((M i j).value s))
    (hW1 : (∑ i, ∑ j, hilbertTrace b ((W i j).value Set.univ))=1)
    (σ : PositiveHilbertMeasure T H b) (hσ1 : σ.traceMeasure Set.univ=1) :
    ENNReal.ofReal (1/5) ≤ hilbertCQDistance b W σ := by
  obtain ⟨d,v,Z,hv,hx,hg⟩ := purification_orthonormal_expansion x
  have hGram : Zᴴ*Z=Rᵀ := by ext i j; rw [hg,hxGram]
  have hd : 0<d := by
    by_contra hn
    have hz : d=0 := Nat.eq_zero_of_not_pos hn
    subst d
    have hzero : Zᴴ*Z=0 := by ext i j; simp [Matrix.mul_apply]
    have ht := congrArg Matrix.trace hGram
    rw [hzero,Matrix.trace_zero,Matrix.trace_transpose,hR.2.1] at ht
    exact zero_ne_one ht
  let j₀ : Fin d := ⟨0,hd⟩
  let V := fun i j => ((M i j).filter Z).hilbertEmbedding b v hv
  have hValues i j s (hs : MeasurableSet s) : (W i j).value s=(V i j).value s := by
    rw [hW i j s hs]
    change hilbertEmbed x ((M i j).value s)=
      hilbertEmbed v (((M i j).filter Z).value s)
    rw [PositiveMatrixMeasure.filter_value]
    rw [← hilbertEmbed_congruence]
    congr 1
    funext j
    exact (hx j).symm
  have hnorm : (∑ i, ∑ j, (Matrix.trace (((M i j).filter Z).value Set.univ)).re)=1 := by
    rw [← hW1]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    rw [hValues i j Set.univ MeasurableSet.univ]
    exact (hilbertEmbed_trace b v hv _).symm
  have hgap := independent_tested_quantum_gap ν t ht hA hB hind a q ha hq M hdom
    hleft hright hjoint b R hR i₀ v hv j₀ Z hGram hnorm σ hσ1
  have he : hilbertCQDistance b W σ=hilbertCQDistance b V σ := by
    unfold hilbertCQDistance
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    unfold hilbertVariation
    apply iSup_congr; intro P
    apply iSup_congr; intro hP
    apply iSup_congr; intro hpd
    apply Finset.sum_congr rfl; intro s hs
    exact congrArg (fun D => hilbertENorm b (D-hilbertIdeal σ.value i j s))
      (hValues i j s (hP s hs))
  rw [he]
  exact hgap

end SecretKey

end

end OAI
