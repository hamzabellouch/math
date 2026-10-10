import OAI.InformationTheory.Entanglement.HilbertLawRecovery
import OAI.InformationTheory.Entanglement.HilbertLawFinite
import OAI.InformationTheory.Entanglement.FactorizedLawGap

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder MatrixOrder Kronecker
open MeasureTheory Matrix ContinuousLinearMap
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n m e : Type} [Fintype n] [Fintype m] [Fintype e]
  [DecidableEq n] [DecidableEq m] [DecidableEq e]
lemma canonical_filter_eveBlock (R : Mat (n×m)) (hR : R.PosSemidef) (D : Mat (n×m)) :
    CFC.sqrt Rᵀ*Dᵀ*(CFC.sqrt Rᵀ)ᴴ=eveBlock R D := by
  rw [sqrt_transpose hR,conjugate_transpose_transpose,sqrt_herm]
  simp only [eveBlock,Matrix.transpose_mul,Matrix.mul_assoc]

theorem full_quantum_factorized_gap (b : HilbertBasis ι ℂ H)
    (R : Mat (n×m)) (hR : Represented R) (i₀ : n×m)
    (v : e→H) (hv : Orthonormal ℂ v) (j₀ : e) (B : Matrix e (n×m) ℂ)
    (hGram : Bᴴ*B=Rᵀ)
    (M : Fin 2 → Fin 2 → PositiveMatrixMeasure T (n×m))
    (μ : Measure T) [IsFiniteMeasure μ]
    (X : Fin 2 → T → Mat n) (Y : Fin 2 → T → Mat m)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ j, Measurable (Y j))
    (hXp : ∀ i t, (X i t).PosSemidef) (hYp : ∀ j t, (Y j t).PosSemidef)
    (hMi : ∀ i j a c, Integrable (fun t => ((X i t ⊗ₖ Y j t)ᵀ) a c) μ)
    (hMs : ∀ i j s, MeasurableSet s → ∀ a c,
      (∫ t in s, ((X i t ⊗ₖ Y j t)ᵀ) a c ∂μ)=(M i j).value s a c)
    (hW1 : (∑ i, ∑ j, (Matrix.trace (((M i j).filter B).value Set.univ)).re)=1)
    (σ : PositiveHilbertMeasure T H b) (hσ1 : σ.traceMeasure Set.univ=1) :
    ENNReal.ofReal (1/5) ≤ hilbertCQDistance b
      (fun i j => ((M i j).filter B).hilbertEmbedding b v hv) σ := by
  obtain ⟨F,hF,hTP,hrec,hcontract⟩ := hilbert_purification_law_recovery (T := T) b v hv j₀ i₀ B
  let W := fun i j => (M i j).filter (CFC.sqrt (Bᴴ*B))
  let σ' := (σ.erase v hv j₀).channel F hF
  have hWPs (i j : Fin 2) : ((M i j).filter B).channel F hF=W i j := by
    simpa only [PositiveMatrixMeasure.hilbertEmbedding_recovered] using hrec (M i j)
  have hWnorm : (∑ i, ∑ j, (Matrix.trace ((W i j).value Set.univ)).re)=1 := by
    calc
      _ = ∑ i, ∑ j, (Matrix.trace ((((M i j).filter B).channel F hF).value Set.univ)).re := by
        simp only [hWPs]
      _ = 1 := by simpa only [PositiveMatrixMeasure.channel_value,show ∀ A, Matrix.trace (F A)=Matrix.trace A from hTP] using hW1
  have hσnorm : (Matrix.trace (σ'.value Set.univ)).re=1 := by
    rw [← PositiveMatrixMeasure.traceMeasure_real _ MeasurableSet.univ]
    change (((σ.erase v hv j₀).channel F hF).traceMeasure Set.univ).toReal=1
    rw [PositiveMatrixMeasure.channel_traceMeasure _ F hF hTP,
      PositiveHilbertMeasure.erase_traceMeasure,hσ1]
    norm_num
  have hp := hR.1
  have hdiag (i j t) : CFC.sqrt (Bᴴ*B)*(X i t ⊗ₖ Y j t)ᵀ*(CFC.sqrt (Bᴴ*B))ᴴ=
      eveBlock R (X i t ⊗ₖ Y j t) := by
    rw [hGram]
    exact canonical_filter_eveBlock R hp _
  have hg : 1/5 ≤ cqBitDistance W σ' := by
    apply factorized_law_gap R hR W σ' μ X Y hXm hYm hXp hYp
    · intro i j a c
      simpa only [hdiag] using filter_density_integrable (hMi i j) (CFC.sqrt (Bᴴ*B)) a c
    · intro i j s hs a c
      simpa only [hdiag] using filter_setIntegral (M i j) (CFC.sqrt (Bᴴ*B))
        (fun t => (X i t ⊗ₖ Y j t)ᵀ) (hMi i j) (hMs i j) hs a c
    · exact hWnorm
    · exact hσnorm
  exact (ENNReal.ofReal_le_ofReal hg).trans (hcontract M σ)

end SecretKey

end

end OAI
