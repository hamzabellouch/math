import OAI.InformationTheory.Entanglement.FullQuantumConsumer
import OAI.InformationTheory.Entanglement.ConditionedLaw
import OAI.InformationTheory.Entanglement.HilbertLawScale

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
namespace PositiveHilbertMeasure

def restrict (b : HilbertBasis ι ℂ H) (W : PositiveHilbertMeasure T H b)
    (A : Set T) (hA : MeasurableSet A) : PositiveHilbertMeasure T H b where
  value s := W.value (s∩A)
  coeff x y := (W.coeff x y).restrict A
  coeff_value x y s hs := by
    rw [VectorMeasure.restrict_apply _ hA hs,W.coeff_value _ _ _ (hs.inter hA)]
  positive s hs := W.positive (s∩A) (hs.inter hA)
  traceMeasure := W.traceMeasure.restrict A
  traceFinite := inferInstance
  trace_value s hs := by
    rw [Measure.real,Measure.restrict_apply hs]
    exact W.trace_value _ (hs.inter hA)
lemma restrict_value (b : HilbertBasis ι ℂ H) (W : PositiveHilbertMeasure T H b)
    (A : Set T) (hA : MeasurableSet A) (s : Set T) :
    (W.restrict b A hA).value s=W.value (s∩A) := rfl
end PositiveHilbertMeasure
omit [DecidableEq n] [DecidableEq m] [DecidableEq e] in
lemma filter_scaled_restrict_value (M : PositiveMatrixMeasure T (n×m))
    (B : Matrix e (n×m) ℂ) (A : Set T) (hA : MeasurableSet A)
    (c : ℝ) (hc : 0≤c) {s : Set T} (hs : MeasurableSet s) :
    (((M.restrict A).scale c hc).filter B).value s=
      (c : ℂ) • ((M.filter B).value (s∩A)) := by
  rw [PositiveMatrixMeasure.filter_value,PositiveMatrixMeasure.scale_value,
    PositiveMatrixMeasure.restrict_value _ hA hs,PositiveMatrixMeasure.filter_value,
    Matrix.mul_smul,Matrix.smul_mul]

omit [DecidableEq n] [DecidableEq m] in
lemma embedded_conditioning_value (b : HilbertBasis ι ℂ H) (v : e→H)
    (hv : Orthonormal ℂ v) (M : PositiveMatrixMeasure T (n×m))
    (B : Matrix e (n×m) ℂ) (A : Set T) (hA : MeasurableSet A)
    (c : ℝ) (hc : 0≤c) {s : Set T} (hs : MeasurableSet s) :
    ((((M.restrict A).scale c hc).filter B).hilbertEmbedding b v hv).value s=
      ((((M.filter B).hilbertEmbedding b v hv).restrict b A hA).scale c hc).value s := by
  change hilbertEmbed v _ = (c : ℂ) • hilbertEmbed v _
  rw [filter_scaled_restrict_value M B A hA c hc hs]
  unfold hilbertEmbed
  simp only [Matrix.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]

theorem full_quantum_conditioned_factorized_gap (b : HilbertBasis ι ℂ H)
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
    (A : Set T) (hA : MeasurableSet A)
    (hr : 0<publicMass (fun i j => (M i j).filter B) A)
    (σ : PositiveHilbertMeasure T H b) (hσ1 : σ.traceMeasure Set.univ=1) :
    ENNReal.ofReal (1/5) ≤ hilbertCQDistance b
      (fun i j => ((((M i j).restrict A).scale
        (publicMass (fun i j => (M i j).filter B) A)⁻¹ (inv_nonneg.mpr hr.le)).filter B).hilbertEmbedding b v hv) σ := by
  let c := (publicMass (fun i j => (M i j).filter B) A)⁻¹
  have hc : 0≤c := inv_nonneg.mpr hr.le
  let M' := fun i j => ((M i j).restrict A).scale c hc
  let X' := fun i t => (c : ℂ) • X i t
  have he (i j t) : (X' i t ⊗ₖ Y j t)ᵀ=(c : ℂ) • (X i t ⊗ₖ Y j t)ᵀ := by
    exact congrArg Matrix.transpose (Matrix.smul_kronecker _ _ _)
  apply full_quantum_factorized_gap b R hR i₀ v hv j₀ B hGram M' (μ.restrict A) X' Y
    (fun i => (measurable_const (a := (c : ℂ))).smul (hXm i)) hYm
    (fun i t => (hXp i t).smul (by exact_mod_cast hc)) hYp
  · intro i j a d
    simp only [he,Matrix.smul_apply,smul_eq_mul]
    exact ((hMi i j a d).integrableOn).const_mul _
  · intro i j s hs a d
    simp only [he,Matrix.smul_apply,smul_eq_mul,integral_const_mul]
    rw [Measure.restrict_restrict hs,hMs i j (s∩A) (hs.inter hA)]
    simp only [M',PositiveMatrixMeasure.scale_value,
      PositiveMatrixMeasure.restrict_value _ hA hs,Matrix.smul_apply,smul_eq_mul]
  · simp only [M',filter_scaled_restrict_value _ B A hA c hc MeasurableSet.univ,
      Set.univ_inter,Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,← Finset.mul_sum]
    exact inv_mul_cancel₀ hr.ne'
  · exact hσ1

end SecretKey

end

end OAI
