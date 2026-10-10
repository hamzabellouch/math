import Mathlib
import OAI.Analysis.FreeWords.TensorGram
import OAI.Analysis.FreeWords.TensorHaar

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

open MeasureTheory Matrix

noncomputable section

def matrixPairCLM {ι : Type*} [Fintype ι] (S : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixPair S
      map_add' := fun T R => by simp [matrixPair,mul_add]
      map_smul' := fun c T => by simp [matrixPair,Matrix.mul_smul] }

@[simp] theorem matrixPairCLM_apply {ι : Type*} [Fintype ι] (S T : Matrix ι ι ℂ) :
    matrixPairCLM S T=matrixPair S T := rfl

theorem positionPair_conjugation {r d : ℕ} (π : Equiv.Perm (Fin r))
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    matrixPair (positionMatrix π)
      (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
       star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ))) =
      matrixPair (positionMatrix π) T := by
  let X := tensorMatrix (r := r) (U : Matrix (Fin d) (Fin d) ℂ)
  have hc : Commute (star (positionMatrix (d := d) π)) X := by
    apply Commute.star_left
    simpa only [tensorMatrix_star] using positionMatrix_tensorMatrix_commute (d := d) π (star (U : Matrix (Fin d) (Fin d) ℂ))
  have he : star X*star (positionMatrix π)*X=star (positionMatrix π) :=
    (commute_unitary_iff_star_left_conjugate (tensorMatrix_unitary U)).mp hc.symm
  change Matrix.trace (star (positionMatrix π)*(X*T*star X))=
    Matrix.trace (star (positionMatrix π)*T)
  calc
    _ = Matrix.trace ((star X*star (positionMatrix π)*X)*T) := by
      simpa only [mul_assoc] using Matrix.trace_mul_cycle (star (positionMatrix π)) (X*T) (star X)
    _ = _ := by rw [he]

theorem positionPair_average {r d : ℕ}
    (μ : Measure (Matrix.unitaryGroup (Fin d) ℂ)) [IsProbabilityMeasure μ]
    (π : Equiv.Perm (Fin r)) (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) :
    matrixPair (positionMatrix π) (tensorAverage μ T)=matrixPair (positionMatrix π) T := by
  have hint := (continuous_tensorConjugation T).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  change matrixPairCLM (positionMatrix π) (∫ U, tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*T*
    star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)) ∂μ)=_
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  simp only [matrixPairCLM_apply,positionPair_conjugation]
  simp

theorem tensorAverage_gram_formula {r d : ℕ} (hrd : r ≤ d)
    (μ : Measure (Matrix.unitaryGroup (Fin d) ℂ)) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) :
    tensorAverage μ T = ∑ π,
      (∑ σ,(permutationGram r d)⁻¹ π σ * matrixPair (positionMatrix σ) T) • positionMatrix π := by
  classical
  obtain ⟨c,hc⟩ := tensorAverage_span r d hrd μ T
  have hv : permutationGram r d *ᵥ c = fun σ => matrixPair (positionMatrix σ) T := by
    funext σ
    have hh := positionPair_average μ σ T
    rw [hc,matrixPair_sum_smul] at hh
    simpa only [Matrix.mulVec,dotProduct,permutationGram_apply,mul_comm] using hh
  have he := congrArg (fun v => (permutationGram r d)⁻¹ *ᵥ v) hv
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (permutationGram_det_ne_zero hrd)),Matrix.one_mulVec] at he
  rw [hc,he]
  rfl

def matrixApplyCLM {ι : Type*} [Fintype ι] (a b : ι) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => T a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem matrixApplyCLM_apply {ι : Type*} [Fintype ι] (a b : ι) (T : Matrix ι ι ℂ) :
    matrixApplyCLM a b T=T a b := rfl

theorem tensorAverage_single_apply {r d : ℕ}
    (μ : Measure (Matrix.unitaryGroup (Fin d) ℂ)) [IsProbabilityMeasure μ]
    (a b c e : Fin r → Fin d) :
    tensorAverage μ (Matrix.single b e 1) a c =
      ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
        tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ) a b *
          star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ) c e) ∂μ := by
  classical
  have hint := (continuous_tensorConjugation (Matrix.single b e (1 : ℂ))).integrable_of_hasCompactSupport (μ := μ)
    (HasCompactSupport.of_compactSpace _)
  change matrixApplyCLM a c (∫ U, tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)*Matrix.single b e 1*
    star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)) ∂μ)=_
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  apply integral_congr_ae
  filter_upwards [] with U
  simp [matrixApplyCLM_apply,Matrix.mul_apply,Matrix.single_apply,Matrix.star_apply,ite_and]

theorem matrixPair_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℂ) (b e : ι) :
    matrixPair S (Matrix.single b e 1)=star (S b e) := by
  simp [matrixPair,Matrix.trace_mul_single,Matrix.star_apply]

theorem haar_moment_formula (r d : ℕ) (hrd : r ≤ d)
    (a b c e : Fin r → Fin d) :
    (∫ U : Matrix.unitaryGroup (Fin d) ℂ,
      tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ) a b *
        star (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ) c e) ∂matrixHaar d) =
    ∑ π,∑ σ,(permutationGram r d)⁻¹ π σ *
      positionMatrix π a c * star (positionMatrix σ b e) := by
  classical
  rw [← tensorAverage_single_apply,tensorAverage_gram_formula hrd]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,matrixPair_single,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro σ _
  ring

end

end KKWeingarten
end

end OAI
