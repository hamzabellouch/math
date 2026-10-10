import Mathlib
import OAI.Analysis.FreeWords.MatrixAverageTrace
import OAI.Analysis.FreeWords.RankOneCompression

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKWeingarten MeasureTheory

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

variable {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)

theorem traceNorm_compression_sq (q x : ConcreteAlgebra M) (hq : IsStarProjection q) :
    (((traceNorm τ (q*x*q))^2 : ℝ) : ℂ)=τ.map (q*star x*q*x) := by
  rw [traceNorm_sq]
  have hq2 : q*q=q := hq.isIdempotentElem
  have hqs : star q=q := hq.isSelfAdjoint
  simp only [star_mul,hqs]
  calc
    τ.map (q*(star x*q)*(q*x*q)) = τ.map ((q*star x*(q*q)*x)*q) := by congr 1
    _ = τ.map (q*(q*star x*q*x)) := by rw [hq2,τ.tracial]
    _ = _ := by simp only [← mul_assoc,hq2]

theorem average_traceNorm_sq [NeZero d] (x : ConcreteAlgebra M) :
    τ.map (matrixAverage ρ (star x)*x)=(((traceNorm τ (matrixAverage ρ x))^2 : ℝ) : ℂ) := by
  rw [traceNorm_sq, matrixAverage_star]
  calc
    τ.map (matrixAverage ρ (star x)*x) = τ.map (star x*matrixAverage ρ x) := matrixAverage_trace_symm ρ τ _ _
    _ = τ.map (matrixAverage ρ (star x)*matrixAverage ρ x) := by
      rw [matrixAverage_trace_symm,matrixAverage_idempotent]

theorem continuous_compression_energy (z : Fin d) (x : ConcreteAlgebra M) :
    Continuous (fun U => (traceNorm τ (rankOne ρ z U*x*rankOne ρ z U))^2) := by
  have he (U : Matrix.unitaryGroup (Fin d) ℂ) :
      (traceNorm τ (rankOne ρ z U*x*rankOne ρ z U))^2=
      (τ.map (rankOne ρ z U*star x*rankOne ρ z U*x)).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re
      (traceNorm_compression_sq τ _ x (rankOne_projection ρ z U))
  simp_rw [he]
  exact Complex.continuous_re.comp (continuous_rankOne_pair τ ρ z (star x) x)

theorem integral_compression_energy (hd : 2 ≤ d) (z : Fin d) (x : ConcreteAlgebra M) :
    (∫ U : Matrix.unitaryGroup (Fin d) ℂ,
      (traceNorm τ (rankOne ρ z U*x*rankOne ρ z U))^2 ∂matrixHaar d)=
      ((traceNorm τ x)^2+(d : ℝ)*(traceNorm τ (matrixAverage ρ x))^2)/((d : ℝ)*((d : ℝ)+1)) := by
  have : NeZero d := ⟨by omega⟩
  have he := integral_rankOne_pair τ ρ hd z (star x) x
  rw [← traceNorm_sq,average_traceNorm_sq] at he
  have hU (U : Matrix.unitaryGroup (Fin d) ℂ) :
      τ.map (rankOne ρ z U*star x*rankOne ρ z U*x)=
      (((traceNorm τ (rankOne ρ z U*x*rankOne ρ z U))^2 : ℝ) : ℂ) :=
    (traceNorm_compression_sq τ _ x (rankOne_projection ρ z U)).symm
  simp_rw [hU] at he
  rw [integral_complex_ofReal] at he
  rw [mul_comm,← div_eq_mul_inv] at he
  exact_mod_cast he

theorem integral_compression_sum {ι : Type*} [Fintype ι]
    (hd : 2 ≤ d) (z : Fin d) (x : ι → ConcreteAlgebra M) :
    (∫ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∑ i,(traceNorm τ (rankOne ρ z U*x i*rankOne ρ z U))^2 ∂matrixHaar d)=
      ((∑ i,(traceNorm τ (x i))^2)+(d : ℝ)*∑ i,(traceNorm τ (matrixAverage ρ (x i)))^2)/
       ((d : ℝ)*((d : ℝ)+1)) := by
  rw [integral_finsetSum _ (fun i _ =>
    (continuous_compression_energy τ ρ z (x i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [integral_compression_energy τ ρ hd z,← Finset.sum_div,Finset.sum_add_distrib,Finset.mul_sum]

theorem exists_rankOne_small_compression {ι : Type*} [Fintype ι]
    (hd : 2 ≤ d) (z : Fin d) (x : ι → ConcreteAlgebra M) (ε : ℝ)
    (hb : ((∑ i,(traceNorm τ (x i))^2)+(d : ℝ)*∑ i,(traceNorm τ (matrixAverage ρ (x i)))^2)/
       ((d : ℝ)*((d : ℝ)+1)) < ε/(d : ℝ)) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∑ i,(traceNorm τ (rankOne ρ z U*x i*rankOne ρ z U))^2 < ε/(d : ℝ) := by
  by_contra hh
  push Not at hh
  have hi : Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      ∑ i,(traceNorm τ (rankOne ρ z U*x i*rankOne ρ z U))^2) (matrixHaar d) := by
    apply integrable_finsetSum
    intro i hi
    exact (continuous_compression_energy τ ρ z (x i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hle := integral_mono (integrable_const (ε/(d : ℝ))) hi hh
  rw [integral_const,integral_compression_sum τ ρ hd z x] at hle
  simp only [probReal_univ,smul_eq_mul,one_mul] at hle
  linarith

end

end KKMatrixQuantization
end

end OAI
