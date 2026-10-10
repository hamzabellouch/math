import Mathlib
import OAI.Analysis.FreeWords.MatrixCommutantTrace
import OAI.Analysis.FreeWords.MatrixEnergyDecrease
import OAI.Analysis.FreeWords.MatrixProduct
import OAI.Analysis.FreeWords.MatrixReindex

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem map_matrixAverage {ι A B : Type*} [Fintype ι] [DecidableEq ι]
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (f : A →⋆ₐ[ℂ] B) (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (x : A) :
    f (matrixAverage ρ x)=matrixAverage (f.comp ρ) (f x) := by
  simp only [matrixAverage,map_smul,map_sum,map_mul,StarAlgHom.comp_apply]

theorem exists_extended_energy_decrease {ι : Type*} [Fintype ι]
    {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M) (x : ι → ConcreteAlgebra M)
    (hx : ∀ i, τ.map (x i)=0) (n : ℕ) (hn : 0 < n)
    (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)
    (hs : 0 < ∑ i, (traceNorm τ (matrixAverage ρ (x i)))^2) :
    ∃ (m : ℕ) (_hm : 0 < m)
      (σ : Matrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
      Function.Injective σ ∧
      ∑ i, (traceNorm τ (matrixAverage σ (x i)))^2 <
        7/8*∑ i, (traceNorm τ (matrixAverage ρ (x i)))^2 := by
  classical
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let B := matrixCommutant ρ
  let τB := commutantTrace ρ τ
  let y (i : ι) : ConcreteAlgebra B :=
    inCommutant ρ (matrixAverage ρ (x i)) (matrixAverage_commute ρ (x i))
  have hy (i : ι) : τB.map (y i)=0 := by
    change τ.map (matrixAverage ρ (x i))=0
    rw [matrixAverage_trace,hx]
  have hnrm (i : ι) : traceNorm τB (y i)=traceNorm τ (matrixAverage ρ (x i)) :=
    commutantTrace_norm ρ τ (y i)
  obtain ⟨k,hk,σ,vσ,hσ⟩ := exists_matrix_energy_decrease τB
    (matrixCommutant_factor ρ hF) (matrixCommutant_diffuse ρ hD) y hy (by simpa only [hnrm] using hs)
  have : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let σ' := (commutantInclusion ρ).comp σ
  have hc (i j : Fin n) (a b : Fin k) : Commute (matrixUnit ρ i j) (matrixUnit σ' a b) :=
    (inclusion_commute ρ (matrixUnit σ a b) i j).symm
  let P := matrixProduct ρ σ' hc
  let e : Fin n × Fin k ≃ Fin (n*k) := finProdFinEquiv
  let Q := P.comp (matrixReindex e.symm)
  have : Nontrivial (ConcreteAlgebra M) := ⟨⟨0,1,fun h => by
    have ht := congrArg τ.map h
    rw [map_zero,τ.normalized] at ht
    exact zero_ne_one ht⟩⟩
  have : NeZero (n*k) := ⟨Nat.ne_of_gt (Nat.mul_pos hn hk)⟩
  refine ⟨n*k,Nat.mul_pos hn hk,Q,Q.toAlgHom.toRingHom.injective,?_⟩
  have he (i : ι) : traceNorm τ (matrixAverage Q (x i))=
      traceNorm τB (matrixAverage σ (y i)) := by
    rw [commutantTrace_norm]
    change traceNorm τ (matrixAverage (P.comp (matrixReindex e.symm)) (x i))=
      traceNorm τ ((commutantInclusion ρ) (matrixAverage σ (y i)))
    rw [reindex_average,map_matrixAverage]
    change traceNorm τ (matrixAverage (matrixProduct ρ σ' hc) (x i))=
      traceNorm τ (matrixAverage σ' (matrixAverage ρ (x i)))
    rw [matrixProduct_average]
  simpa only [he,hnrm] using hσ

end

end KKMatrixQuantization
end

end OAI
