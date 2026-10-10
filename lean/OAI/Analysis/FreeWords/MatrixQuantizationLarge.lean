import Mathlib
import OAI.Analysis.FreeWords.MatrixQuantizationEnd

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_extended_energy_decrease_large {ι : Type*} [Fintype ι]
    {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M) (x : ι → ConcreteAlgebra M)
    (hx : ∀ i, τ.map (x i)=0) (n : ℕ) (hn : 0 < n)
    (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)
    (hs : 0 < ∑ i, (traceNorm τ (matrixAverage ρ (x i)))^2) :
    ∃ (m : ℕ) (_hm : 0 < m)
      (σ : Matrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
      Function.Injective σ ∧ n ≤ m ∧
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
  refine ⟨n*k,Nat.mul_pos hn hk,Q,Q.toAlgHom.toRingHom.injective, Nat.le_mul_of_pos_right n hk,?_⟩
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

theorem matrix_commutant_quantization_large {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (x : ι → ConcreteAlgebra M) (hx : ∀ i, τ.map (x i)=0)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_hn : 0 < n)
      (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
      Function.Injective ρ ∧ N ≤ n ∧ ∀ i, traceNorm τ (matrixAverage ρ (x i)) < ε := by
  classical
  let S : Set ℝ := {s | ∃ (n : ℕ) (_hn : 0 < n)
    (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
    Function.Injective ρ ∧ N ≤ n ∧ s=∑ i, (traceNorm τ (matrixAverage ρ (x i)))^2}
  have hne : S.Nonempty := by
    obtain ⟨ρ,hρ,_⟩ := exists_matrix_subfactor M τ hF hD (max 1 N) (by omega)
    exact ⟨_, max 1 N, by omega,ρ,hρ,le_max_right _ _,rfl⟩
  have hpos : ∀ s∈S, 0 ≤ s := by
    rintro s ⟨n,hn,ρ,hρ,hN,rfl⟩
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdec : ∀ s∈S, 0 < s → ∃ t∈S, t < 7/8*s := by
    rintro s ⟨n,hn,ρ,hρ,hN,rfl⟩ hs
    obtain ⟨m,hm,σ,hσ,hnm,ht⟩ := exists_extended_energy_decrease_large τ hF hD x hx n hn ρ hs
    exact ⟨_,⟨m,hm,σ,hσ,hN.trans hnm,rfl⟩,ht⟩
  have hi := contracting_nonnegative_set_inf_zero S hne hpos hdec
  obtain ⟨s,hs,hsε⟩ := exists_lt_of_csInf_lt hne (show sInf S < ε^2 by rw [hi]; positivity)
  obtain ⟨n,hn,ρ,hρ,hN,rfl⟩ := hs
  refine ⟨n,hn,ρ,hρ,hN,fun i => ?_⟩
  have hh : (traceNorm τ (matrixAverage ρ (x i)))^2 ≤
      ∑ j, (traceNorm τ (matrixAverage ρ (x j)))^2 :=
    Finset.single_le_sum (f := fun j => (traceNorm τ (matrixAverage ρ (x j)))^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hz := traceNorm_nonneg τ (matrixAverage ρ (x i))
  nlinarith

end

end KKMatrixQuantization
end

end OAI
