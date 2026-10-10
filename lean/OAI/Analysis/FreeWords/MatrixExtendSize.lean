import Mathlib
import OAI.Analysis.FreeWords.MatrixCommutantTrace
import OAI.Analysis.FreeWords.MatrixProduct
import OAI.Analysis.FreeWords.MatrixReindex
import OAI.Analysis.FreeWords.MatrixSubfactor
import OAI.Analysis.FreeWords.MatrixTraceUnique

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport KKMatrixQuantization

noncomputable section

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

theorem matrixProduct_contains_left
    (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) (σ : Matrix κ κ ℂ →⋆ₐ[ℂ] A)
    (hc : ∀ i j k l, Commute (matrixUnit ρ i j) (matrixUnit σ k l)) :
    ρ.range ≤ (matrixProduct ρ σ hc).range := by
  rintro x ⟨a,rfl⟩
  refine ⟨∑ i,∑ j,∑ k, a i j • Matrix.single (i,k) (j,k) 1,?_⟩
  change matrixProduct ρ σ hc (∑ i,∑ j,∑ k, a i j • Matrix.single (i,k) (j,k) 1)=ρ a
  simp only [map_sum,map_smul]
  change (∑ i,∑ j,∑ k, a i j • matrixUnit (matrixProduct ρ σ hc) (i,k) (j,k))=ρ a
  simp only [matrixProduct_unit,productUnits]
  simp only [← Finset.smul_sum,← Finset.mul_sum,matrixUnit_sum_diag,mul_one]
  exact (matrix_representation ρ a).symm

theorem matrixReindex_comp_range (e : ι ≃ κ) (ρ : Matrix ι ι ℂ →⋆ₐ[ℂ] A) :
    (ρ.comp (matrixReindex e.symm)).range=ρ.range := by
  apply le_antisymm
  · rintro x ⟨a,rfl⟩
    exact ⟨matrixReindex e.symm a,rfl⟩
  · rintro x ⟨a,rfl⟩
    refine ⟨matrixReindex e a,?_⟩
    change ρ (matrixReindex e.symm (matrixReindex e a))=ρ a
    congr 1
    ext i j
    change a (e.symm (e i)) (e.symm (e j))=a i j
    simp only [Equiv.symm_apply_apply]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem matrix_extension_size (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M) (n k : ℕ) (hn : 0<n) (hk : 0<k)
    (β : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M) :
    ∃ ρ : Matrix (Fin (n*k)) (Fin (n*k)) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
      Function.Injective ρ ∧ β.range≤ρ.range ∧
      ∀ x, τ.map (ρ x)=((n*k:ℕ):ℂ)⁻¹*Matrix.trace x := by
  classical
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have : NeZero k := ⟨Nat.ne_of_gt hk⟩
  obtain ⟨σ,hσ,_⟩ := exists_matrix_subfactor (matrixCommutant β) (commutantTrace β τ)
    (matrixCommutant_factor β hF) (matrixCommutant_diffuse β hD) k hk
  let σ' := (commutantInclusion β).comp σ
  have hc (i j : Fin n) (a b : Fin k) : Commute (matrixUnit β i j) (matrixUnit σ' a b) :=
    (inclusion_commute β (matrixUnit σ a b) i j).symm
  let P := matrixProduct β σ' hc
  let e : Fin n × Fin k ≃ Fin (n*k) := finProdFinEquiv
  let Q := P.comp (matrixReindex e.symm)
  have : Nontrivial (ConcreteAlgebra M) := ⟨⟨0,1,fun h => by
    have ht := congrArg τ.map h
    rw [map_zero,τ.normalized] at ht
    exact zero_ne_one ht⟩⟩
  have : NeZero (n*k) := ⟨Nat.ne_of_gt (Nat.mul_pos hn hk)⟩
  refine ⟨Q,Q.toAlgHom.toRingHom.injective,?_,?_⟩
  · change β.range≤(P.comp (matrixReindex e.symm)).range
    rw [matrixReindex_comp_range]
    exact matrixProduct_contains_left β σ' hc
  · intro x
    simpa only [Fintype.card_fin] using matrixHom_trace Q τ.map τ.normalized τ.tracial x

end

end KKVariableUltra
end

end OAI
