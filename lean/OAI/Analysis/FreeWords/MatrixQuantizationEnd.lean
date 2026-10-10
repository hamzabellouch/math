import Mathlib
import OAI.Analysis.FreeWords.MatrixEnergyExtend
import OAI.Analysis.FreeWords.MatrixSubfactor

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier KKProjectionSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem contracting_nonnegative_set_inf_zero (S : Set ℝ) (hne : S.Nonempty)
    (hpos : ∀ s∈S, 0 ≤ s)
    (hdec : ∀ s∈S, 0 < s → ∃ t∈S, t < 7/8*s) : sInf S=0 := by
  have hb : BddBelow S := ⟨0,hpos⟩
  have hi : 0 ≤ sInf S := le_csInf hne hpos
  apply le_antisymm _ hi
  by_contra hh
  have hp : 0 < sInf S := lt_of_not_ge hh
  obtain ⟨s,hs,hsl⟩ := exists_lt_of_csInf_lt hne (show sInf S < 8/7*sInf S by linarith)
  have hsi := csInf_le hb hs
  obtain ⟨t,ht,htl⟩ := hdec s hs (by linarith)
  have hti := csInf_le hb ht
  linarith

theorem matrix_commutant_quantization {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (x : ι → ConcreteAlgebra M) (hx : ∀ i, τ.map (x i)=0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_hn : 0 < n)
      (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
      Function.Injective ρ ∧ ∀ i, traceNorm τ (matrixAverage ρ (x i)) < ε := by
  classical
  let S : Set ℝ := {s | ∃ (n : ℕ) (_hn : 0 < n)
    (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
    Function.Injective ρ ∧ s=∑ i, (traceNorm τ (matrixAverage ρ (x i)))^2}
  have hne : S.Nonempty := by
    obtain ⟨ρ,hρ,_⟩ := exists_matrix_subfactor M τ hF hD 1 (by omega)
    exact ⟨_,1,by omega,ρ,hρ,rfl⟩
  have hpos : ∀ s∈S, 0 ≤ s := by
    rintro s ⟨n,hn,ρ,hρ,rfl⟩
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdec : ∀ s∈S, 0 < s → ∃ t∈S, t < 7/8*s := by
    rintro s ⟨n,hn,ρ,hρ,rfl⟩ hs
    obtain ⟨m,hm,σ,hσ,ht⟩ := exists_extended_energy_decrease τ hF hD x hx n hn ρ hs
    exact ⟨_,⟨m,hm,σ,hσ,rfl⟩,ht⟩
  have hi := contracting_nonnegative_set_inf_zero S hne hpos hdec
  obtain ⟨s,hs,hsε⟩ := exists_lt_of_csInf_lt hne (show sInf S < ε^2 by rw [hi]; positivity)
  obtain ⟨n,hn,ρ,hρ,rfl⟩ := hs
  refine ⟨n,hn,ρ,hρ,fun i => ?_⟩
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
