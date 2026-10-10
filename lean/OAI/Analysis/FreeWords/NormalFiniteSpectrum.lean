import Mathlib
import OAI.Analysis.FreeWords.FiniteSpectrum

namespace OAI

noncomputable section

namespace KKSpectralSupport

open KKTraceTransfer KKPolarSupport

open scoped ComplexStarModule

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H}

theorem product_partition_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ConcreteAlgebra M) (q : κ → ConcreteAlgebra M)
    (hp : ∑ i, p i=1) (hq : ∑ j, q j=1) : ∑ ij : ι × κ, p ij.1*q ij.2=1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,hq,mul_one,hp]

theorem product_partition_weight {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ConcreteAlgebra M) (q : κ → ConcreteAlgebra M)
    (hp : ∑ i, p i=1) (hq : ∑ j, q j=1) (c : ι → ℂ) (d : κ → ℂ) :
    ∑ ij : ι × κ, (c ij.1 + Complex.I*d ij.2) • (p ij.1*q ij.2)=
      (∑ i, c i • p i)+Complex.I • (∑ j, d j • q j) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [add_smul,Finset.sum_add_distrib]
  congr 1
  · simp only [← smul_mul_assoc,← Finset.mul_sum,hq,mul_one]
  · simp only [← mul_smul_comm,← Finset.mul_sum,← Finset.sum_mul,hp,one_mul,
      mul_smul,Finset.smul_sum]

theorem normal_finite_spectrum_approximation (M : VonNeumannAlgebra H)
    (a : ConcreteAlgebra M) (ha : IsStarNormal a) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m n : ℕ) (p : Fin m × Fin n → ConcreteAlgebra M) (c : Fin m × Fin n → ℂ),
      (∀ i, IsStarProjection (p i)) ∧ (∀ i j, i ≠ j → p i*p j=0) ∧
      (∑ i, p i=1) ∧ (∀ i, Commute a (p i)) ∧
      ‖a-∑ i, c i • p i‖ < ε := by
  classical
  let r : ConcreteAlgebra M := ℜ a
  let s : ConcreteAlgebra M := ℑ a
  have hrs : Commute r s := isStarNormal_iff_commute_realPart_imaginaryPart.mp ha
  obtain ⟨m,p,c,hp,hpo,hp1,hpr,hpc,hpre⟩ := finite_spectrum_approximation_central M r (ℜ a).property (ε/2) (half_pos hε)
  obtain ⟨n,q,d,hq,hqo,hq1,hqs,hqc,hqre⟩ := finite_spectrum_approximation_central M s (ℑ a).property (ε/2) (half_pos hε)
  have hpq (i : Fin m) (j : Fin n) : Commute (p i) (q j) :=
    (hpc (q j) (hqc r hrs j).symm i).symm
  have hpa (i : Fin m) : Commute a (p i) := by
    rw [← realPart_add_I_smul_imaginaryPart a]
    exact (hpr i).add_left ((hpc s hrs.symm i).smul_left _)
  have hqa (j : Fin n) : Commute a (q j) := by
    rw [← realPart_add_I_smul_imaginaryPart a]
    exact (hqc r hrs j).add_left ((hqs j).smul_left _)
  let f : Fin m × Fin n → ConcreteAlgebra M := fun ij => p ij.1*q ij.2
  let z : Fin m × Fin n → ℂ := fun ij => (c ij.1:ℂ)+Complex.I*(d ij.2:ℂ)
  refine ⟨m,n,f,z,(fun ij => (hp ij.1).mul (hq ij.2) (hpq ij.1 ij.2)),?_,
    product_partition_sum p q hp1 hq1,(fun ij => (hpa ij.1).mul_right (hqa ij.2)),?_⟩
  · intro ij kl hne
    change (p ij.1*q ij.2)*(p kl.1*q kl.2)=0
    have he : (p ij.1*q ij.2)*(p kl.1*q kl.2)=(p ij.1*p kl.1)*(q ij.2*q kl.2) := by
      calc
        _ = p ij.1*(q ij.2*p kl.1)*q kl.2 := by simp only [mul_assoc]
        _ = p ij.1*(p kl.1*q ij.2)*q kl.2 := by rw [← (hpq kl.1 ij.2).eq]
        _ = _ := by simp only [mul_assoc]
    rw [he]
    by_cases hi : ij.1=kl.1
    · have hj : ij.2≠kl.2 := fun hj => hne (Prod.ext hi hj)
      rw [hqo _ _ hj,mul_zero]
    · rw [hpo _ _ hi,zero_mul]
  · dsimp only [f,z]
    rw [product_partition_weight p q hp1 hq1 (fun i => (c i : ℂ)) (fun j => (d j : ℂ))]
    have he : a-((∑ i, (c i:ℂ) • p i)+Complex.I • (∑ j, (d j:ℂ) • q j))=
      (r-∑ i, (c i:ℂ) • p i)+Complex.I • (s-∑ j, (d j:ℂ) • q j) := by
      rw [smul_sub]
      have ha' : a=r+Complex.I • s := (realPart_add_I_smul_imaginaryPart a).symm
      rw [ha']; abel
    rw [he]
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_smul,Complex.norm_I,one_mul]
    linarith

end

end KKSpectralSupport
end

end OAI
