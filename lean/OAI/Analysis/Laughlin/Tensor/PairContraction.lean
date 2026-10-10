import OAI.Analysis.Laughlin.Fock.Hamiltonian
import OAI.Analysis.Laughlin.Tensor.ExteriorIsometry

namespace OAI

namespace Laughlin
open scoped BigOperators

noncomputable def headPairAmplitude {n Q : ℕ} (ψ : State (n+2) Q)
    (p : ℕ) (b : Configuration n Q) : ℂ :=
  ∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * ψ (Fin.cons x (Fin.cons y b))

theorem headPairAmplitude_antisymmetric {n Q : ℕ} (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) (p : ℕ) : Antisymmetric (headPairAmplitude ψ p) := by
  intro i j hij b
  unfold headPairAmplitude
  simp_rw [(antisymmetric_cons (antisymmetric_cons hψ _) _) i j hij,
    mul_neg,Finset.sum_neg_distrib]

namespace Fock

theorem tensorExterior_sum {I : Type*} (n Q : ℕ) (s : Finset I) (ψ : I → State n Q) :
    tensorExterior n Q (fun a => ∑ i ∈ s, ψ i a) = ∑ i ∈ s, tensorExterior n Q (ψ i) := by
  simp only [tensorExterior,Finset.sum_smul]
  rw [Finset.sum_comm]

theorem tensorExterior_smul (n Q : ℕ) (c : ℂ) (ψ : State n Q) :
    tensorExterior n Q (fun a => c * ψ a) = c • tensorExterior n Q ψ := by
  simp only [tensorExterior,Finset.smul_sum,smul_smul]

theorem two_annihilate_tensorExterior (n Q : ℕ) (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) (i j : Fin (Q+1)) :
    annihilate j (annihilate i (tensorExterior (n+2) Q ψ)) =
      ((n+2 : ℂ)*(n+1)) • tensorExterior n Q (fun a => ψ (Fin.cons i (Fin.cons j a))) := by
  rw [annihilate_tensorExterior (n+1) Q ψ hψ,map_smul,
    annihilate_tensorExterior n Q _ (antisymmetric_cons hψ i),smul_smul]
  congr 1
  push_cast
  ring

theorem sourcePairEnd_tensorExterior (n Q : ℕ) (ψ : State (n+2) Q)
    (hψ : Antisymmetric ψ) (p : ℕ) :
    sourcePairEnd Q p (tensorExterior (n+2) Q ψ) =
      (((n+2 : ℂ)*(n+1))/(Real.sqrt 2 : ℂ)) •
        tensorExterior n Q (headPairAmplitude ψ p) := by
  simp only [sourcePairEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,
    Module.End.mul_apply,two_annihilate_tensorExterior n Q ψ hψ,smul_smul]
  unfold headPairAmplitude
  simp only [tensorExterior_sum,tensorExterior_smul,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  push_cast
  ring

end Fock

end Laughlin

end OAI
