import OAI.NumberTheory.Ostmann.Supply.NaturalWeight
import OAI.NumberTheory.Ostmann.Supply.PrimeEnumeration

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
open BivariateTruncation

theorem truncatedWeight_fin_univ (b : ℕ→ℝ) (n K : ℕ) :
    truncatedWeight Finset.univ (fun i:Fin n => b i) K=truncatedWeight (Finset.range n) b K := by
  apply Complex.ofReal_injective
  have hf := rectangularTruncation_eq_weight
    (c:=subsetPairPolynomial (Finset.range n) (fun i => (b i:ℂ)))
    Finset.univ (fun i:Fin n => b i)
    (fun u v => by
      rw [eval_subsetPairPolynomial]
      exact (Fin.prod_univ_eq_prod_range (fun i => (1+u*(b i:ℂ))*(1+v*(b i:ℂ))) n).symm) K
  exact hf.symm.trans (rectangularTruncation_real_subsetPairPolynomial (Finset.range n) b K)

theorem naturalKernelWeight_fin_univ (p : ℕ→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (n K k : ℕ) :
    truncatedWeight Finset.univ
      (fun i:Fin n => localKernel (S i.val) sparseKernelScale (k:ZMod (p i.val))) K =
      naturalKernelWeight p S n K k :=
  truncatedWeight_fin_univ (fun i => localKernel (S i) sparseKernelScale (k:ZMod (p i))) n K

theorem unitKernelProduct_fin_univ (p : ℕ→ℕ) [∀i,NeZero (p i)]
    (S : ∀i,Finset (ZMod (p i))) (n : ℕ) :
    (∏i:Fin n,unitKernelMean (S i) sparseKernelScale)=kernelUnitProduct (Finset.range n) p S :=
  Fin.prod_univ_eq_prod_range (fun i => unitKernelMean (S i) sparseKernelScale) n

theorem reciprocalMass_fin_univ (p : ℕ→ℕ) (n : ℕ) :
    (∑i:Fin n,(1:ℝ)/(p i:ℝ))=reciprocalMass (Finset.range n) p :=
  Fin.sum_univ_eq_sum_range (fun i => (1:ℝ)/(p i:ℝ)) n

end Ostmann.Supply

end

end OAI
