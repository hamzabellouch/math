import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.GroupTheory.Perm.Fin
import OAI.Analysis.Laughlin.Polynomial.LaughlinMultidegree

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

def spinorPermutation {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (SpinorVariables N) :=
  σ.prodCongr (Equiv.refl Bool)

theorem bracket_rename {N : ℕ} (σ : Equiv.Perm (Fin N)) (i j : Fin N) :
    rename (spinorPermutation σ) (bracket i j)=bracket (σ i) (σ j) := by
  simp [bracket,spinorPermutation]

theorem laughlinPolynomial_eq_Ioi (N : ℕ) :
    laughlinPolynomial N=∏ i : Fin N, ∏ j ∈ Finset.Ioi i, bracket i j^3 := by
  unfold laughlinPolynomial
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

theorem laughlinPolynomial_rename_swap {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    rename (spinorPermutation (Equiv.swap i j)) (laughlinPolynomial N) = -laughlinPolynomial N := by
  rw [laughlinPolynomial_eq_Ioi]
  simp only [map_prod,map_pow,bracket_rename]
  rw [(Equiv.swap i j).prod_Ioi_comp_eq_sign_mul_prod (f := fun a b => bracket a b^3)]
  · simp [Equiv.Perm.sign_swap hij]
  · intro a b
    rw [bracket_swap b a]
    ring

theorem monomialExponent_rename {N Q : ℕ} (σ : Equiv.Perm (Fin N)) (a : Configuration N Q) :
    (monomialExponent a).mapDomain (spinorPermutation σ)=monomialExponent (a ∘ σ.symm) := by
  ext ⟨k,b⟩
  rw [Finsupp.mapDomain_equiv_apply]
  simp [monomialExponent,spinorPermutation]

theorem spinWeight_permute {N Q : ℕ} (σ : Equiv.Perm (Fin N)) (a : Configuration N Q) :
    spinWeight (a ∘ σ)=spinWeight a := by
  unfold spinWeight
  congr 1
  exact Equiv.prod_comp σ (fun k => Real.sqrt (Nat.choose Q (a k).val : ℝ))

theorem laughlinVector_antisymmetric (N : ℕ) : Antisymmetric (laughlinVector N (3*(N-1))) := by
  intro i j hij a
  have hc := coeff_rename_mapDomain (spinorPermutation (Equiv.swap i j))
    (spinorPermutation (Equiv.swap i j)).injective (laughlinPolynomial N) (monomialExponent a)
  rw [laughlinPolynomial_rename_swap i j hij,monomialExponent_rename] at hc
  simp only [coeff_neg,Equiv.symm_swap] at hc
  change (laughlinPolynomial N).coeff (monomialExponent (a ∘ Equiv.swap i j)) /
    spinWeight (a ∘ Equiv.swap i j) = -((laughlinPolynomial N).coeff (monomialExponent a)/spinWeight a)
  rw [spinWeight_permute]
  have he : (laughlinPolynomial N).coeff (monomialExponent (a ∘ Equiv.swap i j)) =
      -(laughlinPolynomial N).coeff (monomialExponent a) := by linear_combination -hc
  rw [he,neg_div]

end Laughlin

end OAI
