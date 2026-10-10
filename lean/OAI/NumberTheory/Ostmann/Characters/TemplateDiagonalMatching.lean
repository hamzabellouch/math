import OAI.NumberTheory.Ostmann.Characters.PivotProductFibers

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateDiagonalMatching
open scoped BigOperators
open Ostmann.Preliminaries

variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}

omit [DecidableEq I] in
theorem prime_tuple_equal_product_match [DecidableEq I] (f g : I → PrimeUpTo N)
    (hprod : (∏i,(f i).val)=(∏i,(g i).val)) (i : I) :
    ∃j,g j=f i := by
  have hp := primeUpTo_prime (f i)
  have hd : (f i).val ∣ ∏j,(g j).val := by
    rw [←hprod]
    exact Finset.dvd_prod_of_mem (fun j => (f j).val) (Finset.mem_univ i)
  obtain ⟨j,hj,hdiv⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff (fun j => (g j).val)).mp hd
  refine ⟨j,Subtype.ext ?_⟩
  exact ((Nat.dvd_prime (primeUpTo_prime (g j))).mp hdiv |>.resolve_left hp.ne_one).symm

theorem existsUnique_prime_tuple_matching (f g : I → PrimeUpTo N)
    (hf : Function.Injective (fun i => (f i).val))
    (hg : Function.Injective (fun i => (g i).val))
    (hprod : (∏i,(f i).val)=(∏i,(g i).val)) :
    ∃! e : Equiv.Perm I, ∀i,g (e i)=f i := by
  classical
  choose e he using prime_tuple_equal_product_match f g hprod
  have hinj : Function.Injective e := by
    intro i j hij
    apply hf
    exact congrArg Subtype.val ((he i).symm.trans ((congrArg g hij).trans (he j)))
  let E : Equiv.Perm I := Equiv.ofBijective e ⟨hinj,Finite.surjective_of_injective hinj⟩
  refine ⟨E,he,?_⟩
  intro e' he'
  apply Equiv.ext
  intro i
  apply hg
  exact congrArg Subtype.val ((he' i).trans (he i).symm)

theorem tuple_prior_mass_eq (E : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) (w : I → PrimeUpTo N) :
    (productPrior (fun i => primeShellPrior (E i) (hE i))).mass w =
      if ∀i,w i∈E i then (∏i,(primeShellMass (E i))⁻¹)/((∏i,(w i).val : ℕ):ℝ) else 0 := by
  classical
  by_cases hw : ∀i,w i∈E i
  · rw [ite_eq_left hw]
    change (∏i,(primeShellPrior (E i) (hE i)).mass (w i))=_
    simp_rw [primeShellPrior_mass,ite_eq_left (hw _),div_eq_mul_inv]
    rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
    simp only [Nat.cast_prod]
    ring
  · rw [ite_eq_right hw]
    obtain ⟨i,hi⟩ := not_forall.mp hw
    change (∏i,(primeShellPrior (E i) (hE i)).mass (w i))=0
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [primeShellPrior_mass,ite_eq_right hi,zero_div]

theorem matched_tuple_prior_mass_eq (E : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) (f : I → PrimeUpTo N) (e : Equiv.Perm I) :
    (productPrior (fun i => primeShellPrior (E i) (hE i))).mass (f ∘ e) =
      (∏i,(primeShellMass (E i))⁻¹)/((∏i,(f i).val : ℕ):ℝ)*
        (if ∀i,f (e i)∈E i then 1 else 0) := by
  classical
  rw [tuple_prior_mass_eq]
  have hp := Equiv.prod_comp e (fun i => (f i).val)
  simp only [Function.comp_apply,hp]
  split_ifs <;> simp

end Ostmann.Characters.TemplateDiagonalMatching

end

end OAI
