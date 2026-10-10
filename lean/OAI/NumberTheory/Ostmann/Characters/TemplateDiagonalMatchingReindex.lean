import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatching

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateDiagonalMatching
open scoped BigOperators
open Ostmann.Preliminaries
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}

theorem fixed_diagonal_sum_eq_permutations (f : I → PrimeUpTo N)
    (hf : Function.Injective (fun i => (f i).val)) (H : (I → PrimeUpTo N) → ℂ) :
    (∑g : I → PrimeUpTo N, if Function.Injective (fun i => (g i).val) ∧
      (∏i,(g i).val)=(∏i,(f i).val) then H g else 0) =
      ∑e : Equiv.Perm I,H (f ∘ e) := by
  classical
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun (e : Equiv.Perm I) _ => f ∘ e)
  · intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · exact hf.comp e.injective
    · exact Equiv.prod_comp e (fun i => (f i).val)
  · intro e he e' he' heq
    apply Equiv.ext
    intro i
    apply hf
    exact congrArg Subtype.val (congrFun heq i)
  · intro g hg
    have hg' := (Finset.mem_filter.mp hg).2
    obtain ⟨e,he,hunique⟩ := existsUnique_prime_tuple_matching g f hg'.1 hf hg'.2
    refine ⟨e,Finset.mem_univ _,?_⟩
    funext i
    exact he i
  · intro e he
    rfl

theorem diagonal_prior_sum_eq_permutations
    (E F : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) (hF : ∀i,0<primeShellMass (F i))
    (H : (I → PrimeUpTo N) → (I → PrimeUpTo N) → ℂ) :
    (∑f : I → PrimeUpTo N, ∑g : I → PrimeUpTo N,
      if Function.Injective (fun i => (f i).val) ∧
        Function.Injective (fun i => (g i).val) ∧ (∏i,(g i).val)=(∏i,(f i).val) then
        ((productPrior (fun i => primeShellPrior (E i) (hE i))).mass f : ℂ)*
        ((productPrior (fun i => primeShellPrior (F i) (hF i))).mass g : ℂ)*H f g else 0) =
    ∑f : I → PrimeUpTo N, if Function.Injective (fun i => (f i).val) then
      ∑e : Equiv.Perm I,
        ((productPrior (fun i => primeShellPrior (E i) (hE i))).mass f : ℂ)*
        ((productPrior (fun i => primeShellPrior (F i) (hF i))).mass (f ∘ e) : ℂ)*H f (f ∘ e) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro f hfmem
  by_cases hf : Function.Injective (fun i => (f i).val)
  · simp only [hf,true_and,ite_true]
    exact fixed_diagonal_sum_eq_permutations f hf _
  · simp only [hf,false_and,ite_false,Finset.sum_const_zero]

theorem diagonal_prior_sum_eq_normalized_permutations
    (E F : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) (hF : ∀i,0<primeShellMass (F i))
    (H : (I → PrimeUpTo N) → (I → PrimeUpTo N) → ℂ) :
    (∑f : I → PrimeUpTo N, ∑g : I → PrimeUpTo N,
      if Function.Injective (fun i => (f i).val) ∧
        Function.Injective (fun i => (g i).val) ∧ (∏i,(g i).val)=(∏i,(f i).val) then
        ((productPrior (fun i => primeShellPrior (E i) (hE i))).mass f : ℂ)*
        ((productPrior (fun i => primeShellPrior (F i) (hF i))).mass g : ℂ)*H f g else 0) =
    ∑f : I → PrimeUpTo N, if Function.Injective (fun i => (f i).val) then
      ∑e : Equiv.Perm I,
        ((productPrior (fun i => primeShellPrior (E i) (hE i))).mass f : ℂ)*
        (((∏i,(primeShellMass (F i))⁻¹)/((∏i,(f i).val : ℕ):ℝ)*
          (if ∀i,f (e i)∈F i then 1 else 0) : ℝ) : ℂ) * H f (f ∘ e) else 0 := by
  rw [diagonal_prior_sum_eq_permutations]
  simp_rw [matched_tuple_prior_mass_eq]

end Ostmann.Characters.TemplateDiagonalMatching

end

end OAI
