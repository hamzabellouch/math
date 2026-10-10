import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatchingReindex
import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatchingWhole

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateDiagonalMatching
open scoped BigOperators
open Ostmann.Preliminaries
attribute [local instance] Classical.propDecidable

theorem finite_indicator_eq_product {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P] :
    (if ∀i,P i then (1:ℝ) else 0)=∏i,if P i then (1:ℝ) else 0 := by
  classical
  by_cases hp : ∀i,P i
  · simp only [ite_eq_left hp,ite_eq_left (hp _),Finset.prod_const_one]
  · rw [ite_eq_right hp]
    obtain ⟨i,hi⟩ := not_forall.mp hp
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem matched_tuple_prior_mass_eq_unary {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (f : I → PrimeUpTo N) (e : Equiv.Perm I) :
    (productPrior (fun i => primeShellPrior (E i) (hE i))).mass (f ∘ e)=
      (∏i,(primeShellMass (E i))⁻¹)/((∏i,(f i).val : ℕ):ℝ)*
        ∏i,if f (e i)∈E i then (1:ℝ) else 0 := by
  rw [matched_tuple_prior_mass_eq]
  apply congrArg (fun x : ℝ => ((∏i,(primeShellMass (E i))⁻¹)/((∏i,(f i).val : ℕ):ℝ))*x)
  exact finite_indicator_eq_product (fun i => f (e i)∈E i)

end Ostmann.Characters.TemplateDiagonalMatching

end

end OAI
