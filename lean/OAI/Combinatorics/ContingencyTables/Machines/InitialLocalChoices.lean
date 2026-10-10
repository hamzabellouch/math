import OAI.Combinatorics.ContingencyTables.Counting.InitializationBrackets

namespace OAI

/-! # The initialization brackets are actual sums over remaining row labels -/

namespace ContingencyTables.InitialLocalChoices

open scoped BigOperators Classical
open Nat
open InitializationBrackets

noncomputable def localWeight (b u v : ℕ) (S : Finset (Fin (b-u-v))) : ℝ :=
  ((S.card+v)!:ℝ)*((b-u-v-S.card+v)!:ℝ)/(b !:ℝ)

/-- Enumerating all choices of the remaining row labels gives exactly
the binomial/factorial bracket, including empty local spaces. -/
theorem sum_localWeight (b u v : ℕ) :
    (∑ S : Finset (Fin (b-u-v)), localWeight b u v S)=bracket b u v := by
  have h := Finset.sum_powerset_apply_card
    (fun k => ((k+v)!:ℝ)*((b-u-v-k+v)!:ℝ)/(b !:ℝ))
    (x := (Finset.univ : Finset (Fin (b-u-v))))
  simpa [localWeight,bracket,nsmul_eq_mul,Finset.sum_div,mul_div_assoc,mul_assoc] using h

/-- Independent choices in the cells factor exactly; the expression is
a finite combinatorial sum before evaluating its four bracket cases. -/
theorem sum_independent_choices {C : Type*} [Fintype C] (b u v : C → ℕ) :
    (∑ S : ((c : C) → Finset (Fin (b c-u c-v c))),
      ∏ c, localWeight (b c) (u c) (v c) (S c))=
      ∏ c, bracket (b c) (u c) (v c) := by
  rw [← Fintype.prod_sum]
  simp_rw [sum_localWeight]

end ContingencyTables.InitialLocalChoices

end OAI
