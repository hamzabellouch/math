import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedRetention

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def conditionSuccess (p : Law Ω) (E : Ω→Prop) (h : 0<acceptProb p E) : Law Ω where
  mass x := if E x then p.mass x/acceptProb p E else 0
  nonneg x := by
    split_ifs
    · exact div_nonneg (p.nonneg x) h.le
    · exact le_rfl
  total := by
    have he : (∑ x,if E x then p.mass x/acceptProb p E else 0)=
        (∑ x,if E x then p.mass x else 0)/acceptProb p E := by
      rw [sum_div]
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp only [zero_div]
    rw [he]
    have ht : (∑ x,if E x then p.mass x else 0)=acceptProb p E := by
      simp only [acceptProb,accepted,mul_one]
    rw [ht,div_self (ne_of_gt h)]

lemma conditionSuccess_support (p : Law Ω) (E : Ω→Prop) (h : 0<acceptProb p E)
    (x : Ω) (hx : (conditionSuccess p E h).mass x≠0) : p.mass x≠0 ∧ E x := by
  by_cases he : E x
  · refine ⟨?_,he⟩
    intro hp
    exact hx (by simp only [conditionSuccess,he,ite_true,hp,zero_div])
  · exact False.elim (hx (by simp only [conditionSuccess,he,ite_false]))

omit [Fintype Ξ] in

theorem conditionSuccess_fiber (p : Law Ω) (E : Ω→Prop) (h : 0<acceptProb p E)
    (stream : Ω→Ξ) (base : Ξ→ℝ) (L c : ℝ) (hc : 0<c) (hprob : c≤acceptProb p E)
    (hb : ∀ x,0≤base x) (hL : 0≤L)
    (hdom : ∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),p.mass ω)≤L*base x) :
    ∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),(conditionSuccess p E h).mass ω)≤
      (L/c)*base x := by
  intro x
  calc
    _ ≤ ∑ ω∈univ.filter (fun ω=>stream ω=x),p.mass ω/acceptProb p E := by
      apply sum_le_sum
      intro ω _
      dsimp only [conditionSuccess]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (p.nonneg ω) h.le
    _ = (∑ ω∈univ.filter (fun ω=>stream ω=x),p.mass ω)/acceptProb p E := (sum_div ..).symm
    _ ≤ (L*base x)/acceptProb p E := div_le_div_of_nonneg_right (hdom x) h.le
    _ ≤ (L*base x)/c := div_le_div_of_nonneg_left (mul_nonneg hL (hb x)) hc hprob
    _ = _ := by ring

end
end SharpLogRamsey.PublicTables

end

end OAI
