import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarEarlyMoment

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem scalarPrefixVariance_append_cut {A : Type} (l r : List A) (f : A → ℝ) :
    scalarPrefixVariance (l++r).length (fun i => f ((l++r).get i))
      ⟨l.length,by simp only [List.length_append]; omega⟩=(l.map (fun p => (f p)^2)).sum := by
  induction l with
  | nil => simp [scalarPrefixVariance,scalarPrefixVector]
  | cons p l ih =>
    unfold scalarPrefixVariance scalarPrefixVector at *
    change (∑ i : Fin ((l++r).length+1), (if i.val<l.length+1 then f (((p::l)++r).get i) else 0)^2)=_
    rw [Fin.sum_univ_succ]
    simp only [List.cons_append,List.get_eq_getElem,Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,
      List.getElem_cons_succ,Nat.zero_lt_succ,ite_true,Nat.add_lt_add_iff_right,List.map_cons,List.sum_cons]
    rw [← ih]
    rfl

end SK.Analytic

end
end

end OAI
