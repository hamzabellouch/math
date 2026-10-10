import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarEarlyMoment

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem scalarPrefixVariance_list {A : Type} (w : List A) (f : A → ℝ) (j : Fin (w.length+1)) :
    scalarPrefixVariance w.length (fun i => f (w.get i)) j=((w.take j.val).map (fun p => (f p)^2)).sum := by
  induction w with
  | nil => simp [scalarPrefixVariance,scalarPrefixVector]
  | cons p w ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [scalarPrefixVariance,scalarPrefixVector]
    · unfold scalarPrefixVariance scalarPrefixVector
      change (∑ i : Fin (w.length+1), (if i.val<k.val+1 then f ((p::w).get i) else 0)^2)=_
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero,Fin.val_succ,List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,
        Nat.zero_lt_succ,ite_true,Nat.add_lt_add_iff_right,List.take_succ_cons,List.map_cons,List.sum_cons]
      rw [← ih k]
      rfl

end SK.Analytic

end
end

end OAI
