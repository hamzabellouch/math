import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.MixedOrdering

namespace OAI

/-! A computable ordering of mixed derivatives for the finite evaluator. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff

def timeSpaceWord : List (Fin 4) → ℕ × List (Fin 3) :=
  List.rec (0, []) (fun j _ word => Fin.cases
    (word.1 + 1, word.2) (fun k => (word.1, k :: word.2)) j)

theorem timeSpaceWord_perm (α : List (Fin 4)) :
    α.Perm (List.replicate (timeSpaceWord α).1 0 ++
      (timeSpaceWord α).2.map Fin.succ) := by
  induction α with
  | nil => exact List.Perm.refl []
  | cons j α ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [timeSpaceWord, Fin.cases_zero, List.replicate_succ,
        List.cons_append] using ih.cons 0
    · have he := (List.perm_append_comm :
        ([k.succ] ++ List.replicate (timeSpaceWord α).1 0).Perm
          (List.replicate (timeSpaceWord α).1 0 ++ [k.succ])).append_right
        ((timeSpaceWord α).2.map Fin.succ)
      simpa only [timeSpaceWord, Fin.cases_succ, List.singleton_append,
        List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using
        (ih.cons k.succ).trans he

theorem mixedDerivative_normalForm {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (α : List (Fin 4)) (t : ℝ) (x : Space) :
    mixedDerivative V α (t, x) =
      iteratedDeriv (timeSpaceWord α).1
        (fun s => spatialWord (timeSpaceWord α).2 (fun y => V (s, y)) x) t := by
  rw [mixedDerivative_perm hV (timeSpaceWord_perm α)]
  exact mixedDerivative_time_spatial hV _ _ t x

end ForcedComputation

end OAI
