import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStageOptionMeanBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction

private theorem ite_true_guard (p : Prop) (s : Decidable p)
    (t : Decidable ((true : Bool) ∧ p)) (x : ℂ) :
    @ite ℂ p s 0 x = @ite ℂ ((true : Bool) ∧ p) t 0 x := by
  classical
  by_cases hp : p <;> simp [hp]

theorem option_cmean_eq_of_point_true_guard {α δ : Type*} [Fintype α]
    (μ : FinitePrior α) (opt : Option δ)
    (A : δ → α → ℂ) (K D : δ → ℂ) (V : δ → α → ℂ)
    (p : α → Prop) (s : ∀u,Decidable (p u))
    (t : ∀u,Decidable ((true : Bool) ∧ p u))
    (h : ∀r u,A r u=K r*(D r*@ite ℂ (p u) (s u) 0 (V r u))) :
    μ.cmean (fun u=>opt.elim 0 (fun r=>A r u)) =
      opt.elim 0 (fun r=>K r*μ.cmean (fun u=>
        D r*@ite ℂ ((true : Bool) ∧ p u) (t u) 0 (V r u))) :=
  option_cmean_eq_of_point μ opt A K
    (fun r u=>D r*@ite ℂ ((true : Bool) ∧ p u) (t u) 0 (V r u))
    (fun r u=>(h r u).trans (congrArg (fun x : ℂ=>K r*(D r*x))
      (ite_true_guard (p u) (s u) (t u) (V r u))))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
