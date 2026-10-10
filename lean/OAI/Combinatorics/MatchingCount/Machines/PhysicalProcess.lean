import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.PhysicalPost

namespace OAI

namespace MatchingFPRAS.PhysicalPost
open Turing PhysicalStream

variable {Γ Q α β : Type} [Inhabited Γ]

inductive Implements (M : Table Γ Q) (out : α → Cfg Γ Q) :
    Cfg Γ Q → Experiment α → Prop
  | done (a) : Implements M out (out a) (.done a)
  | read (c) (f : Bool → Experiment α)
      (h : ∀ b,Implements M out (tick M c b) (f b)) : Implements M out c (.read f)
  | delay (c d) (n : ℕ) (p : Experiment α)
      (step : ∀ b : Stream,execute M n c b=d)
      (rest : Implements M out d p) : Implements M out c (.delay n p)

namespace Implements
variable {M : Table Γ Q} {out : α → Cfg Γ Q} {c : Cfg Γ Q} {p : Experiment α}

lemma execution (h : Implements M out c p) (b : Stream) :
    execute M (p.run b).2 c b=out (p.run b).1 := by
  induction h generalizing b with
  | done a => rfl
  | read c f h ih =>
    simp only [Experiment.run,execute_add]
    exact ih (b 0) (shift 1 b)
  | delay c d n p hs hr ih =>
    simp only [Experiment.run,execute_add,hs]
    exact ih (shift n b)

lemma bind (h : Implements M out c p) (q : α → Experiment β)
    (out' : β → Cfg Γ Q) (hq : ∀ a,Implements M out' (out a) (q a)) :
    Implements M out' c (p.bind q) := by
  induction h with
  | done a => exact hq a
  | read c f h ih => exact .read c _ ih
  | delay c d n p hs hr ih => exact .delay c d n _ hs ih

lemma padded_execution (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (b : Stream) :
    execute M n c b=out (p.run b).1 := by
  have hb : (p.run b).2 ≤ n:=(Experiment.run_cost p b).trans hn
  obtain ⟨k,hk⟩:=Nat.exists_eq_add_of_le hb
  rw [hk,execute_add,h.execution b]
  have he : out (p.run b).1=⟨none,(out (p.run b).1).tape⟩ := by
    cases e:out (p.run b).1 with
    | mk state tape =>
      have hstate := halt (p.run b).1
      rw [e] at hstate
      change state = none at hstate
      subst state
      rfl
  rw [he,execute_halted]

theorem fair_law (h : Implements M out c p) (halt : ∀ a,(out a).state=none)
    (n : ℕ) (hn : p.cost ≤ n) (f : Cfg Γ Q → ℚ) :
    average (fun b : Bits n=>f (execute M n c (extend b)))=p.mean (fun a=>f (out a)) := by
  simp_rw [h.padded_execution halt n hn]
  exact Experiment.average_run p (fun a=>f (out a)) n hn

end Implements
end MatchingFPRAS.PhysicalPost

end OAI
