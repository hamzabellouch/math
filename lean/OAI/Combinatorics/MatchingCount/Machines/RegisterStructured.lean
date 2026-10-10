import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.RegisterControl

namespace OAI

namespace MatchingFPRAS.RegisterStructured
open RegisterProc TreeData TreeMachine RegisterControl

variable {R : Type} [DecidableEq R]

inductive Select where | test | left | right | halt deriving DecidableEq, Inhabited
instance : Fintype Select := ⟨{.test,.left,.right,.halt},by intro s; cases s <;> simp⟩
def selectCode (i : R) (P Q : Proc (K R)) : Select → RegisterControl.Instr R Select
  | .test => .branch i .left .right
  | .left => .call P .halt
  | .right => .call Q .halt
  | .halt => .halt
def select (i : R) (P Q : Proc (K R)) : Proc (K R) := compile (selectCode i P Q)
lemma select_nil (i : R) (P Q : Proc (K R)) (E F : Env R) (n : ℕ)
    (hi : E i=.nil) (h : Exec P (encodeEnv E) (encodeEnv F) n) :
    Exec (select i P Q) (encodeEnv E) (encodeEnv F) (n+3) := by
  have hh : RegisterControl.Runs (selectCode i P Q) (some Select.halt) F F 1 :=
    Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
  have hl : RegisterControl.Runs (selectCode i P Q) (some Select.left) E F ((n+1)+1) :=
    Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ n h) hh
  have ht : RegisterControl.Runs (selectCode i P Q) (some Select.test) E F (1+((n+1)+1)) :=
    Runs.step _ _ _ _ _ _ _ (Effect.nilBranch E i _ _ hi) hl
  exact (compile_exec _ _ _ _ ht).mono (by omega)
lemma select_cons (i : R) (P Q : Proc (K R)) (E F : Env R) (n : ℕ) (x y : Data)
    (hi : E i=.cons x y) (h : Exec Q (encodeEnv E) (encodeEnv F) n) :
    Exec (select i P Q) (encodeEnv E) (encodeEnv F) (n+3) := by
  have hh : RegisterControl.Runs (selectCode i P Q) (some Select.halt) F F 1 :=
    Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
  have hr : RegisterControl.Runs (selectCode i P Q) (some Select.right) E F ((n+1)+1) :=
    Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ n h) hh
  have ht : RegisterControl.Runs (selectCode i P Q) (some Select.test) E F (1+((n+1)+1)) :=
    Runs.step _ _ _ _ _ _ _ (Effect.consBranch E i _ _ x y hi) hr
  exact (compile_exec _ _ _ _ ht).mono (by omega)

inductive Loop where | test | body | halt deriving DecidableEq, Inhabited
instance : Fintype Loop := ⟨{.test,.body,.halt},by intro l; cases l <;> simp⟩
def loopCode (i : R) (P : Proc (K R)) : Loop → RegisterControl.Instr R Loop
  | .test => .branch i .halt .body
  | .body => .call P .test
  | .halt => .halt
def loop (i : R) (P : Proc (K R)) : Proc (K R) := compile (loopCode i P)

lemma loop_exec (i : R) (P : Proc (K R)) (E : ℕ → Env R) (n B : ℕ)
    (hc : ∀ k<n, E k i ≠ .nil)
    (hb : ∀ k<n, Exec P (encodeEnv (E k)) (encodeEnv (E (k+1))) B)
    (he : E n i=.nil) :
    Exec (loop i P) (encodeEnv (E 0)) (encodeEnv (E n)) (n*(B+2)+2) := by
  have aux : ∀ n (E : ℕ → Env R), (∀ k<n,E k i≠.nil) →
      (∀ k<n,Exec P (encodeEnv (E k)) (encodeEnv (E (k+1))) B) → E n i=.nil →
      RegisterControl.Runs (loopCode i P) (some Loop.test) (E 0) (E n) (n*(B+2)+2) := by
    intro n
    induction n with
    | zero =>
      intro E _nonempty _body he
      have hh : RegisterControl.Runs (loopCode i P) (some Loop.halt) (E 0) (E 0) 1 :=
        Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
      simpa only [Nat.zero_mul,Nat.zero_add] using RegisterControl.Runs.step (M:=loopCode i P) Loop.test (E 0) (some Loop.halt) (E 0) (E 0) 1 1 (Effect.nilBranch _ i Loop.halt Loop.body he) hh
    | succ n ih =>
      intro E hc hb he
      have ht := ih (fun k=>E (k+1)) (fun k hk=>hc (k+1) (by omega))
        (fun k hk=>hb (k+1) (by omega)) he
      have hr : RegisterControl.Runs (loopCode i P) (some Loop.body) (E 0) (E (n+1))
          ((B+1)+(n*(B+2)+2)) :=
        Runs.step _ _ _ _ _ _ _ (Effect.call _ _ _ _ B (hb 0 (by omega))) ht
      cases hx : E 0 i with
      | nil => exact False.elim (hc 0 (by omega) hx)
      | cons x y =>
        have hh : RegisterControl.Runs (loopCode i P) (some Loop.test) (E 0) (E (n+1))
            (1+((B+1)+(n*(B+2)+2))) :=
          Runs.step _ _ _ _ _ _ _ (Effect.consBranch _ i _ _ x y hx) hr
        convert hh using 1; ring
  exact compile_exec _ _ _ _ (aux n E hc hb he)
end MatchingFPRAS.RegisterStructured

end OAI
