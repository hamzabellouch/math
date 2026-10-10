import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeList
import OAI.Combinatorics.MatchingCount.Machines.TreePartialChoice

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {B : Type} [Codec B]

def predecessor : Realizer (fun n : ℕ=>n-1) := composition (pair identity (constant 1)) subtract

def countDown (f : ℕ×B → B) : ℕ → B → B
  | 0,b => b
  | n+1,b => countDown f n (f (n+1,b))

namespace Repeat
open RegisterControl (Instr Runs Effect)

inductive Point where | loop | check | rebuild | body | halt
  deriving DecidableEq, Inhabited
instance : Fintype Point := ⟨{.loop,.check,.rebuild,.body,.halt},by intro p; cases p <;> simp⟩
def next (f : ℕ×B → B) (nb : ℕ×B) : ℕ×B := (nb.1-1,f nb)
def nextRealizer {f : ℕ×B → B} (F : Realizer f) : Realizer (next f) :=
  pair (composition first predecessor) F

def code (P : Proc (K Reg)) : Point → RegisterControl.Instr Reg Point
  | .loop => .call (TreeFunction.split 1 0 (by decide)) .check
  | .check => .branch 1 .halt .rebuild
  | .rebuild => .call (TreeFunction.cons 1 0 (by decide)) .body
  | .body => .call P .loop
  | .halt => .halt

def cost (f : ℕ×B → B) (t : ℕ×B → ℕ) : ℕ → B → ℕ
  | 0,_ => 10
  | n+1,b => t (n+1,b)+4*TreeFunction.size (nat (n+1))+12+cost f t n (f (n+1,b))

lemma runs {f : ℕ×B → B} (F : Realizer f) (n : ℕ) (b : B) (s : Data) :
    Runs (code (nextRealizer F).program) (some Point.loop) (env (encode (n,b)) .nil s)
      (env (encode (countDown f n b)) .nil s) (cost f (nextRealizer F).cost n b) := by
  induction n generalizing b with
  | zero =>
    have hh : Runs (code (nextRealizer F).program) (some Point.halt) (env (encode b) .nil s)
        (env (encode b) .nil s) 1 := Runs.step _ _ _ _ _ 0 1 (Effect.halt _) (Runs.done _)
    have hc : Runs (code (nextRealizer F).program) (some Point.check) (env (encode b) .nil s)
        (env (encode b) .nil s) 2 := Runs.step _ _ _ _ _ 1 1 (Effect.nilBranch _ 1 _ _ rfl) hh
    have hs := split10 (nat 0) (encode b) .nil s
    change Exec _ _ _ 7 at hs
    exact Runs.step _ _ _ _ _ 2 8 (Effect.call _ _ _ _ 7 hs) hc
  | succ n ih =>
    have hr:=ih (f (n+1,b))
    have hb:=(nextRealizer F).correct (n+1,b) s
    have he : next f (n+1,b)=(n,f (n+1,b)) := by simp [next]
    change Exec _ _ (encodeEnv (env (encode (next f (n+1,b))) .nil s)) _ at hb
    rw [he] at hb
    let c := cost f (nextRealizer F).cost n (f (n+1,b))
    let t := (nextRealizer F).cost (n+1,b)
    let d := TreeFunction.size (nat (n+1))
    have hbody : Runs (code (nextRealizer F).program) (some Point.body) (env (encode (n+1,b)) .nil s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((t+1)+c) :=
      Runs.step _ _ _ _ _ c (t+1) (Effect.call _ _ _ _ t hb) hr
    have hcons:=cons10 (encode b) (nat (n+1)) s
    have hreb : Runs (code (nextRealizer F).program) (some Point.rebuild) (env (encode b) (nat (n+1)) s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((2*d+4)+((t+1)+c)) :=
      Runs.step _ _ _ _ _ _ (2*d+4) (Effect.call _ _ _ _ (2*d+3) hcons) hbody
    have hn : ∃ a z,nat (n+1)=.cons a z := by
      cases he : (n+1).bits with
      | nil =>
        have hv:=StackAddition.value_bits (n+1)
        rw [he] at hv
        simp [StackAddition.value] at hv
      | cons a z => exact ⟨bit a,bits z,by change bits (n+1).bits=Data.cons (bit a) (bits z); rw [he]; rfl⟩
    obtain ⟨a,z,ha⟩:=hn
    have hc : Runs (code (nextRealizer F).program) (some Point.check) (env (encode b) (nat (n+1)) s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) (1+((2*d+4)+((t+1)+c))) :=
      Runs.step _ _ _ _ _ _ 1 (Effect.consBranch _ 1 _ _ a z ha) hreb
    have hs:=split10 (nat (n+1)) (encode b) .nil s
    have hs' := hs.mono (show TreeFunction.size Data.nil+2*d+4 ≤ 2*d+5 by simp only [size_nil]; omega)
    have hh : Runs (code (nextRealizer F).program) (some Point.loop) (env (encode (n+1,b)) .nil s)
        (env (encode (countDown f n (f (n+1,b)))) .nil s) ((2*d+6)+(1+((2*d+4)+((t+1)+c)))) :=
      Runs.step _ _ _ _ _ _ (2*d+6) (Effect.call _ _ _ _ (2*d+5) hs') hc
    convert hh using 1
    all_goals try rfl
    simp only [cost,d,t,c]
    omega
end Repeat

def iterateDown {f : ℕ×B → B} (F : Realizer f) : Realizer (fun nb : ℕ×B=>countDown f nb.1 nb.2) :=
  ⟨RegisterControl.compile (Repeat.code (Repeat.nextRealizer F).program),
    fun nb=>Repeat.cost f (Repeat.nextRealizer F).cost nb.1 nb.2,
    fun nb s=>RegisterControl.compile_exec _ _ _ _ (Repeat.runs F nb.1 nb.2 s)⟩

def rangeStep (x : ℕ×List ℕ) : List ℕ := (x.1-1)::x.2
def rangeStepRealizer : Realizer rangeStep := composition (pair (composition first predecessor) second) listCons
lemma countDown_range (n : ℕ) (as : List ℕ) : countDown rangeStep n as=List.range n++as := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih => simp [countDown,rangeStep,ih,List.range_succ,List.append_assoc]
def range : Realizer List.range :=
  (composition (pair identity (constant ([] : List ℕ))) (iterateDown rangeStepRealizer)).congr (by
    intro n; simp [countDown_range])

omit [Codec B] in
lemma Repeat.cost_bound {f : ℕ×B → B} (t : ℕ×B → ℕ) (I : ℕ → B → Prop) (N : ℕ) (b : B)
    (T S : ℕ) (hb : I N b)
    (hstep : ∀ n<N,∀ z,I (n+1) z → I n (f (n+1,z)) ∧ t (n+1,z) ≤ T)
    (hsize : ∀ n<N,TreeFunction.size (nat (n+1)) ≤ S) :
    Repeat.cost f t N b ≤ N*(T+4*S+12)+10 := by
  induction N generalizing b with
  | zero => simp [cost]
  | succ n ih =>
    have hs:=hstep n (by omega) b hb
    have ht:=ih (f (n+1,b)) hs.1 (fun k hk z hz=>hstep k (by omega) z hz) (fun k hk=>hsize k (by omega))
    have hz:=hsize n (by omega)
    simp only [cost]
    nlinarith
end MatchingFPRAS.TreeTyped

end OAI
