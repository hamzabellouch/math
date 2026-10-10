import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeMachine

namespace OAI

namespace MatchingFPRAS.TreeFunction
open TreeData TreeMachine RegisterProc

abbrev Reg := Fin 10
def env (x y s : Data) : Env Reg := fun i=>if i=0 then x else if i=1 then y else if i=2 then s else .nil
@[simp] lemma env0 (x y s : Data) : env x y s 0=x := rfl
@[simp] lemma env1 (x y s : Data) : env x y s 1=y := rfl
@[simp] lemma env2 (x y s : Data) : env x y s 2=s := rfl
def size (x : Data) : ℕ := (TreeData.encode x).length
@[simp] lemma size_nil : size .nil=1 := rfl
@[simp] lemma size_cons (x y : Data) : size (.cons x y)=size x+size y+1 := by
  simp [size,TreeData.encode]

def Realizes (P : Proc (K Reg)) (f : Data → Data) (t : Data → ℕ) : Prop :=
  ∀ x s,Exec P (encodeEnv (env x .nil s)) (encodeEnv (env (f x) .nil s)) (t x)

lemma env_ext {x y s a b c : Data} (hx : x=a) (hy : y=b) (hs : s=c) : env x y s=env a b c := by
  rw [hx,hy,hs]
lemma env_update0 (x y s a : Data) : Function.update (env x y s) 0 a=env a y s := by
  funext i; fin_cases i <;> simp [env]
lemma env_update1 (x y s a : Data) : Function.update (env x y s) 1 a=env x a s := by
  funext i; fin_cases i <;> simp [env]
lemma env_update2 (x y s a : Data) : Function.update (env x y s) 2 a=env x y a := by
  funext i; fin_cases i <;> simp [env]
attribute [simp] env_update0 env_update1 env_update2

def clear (i : Reg) : Proc (K Reg) := procedure (.nil i ())
def copy (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.copy i j h ())
def cons (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.cons i j h ())
def split (i j : Reg) (h : i≠j) : Proc (K Reg) := procedure (.split i j h ())

lemma copy01 (x y s : Data) :
    Exec (copy 0 1 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env x x s)) (size y+3*size x+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,copy] using copy_exec (env x y s) 0 1 (by decide) ()
lemma copy10 (x y s : Data) :
    Exec (copy 1 0 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env y y s)) (size x+3*size y+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,copy] using copy_exec (env x y s) 1 0 (by decide) ()
lemma cons12 (x y s : Data) :
    Exec (cons 1 2 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env x .nil (.cons y s))) (2*size y+3) := by
  simpa only [putPair,env_update1,env_update2,env1,env2,size,cons] using cons_exec (env x y s) 1 2 (by decide) ()
lemma cons02 (x y s : Data) :
    Exec (cons 0 2 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env .nil y (.cons x s))) (2*size x+3) := by
  simpa only [putPair,env_update0,env_update2,env0,env2,size,cons] using cons_exec (env x y s) 0 2 (by decide) ()
lemma cons10 (x y s : Data) :
    Exec (cons 1 0 (by decide)) (encodeEnv (env x y s)) (encodeEnv (env (.cons y x) .nil s)) (2*size y+3) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,cons] using cons_exec (env x y s) 1 0 (by decide) ()
lemma split12 (x y a s : Data) :
    Exec (split 1 2 (by decide)) (encodeEnv (env x y (.cons a s))) (encodeEnv (env x a s)) (size y+2*size a+4) := by
  simpa only [putPair,env_update1,env_update2,env1,env2,size,split] using split_exec (env x y (.cons a s)) 1 2 (by decide) () a s rfl
lemma split10 (x y z s : Data) :
    Exec (split 1 0 (by decide)) (encodeEnv (env (.cons x y) z s)) (encodeEnv (env y x s)) (size z+2*size x+4) := by
  simpa only [putPair,env_update0,env_update1,env0,env1,size,split] using split_exec (env (.cons x y) z s) 1 0 (by decide) () x y rfl
lemma clear0 (x y s : Data) :
    Exec (clear 0) (encodeEnv (env x y s)) (encodeEnv (env .nil y s)) (size x+2) := by
  simpa only [env_update0,env0,size,clear] using nil_exec (env x y s) 0 ()
lemma clear1 (x y s : Data) :
    Exec (clear 1) (encodeEnv (env x y s)) (encodeEnv (env x .nil s)) (size y+2) := by
  simpa only [env_update1,env1,size,clear] using nil_exec (env x y s) 1 ()

lemma realizes_seq {P Q : Proc (K Reg)} {f g : Data → Data} {t u : Data → ℕ}
    (hP : Realizes P f t) (hQ : Realizes Q g u) :
    Realizes (seq P Q) (g ∘ f) (fun x=>t x+u (f x)) := fun x s=>(hP x s).seq (hQ (f x) s)

def pair (P Q : Proc (K Reg)) : Proc (K Reg) :=
  seq (copy 0 1 (by decide)) (seq (cons 1 2 (by decide)) (seq P
    (seq (split 1 2 (by decide)) (seq (cons 0 2 (by decide))
      (seq (copy 1 0 (by decide)) (seq (clear 1) (seq Q
        (seq (split 1 2 (by decide)) (cons 1 0 (by decide))))))))))

lemma realizes_pair {P Q : Proc (K Reg)} {f g : Data → Data} {t u : Data → ℕ}
    (hP : Realizes P f t) (hQ : Realizes Q g u) :
    Realizes (pair P Q) (fun x=>.cons (f x) (g x))
      (fun x=>t x+u x+11*size x+6*size (f x)+31) := by
  intro x s
  have h1:=copy01 x .nil s
  have h2:=cons12 x x s
  have h3:=hP x (.cons x s)
  have h4:=split12 (f x) .nil x s
  have h5:=cons02 (f x) x s
  have h6:=copy10 .nil x (.cons (f x) s)
  have h7:=clear1 x x (.cons (f x) s)
  have h8:=hQ x (.cons (f x) s)
  have h9:=split12 (g x) .nil (f x) s
  have h10:=cons10 (g x) (f x) s
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq h10))))))))).mono
  simp only [size_nil]
  omega
end MatchingFPRAS.TreeFunction

end OAI
