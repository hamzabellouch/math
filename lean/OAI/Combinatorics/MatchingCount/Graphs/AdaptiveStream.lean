import Mathlib
import OAI.Combinatorics.MatchingCount.Model

namespace OAI

namespace MatchingFPRAS.PhysicalStream
open Finset

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Stream := ℕ → Bool

def shift (n : ℕ) (b : Stream) : Stream := fun i => b (n+i)
@[simp] lemma shift_zero (b : Stream) : shift 0 b=b := by funext i; simp [shift]
def extend {n : ℕ} (b : Bits n) : Stream := fun i => if h : i<n then b ⟨i,h⟩ else false

def concat {n m : ℕ} (a : Bits n) (b : Bits m) : Bits (n+m) := Fin.append a b

def split (n m : ℕ) : Bits (n+m) ≃ Bits n × Bits m where
  toFun b := (fun i=>b (Fin.castAdd m i), fun j=>b (Fin.natAdd n j))
  invFun b := concat b.1 b.2
  left_inv b := by funext i; exact Fin.addCases (by simp [concat]) (by simp [concat]) i
  right_inv b := by ext i <;> simp [concat]

@[simp] lemma concat_left {n m : ℕ} (a : Bits n) (b : Bits m) (i : Fin n) :
    concat a b (Fin.castAdd m i)=a i := by simp [concat]
@[simp] lemma concat_right {n m : ℕ} (a : Bits n) (b : Bits m) (i : Fin m) :
    concat a b (Fin.natAdd n i)=b i := by simp [concat]

noncomputable def average {n : ℕ} (f : Bits n → ℚ) : ℚ :=
  (∑ b,f b)/(2:ℚ)^n

lemma average_const (n : ℕ) (a : ℚ) : average (fun _ : Bits n=>a)=a := by
  simp [average]

lemma average_add {n : ℕ} (f g : Bits n → ℚ) :
    average (fun b=>f b+g b)=average f+average g := by
  simp [average,sum_add_distrib,add_div]

lemma average_mul {n : ℕ} (a : ℚ) (f : Bits n → ℚ) :
    average (fun b=>a*f b)=a*average f := by
  simp [average,←mul_sum,mul_div_assoc]

lemma average_split {n m : ℕ} (f : Bits (n+m) → ℚ) :
    average f=average (fun a : Bits n=>average (fun b : Bits m=>f (concat a b))) := by
  unfold average
  have h : (∑ b : Bits (n+m),f b)=∑ a : Bits n,∑ b : Bits m,f (concat a b) := by
    calc
      _ = ∑ ab : Bits n × Bits m,f (concat ab.1 ab.2) :=
        Fintype.sum_equiv (split n m) f (fun ab=>f (concat ab.1 ab.2)) (fun b=>by
          change f b=f ((split n m).symm ((split n m) b))
          rw [Equiv.symm_apply_apply])
      _ = _ := Fintype.sum_prod_type _
  rw [h,←sum_div,pow_add,div_div]
  congr 1
  ring

lemma average_one (f : Bits 1 → ℚ) :
    average f=(f (fun _=>false)+f (fun _=>true))/2 := by
  have h : (∑ b : Bits 1,f b)=f (fun _=>false)+f (fun _=>true) := by
    let e : Bits 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
    have hh:=Fintype.sum_equiv e f (fun b=>f (fun _=>b)) (fun b=>by
      congr 1; funext i; exact congrArg b (Subsingleton.elim i default))
    simpa only [Fintype.sum_bool,add_comm] using hh
  simp only [average,h,pow_one]

lemma shift_extend_concat {n m : ℕ} (a : Bits n) (b : Bits m) (i : ℕ) (hi : i < m) :
    shift n (extend (concat a b)) i=extend b i := by
  have hni : n+i<n+m := Nat.add_lt_add_left hi n
  simp only [shift,extend,dite_eq_left hi,dite_eq_left hni]
  exact concat_right a b ⟨i,hi⟩

lemma extend_concat_zero {m : ℕ} (a : Bits 1) (b : Bits m) :
    extend (concat a b) 0=a 0 := by
  simp only [extend,dite_eq_left (by omega : 0<1+m)]
  exact concat_left a b 0

inductive Experiment (α : Type) where
  | done (a : α)
  | read (next : Bool → Experiment α)
  | delay (ticks : ℕ) (next : Experiment α)

namespace Experiment
variable {α β : Type}

def cost : Experiment α → ℕ
  | .done _ => 0
  | .read f => 1+max (cost (f false)) (cost (f true))
  | .delay n p => n+cost p

def run : Experiment α → Stream → α × ℕ
  | .done a,_ => (a,0)
  | .read f,b => let r := run (f (b 0)) (shift 1 b); (r.1,1+r.2)
  | .delay n p,b => let r := run p (shift n b); (r.1,n+r.2)

def mean : Experiment α → (α → ℚ) → ℚ
  | .done a,f => f a
  | .read p,f => (mean (p false) f+mean (p true) f)/2
  | .delay _ p,f => mean p f

lemma run_cost (p : Experiment α) (b : Stream) : (p.run b).2≤p.cost := by
  induction p generalizing b with
  | done a => rfl
  | read p ih =>
    simp only [run,cost]
    have h:=ih (b 0) (shift 1 b)
    cases hb : b 0 <;> simp only [hb] at h <;> omega
  | delay n p ih => exact Nat.add_le_add_left (ih (shift n b)) n

lemma run_congr (p : Experiment α) (a b : Stream)
    (h : ∀ i,i<p.cost → a i=b i) : p.run a=p.run b := by
  induction p generalizing a b with
  | done x => rfl
  | read p ih =>
    have h0 : a 0=b 0 := h 0 (by simp [cost])
    simp only [run,h0]
    have hh : run (p (b 0)) (shift 1 a)=run (p (b 0)) (shift 1 b) := by
      apply ih
      intro i hi
      apply h
      cases he : b 0 <;> simp only [he] at hi <;> simp only [cost] <;> omega
    rw [hh]
  | delay n p ih =>
    simp only [run]
    have hh : run p (shift n a)=run p (shift n b) := by
      apply ih
      intro i hi
      exact h (n+i) (by simp only [cost]; omega)
    rw [hh]

lemma run_suffix {n m : ℕ} (p : Experiment α) (h : p.cost ≤ m)
    (a : Bits n) (b : Bits m) :
    p.run (shift n (extend (concat a b)))=p.run (extend b) := by
  apply run_congr
  intro i hi
  exact shift_extend_concat a b i (lt_of_lt_of_le hi h)

theorem average_run (p : Experiment α) (f : α → ℚ) (n : ℕ) (hn : p.cost≤n) :
    average (fun b : Bits n=>f (p.run (extend b)).1)=p.mean f := by
  induction p generalizing n with
  | done a => exact average_const n (f a)
  | delay k p ih =>
    have hk : k≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm : p.cost ≤ m := by simpa only [cost,Nat.add_le_add_iff_left] using hn
    rw [average_split]
    have hrun (a : Bits k) (b : Bits m) :
        f ((delay k p).run (extend (concat a b))).1=f (p.run (extend b)).1 := by
      simp only [run,run_suffix p hm a b]
    simp_rw [hrun,ih m hm]
    exact average_const k (p.mean f)
  | read p ih =>
    have hk : 1≤n := by simp only [cost] at hn; omega
    obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hk
    have hm (b : Bool) : (p b).cost ≤ m := by
      simp only [cost,Nat.add_le_add_iff_left] at hn
      cases b <;> omega
    rw [average_split]
    have hrun (a : Bits 1) (b : Bits m) :
        f ((read p).run (extend (concat a b))).1=f ((p (a 0)).run (extend b)).1 := by
      simp only [run,extend_concat_zero,run_suffix _ (hm (a 0)) a b]
    simp_rw [hrun,ih _ m (hm _)]
    rw [average_one]
    rfl

def bind : Experiment α → (α → Experiment β) → Experiment β
  | .done a,f => f a
  | .read p,f => .read (fun b=>(p b).bind f)
  | .delay n p,f => .delay n (p.bind f)

lemma mean_bind (p : Experiment α) (q : α → Experiment β) (f : β → ℚ) :
    (p.bind q).mean f=p.mean (fun a=>(q a).mean f) := by
  induction p with
  | done a => rfl
  | read p ih => simp [bind,mean,ih]
  | delay n p ih => exact ih

lemma run_bind (p : Experiment α) (q : α → Experiment β) (b : Stream) :
    (p.bind q).run b=
      let r:=p.run b
      let s:=(q r.1).run (shift r.2 b)
      (s.1,r.2+s.2) := by
  induction p generalizing b with
  | done a => simp [bind,run]
  | read p ih =>
    simp only [bind,run,ih]
    have hs (n : ℕ) : shift n (shift 1 b)=shift (1+n) b := by
      funext i; simp [shift,Nat.add_assoc]
    simp only [hs,Nat.add_assoc]
  | delay n p ih =>
    simp only [bind,run,ih]
    have hs (m : ℕ) : shift m (shift n b)=shift (n+m) b := by
      funext i; simp [shift,Nat.add_assoc]
    simp only [hs,Nat.add_assoc]

lemma cost_bind_le (p : Experiment α) (q : α → Experiment β) (N : ℕ)
    (hq : ∀ a,(q a).cost ≤ N) : (p.bind q).cost ≤ p.cost+N := by
  induction p with
  | done a => simpa only [bind,cost,Nat.zero_add] using hq a
  | read p ih =>
    simp only [bind,cost]
    have h0:=ih false
    have h1:=ih true
    omega
  | delay n p ih => simpa only [bind,cost,Nat.add_assoc] using Nat.add_le_add_left ih n

def map (f : α → β) (p : Experiment α) : Experiment β := p.bind (fun a=>.done (f a))

@[simp] lemma cost_map (f : α → β) (p : Experiment α) : (p.map f).cost=p.cost := by
  induction p with
  | done a => rfl
  | read p ih => simp only [map,bind,cost]; change 1+max ((p false).map f).cost ((p true).map f).cost=_; rw [ih false,ih true]
  | delay n p ih => change n+(p.map f).cost=n+p.cost; rw [ih]

lemma run_map (f : α → β) (p : Experiment α) (b : Stream) :
    (p.map f).run b=(f (p.run b).1,(p.run b).2) := by simp [map,run_bind,run]

lemma mean_map (f : α → β) (p : Experiment α) (g : β → ℚ) :
    (p.map f).mean g=p.mean (fun a=>g (f a)) := by simp [map,mean_bind,mean]

def word : (n : ℕ) → Experiment (Bits n)
  | 0 => .done Fin.elim0
  | n+1 => .read (fun b=>(word n).map (Fin.cons b))

@[simp] lemma cost_word (n : ℕ) : (word n).cost=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [word,cost,cost_map,ih,max_self]; omega

lemma run_word (n : ℕ) (b : Stream) :
    (word n).run b=((fun i : Fin n=>b i),n) := by
  induction n generalizing b with
  | zero => exact Prod.ext (funext (fun i=>Fin.elim0 i)) rfl
  | succ n ih =>
    simp only [word,run,run_map,ih,shift]
    congr 1
    · funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · rfl
      · simp only [Fin.cons_succ,Fin.val_succ]; congr 1; omega
    · omega

lemma mean_word (n : ℕ) (f : Bits n → ℚ) : (word n).mean f=average f := by
  rw [←average_run (word n) f n (by rw [cost_word])]
  congr 1
  funext b
  rw [run_word]
  congr 1
  funext i
  simp [extend,i.isLt]

theorem adaptive_word_law (p : Experiment α) (width : α → ℕ)
    (q : (a : α) → Bits (width a) → Experiment β) (f : β → ℚ)
    (n : ℕ) (hn : (p.bind (fun a=>(word (width a)).bind (q a))).cost ≤ n) :
    average (fun b : Bits n=> f ((p.bind (fun a=>(word (width a)).bind (q a))).run (extend b)).1)=
      p.mean (fun a=>average (fun w=>(q a w).mean f)) := by
  rw [average_run _ _ _ hn,mean_bind]
  congr 1
  funext a
  rw [mean_bind,mean_word]

end Experiment
end MatchingFPRAS.PhysicalStream

end OAI
