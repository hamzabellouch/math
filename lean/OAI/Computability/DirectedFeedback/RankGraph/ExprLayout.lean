import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.Store

namespace OAI


namespace DirectedFeedback.BoundedExpr
open StackDSL StackDSL.Code StackDSL.Ops

structure Layout (r : Nat) where
  input : Nat
  args : Fin r → Nat
  output : Nat
  fresh : Nat
  input_lt : input < fresh
  args_lt : ∀ i, args i < fresh
  output_lt : output < fresh
  input_ne : input ≠ output
  args_ne : ∀ i, args i ≠ output

namespace Layout
variable {r : Nat} (L : Layout r)

def temp (j d : Nat) (h : j < d) : Layout r where
  input := L.input
  args := L.args
  output := L.fresh+j
  fresh := L.fresh+d
  input_lt := by have := L.input_lt; omega
  args_lt := by intro i; have := L.args_lt i; omega
  output_lt := by omega
  input_ne := by have := L.input_lt; omega
  args_ne := by intro i; have := L.args_lt i; omega

def sumBody : Layout (r+1) where
  input := L.input
  args := Fin.cons (L.fresh+1) L.args
  output := L.output
  fresh := L.fresh+2
  input_lt := by have := L.input_lt; omega
  args_lt := by intro i; refine Fin.cases ?_ (fun i => ?_) i
                · simp
                · simpa using (L.args_lt i).trans (by omega : L.fresh < L.fresh+2)
  output_lt := by have := L.output_lt; omega
  input_ne := L.input_ne
  args_ne := by intro i; refine Fin.cases ?_ (fun i => ?_) i
                · simp; have := L.output_lt; omega
                · simpa using L.args_ne i

structure Ready (s : Store Nat Bool) (input : List Bool) (args : Fin r → Nat) : Prop where
  input_eq : s.tape L.input = input
  args_eq : ∀ i, s.tape (L.args i) = List.replicate (args i) true
  clean : ∀ k, L.fresh ≤ k → s.tape k = []

namespace Ready
variable {L : Layout r} {s : Store Nat Bool} {x : List Bool} {a : Fin r → Nat}

 theorem flag (h : L.Ready s x a) (b : Bool) : L.Ready (s.flag b) x a := ⟨h.input_eq,h.args_eq,h.clean⟩

 theorem temp (h : L.Ready s x a) (j d : Nat) (hjd : j<d) : (L.temp j d hjd).Ready s x a where
  input_eq := h.input_eq
  args_eq := h.args_eq
  clean := by intro k hk; apply h.clean; change L.fresh+d ≤ k at hk; omega

 theorem put (h : L.Ready s x a) (k : Nat) (v : List Bool) (hk : k<L.fresh)
    (hki : L.input ≠ k) (hka : ∀ i, L.args i ≠ k) : L.Ready (s.put k v) x a where
  input_eq := by simpa [hki] using h.input_eq
  args_eq := by intro i; simpa [hka i] using h.args_eq i
  clean := by intro j hj; rw [Store.put_tape_other _ (by omega)]; exact h.clean j hj

 theorem output (h : L.Ready s x a) (v : List Bool) : L.Ready (s.put L.output v) x a :=
  h.put L.output v L.output_lt L.input_ne L.args_ne

 theorem temp_put (h : L.Ready s x a) (j d k : Nat) (hjd : j<d) (hkd : k<d) (v : List Bool) :
    (L.temp j d hjd).Ready (s.put (L.fresh+k) v) x a := by
  apply (h.temp j d hjd).put (L.fresh+k) v
  · change L.fresh+k < L.fresh+d; omega
  · change L.input ≠ L.fresh+k; have := L.input_lt; omega
  · intro i; change L.args i ≠ L.fresh+k; have := L.args_lt i; omega

end Ready
end Layout

namespace Expr

def Correct {r : Nat} (e : Expr r) : Prop :=
  ∀ (L : Layout r) (x : List Bool) (a : Fin r → Nat) (s : Store Nat Bool), L.Ready s x a →
    (e.compile L.input L.args L.output L.fresh).Exec s (e.cost x a)
      ((s.put L.output (List.replicate (e.eval x a) true ++ s.tape L.output)).flag false)

theorem correct_lit {r : Nat} (n : Nat) : Correct (Expr.lit (r := r) n) := by
  intro L x a s h
  exact pushN_run L.output n s

theorem correct_arg {r : Nat} (i : Fin r) : Correct (Expr.arg i) := by
  intro L x a s h
  have ht := h.clean L.fresh (by omega)
  have hr := copy_run (L.args i) L.output L.fresh (L.args_ne i)
    (Nat.ne_of_lt (L.args_lt i)) (Nat.ne_of_lt L.output_lt) s ht
  simpa [h.args_eq i,eval,cost] using hr

theorem correct_length {r : Nat} : Correct (Expr.length (r := r)) := by
  intro L x a s h
  have ht := h.clean L.fresh (by omega)
  have hr := count_run L.input L.output L.fresh L.input_ne
    (Nat.ne_of_lt L.input_lt) (Nat.ne_of_lt L.output_lt) s ht
  simpa [h.input_eq,eval,cost] using hr

theorem correct_add {r : Nat} {e f : Expr r} (he : e.Correct) (hf : f.Correct) : (e.add f).Correct := by
  intro L x a s h
  have h1 := he L x a s h
  have h2 := hf L x a _ ((h.output (List.replicate (e.eval x a) true ++ s.tape L.output)).flag false)
  have hh := Exec.seq h1 h2
  convert hh using 1 <;> try rfl
  simp only [eval,Store.put_tape_same,Store.flag_tape,Store.put_flag,Store.put_put,Store.flag_flag]
  rw [← List.append_assoc,← List.replicate_add, Nat.add_comm]

end Expr
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

theorem correct_mul {r : Nat} {e g : Expr r} (he : e.Correct) (hg : g.Correct) : (e.mul g).Correct := by
  intro L x a s h
  let u := e.eval x a
  let v := g.eval x a
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have h2o : L.fresh+2 ≠ L.output := by have := L.output_lt; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have hs2 := h.clean (L.fresh+2) (by omega)
  have h1 := he (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  have h2 := hg (L.temp 1 2 (by omega)) x a
    ((s.put L.fresh (List.replicate u true)).flag false)
    ((h.temp_put 1 2 0 (by omega) (by omega) (List.replicate u true)).flag false)
  simp only [Layout.temp,Store.flag_tape,Store.put_tape_other _ (by omega : L.fresh+1 ≠ L.fresh),
    hs1,List.append_nil,Store.put_flag,Store.flag_flag] at h2
  let states := fun i : Nat =>
    ((((s.put (L.fresh+1) (List.replicate v true)).put L.fresh (List.replicate (u-i) true)).put
      L.output (List.replicate (i*v) true ++ s.tape L.output)).flag false)
  have hp : ∀ i, (copy (L.fresh+1) L.output (L.fresh+2)).Exec
      ((states i).put L.fresh (List.replicate (u-(i+1)) true)) (5*v+4) (states (i+1)) := by
    intro i
    have hr := copy_run (L.fresh+1) L.output (L.fresh+2) h1o (by omega) (by omega : L.output ≠ L.fresh+2)
      ((states i).put L.fresh (List.replicate (u-(i+1)) true)) (by simp [states,hs2,h2o])
    have hb : (((states i).put L.fresh (List.replicate (u-(i+1)) true)).tape (L.fresh+1)) =
        List.replicate v true := by simp [states,h1o]
    rw [hb,List.length_replicate] at hr
    convert hr using 1
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output
    · subst k
      simp only [states,Store.flag_tape,Store.put_tape_same,Store.put_tape_other _ (Ne.symm hfo)]
      rw [← List.append_assoc,← List.replicate_add]
      congr 2
      ring
    · by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
        simp_all [states,Store.put,Store.flag]
  have hlo := scan_indexed L.fresh (copy (L.fresh+1) L.output (L.fresh+2)) u states
    (fun _ => 5*v+4) (by intro i hi; simp [states,hfo]) (by intro i hi; exact hp i)
  have hstart : states 0 = (((s.put L.fresh (List.replicate u true)).put
      (L.fresh+1) (List.replicate v true)).flag false) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output <;> by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hstart] at hlo
  have hc := clear_run (L.fresh+1) (states u)
  have hcval : (states u).tape (L.fresh+1) = List.replicate v true := by simp [states,h1o]
  rw [hcval,List.length_replicate] at hc
  have hend : (states u).put (L.fresh+1) [] =
      (s.put L.output (List.replicate (u*v) true ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output <;> by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hend] at hc
  have hh := Exec.seq h1 (Exec.seq h2 (Exec.seq hlo hc))
  convert hh using 1 <;> try rfl
  simp only [cost,Finset.sum_const,Finset.card_range,smul_eq_mul]
  dsimp [u,v]
  ring

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops

theorem correct_sub {r : Nat} {e g : Expr r} (he : e.Correct) (hg : g.Correct) : (e.sub g).Correct := by
  intro L x a s h
  let u := e.eval x a
  let v := g.eval x a
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have h1 := he (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  have h2 := hg (L.temp 1 2 (by omega)) x a
    ((s.put L.fresh (List.replicate u true)).flag false)
    ((h.temp_put 1 2 0 (by omega) (by omega) (List.replicate u true)).flag false)
  simp only [Layout.temp,Store.flag_tape,Store.put_tape_other _ (by omega : L.fresh+1 ≠ L.fresh),
    hs1,List.append_nil,Store.put_flag,Store.flag_flag] at h2
  have hr := subtract_run L.fresh (L.fresh+1) (by omega) u v (s.flag false)
  simp only [Store.put_flag] at hr
  have ht := transfer_run L.fresh L.output hfo
    (((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false)
  have hv : (((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false).tape L.fresh =
      List.replicate (u-v) true := by simp
  rw [hv,List.length_replicate,List.reverse_replicate] at ht
  have hend : (((((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false).put L.fresh []).put
      L.output (List.replicate (u-v) true ++
        (((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false).tape L.output)).flag false =
      (s.put L.output (List.replicate (u-v) true ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output <;> by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
      simp_all [Store.put,Store.flag]
  rw [hend] at ht
  have hh := Exec.seq h1 (Exec.seq h2 (Exec.seq hr ht))
  convert hh using 1 <;> try rfl
  dsimp [cost,u,v]
  omega

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

theorem correct_sum {r : Nat} {b : Expr r} {e : Expr (r+1)}
    (hb : b.Correct) (he : e.Correct) : (b.sum e).Correct := by
  intro L x a s h
  let n := b.eval x a
  let sums := fun i => ∑ j ∈ Finset.range i, e.eval x (Fin.cons j a)
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have hfi : L.input ≠ L.fresh := Nat.ne_of_lt L.input_lt
  have h1i : L.input ≠ L.fresh+1 := by have := L.input_lt; omega
  have hfa : ∀ j, L.args j ≠ L.fresh := fun j => Nat.ne_of_lt (L.args_lt j)
  have h1a : ∀ j, L.args j ≠ L.fresh+1 := by intro j; have := L.args_lt j; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have h1 := hb (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let states := fun i =>
    ((((s.put (L.fresh+1) (List.replicate i true)).put L.fresh (List.replicate (n-i) true)).put
      L.output (List.replicate (sums i) true ++ s.tape L.output)).flag false)
  have hrdy : ∀ i, L.sumBody.Ready ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      x (Fin.cons i a) := by
    intro i
    constructor
    · simp [states,Layout.sumBody,hfi,h1i,L.input_ne,h.input_eq]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [states,Layout.sumBody,h1o]
      · simp [states,Layout.sumBody,hfa,h1a,L.args_ne,h.args_eq]
    · intro k hk
      change L.fresh+2 ≤ k at hk
      have hk0 : k≠L.fresh := by omega
      have hk1 : k≠L.fresh+1 := by omega
      have hko : k≠L.output := by have := L.output_lt; omega
      simp [states,hk0,hk1,hko,h.clean k (by omega)]
  have hp : ∀ i, (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2))
      (push (L.fresh+1) true)).Exec
      ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      (e.cost x (Fin.cons i a)+1) (states (i+1)) := by
    intro i
    have hbody := he L.sumBody x (Fin.cons i a)
      ((states i).put L.fresh (List.replicate (n-(i+1)) true)) (hrdy i)
    have hpush := push_run ((((states i).put L.fresh (List.replicate (n-(i+1)) true)).put L.output
      (List.replicate (e.eval x (Fin.cons i a)) true ++
        ((states i).put L.fresh (List.replicate (n-(i+1)) true)).tape L.output)).flag false)
      (L.fresh+1) true
    have hh := Exec.seq hbody hpush
    convert hh using 1 <;> try rfl
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output
    · subst k
      simp only [states,Store.flag_tape,Store.put_tape_same,Store.put_tape_other _ (Ne.symm hfo),
        Store.put_tape_other _ (Ne.symm h1o)]
      rw [← List.append_assoc,← List.replicate_add]
      congr 2
      simp only [sums,Finset.sum_range_succ]
      omega
    · by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
        simp_all [states,Store.put,Store.flag,List.replicate_succ]
  have hlo := scan_indexed L.fresh
    (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2)) (push (L.fresh+1) true))
    n states (fun i => e.cost x (Fin.cons i a)+1)
    (by intro i hi; simp [states,hfo]) (by intro i hi; exact hp i)
  have hstart : states 0 = (s.put L.fresh (List.replicate n true)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,sums,Store.put,Store.flag]
  rw [hstart] at hlo
  have hc := clear_run (L.fresh+1) (states n)
  have hcval : (states n).tape (L.fresh+1) = List.replicate n true := by simp [states,h1o]
  rw [hcval,List.length_replicate] at hc
  have hend : (states n).put (L.fresh+1) [] =
      (s.put L.output (List.replicate (sums n) true ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hend] at hc
  have hh := Exec.seq h1 (Exec.seq hlo hc)
  convert hh using 1 <;> try rfl
  simp only [cost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  dsimp [n]
  omega

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops

theorem terminal_run (output : Nat) (s : Store Nat Bool) :
    (Code.seq (.branch id (push output true) idle) reset).Exec s 3
      ((s.put output (List.replicate (if s.state then 1 else 0) true ++ s.tape output)).flag false) := by
  cases hb : s.state with
  | false =>
    have h1 := Exec.branch_false (f := id) (c := push output true) (d := idle) hb (idle_run s)
    have h2 := Exec.seq h1 (reset_run s)
    simpa [hb] using h2
  | true =>
    have h1 := Exec.branch_true (f := id) (c := push output true) (d := idle) hb (push_run s output true)
    have h2 := Exec.seq h1 (reset_run _)
    simpa [hb] using h2

theorem correct_zero {r : Nat} {e : Expr r} (he : e.Correct) : e.zero.Correct := by
  intro L x a s h
  let u := e.eval x a
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have hs0 := h.clean L.fresh (by omega)
  have h1 := he (L.temp 0 1 (by omega)) x a s (h.temp 0 1 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let s1 := (s.put L.fresh (List.replicate u true)).flag false
  have hp : (Code.atom (.peek L.fresh (fun _ x => x.isNone))).Exec s1 1
      ((s.put L.fresh (List.replicate u true)).flag (decide (u=0))) := by
    convert Exec.atom (.peek L.fresh (fun _ x => x.isNone)) s1 using 1
    dsimp [s1,Prim.run,Store.put,Store.flag]
    cases u <;> simp
  have hc := clear_run L.fresh ((s.put L.fresh (List.replicate u true)).flag (decide (u=0)))
  simp only [Store.flag_tape,Store.put_tape_same,List.length_replicate,Store.put_flag,Store.put_put] at hc
  have hz : s.put L.fresh [] = s := by rw [← hs0,Store.put_self]
  rw [hz] at hc
  have ht := terminal_run L.output (s.flag (decide (u=0)))
  have hh := Exec.seq h1 (Exec.seq hp (Exec.seq hc ht))
  convert hh using 1 <;> try rfl
  · dsimp [cost,u]; omega
  · simp [eval,u]

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops

theorem correct_bit {r : Nat} {e : Expr r} (he : e.Correct) : e.bit.Correct := by
  intro L x a s h
  let u := e.eval x a
  have hfi : L.input ≠ L.fresh := Nat.ne_of_lt L.input_lt
  have h1i : L.input ≠ L.fresh+1 := by have := L.input_lt; omega
  have h2i : L.input ≠ L.fresh+2 := by have := L.input_lt; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have hs2 := h.clean (L.fresh+2) (by omega)
  have h1 := he (L.temp 0 1 (by omega)) x a s (h.temp 0 1 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  have hcopy := copy_run L.input (L.fresh+1) (L.fresh+2) h1i h2i (by omega)
    ((s.put L.fresh (List.replicate u true)).flag false) (by simp [hs2])
  simp only [Store.flag_tape,Store.put_tape_other _ hfi,h.input_eq,
    Store.put_tape_other _ (by omega : L.fresh+1 ≠ L.fresh),hs1,List.append_nil,
    Store.put_flag,Store.flag_flag] at hcopy
  have hr := drop_run (L.fresh+1) L.fresh (by omega) x u (s.flag false)
  simp only [Store.put_flag] at hr
  rw [Store.put_comm _ (by omega : L.fresh+1 ≠ L.fresh)] at hr
  let s2 := ((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag false
  have hp : (Code.atom (.peek (L.fresh+1) (fun _ x => x.getD false))).Exec s2 1
      (((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false)) := by
    convert Exec.atom (.peek (L.fresh+1) (fun _ x => x.getD false)) s2 using 1
    dsimp [s2,Prim.run,Store.put,Store.flag]
    simp
  have hc := clear_run (L.fresh+1)
    (((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false))
  have htape : (((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false)).tape
      (L.fresh+1) = x.drop u := by simp
  rw [htape,List.length_drop] at hc
  have hz : ((((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false)).put
      (L.fresh+1) []) = s.flag (x[u]?.getD false) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [Store.put,Store.flag]
  rw [hz] at hc
  have ht := terminal_run L.output (s.flag (x[u]?.getD false))
  have hh := Exec.seq h1 (Exec.seq hcopy (Exec.seq hr (Exec.seq hp (Exec.seq hc ht))))
  convert hh using 1 <;> try rfl
  dsimp [cost,u]
  omega

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr

theorem correct {r : Nat} (e : Expr r) : e.Correct := by
  induction e with
  | lit n => exact correct_lit n
  | arg i => exact correct_arg i
  | length => exact correct_length
  | add e f ihe ihf => exact correct_add ihe ihf
  | mul e f ihe ihf => exact correct_mul ihe ihf
  | sub e f ihe ihf => exact correct_sub ihe ihf
  | zero e ih => exact correct_zero ih
  | bit e ih => exact correct_bit ih
  | sum b e ihb ihe => exact correct_sum ihb ihe

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

inductive Output : Nat → Type
  | nil {r : Nat} : Output r
  | bit {r : Nat} (b : Bool) : Output r
  | nat {r : Nat} (e : Expr r) : Output r
  | append {r : Nat} (a b : Output r) : Output r
  | loop {r : Nat} (bound : Expr r) (body : Output (r+1)) : Output r
  | when {r : Nat} (test : Expr r) (body : Output r) : Output r

namespace Output

def eval {r : Nat} (o : Output r) (input : List Bool) (args : Fin r → Nat) : List Bool :=
  match o with
  | .nil => []
  | .bit b => [b]
  | .nat e => List.replicate (e.eval input args) true ++ [false]
  | .append a b => a.eval input args ++ b.eval input args
  | .loop b e => (List.range (b.eval input args)).flatMap (fun i => e.eval input (Fin.cons i args))
  | .when t b => if t.eval input args = 0 then [] else b.eval input args

@[reducible] def compile {r : Nat} (o : Output r) (input : Nat) (args : Fin r → Nat)
    (out fresh : Nat) : Code Nat Bool :=
  match o with
  | .nil => reset
  | .bit b => .seq (push out b) reset
  | .nat e => .seq (e.compile input args out fresh) (push out false)
  | .append a b => .seq (a.compile input args out fresh) (b.compile input args out fresh)
  | .loop b e =>
    .seq (b.compile input args fresh (fresh+2))
      (.seq (.scan fresh (fun s _ => s)
        (.seq (e.compile input (Fin.cons (fresh+1) args) out (fresh+2)) (push (fresh+1) true)))
        (clear (fresh+1)))
  | .when t b =>
    .seq (t.compile input args fresh (fresh+1))
      (.seq (.atom (.peek fresh (fun _ x => x.isSome)))
        (.seq (clear fresh) (.branch id (b.compile input args out fresh) reset)))

def cost {r : Nat} (o : Output r) (input : List Bool) (args : Fin r → Nat) : Nat :=
  match o with
  | .nil => 1
  | .bit _ => 2
  | .nat e => e.cost input args+1
  | .append a b => a.cost input args+b.cost input args
  | .loop b e => b.cost input args+
      (∑ i ∈ Finset.range (b.eval input args), e.cost input (Fin.cons i args))+4*b.eval input args+2
  | .when t b => t.cost input args+2*t.eval input args+3+
      (if t.eval input args=0 then 1 else b.cost input args)

noncomputable def bound {r : Nat} : Output r → Polynomial Nat
  | .nil => 0
  | .bit _ => 1
  | .nat e => e.bound+1
  | .append a b => a.bound+b.bound
  | .loop b e => b.bound*e.bound.comp (Polynomial.X+b.bound)
  | .when _ b => b.bound

noncomputable def costBound {r : Nat} : Output r → Polynomial Nat
  | .nil => 1
  | .bit _ => 2
  | .nat e => e.costBound+1
  | .append a b => a.costBound+b.costBound
  | .loop b e => b.costBound+b.bound*e.costBound.comp (Polynomial.X+b.bound)+4*b.bound+2
  | .when t b => t.costBound+2*t.bound+4+b.costBound

theorem length_range_flatMap {α : Type} (n : Nat) (f : Nat → List α) :
    ((List.range n).flatMap f).length = ∑ i ∈ Finset.range n, (f i).length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,List.flatMap_append,ih]

theorem length_le_bound {r : Nat} (o : Output r) (x : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : x.length ≤ n) (ha : ∀ i, args i ≤ n) : (o.eval x args).length ≤ o.bound.eval n := by
  induction o generalizing x n with
  | nil => simp [eval,bound]
  | bit b => simp [eval,bound]
  | nat e => simpa [eval,bound] using Nat.add_le_add_right (e.eval_le_bound x args n hi ha) 1
  | append a b iha ihb => simpa [eval,bound] using Nat.add_le_add (iha x args n hi ha) (ihb x args n hi ha)
  | when t b ih =>
    have hb := ih x args n hi ha
    simp only [eval,bound]
    split <;> simp_all
  | @loop r b e ihe =>
    have hb := b.eval_le_bound x args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval x args),
        (e.eval x (Fin.cons i args)).length ≤ e.bound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval x args := Finset.mem_range.mp hm
      apply ihe x (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    simp only [eval,bound,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,
      length_range_flatMap]
    calc
      _ ≤ ∑ _i ∈ Finset.range (b.eval x args), e.bound.eval (n+b.bound.eval n) := Finset.sum_le_sum heach
      _ = b.eval x args * e.bound.eval (n+b.bound.eval n) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hb

theorem cost_le_bound {r : Nat} (o : Output r) (x : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : x.length ≤ n) (ha : ∀ i, args i ≤ n) : o.cost x args ≤ o.costBound.eval n := by
  induction o generalizing x n with
  | nil => simp [cost,costBound]
  | bit b => simp [cost,costBound]
  | nat e => simpa [cost,costBound] using Nat.add_le_add_right (e.cost_le_bound x args n hi ha) 1
  | append a b iha ihb => simpa [cost,costBound] using Nat.add_le_add (iha x args n hi ha) (ihb x args n hi ha)
  | when t b ih =>
    have h1 := t.cost_le_bound x args n hi ha
    have h2 := t.eval_le_bound x args n hi ha
    have h3 := ih x args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    split <;> omega
  | @loop r b e ihe =>
    have hb := b.eval_le_bound x args n hi ha
    have hbc := b.cost_le_bound x args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval x args),
        e.cost x (Fin.cons i args) ≤ e.costBound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval x args := Finset.mem_range.mp hm
      apply ihe x (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    have hs : (∑ i ∈ Finset.range (b.eval x args), e.cost x (Fin.cons i args)) ≤
        b.bound.eval n * e.costBound.eval (n+b.bound.eval n) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (b.eval x args), e.costBound.eval (n+b.bound.eval n) := Finset.sum_le_sum heach
        _ = b.eval x args * e.costBound.eval (n+b.bound.eval n) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hb
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp,Polynomial.eval_X]
    omega

end Output
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr.Output
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

def Correct {r : Nat} (e : Output r) : Prop :=
  ∀ (L : Layout r) (x : List Bool) (a : Fin r → Nat) (s : Store Nat Bool), L.Ready s x a →
    (e.compile L.input L.args L.output L.fresh).Exec s (e.cost x a)
      ((s.put L.output ((e.eval x a).reverse ++ s.tape L.output)).flag false)

theorem correct_nil {r : Nat} : Correct (Output.nil (r := r)) := by
  intro L x a s h
  simpa [cost,eval] using reset_run s

theorem correct_bit {r : Nat} (b : Bool) : Correct (Output.bit (r := r) b) := by
  intro L x a s h
  have hh := Exec.seq (push_run s L.output b) (reset_run _)
  simpa [cost,eval] using hh

theorem correct_nat {r : Nat} (e : Expr r) : Correct (Output.nat e) := by
  intro L x a s h
  have he := e.correct L x a s h
  have hh := Exec.seq he (push_run _ L.output false)
  convert hh using 1 <;> try rfl
  simp [eval,List.reverse_append]

theorem correct_append {r : Nat} {e f : Output r} (he : e.Correct) (hf : f.Correct) : (e.append f).Correct := by
  intro L x a s h
  have h1 := he L x a s h
  have h2 := hf L x a _ ((h.output ((e.eval x a).reverse ++ s.tape L.output)).flag false)
  have hh := Exec.seq h1 h2
  convert hh using 1 <;> try rfl
  simp [eval,List.reverse_append,List.append_assoc]

theorem correct_when {r : Nat} (t : Expr r) {o : Output r} (ho : o.Correct) : (Output.when t o).Correct := by
  intro L x a s h
  let u := t.eval x a
  have hs0 := h.clean L.fresh (by omega)
  have h1 := t.correct (L.temp 0 1 (by omega)) x a s (h.temp 0 1 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let s1 := (s.put L.fresh (List.replicate u true)).flag false
  have hp : (Code.atom (.peek L.fresh (fun _ x => x.isSome))).Exec s1 1
      ((s.put L.fresh (List.replicate u true)).flag (decide (u≠0))) := by
    convert Exec.atom (.peek L.fresh (fun _ x => x.isSome)) s1 using 1
    dsimp [s1,Prim.run,Store.put,Store.flag]
    cases u <;> simp
  have hc := clear_run L.fresh ((s.put L.fresh (List.replicate u true)).flag (decide (u≠0)))
  simp only [Store.flag_tape,Store.put_tape_same,List.length_replicate,Store.put_flag,Store.put_put] at hc
  have hz : s.put L.fresh [] = s := by rw [← hs0,Store.put_self]
  rw [hz] at hc
  have hbranch : (Code.branch id (o.compile L.input L.args L.output L.fresh) reset).Exec
      (s.flag (decide (u≠0))) (1+(if u=0 then 1 else o.cost x a))
      ((s.put L.output (((Output.when t o).eval x a).reverse ++ s.tape L.output)).flag false) := by
    by_cases hu : u=0
    · have hh := Exec.branch_false (f := id) (c := o.compile L.input L.args L.output L.fresh)
        (d := reset) (s := s.flag (decide (u≠0))) (by simp [hu]) (reset_run _)
      simpa [eval,show t.eval x a = u from rfl,hu] using hh
    · have hh := Exec.branch_true (f := id) (c := o.compile L.input L.args L.output L.fresh)
        (d := reset) (s := s.flag (decide (u≠0))) (by simp [hu]) (ho L x a _ (h.flag _))
      simpa [eval,show t.eval x a = u from rfl,hu] using hh
  have hh := Exec.seq h1 (Exec.seq hp (Exec.seq hc hbranch))
  convert hh using 1; try rfl
  dsimp [cost,u]
  omega

theorem correct_loop {r : Nat} (b : Expr r) {e : Output (r+1)}
    (he : e.Correct) : (Output.loop b e).Correct := by
  intro L x a s h
  let n := b.eval x a
  let outputs := fun i => (List.range i).flatMap (fun j => e.eval x (Fin.cons j a))
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have hfi : L.input ≠ L.fresh := Nat.ne_of_lt L.input_lt
  have h1i : L.input ≠ L.fresh+1 := by have := L.input_lt; omega
  have hfa : ∀ j, L.args j ≠ L.fresh := fun j => Nat.ne_of_lt (L.args_lt j)
  have h1a : ∀ j, L.args j ≠ L.fresh+1 := by intro j; have := L.args_lt j; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have h1 := b.correct (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let states := fun i =>
    ((((s.put (L.fresh+1) (List.replicate i true)).put L.fresh (List.replicate (n-i) true)).put
      L.output ((outputs i).reverse ++ s.tape L.output)).flag false)
  have hrdy : ∀ i, L.sumBody.Ready ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      x (Fin.cons i a) := by
    intro i
    constructor
    · simp [states,Layout.sumBody,hfi,h1i,L.input_ne,h.input_eq]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [states,Layout.sumBody,h1o]
      · simp [states,Layout.sumBody,hfa,h1a,L.args_ne,h.args_eq]
    · intro k hk
      change L.fresh+2 ≤ k at hk
      have hk0 : k≠L.fresh := by omega
      have hk1 : k≠L.fresh+1 := by omega
      have hko : k≠L.output := by have := L.output_lt; omega
      simp [states,hk0,hk1,hko,h.clean k (by omega)]
  have hp : ∀ i, (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2))
      (push (L.fresh+1) true)).Exec
      ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      (e.cost x (Fin.cons i a)+1) (states (i+1)) := by
    intro i
    have hbody := he L.sumBody x (Fin.cons i a)
      ((states i).put L.fresh (List.replicate (n-(i+1)) true)) (hrdy i)
    have hpush := push_run ((((states i).put L.fresh (List.replicate (n-(i+1)) true)).put L.output
      ((e.eval x (Fin.cons i a)).reverse ++
        ((states i).put L.fresh (List.replicate (n-(i+1)) true)).tape L.output)).flag false)
      (L.fresh+1) true
    have hh := Exec.seq hbody hpush
    convert hh using 1 <;> try rfl
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output
    · subst k
      simp only [states,Store.flag_tape,Store.put_tape_same,Store.put_tape_other _ (Ne.symm hfo),
        Store.put_tape_other _ (Ne.symm h1o)]
      simp [outputs,List.range_succ,List.flatMap_append,List.reverse_append,List.append_assoc]
    · by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
        simp_all [states,Store.put,Store.flag,List.replicate_succ]
  have hlo := scan_indexed L.fresh
    (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2)) (push (L.fresh+1) true))
    n states (fun i => e.cost x (Fin.cons i a)+1)
    (by intro i hi; simp [states,hfo]) (by intro i hi; exact hp i)
  have hstart : states 0 = (s.put L.fresh (List.replicate n true)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,outputs,Store.put,Store.flag]
  rw [hstart] at hlo
  have hc := clear_run (L.fresh+1) (states n)
  have hcval : (states n).tape (L.fresh+1) = List.replicate n true := by simp [states,h1o]
  rw [hcval,List.length_replicate] at hc
  have hend : (states n).put (L.fresh+1) [] =
      (s.put L.output ((outputs n).reverse ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hend] at hc
  have hh := Exec.seq h1 (Exec.seq hlo hc)
  convert hh using 1 <;> try rfl
  simp only [cost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  dsimp [n]
  omega

theorem correct {r : Nat} (o : Output r) : o.Correct := by
  induction o with
  | nil => exact correct_nil
  | bit b => exact correct_bit b
  | nat e => exact correct_nat e
  | append a b iha ihb => exact correct_append iha ihb
  | loop b e ihe => exact correct_loop b ihe
  | when t b ih => exact correct_when t ih

end DirectedFeedback.BoundedExpr.Output

end OAI
