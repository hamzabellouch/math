import OAI.Combinatorics.VariableWL.Decision

namespace OAI

namespace VariableWL.Computation.Stack.Code
variable {k : ℕ}

def tripleStore (s : Stores k) (j t u : Fin (k+1)) (w a b : Word) : Stores k :=
  Function.update (pairStore s j t w a) u b

def distribute (j t u : Fin (k+1)) (f : Bool → Bool) : Code k :=
  .loop (fun h => (h j).isSome) (.action fun h i =>
    if i=j then .pop else if i=t then .push ((h j).getD false)
    else if i=u then .push (f ((h j).getD false)) else .keep)

 theorem distribute_action (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (f : Bool → Bool) (s : Stores k) (b : Bool) (w a v : Word) :
    execute (fun i => if i=j then .pop else if i=t then .push ((heads (tripleStore s j t u (b::w) a v) j).getD false)
      else if i=u then .push (f ((heads (tripleStore s j t u (b::w) a v) j).getD false)) else .keep)
      (tripleStore s j t u (b::w) a v)=tripleStore s j t u w (b::a) (f b::v) := by
  funext i
  by_cases hi : i=j
  · subst i; simp [execute,tripleStore,pairStore,hju,hjt,Action.apply]
  · by_cases hit : i=t
    · subst i; simp [execute,tripleStore,pairStore,htu,hjt,Ne.symm hjt,hju,heads,Action.apply]
    · by_cases hiu : i=u
      · subst i; simp [execute,tripleStore,pairStore,Ne.symm hju,Ne.symm htu,hju,hjt,heads,Action.apply]
      · simp [execute,tripleStore,pairStore,hi,hit,hiu,Action.apply]

 theorem eval_distribute (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (f : Bool → Bool) (s : Stores k) (w a b : Word) :
    Eval (distribute j t u f) (tripleStore s j t u w a b) (3*w.length)
      (tripleStore s j t u [] (w.reverse++a) (w.reverse.map f++b)) := by
  induction w generalizing a b with
  | nil => exact Eval.loop_false (by simp [heads,tripleStore,pairStore,hju,hjt])
  | cons c w ih =>
    have he := Eval.action (fun h i => if i=j then .pop else if i=t then .push ((h j).getD false)
      else if i=u then .push (f ((h j).getD false)) else .keep) (tripleStore s j t u (c::w) a b)
    rw [distribute_action j t u hjt hju htu f] at he
    have hh := Eval.loop_true (p := fun h => (h j).isSome)
      (by simp [heads,tripleStore,pairStore,hjt,hju]) he (ih (c::a) (f c::b))
    convert hh using 1 <;> simp only [distribute,List.length_cons,List.reverse_cons,
      List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]; omega

def duplicate (j t u : Fin (k+1)) (f : Bool → Bool) : Code k :=
  .seq (distribute j t u f) (transfer t j id)

 theorem eval_duplicate (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (f : Bool → Bool) (s : Stores k) (ht : s t=[]) :
    Eval (duplicate j t u f) s (6*(s j).length+1)
      (Function.update s u ((s j).reverse.map f++s u)) := by
  have he := eval_distribute j t u hjt hju htu f s (s j) [] (s u)
  have hin : tripleStore s j t u (s j) [] (s u)=s := by
    simp only [tripleStore,pairStore,← ht,Function.update_eq_self]
  rw [hin] at he
  let s' := tripleStore s j t u [] ((s j).reverse++[]) ((s j).reverse.map f++s u)
  have htrans := eval_transfer t j (Ne.symm hjt) id s'
  have hs' : s' t=(s j).reverse := by simp [s',tripleStore,pairStore,htu]
  have hj' : s' j=[] := by simp [s',tripleStore,pairStore,hjt,hju]
  rw [hs',hj'] at htrans
  simp only [List.reverse_reverse,List.map_id_fun,id_eq,List.append_nil,List.length_reverse] at htrans
  have hout : pairStore s' t j [] (s j)=Function.update s u ((s j).reverse.map f++s u) := by
    funext i
    by_cases hi : i=j
    · subst i; simp [pairStore,hju]
    · by_cases hit : i=t
      · subst i; simp [pairStore,Ne.symm hjt,htu,ht]
      · by_cases hiu : i=u
        · subst i; simp [pairStore,s',tripleStore,Ne.symm hju,Ne.symm htu]
        · simp [pairStore,s',tripleStore,hi,hit,hiu]
  rw [hout] at htrans
  have hh := Eval.seq he htrans
  unfold duplicate
  have hn : 6*(s j).length+1=3*(s j).length+1+3*(s j).length := by omega
  rw [hn]
  exact hh

 theorem eval_length_add (j t u : Fin (k+1)) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (s : Stores k) (ht : s t=[]) (m : ℕ) (hu : s u=List.replicate m true) :
    Eval (duplicate j t u (fun _ => true)) s (6*(s j).length+1)
      (Function.update s u (List.replicate ((s j).length+m) true)) := by
  have h := eval_duplicate j t u hjt hju htu (fun _ => true) s ht
  simpa only [List.map_const',List.length_reverse,hu,← List.replicate_add] using h

end VariableWL.Computation.Stack.Code

namespace VariableWL.Computation.Stack.Code
variable {k : ℕ}

def multiplyAdd (a j t u : Fin (k+1)) : Code k :=
  .loop (fun h => (h a).isSome)
    (.seq (pop a) (duplicate j t u (fun _ => true)))

 theorem eval_multiplyAdd (a j t u : Fin (k+1))
    (haj : a≠j) (hat : a≠t) (hau : a≠u) (hjt : j≠t) (hju : j≠u) (htu : t≠u)
    (m q : ℕ) (s : Stores k) (ha : s a=List.replicate m true)
    (ht : s t=[]) (hu : s u=List.replicate q true) :
    Eval (multiplyAdd a j t u) s (m*(6*(s j).length+5))
      (pairStore s a u [] (List.replicate (m*(s j).length+q) true)) := by
  induction m generalizing q s with
  | zero =>
    have haz : s a=[] := by simpa only [List.replicate_zero] using ha
    have he : pairStore s a u [] (List.replicate (0*(s j).length+q) true)=s := by
      simp only [Nat.zero_mul,Nat.zero_add,pairStore,← haz,← hu,Function.update_eq_self]
    rw [he]
    simpa only [multiplyAdd,Nat.zero_mul] using
      (Eval.loop_false (p := fun h => (h a).isSome)
        (a := .seq (pop a) (duplicate j t u (fun _ => true))) (s := s) (by simp [heads,haz]))
  | succ m ih =>
    let s' := Function.update s a (List.replicate m true)
    have hp : Eval (pop a) s 1 s' := by
      simpa only [ha,List.replicate_succ,List.tail_cons] using eval_pop a s
    have ht' : s' t=[] := by simp [s',Ne.symm hat,ht]
    have hu' : s' u=List.replicate q true := by simp [s',Ne.symm hau,hu]
    have hs' : s' j=s j := by simp [s',Ne.symm haj]
    have hd := eval_length_add j t u hjt hju htu s' ht' q hu'
    rw [hs'] at hd
    let s'' := Function.update s' u (List.replicate ((s j).length+q) true)
    have hb : Eval (.seq (pop a) (duplicate j t u (fun _ => true))) s
        (1+1+(6*(s j).length+1)) s'' := Eval.seq hp hd
    have ha'' : s'' a=List.replicate m true := by simp [s'',s',hau]
    have ht'' : s'' t=[] := by simp [s'',htu,ht']
    have hu'' : s'' u=List.replicate ((s j).length+q) true := by simp [s'']
    have hj'' : s'' j=s j := by simp [s'',hju,hs']
    have hi := ih ((s j).length+q) s'' ha'' ht'' hu''
    rw [hj''] at hi
    have hh := Eval.loop_true (p := fun h => (h a).isSome)
      (by simp [heads,ha,List.replicate_succ]) hb hi
    have hout : pairStore s'' a u [] (List.replicate (m*(s j).length+((s j).length+q)) true)=
        pairStore s a u [] (List.replicate ((m+1)*(s j).length+q) true) := by
      have hn : m*(s j).length+((s j).length+q)=(m+1)*(s j).length+q := by ring
      rw [hn]
      funext i
      by_cases hia : i=a
      · subst i; simp [pairStore,hau]
      · by_cases hiu : i=u
        · subst i; simp [pairStore]
        · simp [pairStore,s'',s',hia,hiu]
    rw [hout] at hh
    convert hh using 1 <;> first | rfl | ring

end VariableWL.Computation.Stack.Code

namespace VariableWL.Computation.Stack.UnaryPower
open Code

def multiply : Code 4 := .seq (multiplyAdd 2 1 3 4) (transfer 4 2 id)

 theorem eval_multiply (s : Stores 4) (n q : ℕ) (hb : s 1=List.replicate n true)
    (ha : s 2=List.replicate q true) (ht : s 3=[]) (hu : s 4=[]) :
    Eval multiply s (q*(9*n+5)+1) (Function.update s 2 (List.replicate (q*n) true)) := by
  have hm := eval_multiplyAdd (k := 4) 2 1 3 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) q 0 s ha ht (by simpa only [List.replicate_zero] using hu)
  simp only [hb,List.length_replicate,Nat.add_zero] at hm
  let s' := pairStore s 2 4 [] (List.replicate (q*n) true)
  have hh := eval_transfer (k := 4) 4 2 (by decide) id s'
  have h4 : s' 4=List.replicate (q*n) true := by simp [s',pairStore]
  have h2 : s' 2=[] := by simp [s',pairStore]
  rw [h4,h2] at hh
  simp only [List.length_replicate,List.reverse_replicate,List.map_id_fun,id_eq,List.append_nil] at hh
  have hout : pairStore s' 4 2 [] (List.replicate (q*n) true)=
      Function.update s 2 (List.replicate (q*n) true) := by
    funext i
    by_cases hi2 : i=2
    · subst i; simp [pairStore]
    · by_cases hi4 : i=4
      · subst i; simp [pairStore,hu]
      · simp [pairStore,s',hi2,hi4]
  rw [hout] at hh
  have he := Eval.seq hm hh
  unfold multiply
  have hn : q*(9*n+5)+1=q*(6*n+5)+1+3*(q*n) := by ring
  rw [hn]
  exact he

def program : ℕ → Code 4
  | 0 => .skip
  | d+1 => .seq (program d) multiply

def time (n q : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => time n q d+1+(q*n^d*(9*n+5)+1)

 theorem eval_program (d : ℕ) (s : Stores 4) (n q : ℕ)
    (hb : s 1=List.replicate n true) (ha : s 2=List.replicate q true)
    (ht : s 3=[]) (hu : s 4=[]) :
    Eval (program d) s (time n q d) (Function.update s 2 (List.replicate (q*n^d) true)) := by
  induction d with
  | zero => simpa only [program,time,pow_zero,Nat.mul_one,← ha,Function.update_eq_self] using Eval.skip s
  | succ d ih =>
    let s' := Function.update s 2 (List.replicate (q*n^d) true)
    have hmul := eval_multiply s' n (q*n^d) (by simp [s',hb]) (by simp [s'])
      (by simp [s',ht]) (by simp [s',hu])
    have he := Eval.seq ih hmul
    have hn : (q*n^d)*n=q*n^(d+1) := by rw [pow_succ,Nat.mul_assoc]
    simpa only [program,time,s',Function.update_idem,hn] using he

 theorem time_bound (n q d : ℕ) : time n q d≤16*(d+1)*(q+1)*(n+1)^(d+1) := by
  induction d with
  | zero => simp [time]
  | succ d ih =>
    have hx : n^d≤(n+1)^(d+1) := (Nat.pow_le_pow_left (Nat.le_succ n) d).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_succ d))
    have hterm : q*n^d*(9*n+5)≤14*(q+1)*(n+1)^(d+2) := by
      calc
        _ ≤ (q+1)*(n+1)^(d+1)*(9*n+5) := by gcongr; omega
        _ ≤ (q+1)*(n+1)^(d+1)*(14*(n+1)) := by gcongr; omega
        _ = _ := by rw [show d+2=(d+1)+1 by omega,pow_succ]; ring
    have hm : (n+1)^(d+1)≤(n+1)^(d+2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hp : 1≤(q+1)*(n+1)^(d+2) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (pow_pos (by omega) _))
    simp only [time]
    have hbase := Nat.mul_le_mul_left (16*(d+1)*(q+1)) hm
    nlinarith

end VariableWL.Computation.Stack.UnaryPower

namespace VariableWL.Computation.Stack.UnaryPower
open Code

def store (w : Word) (n q : ℕ) : Stores 4 := fun i =>
  if i=0 then w.reverse else if i=1 then List.replicate n true
  else if i=2 then List.replicate q true else []

 theorem store_initial (w : Word) : store w 0 0=(fun j => if j=0 then w.reverse else []) := by
  funext i
  simp only [store,List.replicate_zero,ite_self]

 theorem store_update_base (w : Word) (n q b : ℕ) :
    Function.update (store w n q) 1 (List.replicate b true)=store w b q := by
  funext i
  fin_cases i <;> simp [store]

 theorem store_update_accumulator (w : Word) (n q b : ℕ) :
    Function.update (store w n q) 2 (List.replicate b true)=store w n b := by
  funext i
  fin_cases i <;> simp [store]

def setup : Code 4 := .seq (duplicate 0 3 1 (fun _ => true)) (.seq (push 1 true) (push 2 true))

 theorem eval_setup (w : Word) : Eval setup (store w 0 0) (6*w.length+5) (store w (w.length+1) 1) := by
  have hd := eval_length_add (k := 4) 0 3 1 (by decide) (by decide) (by decide)
    (store w 0 0) (by simp [store]) 0 (by simp [store])
  simp only [store,ite_true,List.length_reverse,Nat.add_zero] at hd
  rw [store_update_base] at hd
  have hp1 := eval_push (k := 4) 1 true (store w w.length 0)
  have hp2 := eval_push (k := 4) 2 true (store w (w.length+1) 0)
  have he1 : Function.update (store w w.length 0) 1 (true::store w w.length 0 1)=
      store w (w.length+1) 0 := by
    rw [show store w w.length 0 1=List.replicate w.length true by simp [store],← List.replicate_succ]
    exact store_update_base w w.length 0 (w.length+1)
  have he2 : Function.update (store w (w.length+1) 0) 2 (true::store w (w.length+1) 0 2)=
      store w (w.length+1) 1 := by
    rw [show store w (w.length+1) 0 2=[] by simp [store]]
    exact store_update_accumulator w (w.length+1) 0 1
  rw [he1] at hp1
  rw [he2] at hp2
  have he := Eval.seq hd (Eval.seq hp1 hp2)
  have hn : 6*w.length+5=(6*w.length+1)+1+(1+1+1) := by omega
  rw [hn]
  exact he

def full (d : ℕ) : Code 4 := .seq setup (program d)

 theorem eval_full (d : ℕ) (w : Word) : Eval (full d) (store w 0 0)
    (6*w.length+6+time (w.length+1) 1 d) (store w (w.length+1) ((w.length+1)^d)) := by
  have hp := eval_program d (store w (w.length+1) 1) (w.length+1) 1
    (by simp [store]) (by simp [store]) (by simp [store]) (by simp [store])
  simp only [Nat.one_mul,store_update_accumulator] at hp
  have hh := Eval.seq (eval_setup w) hp
  simpa only [full,Nat.add_assoc,show 5+1=6 by rfl] using hh

 theorem full_bound (d m : ℕ) :
    4*(m+(6*m+6+time (m+1) 1 d)+1)≤
      (4*(32*(d+1)*2^(d+1)+14))*(m+1)^(d+2) := by
  have ht := time_bound (m+1) 1 d
  have hbase : m+1+1≤2*(m+1) := by omega
  have hpow := Nat.pow_le_pow_left hbase (d+1)
  rw [mul_pow] at hpow
  have hc := Nat.mul_le_mul_left (16*(d+1)*(1+1)) hpow
  have hstep : (m+1)^(d+1)≤(m+1)^(d+2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hC := Nat.mul_le_mul_left (32*(d+1)*2^(d+1)) hstep
  have hmono : m+1≤(m+1)^(d+2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (n := m+1) (by omega) (show 1≤d+2 by omega)
  nlinarith

noncomputable def machine (d : ℕ) : VariableWL.Machine := ((full d).machine 2).compile

def constant (d : ℕ) : ℕ := 4*(32*(d+1)*2^(d+1)+14)

 theorem outputs (d : ℕ) (w : Word) :
    VariableWL.OutputsWithin (machine d) w (List.replicate ((w.length+1)^d) true)
      (constant d*(w.length+1)^(d+2)) := by
  have he := eval_full d w
  rw [store_initial] at he
  have hh := eval_outputs (full d) 2 w he
  have hout : store w (w.length+1) ((w.length+1)^d) 2=List.replicate ((w.length+1)^d) true := by simp [store]
  rw [hout] at hh
  obtain ⟨t,ht,hhalt,hout⟩ := hh
  exact ⟨t,ht.trans (full_bound d w.length),hhalt,hout⟩

end VariableWL.Computation.Stack.UnaryPower

namespace VariableWL.Encoding

 theorem order_le_code_length (G : Graph) : G.order ≤ (graphCode G).length := by
  have hn : G.order ≤ G.order*G.order := by
    by_cases hz : G.order=0
    · simp [hz]
    · have h := Nat.mul_le_mul_left G.order (Nat.one_le_iff_ne_zero.mpr hz)
      simpa only [Nat.mul_one] using h
  rw [graphCode_eq,List.length_append,matrix_length]
  omega

 theorem pair_orders {w : Word} {G H : Graph} {k : ℕ} (h : pair w=some (G,H,k)) :
    G.order ≤ w.length ∧ H.order ≤ w.length := by
  rw [pair_sound h,pairCode,List.length_append,List.length_append]
  have hG := order_le_code_length G
  have hH := order_le_code_length H
  omega

end VariableWL.Encoding

namespace VariableWL.RefinementSize

 theorem count_bound (G H : Graph) (k m : ℕ) (hG : G.order ≤ m) (hH : H.order ≤ m) (hk : k ≤ m) :
    RefinementArray.count G H k ≤ 2^(m*m+1) := by
  have hp (a : ℕ) (ha : a ≤ m) : a^k ≤ 2^(m*m) := by
    calc
      _  ≤  (2^m)^k := Nat.pow_le_pow_left (ha.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := m)))) k
      _ = 2^(m*k) := (pow_mul 2 m k).symm
      _  ≤  2^(m*m) := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left m hk)
  have h1 := hp G.order hG
  have h2 := hp H.order hH
  unfold RefinementArray.count
  rw [pow_succ]
  omega

 theorem capped_count_bound {w : Word} {G H : Graph} {k : ℕ}
    (h : Encoding.pair w=some (G,H,k)) :
    RefinementArray.count G H (InputDecision.capped G k) ≤ 2^((w.length+2)^2+1) := by
  obtain ⟨hG,hH⟩ := Encoding.pair_orders h
  have hk : InputDecision.capped G k ≤ w.length+2 := by unfold InputDecision.capped; omega
  simpa only [pow_two] using count_bound G H (InputDecision.capped G k) (w.length+2)
    (by omega) (by omega) hk

 theorem array_bits_bound {w : Word} {G H : Graph} {k : ℕ}
    (h : Encoding.pair w=some (G,H,k)) (s : ℕ) :
    (RefinementArray.array G H (InputDecision.capped G k) s).length ≤ 2^(2*((w.length+2)^2+1)) := by
  rw [RefinementArray.array_length]
  have hh := Nat.pow_le_pow_left (capped_count_bound h) 2
  rw [← pow_mul] at hh
  simpa only [Nat.mul_comm] using hh

 theorem polynomial_of_exponential (c d m N : ℕ) (hN : N ≤ 2^(m*m+1)) :
    c*(N+1)^d ≤ 2^((c+d+1)*(m+2)^2) := by
  have hP : 1 ≤ 2^(m*m+1) := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hN' : N+1 ≤ 2^(m*m+2) := by
    rw [show m*m+2=(m*m+1)+1 by omega,pow_succ]
    omega
  calc
    _  ≤  2^c*(2^(m*m+2))^d := Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n := c))) (Nat.pow_le_pow_left hN' d)
    _ = 2^(c+(m*m+2)*d) := by rw [← pow_mul,← pow_add]
    _  ≤  _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

end VariableWL.RefinementSize

end OAI
