import OAI.Computability.Logspace.CounterPrograms

namespace OAI

/-!
Uniform numerical encodings and finite configuration graphs of randomized machines.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Configuration reduction: numerical encoding.
Positions on work tapes represented relatively, by two binary stacks. Absolute
head positions are not observed by the machine; space bounds on the original
run give polynomial bounds on these relative encodings.
-/
namespace ExactDerandomization.Base

abbrev front (n : ℕ) : Bool := decide (n%2=1)
def push (b : Bool) (n : ℕ) : ℕ := (if b then 1 else 0)+2*n

@[simp] lemma push_front (n : ℕ) : push (front n) (n/2) = n := by
  simp only [push,front,decide_eq_true_eq]; split <;> omega
@[simp] lemma front_push (n : ℕ) (b : Bool) : front (push b n)=b := by
  unfold push; cases b <;> simp [front,Nat.mul_comm 2]
@[simp] lemma div_push (n : ℕ) (b : Bool) : push b n/2=n := by
  unfold push; split <;> omega

def bit : ℕ → ℕ → Bool
  | a,0 => front a
  | a,k+1 => bit (a/2) k

lemma bit_push (n k : ℕ) (b : Bool) : bit (push b n) (k+1)=bit n k := by rw [bit,div_push]
lemma bit_zero (k : ℕ) : bit 0 k=false := by induction k <;> simp_all [bit,front]

abbrev Zip := ℕ × ℕ

def Zip.act (a : Zip) (b : Bool) : Direction → Zip
  | .stay => (a.1,push b (a.2/2))
  | .right => (push b a.1,a.2/2)
  | .left => (a.1/2,push (front a.1) (push b (a.2/2)))

/-- Right stack includes current cell. -/
def Zipped (w : ℤ → Bool) (z : ℤ) (A : Zip) :=
  (∀ j : ℕ, bit A.1 j = w (z-1-j)) ∧
  (∀ j : ℕ, bit A.2 j = w (z+j))

lemma Zipped.read {w z A} (h : Zipped w z A) : front A.2=w z := by simpa [bit] using h.2 0

lemma upd_ne (w : ℤ → Bool) (b) (z z' y : ℤ) (e : z'≠z) (h : z'=y) :
    Function.update w z b z' = w y := by simp [e,← h]

lemma Zipped.move {w z A} (h : Zipped w z A) (b : Bool) (d : Direction) :
    Zipped (Function.update w z b) (d.move z) (A.act b d) := by
  obtain ⟨hl,hr⟩ := h
  cases d with
  | stay =>
    dsimp [Zipped,Direction.move,Zip.act]
    constructor
    · intro j; rw [hl, upd_ne w b z _ _ (by omega) rfl]
    · intro j
      cases j with
      | zero => simp [bit]
      | succ j => rw [bit_push,← bit,hr,upd_ne w b z _ _ (by omega) rfl]
  | right =>
    dsimp [Zipped,Direction.move,Zip.act]
    constructor
    · intro j
      cases j with
      | zero => simp [bit]
      | succ j =>
        rw [bit_push,hl,upd_ne w b z _ (z-1-j) (by omega) (by omega)]
    · intro j; rw [← bit,hr,upd_ne w b z _ _ (by omega) (show z+1+j=z+(↑(j+1):ℤ) by omega)]
  | left =>
    dsimp [Zipped,Direction.move,Zip.act]
    constructor
    · intro j
      rw [← bit,hl,upd_ne w b z _ _ (by omega)
                         (show z-1-1-j=z-1-↑(j+1) by omega)]
    · intro j
      cases j with
      | zero =>
        have e := hl 0
        simp only [bit,Nat.cast_zero,sub_zero] at e
        simp [bit,e]
      | succ j =>
        cases j with
        | zero => simp [bit]
        | succ j =>
          rw [bit_push,bit_push, ← bit,hr,upd_ne w b z _ _ (by omega)
                  (show z-1+↑(j+1+1)=z+↑(j+1) by omega)]

lemma trunc_bits (m n : ℕ) (h : ∀ j, m≤j → bit n j=false) : n<2^m := by
  induction m generalizing n with
  | zero =>

    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases e : n=0
      · simp [e]
      have he := ih (n/2) (by omega) (fun j _=> h (j+1) (by omega))
      have ht := h 0 (by omega)
      simp [bit,front] at ht; simp at he; simp; omega
  | succ m ih =>
    have he := ih (n/2) (fun j e=> h (j+1) (by omega))
    rw [pow_succ]; omega

lemma Zipped.bound {w z A} {s : ℕ} (h : Zipped w z A)
    (hp : |z| ≤ (s:ℤ)) (hh : ∀ v, (s:ℤ) < |v| → w v=false) :
    A.1<2^(2*s+1) ∧ A.2<2^(2*s+1) := by
  rw [abs_le] at hp
  constructor <;> apply trunc_bits <;> intro j hj
  · rw [h.1, hh]; rw [lt_abs]; omega
  · rw [h.2, hh]; rw [lt_abs]; omega

lemma Zip.unique {A A' : Zip} {b b' : Bool} {d : Direction}
    (h : front A.2=front A'.2)
    (e : A.act b d=A'.act b' d) : A=A' := by
  have H : ∀ (z w : ℕ), front z=front w → z/2=w/2 → z=w := by
    intro z w h h'
    rw [← push_front z,h,h',push_front]
  cases d <;> simp only [Zip.act,Prod.mk.injEq] at e
  ·
    apply Prod.ext
    · exact H _ _ (by simpa using congrArg front e.2) e.1
    · apply H _ _ h
      simpa using congrArg (fun a : ℕ => a/2/2) e.2
  · exact Prod.ext e.1 (H _ _ h (by simpa using congrArg (fun a : ℕ=>a/2) e.2))
  · exact Prod.ext (by simpa using congrArg (fun a : ℕ=>a/2) e.1) (H _ _ h e.2)

end ExactDerandomization.Base

end

section

namespace ExactDerandomization.Base

/-- Record of numeric registers (time separate from rest). -/
@[ext] structure R (w h : ℕ) where
  tm : ℕ
  st : ℕ
  inp : Fin h → ℕ
  tapes : Fin w → Zip

namespace R
variable {q w h : ℕ} (M : Machine q w h)

def state (A : R w h) (q : ℕ) : Fin (q+1) := ⟨A.st%(q+1), Nat.mod_lt _ (by omega)⟩
def out (A : R w h) : Option Bool := M.output (A.state q)

def minput (x : Word) (i : ℕ) : Direction → ℕ
  | .stay => i
  | .left => i-1
  | .right => if i<x.length+1 then i+1 else i

lemma minput_fin (x : Word) (i : Fin (x.length+2)) (d : Direction) :
    minput x i d = (d.moveInput i).val := by
  cases d <;> simp [minput, Direction.moveInput]
  split <;> omega

def action (A : R w h) (x : Word) (b : Bool) : Action q w h :=
  match A.out M with
  | none => M.transition (A.state q) (fun i=> Counter.scan x (A.inp i))
              (fun i=> front (A.tapes i).2) b
  | some _ => ⟨A.state q,fun i=> front (A.tapes i).2,fun _=>.stay,fun _=>.stay⟩

def step (A : R w h) (x : Word) (b : Bool) : R w h :=
  let u := A.action M x b
  { tm := A.tm+1
    st := u.nextState
    inp := fun j=> minput x (A.inp j) (u.inputMove j)
    tapes := fun k=> (A.tapes k).act (u.write k) (u.workMove k) }

def start : R w h := ⟨0,M.initialState.val,fun _=>0, fun _=>(0,0)⟩

def runs (x : Word) (coins : CoinTape) : ℕ → R w h
  | 0 => start M
  | t+1 => step M (runs x coins t) x (coins t)

variable {M}
structure OK {n : ℕ} (t : ℕ) (A : R w h) (c : Configuration q w h n) : Prop where
  tm : A.tm=t
  st : A.st=c.state.val
  inp (i : Fin h) : A.inp i = (c.inputPos i).val
  tapes (k : Fin w) : Zipped (c.work k) (c.workPos k) (A.tapes k)

lemma OK.state {x : Word} {t A} {c : Configuration q w h x.length} (hc : OK t A c) :
    A.state q = c.state := by ext; simp [R.state,hc.st,Nat.mod_eq_of_lt c.state.isLt]

lemma OK.next {x : Word} {t A} {c : Configuration q w h x.length} (hc : OK t A c)
    (b : Bool) :
    OK (t+1) (A.step M x b) (M.step x b c) := by
  have hs : A.state q = c.state := hc.state (x:=x)
  cases hb : M.output c.state with
  | some v =>
    have he : M.step x b c=c := by simp [Machine.step,hb]
    rw [he]; constructor
    · simp [step,hc.tm]
    · simp [step,action,out,hs,hb]
    · simp [step,action,out,hs,hb,minput,hc.inp]
    · intro k; simpa [step,action,out,hs,hb,Zip.act] using hc.tapes k
  | none =>
    let u := M.transition c.state (fun i => readInput x (c.inputPos i))
                  (fun k=> c.work k (c.workPos k)) b
    have he : A.action M x b=u := by
      have hh (k) := Zipped.read (hc.tapes k)
      simp [R.action,out,u,hs,hb,hc.inp,hh]
    constructor
    · simp [step,hc.tm]
    · simp [step,he,u,Machine.step,hb]
    · intro i
      simp only [step,he,hc.inp,minput_fin, Machine.step,hb]; rfl
    · intro i
      simp only [step,he,Machine.step,hb]
      exact (hc.tapes i).move (u.write i) (u.workMove i)

variable (M)
lemma runs_OK (x : Word) (coins : CoinTape) (t) :
    OK t (runs M x coins t) (M.run x coins t) := by
  induction t with
  | zero =>
    constructor
    · rfl
    · rfl
    · intro i; rfl
    · intro k; exact ⟨bit_zero,bit_zero⟩
  | succ t ih => exact ih.next _

lemma runs_out (x : Word) (coins : CoinTape) (t) :
    (runs M x coins t).out M = M.output (M.run x coins t).state := by
  rw [out,(runs_OK M x coins t).state]

/-- Work within radix, one chosen polynomial in n. cs: space coefficient,
k,e time coefficient/exponent. -/
def radix (q cs k e n : ℕ) : ℕ := q+2 + polynomialClock k e n +
           (n+2) + 2*(2*(n+2))^(2*cs)

lemma radix_pos (q cs k e n : ℕ) : 0<radix q cs k e n := by unfold radix; positivity

def Small (A : R w h) (m : ℕ) :=
  A.tm < m ∧ A.st < m ∧ (∀ i, A.inp i < m) ∧ (∀ i, (A.tapes i).1 < m ∧ (A.tapes i).2 < m)

lemma runs_small (x : Word) (coins : CoinTape) {cs k e : ℕ}
    (ht : ∀ t, M.spaceThrough x coins t ≤ cs * Nat.clog 2 (x.length+2))
    {t : ℕ} (he : t ≤ polynomialClock k e x.length) :
    (runs M x coins t).Small (radix q cs k e x.length) := by
  let n := x.length
  have ok := runs_OK M x coins t
  simp only [Small, ok.tm, ok.st, ok.inp, radix]
  refine ⟨by omega, by have := (M.run x coins t).state.isLt; omega, ?_, ?_⟩
  · intro i; have := ((M.run x coins t).inputPos i).isLt; omega
  · intro i
    let s := cs * Nat.clog 2 (n+2)
    have hv := @Zipped.bound ( (M.run x coins t).work i) _ _ s (ok.tapes i)
      (le_trans (M.workPos_abs_le_space x coins t i)
         (show (M.spaceThrough x coins t : ℤ) ≤ (s:ℤ) by exact_mod_cast ht t))
      (M.work_eq_false_outside ht t i)
    have hz : 2^(2*s+1) ≤ 2*(2*(x.length+2))^(2*cs) := by
      have e : 2*s=Nat.clog 2 (n+2)*(2*cs) := by dsimp [s]; ring
      rw [e,pow_succ,pow_mul,Nat.mul_comm _ 2]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (two_pow_clog_le _) _)
    omega

lemma minput_range (x : Word) (i : ℕ) (d : Direction) :
    i ≤ minput x i d + 1 ∧ minput x i d ≤ i+1 := by
  cases d <;> dsimp [minput] <;> grind

/-- Step source determinable from destination and bounded side information. -/
abbrev Hint (q w h : ℕ) := Bool × Fin (q+1) × (Fin h → Fin 3) × (Fin w → Bool)

def hint (A : R w h) (q : ℕ) (b : Bool) : Hint q w h :=
  (b,A.state q,fun i=> ⟨A.inp i%3,by omega⟩, fun k=> front (A.tapes k).2)

lemma step_inj (x : Word) (A A' : R w h) (b b' : Bool)
    (hk : A.step M x b=A'.step M x b') (hh : A.hint q b=A'.hint q b')
    (h : A.st<q+1) (h' : A'.st<q+1) : A=A' := by
  simp only [hint,Prod.mk.injEq] at hh
  obtain ⟨rfl,hst,hin,hq⟩ := hh
  have he : A.inp=A'.inp := by
    funext i
    have hv := congrFun (congrArg R.inp hk) i
    have hm := congrArg Fin.val (congrFun hin i)
    simp only [step] at hv
    have hs := minput_range x (A.inp i) ((A.action M x b).inputMove i)
    have ht := minput_range x (A'.inp i) ((A'.action M x b).inputMove i)
    dsimp only at hm
    omega
  have ha : A.action M x b=A'.action M x b := by rw [action,action,out,out,hst,he,hq]
  refine R.ext ?_ ?_ he ?_
  · have H := congrArg R.tm hk; simp [step] at H; exact H
  · simpa [R.state,Nat.mod_eq_of_lt h,Nat.mod_eq_of_lt h'] using congrArg Fin.val hst
  · funext i
    have hv := congrFun (congrArg tapes hk) i
    simp only [step,ha] at hv
    exact Zip.unique (congrFun hq i) hv

end R
end ExactDerandomization.Base

end

section

namespace ExactDerandomization.Base

abbrev Vec (w : ℕ) := Fin w → ℕ

def wrap (m : ℕ) (a z : ℕ) := a+m*z
def enc (m : ℕ) (z : ℕ) : {d : ℕ} → Vec d → ℕ
 | 0,_ => z
 | d+1,f => wrap m (f 0) (enc m z (fun i : Fin d => f i.succ))

def dec (m : ℕ) : (d z : ℕ) → Vec d
 | 0, _ => Fin.elim0
 | d+1,z => Fin.cons (z%m) (dec m d (z/m))

def upper (m : ℕ) : (d z : ℕ) → ℕ
 | 0,z => z
 | d+1,z => upper m d (z/m)

lemma wrap_lo {m a z} (h : a < m) : wrap m a z % m = a := by
  rw [wrap, Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt h]
lemma wrap_hi {m a z} (h : a < m) : wrap m a z / m = z := by
  rw [wrap,Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt h, Nat.zero_add]

lemma enc_dec (m d z : ℕ) : enc m (upper m d z) (dec m d z) = z := by
  induction d generalizing z with
  | zero => rfl
  | succ d ih =>
    simp only [enc, upper,dec,Fin.cons_zero,Fin.cons_succ,ih,wrap, Nat.mod_add_div]

lemma dec_enc (m z : ℕ) {d : ℕ} (v : Vec d) (h : ∀ i, v i < m) :
    dec m d (enc m z v) = v ∧ upper m d (enc m z v) = z := by
  induction d with
  | zero => exact ⟨funext (fun i => Fin.elim0 i),rfl⟩
  | succ d ih =>
    obtain ⟨e,e'⟩ := ih (fun i=>v i.succ) (fun i=>h _)
    simp [enc,dec,upper,wrap_lo (h 0),wrap_hi (h 0),e,e']
    funext i; refine Fin.cases ?_ ?_ i <;> simp

lemma upper_le {a b} (m d) (h : a≤b) : upper m d a ≤ upper m d b := by
  induction d generalizing a b with
  | zero => exact h
  | succ d ih => exact ih (Nat.div_le_div_right h)

lemma wrap_bound {m a z k} (h : a < m) (e : z<k) : wrap m a z < m*k := by
  unfold wrap
  nlinarith

lemma enc_bound {m z k d} (e : z<k) (v : Vec d) (h : ∀ i, v i < m) :
    enc m z v < m^d * k := by
  induction d with
  | zero => simpa [enc] using e
  | succ d ih =>
    calc enc m z v < m*(m^d*k) := wrap_bound (h _) (ih _ (fun i=>h _))
         _ = _ := by ring

namespace R
variable {w h : ℕ}

def id (A : R w h) (m : ℕ) :=
  enc m (enc m (enc m (wrap m A.st A.tm) A.inp) fun i=> (A.tapes i).1) fun i => (A.tapes i).2

def recov (w h : ℕ) (m n : ℕ) : R w h :=
  let n1 := upper m w n
  let n2 := upper m w n1
  let n3 := upper m h n2
  {tm:= n3/m
   st:= n3%m
   inp:= dec m h n2
   tapes:= fun i=> (dec m w n1 i,dec m w n i)}

lemma id_recov (m w h n) :
    (recov w h m n).id m = n := by
  unfold id recov wrap
  simp only [Nat.mod_add_div, enc_dec]

lemma recov_id {A : R w h} {m} (he : A.Small m) : recov w h m (A.id m)=A := by
  obtain ⟨_,hs,hi,ht⟩ := he
  have hl (z : ℕ) := dec_enc m z (fun i=> (A.tapes i).1) (fun i=> (ht i).1)
  have hr (z : ℕ) := dec_enc m z (fun i=> (A.tapes i).2) (fun i=> (ht i).2)
  have hin (z : ℕ) := dec_enc m z A.inp hi
  simp only [id, recov,(hr _).2,(hl _).2,(hin _).2,(hr _).1,(hl _).1,
    (hin _).1,wrap_hi hs,wrap_lo hs]

def total (w h m : ℕ) := m^w * (m^w * (m^h*(m*m)))

lemma id_lt {A : R w h} {m} (he : A.Small m) :
    A.id m < total w h m :=
  enc_bound (enc_bound (enc_bound (wrap_bound he.2.1 he.1)
    _ he.2.2.1) _ fun i=>(he.2.2.2 i).1) _ fun i=>(he.2.2.2 i).2

lemma recov_mono (m w h) (a b) (he : a≤b) :
    (recov w h m a).tm ≤ (recov w h m b).tm :=
  Nat.div_le_div_right (upper_le _ _ (upper_le _ _ (upper_le _ _ he)))

end R
end ExactDerandomization.Base

end

section

namespace ExactDerandomization.Base

/-- Source machines with supplied polynomial clock parameters (need not
be positive for building the graph) and controller space coefficient.
Semantics will justify these externally. -/
structure Source (q w h : ℕ) where
  mach : Machine q w h
  cs : ℕ
  c : ℕ
  k : ℕ

namespace Source
variable {q w h : ℕ} (P : Source q w h)

def clock (x : Word) := polynomialClock P.c P.k x.length
def mrad (x : Word) := R.radix q P.cs P.c P.k x.length
def size (x : Word) := R.total w h (P.mrad x)
def dom (x : Word) := Finset.range (P.size x)

def row (x : Word) (n : ℕ) := R.recov w h (P.mrad x) n
def ident (x : Word) (A : R w h) := R.id A (P.mrad x)
def first (x : Word) := P.ident x (R.start P.mach)

instance decSmall (A : R w h) (m) : Decidable (A.Small m) := by unfold R.Small; infer_instance

def legal (x : Word) (A : R w h) : Prop := A.Small (P.mrad x) ∧ A.st < q+1
instance decLegal (x : Word) (A : R w h) : Decidable (P.legal x A) :=
  inferInstanceAs (Decidable (_ ∧ _))

def fin (x : Word) (n : ℕ) : Bool :=
  decide (P.legal x (P.row x n) ∧ (P.row x n).tm = P.clock x ∧
                  (P.row x n).out P.mach = some true)

def next (x : Word) (n : ℕ) (b : Bool) : Option ℕ :=
  let a := P.row x n
  let v := a.step P.mach x b
  if P.legal x a ∧ a.tm < P.clock x ∧ P.legal x v then some (P.ident x v)
  else none

def reward (x : Word) (n : ℕ) : ℚ := if P.fin x n then 1 else 0

def edge (x : Word) (n j : ℕ) : ℕ :=
  (if P.next x n false=some j then 1 else 0)+(if P.next x n true=some j then 1 else 0)

def S (x : Word) (n j : ℕ) : ℚ := P.edge x n j / (2:ℚ)

lemma steps_to {x n b y} (h : P.next x n b = some y) :
    P.legal x (P.row x n) ∧ (P.row x n).tm<P.clock x ∧ P.legal x (P.row x y) ∧
      (P.row x n).step P.mach x b=P.row x y := by
  dsimp only [next] at h; split at h
  · rename_i he
    obtain rfl := Option.some.inj h
    unfold row at he
    simp only [row,ident, R.recov_id he.2.2.1]; exact ⟨he.1,he.2.1,he.2.2,trivial⟩
  · simp at h

lemma mem {x n} (h : P.legal x (P.row x n)) : n ∈ P.dom x := by
  have e := R.id_lt h.1
  simp only [row,R.id_recov] at e; exact Finset.mem_range.mpr e

lemma forward {x n b y} (e : P.next x n b = some y) : n < y := by
  by_contra! hy
  have hm := R.recov_mono (P.mrad x) w h y n hy
  have hk := congrArg R.tm (P.steps_to e).2.2.2
  simp only [row,R.step] at hk; omega

lemma S_nonneg (x n j) : 0≤ P.S x n j := by unfold S; positivity
lemma S_le (x n j) : P.S x n j ≤ 1 := by unfold S edge; split <;> split <;> norm_num

lemma S_pos {x n j} :
    0<P.S x n j ↔ P.next x n false=some j ∨ P.next x n true=some j := by
  unfold S edge; split <;> split <;> simp_all

def payoff (f : ℕ → ℚ) (p : Option ℕ) : ℚ := p.elim 0 f
def avg (x : Word) (n : ℕ) (f : ℕ → ℚ) : ℚ :=
  (payoff f (P.next x n false) + payoff f (P.next x n true)) / 2

open Finset
lemma avg_S (x n) (f) :
    P.avg x n f = ∑ j ∈ P.dom x, P.S x n j * f j := by
  let term (b : Bool) j : ℚ := if P.next x n b= some j then f j/2 else 0
  have he (b : Bool) : payoff f (P.next x n b)/2=∑ j∈P.dom x,term b j := by
    cases h : P.next x n b with
    | none => simp [term,payoff,h]
    | some j => simp [term,payoff,h,P.mem (P.steps_to h).2.2.1]
  have hk (j) : P.S x n j * f j= term false j + term true j := by
    unfold S edge term; split <;> split <;> norm_num <;> ring
  simp [avg,add_div,he,hk,sum_add_distrib]

lemma S_sub (x n) : ∑ j ∈ P.dom x, P.S x n j ≤ 1 := by
  have h := P.avg_S x n (fun _=>1)
  simp at h
  rw [← h]; unfold avg
  cases P.next x n false <;> cases P.next x n true <;> norm_num [payoff]

lemma dead {x n} (e : P.fin x n=true) (b) : P.next x n b = none := by
  simp only [fin,decide_eq_true_eq] at e
  simp [next,e.2.1]

lemma out_degree (x n) :
   ((P.dom x).filter (fun j=>0<P.S x n j)).card ≤ 2 := by
  let f (b : Bool) := (P.next x n b).getD 0
  have he : (P.dom x).filter (fun j=>0<P.S x n j) ⊆ Finset.univ.image f := by
    intro j h
    obtain a|a := (S_pos P).1 (Finset.mem_filter.1 h).2
    · exact Finset.mem_image.2 ⟨false, Finset.mem_univ _,by simp [f,a]⟩
    · exact Finset.mem_image.2 ⟨true, Finset.mem_univ _,by simp [f,a]⟩
  exact le_trans (Finset.card_le_card he) (by
    simpa only [Finset.card_univ,Fintype.card_bool] using Finset.card_image_le (s:=Finset.univ) (f:=f))

lemma in_degree (x y) :
   ((P.dom x).filter (fun n=>0<P.S x n y)).card ≤ Fintype.card (R.Hint q w h) := by
  classical
  let v := (P.dom x).filter (fun n=>0<P.S x n y)
  change v.card ≤ _
  let b n : Bool := if P.next x n true=some y then true else false
  have hs (n) (hn : n∈v) : P.next x n (b n)=some y := by
    have hv := P.S_pos.1 (Finset.mem_filter.1 hn).2
    dsimp only [b]; split <;> grind
  let code (n : ↥v) := (P.row x n.val).hint q (b n.val)
  have hi : Function.Injective code := by
    intro n m he
    have hn := P.steps_to (hs n n.prop)
    have hm := P.steps_to (hs m m.prop)
    have e := R.step_inj P.mach x _ _ _ _ (hn.2.2.2.trans hm.2.2.2.symm) he hn.1.2 hm.1.2
    apply Subtype.ext
    simpa only [row, ident,R.id_recov] using congrArg (P.ident x) e
  simpa using Fintype.card_le_of_injective _ hi

/-- potential via bounded recursion. -/
def potential (x : Word) : ℕ → ℕ → ℚ
 | 0 => P.reward x
 | k+1 => fun n=> P.reward x n + P.avg x n (potential x k)

lemma bounded (x k n) : 0≤P.potential x k n ∧ P.potential x k n ≤ 1 := by
  induction k generalizing n with
  | zero => unfold potential reward; split <;> norm_num
  | succ k ih =>
    cases h : P.fin x n with
    | true => simp [potential,reward,h,avg,P.dead h,payoff]
    | false =>
      have H (b) : 0 ≤ payoff (P.potential x k) (P.next x n b) ∧
            payoff (P.potential x k) (P.next x n b) ≤ 1 := by
        cases P.next x n b <;> simp [payoff, ih]
      have ht := H true
      have hf := H false
      simp [potential,reward,h,avg]
      constructor <;> linarith

lemma stable (x n k) (h : P.clock x ≤ (P.row x n).tm+k) :
    P.potential x k n=P.potential x (k+1) n := by
  induction k generalizing n with
  | zero =>
    have he (b) : P.next x n b=none := by
      simp only [Nat.add_zero] at h; simp [next,not_lt.2 h]
    simp [potential,avg,he,payoff]
  | succ k ih =>
    have he (b) : payoff (P.potential x k) (P.next x n b) =
                    payoff (P.potential x (k+1)) (P.next x n b) := by
      cases hb : P.next x n b with
      | none => rfl
      | some j =>
        apply ih
        have H := congrArg R.tm (P.steps_to hb).2.2.2
        simp only [R.step] at H
        omega
    change P.reward x n+ _=P.reward x n+_
    unfold avg; rw [he,he]

def pr (x : Word) := P.potential x (P.clock x)

lemma pr_eq (x n) : P.pr x n=P.reward x n + P.avg x n (P.pr x) := by
  exact stable P x n (P.clock x) (by omega)

abbrev Space (P : Source q w h) :=
  ∀ x coins t, P.mach.spaceThrough x coins t≤P.cs * Nat.clog 2 (x.length+2)
def walker (x : Word) (coins : CoinTape) (t : ℕ) := P.ident x (R.runs P.mach x coins t)

lemma visited (e : Space P) (x : Word) (coins t) (h : t≤P.clock x) :
    P.row x (P.walker x coins t) = R.runs P.mach x coins t ∧
      P.legal x (R.runs P.mach x coins t) ∧ (R.runs P.mach x coins t).tm=t := by
  have H := @R.runs_small q w _ P.mach x coins P.cs P.c P.k (e x coins) t h
  have I := R.runs_OK P.mach x coins t
  exact ⟨R.recov_id H,⟨H,I.st ▸ ((P.mach.run x coins t).state).isLt⟩,I.tm⟩

lemma mem_first (e : Space P) (x) : P.first x∈ P.dom x := by
  let coins : CoinTape := fun _=>false
  obtain ⟨h,k,_⟩ := P.visited e x coins 0 (Nat.zero_le _)
  exact P.mem (n:=P.walker x coins 0) (h.symm ▸ k)

lemma step_true (e : Space P) (x coins t) (h : t<P.clock x) :
    P.next x (P.walker x coins t) (coins t) =
      some (P.walker x coins (t+1)) ∧ P.fin x (P.walker x coins t) = false := by
  obtain ⟨H,G,S⟩ := P.visited e x coins t (le_of_lt h)
  obtain ⟨_,T,_⟩ := P.visited e x coins (t+1) h
  simp only [R.runs] at T
  simp only [next,fin,H,G,S,h,T,true_and,ite_true]
  simp [walker,R.runs,Nat.ne_of_lt h]

lemma pr_end (e : Space P) (x coins) :
    P.pr x (P.walker x coins (P.clock x)) =
      if P.mach.output (P.mach.run x coins (P.clock x)).state = some true then 1 else 0 := by
  obtain ⟨H,G,S⟩ := P.visited e x coins (P.clock x) le_rfl
  rw [pr_eq]
  simp [avg,reward,fin,next,H,G,S,payoff,R.runs_out]

lemma same (x : Word) (coins₁ coins₂ : CoinTape) (t : ℕ)
    (h : ∀ j<t, coins₁ j=coins₂ j) :
    P.walker x coins₁ t=P.walker x coins₂ t := by
  unfold walker; congr 1
  induction t with
  | zero=>rfl
  | succ t ih=> rw [R.runs,h t (by omega), ih (fun j hj=>h j (by omega)), ← R.runs]

abbrev Tapes (n : ℕ) := Fin n → Bool

def Toggle {n : ℕ} (i : Fin n) : Equiv.Perm (Tapes n) :=
  let f := fun (b : Tapes n) j => if i=j then !b j else b j
  have H : Function.LeftInverse f f := fun b=>by funext j; dsimp [f]; split <;> simp_all
  ⟨f,f,H,H⟩

lemma fair (e : Space P) (x : Word) :
    P.pr x (P.first x)=P.mach.acceptanceProbability x (P.clock x) := by
  let k := P.clock x
  let f (b : Tapes k) (t) := P.walker x (Machine.extendCoins b) t
  let g (t) (b : Tapes k) := P.pr x (f b t)
  have HH (t) (ht : t<k) (b : Tapes k) :
      g t b = (g (t+1) b + g (t+1) (Toggle ⟨t,ht⟩ b))/2 := by
    let i : Fin k := ⟨t,ht⟩
    let l := Toggle i b
    let w := Machine.extendCoins
       (t:=k)
    have hv : f b t=f l t := by
      apply P.same
      intro j hj
      have hk : j<k := by omega
      have hne : i.val≠j := by dsimp [i]; omega
      have hne' : i ≠ ⟨j,hk⟩ := fun h=>hne (congrArg Fin.val h)
      simp [Machine.extendCoins, l, Toggle,hk,hne']
    obtain ⟨hn,Hp⟩ := P.step_true e x (w b) t ht
    obtain ⟨hn',-⟩ := P.step_true e x (w l) t ht
    have h1 : w b t=b i := Machine.extendCoins_apply b i
    have h2 : w l t= (!b i) :=
      (Machine.extendCoins_apply l i).trans (by simp [l,Toggle])
    rw [h1] at hn
    rw [h2] at hn'
    change P.next x (f b t) (b i)=some (f b (t+1)) at hn
    change P.next x (f l t) (!b i)=some (f l (t+1)) at hn'
    change P.fin x (f b t)=false at Hp
    rw [← hv] at hn'
    change P.pr x (f b t) = (P.pr x (f b (t+1)) + P.pr x (f l (t+1))) / 2
    rw [pr_eq]
    cases h : b i <;> simp only [h, Bool.not_true,Bool.not_false] at hn hn' <;>
      simp [reward,Hp,avg,payoff,hn,hn',add_comm]
  have hs (t) (ht : t≤k) : ∑ b, g 0 b= ∑ b, g t b := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have hlt : t<k := ht
      rw [ih (by omega)]
      calc
        _ = ∑ b, (g (t+1) b+g (t+1) (Toggle ⟨t,hlt⟩ b))/2 :=
             Finset.sum_congr rfl (fun b _=> HH t hlt b)
        _ = _ := by
          rw [← Finset.sum_div, Finset.sum_add_distrib,Fintype.sum_equiv
             (Toggle ⟨t,hlt⟩) _ (g (t+1)) (fun b=>rfl)]
          ring
  let p (b : Tapes k) := P.mach.output (P.mach.run x (Machine.extendCoins b) k).state = some true
  let : DecidablePred p := fun i => inferInstanceAs (Decidable (_ = some true))
  have hv (b) : g k b = if p b then 1 else 0 := P.pr_end e x _
  have hz (b) : g 0 b = P.pr x (P.first x) := rfl
  have he := hs k le_rfl
  simp only [hz,hv] at he
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at he
  unfold Machine.acceptanceProbability
  rw [eq_div_iff (by positivity),mul_comm]
  change (2:ℚ)^k * P.pr x (P.first x) = _
  rw [Finset.card_filter]
  simpa using he

end Source
end ExactDerandomization.Base

end

section

namespace ExactDerandomization.Base

open Counter

lemma enc_E {w} (m z : NE) (f : Fin w → NE) (hm : E m) (hz : E z)
    (h : ∀ i, E (f i)) : E (fun x a=> enc (m x a) (z x a) (fun i=>f i x a)) := by
  induction w with
  | zero => exact hz
  | succ w ih =>
    exact (h 0).add (hm.mul (ih (fun i=>f i.succ) (fun i=> h i.succ)))

lemma dec_E {m n : NE} (hm : E m) (hn : E n) (d : ℕ) :
    E (fun x a=>upper (m x a) d (n x a)) ∧
      ∀ i, E (fun x a=>dec (m x a) d (n x a) i) := by
  induction d generalizing n with
  | zero => exact ⟨hn,fun i=>Fin.elim0 i⟩
  | succ d ih =>
    obtain ⟨h,h'⟩ := ih (hn.div hm)
    refine ⟨h,fun i=> Fin.cases ?_ ?_ i⟩
    · simpa only [dec,Fin.cons_zero] using (hn.mod hm)
    · intro i; simpa only [dec,Fin.cons_succ] using h' i

lemma PickAND {p q : Word → Store → Prop} [∀ x, DecidablePred (p x)] [∀ x, DecidablePred (q x)]
    (h : Pick (fun x a=>decide (p x a))) (k : Pick (fun x a => decide (q x a))) :
    Pick (fun x a => decide (p x a ∧ q x a)) := by
  simpa using h.and k

lemma front_E {n : NE} (h : E n) : Pick (fun x a=>front (n x a)) :=
  Pick.test_eq (h.mod (E.const 2)) (E.const 1)

lemma push_E {n : NE} {f : Word → Store → Bool} (h : E n) (e : Pick f) :
    E (fun x a=>push (f x a) (n x a)) :=
  (e.ite (E.const 1) (E.const 0)).add ((E.const 2).mul h)

variable {w h q : ℕ}

structure RE (f : Word → Store → R w h) : Prop where
  tim : E fun x a=> (f x a).tm
  st : E fun x a=> (f x a).st
  inp (i : Fin h) : E fun x a=> (f x a).inp i
  ll (i : Fin w) : E fun x a=> ((f x a).tapes i).1
  rr (i : Fin w) : E fun x a=> ((f x a).tapes i).2

namespace RE

variable {f : Word → Store → R w h}

lemma code {m : NE} (hf : RE f) (hm : E m) : E (fun x a=>(f x a).id (m x a)) :=
  enc_E _ _ _ hm (enc_E _ _ _ hm (enc_E _ _ _ hm (hf.st.add (hm.mul hf.tim)) hf.inp)
    hf.ll) hf.rr

lemma recover {m n : NE} (hm : E m) (hn : E n) :
    RE (fun x a=>R.recov w h (m x a) (n x a)) := by
  obtain ⟨he0,h0⟩ := dec_E hm hn w
  obtain ⟨he1,h1⟩ := dec_E hm he0 w
  obtain ⟨he2,h2⟩ := dec_E hm he1 h
  exact ⟨he2.div hm,he2.mod hm,h2,h1,h0⟩

lemma small {m : NE} (hf : RE f) (hm : E m) :
    Pick (fun x a=> decide ((f x a).Small (m x a))) :=
  PickAND (Pick.test_lt hf.tim hm) (PickAND (Pick.test_lt hf.st hm)
    (PickAND (Pick.all _ (fun i=> Pick.test_lt (hf.inp i) hm))
       (Pick.all _ (fun i=> PickAND (Pick.test_lt (hf.ll i) hm)
             (Pick.test_lt (hf.rr i) hm)))))

lemma stPick (hf : RE f) (q) : Pick (fun x a => (f x a).state q) :=
  Pick.pos (hf.st.mod (E.const _))

lemma choose (hf : RE f) (M : Machine q w h) (b : Bool) :
    Pick (fun x a => (f x a).action M x b) := by
  let v x a := fun i => Counter.scan x ((f x a).inp i)
  let z x a := fun i=> front ((f x a).tapes i).2
  have hv : Pick v := Pick.tuple (fun i=> Pick.read (hf.inp i))
  have hz : Pick z := Pick.tuple (fun i=> front_E (hf.rr i))
  let doIt := fun (s : Fin (q+1)) (u : Fin h → InputSymbol) (n : Fin w → Bool) =>
     match M.output s with
     | none=> M.transition s u n b
     | some _=> ⟨s,n,fun _=> .stay,fun _=>.stay⟩
  exact (hf.stPick q).bind (g:=fun s x a=>doIt s (v x a) (z x a))
      (fun s=> hv.bind (g:=fun u x a => doIt s u (z x a)) (fun u => hz.map (doIt s u)))

lemma step (hf : RE f) (M : Machine q w h) (b : Bool) :
    RE (fun x a => (f x a).step M x b) := by
  have he := hf.choose M b
  constructor
  · exact hf.tim.succ
  · exact he (fun z _ _=>z.nextState.val) (fun _=> E.const _)
  · intro i
    refine (he.map (fun z=>z.inputMove i))
       (fun d x a=> R.minput x ((f x a).inp i) d) (fun d=>?_ )
    cases d
    · exact (hf.inp i).pred
    · exact hf.inp i
    · exact E.ite_lt (hf.inp i) E.length.succ (hf.inp i).succ (hf.inp i)
  · intro i
    apply he (fun z x a => (((f x a).tapes i).act (z.write i) (z.workMove i)).1)
    intro z
    cases H : z.workMove i with
    | stay => exact hf.ll i
    | right => exact push_E (hf.ll i) (Pick.const _)
    | left => exact (hf.ll i).div (E.const 2)
  · intro i
    apply he (fun z x a => (((f x a).tapes i).act (z.write i) (z.workMove i)).2)
    intro z
    cases H : z.workMove i with
    | stay => exact push_E ((hf.rr i).div (E.const 2)) (Pick.const _)
    | right => exact (hf.rr i).div (E.const 2)
    | left => exact push_E (push_E ((hf.rr i).div (E.const 2)) (Pick.const _)) (front_E (hf.ll i))
end RE

namespace Source

variable (P : Source q w h)

lemma eClock : E (fun x _=>P.clock x) :=
  (E.const _).mul ((E.length.add (E.const 2)).pow_const _)

lemma eRad : E (fun x _=>P.mrad x) :=
  (((E.const (q+2)).add P.eClock).add (E.length.add (E.const 2))).add
    ((E.const 2).mul (((E.const 2).mul (E.length.add (E.const 2))).pow_const _))

lemma eSize : E (fun x _=>P.size x) := (P.eRad.pow_const _).mul
   ((P.eRad.pow_const _).mul ((P.eRad.pow_const _).mul (P.eRad.mul P.eRad)))

lemma eFirst : E (fun x _=>P.first x) :=
  RE.code (f:=fun _ _=>R.start P.mach)
     ⟨E.const _,E.const _,fun _=>E.const _,fun _=>E.const _,fun _=>E.const _⟩ P.eRad

lemma eLegal {v : Word → Store → R w h} (hv : RE v) :
    Pick (fun x a=> decide (P.legal x (v x a))) :=
  PickAND (hv.small P.eRad) (Pick.test_lt hv.st (E.const (q+1)))

lemma eReward {f : NE} (hf : E f) :
    Pick (fun x a=> P.fin x (f x a)) := by
  have hk : RE (fun x a=> P.row x (f x a)) := RE.recover P.eRad hf
  exact PickAND (P.eLegal hk) (PickAND (Pick.test_eq hk.tim P.eClock)
    ((hk.stPick q).map (fun s=>decide (P.mach.output s=some true))))

lemma eWeight {f g : NE} (hf : E f) (hg : E g) :
    E (fun x a=> P.edge x (f x a) (g x a)) := by
  let v x a := P.row x (f x a)
  have hk : RE v := RE.recover P.eRad hf
  have he (b : Bool) : E (fun x a=> if P.next x (f x a) b=some (g x a) then 1 else 0) := by
    let z x a := R.step P.mach (v x a) x b
    have hz : RE z := hk.step P.mach b
    have hc := hz.code P.eRad
    have ht := PickAND (P.eLegal hk) (PickAND (Pick.test_lt hk.tim P.eClock) (P.eLegal hz))
    convert ht.ite (hc.ite_eq hg (E.const 1) (E.const 0)) (E.const 0) using 1
    ext x a
    simp [next,v,z,ident] ; grind
  exact (he false).add (he true)

end Source
end ExactDerandomization.Base

end

end OAI
