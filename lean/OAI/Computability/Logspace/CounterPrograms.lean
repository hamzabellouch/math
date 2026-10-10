import OAI.Computability.Logspace.TransitionTables

namespace OAI

/-!
Bounded natural-register programs and their realization by finite deterministic machines.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Counter

def scan (x : Word) (m : ℕ) : InputSymbol :=
  if h : m < x.length+2 then readInput x ⟨m,h⟩ else .rightMarker

@[simp] lemma scan_zero (x : Word) : scan x 0 = .leftMarker := by simp [scan, readInput]

@[simp] lemma scan_lt (x : Word) (m : Fin (x.length+2)) :
    scan x m.val = readInput x m := by simp [scan]

@[simp] lemma marker_left {x : Word} {m : Fin (x.length+2)} :
    readInput x m = .leftMarker ↔ m.val = 0 := by
  unfold readInput; split
  · simp_all
  · split <;> simp_all

@[simp] lemma marker_right {x : Word} {m : Fin (x.length+2)} :
    readInput x m = .rightMarker ↔ m.val+1 = x.length+2 := by
  classical
  unfold readInput; split
  · simp_all
  · rename_i h
    split
    · rename_i he
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp he
      simp
      omega
    · rename_i he
      have := List.getElem?_eq_none_iff.mp he
      simp
      omega

lemma scan_is_zero (x : Word) (m : ℕ) :
    scan x m = .leftMarker ↔ m = 0 := by
  unfold scan; split <;> simp_all
  omega

/-- dir = false means ascending -/
def dir (q : ℕ) : Bool := decide (q%2=1)

@[simp] lemma dir_zero : dir 0 = false := rfl
@[simp] lemma dir_next (q) : dir (q+1) = !(dir q) := by
  unfold dir
  rw [Bool.eq_iff_iff]; simp; omega

def digit (n a : ℕ) : Fin (n+2) :=
  let r : Fin (n+2) := ⟨a%(n+2), Nat.mod_lt _ (by omega)⟩
  if dir (a/(n+2)) then r.rev else r

def dirs (n : ℕ) : (d a : ℕ) → Fin d → Bool
 | 0, _ => Fin.elim0
 | d+1, a => Fin.cons (dir (a/(n+2))) (dirs n d (a/(n+2)))

def digits (n : ℕ) : (d a : ℕ) → Fin d → Fin (n+2)
 | 0, _ => Fin.elim0
 | d+1, a => Fin.cons (digit n a) (digits n d (a/(n+2)))

lemma dirs_zero (n d : ℕ) : dirs n d 0 = fun _ => false := by
  induction d with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ d ih =>
    ext i
    refine Fin.cases ?_ ?_ i <;> simp [dirs, ih]

lemma digits_zero (n d : ℕ) : digits n d 0 = fun _ => ⟨0, by omega⟩ := by
  induction d with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ d ih =>
    funext i
    refine Fin.cases ?_ ?_ i <;> simp [digits, digit, ih]

abbrev obs (x : Word) (d a : ℕ) := fun i => readInput x (digits x.length d a i)

lemma quot_bound {n d a : ℕ} (h : a < (n+2)^(d+1)) :
    a/(n+2) < (n+2)^d :=
  (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [pow_succ] using h)

lemma eq_zero_obs (x : Word) (d a : ℕ) (h : a < (x.length+2)^d) :
    (∀ i, obs x d a i = .leftMarker) ↔ a = 0 := by
  refine ⟨?_, fun e i => ?_⟩
  · induction d generalizing a with
    | zero => simpa using Nat.lt_one_iff.mp h
    | succ d ih =>
      intro hp
      have high := (ih (a/(x.length+2)) (quot_bound h)) fun i =>
        by simpa [obs, digits] using hp (Fin.succ i)
      have low := marker_left.1 (hp 0)
      simp [digits,digit,high] at low
      have := Nat.mod_add_div a (x.length+2)
      rw [high, low] at this
      simpa [eq_comm] using this
  · simp [obs, e, digits_zero, readInput]

def symbol : (d : ℕ) → (Fin d → InputSymbol) → InputSymbol
  | 0, _ => .leftMarker
  | d+1, r => if ∀ i : Fin d, r i.succ = .leftMarker then r 0 else .rightMarker

lemma symbol_obs (x : Word) (d a : ℕ) (h : a < (x.length+2)^d) :
    symbol d (obs x d a) = scan x a := by
  cases d with
  | zero =>
    have : a=0 := by simpa using h
    simp [symbol, this]
  | succ d =>
    have ih := eq_zero_obs x d (a/(x.length+2)) (quot_bound h)
    simp only [symbol, obs, digits, Fin.cons_succ, Fin.cons_zero]
    by_cases hh : a < x.length+2
    · have h0 : a/(x.length+2)=0 := Nat.div_eq_of_lt hh
      simp [digit, h0, digits_zero, scan, hh, Nat.mod_eq_of_lt hh]
    · have h0 : a/(x.length+2) ≠ 0 := Nat.ne_of_gt (
        Nat.div_pos (by omega) (by omega))
      simp [obs] at ih
      simp [ih, scan, hh]

/-- gray positive step at a digit: 'up' = increase overall number, 'rev' = digit reversed -/
def goLeft (up rev : Bool) : Bool := decide (up = rev)
def spills (up rev : Bool) (s : InputSymbol) : Bool :=
  decide (s = if goLeft up rev then InputSymbol.leftMarker else InputSymbol.rightMarker)
def shift (up rev : Bool) : Direction :=
  if goLeft up rev then .left else .right

/-- change orientation and multi-head moves, attempting to step (uses at
interior, no overflow or underflow) -/
def attempt (up : Bool) :
    (d : ℕ) → (Fin d → Bool) → (Fin d → InputSymbol) → (Fin d → Bool) × (Fin d → Direction)
  | 0, r, _ => (r, Fin.elim0)
  | d+1, r, s =>
    if spills up (r 0) (s 0) then
      let q := attempt up d (fun i => r i.succ) (fun i => s i.succ)
      (Fin.cons (!(r 0)) q.1, Fin.cons .stay q.2)
    else (r, Fin.cons (shift up (r 0)) fun _ => .stay)

abbrev steps (up : Bool) (x : Word) (d a b : ℕ) : Prop :=
  let q := attempt up d (dirs x.length d a) (obs x d a)
  q.1 = dirs x.length d b ∧
    dirs_needs_move x.length q.2 (digits x.length d a) (digits x.length d b)
where
 dirs_needs_move n {d : ℕ} (m : Fin d → Direction) (a b : Fin d → Fin (n+2)) :=
   ∀ i, (m i).moveInput (a i) = b i

lemma low_steps (up) (x : Word) (d a b : ℕ)
    (he : a/(x.length+2) = b/(x.length+2))
    (hf : spills up (dir (a/(x.length+2))) (readInput x (digit x.length a)) = false)
    (hs : (shift up (dir (a/(x.length+2)))).moveInput (digit x.length a) =
       digit x.length b) : steps up x (d+1) a b := by
  simp only [steps, dirs, digits, steps.dirs_needs_move, obs, attempt, Fin.cons_zero,
     hf, Bool.false_eq_true, ↓reduceIte]
  rw [← he]
  refine ⟨rfl, fun i => ?_⟩
  refine Fin.cases ?_ ?_ i
  · simpa using hs
  · simp [Direction.moveInput]

lemma high_steps (up) (x : Word) (d a b : ℕ)
    (he : (!(dir (a/(x.length+2)))) = dir (b/(x.length+2)))
    (hf : spills up (dir (a/(x.length+2))) (readInput x (digit x.length a)) = true)
    (hs : digit x.length a = digit x.length b)
    (hh : steps up x d (a/(x.length+2)) (b/(x.length+2))) :
    steps up x (d+1) a b := by
  simp only [steps, steps.dirs_needs_move] at *
  simp only [obs, dirs, digits, attempt, Fin.cons_zero, Fin.cons_succ, hf, ↓reduceIte, he, eq_self]
  constructor
  · congr 1; exact hh.1
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa [Direction.moveInput] using hs
    · intro j; simpa using hh.2 j

lemma attempt_both (x : Word) (d a : ℕ) (h : a+1<(x.length+2)^d) :
    steps true x d a (a+1) ∧ steps false x d (a+1) a := by
  induction d generalizing a with
  | zero => simp at h
  | succ d ih =>
    let n := x.length
    let q := a / (n+2)
    let l := a % (n+2)
    have hl : l < n+2 := Nat.mod_lt _ (by omega)
    have ha : l+(n+2)*q=a := Nat.mod_add_div a _
    have he : a+1 = (l+1)+(n+2)*q := by omega
    have ha1 : (a+1)/(n+2) = (l+1)/(n+2)+q := by
      rw [he, Nat.add_mul_div_left _ _ (by omega)]
    have ha2 : (a+1)%(n+2) = (l+1)%(n+2) := by
      rw [he,Nat.add_mul_mod_self_left]
    have h0 : a%(x.length+2)=l := rfl
    by_cases hm : l+1<n+2
    · have h1 : (a+1)/(x.length+2)=a/(x.length+2) := by
        rw [ha1, Nat.div_eq_of_lt hm, Nat.zero_add]
      have h2 : (a+1)%(x.length+2)=l+1 := Eq.trans ha2 (Nat.mod_eq_of_lt hm)
      cases e : dir (a/(x.length+2)) <;>
        (refine ⟨low_steps _ _ _ _ _ h1.symm ?_ ?_, low_steps _ _ _ _ _ h1 ?_ ?_⟩ <;>
          simp [spills, digit, shift, goLeft, e, h1, Direction.moveInput, Fin.ext_iff,
            Fin.rev] <;> omega)
    · have hm' : l+1=n+2 := by omega
      have h1 : (a+1)/(x.length+2)=a/(x.length+2)+1 := by
        rw [ha1,hm', Nat.div_self (by omega), Nat.add_comm]
      have h2 : (a+1)%(x.length+2)=0 := ha2.trans (by rw [hm', Nat.mod_self])
      have hk := quot_bound h
      rw [h1] at hk
      have hg := ih _ hk
      cases e : dir (a/(x.length+2)) <;>
        (constructor
         · refine high_steps _ _ _ _ _ ?_ ?_ ?_ ?_
           · simp [h1]
           · simp [digit,spills,e,goLeft,Fin.rev]; omega
           · simp [h1,e,digit,Fin.ext_iff,Fin.rev]; omega
           · rw [h1]; exact hg.1
         · refine high_steps _ _ _ _ _ ?_ ?_ ?_ ?_
           · simp [h1]
           · simp [digit,h1,spills,e,goLeft,Fin.rev]; omega
           · simp [h1,e,digit,Fin.ext_iff,Fin.rev]; omega
           · rw [h1]; exact hg.2)

def adj (d : ℕ) (b : Direction) (o : Fin d → Bool) (r : Fin d → InputSymbol) :
    (Fin d → Bool) × (Fin d → Direction) :=
  match b with
  | .stay => (o,fun _=>.stay)
  | .left => if symbol d r = .leftMarker then (o,fun _=>.stay) else attempt false d o r
  | .right => attempt true d o r

def ch (b : Direction) (a : ℕ) :=
  match b with
  | .stay => a
  | .left => a-1
  | .right => a+1

lemma adj_spec (d : ℕ) (b : Direction) (a : ℕ) (x : Word)
    (h : a<(x.length+2)^d) (h' : ch b a < (x.length+2)^d) :
    let q := adj d b (dirs x.length d a) (obs x d a)
    q.1 = dirs x.length d (ch b a) ∧
      ∀ i, (q.2 i).moveInput (digits x.length d a i) = digits x.length d (ch b a) i := by
  cases b with
  | stay => exact ⟨rfl, fun _ => rfl⟩
  | right => exact (attempt_both x d a h').1
  | left =>
    simp only [adj, symbol_obs x d a h, scan_is_zero, ch]
    split
    · rename_i e; subst a; exact ⟨rfl, fun _ => rfl⟩
    · match a with
      | c+1 =>
        simpa [steps, steps.dirs_needs_move] using (attempt_both x d c h).2

end ExactDerandomization.Counter

end

section

/-!
A finite-control, natural-register while-program implementation device.
CM source semantics has unbounded natural counters, left motion clipped at zero,
read of symbol at counter address (off-data is Right, hence Left iff zero).
To compile to Machine we must prove all counters at all steps are of polynomial
magnitude. Only a fixed number of counters is ever used.
-/

namespace ExactDerandomization.Counter

abbrev Store := ℕ → ℕ
abbrev Fit (c : Store) (k : ℕ) := ∀ i, c i < k

/-- bounded program instruction: read at i, set pc and maybe ±1 that same i. -/
structure Jump (S : Type) where
  atReg : ℕ
  op : InputSymbol → S × Direction

def tweak (c : Store) (i : ℕ) (b : Direction) : Store :=
  fun j => ch (if i=j then b else .stay) (c j)

@[simp] theorem tweak_self (c : Store) (i : ℕ) (b : Direction) :
    tweak c i b i = ch b (c i) := by simp [tweak]

@[simp] theorem tweak_other (c : Store) (i : ℕ) (b : Direction) (j : ℕ) (h : i≠j) :
    tweak c i b j = c j := by simp [tweak,h,ch]

@[simp] theorem tweak_stay (c : Store) (i : ℕ) : tweak c i .stay = c := by funext a; simp [tweak,ch]

variable {S : Type}

def Jump.apply (j : Jump S) (x : Word) (c : Store) : S × Store :=
  let a := j.op (scan x (c j.atReg))
  (a.1, tweak c j.atReg a.2)

structure CM (S : Type) where
  start : S
  prog : S → Bool ⊕ Jump S

namespace CM

variable (p : CM S)

inductive Runs (x : Word) (k : ℕ) : S → Store → Bool → Prop
 | stop s c b (hc : Fit c k) (es : p.prog s = .inl b) : Runs x k s c b
 | more {s c s' c' b} (j : Jump S) (hc : Fit c k) (es : p.prog s = .inr j)
        (ea : j.apply x c = (s', c')) (h : Runs x k s' c' b) : Runs x k s c b

theorem Runs.fits {x : Word} {k : ℕ} {c : Store} {s b} (h : p.Runs x k s c b) :
    Fit c k := by cases h <;> assumption

open Table

def tab (m d : ℕ) :
    TM (S × (Fin m → Fin d → Bool)) Empty (Fin m × Fin d) :=
  { start := (p.start, fun _ _ => false)
    out := fun s => match p.prog s.1 with
      | .inl b => some b
      | .inr _ => none
    go := fun s r v _ => match p.prog s.1 with
      | .inl _ => TM.idle s v
      | .inr j =>
        if e : j.atReg < m then
          let scans := fun (i : Fin m) u => r (i,u)
          let a := j.op (symbol d (scans ⟨j.atReg,e⟩))
          let z := fun (i : Fin m) => adj d (if j.atReg=i.val then a.2 else .stay) (s.2 i) (scans i)
          ⟨(a.1, fun i => (z i).1), v, Empty.elim, fun (i,u) => (z i).2 u⟩
        else TM.idle s v }

def rep (n m d : ℕ) (s : S) (c : Store) :
    Table.Conf (S × (Fin m → Fin d → Bool)) Empty (Fin m × Fin d) n :=
  ⟨(s,fun i => dirs n d (c i.val)),fun (i,u) => digits n d (c i.val) u,Empty.elim,Empty.elim⟩

lemma rep_step {m d : ℕ} (x : Word) (s : S) (c : Store) (coin) (j : Jump S)
    (ep : p.prog s = .inr j) (hm : j.atReg < m)
    (ha : Fit c ((x.length+2)^d)) (hb : Fit (j.apply x c).2 ((x.length+2)^d)) :
    (p.tab m d).step x coin (rep x.length m d s c) =
       rep x.length m d (j.apply x c).1 (j.apply x c).2 := by
  let a := j.op (scan x (c j.atReg))
  let b (i : Fin m) : Direction := if j.atReg=i.val then a.2 else .stay
  have hs (i : Fin m) := adj_spec d (b i) (c i) x (ha _) (hb i)
  simp only [TM.step, rep, tab, ep, hm, ↓reduceDIte, TM.applyAct, Jump.apply]
  rw [symbol_obs x d (c j.atReg) (ha j.atReg)]
  refine Conf.ext (Prod.ext rfl (funext fun i => (hs i).1)) ?_ ?_ ?_
  · exact funext fun i => (hs i.1).2 i.2
  · exact funext fun e => Empty.elim e
  · exact funext fun e => Empty.elim e

/-- A Runs derivation supplies an input-dependent but tape-independent clock. -/
theorem realize {x : Word} {m d : ℕ}
    (hm : ∀ s j, p.prog s = .inr j → j.atReg < m)
    {s : S} {c : Store} {b : Bool} (h : p.Runs x ((x.length+2)^d) s c b) :
    ∀ t, (∀ coins, (p.tab m d).run x coins t = rep x.length m d s c) →
      ∃ u, ∀ coins, (p.tab m d).out ((p.tab m d).run x coins u).state = some b := by
  induction h with
  | stop s c b hc es =>
    intro t ht; exact ⟨t, fun coins => by rw [ht]; simp [rep, tab, es]⟩
  | @more s c s' c' b j hc es ea h ih =>
    intro t ht
    refine ih (t+1) fun coins => ?_
    have he := p.rep_step (m:=m) x s c (coins t) j es (hm s j es) hc
        (by rw [ea]; exact h.fits)
    rw [TM.run, ht, he, ea]

theorem gives_L [Finite S] (A : Language) (d : ℕ)
    (h : ∀ x : Word, ∃ b : Bool, (b=true ↔ x∈A) ∧
           p.Runs x ((x.length+2)^d) p.start (fun _ => 0) b) : A ∈ L := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let cnt (s : S) := (p.prog s).elim (fun _=>0) fun j => j.atReg
  let m : ℕ := 1+∑ s:S, cnt s
  have hm : ∀ s j, p.prog s = .inr j → j.atReg < m := by
    intro s j e
    have := Finset.single_le_sum (s:=Finset.univ) (f:=cnt) (fun _ _ => Nat.zero_le _)
       (Finset.mem_univ s)
    have : cnt s = j.atReg := by simp [cnt, e]
    dsimp only [m]
    omega
  let Q := p.tab m d
  let : Nonempty S := ⟨p.start⟩
  let num := @TM.number (S × (Fin m → Fin d → Bool)) _ _
  let f := Fintype.equivFin Empty
  let g := Fintype.equivFin (Fin m × Fin d)
  refine ⟨_,_,_,Q.reindex num f g,TM.det_reindex _ _ _ _ (fun _ _ _=>rfl), ?_, ?_⟩
  · exact ⟨1, Nat.one_pos, fun x coins t => by rw [TM.space_reindex]; simp [TM.spaceThrough]⟩
  · intro x
    obtain ⟨b,eb,hb⟩ := h x
    have hi (coins : CoinTape) : Q.run x coins 0 =
        rep x.length m d p.start (fun _ => 0) := by
      refine Conf.ext ?_ ?_ (funext fun e => Empty.elim e) (funext fun e => Empty.elim e)
      · simp [Q, TM.run, TM.init, tab, rep, dirs_zero]
      · simp [Q, TM.run, TM.init, rep, digits_zero]
    obtain ⟨u,hu⟩ := p.realize hm hb 0 hi
    exact ⟨u,b,eb,fun coins => by rw [TM.out_reindex]; exact hu coins⟩

end CM
end ExactDerandomization.Counter

end

section

namespace ExactDerandomization.Counter

inductive Cmd where
 | atom (i : ℕ) (b : Direction)
 | seq (p q : Cmd)
 | bif (i : ℕ) (test : InputSymbol → Bool) (p q : Cmd)
 | loop (i : ℕ) (test : InputSymbol → Bool) (body : Cmd)

namespace Cmd

abbrev cond (i : ℕ) (test : InputSymbol → Bool) (x : Word) (a : Store) : Bool :=
  test (scan x (a i))

inductive Run (x : Word) (k : ℕ) : Cmd → Store → Store → Prop
 | atom {i d a b} (e : tweak a i d = b) (ha : Fit a k) (hb : Fit b k) :
     Run x k (.atom i d) a b
 | seq {p q a b c} : Run x k p a b → Run x k q b c → Run x k (.seq p q) a c
 | yes {i t a b p q} : cond i t x a = true → Run x k p a b → Run x k (.bif i t p q) a b
 | no {i t a b p q} : cond i t x a = false → Run x k q a b → Run x k (.bif i t p q) a b
 | endLoop {i t a p} : cond i t x a = false → Fit a k → Run x k (.loop i t p) a a
 | iter {i t a b c p} : cond i t x a = true → Run x k p a b →
     Run x k (.loop i t p) b c → Run x k (.loop i t p) a c

lemma Run.fits {x k p a c} (h : Run x k p a c) : Fit a k ∧ Fit c k := by
  induction h <;> grind

lemma Run.mono {x k p a c} (h : Run x k p a c) {l} (e : k≤l) : Run x l p a c := by
  have imp (a) (h : Fit a k) : Fit a l := fun i => lt_of_lt_of_le (h i) e
  induction h with
  | atom eq ha hb => exact .atom eq (imp _ ha) (imp _ hb)
  | seq _ _ ha hb => exact .seq ha hb
  | yes h _ ha => exact .yes h ha
  | no h _ ha => exact .no h ha
  | endLoop h hk => exact .endLoop h (imp _ hk)
  | iter h _ _ ha hb => exact .iter h ha hb

def Node : Cmd → Type
 | .atom _ _ => Unit
 | .seq p q => Node p ⊕ Node q
 | .bif _ _ p q => Unit ⊕ Node p ⊕ Node q
 | .loop _ _ p => Unit ⊕ Node p

instance (p : Cmd) : Finite (Node p) := by
  induction p <;> (dsimp only [Node]; infer_instance)

def enter : (p : Cmd) → Node p
 | .atom _ _ => ()
 | .seq p _ => Sum.inl (enter p)
 | .bif .. => Sum.inl ()
 | .loop .. => Sum.inl ()

variable {S : Type}

def code : (p : Cmd) → (Node p → S) → S → Node p → Jump S
 | .atom i b, _, y, _ => ⟨i,fun _=>(y,b)⟩
 | .seq p q, f, _, Sum.inl u =>
      code p (fun u => f (Sum.inl u)) (f (Sum.inr (enter q))) u
 | .seq _p q, f, y, Sum.inr u =>
      code q (fun u => f (Sum.inr u)) y u
 | .bif i t p q, f, _, Sum.inl _ =>
    ⟨i,fun s => (f (Sum.inr (if t s then Sum.inl (enter p) else Sum.inr (enter q))),.stay)⟩
 | .bif _ _ p _q, f, y, Sum.inr (Sum.inl u) =>
    code p (fun u=> f (Sum.inr (Sum.inl u))) y u
 | .bif _ _ _p q, f, y, Sum.inr (Sum.inr u) =>
    code q (fun u=> f (Sum.inr (Sum.inr u))) y u
 | .loop i t p, f, y, Sum.inl _ =>
    ⟨i, fun s => (if t s then f (Sum.inr (enter p)) else y,.stay)⟩
 | .loop _ _ p, f, _, Sum.inr u =>
    code p (fun u => f (Sum.inr u)) (f (Sum.inl ())) u

lemma compile {x k p a c} (h : Run x k p a c) {P : CM S} :
    ∀ (f : Node p → S) y b, (∀ u, P.prog (f u) = .inr (code p f y u)) →
      P.Runs x k y c b → P.Runs x k (f (enter p)) a b := by
  induction h with
  | @atom i d a b e ha hb =>
    intro f y v h hp
    apply CM.Runs.more (code _ _ _ (enter (.atom i d))) ha (h _) _ hp
    simp only [code, Jump.apply,e]
  | @seq p q a b c hab hbc ihp ihq =>
    intro f y v h hp
    apply ihp (fun u => f (Sum.inl u)) (f (Sum.inr (enter q))) v
    · exact fun u => h (Sum.inl u)
    exact ihq (fun u => f (Sum.inr u)) y v (fun u => h (Sum.inr u)) hp
  | @yes i t a b p q e hab ih =>
    intro f y v h hp
    have he := ih (fun u=> f (Sum.inr (Sum.inl u))) y v
         (fun u => h (Sum.inr (Sum.inl u))) hp
    refine CM.Runs.more (code _ _ _ (enter (.bif i t p q))) hab.fits.1 (h _) ?_ he
    simp [code, enter, Jump.apply, cond] at *
    rw [ite_eq_left e]
  | @no i t a b p q e hab ih =>
    intro f y v h hp
    have he := ih (fun u=> f (Sum.inr (Sum.inr u))) y v
         (fun u => h (Sum.inr (Sum.inr u))) hp
    refine CM.Runs.more (code _ _ _ (enter (.bif i t p q))) hab.fits.1 (h _) ?_ he
    dsimp only [cond] at e
    simp [code, enter, Jump.apply,e]
  | @endLoop i t a p h ha =>
    intro f y v he hp
    refine CM.Runs.more (code _ _ _ (enter (.loop i t p))) ha (he _) ?_ hp
    dsimp only [cond] at h
    simp [code, enter, Jump.apply,h]
  | @iter i t a b c p h hab hbc ihp ihq =>
    intro f y v he hp
    have hu := ihp (fun u=> f (Sum.inr u)) (f (Sum.inl ())) v
         (fun u => he (Sum.inr u)) (ihq f y v he hp)
    refine CM.Runs.more (code _ _ _ (enter (.loop i t p))) hab.fits.1 (he _) ?_ hu
    dsimp only [cond] at h
    simp [code, enter, Jump.apply,h]

abbrev States (p : Cmd) := Unit ⊕ Bool ⊕ Node p
def mach (p : Cmd) (i : ℕ) : CM (States p) :=
  let f := fun u => Sum.inr (Sum.inr u)
  { start := f (enter p)
    prog := fun s => match s with
      | Sum.inl _ => Sum.inr ⟨i, fun s => (Sum.inr (Sum.inl (decide (s≠.leftMarker))),.stay)⟩
      | Sum.inr (Sum.inl b) => Sum.inl b
      | Sum.inr (Sum.inr u) => Sum.inr (code p f (Sum.inl ()) u) }

theorem while_L (p : Cmd) (i d : ℕ) (A : Language)
    (h : ∀ x : Word, ∃ c, Run x ((x.length+2)^d) p (fun _=>0) c ∧
        (c i ≠ 0 ↔ x∈A)) : A ∈ L := by
  apply CM.gives_L (p.mach i) A d
  intro x
  obtain ⟨c,e,h⟩ := h x
  let v := decide (scan x (c i) ≠ .leftMarker)
  refine ⟨v, by simp [v, scan_is_zero,h], compile e (fun u=>Sum.inr (Sum.inr u)) (Sum.inl ()) v
    (fun _ => rfl) ?_⟩
  apply CM.Runs.more _ e.fits.2 rfl _ (
     CM.Runs.stop (Sum.inr (Sum.inl v)) c v e.fits.2 rfl)
  simp [Jump.apply,v]

end Cmd
end ExactDerandomization.Counter

end

section

namespace ExactDerandomization.Counter

abbrev High0 (a : Store) (l : ℕ) := ∀ i, l ≤ i → a i=0
abbrev put (a : Store) (i v : ℕ) : Store := fun j => if i=j then v else a j

@[simp] lemma put_self (a i v) : put a i v i = v := by simp [put]
@[simp] lemma put_ne (a i v j) (e : i≠j) : put a i v j = a j := by simp [put,e]
@[simp] lemma put_same (a i) : put a i (a i) = a := by funext j; by_cases i=j <;> simp_all
@[simp] lemma put_over (a i v w) : put (put a i v) i w = put a i w := by
  funext j; by_cases i=j <;> simp_all
lemma put_swap (a i j v w) (e : i≠j) :
    put (put a i v) j w = put (put a j w) i v := by
  funext r
  by_cases i=r <;> by_cases j=r <;> simp_all

lemma put_fit {a k v} (i) (h : Fit a k) (hv : v<k) : Fit (put a i v) k := by
  intro j; by_cases i=j <;> simp_all [Fit]
lemma put_high0 {a i l} (v) (h : High0 a l) (hi : i<l) : High0 (put a i v) l := by
  intro j hj; rw [put_ne _ _ _ _ (by omega)]; exact h _ hj
lemma tweak_put (a i d) : tweak a i d = put a i (ch d (a i)) := by
  funext j; by_cases i=j <;> simp_all

abbrev Tr := Word → Store → Store

/-- Counter program transformations, correctness with initial certified
zeros available FROM threshold l onwards. l is quantified: we can
request a program with the scratch moved out to make room. d bounds
all counters throughout simultaneously. -/
def Room (f : Tr) (l : ℕ) : Prop :=
  ∃ p : Cmd, ∃ d : ℕ, 0<d ∧ ∀ x a B, x.length+2≤B → High0 a l →
     Fit a B → Cmd.Run x (B^d) p a (f x a) ∧ High0 (f x a) l

def Op (f : Tr) : Prop := ∃ l, ∀ r, l ≤ r → Room f r

lemma fit_mono {a k l} (h : Fit a k) (hl : k≤l) : Fit a l := fun i => lt_of_lt_of_le (h i) hl
lemma high_mono {a k l} (h : High0 a k) (hl : k≤l) : High0 a l :=
  fun i hi => h i (le_trans hl hi)
lemma self_pow {B d : ℕ} (hp : 0<B) (hd : 0<d) : B≤B^d :=
  calc B = B^1 := by simp
       _ ≤ B^d := Nat.pow_le_pow_right hp hd

lemma Op.trans {f g : Tr} (h : Op f) (e : Op g) : Op (fun x a => g x (f x a)) := by
  obtain ⟨k,h⟩ := h; obtain ⟨l,e⟩ := e
  refine ⟨k+l,fun r hr => ?_⟩
  obtain ⟨p,d,hd,h⟩ := h r (by omega)
  obtain ⟨q,D,hD,e⟩ := e r (by omega)
  refine ⟨.seq p q,d*D,by positivity,fun x a B hB hh hf => ?_⟩
  obtain ⟨hp, hz⟩ := h x a B hB hh hf
  have hB2 := self_pow (B:=B) (by omega) hd
  obtain ⟨hq,hzq⟩ := e x _ (B^d) (le_trans hB hB2) hz hp.fits.2
  rw [pow_mul]
  exact ⟨.seq (hp.mono (self_pow (by omega) hD)) hq,hzq⟩

lemma Op.hide {f : Tr}
    (h : ∃ k, ∀ l, k≤l → ∃ g : Tr, Op g ∧
       ∀ x a, High0 a l → f x a = g x a ∧ High0 (f x a) l) : Op f := by
  obtain ⟨k,h⟩ := h
  refine ⟨k, fun l hl => ?_⟩
  obtain ⟨g,⟨t,ht⟩,he⟩ := h l hl
  obtain ⟨p,d,hd,hg⟩ := ht (t+l) (by omega)
  refine ⟨p,d,hd,fun x a B hB hh hf => ⟨?_, (he _ _ hh).2⟩⟩
  rw [(he _ _ hh).1]
  exact (hg _ _ _ hB (high_mono hh (by omega)) hf).1

lemma Op.atom (i d) : Op (fun _x a => put a i (ch d (a i))) := by
  refine ⟨i+1,fun l hl => ⟨.atom i d,2,by decide,fun x a B hb hh hf => ?_⟩⟩
  have e : 1<B := by omega
  have eb : B<B^2 := by nlinarith
  have ha := fit_mono hf (le_of_lt eb)
  have hi := hf i
  refine ⟨.atom (tweak_put ..) ha (put_fit _ ha ?_), put_high0 _ hh (by omega)⟩
  cases d <;> dsimp [ch] <;> omega

lemma Op.identity : Op (fun _ a=>a) := by simpa [ch] using Op.atom 0 .stay

lemma Op.inc (i) : Op (fun _ a=>put a i (a i+1)) := Op.atom i .right
lemma Op.dec (i) : Op (fun _ a=>put a i (a i-1)) := Op.atom i .left

lemma Op.bif {f g : Tr} (i) (t : InputSymbol → Bool) (h : Op f) (e : Op g) :
    Op (fun x a => if t (scan x (a i)) then f x a else g x a) := by
  obtain ⟨kf,h⟩ := h
  obtain ⟨kg,e⟩ := e
  refine ⟨kf+kg, fun r hr => ?_⟩
  obtain ⟨p,d,hd,h⟩ := h r (by omega)
  obtain ⟨q,D,hD,e⟩ := e r (by omega)
  refine ⟨.bif i t p q,d+D,by omega,fun x a B hb hh hf => ?_⟩
  simp only []
  split
  · rename_i htest; obtain ⟨he,he'⟩ := h x a B hb hh hf
    exact ⟨.yes htest (he.mono (Nat.pow_le_pow_right (by omega) (by omega))),he'⟩
  · rename_i htest; obtain ⟨he,he'⟩ := e x a B hb hh hf
    exact ⟨.no (Bool.eq_false_iff.mpr htest) (he.mono
       (Nat.pow_le_pow_right (by omega) (by omega))),he'⟩

/-- Iterate transformation while condition true, supplied sequence of finite
states proves termination and the two bounds on the trajectory. -/
lemma Op.loop {f g : Tr} (i) (t : InputSymbol → Bool) (h : Op f)
    (e : ∃ k, ∀ l, k≤l → ∃ d : ℕ, 0<d ∧ ∀ x a B, x.length+2≤B →
       High0 a l → Fit a B → ∃ (n : ℕ) (r : ℕ → Store),
       r 0=a ∧ (∀ j, j≤n → High0 (r j) l ∧ Fit (r j) (B^d)) ∧
       (∀ j, j<n → Cmd.cond i t x (r j)=true ∧ r (j+1) = f x (r j)) ∧
       Cmd.cond i t x (r n)=false ∧ g x a=r n) :
    Op g := by
  obtain ⟨k,h⟩ := h
  obtain ⟨K,e⟩ := e
  refine ⟨k+K,fun l hl => ?_⟩
  obtain ⟨p,D,hD,h⟩ := h l (by omega)
  obtain ⟨d,hd,e⟩ := e l (by omega)
  refine ⟨.loop i t p,d*D,by positivity,fun x a B hB hh hf => ?_⟩
  obtain ⟨n,r,h0,hk,hj,hn,rn⟩ := e x a B hB hh hf
  have hp : 0<B := by omega
  have hu := self_pow hp hd
  have hs (j) (e : j≤n) : Cmd.Run x ((B^d)^D) (.loop i t p) (r j) (r n) := by
    induction e using Nat.decreasingInduction with
    | self => exact .endLoop hn (fit_mono (hk n le_rfl).2 (self_pow (by positivity) hD))
    | of_succ j ej ih =>
      obtain ⟨ht,he'⟩ := hj j ej
      refine .iter ht ?_ ih
      rw [he']; exact (h x _ (B^d) (le_trans hB hu) (hk j (by omega)).1 (hk j (by omega)).2).1
  rw [rn, ← h0, pow_mul]
  exact ⟨hs 0 n.zero_le,(hk n le_rfl).1⟩

def nz (s : InputSymbol) : Bool := decide (s ≠ .leftMarker)

@[simp] lemma cond_nz (x : Word) (i a) : Cmd.cond i nz x a = decide (a i≠0) := by
  simp [Cmd.cond,nz,scan_is_zero]

lemma Op.zero (i : ℕ) : Op (fun _ a=>put a i 0) := by
  refine Op.loop i nz (Op.dec i) ⟨i+1,fun l hl=>⟨1,by omega,fun x a B hB hh hf =>
    ⟨a i, fun j => put a i (a i-j), by simp, fun j hj=>?_,fun j hj=>?_,by simp,by simp⟩⟩⟩
  · exact ⟨put_high0 _ hh (by omega), put_fit _ (by simpa using hf) (by
      have := hf i; simp; omega)⟩
  · simp only [cond_nz, put_self, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
      put_over]
    constructor
    · omega
    · congr 1

lemma sum_lt_cube {B a b : ℕ} (hb : 1<B) (ha : a<B) (h : b<B) : a+b<B^2 := by
  nlinarith

lemma Op.send (s i : ℕ) (e : s≠i) :
    Op (fun _ a => put (put a s 0) i (a i+a s)) := by
  refine Op.loop s nz ((Op.dec s).trans (Op.inc i)) ⟨s+i+1,fun l hl =>
   ⟨2,by omega,fun x a B hB hh hf =>
    ⟨a s,fun j=>put (put a s (a s-j)) i (a i+j),?_,fun j hj=>?_,fun j hj=>?_,?_,by simp⟩⟩⟩
  · simp
  · have hd := self_pow (B:=B) (by omega) (show 0<2 by decide)
    have hs := hf s
    exact ⟨put_high0 _ (put_high0 _ hh (by omega)) (by omega),
      put_fit _ (put_fit _ (fit_mono hf hd) (by omega))
        (sum_lt_cube (by omega) (hf _) (by omega))⟩
  · have ex : i≠s := Ne.symm e
    simp only [cond_nz, ne_eq, put_ne _ _ _ _ ex, put_ne _ _ _ _ e, put_self, decide_not,
      Bool.not_eq_true', decide_eq_false_iff_not]
    constructor
    · omega
    · funext v; by_cases i=v <;> by_cases s=v <;> simp_all [put] <;> omega
  · simp [Ne.symm e]

lemma Op.sendTwo (s i j : ℕ) (e : s≠i) (h : s≠j) (g : i≠j) :
    Op (fun _ a => put (put (put a s 0) i (a i+a s)) j (a j+a s)) := by
  refine Op.loop s nz (((Op.dec s).trans (Op.inc i)).trans (Op.inc j))
   ⟨s+i+j+1,fun l hl =>
   ⟨2,by omega,fun x a B hB hh hf =>
    ⟨a s,fun t=>put (put (put a s (a s-t)) i (a i+t)) j (a j+t),?_,
      fun t ht=>?_,fun t ht=>?_,?_,by simp⟩⟩⟩
  · funext v; by_cases i=v <;> by_cases s=v <;> by_cases j=v <;> simp_all
  · have hd := self_pow (B:=B) (by omega) (show 0<2 by decide)
    have hs := hf s
    exact ⟨put_high0 _ (put_high0 _ (put_high0 _ hh (by omega)) (by omega)) (by omega),
      put_fit _ (put_fit _ (put_fit _ (fit_mono hf hd) (by omega))
        (sum_lt_cube (by omega) (hf _) (by omega)))
        (sum_lt_cube (by omega) (hf _) (by omega))⟩
  · have es : i≠s := Ne.symm e
    have hs : j≠s := Ne.symm h
    have gs : j≠i := Ne.symm g
    constructor
    · simp [es, hs]; omega
    · funext v; by_cases i=v <;> by_cases s=v <;> by_cases j=v <;> simp_all [put] <;> omega
  · simp [Ne.symm e, Ne.symm h]

lemma Op.copy (i j : ℕ) : Op (fun _ a=>put a j (a i)) := by
  by_cases h : i=j
  · subst j; simpa using identity
  refine Op.hide ⟨i+j+1, fun l hl => ⟨_,
    ((Op.zero j).trans (Op.sendTwo i j l h (by omega) (by omega))).trans
        (Op.send l i (by omega)),fun x a ha => ?_⟩⟩
  refine ⟨?_, put_high0 _ ha (by omega)⟩
  have h1 : l≠i := by omega
  have h2 : l≠j := by omega
  have ha := ha l le_rfl
  funext v
  by_cases i=v <;> by_cases j=v <;> by_cases l=v <;> simp_all [put]; grind

end ExactDerandomization.Counter

end

section

/-! Closure layer: symbolic natural-valued expressions evaluable by a
polynomial-magnitude counter program. Locality binds the expression to finitely
many arguments so scratch registers can be hidden. -/

namespace ExactDerandomization.Counter

abbrev NE := Word → Store → ℕ

abbrev Agree (l : ℕ) (a b : Store) := ∀ i, i<l → a i=b i
lemma Agree.mono {l s a b} (h : Agree l a b) (e : s≤l) : Agree s a b :=
  fun i hi => h i (lt_of_lt_of_le hi e)
lemma Agree.put {l a b i} (v) (h : Agree l a b) (e : l ≤ i) :
    Agree l a (Counter.put b i v) :=
  fun j hj => by rw [put_ne _ _ _ j (by omega),h j hj]

abbrev Local (e : NE) := ∃ k, ∀ x a b, Agree k a b → e x a = e x b
abbrev setE (e : NE) (i : ℕ) : Tr := fun x a => put a i (e x a)
def E (e : NE) := Local e ∧ ∀ i, Op (setE e i)

lemma E.bound {f : NE} (h : E f) :
    ∃ d : ℕ, 0<d ∧ ∀ x a B, x.length+2≤B → Fit a B → f x a < B^d := by
  obtain ⟨⟨k,h⟩,hf⟩ := h
  obtain ⟨l,e⟩ := hf 0
  obtain ⟨p,d,hd,e⟩ := e (k+l+1) (by omega)
  refine ⟨d,hd,fun x a B hB ha => ?_⟩
  let r : Store := fun i => if i<k then a i else 0
  have hh : Agree k a r := fun i hi => by simp [r,hi]
  have hr : High0 r (k+l+1) := fun i hi => by simp [r,show ¬i<k by omega]
  have hk : Fit r B := by
    intro i; dsimp [r]; split
    · apply ha
    · omega
  rw [h x a r hh]; simpa [setE] using ((e x r B hB hr hk).1.fits.2 0)

lemma E.var (i : ℕ) : E (fun _ a=>a i) := ⟨⟨i+1,fun x a b e=>e i (by omega)⟩,Op.copy i⟩

lemma E.succ {f : NE} (h : E f) : E (fun x a=>f x a+1) := by
  obtain ⟨⟨k,h⟩,hf⟩ := h
  exact ⟨⟨k,fun x a b he => by simp only [h x _ _ he]⟩,fun i=> by
    simpa [setE] using (hf i).trans (Op.inc i)⟩

lemma E.pred {f : NE} (h : E f) : E (fun x a=>f x a-1) := by
  obtain ⟨⟨k,h⟩,hf⟩ := h
  exact ⟨⟨k,fun x a b he => by simp only [h x _ _ he]⟩,fun i=> by
    simpa [setE] using (hf i).trans (Op.dec i)⟩

lemma E.const (a : ℕ) : E (fun _ _=>a) := by
  induction a with
  | zero => exact ⟨⟨0,fun _ _ _ _=>rfl⟩,Op.zero⟩
  | succ a ih => exact E.succ ih

lemma put_restore (a : Store) (i j v u : ℕ) (h : i≠j) :
    put (put (put a i v) j u) i (a i) = put a j u := by rw [put_swap a i j _ _ h,put_over,
       ← put_ne a j u i (Ne.symm h), put_same]

lemma E.bif {g f e : NE} (p : InputSymbol → Bool) (hg : E g) (hf : E f) (he : E e) :
    E (fun x a=> if p (scan x (g x a)) then f x a else e x a) := by
  obtain ⟨⟨kG,hg⟩,gp⟩ := hg
  obtain ⟨⟨kF,hf⟩,fp⟩ := hf
  obtain ⟨⟨kE,he⟩,ep⟩ := he
  refine ⟨⟨kG+kE+kF,fun x a b h => by
    simp only [he x a b (h.mono (by omega)),hf x a b (h.mono (by omega)),hg x a b (h.mono (by omega))]⟩,
    fun i=>?_⟩
  apply Op.hide
  refine ⟨kE+kF+i+1,fun l hl => ⟨_,
    ((gp l).trans (Op.bif l p (fp i) (ep i))).trans (Op.zero l),fun x a hh => ?_⟩⟩
  refine ⟨?_, put_high0 _ hh (by omega)⟩
  simp only [setE, put_self]
  have hs (k') (hk : k'≤l) : Agree k' a (put a l (g x a)) :=
    Agree.put _ (fun _ _ => rfl) hk
  rw [← he x _ _ (hs _ (by omega)),← hf x _ _ (hs _ (by omega))]
  split <;> rw [← hh l le_rfl, put_restore a l i _ _ (by omega)]

lemma E.ite {g f e : NE} (hg : E g) (hf : E f) (he : E e) :
    E (fun x a => if g x a=0 then f x a else e x a) := by
  simpa [scan_is_zero] using E.bif (fun s=>decide (s=.leftMarker)) hg hf he

lemma E.gives_L {f : NE} (h : E f) (A : Language) (e : ∀ x, f x (fun _=>0)≠0 ↔ x∈A) :
    A ∈ L := by
  obtain ⟨l,g⟩ := h.2 0
  obtain ⟨p,d,_,hp⟩ := g l le_rfl
  refine Cmd.while_L p 0 d A (fun x=>⟨_,
    (hp x (fun _=>0) (x.length+2) le_rfl (fun _ _=>rfl) (fun _=>by simp)).1,?_⟩)
  simpa [setE] using e x

/-- Synthetic state trajectory. Like Op.loop, but allows loop valid just
between a setup and teardown block, for one requested room. -/
lemma drive {beg step done ans : Tr} (l i : ℕ) (t : InputSymbol → Bool)
    (hg : Op beg) (hf : Op step) (hj : Op done)
    (h : ∃ (u d : ℕ), 0<d ∧ ∀ x a B, x.length+2≤B →
       High0 a l → Fit a B → ∃ (n : ℕ) (r : ℕ → Store),
       r 0=beg x a ∧ (∀ j, j≤n → High0 (r j) u ∧ Fit (r j) (B^d)) ∧
       (∀ j, j<n → Cmd.cond i t x (r j)=true ∧ r (j+1) = step x (r j)) ∧
       Cmd.cond i t x (r n)=false ∧ ans x a=done x (r n) ∧ High0 (ans x a) l) :
    Room ans l := by
  obtain ⟨u,d,hd,h⟩ := h
  obtain ⟨g,hg⟩ := hg; obtain ⟨f,hf⟩ := hf; obtain ⟨j,hj⟩ := hj
  let v := g+f+j+u+l
  obtain ⟨pg,dg,eg,hg⟩ := hg v (by dsimp [v]; omega)
  obtain ⟨pf,df,ef,hf⟩ := hf v (by dsimp [v]; omega)
  obtain ⟨pj,dj,ej,hj⟩ := hj v (by dsimp [v]; omega)
  let N := dg + d*(df+dj)
  refine ⟨.seq pg (.seq (.loop i t pf) pj), N, show 0<N by dsimp [N]; positivity,
        fun x a B he ha heB => ?_⟩
  have hk0 : l ≤ v := by dsimp [v]; omega
  obtain ⟨n,r,h0,hk,hr,hn,hy,he'⟩ := h x a B he ha heB
  have hB : 0<B := by omega
  have hu := self_pow hB hd
  have le {t : ℕ} (e : t≤N) := Nat.pow_le_pow_right hB e
  have hvf : (B^d)^df≤B^N := by
    rw [← pow_mul]
    exact le (by dsimp [N]; rw [mul_add]; omega)
  have hvj : (B^d)^dj≤B^N := by
    rw [← pow_mul]
    exact le (by dsimp [N]; rw [mul_add]; omega)
  have hh (j) (h : j≤n) := high_mono (hk j h).1 (show u ≤ v by dsimp [v]; omega)
  have heq (j) (e : j≤n) : Cmd.Run x (B^N) (.loop i t pf) (r j) (r n) := by
    induction e using Nat.decreasingInduction with
    | self => exact .endLoop hn (fit_mono (fit_mono (hk n le_rfl).2
                    (self_pow (by positivity) ej)) hvj)
    | of_succ j e ih =>
      obtain ⟨ht,ea⟩ := hr j e
      refine .iter ht ?_ ih
      rw [ea]
      exact ((hf x _ (B^d) (le_trans he hu) (hh j (by omega))
               (hk j (by omega)).2).1).mono hvf
  refine ⟨?_,he'⟩
  rw [hy]
  refine .seq ?_ (.seq (heq 0 n.zero_le) ?_)
  · rw [h0]
    exact ((hg x a B he (high_mono ha hk0) heB).1).mono (le (by dsimp [N]; omega))
  · exact ((hj x _ (B^d) (le_trans he hu) (hh n le_rfl)
          (hk n le_rfl).2).1).mono hvj

/-- Fold counting up. -/
def forNat {α : Type} (f : ℕ → α → α) (z : α) : ℕ → α
  | 0 => z
  | k+1 => f k (forNat f z k)

lemma E.iterate (f : Word → Store → ℕ → ℕ → ℕ) (n z : NE)
    (hf : ∀ g j, E g → E j → E (fun x a => f x a (g x a) (j x a)))
    (hn : E n) (hz : E z)
    (hloc : ∃ k, ∀ x a b, Agree k a b → f x a=f x b)
    (hb : ∃ d, 0<d ∧ ∀ x a B, x.length+2≤B → Fit a B →
          ∀ j≤ n x a, forNat (f x a) (z x a) j <B^d) :
    E (fun x a=> forNat (f x a) (z x a) (n x a)) := by
  have nk := hn.bound
  obtain ⟨⟨ln,hn⟩,en⟩ := hn
  obtain ⟨⟨lz,hz⟩,ez⟩ := hz
  obtain ⟨lf,hl⟩ := hloc
  let k := ln+lz+lf
  have hk : ln≤k ∧ lz≤k ∧ lf≤k := by dsimp [k]; omega
  refine ⟨⟨k,fun x a b e=> by
    simp only [hn x a b (e.mono hk.1),hz x a b (e.mono hk.2.1),hl x a b (e.mono hk.2.2)]⟩,
    fun i => ⟨k+i+1, fun l hh=>?_⟩⟩
  let g := l
  let s := l+1
  let u := l+2
  have ei : i<l := by omega
  have hu : s=l+1 ∧ g=l ∧ u=l+2 := ⟨rfl,rfl,rfl⟩
  let start : Tr := fun x a=> setE n s x (setE z g x a)
  let loopf : NE := fun x a=> f x a (a u) (a g)
  let next : Tr := fun x a=>
    let r := setE loopf g x a
    let t := put r u (r u+1)
    put t s (t s-1)
  let done : Tr := fun _ a=> put (put (put a i (a g)) g 0) u 0
  refine drive (beg:=start) (step:=next) (done:=done) l s nz
     ((ez g).trans (en s))
     ((((hf _ _ (E.var u) (E.var g)).2 g).trans (Op.inc u)).trans (Op.dec s))
     (((Op.copy g i).trans (Op.zero g)).trans (Op.zero u)) ?_
  obtain ⟨dn,hdn,nb⟩ := nk
  obtain ⟨dj,hdj,hb⟩ := hb
  refine ⟨l+3,dn+dj,by omega,fun x a B he ha hfit=>?_⟩
  let v := n x a
  let w := forNat (f x a) (z x a)
  let r (j) := put (put (put a g (w j)) s (v-j)) u j
  have es : g≠s := by omega
  have eg : g≠u := by omega
  have eus : s≠u := by omega
  have heq (j) : Agree k a (r j) :=
     Agree.put _ (Agree.put _ (Agree.put _ (fun _ _=>rfl) (by omega)) (by omega)) (by omega)
  have hag := ha g (by omega)
  have has := ha s (by omega)
  have hau := ha u (by omega)
  have hr0 (j) : r j g = w j := by simp [r,Ne.symm es,Ne.symm eg]
  have hr1 (j) : r j s = v-j := by simp [r,Ne.symm eus]
  have hr2 (j) : r j u = j := by simp [r]
  refine ⟨v,r,?_,fun j h=>?_,fun j h=>?_,by simp [cond_nz,hr1],?_,
     put_high0 _ ha ei⟩
  · have H := hn x a (put a g (z x a)) (Agree.put _ (fun _ _=>rfl) (by omega))
    dsimp only [start,r,w,forNat,setE]
    rw [← H]
    funext j
    by_cases u=j
    · subst j; simp [put,hau,eus,eg]
    · rename_i e; simp [put,e,v]
  · have hB : 0<B := by omega
    have hi := self_pow hB hdn
    have hd : B^dn≤B^(dn+dj) := Nat.pow_le_pow_right hB (by omega)
    have hj : B^dj≤B^(dn+dj) := Nat.pow_le_pow_right hB (by omega)
    have hv : v<B^dn := nb _ _ _ he hfit
    exact ⟨put_high0 _ (put_high0 _ (put_high0 _ (high_mono ha (by omega))
        (by omega)) (by omega)) (by omega),
      put_fit _ (put_fit _ (put_fit _ (fit_mono hfit (le_trans hi hd))
              (lt_of_lt_of_le (hb _ _ _ he hfit j h) hj)) (by omega))
        (by omega)⟩
  · refine ⟨by simp [cond_nz,hr1]; omega,?_⟩
    have hs : loopf x (r j)=w (j+1) := by
      dsimp only [loopf]
      rw [hr2,hr0,← hl x a _ ((heq j).mono hk.2.2)]
      rfl
    dsimp only [next,setE]
    rw [hs, put_ne _ _ _ u eg,hr2,put_ne _ _ _ s (Ne.symm eus),
        put_ne _ _ _ s es,hr1]
    funext m
    by_cases m1 : g=m
    · subst m; simp [Ne.symm eg, Ne.symm es,r]
    by_cases m2 : s=m
    · subst m; simp [Ne.symm eus, r]; try omega
    by_cases m3 : u=m
    · subst m; simp [eus,r]
    simp [r,m1,m2,m3]
  · dsimp only [done,setE]; rw [hr0]
    funext m
    by_cases m1 : g=m
    · subst m; simp [show i≠g by omega, hag,Ne.symm eg]
    by_cases m2 : u=m
    · subst m; simp [show i≠u by omega, hau]
    by_cases m3 : s=m
    · subst m; simp [show i≠s by omega, has,es,Ne.symm eus,r]
    by_cases m4 : i=m
    · subst m; simp [m1,m2,w,v]
    simp [m1,m2,m3,m4,r]

end ExactDerandomization.Counter

end

section

namespace ExactDerandomization.Counter

namespace E

lemma plus_sum {u v p q B d e : ℕ} (hu : u<B^d) (hv : v<B^e)
    (hp : p≤u) (hq : q≤v) (hb : 2≤B) : p+q<B^(d+e+1) := by
  have hx := Nat.pow_le_pow_right (show 0<B by omega) (show d≤d+e by omega)
  have hy := Nat.pow_le_pow_right (show 0<B by omega) (show e≤d+e by omega)
  rw [pow_succ]
  nlinarith

lemma addIter (a b : ℕ) : forNat (fun _ v=>v+1) a b = a+b := by
  induction b <;> simp_all [forNat, Nat.add_assoc]

lemma subIter (a b : ℕ) : forNat (fun _ v=>v-1) a b = a-b := by
  induction b <;> simp_all [forNat, Nat.sub_sub]

lemma mulIter (a b : ℕ) : forNat (fun _ v=>v+a) 0 b = a*b := by
  induction b <;> simp_all [forNat, Nat.mul_add]

variable {f g m r : NE}

lemma add (h : E f) (e : E g) : E (fun x a=> f x a + g x a) := by
  have H := E.iterate (fun _ _ _ v=>v+1) g f (fun _ _ _ e=> e.succ)
      e h ⟨0,fun _ _ _ _=>rfl⟩ (by
        obtain ⟨d,hd,h⟩ := h.bound; obtain ⟨D,hD,e⟩ := e.bound
        refine ⟨d+D+1,by omega,fun x a B hB ha j hj => ?_⟩
        rw [addIter]
        exact plus_sum (h _ _ _ hB ha) (e _ _ _ hB ha) le_rfl hj (by omega))
  simpa only [addIter] using H

lemma sub (h : E f) (e : E g) : E (fun x a=> f x a - g x a) := by
  have H := E.iterate (fun _ _ _ v=>v-1) g f (fun _ _ _ e=> e.pred) e h
      ⟨0,fun _ _ _ _=>rfl⟩ (by
        obtain ⟨d,hd,h⟩ := h.bound
        refine ⟨d,hd,fun x a B hB ha j hj => ?_⟩
        rw [subIter]
        exact lt_of_le_of_lt (Nat.sub_le _ _) (h _ _ _ hB ha))
  simpa only [subIter] using H

lemma mul (h : E f) (e : E g) : E (fun x a=> f x a * g x a) := by
  have H := E.iterate (fun x a _ v=>v+f x a) g (fun _ _=>0) (fun _ _ _ t=>t.add h)
      e (E.const 0) (by
        obtain ⟨k,h⟩ := h.1
        exact ⟨k,fun x a b hab=> by simp only [h x a b hab]⟩) (by
        obtain ⟨d,hd,h⟩ := h.bound; obtain ⟨D,hD,e⟩ := e.bound
        refine ⟨d+D,by omega,fun x a B hB ha j hj => ?_⟩
        simp only [mulIter,pow_add]
        have hh := e _ _ _ hB ha
        exact Nat.mul_lt_mul_of_lt_of_lt (h x a B hB ha) (lt_of_le_of_lt hj hh))
  simpa only [mulIter] using H

lemma pow_const (h : E f) (d : ℕ) : E (fun x a=> (f x a)^d) := by
  induction d with
  | zero => simpa using E.const 1
  | succ d e => simpa [pow_succ] using E.mul e h

lemma ite_le (h : E f) (e : E g) (s : E m) (t : E r) :
    E (fun x a => if f x a ≤ g x a then m x a else r x a) := by
  simpa only [Nat.sub_eq_zero_iff_le] using (h.sub e).ite s t

lemma ite_lt (h : E f) (e : E g) (s : E m) (t : E r) :
    E (fun x a => if f x a < g x a then m x a else r x a) :=
  ite_le (h.succ) e s t

lemma minE (h : E f) (e : E g) : E (fun x a => min (f x a) (g x a)) := by
  simpa only [min_def] using ite_le h e h e

lemma scan_right (x : Word) (m : ℕ) : scan x m = .rightMarker ↔ x.length < m := by
  unfold scan
  split <;> simp <;> omega

lemma length : E (fun x _ => x.length) := by
  let f (i) : Tr := fun x a => put a i (max (a i) (x.length+1))
  have hs (i : ℕ) : Op (f i) := by
    let t := fun s : InputSymbol => decide (s≠.rightMarker)
    apply Op.loop i t (Op.inc i)
    refine ⟨i+1,fun l hl=>⟨1,by decide,fun x a B hB hh hf=> ?_⟩⟩
    refine ⟨x.length+1-a i, fun j=>put a i (a i+j),by simp,fun j hj=>?_,
      fun j hj=>?_,?_,?_⟩
    · exact ⟨put_high0 _ hh (by omega),put_fit _ (by simpa using hf)
              (by have := hf i; simp; omega)⟩
    · simp [Cmd.cond,t,scan_right,Nat.add_assoc]; omega
    · simp [Cmd.cond,t,scan_right]; omega
    · dsimp [f]; congr 1; omega
  refine ⟨⟨0,fun _ _ _ _=>rfl⟩,fun i=>?_⟩
  simpa [setE,f] using (((Op.zero i).trans (hs i)).trans (Op.dec i))

lemma ite_eq (h : E f) (e : E g) (s : E m) (t : E r) :
    E (fun x a => if f x a = g x a then m x a else r x a) := by
  have H := ite_le h e (ite_le e h s t) t
  convert H using 1
  ext x a
  grind

lemma powStep (a b c : ℕ) :
    forNat (fun _ v=> min c (v*a)) (min c 1) b = min c (a^b) := by
  induction b with
  | zero => simp [forNat]
  | succ b ih =>
    simp only [forNat, ih, pow_succ]
    by_cases h : c ≤ a^b
    · rw [min_eq_left h]
      match a with
      | 0 => simp
      | a+1 =>
        have e : c ≤ c*(a+1) := by nlinarith
        have g : c ≤ (a+1)^b*(a+1) :=
           le_trans e (Nat.mul_le_mul_right (a+1) h)
        simp [e,g]
    · rw [min_eq_right (show a^b≤c by omega)]

lemma capPow (h : E f) (e : E g) (s : E m) :
    E (fun x a => min (m x a) ((f x a)^(g x a))) := by
  have H := E.iterate (fun x a _ v=>min (m x a) (v*f x a)) g
    (fun x a=> min (m x a) 1) (fun _ _ _ u=>s.minE (u.mul h))
    e (s.minE (E.const 1)) (by
      obtain ⟨k,h⟩ := h.1; obtain ⟨l,s⟩ := s.1
      exact ⟨k+l,fun x a b e=> by
        simp only [h x a b (e.mono (by omega)),s x a b (e.mono (by omega))]⟩) (by
      obtain ⟨d,hd,s⟩ := s.bound
      refine ⟨d,hd,fun x a B hB ha j _=>?_⟩
      simpa only [powStep] using
        lt_of_le_of_lt (min_le_left (m x a) ((f x a)^j)) (s x a B hB ha))
  simpa only [powStep] using H

lemma searchDiv (a b n : ℕ) :
    forNat (fun j v=> if b=0 then 0 else if (j+1)*b≤a then j+1 else v)
       0 n = min n (a/b) := by
  induction n with
  | zero => simp [forNat]
  | succ n ih =>
    simp only [forNat,ih]
    by_cases h : b=0
    · simp [h]
    rw [ite_eq_right h]
    have H := Nat.le_div_iff_mul_le (x:=n+1) (y:=a) (show 0<b by omega)
    split <;> omega

lemma div (h : E f) (e : E g) : E (fun x a=> f x a / g x a) := by
  let q x a (j v : ℕ) := if g x a = 0 then 0 else if (j+1)*g x a ≤ f x a then j+1 else v
  have H := E.iterate q f (fun _ _=>0) (fun _ _ j v=>e.ite (E.const 0)
    (((j.succ).mul e).ite_le h j.succ v))
    h (E.const 0) (by
      obtain ⟨k,h⟩ := h.1; obtain ⟨l,e⟩ := e.1
      exact ⟨k+l,fun x a b t=> by
        simp only [q,h x a b (t.mono (by omega)),e x a b (t.mono (by omega))]⟩) (by
      obtain ⟨d,hd,h⟩ := h.bound
      refine ⟨d,hd,fun x a B hB ha j hj=>?_⟩
      simp only [q,searchDiv]
      exact lt_of_le_of_lt (le_trans (min_le_left _ _) hj) (h _ _ _ hB ha))
  simpa only [q, searchDiv, min_eq_right (Nat.div_le_self ..)] using H

lemma mod (h : E f) (e : E g) : E (fun x a=> f x a % g x a) := by
  convert h.sub (e.mul (h.div e)) using 1
  ext x a
  have H := Nat.mod_add_div (f x a) (g x a); omega

end E

end ExactDerandomization.Counter

end

section

namespace ExactDerandomization.Counter

variable {S T : Type}

def Pick (f : Word → Store → S) : Prop :=
  ∀ g : S → NE, (∀ s, E (g s)) → E (fun x a=> g (f x a) x a)

lemma Pick.const (s : S) : Pick (fun _ _=>s) := fun _ h=> h s

lemma Pick.bind {f : Word → Store → S} {g : S → Word → Store → T}
    (h : Pick f) (e : ∀ s, Pick (g s)) :
    Pick (fun x a=> g (f x a) x a) := fun _ hk=> h _ (fun s=>e s _ hk)

lemma Pick.map {f : Word → Store → S} (h : Pick f) (g : S → T) :
    Pick (fun x a=> g (f x a)) := h.bind (g:=fun s _ _=>g s) (fun _=>Pick.const _)

lemma Pick.ite {f : Word → Store → Bool} (h : Pick f) {s t : NE} (e : E s) (g : E t) :
    E (fun x a=> if f x a then s x a else t x a) := by
  apply h (fun b x a=> if b then s x a else t x a); intro b
  cases b
  · simpa using g
  · simpa using e

lemma Pick.cond {f : Word → Store → Bool} (h : Pick f) {s t : Word → Store → S}
    (e : Pick s) (g : Pick t) :
    Pick (fun x a=> if f x a then s x a else t x a) := by
  apply h.bind (g:=fun b x a=> if b then s x a else t x a); intro b
  cases b
  · simpa using g
  · simpa using e

lemma Pick.test_lt {f g : NE} (e : E f) (h : E g) :
    Pick (fun x a=> decide (f x a<g x a)) := by
  intro s H
  convert e.ite_lt h (H true) (H false) using 1
  ext x a
  by_cases he : f x a<g x a <;> simp [he]

lemma Pick.test_eq {f g : NE} (e : E f) (h : E g) :
    Pick (fun x a=> decide (f x a=g x a)) := by
  intro s H
  convert e.ite_eq h (H true) (H false) using 1
  ext x a
  by_cases f x a=g x a <;> simp_all

lemma Pick.and {s t : Word → Store → Bool} (e : Pick s) (h : Pick t) :
    Pick (fun x a=> s x a && t x a) := by
  refine e.bind (g:=fun b x a=> b && t x a) (fun b=> h.map (fun u=> b&&u))

lemma Pick.tuple {n} {f : Word → Store → Fin n → S}
    (h : ∀ i, Pick (fun x a=> f x a i)) : Pick f := by
  induction n with
  | zero =>
    intro g hg
    convert hg (fun i=>Fin.elim0 i) using 1
    ext x a; congr 2; exact funext (fun i=>Fin.elim0 i)
  | succ n ih =>
    let p := fun x a (i : Fin n)=> f x a i.succ
    have hp : Pick p := ih (fun i=>h i.succ)
    convert (h 0).bind (g:=fun s x a=> Fin.cons (α:=fun _ : Fin (n+1) => S) s (p x a)) (fun s => hp.map
      (fun g : Fin n → S => Fin.cons (α:=fun _ : Fin (n+1) => S) s g)) using 1
    ext x a i
    refine Fin.cases ?_ ?_ i <;> simp [p]

lemma Pick.pos {n} {f : Word → Store → Fin n} (e : E fun x a => (f x a).val) :
    Pick f := by
  classical
  intro g hg
  have aux (s : Finset (Fin n)) :
      E (fun x a=> if f x a ∈ s then g (f x a) x a else 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using E.const 0
    | @insert b s h H =>
      convert e.ite_eq (E.const b.val) (hg b) H using 1
      ext x a
      by_cases f x a=b <;> simp_all; grind
  simpa using aux .univ

lemma Pick.read {f : NE} (h : E f) : Pick (fun x a=>scan x (f x a)) := by
  intro g e
  let u := InputSymbol.leftMarker
  let v := InputSymbol.rightMarker
  let b := InputSymbol.bit
  have hz (s : InputSymbol) {i j : NE} (e : E i) (k : E j) := h.bif (fun x=>decide (x=s)) e k
  have H := hz u (e u) (hz v (e v) (hz (b false) (e (b false)) (e (b true))))
  convert H using 1
  ext x a
  cases he : scan x (f x a) with
  | leftMarker => simp [he,u]
  | rightMarker => simp [he,u,v]
  | bit i => cases i <;> simp [he,u,v,b]

lemma Pick.all {n} (p : Word → Store → Fin n → Prop) [(x : Word) → (a : Store) → DecidablePred (p x a)]
    (h : ∀ i, Pick (fun x a=> decide (p x a i))) :
    Pick (fun x a=> decide (∀ i, p x a i)) := by
  let f (x a) (i : Fin n) := decide (p x a i)
  have hf : Pick f := Pick.tuple h
  convert hf.map (fun l=> decide (∀ i, l i=true)) using 1
  ext x a
  simp [f]

end ExactDerandomization.Counter

end

end OAI
