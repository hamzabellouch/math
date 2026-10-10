import OAI.Computability.Logspace.CounterPrograms

namespace OAI

/-!
Measured stack encodings and the realization of recursive programs with simultaneous space bounds.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Measured encodings. `cord` appends with overhead on just the new
piece, not the previously suspended stack. -/
namespace ExactDerandomization.Relay
open Counter

def lb (x : ℕ) := x.log2+1

lemma lb_pos (x) : 0<lb x := by dsimp [lb]; omega
lemma lb_zero : lb 0=1 := rfl
lemma lb_one : lb 1=1 := rfl
lemma below (x) : x < 2^lb x := Nat.lt_log2_self
lemma above {x:ℕ} (h:0<x) : 2^(lb x)  ≤  2*x := by
   unfold lb; rw [pow_succ]
   have he : 2^x.log2 ≤ x := Nat.log2_self_le (by omega)
   omega
lemma modest {x k : ℕ} (h:x < 2^k) (e:1 ≤ k) : lb x ≤ k := by
   by_cases hx : x=0
   · simpa [hx,lb_zero]
   by_contra! hh
   have he : lb x ≥ k+1 := by omega
   have ht := le_trans (Nat.pow_le_pow_right (Nat.zero_lt_two) he) (above (x:=x) (by omega))
   rw [pow_succ] at ht
   omega
lemma growing (x : ℕ) : x+1 ≤ 2^x := by
   induction x with
   | zero=> simp
   | succ x ih=> rw [pow_succ]; omega
lemma lb_le_inc (x : ℕ) : lb x ≤ x+1 :=
    modest (lt_of_lt_of_le (show x < (x+1)+1 by omega) (growing _)) (by omega)
lemma lb_mono {x y} (h:x ≤ y) : lb x ≤ lb y:=
   modest (h.trans_lt (below _)) (lb_pos y)
lemma lb_succ (x) : lb (x+1)  ≤  lb x+1 :=
   modest (by have:= below x; rw [pow_succ]; omega) (by omega)
lemma lb_plus (x y) : lb (x+y) ≤ max (lb x) (lb y)+1 := by
   apply modest _ (by omega)
   have xx := (below x).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (le_max_left (lb x) (lb y)))
   have yy := (below y).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (le_max_right (lb x) (lb y)))
   rw [pow_succ]; omega
lemma lb_times (x y) : lb (x*y)  ≤ lb x+lb y :=
    modest (by rw [pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt (below x) (below y))
         ((lb_pos x).trans_le (by omega))
lemma lb_shift (x) : lb (2^x)=x+1 := by
   apply le_antisymm
   · have ht : 0<(2:ℕ)^x := by positivity
     exact modest (by rw [pow_succ]; omega) (by omega)
   by_contra! he
   have hs:=Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two (show lb (2^x) ≤ x by omega)
   have he:=below (2^x); omega

def cord (a s : ℕ) : ℕ := 2^(lb a) * (1+ 2*a +2^(lb a+1)*s)

lemma cord_bounds (a s : ℕ) (hs : 1  ≤  s) :
   2 ^ (lb s-1+(2*lb a+1))  ≤  cord a s ∧ cord a s<2^(lb s+ (2*lb a+1)) := by
   let k:=lb a
   have he1 := (below a)
   have he2 := (below s)
   have he3 : 2^(lb s-1) ≤ s := by
      simp only [lb, Nat.add_sub_cancel]
      exact Nat.log2_self_le (by omega)
   have he4 (i) : 2^(i+(2*k+1)) = 2^k*(2^(k+1)* (2:ℕ)^i) := by
      rw [show i+(2*k+1)=k+((k+1)+i) by omega,pow_add,pow_add]
   change 2^(lb s-1+ (2*k+1))  ≤  2^k*(1+2*a+2^(k+1)*s) ∧
        2^k*(1+2*a+2^(k+1)*s) < 2^(lb s+(2*k+1))
   simp only [he4]
   constructor
   · exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left (2^(k+1)) he3).trans (by omega))
   apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
   have he := Nat.mul_le_mul_left (2^(k+1)) (show s+1  ≤  2^(lb s) from he2)
   change a < 2^k at he1
   nlinarith [pow_succ (2:ℕ) k]

lemma lb_cord (a s : ℕ) (hs : 1  ≤  s) :
   lb (cord a s)=lb s+(2*lb a+1) := by
  obtain ⟨ha,hb⟩:=cord_bounds a s hs
  apply le_antisymm (modest hb (by omega))
  by_contra! h
  have h1:=lb_pos s
  have h2:=Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two
          (show lb (cord a s)  ≤  lb s-1+(2*lb a+1) by omega)
  have he:=below (cord a s)
  omega

lemma cord_fine (a s : ℕ) : s< cord a s ∧ a<cord a s ∧ 1 < cord a s := by
   have h : 2  ≤  2^(lb a):=by
      simpa using Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two (lb_pos a)
   unfold cord; rw [pow_succ]
   have he := Nat.mul_le_mul_right (1+ 2*a +2^lb a*2*s) h
   have hz := Nat.mul_le_mul_right s h
   refine ⟨?_,?_,?_⟩ <;> nlinarith

def discover (x : ℕ) (k : ℕ) : ℕ :=
   forNat (fun j t=> if x % (min (x+1) (2^(j+1)))=0 then j+1 else t) 0 k

def pierce (x : ℕ) := discover x x
def wing (x : ℕ) := min (x+1) (2^pierce x)
def middle (x : ℕ) := x/ wing x /2
def fore (x) := middle x % wing x
def aft (x) := middle x / wing x

lemma pierce_rule (a s : ℕ) : pierce (cord a s)=lb a := by
   let k:=lb a
   let n:=2^k
   let x:=cord a s
   let w:=a+n*s
   have hn : 0<n := by dsimp [n]; positivity
   have hx : x = n*(1+2*w) := by simp only [x,w,n,k,cord,pow_succ]; ring
   have hh : n  ≤  x := by nlinarith
   have hp (j : ℕ) : x%min (x+1) (2^j)=0 ↔ j ≤ k := by
      by_cases hg : j ≤ k
      · have he : 2^j ∣ x := (pow_dvd_pow _ hg).trans (hx ▸ ⟨_,rfl⟩)
        have ht : 2^j  ≤  x+1 := by
           have h2 : 2^j ≤ n := Nat.pow_le_pow_right Nat.zero_lt_two hg; omega
        simp [hg,ht,Nat.mod_eq_zero_of_dvd he]
      by_cases ho : 2^j  ≤  x+1
      · rw [min_eq_right ho]; refine ⟨fun he=>?_,fun e=>by omega⟩
        have he1:= (pow_dvd_pow 2 (show k+1 ≤ j by omega)).trans (Nat.dvd_of_mod_eq_zero he)
        rw [pow_succ,hx] at he1
        obtain ⟨b,hb⟩:=he1
        change n*(1+2*w)=n*2*b at hb
        rw [mul_assoc] at hb
        have ht := Nat.eq_of_mul_eq_mul_left hn hb
        omega
      rw [min_eq_left (by omega),Nat.mod_eq_of_lt (by omega)]; omega
   have hi (j) : discover x j=min j k := by
      induction j with
      | zero=> simp [discover,forNat]
      | succ j ih=>
         change (if _ then _ else discover x j)=_
         rw [ih]; simp only [hp]
         by_cases he:j+1 ≤ k
         · simp [he]
         have ht:k≤j:=by omega
         simp [he,ht,le_trans ht (show j ≤ j+1 by omega)]
   have hv:=growing k
   change k+1 ≤ n at hv
   exact (hi x).trans (by omega)

@[simp] lemma wing_cord (a s) : wing (cord a s)=2^lb a := by
   rw [wing,pierce_rule, min_eq_right]
   unfold cord
   apply le_trans (show _ ≤ 2^lb a*(1+2*a+ 2^(lb a+1)*s) from ?_) (by omega)
   exact Nat.le_mul_of_pos_right _ (by omega)

lemma middle_cord (a s) : middle (cord a s)=a+2^(lb a)*s := by
   rw [middle,wing_cord,cord,pow_succ]
   rw [Nat.mul_div_cancel_left _ (by positivity)]
   have he : 1+2*a+2^(lb a)*2*s=1+(a+2^(lb a)*s)*2 :=by ring
   rw [he,Nat.add_mul_div_right _ _ (by omega)]
   simp

@[simp] lemma fore_cord (a s) : fore (cord a s)=a := by simp [fore,middle_cord,Nat.mod_eq_of_lt (below a)]
@[simp] lemma aft_cord (a s) : aft (cord a s)=s := by
   rw [aft,middle_cord,wing_cord,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt (below a),
       zero_add]

def bead (a b : ℕ) : ℕ := cord a (b+1)
def heed (n : ℕ) := fore n
def readt (n : ℕ) := aft n-1

@[simp] lemma heed_eq (a b) : heed (bead a b)=a := by simp [heed,bead]
@[simp] lemma read_eq (a b) : readt (bead a b)=b := by simp [readt,bead]

lemma bead_small (a b) : lb (bead a b)  ≤  2*lb a + lb b +2 := by
   rw [bead,lb_cord _ _ (by omega)]
   have:= lb_succ b; omega

end ExactDerandomization.Relay

end

section

namespace ExactDerandomization.Relay
open Counter

def hunt (x k : ℕ) := forNat (fun j a=> if min (x+1) (2^(j+1)) ≤ x then j+1 else a) 0 k

lemma under_pow (x j : ℕ) :
    min (x+1) (2^(j+1)) ≤ x ↔ j+1 ≤ x.log2 := by
   by_cases h:x=0
   · subst x
     have hs : 1 ≤ (2:ℕ)^(j+1) := Nat.one_le_pow _ _ (by omega)
     simp [hs]
   have hs : 2^x.log2 ≤ x := Nat.log2_self_le h
   have he := below x
   unfold lb at he
   constructor
   · intro hf; have hl : 2^(j+1) ≤ x:=by omega
     by_contra! hm
     have hg := (Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two (show x.log2+1 ≤ j+1 by omega))
     omega
   intro hh
   have hl : 2^(j+1) ≤ x := le_trans (Nat.pow_le_pow_right Nat.zero_lt_two hh) hs
   omega

lemma found (x k) : hunt x k=min k x.log2 := by
   induction k with
   | zero=> simp [hunt,forNat]
   | succ k ih=>
     change (if _ then _ else hunt x k)=_
     rw [ih]; simp only [under_pow]
     by_cases h:k+1≤x.log2
     · simp [h]
     have he : x.log2≤ k := by omega
     simp [h,he,show x.log2≤ k+1 by omega]

variable {f g : NE}

/-- E calculation of a "current or small index" loop -/
lemma run_huntE (f : NE) (p : ℕ→ℕ→Prop) [(x y : ℕ) → Decidable (p x y)]
    (hp : ∀ {g j:NE}, E g → E j → Counter.Pick (fun x a => decide (p (g x a) (j x a))))
    (h : E f) :
    E (fun x a => forNat
         (fun j v=> if p (f x a) j then j+1 else v) 0 (f x a)) := by
   apply E.iterate (fun x a j v=> if p (f x a) j then j+1 else v) f (fun _ _=>0)
   · intro g j hg he
     simpa only [decide_eq_true_eq] using (hp h hg).ite hg.succ he
   · exact h
   · exact E.const 0
   · obtain ⟨k,h⟩:=h.1; exact ⟨k,fun x a b e=>by rw [h x a b e]⟩
   obtain ⟨d,hp,he⟩:=h.bound
   refine ⟨d,hp,fun x a B hb hs j hj=>?_⟩
   have hl (j) : forNat (fun j v=> if p (f x a) j then j+1 else v) 0 j ≤ j := by
      induction j <;> simp only [forNat]
      · exact le_rfl
      split <;> omega
   exact lt_of_le_of_lt (le_trans (hl j) hj) (he _ _ _ hb hs)

lemma log2E (h:E f) : E (fun x a=> (f x a).log2) := by
   have he (n) : hunt n n=n.log2 := (found n n).trans
     (min_eq_right (by have he:=lb_le_inc n; unfold lb at he; omega))
   simp_rw [← he]
   apply run_huntE _ (fun x j=> min (x+1) (2^(j+1)) ≤ x) _ h
   intro x j hx hj
   have hr := E.capPow (E.const 2) hj.succ hx.succ

   convert Pick.test_eq (hr.sub hx) (E.const 0) using 1
   ext x a
   simp
   omega

lemma lbE (h:E f) : E (fun x a=> lb (f x a)) := (log2E h).succ
lemma digitsE (h:E f) : E (fun x a=> 2^lb (f x a)) := by
   have he(n) : min (2*(n+1)) (2^lb n)=2^lb n := by
      apply min_eq_right
      by_cases h:n=0
      · subst n; simp [lb_zero]
      have he:=above (x:=n) (by omega); omega
   simpa only [he] using E.capPow (E.const 2) (lbE h) ((E.const 2).mul h.succ)

lemma cordE (h:E f) (e:E g) : E (fun x a=> cord (f x a) (g x a)) := by
   unfold cord; simp_rw [pow_succ]
   have ht:=digitsE h
   exact ht.mul (((E.const 1).add ((E.const 2).mul h)).add ((ht.mul (E.const 2)).mul e))
lemma pierceE (h:E f) : E (fun x a=> pierce (f x a)) := by
   apply run_huntE _ (fun x j=> x%min (x+1) (2^(j+1))=0) _ h
   intro x j hx hj
   exact Pick.test_eq (hx.mod (E.capPow (E.const 2) hj.succ hx.succ)) (E.const 0)
lemma wingE (h:E f) : E (fun x a=> wing (f x a)) :=
   E.capPow (E.const 2) (pierceE h) h.succ
lemma middleE (h:E f) : E (fun x a=> middle (f x a)) := (h.div (wingE h)).div (E.const 2)
lemma foreE (h:E f) : E (fun x a=> fore (f x a)) := (middleE h).mod (wingE h)
lemma aftE (h:E f) : E (fun x a=> aft (f x a)) := (middleE h).div (wingE h)

def Uni (f : Word → ℕ → ℕ) := ∀ ⦃g : NE⦄,E g → E fun x a=> f x (g x a)

class Wire (α:Type) where
    enc : α→ℕ
    dec : ℕ→α
    eq : ∀ a,dec (enc a)=a
    tidy : Uni (fun _ i=>enc (dec i))

export Wire (enc dec)

abbrev measure {α} [Wire α] (a : α) := lb (enc a)

instance : Wire ℕ := ⟨id,id,fun _=>rfl,fun _ h=>h⟩
lemma enc_nat (n:ℕ) : enc n=n := rfl

instance {α β} [Wire α] [Wire β] : Wire (α×β) where
   enc p:= bead (enc p.1) (enc p.2)
   dec i:= (dec (heed i),dec (readt i))
   eq p:= by simp [Wire.eq]
   tidy:= by
     intro g h
     have he:= @Wire.tidy α _
     have ht:= @Wire.tidy β _
     exact cordE (he (foreE h)) (ht (aftE h).pred).succ

instance : Wire Bool where
   enc p:= if p then 1 else 0
   dec i:= decide (1 ≤ i)
   eq p:= by cases p <;> simp
   tidy:= by
     intro g h
     have hg:= E.ite_le (E.const 1) h (E.const 1) (E.const 0)
     simpa only [decide_eq_true_eq] using hg

@[simp] lemma dec_round {α} [Wire α] (a : α) : dec (enc a)=a := Wire.eq a
lemma measure_pair {α β} [Wire α] [Wire β] (a : α) (b:β) :
    measure (a,b) ≤2*measure a+measure b+2:=bead_small _ _

/-- Pointwise semantic LF functions requiring only wire encodings. -/
abbrev PT (α β : Type) := Word→α→β

def Kn {α β : Type} [Wire α] [Wire β] (f : PT α β) := Uni fun x a => enc (f x (dec a))

namespace Kn
variable {α β γ δ : Type} [Wire α] [Wire β] [Wire γ] [Wire δ]

lemma identity : Kn (fun (_:Word) (x:α)=>x) := Wire.tidy

lemma comp {f:PT α β} {g:PT β γ} (h:Kn g) (e:Kn f) :
   Kn (fun x a=> g x (f x a)) := by
   intro v hv
   simpa only [Wire.eq] using h (e hv)
lemma tuple {f:PT α β} {g:PT α γ} (h:Kn f) (k:Kn g) :
   Kn (fun x a=> (f x a,g x a)) := by
   intro v hv
   exact cordE (h hv) (k hv).succ
lemma first : Kn (fun (_:Word) (x:α×β)=> x.1) := by
   intro g h
   exact @Wire.tidy α _ _ (foreE h)
lemma next : Kn (fun (_:Word) (x:α×β)=> x.2) := by
   intro g h
   exact @Wire.tidy β _ _ (aftE h).pred
lemma left {f:PT α (β×γ)} (h:Kn f) : Kn (fun x a=> (f x a).1) := first.comp h
lemma right {f:PT α (β×γ)} (h:Kn f) : Kn (fun x a=> (f x a).2) := next.comp h
lemma wash : Kn (fun (_:Word) (x:α)=>enc x):= Wire.tidy
lemma unpack : Kn (fun (_:Word) (x:ℕ)=> (dec x:α)):= Wire.tidy
lemma fix (b:β) : Kn (fun (_:Word) (_:α)=>b):= fun _ _=> E.const _
lemma word (b : Word→β) (h:E (fun x _=>enc (b x))) :
    Kn (fun (x:Word) (_:α)=>b x) := fun _ _=>h

variable {f g t w : PT α ℕ}

lemma add (h:Kn f) (e:Kn g) : Kn (fun x a=> f x a+g x a):=fun _ u=>(h u).add (e u)
lemma sub (h:Kn f) (e:Kn g) : Kn (fun x a=> f x a-g x a):=fun _ u=>(h u).sub (e u)
lemma times (h:Kn f) (e:Kn g) : Kn (fun x a=> f x a*g x a):=fun _ u=>(h u).mul (e u)
lemma div (h:Kn f) (e:Kn g) : Kn (fun x a=> f x a/g x a):=fun _ u=>(h u).div (e u)
lemma mod (h:Kn f) (e:Kn g) : Kn (fun x a=> f x a%g x a):=fun _ u=>(h u).mod (e u)
lemma power (d:ℕ) (h:Kn f) : Kn (fun x a=> (f x a)^d) := fun _ u=>E.pow_const (h u) d
lemma succ (h:Kn f) : Kn (fun x a=> f x a+1):=h.add (fix (α:=α) (1:ℕ))
lemma pred (h:Kn f) : Kn (fun x a=> f x a-1):=h.sub (fix (α:=α) (1:ℕ))

lemma cond {f g:PT α β} {s:PT α Bool} (hs:Kn s) (h:Kn f) (e:Kn g) :
    Kn (fun x a=> if s x a then f x a else g x a) := by
   intro u hu
   convert (hs hu).ite (e hu) (h hu) using 1
   ext x a; cases hv:s x (dec (u x a)) <;> simp [Wire.enc,hv]

lemma le (h:Kn f) (e:Kn g) : Kn (fun x a=> decide (f x a ≤ g x a)) := by
   intro u hu
   have ht:= (h hu).ite_le (e hu) (E.const 1) (E.const 0)
   convert ht using 1; ext x a; simp [Wire.enc]
lemma lt (h:Kn f) (e:Kn g) : Kn (fun x a=> decide (f x a < g x a)) :=
   h.succ.le e
lemma eq (h:Kn f) (e:Kn g) : Kn (fun x a=> decide (f x a=g x a)) := by
   intro u hu
   have ht:= (h hu).ite_eq (e hu) (E.const 1) (E.const 0)
   convert ht using 1; ext x a; simp [Wire.enc]
lemma cond_le (h:Kn f) (e:Kn g) {u v:PT α β} (hu:Kn u) (hv:Kn v) :
    Kn (fun x a=> if f x a ≤ g x a then u x a else v x a) := by
   simpa only [decide_eq_true_eq] using (h.le e).cond hu hv
lemma cond_lt (h:Kn f) (e:Kn g) {u v:PT α β} (hu:Kn u) (hv:Kn v) :
    Kn (fun x a=> if f x a < g x a then u x a else v x a) := by
   simpa only [decide_eq_true_eq] using (h.lt e).cond hu hv
lemma cond_eq (h:Kn f) (e:Kn g) {u v:PT α β} (hu:Kn u) (hv:Kn v) :
    Kn (fun x a=> if f x a=g x a then u x a else v x a) := by
   simpa only [decide_eq_true_eq] using (h.eq e).cond hu hv
lemma cap (h:Kn t) (k:Kn f) (u:Kn g) :
    Kn (fun x a=> min (t x a) ((f x a)^(g x a))) :=
   fun _ e=>E.capPow (k e) (u e) (h e)
lemma small (h:Kn f) (k:Kn g) : Kn (fun x a=> min (f x a) (g x a)) :=
    fun _ e=>E.minE (h e) (k e)
lemma bl (h:Kn f) : Kn (fun x a=> lb (f x a)) := fun _ e=>lbE (h e)

lemma push (h:Kn f) (k:Kn g) :
    Kn (fun x a=> cord (f x a) (g x a)):= fun _ e=>cordE (h e) (k e)
lemma top (h:Kn f) :
    Kn (fun x a=> fore (f x a)):= fun _ e=>foreE (h e)
lemma tail (h:Kn f) :
    Kn (fun x a=> aft (f x a)):= fun _ e=>aftE (h e)

/-- LF state loops with a uniform numeric ceiling given by another LF expression -/
lemma stroll (step : PT (α×ℕ×ℕ) ℕ)
    (n z limit : PT α ℕ)
    (h : Kn step) (hn:Kn n) (hz:Kn z) (he:Kn limit)
    (hp : ∀ x a,∀ j≤ n x a, forNat (fun k v=>step x (a,k,v)) (z x a) j ≤ limit x a) :
    Kn (fun x a=> forNat (fun k v=> step x (a,k,v)) (z x a) (n x a)) := by
   intro g hg
   let f (x : Word) (a : Store) (j v: ℕ) := step x ((dec (g x a):α), j, v)
   apply E.iterate f (fun x a=> n x (dec (g x a))) (fun x a=> z x (dec (g x a)))
   · intro j v hj hv
     have eu : E (fun x a=> enc ((dec (g x a):α), j x a, v x a)) :=
       cordE (@Wire.tidy α _ _ hg) (cordE hj hv.succ).succ
     simpa only [Wire.eq,enc_nat,f] using h eu
   · exact hn hg
   · exact hz hg
   · obtain ⟨k,h⟩:=hg.1; exact ⟨k,fun x a b e=>by simp only [f,h x a b e]⟩
   obtain ⟨d,hd,h⟩:=(he hg).bound
   exact ⟨d,hd,fun x a B e u j v => lt_of_le_of_lt (hp x (dec (g x a)) j v) (h x a B e u)⟩

end Kn
end ExactDerandomization.Relay

end

section

namespace ExactDerandomization.Relay
open Counter

lemma cord_mono {a b c d} (h:a≤b) (e:c≤d) : cord a c≤cord b d := by
   have ht:=lb_mono h
   unfold cord; gcongr
lemma bead_mono {a b c d} (h:a≤b) (e:c≤d) : bead a c≤bead b d := cord_mono h (by omega)
lemma pair_mono {a b c d : ℕ} (h:a≤b) (e:c≤d) : enc (a,c)≤enc (b,d):=bead_mono h e

lemma Kn.fold {α β : Type} [Wire α] [Wire β] (step : PT (α× ℕ×β) β)
    (z : PT α β) (n lim : PT α ℕ)
    (hf: Kn step) (hz:Kn z) (ht:Kn n) (he: Kn lim)
    (hh : ∀ x a,∀ j≤ n x a, enc (forNat (fun k v=>step x (a,k,v)) (z x a) j) ≤ lim x a) :
    Kn (fun x a=> forNat (fun k v=>step x (a,k,v)) (z x a) (n x a)) := by
   let f : PT (α×ℕ×ℕ) ℕ := fun x u=> enc (step x (u.1,u.2.1,dec u.2.2))
   have hu(x a j) :
       forNat (fun k v=>f x (a,k,v)) (enc (z x a)) j= enc
           (forNat (fun k v=>step x (a,k,v)) (z x a) j) := by
     induction j <;> simp_all [forNat,f]
   have hn : Kn f := wash.comp (hf.comp
          (first.tuple (next.left.tuple (unpack.comp next.right))))
   have h:= stroll f _ _ _ hn ht (wash.comp hz) he (fun x a j hv=>by rw [hu]; exact hh x a j hv)
   simpa only [hu,Wire.eq] using (unpack (α:=β)).comp h

def mesh : List ℕ → ℕ
   | []=>1
   | a::b=>cord a (mesh b)
lemma mesh_length (l) : l.length < mesh l:=by
    induction l with
    | nil=>simp [mesh]
    | cons a l ih=> exact lt_of_le_of_lt ih (cord_fine a (mesh l)).1
lemma mesh_pos (l) : 1≤ mesh l:= (Nat.zero_le _).trans_lt (mesh_length l)
lemma measure_mesh (a l) : lb (mesh (a::l))=lb (mesh l)+(2*lb a+1) :=
    lb_cord _ _ (mesh_pos l)

lemma mesh_append (l r) : lb (mesh (l++r))+1=lb (mesh l)+lb (mesh r) := by
   induction l with
   | nil=> simp [mesh,lb_one,Nat.add_comm]
   | cons v l ih=>
     simp only [List.cons_append,measure_mesh]
     omega
lemma mesh_reverse (l) : lb (mesh l.reverse)=lb (mesh l) := by
   induction l with
   | nil=> simp
   | cons a l ih=>
     rw [List.reverse_cons,measure_mesh]
     have ht:=mesh_append l.reverse [a]; rw [measure_mesh,ih] at ht
     change _+1=lb (mesh l)+(lb 1+_) at ht; rw [lb_one] at ht
     omega

def ebb {α} (f:PT (α×ℕ×ℕ) ℕ) (x : Word) (a : α) (lim load : ℕ) (v:ℕ×ℕ) : ℕ×ℕ :=
   if v.1≤1 then v else (min load (aft v.1),min lim (f x (a,fore v.1,v.2)))
def sweep {α} (f:PT (α×ℕ×ℕ) ℕ) (r z lim : PT α ℕ) : PT α ℕ :=
   fun x a=>
   (forNat (fun _ v=>ebb f x a (lim x a) (r x a) v)
      (r x a,min (lim x a) (z x a)) (r x a)).2

lemma Kn.sweepK {α : Type} [Wire α] (f:PT (α×ℕ×ℕ) ℕ) (r z lim : PT α ℕ)
   (hf:Kn f) (hr:Kn r) (hz:Kn z) (h:Kn lim) : Kn (sweep f r z lim) := by
   let step : PT (α×ℕ×(ℕ×ℕ)) (ℕ×ℕ) := fun x a=> ebb f x a.1 (lim x a.1) (r x a.1) a.2.2
   let src : PT α (ℕ×ℕ) := fun x a=>(r x a,min (lim x a) (z x a))
   have hv : Kn step := by
     have h1 : Kn (fun (_:Word) (a:α×ℕ×(ℕ×ℕ))=> a.1):=first
     have ht : Kn (fun (_:Word) (a:α×ℕ×(ℕ×ℕ))=> a.2.2):=next.right
     exact ht.left.cond_le (fix 1) ht (((hr.comp h1).small ht.left.tail).tuple
       ((h.comp h1).small (hf.comp (h1.tuple (ht.left.top.tuple ht.right)))))
   have hh : Kn src := hr.tuple (h.small hz)
   have he : Kn (fun x a=>enc ((r x a),(lim x a))) := wash.comp (hr.tuple h)
   apply right (fold step src r _ hv hh hr he ?_)
   intro x a j _
   let p:= forNat (fun k v=>step x (a,k,v)) (src x a)
   have h1 (j) : (p j).1 ≤ r x a ∧ (p j).2≤ lim x a := by
     induction j with
     | zero=> exact ⟨le_rfl,min_le_left ..⟩
     | succ j ih=>
       change (ebb _ _ _ _ _ (p j)).1 ≤ _ ∧ (ebb _ _ _ _ _ (p j)).2 ≤ _
       unfold ebb; split
       · exact ih
       · exact ⟨min_le_left ..,min_le_left ..⟩
   exact pair_mono (h1 j).1 (h1 j).2

inductive Scan (lim:ℕ) (g:ℕ→ℕ→ℕ) : ℕ→List ℕ→ℕ→Prop
   | nil {x} (h:x≤lim) : Scan lim g x [] x
   | cons {x a l y} (h:x≤lim) (e:Scan lim g (g a x) l y) : Scan lim g x (a::l) y
lemma Scan.start {l g a v y} (h:Scan l g a v y) : a≤l := by cases h <;> assumption

lemma forNat_cons {α} (f:α→α) (x : α) (n : ℕ) :
    forNat (fun _=>f) x (n+1)=forNat (fun _=>f) (f x) n := by
   induction n with
   | zero=> rfl
   | succ n ih=>
     rw [forNat,ih]
     rfl

lemma exact_ebb {α} {f:PT (α×ℕ×ℕ) ℕ} {x lim load l a y z}
   (h:Scan lim (fun v w=> f x (a,v,w)) z l y) (e:mesh l≤load) (n:ℕ) (hh:l.length≤ n) :
   forNat (fun _ v=>ebb f x a lim load v) (mesh l,z) n=(1,y) := by
   induction h generalizing n with
   | @nil z h=>
     induction n with
     | zero=> rfl
     | succ n ih=>
       simp only [forNat,ih (by simp)]
       simp [ebb]
   | @cons u v l y h g ih=>
     cases n with
     | zero=> simp at hh
     | succ n=>
       let a0:=mesh (v::l)
       change mesh (v::l)≤ load at e
       have he := cord_fine v (mesh l)
       have ht : ¬mesh (v::l) ≤ 1 := not_le_of_gt he.2.2
       have hh1 : mesh l≤load := he.1.le.trans e
       rw [forNat_cons]
       change forNat _ (ebb f x a lim load (mesh (v::l),u)) n=_
       change ¬cord v (mesh l) ≤ 1 at ht
       unfold ebb; simp only [ht,mesh, ↓reduceIte,fore_cord,aft_cord,min_eq_right hh1,min_eq_right g.start]
       exact ih hh1 n (by simpa using hh)

lemma exact_sweep {α} {f : PT (α×ℕ×ℕ) ℕ} {r z lim : PT α ℕ} {x a l y}
    (h:Scan (lim x a) (fun i j=> f x (a,i,j)) (z x a) l y)
    (e:r x a=mesh l) :
   sweep f r z lim x a=y := by
   unfold sweep; rw [e,min_eq_right h.start]
   rw [exact_ebb h le_rfl _ (mesh_length _).le]

def caplen (n:ℕ) := 2^lb n
def windback (_:Word) (n:ℕ) :=
    sweep (fun _ (i : ℕ×ℕ×ℕ) => cord i.2.1 i.2.2)
      (fun _ k=>k) (fun _ _=>1) (fun _ k=>caplen k) [] n

lemma Kn.caplenK : Kn (fun (_:Word) (n:ℕ)=>caplen n) := fun _ h=>digitsE h
lemma Kn.windbackK : Kn windback :=
   sweepK _ _ _ _ (next.left.push next.right) identity (fix 1) caplenK

lemma backscan (l r:List ℕ) (lim) (h:2^lb (mesh (l++r)) ≤ lim) :
    Scan lim cord (mesh r) l (mesh (l.reverse++r)) := by
   induction l generalizing r with
   | nil=>
     simp only [List.nil_append,List.reverse_nil]
     exact .nil ((below _).le.trans (by simpa using h))
   | cons a l ih=>
     have he r : lb (mesh l)+lb (mesh r)=lb (mesh (l++r))+1 := (mesh_append l r).symm
     have hs : List.reverse (a::l)++r=l.reverse++(a::r) :=by simp
     have hu : lb (mesh r) ≤ lb (mesh ((a::l)++r)) := by
       simp only [List.cons_append,measure_mesh]
       have := he r; have h1:=lb_pos (mesh l); omega
     rw [hs]
     apply Scan.cons ((below (mesh r)).le.trans ((Nat.pow_le_pow_right Nat.zero_lt_two hu).trans h))
     apply ih (a::r)
     have hw : lb (mesh (l++a::r))=lb (mesh ((a::l)++r)) := by
        have h1:=he (a::r)
        rw [measure_mesh] at h1
        simp only [List.cons_append,measure_mesh]
        have := he r; omega
     rw [hw]; exact h

lemma windback_mesh (x) (l:List ℕ) : windback x (mesh l)=mesh l.reverse := by
   have h:=backscan l [] (caplen (mesh l)) (by simp [caplen])
   exact exact_sweep (by simpa only [List.append_nil,mesh] using h) rfl

end ExactDerandomization.Relay

end

section

/-!
A recursive fixed program interface (only for algorithms whose
space certificates include the suspended calls). The replayed child
query is computed from the caller's tuple and suspended record. In
particular that recipe has **no** access to the caller's shared cursor.
Computed through already uniform functions (LF), charging those as
ephemeral scratch of log magnitude. -/
namespace ExactDerandomization.Relay
open Counter

structure Cub (α β : Type) [Wire α] [Wire β] where
    f : PT α β
    runs : Kn f

abbrev Site := ℕ×ℕ
abbrev Plot := ℕ×Site
abbrev Slip := ℕ×ℕ
abbrev Drain := Slip × Site
abbrev Flag := Cub Plot Bool

inductive Cog where
   | edit (move : Cub Plot Site)
   | toss (stem : Cub Slip ℕ) (send : Cub Drain Site)
   | seq (p q : Cog)
   | bif (cond : Flag) (p q : Cog)
   | loop (cond : Flag) (p : Cog)

structure Fare where
   limit : ℕ
   meter : ℕ→ℕ
def Fare.atm (v:Fare) (q : ℕ) (p : Site) :=
    q ≤ v.limit ∧ p.2 ≤ v.limit ∧ lb p.1≤v.meter q

def Fare.pull (v:Fare) (q h q':ℕ) := lb h+1+v.meter q'≤v.meter q

inductive Boots (x:Word) (F:Fare) (main : Cog) :
     ℕ → Cog → Site → Site → Prop
   | edit {q p a b} : p.f x (q,a)=b → F.atm q a → F.atm q b →
       Boots x F main q (.edit p) a b
   | toss {q p e a a' b q'} :
       p.f x (q,a.1)=q' → e.f x ((q,a.1),a')=b →
       F.atm q a → F.atm q b → F.pull q a.1 q' →
       Boots x F main q' main (0,a.2) a' →
       Boots x F main q (.toss p e) a b
   | seq {q p s a b c} : Boots x F main q p a b → Boots x F main q s b c →
       Boots x F main q (.seq p s) a c
   | yes {q u p s a b} : u.f x (q,a)=true → Boots x F main q p a b →
       Boots x F main q (.bif u p s) a b
   | no {q u p s a b} : u.f x (q,a)=false → Boots x F main q s a b →
       Boots x F main q (.bif u p s) a b
   | more {q u p a b c} : u.f x (q,a)=true → Boots x F main q p a b →
       Boots x F main q (.loop u p) b c →
       Boots x F main q (.loop u p) a c
   | lend {q u p a} : u.f x (q,a)=false → F.atm q a →
       Boots x F main q (.loop u p) a a

lemma Boots.fits {x F main q p a b} (h:Boots x F main q p a b) :
    F.atm q a ∧ F.atm q b:= by induction h <;> grind

inductive Act where
   | edit (move : Cub Plot Site) (goal : ℕ)
   | fork (u : Flag) (A B : ℕ)
   | toss (p : Cub Slip ℕ) (e : Cub Drain Site) (goal : ℕ)
   | rest

structure Grid where
    slot : ℕ
    entry : ℕ
    prog : ℕ → Act
    low : entry ≤ slot
    shut : prog 0=.rest
    dome : ∀ i,slot < i → prog i=.rest

namespace Grid
variable (r:Grid)

/-- routes represent synchronous, hence restoring-program-frame execution.
(They need not be cursor-restoring.) -/
inductive Route (r:Grid) (x:Word) (F:Fare) : ℕ→ℕ→Site→ℕ→Site→Prop
   | edit {q i a j b f} : r.prog i=.edit f j → f.f x (q,a)=b →
          i≤r.slot → j≤r.slot → F.atm q a → F.atm q b → Route r x F q i a j b
   | toss {q i a j b q' a' p e} : r.prog i=.toss p e j →
          p.f x (q,a.1)=q' → e.f x ((q,a.1),a')=b →
          i≤r.slot → j≤r.slot → F.atm q a → F.atm q b → F.pull q a.1 q' →
          Route r x F q' r.entry (0,a.2) 0 a' →
          Route r x F q i a j b
   | fork {q i a j f s t} : r.prog i=.fork f s t → (if f.f x (q,a) then s else t)=j →
          i≤r.slot → j≤r.slot → F.atm q a → Route r x F q i a j a
   | seq {q i a j b l c} : Route r x F q i a j b → Route r x F q j b l c → Route r x F q i a l c
lemma Route.fits {r x F q i a j b} (h:Route r x F q i a j b) :
    i≤r.slot ∧ j≤r.slot ∧ F.atm q a ∧ F.atm q b:= by induction h <;> grind

end Grid

namespace Cog

def Body : Cog→Type
   | .edit _| .toss ..=> Unit
   | .seq p q=> Body p ⊕ Body q
   | .loop _ p=> Unit ⊕ Body p
   | .bif _ p q=> Unit ⊕ (Body p ⊕ Body q)
instance (p:Cog) : Finite (Body p):=by
   induction p <;>(dsimp only [Body];infer_instance)

def first : (p : Cog) → Body p
   | .edit _| .toss ..=>()
   | .seq p _=> .inl (first p)
   | .loop ..| .bif ..=>.inl ()

def code : (p : Cog) → (Body p → ℕ) → ℕ → Body p → Act
   | .edit p,_,t,_=> .edit p t
   | .toss p q,_,t,_=> .toss p q t
   | .seq p q,f,_,.inl u=>code p (fun i=>f (.inl i)) (f (.inr (first q))) u
   | .seq _ q,f,t,.inr u=>code q (fun i=>f (.inr i)) t u
   | .loop c p,f,t,.inl _=>.fork c (f (.inr (first p))) t
   | .loop _ p,f,_,.inr u=>code p (fun i=>f (.inr i)) (f (.inl ())) u
   | .bif c p q,f,_,.inl _=> .fork c (f (.inr (.inl (first p)))) (f (.inr (.inr (first q))))
   | .bif _ p _,f,t,.inr (.inl u)=>code p (fun i=> f (.inr (.inl i))) t u
   | .bif _ _ q,f,t,.inr (.inr u)=>code q (fun i=> f (.inr (.inr i))) t u

lemma lays {r:Grid} {x F main} (m : Body main→ℕ)
   (hl:∀ i,m i≤r.slot) (he : ∀ i,r.prog (m i)=code main m 0 i)
   (hs : m (first main)=r.entry)
   {q p a b} (h:Boots x F main q p a b) (v:Body p → ℕ) (t:ℕ)
   (hu:∀ i,v i≤r.slot) (ht:t≤r.slot) (hh:∀ i,r.prog (v i)=code p v t i) :
    r.Route x F q (v (first p)) a t b := by
   induction h generalizing t with
   | edit e ha hb=> exact .edit (hh _) e (hu _) ht ha hb
   | toss u y ha hb h j ih=>
     exact .toss (hh _) u y (hu _) ht ha hb h (by rw [← hs]; exact ih m _ hl (Nat.zero_le _) he)
   | @seq q p z a b c h1 h2 ih1 ih2=>
     exact .seq (ih1 (fun i=> v (Sum.inl i)) _ (fun i=>hu _) (hu (Sum.inr (first z)))
                        (fun i=>hh (Sum.inl i)))
                (ih2 (fun i=>v (Sum.inr i)) t (fun i=>hu _) ht (fun i=>hh (Sum.inr i)))
   | @yes q f p z a b e h ih=>
     have hh1:= ih (fun i=>v (Sum.inr (Sum.inl i))) t (fun i=>hu _) ht (fun i=>hh (.inr (.inl i)))
     exact .seq (.fork (hh _) (ite_eq_left e) (hu _) (hu _) h.fits.1) hh1
   | @no q f p z a b e h ih=>
     have hh1:= ih (fun i=>v (Sum.inr (Sum.inr i))) t (fun i=>hu _) ht (fun i=>hh (.inr (.inr i)))
     exact .seq (.fork (hh _) (ite_eq_right (by simp [e])) (hu _) (hu _) h.fits.1) hh1
   | @more q f p a b c e h g ih1 ih2=>
     have hh2:= ih1 (fun i=>v (Sum.inr i)) (v (Sum.inl ())) (fun i=>hu _) (hu _)
           (fun i=> hh (.inr i))
     exact .seq (.fork (hh _) (ite_eq_left e) (hu _) (hu _) h.fits.1) (.seq hh2 (ih2 v t hu ht hh))
   | lend e h=> exact .fork (hh _) (ite_eq_right (by simp [e])) (hu _) ht h

lemma room (p:Cog) :
    ∃ r:Grid, ∀ {x F q a b}, Boots x F p q p a b → r.Route x F q r.entry a 0 b := by
   classical
   let:=Fintype.ofFinite (Body p)
   let e:=Fintype.equivFin (Body p)
   let n:=Fintype.card (Body p)
   let m : Body p→ℕ :=fun i=> (e i).val+1
   let f : ℕ→ Act := fun i=> if h : i<n+1∧i≠0 then code p m 0 (e.symm ⟨i-1,by omega⟩)
                                                 else .rest
   have hl (i) : m i≤ n := (e i).isLt
   let r:Grid:=⟨n,m (first p),f,hl _,by simp [f],fun i hi=> by
                                      exact dite_eq_right (by omega)⟩
   have he(i) : f (m i)=code p m 0 i := by
       unfold f
       have hz : m i<n+1∧m i≠0 := ⟨by have:=hl i; omega,Nat.succ_ne_zero _⟩
       rw [dite_eq_left hz]
       congr 1; simp [m,e]
   exact ⟨r,fun {_ _ _ _ _} h=> lays (r:=r) m hl he rfl h m 0 hl (Nat.zero_le n) he⟩

end Cog
end ExactDerandomization.Relay

end

section

namespace ExactDerandomization.Relay
open Counter
namespace Grid
variable (r:Grid)

abbrev Motor := ℕ × ℕ × Site
abbrev Hood := ℕ×ℕ
abbrev Carrier := Hood × Motor

/-- which query was invoked from this instruction -/
def fame (x:Word) (a q:ℕ) : ℕ :=
   let p : ℕ×ℕ:= dec a
   match r.prog p.1 with
   | .toss h _ _=>h.f x (q,p.2)
   | _=>0

def replay : PT (Hood × ℕ) ℕ :=
    sweep (fun x j => r.fame x j.2.1 j.2.2)
      (fun x j=>windback x j.2)
      (fun _ j=>j.1.2) (fun _ j=>j.1.1)

/-- finite branch selection -/
lemma numerous {α β : Type} [Wire α] [Wire β] (f: Act→ PT α β)
   (h:∀ p,Kn (f p)) (n:PT α ℕ) (hn:Kn n) :
    Kn (fun x a=> f (r.prog (n x a)) x a) := by
  classical
  have he(k) :
     Kn (fun x a=> if n x a<k then f (r.prog (n x a)) x a else f .rest x a) := by
     induction k with
     | zero=> simpa using h .rest
     | succ k ih=>
       convert hn.cond_eq (Kn.fix k) (h (r.prog k)) ih using 1
       ext x a
       by_cases hn:n x a=k <;> simp [hn] ; grind
  convert he (r.slot+1) using 1
  ext x a
  split
  · rfl
  · rw [r.dome _ (by omega)]

lemma fameK {α} [Wire α] (h k: PT α ℕ) (hs:Kn h) (he:Kn k) :
     Kn (fun x a=> r.fame x (h x a) (k x a)) := by
   let p : PT α (ℕ×ℕ):= fun x a=>dec (h x a)
   have hp : Kn p := Kn.unpack.comp hs
   let f (v:Act) : PT α ℕ:=fun x a=> match v with
     | .toss q _ _=> q.f x (k x a,(p x a).2)
     | _=>0
   apply r.numerous f ?_ _ hp.left
   intro j; cases j <;> first| exact Kn.fix _ | next p1 _ _=> exact p1.runs.comp (he.tuple hp.right)
lemma replayK : Kn r.replay := Kn.sweepK _ _ _ _
      (r.fameK _ _ Kn.next.left Kn.next.right)
      (Kn.windbackK.comp Kn.next) Kn.first.right Kn.first.left

def advance (r:Grid) (op:Act) (x:Word) (a:Carrier) : Motor :=
   let q:=r.replay x (a.1,a.2.2.1)
   let m:=a.2
   match op with
   | .edit f i=> (i,m.2.1, f.f x (q,m.2.2))
   | .fork f i j=> (if f.f x (q,m.2.2) then i else j,m.2.1,m.2.2)
   | .toss ..=> (r.entry,cord (enc (m.1,m.2.2.1)) m.2.1,0,m.2.2.2)
   | .rest=>m

def recede (r:Grid) (op:Act) (x:Word) (a:Carrier) : Motor :=
   let m:=a.2; let s:=aft m.2.1; let q:=r.replay x (a.1,s)
   match op with
   | .toss _ e i=> (i,s, e.f x ((q,(dec (fore m.2.1):ℕ×ℕ).2),m.2.2))
   | _=>m

def roll (r:Grid) (x:Word) (a:Carrier) : Motor :=
   let m:=a.2
   if m.1=0 then
     if m.2.1≤1 then m else r.recede (r.prog (dec (fore m.2.1):ℕ×ℕ).1) x a
   else r.advance (r.prog m.1) x a

lemma rollK : Kn r.roll := by
   have h0 : Kn (fun (_:Word) (a: Carrier)=> a.1) := Kn.first
   have h1 : Kn (fun (_:Word) (a: Carrier)=> a.2) := Kn.next
   have h2 : Kn (fun (_:Word) (a: Carrier)=> a.2.2.1) := h1.right.left
   have he : Kn (fun (_:Word) (a: Carrier)=> (dec (fore a.2.2.1):ℕ×ℕ)) :=
            Kn.unpack.comp h2.top
   apply h1.left.cond_eq (Kn.fix _)
      (h2.cond_le (Kn.fix _) h1 (r.numerous r.recede _ _ he.left))
      (r.numerous r.advance _ _ h1.left)
   · intro p
     cases p
     · exact h1
     · exact h1
     · next _ p i => exact (Kn.fix i).tuple (h2.tail.tuple
                      (p.runs.comp (((r.replayK.comp (h0.tuple h2.tail)).tuple he.right).tuple
                                    h1.right.right)))
     · exact h1
   intro p
   have hx := (r.replayK.comp (h0.tuple h2)).tuple h1.right.right
   cases p
   · next p i=> exact (Kn.fix i).tuple (h2.tuple (p.runs.comp hx))
   · next p i j => exact ((p.runs.comp hx).cond (Kn.fix i) (Kn.fix j)).tuple
                             (h2.tuple h1.right.right)
   · exact (Kn.fix r.entry).tuple
        (((Kn.wash.comp (h1.left.tuple h1.right.right.left)).push h2).tuple
            ((Kn.fix 0).tuple h1.right.right.right))
   · exact h1

lemma Scan.snatch {lim f x l q p a} (h:Scan lim f x l q) (hz: f a q=p) (hh:p≤lim) :
    Scan lim f x (l++[a]) p := by
   induction h
   · rw [← hz]; exact .cons (by assumption) (.nil (by omega))
   · apply Scan.cons (by assumption); apply_rules

lemma replay_s {x U q0 s q} (h:Scan U (r.fame x) q0 s.reverse q) :
   r.replay x ((U,q0),mesh s)=q :=
   exact_sweep (l:=s.reverse) h (windback_mesh ..)

lemma parked (x h a) : r.roll x (h,(0,1,a))=(0,1,a):=by simp [roll]

end Grid
end ExactDerandomization.Relay

end

section

namespace ExactDerandomization.Relay

/-- bounded transitive closure -/
inductive WPath {α} (safe:α→Prop) (g:α→α) : α→α→Prop
   | start {x} (h:safe x) : WPath safe g x x
   | next {x y z} : safe x → g x=y → WPath safe g y z → WPath safe g x z
lemma WPath.seq {α} {p:α→Prop} {g x y z} (h : WPath p g x y) (e:WPath p g y z): WPath p g x z := by
   induction h with | start=> exact e | next h g e ih=> exact .next h g (ih (by assumption))

namespace Grid
variable (r:Grid)

def elbow := 10*(lb r.slot+1)
lemma elbow_hi : 1 ≤ r.elbow := by unfold elbow; omega
def rooms (U : ℕ) := caplen U ^ (10*r.elbow)
abbrev fitsM (U:ℕ) (m:Motor) := enc m ≤ r.rooms U

lemma seats {F : Fare} {U q0 q s i a} (h:lb (mesh s)+r.elbow*F.meter q≤1+r.elbow*F.meter q0)
    (ht:i≤r.slot) (hf:F.atm q a)
    (hp:2^(F.meter q0) ≤ U) (hs:F.limit ≤ U) :
    r.fitsM U (i,mesh s,a) := by
   have hu:=lb_mono hp; rw [lb_shift] at hu
   have he:= r.elbow_hi
   have hm: F.meter q≤F.meter q0 := by
       have hz:=mesh_pos s
       have hb:=lb_pos (mesh s)
       nlinarith
   have hey:=lb_mono ht
   obtain ⟨ha,hb,hc⟩:=hf
   have hec:=lb_mono (hb.trans hs)
   have hx:=measure_pair i (mesh s,a)
   have hz:=measure_pair (mesh s) a
   have hh:=measure_pair a.1 a.2
   have hh0:=lb_pos U; have hg:=lb_pos r.slot
   change measure a≤2*lb a.1+lb a.2+2 at hh
   change measure (i,mesh s,a) ≤ 2*lb i+measure (mesh s,a)+2 at hx
   change measure (mesh s,a) ≤ 2*lb (mesh s)+measure a+2 at hz
   have hk : measure (i,mesh s,a) ≤ lb U*(10*r.elbow) :=by
       unfold elbow at *
       nlinarith [Nat.mul_le_mul_right (lb U) (show 1 ≤ lb r.slot from hg),
           Nat.mul_le_mul_left (10*(lb r.slot+1)) hu]
   exact le_trans (below _).le ((Nat.pow_le_pow_right Nat.zero_lt_two hk).trans_eq (by
      unfold rooms caplen; rw [pow_mul]))

lemma extends_by {F : Fare} {q0 q s i a q'} (h:lb (mesh s)+r.elbow*F.meter q≤1+r.elbow*F.meter q0)
    (ht:i≤r.slot) (hf:F.pull q a q') :
    lb (mesh (enc (i,a)::s))+r.elbow*F.meter q'≤1+r.elbow*F.meter q0 := by
   have h2 : lb (enc (i,a)) ≤ 2*lb i+lb a+2:=measure_pair i a
   have h3:=lb_mono ht
   rw [measure_mesh]
   unfold Fare.pull at hf
   have hp:=Nat.mul_le_mul_left r.elbow hf
   have he:=lb_pos a; have ht1:=lb_pos r.slot
   unfold elbow at *
   nlinarith

theorem journey {F : Fare} {x q0 U}
    (hp:2^(F.meter q0) ≤ U) (hs:F.limit ≤ U)
    {q i a j b} (h:r.Route x F q i a j b) {s}
    (hh:Scan U (r.fame x) q0 s.reverse q)
    (hz:lb (mesh s)+r.elbow*F.meter q≤1+r.elbow*F.meter q0) :
    WPath (r.fitsM U) (fun a=> r.roll x ((U,q0),a))
      (i,mesh s,a) (j,mesh s,b) := by
   induction h generalizing s with
   | @edit q i a j b f e l hi hj ha hb=>
     refine .next (r.seats hz hi ha hp hs) ?_ (.start (r.seats hz hj hb hp hs))
     have hk : i≠0 := fun hv=>by subst i; rw [r.shut] at e; contradiction
     simp [roll,advance,hk,e,r.replay_s hh,l]
   | @fork q i a j f s' t e l hi hj ha=>
     refine .next (r.seats hz hi ha hp hs) ?_ (.start (r.seats hz hj ha hp hs))
     have hk : i≠0 := fun hv=>by subst i; rw [r.shut] at e; contradiction
     simp [roll,advance,hk,e,r.replay_s hh,l]
   | @toss q i a j b q' a' p e he hl hu hi hj ha hb hf hm ih=>
     let w:= enc (i,a.1)
     have h1 : lb (mesh (w::s))+r.elbow*F.meter q'≤1+r.elbow*F.meter q0 :=r.extends_by hz hi hf
     have h2 : Scan U (r.fame x) q0 (w::s).reverse q':=by
          rw [List.reverse_cons]
          exact Scan.snatch hh (by simp [w,fame,he,hl]) (hm.fits.2.2.1.1.trans hs)
     have h3:= ih h2 h1
     refine .next (r.seats hz hi ha hp hs) ?_
         (h3.seq (.next (r.seats h1 (Nat.zero_le _) hm.fits.2.2.2 hp hs)
                          ?_ (.start (r.seats hz hj hb hp hs))))
     · have hk : i≠0 := fun hv=>by subst i; rw [r.shut] at he; contradiction
       simp [roll,advance,mesh,hk,he,w]
     have he1 : ¬(cord w (mesh s) ≤ 1):= not_le_of_gt (cord_fine ..).2.2
     simp only [roll,ite_true,recede,mesh,he1,ite_false,fore_cord,aft_cord,w,dec_round,he,r.replay_s hh,hu]
   | seq _ _ ih ig => exact (ih hh hz).seq (ig hh hz)

end Grid
end ExactDerandomization.Relay

end

section

namespace ExactDerandomization.Relay
open Counter

abbrev hitloop (f : ℕ→ℕ) (x:ℕ) := forNat (fun _=>f) x

lemma conserve {f:ℕ→ℕ} {L z} (h:z≤L) : ∀ n, hitloop (fun i=>min L (f i)) z n≤L := by
   intro n; cases n
   · exact h
   · exact min_le_left ..
lemma forever {f:ℕ→ℕ} {y z : ℕ} (h:f z=z) {j n} (hz:hitloop f y j=z) (hh:j≤ n) :
    hitloop f y n=z := by induction n,hh using Nat.le_induction <;> simp_all [hitloop,forNat]

lemma quick {f:ℕ→ℕ} {L x y}
   (hh:x≤L) (h:∀ n,f n≤L) (he:f y=y) (hr:∃ j,hitloop f x j=y) :
   hitloop f x L=y := by
   let j:=Nat.find hr
   have hz: hitloop f x j=y:= Nat.find_spec hr
   apply forever he hz
   have hv : Function.Injective (fun i : Fin (j+1)=>hitloop f x i.val) := by
      have hz1 {u v : Fin (j+1)} (ht:u<v) : hitloop f x u.val≠hitloop f x v.val := by
        intro hs
        have he1 (n:ℕ) : hitloop f x (u.val+n)=hitloop f x (v.val+n) := by
           induction n with
           | zero=> simpa using hs
           | succ n ih=>
             unfold hitloop at *; rw [show u.val+(n+1)=u.val+n+1 by omega,
                  show v.val+(n+1)=v.val+n+1 by omega,forNat,forNat,ih]
        have hx:= he1 (j-v.val)
        rw [show v.val+(j-v.val)=j by have:=v.isLt; omega,hz] at hx
        have hg:j≤u.val+(j-v.val):= Nat.find_min' hr hx
        have ht1:=v.isLt; exact (by change u.val < v.val at ht; omega)
      intro i v h; rcases lt_trichotomy i v with ht|ht|ht
      · exact (hz1 ht h).elim
      · exact ht
      · exact (hz1 ht h.symm).elim
   have hu (n) : hitloop f x n≤L:= by cases n; exact hh; exact h _
   let w : Fin (j+1)→ Fin (L+1) := fun i=>⟨_,Nat.lt_succ_of_le (hu i.val)⟩
   have he := Fintype.card_le_of_injective w fun i v hz=> hv (congrArg Fin.val hz)
   simpa using he

variable {α} [Wire α]

lemma WPath.clipIter {a b:α} {f L} (h:WPath (fun i:α=> enc i≤L) f a b) :
   enc a≤L ∧ enc b≤L ∧ ∃ j,hitloop (fun i=> min L (enc (f (dec i)))) (enc a) j=enc b := by
   induction h with
   | start ha=> exact ⟨ha,ha,0,rfl⟩
   | @next a v b ha he h ih=>
     obtain ⟨hv,hb,j,hz⟩:=ih
     refine ⟨ha,hb,j+1,?_⟩
     unfold hitloop; rw [forNat_cons,Wire.eq,he,min_eq_right hv]; exact hz

namespace Grid
variable (r:Grid)
abbrev Job := Hood × Site
def run (r : Grid) : PT Job Site :=
   fun x a=>
   let L:=r.rooms a.1.1
   let z:Motor:= (r.entry,1,a.2)
   let n:= hitloop (fun i : ℕ=> min L (enc (r.roll x (a.1,(dec i))))) (min L (enc z)) L
   (dec n : Motor).2.2

lemma runK : Kn r.run := by
   let L : PT Job ℕ:=fun _ a=>r.rooms a.1.1
   have e : Kn L:= Kn.power (10*r.elbow) (Kn.caplenK.comp Kn.first.left)
   let z : PT Job Motor :=fun _ a=>(r.entry,1,a.2)
   have he: Kn z:= (Kn.fix _).tuple ((Kn.fix _).tuple Kn.next)
   let f : PT (Job×ℕ×ℕ) ℕ:= fun x a=> min (L x a.1) (enc (r.roll x (a.1.1,dec a.2.2)))
   have ht : Kn f:= (e.comp Kn.first).small
            (Kn.wash.comp (r.rollK.comp (Kn.first.left.tuple (Kn.unpack.comp Kn.next.right))))
   have hh:= Kn.stroll f L _ L ht e (e.small (Kn.wash.comp he)) e (by
      intro x a j _
      cases j <;> exact min_le_left _ _)
   exact ((Kn.unpack (α:=Motor)).comp hh).right.right

lemma actual {x q F a b U} (ht:r.Route x F q r.entry a 0 b)
   (hu : 2^(F.meter q) ≤ U) (hv:F.limit≤U) : r.run x ((U,q),a)=b := by
   have hh : Scan U (r.fame x) q ([]:List ℕ) q := .nil (ht.fits.2.2.1.1.trans hv)
   have h:= r.journey hu hv ht (s:=[]) hh (by change lb 1+_≤_; rw [lb_one])
   obtain ⟨e,f,g⟩:=h.clipIter
   change enc (0,(1:ℕ),b)≤_ at f
   have he0 : min (r.rooms U) (enc (r.roll x ((U,q),
        dec (enc (0,(1:ℕ),b))))) = enc (0,(1:ℕ),b) := by
      rw [dec_round,r.parked,min_eq_right f]
   have he := quick e (fun i=> min_le_left (r.rooms U) (enc (r.roll x ((U,q),dec i))))
            he0 g
   unfold run
   dsimp only
   rw [min_eq_right (show enc (r.entry,(1:ℕ),a) ≤ r.rooms U from e)]
   change ((dec (hitloop _ (enc (r.entry,mesh [],a)) (r.rooms U)):Motor).2.2)=b
   rw [he,dec_round]

end Grid

/-- Compilation of simultaneous stack certificates. Partial logspace
function extension on all certified executions. -/
theorem realization (main:Cog) : ∃ f : PT Grid.Job Site, Kn f ∧ ∀ {x U F q a b},
   2^(F.meter q) ≤ U → F.limit ≤ U → Boots x F main q main a b →
    f x ((U,q),a)=b := by
   obtain ⟨r,h⟩:=main.room
   exact ⟨r.run,r.runK,fun ht he hz=> r.actual (h hz) ht he⟩

lemma Boots.same {F : Fare} {G : Fare} {p x q a b c}
    (h:Boots x F p q p a b) (e:Boots x G p q p a c) : b=c := by
   obtain ⟨f,_,hf⟩:=realization p
   let u:=max (max (2^(F.meter q)) F.limit) (max (2^(G.meter q)) G.limit)
   have hp : f x ((u,q),a)=b:=hf (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_left _ _)) h
   have ht : f x ((u,q),a)=c:=hf (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _)) e
   exact hp.symm.trans ht
end ExactDerandomization.Relay

end

section

/-! A local recipe layer, with spans accounting for numerical clock difference.
The allowance gap pays for both immediate structural information and any
overshoot in requested precision. -/
namespace ExactDerandomization.Relay
open Counter

abbrev span (c d t j x : ℕ) := x+c*j ≤ c*t+c*c*d
abbrev charge (c w t : ℕ):=c*t+c*c*w
lemma movespan {c d t j h e : ℕ} (u:span c d t j h) (hh:d ≤ e) :
    span c e t j h:= u.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hh) _)

lemma leaner {c d t j x y : ℕ} (h:span c d t j y) (he:x≤y):span c d t j x :=
   le_trans (Nat.add_le_add_right he _) h

lemma acock {c d t j x} (h : span c d t j x) (he: 1≤ c) : j ≤ t+c*d:= by
   unfold span at h
   by_contra! hz; nlinarith

lemma lax {c d t j x} (h:span c d t j x) {D m : ℕ} (he:m*c ≤ D) (hp:1≤c) :
    m*x + D*j ≤ D*t+D*c*d := by
   obtain ⟨u,hD⟩:=Nat.exists_eq_add_of_le he
   have hz:=acock h hp
   unfold span at *
   have hu:=Nat.mul_le_mul_left u hz
   have hw:=Nat.mul_le_mul_left m h
   rw [hD]
   nlinarith

lemma span_mono {c d t j x} (h:span c d t j x) {D} (he:c ≤ D) (hp:1≤c):
    span D d t j x := by
   apply le_trans _ (Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.mul_le_mul_left D he)) (D*t))
   simpa only [one_mul] using lax h (m:=1) (by omega) hp

structure Level where
    w : ℕ
    t : ℕ

/-- fixed syntactic play, prices ignored until the enclosing layer is ready. -/
structure Lot where
    x : Word
    P : Cog
    F : Fare
    book : ℕ→Level

namespace Lot
variable (l:Lot)
def state (c : ℕ) (b : Level) (h:Site) :=
    h.2 ≤ l.F.limit ∧ span c b.w b.t 0 (lb h.1+1)
def jump (c : ℕ) (b : Level) (d h q:ℕ) :=
    let b':=l.book q
    b'.w+d ≤ b.w ∧ span c (b.w-b'.w) b.t b'.t (lb h+1)

/-- The clock argument is in b. q is the immutable tuple seen by the
inline recipe (may be virtual, i.e. regenerated via an inline frame). -/
inductive Mane (l:Lot) (c : ℕ) (b : Level) (d : ℕ) (q : ℕ) : Cog→Site→Site→Prop
   | edit {p h j} : p.f l.x (q,h)=j → l.state c b h → l.state c b j →
         Mane l c b d q (.edit p) h j
   | toss {p e a a' u q'} :
       p.f l.x (q,a.1)=q' → e.f l.x ((q,a.1),a')=u →
       l.state c b a → l.state c b u → l.jump c b d a.1 q' →
       Boots l.x l.F l.P q' l.P (0,a.2) a' →
       Mane l c b d q (.toss p e) a u
   | seq {p s a y u} : Mane l c b d q p a y → Mane l c b d q s y u →
       Mane l c b d q (.seq p s) a u
   | yes {s u p a y} : s.f l.x (q,a)=true → Mane l c b d q p a y →
       Mane l c b d q (.bif s p u) a y
   | no {s u p a y} : s.f l.x (q,a)=false → Mane l c b d q u a y →
       Mane l c b d q (.bif s p u) a y
   | more {s p a y v} : s.f l.x (q,a)=true → Mane l c b d q p a y →
       Mane l c b d q (.loop s p) y v → Mane l c b d q (.loop s p) a v
   | stop {s p a} : s.f l.x (q,a)=false → l.state c b a → Mane l c b d q (.loop s p) a a

lemma Mane.spots {l c b d q p a y} (h:Mane l c b d q p a y) : l.state c b a ∧ l.state c b y:=
   by induction h <;> grind

lemma Mane.mono {l c b d q p a y} (h:Mane l c b d q p a y) {D}
   (he:c ≤ D) (hp:1≤c) :
     Mane l D b d q p a y := by
   have hs {v:Site} (e:l.state c b v) : l.state D b v:=⟨e.1,span_mono e.2 he hp⟩
   have ht {v t} (e:l.jump c b d v t) : l.jump D b d v t:=⟨e.1,span_mono e.2 he hp⟩
   induction h
   · apply Mane.edit (by assumption) (hs ‹_›) (hs ‹_›)
   · rename_i q' e f _ _ _ g
     exact .toss e f (hs ‹_›) (hs ‹_›) (ht ‹_›) g
   · exact .seq (by assumption) (by assumption)
   · exact .yes (by assumption) (by assumption)
   · exact .no (by assumption) (by assumption)
   · exact .more (by assumption) (by assumption) (by assumption)
   · exact .stop (by assumption) (hs ‹_›)

theorem Mane.issue {l c b d q p a y} (h:Mane l c b d q p a y) (hb:b=l.book q) (hu:q≤l.F.limit)
   (ht : ∀ x, l.F.meter x=charge c (l.book x).w (l.book x).t) :
     Boots l.x l.F l.P q p a y:= by
   have hs {v:Site} (e:l.state c b v) : l.F.atm q v := by
     refine ⟨hu,e.1,?_⟩
     rw [ht q,← hb]
     obtain ⟨-,he⟩:= e; unfold span charge at *; omega
   have he {v t} (e:l.jump c b d v t) : l.F.pull q v t := by
      obtain ⟨hz,hu⟩:= e
      have hl: (b.w-(l.book t).w)+(l.book t).w=b.w:=by omega
      unfold Fare.pull; rw [ht t,ht q,← hb]; unfold span charge at *
      nlinarith [congrArg (fun w=> c*c*w) hl]
   induction h
   · exact .edit (by assumption) (hs ‹_›) (hs ‹_›)
   · rename_i q' e f _ _ _ g
     exact .toss e f (hs ‹_›) (hs ‹_›) (he ‹_›) g
   · exact .seq (by assumption) (by assumption)
   · exact .yes (by assumption) (by assumption)
   · exact .no (by assumption) (by assumption)
   · exact .more (by assumption) (by assumption) (by assumption)
   · exact .lend (by assumption) (hs ‹_›)

end Lot

def hold (o:ℕ) (a:Site) : Site := (enc (o,a.1),a.2)
def mark (a:ℕ) := (dec a:ℕ×ℕ).1
def unseat (a:ℕ) := (dec a:ℕ×ℕ).2

lemma marked (o h) : mark (enc (o,(h:ℕ)))=o := by simp [mark]
lemma unseats0 (o h) : unseat (enc ((o:ℕ),h))=(h:ℕ) :=by simp [unseat]
lemma holdcap {c C g o} {a : ℕ} {d t j k : ℕ}
   (h:span C d j k (lb a+1)) (e:span c d t j (lb o+1))
   (hh:2*c+C≤g) (hc:1≤ c) (hx:1≤ C) :
     span g d t k (lb (enc (o,a))+1) := by
   have h1:=lax h (m:=1) (show 1*C≤g by omega) hx
   have h2:=lax e (m:=2) (show 2*c≤g by omega) hc
   have he : lb (enc (o,a)) ≤2*lb o+lb a+2:=measure_pair o a
   have hl:= Nat.mul_le_mul_left (g*d) (show C+c≤g by omega)
   unfold span
   nlinarith

namespace Cog
variable (f:Cub Slip ℕ)
def locate (a:Cub Slip ℕ) : PT Plot Plot :=
   fun x p=> (a.f x (p.1,mark p.2.1),unseat p.2.1,p.2.2)
lemma location : Kn (locate f):= by
   let p (_:Word) (a:Plot):= (dec a.2.1:ℕ×ℕ)
   have ht:Kn p:= Kn.unpack.comp Kn.next.left
   exact (f.runs.comp (Kn.first.tuple ht.left)).tuple (ht.right.tuple Kn.next.right)

lemma binds {α} [Wire α] (o:PT α ℕ) (a:PT α Site) (h:Kn o) (e:Kn a) :
   Kn (fun x v=> hold (o x v) (a x v)):= (Kn.wash.comp (h.tuple e.left)).tuple e.right

theorem markK {α} [Wire α] {a:PT α ℕ} (e:Kn a) :
    Kn (fun x v=> mark (a x v)):= Kn.left ((Kn.unpack (α:=ℕ×ℕ)).comp e)
theorem unseatK {α} [Wire α] {a:PT α ℕ} (e:Kn a) :
    Kn (fun x v=> unseat (a x v)):= Kn.right ((Kn.unpack (α:=ℕ×ℕ)).comp e)

def guard0 (p:Flag) : Flag := ⟨fun x a=>p.f x (locate f x a),p.runs.comp (location f)⟩

/-- Inlining carries an inner tuple regenerated from q and the piece o. -/
def focus (v:Cog) : Cog :=
   match v with
   | .edit p=> .edit ⟨fun x a=> hold (mark a.2.1) (p.f x (locate f x a)),
                       binds _ _ (markK Kn.next.left) (p.runs.comp (location f))⟩
   | .toss p g=> .toss ⟨fun x a=> p.f x (f.f x (a.1,mark a.2),unseat a.2),
                       p.runs.comp ((f.runs.comp (Kn.first.tuple (markK Kn.next))).tuple (unseatK Kn.next))⟩
                       ⟨fun x a=>let o:=mark a.1.2
                                 hold o (g.f x ((f.f x (a.1.1,o),unseat a.1.2),a.2)),
                        binds _ _ (markK Kn.first.right) (g.runs.comp
                            (((f.runs.comp (Kn.first.left.tuple (markK Kn.first.right))).tuple
                              (unseatK Kn.first.right)).tuple Kn.next))⟩
   | .seq q w=>.seq (focus q) (focus w)
   | .bif p q w=>.bif (guard0 f p) (focus q) (focus w)
   | .loop p q=>.loop (guard0 f p) (focus q)

lemma hitmark {x q o r} (h:f.f x (q,o)=r) (a:Site) :
     locate f x (q,hold o a)=(r,a):=by simp [locate,hold,marked,unseats0,h]

lemma focus_word {l c w j d r p a y} (h:Lot.Mane l c ⟨w,j⟩ d r p a y)
    {C g o t q} (he:f.f l.x (q,o)=r)
    (hr:span C d t j (lb o+1))
    (hf:d≤w) (hz:2*C+c≤g) (hc:1≤ c) (hu:1≤ C) :
    Lot.Mane l g ⟨w,t⟩ d q (focus f p) (hold o a) (hold o y):= by
   have ha {a : Site} (h:l.state c ⟨w,j⟩ a) : l.state g ⟨w,t⟩ (hold o a):=
      ⟨h.1, holdcap h.2 (movespan hr hf) hz hu hc⟩
   have hs {a q} (h:l.jump c ⟨w,j⟩ d a q) : l.jump g ⟨w,t⟩ d (enc (o,a)) q := by
      refine ⟨h.1,holdcap h.2 (movespan hr ?_) hz hu hc⟩
      have hp :(l.book q).w+d ≤ w:=h.1; dsimp only; omega
   induction h
   · rename_i e ha1 ha2
     apply Lot.Mane.edit _ (ha ha1) (ha ha2)
     simp [locate,hold,e,marked,unseats0,he]
   · rename_i q' e y1 ha1 ha2 h3 h4
     refine Lot.Mane.toss ?_ ?_ (ha ha1) (ha ha2) (hs h3) h4
     all_goals simp only [hold,marked,unseats0,he,e,y1]
   · exact .seq (by assumption) (by assumption)
   · rename_i e h ih
     refine .yes ?_ ih; simp only [guard0,hitmark f he,e]
   · rename_i e h ih
     refine .no ?_ ih; simp only [guard0,hitmark f he,e]
   · rename_i e h h' ih ih'
     refine .more ?_ ih ih'; simp only [guard0,hitmark f he,e]
   · rename_i e h; refine .stop ?_ (ha h); simp only [guard0,hitmark f he,e]

end Cog
end ExactDerandomization.Relay

end

section

namespace ExactDerandomization.Relay

variable {α β : Type} [Wire α] [Wire β]
abbrev Lore (α) := ℕ×α
abbrev Pause (v : α) (c:ℕ) : Site := (enc v,c)

def topNote (f:PT (Lore α) β) (h:Kn f) : Cub Plot Site :=
   ⟨fun x a=> (enc (f x (a.1, dec a.2.1)),a.2.2),
     (Kn.wash.comp (h.comp (Kn.first.tuple (Kn.unpack.comp Kn.next.left)))).tuple Kn.next.right⟩
def etch (f:PT (Lore α) β) (h:Kn f) : Cog := .edit (topNote f h)
def gear (f:PT (Lore α) Bool) (h:Kn f) : Flag :=
   ⟨fun x a=> f x (a.1, dec a.2.1),h.comp (Kn.first.tuple (Kn.unpack.comp Kn.next.left))⟩

lemma gear_at (f:PT (Lore α) Bool) (h:Kn f) (x q a c) :
   (gear f h).f x (q,Pause a c)=f x (q,a) := by simp [gear,Pause]
lemma etches (f:PT (Lore α) β) (h:Kn f) {l : Lot} {c b d q i j w}
    (hz:f l.x (q,i)=j) (hv:l.state c b (Pause i w)) (hy:l.state c b (Pause j w)) :
    Lot.Mane l c b d q (etch f h) (Pause i w) (Pause j w):=
   .edit (by simp [topNote,Pause,hz]) hv hy

lemma Kn.bneg (f:PT α Bool) (h: Kn f) : Kn (fun x a=> !(f x a)) := by
   convert h.cond (Kn.fix false) (Kn.fix true) using 1
   ext x a
   cases he:f x a <;> simp []

end ExactDerandomization.Relay

end

end OAI
