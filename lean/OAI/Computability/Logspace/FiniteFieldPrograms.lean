import OAI.Computability.Logspace.AffineSampling
import OAI.Computability.Logspace.ConfigurationGraph
import OAI.Computability.Logspace.DyadicArithmetic
import OAI.Computability.Logspace.ProbabilityDecision
import OAI.Computability.Logspace.RecursivePrograms
import Mathlib.NumberTheory.Bertrand

namespace OAI

/-!
Uniform prime-field enumeration and finite arithmetic for deterministic probability decisions.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Grain
open Relay Counter Finset
namespace Prime

def tube {α} (f:PT (α×ℕ) Bool) (x:Word)(a:α)(n:ℕ):ℕ :=
    forNat (fun j v=>if f x (a,j) then j+1 else v) 0 n
lemma tube_hi {α}(f:PT (α×ℕ) Bool) (x a n):tube f x a n≤n:=by
   induction n <;> simp only [tube,forNat] at *
   · exact le_rfl
   split <;> omega

lemma unique_small {α} {f:PT (α×ℕ) Bool} {x a n} :
    tube f x a n=0 ↔ ∀ j < n, f x (a,j)=false :=by
   induction n with
   | zero=> simp [tube,forNat]
   | succ n ih=>
     have he : (∀ j<n+1,f x (a,j)=false) ↔ f x (a,n)=false ∧ (∀ j<n,f x (a,j)=false) :=by
        constructor
        · exact fun h=>⟨h n (by omega),fun i he=> h i (by omega)⟩
        intro h i hi
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with he|he
        · simpa [he] using h.1
        · exact h.2 i he
     rw [he]; change (if f x (a,n) then n+1 else _)=0 ↔ _
     cases h:f x (a,n) <;> simp [← ih,tube]
lemma uniquely {α} {f:PT (α×ℕ) Bool} {x a n i}
    (h:tube f x a n=i+1) : i < n ∧ f x (a,i)=true:=by
   induction n with
   | zero=> simp [tube,forNat] at h
   | succ n ih=>
     change (if f x (a,n) then n+1 else tube f x a n)=i+1 at h
     split at h
     · have he:i=n:=by omega
       subst i; exact ⟨by omega,by assumption⟩
     obtain ⟨ht,hh⟩:=ih h; exact ⟨by omega,hh⟩

lemma tubeK {α} [Wire α] {f:PT (α×ℕ) Bool}{n:PT α ℕ}(h:Kn f)(he:Kn n):
     Kn (fun x a=>tube f x a (n x a)):=
   Kn.stroll (fun x (b:α×ℕ×ℕ)=>if f x (b.1,b.2.1) then b.2.1+1 else b.2.2)
       n (fun _ _=>0) n ((h.comp (Kn.first.tuple Kn.next.left)).cond Kn.next.left.succ Kn.next.right)
         he (Kn.fix 0) he (fun _ _ _ hv=> le_trans (tube_hi ..) hv)

def test (_:Word)(a:ℕ×ℕ):Bool :=
    if a.2 < 2 then false else decide (a.1%a.2=0)

def primex (x:Word)(k:ℕ):Bool :=
    if k<2 then false else decide (tube test x k k=0)

lemma divK : Kn test:= Kn.next.cond_lt (Kn.fix _) (Kn.fix _) ((Kn.first.mod Kn.next).eq (Kn.fix _))
lemma pxK : Kn primex:= Kn.identity.cond_lt (Kn.fix _) (Kn.fix _)
            ((tubeK divK Kn.identity).eq (Kn.fix _))

lemma px_eq (x n): primex x n=true↔n.Prime:=by
   unfold primex
   by_cases ht:n<2
   · simp only [ht,ite_true,Bool.false_eq_true,false_iff]
     intro h; have he:=h.two_le; omega
   rw [ite_eq_right ht,decide_eq_true_eq,unique_small]
   constructor
   · intro h
     rw [Nat.prime_def_lt]
     refine ⟨by omega,?_⟩
     intro m hm he
     have hs:= h _ hm
     have h0 : m≠0:= by rintro rfl; simp at he; omega
     by_cases hb:m<2
     · omega
     simp [test,hb,Nat.mod_eq_zero_of_dvd he] at hs
   intro h m hm
   unfold test; split
   · rfl
   next hh=>
      by_contra! hv
      have hz:m∣n:= Nat.dvd_of_mod_eq_zero (by simpa using hv)
      have he:= (Nat.dvd_prime h).1 hz; omega

def atp (x:Word) (a:ℕ×ℕ):Bool :=
    if a.1 < a.2 then primex x a.2 else false
def last (x:Word) (n:ℕ) := tube atp x n (2*n+1)-1
lemma last_prime (x n)(h:0<n) : (last x n).Prime ∧ n < last x n ∧ last x n≤ 2*n:= by
    obtain ⟨p,hp,ht,hk⟩:= Nat.bertrand n (by omega)
    have hl: atp x (n,p)=true:=by rw [atp]; simp [ht,(px_eq ..).2 hp]
    unfold last
    cases hh:tube atp x n (2*n+1) with
    | zero=> have he:=unique_small.1 hh p (by omega); simp_all
    | succ i=>
      have he:=uniquely hh
      simp only [Nat.add_sub_cancel]
      unfold atp at *; split at he
      · exact ⟨(px_eq ..).1 he.2,by assumption,by omega⟩
      · grind

lemma lastK : Kn last:=(tubeK (Kn.first.cond_lt Kn.next (pxK.comp Kn.next) (Kn.fix _))
                     (((Kn.fix 2).times Kn.identity).succ)).pred
end Prime
end ExactDerandomization.Grain

end

section

namespace ExactDerandomization.Grain
open Relay Counter Stage Hie
variable {q w h:ℕ}
structure Rock (q w h:ℕ) where
   P:Base.Source q w h
   w:Wares
   pad:ℕ

namespace Rock
variable (p:Rock q w h)
def B (x:Word):ℕ:= p.pad+lb (p.P.size x)+ lb (x.length+2)
def lamp (x:Word):ℕ:=2^(p.w.ceiling (p.B x))+p.w.p.M
def n (x:Word):ℕ:=Prime.last x (p.lamp x)
instance primed (x:Word) : Fact (p.n x).Prime:=⟨(Prime.last_prime x (p.lamp x)
        (by unfold lamp; positivity)).1⟩
lemma nf (x:Word): p.w.p.M<p.n x ∧ 2^(p.w.ceiling (p.B x))≤ p.n x:=by
    have he:p.lamp x < p.n x:=(Prime.last_prime x (p.lamp x) (by unfold lamp; positivity)).2.1
    unfold lamp at he; constructor <;> first|exact le_trans (Nat.le_add_left _ _) he|exact (Nat.le_add_right _ _).trans he.le
noncomputable def matter0 (x:Word):Matter q w h (p.n x):=⟨p.P,p.w,x,p.B x⟩
lemma prompts (e:p.w.Proof) (h:6≤p.pad) (ht:e.T.bank ≤ Est.box p.pad) (x:Word) :
      (p.matter0 x).ready e := by
    have hp:p.pad≤p.B x:=by unfold B; omega
    exact ⟨h.trans hp, (below (p.P.size x)).le.trans (Nat.pow_le_pow_right Nat.zero_lt_two (by change lb (p.P.size x) ≤ p.B x; unfold B; omega)),
           ht.trans (Est.box_mono hp), (p.nf x).1,(p.nf x).2⟩

lemma sizeE :E (fun x _=>p.B x):= ((E.const p.pad).add (lbE p.P.eSize)).add
                  (lbE (E.length.add (E.const 2)))
lemma codeE : E (fun x _=>2^p.B x):= by
    have hh:= ((E.const (2^p.pad)).mul (digitsE p.P.eSize)).mul
                       (digitsE (E.length.add (E.const 2)))
    simpa only [B,pow_add] using hh

section
variable {α} [Wire α]
lemma BKn:Kn (fun x (_:α)=>p.B x):=Kn.word _ p.sizeE
lemma codeKn:Kn (fun x (_:α)=> (2:ℕ)^p.B x):=Kn.word _ p.codeE

abbrev linE (a b:ℕ) (x:Word) := a + b*p.B x
lemma exprKn (i j):Kn (fun x (_:α)=>(2:ℕ)^p.linE i j x):=by
    simpa only [linE, mul_comm j, pow_add,pow_mul] using
                  (Kn.fix (α:=α) (2^i)).times (Kn.power j p.codeKn)
lemma affine :∃ a b,∀ x,p.w.ceiling (p.B x)=p.linE a b x:=by
   let m:=p.w.p.M
   let g:=p.w.A0
   use 8*g+1,8*(4+g*(Net.lag p.w.p)+(1+m)+2)+1+(1+m)
   intro x; unfold Wares.ceiling Wares.top Wares.tolls Wares.density linE Net.coreR m g; ring
lemma lampK:Kn (fun x (_:α)=>p.lamp x):=by
   obtain ⟨a,b,h⟩:=p.affine
   unfold lamp; simp only [h]
   exact (p.exprKn a b).add (Kn.fix _)
lemma nKn :Kn (fun x (_:α)=> p.n x):= Prime.lastK.comp p.lampK

end
end Rock
end ExactDerandomization.Grain

end

section

namespace ExactDerandomization.Grain
open Relay Counter Rill Analysis Square Affine Env Wrap Finset

abbrev Page := Four ℕ
abbrev Stamp:= Page×Page
abbrev Issue:=Stamp×Stamp×Stamp
variable {n:ℕ} [Fact n.Prime]

namespace Print
set_option synthInstance.maxSize 4096
noncomputable section

def ncard (x:V n):Page := vmap (fun i=> i.val) x
def den (n:ℕ)(x:Page) : V n := vmap (fun (i:ℕ)=> (i: ZMod n)) x
def badge (s:Channel n):Stamp :=(ncard s.1.val,ncard s.2)
def issued (s:Env n 0):Issue:=(badge s.1,badge s.2.1,badge s.2.2.1)
lemma nr (x:V n):den n (ncard x)=x:= by simp [den,ncard,vmap]
lemma xi : Function.Injective (@badge n) := by
   intro a b h
   have he1 : a.1.val=b.1.val:=by rw [← nr a.1.val,← nr b.1.val, show ncard a.1.val=ncard b.1.val from
                                                           congrArg Prod.fst h]
   exact Prod.ext (Subtype.ext he1) (by rw [← nr a.2,← nr b.2,show ncard a.2=ncard b.2 from congrArg Prod.snd h])
instance : Subsingleton (Salt 0):=inferInstanceAs (Subsingleton (V 1))
lemma xu : Function.Injective (@issued n) := by
   rintro ⟨v,w,t,r⟩ ⟨v',w',t',r'⟩ h
   unfold issued at h; simp only [Prod.mk.injEq] at h ⊢
   exact ⟨xi h.1,xi h.2.1,xi h.2.2,Subsingleton.elim ..⟩

def barr (a ℓ:ℕ×ℕ):Prop:=a.1<ℓ.1∧a.2<ℓ.2
def brief (a:Page)(n:ℕ):Prop:=barr a.1 (n,n) ∧ barr a.2 (n,n)
def on (a:Stamp)(n:ℕ):Prop:= brief a.1 n ∧ a.1≠0 ∧ brief a.2 n
def revealed (a:Issue)(n:ℕ):Prop:=on a.1 n ∧ on a.2.1 n ∧ on a.2.2 n
instance (a:Page)(n):Decidable (brief a n):=by unfold brief barr;infer_instance
instance (a:Stamp)(n):Decidable (on a n):=by unfold on;infer_instance
instance (a:Issue)(n):Decidable (revealed a n):=by unfold revealed;infer_instance
lemma nsmall (x:V n): brief (ncard x) n := by simp [ncard,vmap,brief,barr,ZMod.val_lt]
omit [Fact (Nat.Prime n)] in
lemma rn (x:Page)(h:brief x n): ncard (den n x)=x:= by
   obtain ⟨⟨ht,hf⟩,hq,hz⟩:=h
   simp [ncard,den,vmap,ZMod.val_natCast,Nat.mod_eq_of_lt,ht,hf,hq,hz]
lemma valid (s:Channel n):on (badge s) n:= by
   refine ⟨nsmall _,?_,nsmall _⟩
   change ncard s.1.val≠_
   intro he
   apply s.1.prop
   rw [← nr s.1.val,he]; simp [den,vmap,Prod.ext_iff]
lemma built (x:Stamp)(h:on x n):∃ s:Channel n,badge s=x:=by
   obtain ⟨ha,hb,hk⟩:=h
   have hp : den n x.1 ≠0:= by
      intro he; apply hb; rw [← rn x.1 ha,he]; simp [ncard,vmap,Prod.ext_iff]
   exact ⟨(⟨den n x.1,hp⟩,den n x.2),by simp [badge,rn x.1 ha,rn x.2 hk]⟩
lemma constit (s:Env n 0):revealed (issued s) n :=⟨valid _,valid _,valid _⟩
lemma fill (x:Issue)(h:revealed x n): ∃ s:Env n 0,issued s=x:=by
   rcases x with ⟨a,b,c⟩
   obtain ⟨u,rfl⟩:= built a h.1
   obtain ⟨v,rfl⟩:= built b h.2.1
   obtain ⟨w,rfl⟩:= built c h.2.2
   exact ⟨(u,v,w,(0:Salt 0)),rfl⟩

def wallP (n:ℕ):Page:=((n,n),(n,n))
def ink (n:ℕ):Stamp:=(wallP n,wallP n)
def pages (n:ℕ):ℕ:=enc ((ink n,ink n,ink n):Issue)+1
lemma boxbound (s:Env n 0):enc (issued s)< pages n:=by
   have he(q:V n):enc (ncard q)≤enc (wallP n):= by
      obtain ⟨⟨ha,hb⟩,hc,hd⟩:=nsmall q
      exact bead_mono (pair_mono ha.le hb.le) (pair_mono hc.le hd.le)
   have hp(x:Channel n): enc (badge x) ≤ enc (ink n):= bead_mono (he _) (he _)
   exact Nat.lt_succ_of_le (bead_mono (hp _) (bead_mono (hp _) (hp _)))

def publish (n v:ℕ) : Bool:= decide (revealed (dec v:Issue) n ∧ enc (dec v:Issue)=v)
def spine (n:ℕ) : Finset ℕ:= (range (pages n)).filter (fun i=> publish n i)
lemma entry (s:Env n 0) : enc (issued s)∈spine n:= by
    rw [spine,mem_filter]; exact ⟨mem_range.2 (boxbound _),
                                   by simp [publish,constit]⟩
lemma owner {x}(h:x∈spine n): ∃ s:Env n 0, enc (issued s)=x:=by
   obtain ⟨ht,he⟩:=mem_filter.1 h
   obtain ⟨hi,hf⟩:= of_decide_eq_true he
   obtain ⟨s,h⟩:= fill (dec x) hi
   exact ⟨s,by rw [h,hf]⟩
lemma columns {n:ℕ} [Fact n.Prime] (f:ℕ→ℝ):
   ∑ i∈spine n,f i=∑ s:Env n 0, f (enc (issued s)):=by
   classical
   symm
   refine sum_nbij (fun s:Env n 0=>enc (issued s)) (fun x _=>entry x) (fun s _ t _ h=>?_)
               (fun x hx=>by obtain ⟨s,h⟩:=owner hx; exact ⟨s,mem_univ _,h⟩) fun _ _=>rfl
   exact xu (by simpa using congrArg (fun a=> (dec a:Issue)) h)

end
variable {α} [Wire α]
open Kn
lemma both {f g:PT α Bool}(h:Kn f)(k:Kn g):Kn (fun x a=> f x a&&g x a):=by
   convert h.cond k (Kn.fix false) using 1
   ext x a; cases hx:f x a <;> simp []
lemma bytesK {f:PT α Page}{g:PT α ℕ}(h:Kn f)(k:Kn g):
    Kn (fun x a=> decide (brief (f x a) (g x a))):=by
   convert both (both (h.left.left.lt k) (h.left.right.lt k)) (both (h.right.left.lt k) (h.right.right.lt k))
       using 1
   ext x a
   rw [Bool.eq_iff_iff]
   simp only [decide_eq_true_eq, Bool.and_eq_true]
   rfl
lemma onK {f:PT α Stamp}{g:PT α ℕ}(h:Kn f)(k:Kn g):
    Kn (fun x a=>decide (on (f x a) (g x a))):=by
   let t:=h.left
   have he:Kn (fun x a=> decide ((f x a).1≠0)):=by
      convert bneg _ ((Kn.wash.comp h.left).eq (Kn.fix (enc (0:Page)))) using 1
      ext x a; rw [Bool.eq_iff_iff]; simp; exact ⟨fun e h=>e (by
                              simpa using congrArg (fun n=>(dec n:Page)) h), fun e h=>e (by rw [h])⟩
   convert both (bytesK h.left k) (both he (bytesK h.right k)) using 1
   ext x a
   rw [Bool.eq_iff_iff]
   simp only [decide_eq_true_eq, Bool.and_eq_true]
   rfl
lemma pagesK {f:PT α ℕ}(h:Kn f):
    Kn (fun x a=>pages (f x a)):= by
   have ha:=h.tuple h; have hb:=ha.tuple ha; have ht:=hb.tuple hb
   exact (Kn.wash.comp (ht.tuple (ht.tuple ht))).succ
lemma pubK {f g:PT α ℕ}(h:Kn f)(k:Kn g):
    Kn (fun x a=>publish (f x a) (g x a)):=by
   have he:=(Kn.unpack (α:=Issue)).comp k
   have hz:=both (onK he.left h) (both (onK he.right.left h) (onK he.right.right h))
   convert both hz ((Kn.wash.comp he).eq k) using 1
   ext x a
   rw [Bool.eq_iff_iff]
   simp only [publish, decide_eq_true_eq, Bool.and_eq_true]
   rfl

end Print
end ExactDerandomization.Grain

end

section

namespace ExactDerandomization.Grain
open Relay Counter Rill Analysis Square Affine Env Wrap Finset
namespace Print
noncomputable section

def ms (n i x y:ℕ) := (x+i*y)%n
def zi (n i:ℕ ) (x y:ℕ×ℕ) := (ms n i x.1 y.1,ms n i x.2 y.2)
def mix (n i:ℕ ) (a b:Page):Page:=(zi n i a.1 b.1,zi n i a.2 b.2)

variable {n:ℕ} [Fact n.Prime]
lemma valms (i:ℕ ) (x y:ZMod n): (x+(i:ZMod n)*y).val=ms n i x.val y.val:=by
    have he:(x+(i:ZMod n)*y)= ↑(x.val+i*y.val):=by simp
    rw [he,ZMod.val_natCast]; rfl
lemma nadd (i:ℕ ) (x y:V n): ncard (x+(i:ZMod n)•y)=mix n i (ncard x) (ncard y) :=
    Prod.ext (Prod.ext (valms ..) (valms ..)) (Prod.ext (valms ..) (valms ..))

def shoot (n k x:ℕ ) (p:Stamp):Bool:=decide (brief (mix n x p.2 p.1 ) (side n k))
lemma shoots (a:Channel n) (k i):
    shoot n k i (badge a)=true ↔ hit k (i:ZMod n) a := by
   unfold shoot badge hit vEval; dsimp only; rw [← nadd,decide_eq_true_eq]; simp [ncard,brief,barr,vmap,restr,each,and_assoc]

def stretch (n s t:ℕ) (p:Stamp):Stamp:=(mix n s 0 p.1,mix n t p.2 p.1)
lemma stretchy (a:Channel n ) (s t:ℕ) (h:(s:ZMod n)≠0) :
   stretch n s t (badge a)=badge (affineChannel (↑s:ZMod n) ↑t h a) := by
   let w:= a.1.val
   unfold stretch badge
   change (_,_)= (ncard ((s:ZMod n)•w), ncard (a.2+(t:ZMod n)•w))
   have he: ncard (0:V n)=0:=by simp [ncard,vmap,Prod.ext_iff]
   apply Prod.ext _ (nadd t a.2 w).symm
   rw [← zero_add ((s:ZMod n) • w)]
   rw [nadd,he]

end
variable {α} [Wire α]
variable {x y k p:PT α ℕ}
lemma asideK (h:Kn x ) (e:Kn k):Kn (fun w a=>side (x w a ) (k w a)):= by
    convert (((h.pred.div (Kn.cap h.succ (Kn.fix 2) e)).succ)) using 1
    ext w a; unfold side
    by_cases he :2^(k w a) ≤ x w a+1
    · rw [min_eq_right he]
    rw [min_eq_left (by omega),Nat.div_eq_of_lt (by omega),Nat.div_eq_of_lt (by omega)]

lemma msK (hr:Kn p) (ht:Kn k ) (h:Kn x ) (e:Kn y):Kn (fun w a=>ms (p w a) (k w a) (x w a) (y w a)):=
    (h.add (ht.times e)).mod hr
lemma ziK (hr:Kn p ) (ht:Kn k){u v:PT α (ℕ×ℕ)}(h:Kn u ) (e:Kn v):
    Kn (fun w a=>zi (p w a ) (k w a ) (u w a ) (v w a)):=
    (msK hr ht h.left e.left).tuple (msK hr ht h.right e.right)
lemma mixK (hr:Kn p ) (ht:Kn k){u v:PT α Page}(h:Kn u ) (e:Kn v):
    Kn (fun w a=>mix (p w a ) (k w a ) (u w a ) (v w a)):=
       (ziK hr ht h.left e.left).tuple (ziK hr ht h.right e.right)
lemma shootK(hr:Kn p ) (ht:Kn k ) (h:Kn x){f:PT α Stamp}(e:Kn f):
    Kn (fun w a=>shoot (p w a ) (k w a ) (x w a ) (f w a)):=bytesK (mixK hr h e.right e.left) (asideK hr ht)
lemma stretchK (hr:Kn p ) (ht:Kn k ) (h:Kn x){f:PT α Stamp}(e:Kn f):
    Kn (fun w a=> stretch (p w a ) (k w a ) (x w a ) (f w a)) :=
       (mixK hr ht (Kn.fix _) e.left).tuple (mixK hr h e.right e.left)
end Print
end ExactDerandomization.Grain

end

section

set_option synthInstance.maxSize 4096

namespace ExactDerandomization.Grain
open Relay Counter Stage Est Analysis Hie Finset
namespace Rock
variable {q w h:ℕ}(p:Rock q w h)
noncomputable section

def camp (x:Word):ℕ:= p.w.p.M^p.B x*p.P.first x
lemma camps (x) : p.camp x=(p.matter0 x).i:=by
   let z:=p.matter0 x
   have he (n): z.s.H.child z.x0 n=p.w.p.M^n*p.P.first x:=by
       induction n with
       | zero=> change p.P.first x=_; simp
       | succ n ih=> rw [Prize.child,ih]
                     unfold radix; change _+p.w.p.M*_=_
                     ring
   exact (he _).symm
lemma campK {α} [Wire α]:Kn (fun x (_:α)=>p.camp x):=by
   let k:=p.w.p.M
   have hf:Kn (fun x (_:α)=>(k)^p.B x):=by
      convert (Kn.cap (p.exprKn 0 k) (Kn.fix k) p.BKn) using 1
      ext x a; symm; apply min_eq_right
      rw [linE,Nat.zero_add,pow_mul]
      have hh:= growing k
      gcongr; omega
   exact hf.times (Kn.word _ p.P.eFirst)

def qualify (x:Word) (a:ℕ) : Bool :=
     Print.publish (p.n x) a && Print.shoot (p.n x) (p.B x) (p.camp x) (dec a:Issue).1

abbrev printid (x:Word)(s:Pool (p.n x)) := enc (Print.issued s)
lemma verified (x:Word) (s:Pool (p.n x)):
    p.qualify x (p.printid x s)= true ↔ (p.matter0 x).polls s:=by
    have he:= (Print.entry s)
    have hk:= (mem_filter.1 he).2
    change Print.publish (p.n x) (p.printid x s)=true at hk
    rw [qualify, Bool.and_eq_true,hk]
    simp only [true_and]
    unfold printid; rw [Wire.eq]
    change _=true ↔ hit (p.B x) (↑(p.matter0 x).i:ZMod (p.n x)) s.1
    rw [← camps]
    exact Print.shoots ..
lemma qualifyK:Kn p.qualify:=
    Print.both (Print.pubK p.nKn Kn.identity) (Print.shootK p.nKn p.BKn p.campK (Kn.unpack (α:=Issue)).left)

lemma numbers (x) (f:ℕ→ℕ):
   (↑(∑ i∈range (Print.pages (p.n x)),if p.qualify x i then f i else 0):ℝ)=
        ∑ s∈ univ.filter (fun s:Pool (p.n x)=> (p.matter0 x).polls s),(f (p.printid x s):ℝ) := by
   classical
   let n:=p.n x
   let : Fact n.Prime:=p.primed x
   let F i:= (↑(if p.qualify x i then f i else 0):ℝ)
   push_cast
   calc
      _ = ∑ i∈Print.spine n,F i := by
             rw [Print.spine,sum_filter]
             refine sum_congr rfl fun i _=> ?_
             unfold F qualify
             by_cases h: Print.publish (p.n x) i=true
             · simp [h,n]
             simp [h,n]
      _ = _:=by
          rw [Print.columns (n:=n),sum_filter]
          refine sum_congr rfl fun i hi=>?_
          unfold F
          change (↑(if p.qualify x (p.printid x i) then f (p.printid x i) else 0):ℝ)=_
          split <;> have ht:= p.verified x i <;> grind

def sumtop (x:Word)(f:ℕ→ℕ) :ℕ:=
       ∑ i∈range (Print.pages (p.n x)), if p.qualify x i then min 64 (f i) else 0
lemma totalK (f:PT ℕ ℕ)(h:Kn f){α}[Wire α]: Kn (fun x (_:α)=> p.sumtop x (f x)):=by
   let g:PT (α × ℕ × ℕ) ℕ:= fun x a=> a.2.2+
                            (if p.qualify x a.2.1 then min 64 (f x a.2.1) else 0)
   have hg:Kn g:= Kn.next.right.add ((p.qualifyK.comp Kn.next.left).cond
                                        ((Kn.fix _).small (h.comp Kn.next.left)) (Kn.fix _))
   have hp (x a j):forNat (fun k v=>g x (a,k,v)) 0 j=
                   ∑ i∈range j, (if p.qualify x i then min 64 (f x i) else 0):=by
       induction j with
       | zero=> simp [forNat]
       | succ i ih=> rw [sum_range_succ,← ih]; rfl
   have ht:Kn (fun x (_:α)=> Print.pages (p.n x)):=Print.pagesK p.nKn
   simpa only [hp,sumtop] using Kn.stroll g _ (fun _ _=>0) _ hg ht (Kn.fix 0) (ht.times (Kn.fix 64)) (by
      intro x a B he
      rw [hp]
      apply le_trans (b:=∑ i∈range B,(64:ℕ))
      · exact sum_le_sum (fun i hi=>by split <;> omega)
      · simpa using Nat.mul_le_mul_right 64 he)

def census (x:Word):ℕ:=p.sumtop x (fun _=>1)
lemma witness0 (x): (p.census x:ℝ) = (univ.filter (fun s:Pool (p.n x)=> (p.matter0 x).polls s)).card:= by
   simpa only [census,sumtop,min_eq_right (show 1≤(64:ℕ) by omega),sum_const,nsmul_eq_mul,Nat.cast_one,mul_one] using p.numbers x (fun _=>1)
lemma positive0 (x):0 < p.census x:=by
   have h0:= (p.matter0 x).quorum
   have hz:= p.witness0 x
   have ht:p.census x=(univ.filter (fun s:Pool (p.n x)=>(p.matter0 x).polls s)).card:=by
        exact_mod_cast hz
   rwa [ht]

def survey (f:PT ℕ ℕ)(x)(s:Pool (p.n x)):ℝ:= (↑(min 64 (f x (p.printid x s))):ℝ) /64
lemma countok (f:PT ℕ ℕ)(x) :
    p.sumtop x (f x)=p.sumtop x (f x) ∧
       ((p.sumtop x (f x):ℝ)/64) = (p.census x:ℝ)*(p.matter0 x).evidence (p.survey f x):=by
   refine ⟨rfl,?_⟩
   rw [p.witness0,← Matter.tally_eq]
   unfold survey
   rw [← sum_div]
   congr 1
   exact p.numbers x (fun v=> min 64 (f x v))

def answer (f:PT ℕ ℕ) (x:Word) :ℕ :=
   if p.census x*32 < p.sumtop x (f x) then 1 else 0
lemma zenK {n:PT ℕ ℕ} (h:Kn n) (x : Word → ℕ) (ht : n=fun w _=>x w):
   E (fun y _=> x y):= by
   rw [ht] at h
   exact h (E.const 0)
lemma censusK : E (fun x _=> p.census x):=
   zenK (p.totalK (α:=ℕ) _ (Kn.fix 1)) _ (by rfl)
lemma tallyK (f:PT ℕ ℕ)(h:Kn f) : E (fun x _=> p.sumtop x (f x)) :=
   zenK (p.totalK (α:=ℕ) _ h) _ rfl
lemma annK (f:PT ℕ ℕ)(h: Kn f): E (fun x _=> p.answer f x):=
        (p.censusK.mul (E.const 32)).ite_lt (p.tallyK f h) (E.const 1) (E.const 0)

lemma scale_cnv {t:ℚ}: (t ≤ (1:ℚ)/3 → (t:ℝ) ≤1/3) ∧ ((2:ℚ)/3≤ t → (2:ℝ)/3≤ t):= by
    constructor <;> intro h
    · have hp:(↑t:ℝ)≤ ↑((1:ℚ)/3):= Rat.cast_le.mpr h
      push_cast at hp; exact hp
    have hp:(↑((2:ℚ)/3):ℝ) ≤ (t:ℝ):= Rat.cast_le.mpr h
    push_cast at hp; exact hp
lemma certificate {t v:ℝ}{a b:ℕ} {h:Prop} (hp: -(1/8:ℝ)< t-v ∧ t-v<1/8)
    (h0:0<(a:ℝ)) (hx:(b:ℝ)/64=a*v) (ht:¬h→ t≤ 1/3) (hu:h → 2/3≤ t):
     a*32 < b ↔ h:=by
       constructor
       · intro hs
         by_contra hv
         have hr:=ht hv
         have he:(a:ℝ)*32 < b:=by exact_mod_cast hs
         nlinarith [hp.1,hp.2]
       intro hs
       have hz:=hu hs
       have hc:(a:ℝ)*32 < b:=by nlinarith [hp.1,hp.2]
       exact_mod_cast hc
theorem convince {A:Language}(hS:p.P.Space)(p1: p.w.Proof)(hv:6≤p.pad)
    (hm:p1.T.bank≤Est.box p.pad)
    (fo:PT ℕ ℕ)(he:Kn fo)
    (ha:∀ x (s:Pool (p.n x)),
       let m:= p.matter0 x
       m.polls s → |p.survey fo x s-m.oracleV s m.i|≤ 1/32)
    (hs:∀ x∈A, (2/3:ℚ) ≤ p.P.mach.acceptanceProbability x (p.P.clock x))
    (ht:∀ x, x∉A → p.P.mach.acceptanceProbability x (p.P.clock x) ≤ (1/3:ℚ)):
    A∈ L :=by
    apply (p.annK fo he).gives_L _
    intro x
    have hx:=(p.countok fo x).2
    have hp :=Matter.probes (p:=p1) (p.matter0 x) hS (p.prompts p1 hv hm x) (p.survey fo x) (ha x)
    let t:ℝ:=p.P.mach.acceptanceProbability x (p.P.clock x)
    let v:ℝ:=(p.matter0 x).evidence (p.survey fo x)
    change |t-v|<_ at hp
    rw [abs_lt] at hp
    let a:=p.census x
    let b:=p.sumtop x (fo x)
    have h1 :0<(a:ℝ):=by exact_mod_cast p.positive0 x
    change (b:ℝ)/_=↑a*v at hx
    change p.answer fo x≠0↔ _
    unfold answer; change (if a*32<b then _ else _)≠_ ↔ _
    suffices hh:a*32 < b ↔x ∈ A by simpa using hh
    apply certificate hp h1 hx ?_ ?_
    · intro hy; exact scale_cnv.1 (ht x hy)
    intro hy; exact scale_cnv.2 (hs x hy)

end
end Rock
end ExactDerandomization.Grain

end

section

namespace ExactDerandomization.Grain
open Relay Counter Rill Analysis Square Affine Env Wrap Finset
namespace Print
noncomputable section
abbrev Z4:=Four ℤ

def zd (a:Page):Z4:=vmap (fun i:ℕ=>(i:ℤ)) a
def red (n:ℕ ) (a:Z4) :Page:=vmap (fun i:ℤ=>(i%(n:ℤ)).toNat) a

def change0 (n:ℕ ) (g:Gen ) (v:Page):Page:=red n (pol false g (zd v))
def change1 (n:ℕ ) (g:Gen ) (v:Page ) (k:ℕ ) (w:W):Page:=
    red n (pol true g (zd v)+addin (side n k) w)
def bare (n:ℕ ) (g:Gen ) (s:Stamp):Stamp:=(change0 n g s.1,red n (pol true g (zd s.2)))
def walkstep (n:ℕ ) (g:Gen ) (k:ℕ ) (w:W ) (s:Stamp):Stamp:=
         (change0 n g s.1,change1 n g s.2 k w)

def reducep (a:Page ) (m:ℕ):Page:= vmap (· % m) a
def fetch (n k i:ℕ ) (g:Gen ) (s:Stamp):W:=
    guess (side n k) (pol true g (zd (reducep (mix n i s.2 s.1) (side n k))))

variable {n m:ℕ} [Fact n.Prime] [NeZero m]
omit [NeZero m] in
lemma readout (v:V m) : zd (ncard v)=raiseV v:= rfl
lemma redCast (v:Z4):red m v=ncard (reduceV m v):=by
    have h(i:ℤ):(i%(m:ℤ)).toNat=(i:ZMod m).val:=by
       rw [← ZMod.val_intCast]; omega
    simp only [red,ncard,vmap,reduceV,h]
omit [NeZero m] in
lemma reducePol_any (b g) (t: Z4) : reduceV m (pol b g t)=pol b g (reduceV m t) := by
   cases b
   · unfold pol; split
     all_goals
       unfold reduceV lower vmap
       cases he:g.2 with
       | inl u=>
          cases u with
          | inl b=> rcases b with ⟨a,b⟩; cases a <;> simp
          | inr b=>cases b <;> simp
       | inr u=> rcases u with ⟨a,b⟩; cases a <;> cases b <;> simp
   · exact reducePol g t

lemma prints_any (v:V m ) (b g):red m (pol b g (zd (ncard v)))=ncard (act b g v):=by
    rw [readout,redCast,reducePol_any,reraise,act_formula]
lemma recast (g ) (s:Channel n):
    bare n g (badge s)=badge (gens n g s):=by
   let a:=s.1.val; let b:=s.2
   exact Prod.ext (prints_any a false g) (prints_any b true g)
lemma zoom (g k w ) (s:Channel n):
    walkstep n g k w (badge s)=badge (Variant k g w s):=by
    let a:=s.1.val; let b:=s.2
    have he:change1 n g (ncard b) k w=ncard (act true g b+reduceV n (addin (side n k) w)):=by
        rw [change1,redCast,reduce_add,readout,reducePol,reraise,act_formula]
    exact Prod.ext (prints_any a false g) he

lemma fetching (k i:ℕ ) (g ) (s:Channel n):
    fetch n k i g (badge s)=guessP k g (closeP k (↑i:ZMod n) s):= by
     let v:=vEval s (↑i:ZMod n)
     have he:mix n i (badge s).2 (badge s).1=ncard v:=(nadd ..).symm
     rw [fetch,he]
     have ht: reducep (ncard v) (side n k)=ncard (vshort k v):= by
        simp only [reducep,ncard,vshort,vmap,ZMod.val_natCast]
     rw [ht,readout]; rfl

variable {α β γ:Type}[Wire α][Wire β][Wire γ]
lemma quads {s:PT α (Four β)} (h:Kn s ) (f:PT (α×β) γ ) (e:Kn f):
    Kn (fun x a=>vmap (fun i=>f x (a,i)) (s x a)):=by
    exact ((e.comp (Kn.identity.tuple h.left.left)).tuple
                (e.comp (Kn.identity.tuple h.left.right))).tuple
             ((e.comp (Kn.identity.tuple h.right.left)).tuple
                (e.comp (Kn.identity.tuple h.right.right)))
lemma zdK {s:PT α Page}(h:Kn s):Kn (fun x a=>zd (s x a)):=quads h (fun _ (a:α×ℕ)=>(a.2:ℤ)) Kn.next.ZofN

lemma holeK {x:PT α ℤ} {m:PT α ℕ} (h:Kn x ) (e:Kn m) :
    Kn (fun w a=> x w a%((m w a:ℕ):ℤ)):= by
    convert e.cond_eq (Kn.fix 0) h (h.modulus e.pred) using 1
    ext w a; split
    · simp_all
    · next hz=> simp [Nat.sub_add_cancel (show 1 ≤ m w a by omega)]

lemma redK {f:PT α Z4} {m:PT α ℕ}(h:Kn f ) (e:Kn m):
    Kn (fun w a=> red (m w a ) (f w a)) :=
       quads h (fun w (a:α×ℤ)=>(a.2%(m w a.1)).toNat) ((holeK Kn.next (e.comp Kn.first)).topNat)
lemma plow (b:Bool ) (g:Affine.Cmd) {s t:PT α (ℤ×ℤ)} (h:Kn s ) (e:Kn t):
    Kn (fun x a => lower b g (s x a) (t x a)):= by
    cases g with
    | inl c=>
      cases c with
      | inl c=>
        rcases c with ⟨w,z⟩; cases w
        · exact h.left.tuple (h.right.plusZ ((Kn.fix (-(amount z:ℤ))).prodZ h.left))
        exact (h.left.plusZ ((Kn.fix (-(amount z:ℤ))).prodZ h.right)).tuple h.right
      | inr c=>
        cases b
        · exact h
        cases c
        · exact h.left.tuple (h.right.plusZ (Kn.fix _))
        exact (h.left.plusZ (Kn.fix _)).tuple h.right
    | inr c=>
      rcases c with ⟨i,j⟩; cases i <;> cases j
      · exact h.left.tuple (h.right.plusZ e.right)
      · exact h.left.tuple (h.right.plusZ e.left)
      · exact (h.left.plusZ e.right).tuple h.right
      exact (h.left.plusZ e.left).tuple h.right

lemma polK {f:PT α Z4}(h:Kn f ) (b:Bool ) (g:Gen):Kn (fun w a=> pol b g (f w a)):= by
   rcases g with ⟨i,j⟩; cases i
   · exact (plow b j h.left h.right).tuple h.right
   exact h.left.tuple (plow b j h.right h.left)

lemma plusK {f g:PT α Z4}(h:Kn f ) (e:Kn g): Kn (fun w a=> f w a+g w a):=
    ((h.left.left.plusZ e.left.left).tuple (h.left.right.plusZ e.left.right)).tuple
               ((h.right.left.plusZ e.right.left).tuple (h.right.right.plusZ e.right.right))

lemma addK {f:PT α ℕ}(h:Kn f ) (v:W):Kn (fun w a=> addin (f w a) v):=by
    have he(i:Fin 11):Kn (fun w a=> (f w a:ℤ)*((i.val:ℤ)-5)) := h.ZofN.prodZ (Kn.fix _)
    exact ((he _).tuple (he _)).tuple ((he _).tuple (he _))

lemma bareK {f:PT α Stamp}(h:Kn f ) (g:Gen){p:PT α ℕ}(he:Kn p):
    Kn (fun x a=> bare (p x a) g (f x a)) :=
    (redK (polK (zdK h.left) false g) he).tuple (redK (polK (zdK h.right) true g) he)
lemma zoomK {f:PT α Stamp}(h:Kn f ) (g:Gen){p k:PT α ℕ}(hp:Kn p ) (hk:Kn k ) (v:W):
    Kn (fun x a=>walkstep (p x a) g (k x a) v (f x a)) :=
   (redK (polK (zdK h.left) false g) hp).tuple
     (redK (plusK (polK (zdK h.right) true g) (addK (asideK hp hk) v)) hp)

lemma downK {x m:PT α ℕ}(h:Kn x ) (e:Kn m): Kn (fun w a=> x w a/m w a):= h.div e
lemma dropK {x:PT α ℤ} {m:PT α ℕ}(h:Kn x ) (e:Kn m):Kn (fun w a=> x w a/(m w a:ℕ)):=by
   convert e.cond_eq (Kn.fix 0) (Kn.fix 0) (h.chop e.pred) using 1
   ext w a; split
   · next hz=> simp [show m w a=0 from hz]
   next hz=> simp [Nat.sub_add_cancel (show 1 ≤ m w a by omega)]
lemma pickK {f:PT α Z4}(h:Kn f) {m:PT α ℕ}(e:Kn m):
    Kn (fun w a=> vmap (fun i:Fin 11=>i.val) (guess (m w a ) (f w a))):=by
    have hp {s:PT α ℤ}(hs: Kn s):Kn (fun w a=>(chooseOne (m w a) (s w a)).val) :=
        (Kn.fix 10).small (((Kn.fix 5).plusZ ((dropK hs e).negZ)).topNat)
    exact ((hp h.left.left).tuple (hp h.left.right)).tuple
          ((hp h.right.left).tuple (hp h.right.right))
lemma fetchK0 {p k z:PT α ℕ}{f:PT α Stamp}(h:Kn f ) (g:Gen ) (hp:Kn p ) (hk:Kn k ) (hz:Kn z):
    Kn (fun x a=>vmap (fun i:Fin 11=>i.val)
                       (fetch (p x a ) (k x a) (z x a) g (f x a))):=by
   have he:= asideK hp hk
   let u (x a):=mix (p x a ) (z x a) ((f x a).2) ((f x a).1)
   have ht:Kn u:= mixK hp hz h.right h.left
   have hv := quads ht _ (Kn.next.mod (he.comp Kn.first))
   exact pickK (polK (zdK hv) true g) he
lemma fetchK {p k z:PT α ℕ}{f:PT α Stamp}(h:Kn f ) (g:Gen ) (hp:Kn p ) (hk:Kn k ) (hz:Kn z ) (v):
    Kn (fun x a=>decide (fetch (p x a ) (k x a ) (z x a) g (f x a)=v)):=by
   let glyph (v:W):=enc (vmap (fun i:Fin 11=>i.val) v)
   have he : Function.Injective glyph:=by
     intro a b hx
     have hp:=congrArg (fun n=>(dec n:Page)) hx; unfold glyph at hp
     simp [vmap,Prod.ext_iff] at *
     exact ⟨⟨Fin.ext hp.1.1,Fin.ext hp.1.2⟩,Fin.ext hp.2.1,Fin.ext hp.2.2⟩
   let s x a:=fetch (p x a ) (k x a ) (z x a) g (f x a)
   convert (Kn.wash.comp (fetchK0 h g hp hk hz)).eq (Kn.fix (glyph v)) using 1
   ext x a
   change decide (s x a=v)=decide (glyph (s x a)=glyph v)
   simp [he.eq_iff]

end
end Print
end ExactDerandomization.Grain

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Grain
open Relay Counter Rill Analysis Square Affine Env Wrap Finset
namespace Print
noncomputable section
abbrev Token:= Atom×Roller

def checkS (v:Token)(n k _ x:ℕ)(s:Issue):Bool :=
   if v.1.1 then match v.1.2 with
     | .inl i=> decide (fetch n k x i s.1=v.2)
     | .inr (.inl _)=>true
     | _=> decide (v.2=0)
   else decide (v.2=0)
def checkD (v:Token)(n _ j x:ℕ)(s:Issue):Bool :=
   if v.1.1 then match v.1.2 with
     | .inr (.inl i)=> decide (fetch n j x i s.2.1=v.2)
     | _=>true
   else true
def arch (v:Token)(n k j:ℕ)(s:Issue):Issue:=
   if v.1.1 then match v.1.2 with
     | .inl i=> (walkstep n i k v.2 s.1,s.2)
     | .inr (.inl i)=> (s.1,walkstep n i j v.2 s.2.1,s.2.2)
     | .inr (.inr (.inl i))=> (s.1,s.2.1,bare n i s.2.2)
     | _=>s
   else s
abbrev Bundle:=(ℕ×ℕ×ℕ)×ℕ×Issue
def tossR (b:Bool)(v:Token)(_ :Word)(a:Bundle):Bool×Issue:=
    let (n,k,j):=a.1
    let (x,s):=a.2
    (if b then checkS v n k j x s else checkD v n k j x s, arch v n k j s)

variable {n:ℕ} [Fact n.Prime]
lemma rose (v:Token)(k j)(s:Env n 0):arch v n k j (issued s)=
                   issued (rol k j (d:=0) (w:=0) le_rfl v.1 v.2 s):=by
    rcases v with ⟨⟨b,i|i|i|i⟩,v⟩ <;> cases b <;>
     rcases s with ⟨s,t,u,w⟩ <;> simp [issued,arch,rol,rollG,unionG,zoom,recast]

lemma landlord (v:Token)(k j x y:ℕ)(s:Env n 0):
    v.2=winner k j (↑x:ZMod n) (↑y:ZMod n) v.1 s ↔
          checkS v n k j x (issued s)=true ∧ checkD v n k j y (issued s)=true :=by
   rcases s with ⟨s,t,u,w⟩; rcases v with ⟨⟨b,i|i|i|i⟩,v⟩ <;>
     cases b <;> simp [issued,winner,checkS,checkD,fetching,eq_comm]

lemma S_K(v:Token):
   Kn (fun (_:Word)(a:Bundle)=>checkS v a.1.1 a.1.2.1 a.1.2.2 a.2.1 a.2.2):=by
    rcases v with ⟨⟨b,i|i|i|i⟩,v⟩ <;> cases b
    all_goals first| exact Kn.fix _ |
        exact fetchK Kn.next.right.left i Kn.first.left Kn.first.right.left Kn.next.left v
lemma D_K(v:Token):
   Kn (fun (_:Word)(a:Bundle)=>checkD v a.1.1 a.1.2.1 a.1.2.2 a.2.1 a.2.2):=by
    rcases v with ⟨⟨b,i|i|i|i⟩,v⟩ <;> cases b <;> first| exact Kn.fix _ |
       exact fetchK Kn.next.right.right.left i Kn.first.left Kn.first.right.right Kn.next.left v

lemma A_K(v:Token):
   Kn (fun (_:Word)(a:Bundle)=> arch v a.1.1 a.1.2.1 a.1.2.2 a.2.2):=by
   have hz:Kn (fun (_:Word)(a:Bundle)=>a.2.2):=Kn.next.right
   rcases v with ⟨⟨b,i|i|i|i⟩,v⟩ <;> cases b
   · exact hz
   · exact (zoomK hz.left i Kn.first.left Kn.first.right.left v).tuple hz.right
   · exact hz
   · exact hz.left.tuple
                     ((zoomK hz.right.left i Kn.first.left Kn.first.right.right v).tuple hz.right.right)
   · exact hz
   · exact hz.left.tuple (hz.right.left.tuple (bareK hz.right.right i Kn.first.left))
   · exact hz
   · exact hz
lemma tossed(b:Bool)(v) : Kn (tossR b v):= by
   cases b
   · exact Kn.tuple (D_K v) (A_K v)
   · exact Kn.tuple (S_K v) (A_K v)

abbrev rad:=Fintype.card Token
lemma rad_pos:0<rad:= Fintype.card_pos
def number : Fin rad≃Token := (Fintype.equivFin Token).symm
def mark (i:ℕ):Token:=number ⟨i%rad,Nat.mod_lt _ rad_pos⟩

lemma mintK {α β} [Wire α][Wire β](f:Token→ PT α β) (h:∀ v,Kn (f v))
   (k:PT α ℕ)(hp:Kn k):Kn (fun x a=> f (mark (k x a)) x a):= by
  let u(v:Fin rad):= v.val
  let m:Fin rad := ⟨0,rad_pos⟩
  classical
  have he (s: ℕ):
    Kn (fun x a=> let n:= (k x a)%rad
                  if n < s then f (mark n) x a else f (mark 0) x a):=by
     induction s with
     | zero=> simpa using h (mark 0)
     | succ s ih =>
       convert ((hp.mod (Kn.fix rad)).cond_eq (Kn.fix s) (h (mark s)) ih) using 1
       ext x a
       dsimp only
       generalize k x a % rad=n
       by_cases he:n=s
       · subst s
         rw [ite_eq_left (by omega),ite_eq_left rfl]
       rw [ite_eq_right he]
       by_cases ht:n<s
       · rw [ite_eq_left (by omega),ite_eq_left ht]
       rw [ite_eq_right (by omega),ite_eq_right ht]
  have ht (v):v%rad<rad:=Nat.mod_lt v rad_pos
  convert he rad using 1
  ext x a
  dsimp only
  rw [ite_eq_left (ht _)]
  simp only [mark,Nat.mod_mod]

def queue : (l c:ℕ) → Paths Atom l×Paths Roller l
   | 0,_=>((),())
   | l+1,c=>
     let u:=mark c
     let v:=queue l (c/rad)
     ((u.1,v.1),(u.2,v.2))

lemma width (r:ℕ)(_:0< r)(n:ℕ)(f:ℕ→ℝ):
   ∑ i∈range (r*n),f i = ∑ i∈range r, ∑ j∈range n,f (i+j*r):=by
   induction n with
   | zero=> simp
   | succ n ih=>
     conv_rhs => arg 2; ext; rw [sum_range_succ]
     rw [mul_add,mul_one, sum_add_distrib,← ih]
     have ht := sum_range_add f (r*n) r
     rw [ht]; simp [Nat.add_comm,mul_comm]

lemma emblem (v:Token→ℝ):
    ∑ i ∈ range rad, v (mark i)= ∑ i:Token,v i:=by
   rw [← Fin.sum_univ_eq_sum_range (fun i => v (mark i))]
   exact Fintype.sum_equiv number _ _ (fun i=>by
       have hp: mark (i:Fin rad).val=number i := congrArg number (Fin.ext (Nat.mod_eq_of_lt i.isLt))
       simp only [hp])

lemma touring (l:ℕ)(f:Paths Atom l → Paths Roller l → ℝ):
    ∑ i ∈ range (rad^l), f (queue l i).1 (queue l i).2 =∑ p,∑ g,f p g:=by
    induction l with
    | zero=> simp [queue]
    | succ l ih=>
      rw [pow_succ',width rad rad_pos]
      let v (s:Token):= ∑ a,∑ b, f (s.1,a) (s.2,b)
      have he (i) (hi:i<rad): ∑ j∈range (rad^l),f (queue _ (i+j*rad)).1 (queue _ (i+j*rad)).2=v (mark i):=by
          convert ih (fun a b=> f ((mark i).1,a) ((mark i).2,b)) using 1
          apply sum_congr rfl; intro j hj
          simp only [queue,Nat.add_mul_div_right _ _ rad_pos,Nat.div_eq_of_lt hi,zero_add,
                  mark,Nat.add_mul_mod_self_right]
      have hx:= sum_congr rfl (fun i (e:i∈range rad)=>he i (mem_range.1 e))
      rw [hx,emblem]
      rw [Fintype.sum_prod_type]; rw [pathFold Atom l]
      apply sum_congr rfl; intro a _
      simp_rw [pathFold Roller l]
      unfold v; rw [sum_comm]
end
end Print
end ExactDerandomization.Grain

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Grain
open Relay Counter Rill Analysis Square Affine Env Wrap Finset
namespace Print
noncomputable section

abbrev Guide:= (ℕ×ℕ×ℕ)×ℕ
abbrev MapState:=ℕ×Bool×Issue

def goon (b:Bool ) (x:Word ) (a:Guide × MapState):MapState :=
   let t:= tossR b (mark a.2.1) x (a.1.1,a.1.2,a.2.2.2)
   (a.2.1/rad, a.2.2.1 && t.1, t.2)

lemma goonK (b):Kn (goon b):=by
   let f (v:Token ) (x:Word ) (a:Guide×MapState):=
       tossR b v x (a.1.1,a.1.2,a.2.2.2)
   have hp(v):Kn (f v):= (tossed b v).comp (Kn.first.left.tuple
                                       (Kn.first.right.tuple Kn.next.right.right))
   have he:=mintK f hp _ Kn.next.left
   exact (Kn.next.left.div (Kn.fix rad)).tuple ((both Kn.next.right.left he.left).tuple he.right)

abbrev Lap:=Guide × MapState × ℕ
def capz (a:Lap) :ℕ:=
   bead a.2.1.1 (bead 1 (pages a.1.1.1))
lemma capzK:Kn (fun (_:Word ) (a:Lap)=>capz a):=by
   have h1:= (Kn.first (α:=Guide ) (β:=MapState×ℕ)).left.left
   have he:= pagesK h1
   have hz:= Kn.wash.comp ((Kn.fix (1:ℕ)).tuple he)
   exact Kn.wash.comp (Kn.next.left.left.tuple hz)
def spin (b:Bool ) (x:Word ) (a:Lap):MapState:=
   let L:=capz a
   dec (forNat (fun _ (v:ℕ)=> min L (enc (goon b x (a.1,dec v))))
        (min L (enc a.2.1)) a.2.2)

lemma spinK (b):Kn (spin b):=by
   let f:PT (Lap×ℕ×ℕ) ℕ:=fun x a=>min (capz a.1) (enc (goon b x (a.1.1,dec a.2.2)))
   have ht := Kn.stroll f _ _ _ ((capzK.comp Kn.first).small
       (Kn.wash.comp ((goonK b).comp (Kn.first.left.tuple (Kn.unpack.comp Kn.next.right)))))
          (Kn.next (α:=Guide ) (β:=MapState×ℕ)).right
          (capzK.small (Kn.wash.comp Kn.next.left)) capzK (by
             intro x a j _
             cases j <;> exact min_le_left _ _)
   exact Kn.unpack.comp ht

variable {n:ℕ}[Fact n.Prime]
lemma limits {v c k j x m H} (h:v≤c) (s:Env n 0 ) (b r:Bool) :
   enc ((v,b,issued s):MapState)≤ capz (((n,k,j),x),(c,r,m),H) :=
   bead_mono h (bead_mono (show enc b≤1 by cases b <;> decide) (boxbound s).le)

def scoreQ (b:Bool ) (k j x:ℕ) :
       {l:ℕ}→Paths Atom l → Paths Roller l→ Env n 0→ Bool
   | 0,_,_,_=>true
   | _+1,(t,a),(v,w),s=>
      (if b then checkS (t,v) n k j x (issued s) else checkD (t,v) n k j x (issued s)) &&
                   scoreQ b k j x a w (rol k j (d:=0 ) (w:=0) le_rfl t v s)

lemma wellQ (k j x y:ℕ){l:ℕ}(a:Paths Atom l ) (b:Paths Roller l ) (s:Env n 0):
   live k j (↑x:ZMod n) (↑y:ZMod n) (d:=0 ) (w:=0) le_rfl a b s=true ↔
       scoreQ true k j x a b s=true ∧ scoreQ false k j y a b s=true:=by
   induction l generalizing s with
   | zero=> simp [live,scoreQ]
   | succ l ih=>
     cases a with | mk t a=>
      cases b with | mk v b=>
       unfold live scoreQ
       let u:Token :=(t,v)
       have hx:= landlord u k j x y s
       dsimp only [u] at hx
       simp only [Bool.and_eq_true,ite_true,Bool.false_eq_true,ite_false]
       split
       · next hz=> have hp:=hx.1 hz; simp [hp,ih]
       next hz=> simp; grind

theorem flowed (b:Bool ) (k j i l c:ℕ ) (x:Word ) (s:Env n 0 ) (v:Bool) :
   spin b x (((n,k,j),i),(c,v,issued s),l) =
        let P:=queue l c
        (c/rad^l, v && scoreQ b k j i P.1 P.2 s,
                         issued (go k j (d:=0 ) (w:=0) le_rfl P.1 P.2 s)) :=by
    let q:Guide:=((n,k,j),i)
    let p:Lap:=(q,(c,v,issued s),l)
    let M:=capz p
    let f (z:ℕ):= min M (enc (goon b x (q,dec z)))
    have he(l':ℕ ) (c':ℕ ) (hv:c'≤c ) (v':Bool ) (s':Env n 0):
      forNat (fun _=> f) (enc ((c',v',issued s'):MapState)) l' =
        let P:=queue l' c'
        enc ((c'/rad^l',v'&&scoreQ b k j i P.1 P.2 s',
              issued (go k j (d:=0 ) (w:=0) le_rfl P.1 P.2 s')):MapState):=by
        induction l' generalizing c' v' s' with
        | zero=> simp [forNat,go,scoreQ]
        | succ l' ih=>
          let c0:=c'/rad
          have ht:c0≤c:=le_trans (Nat.div_le_self ..) hv
          let u:=mark c'
          let s0:=rol k j (d:=0 ) (w:=0) le_rfl u.1 u.2 s'
          let b0:=v' && (tossR b u x (q.1,q.2,issued s')).1
          have hh:f (enc ((c',v',issued s'):MapState))=enc ((c0,b0,issued s0):MapState):=by
               dsimp only [f]
               rw [dec_round]; unfold goon
               change min M (enc ((c0,b0,arch u n k j (issued s')):MapState))=_
               rw [rose]; exact min_eq_right (limits ht s0 b0 v)
          rw [forNat_cons,hh,ih c0 ht]
          simp only [c0,b0,q,s0,u, queue, tossR,scoreQ,go,Equiv.trans_apply,Nat.div_div_eq_div_mul,
                          pow_succ',Bool.and_assoc]
    unfold spin
    change dec (forNat _ (min M _) _)=_
    rw [min_eq_right (limits ..),he l c le_rfl]
    · dsimp only; simp only [Wire.eq]
    exact le_rfl

def stepout (n k j l a:ℕ ) (s:Issue):Issue:= (spin true [] (((n,k,j),0),(a,true,s),l)).2.2
def touched (b:Bool ) (n k j i l a:ℕ ) (s:Issue):Bool:=
                         (spin b [] (((n,k,j),i),(a,true,s),l)).2.1

lemma spin_null (b:Bool ) (x:Word ) (a:Lap):spin b x a=spin b [] a:=rfl

lemma stepK {α} [Wire α]{n k j l c :PT α ℕ}{s:PT α Issue}
   (hn:Kn n ) (hk:Kn k ) (hj:Kn j ) (hl:Kn l ) (hc:Kn c ) (hs:Kn s):
   Kn (fun x a=>stepout (n x a ) (k x a ) (j x a ) (l x a ) (c x a ) (s x a)) :=
   ((spinK true).comp (((hn.tuple (hk.tuple hj)).tuple (Kn.fix 0)).tuple
                                      ((hc.tuple ((Kn.fix _).tuple hs)).tuple hl))).right.right
lemma touchedK {α} [Wire α]{n k j i l c:PT α ℕ}{s:PT α Issue}
   (b ) (hn:Kn n ) (hk:Kn k ) (hj:Kn j ) (hi:Kn i ) (hl:Kn l ) (hc:Kn c ) (hs:Kn s):
   Kn (fun x a=> touched b (n x a ) (k x a ) (j x a ) (i x a ) (l x a ) (c x a ) (s x a)):=
   ((spinK b).comp (((hn.tuple (hk.tuple hj)).tuple hi).tuple
                                      ((hc.tuple ((Kn.fix _).tuple hs)).tuple hl))).right.left

lemma unpacked (k j l a ) (s:Env n 0):
   stepout n k j l a (issued s)=issued
                 (go k j (d:=0 ) (w:=0) le_rfl (queue l a).1 (queue l a).2 s):=by
   rw [stepout,flowed]
lemma exactHit (k j x y l a:ℕ ) (s:Env n 0):
   live k j (↑x:ZMod n) (↑y:ZMod n) (d:=0 ) (w:=0) le_rfl (queue l a).1 (queue l a).2 s=true ↔
     touched true n k j x l a (issued s)=true ∧ touched false n k j y l a (issued s)=true := by
   simp only [touched,flowed, Bool.true_and]; exact wellQ k j x y ..
end
end Print
end ExactDerandomization.Grain

end

end OAI
