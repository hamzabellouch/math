import OAI.Computability.Logspace.RecursivePrograms

namespace OAI

/-!
Catalytic comparison of encoded identifiers and bounded traversal operations.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Deterministic catalytic ID comparisons. B logarithmic is raw code-bit
bound for the ids. Work simultaneously active still controlled by the
priced Bout stack. -/
namespace ExactDerandomization.Glass
open Relay Counter Finset
namespace NatD

abbrev dig (b a k:ℕ) := a/b^k % b
def record (b:ℕ) (z:ℕ→ℕ)(k:ℕ):ℕ:= forNat (fun j a=> a+z j*b^j) 0 k
lemma next (b z k): record b z (k+1)=record b z k+z k*b^k := rfl
lemma under {b z k}(h:∀ j<k,z j<b): record b z k<b^k:=by
   induction k with
   | zero=> simp [record,forNat]
   | succ k ih=>
     have hz:=ih (fun j hj=>h j (by omega))
     have hv:=h k (by omega)
     rw [next,pow_succ,mul_comm (b^k)]
     have hx:=Nat.mul_le_mul_right (b^k) (show z k+1≤b from hv)
     nlinarith
lemma letter {b z k} (hb:2≤b) (h:∀ j<k,z j<b) {j:ℕ}(he:j<k):
   dig b (record b z k) j=z j := by
   induction k with
   | zero=>omega
   | succ k ih=>
     have hz:=under (b:=b) (k:=k) (fun j hj=> h j (by omega))
     have hs:0 < b^j:=Nat.pow_pos (by omega)
     by_cases hu:j=k
     · subst j
       unfold dig; rw [next,Nat.add_mul_div_right _ _ hs,Nat.div_eq_of_lt hz,zero_add,Nat.mod_eq_of_lt (h _ he)]
     unfold dig; rw [next]
     have hk : b^k=b^(k-(j+1))*b*b^j:=by
       rw [←pow_succ,←pow_add]; rw [show k-(j+1)+1+j=k by omega]
     rw [hk,show z k*(b^(k-(j+1))*b*b^j)=z k*b^(k-(j+1))*b*b^j by ring,
         Nat.add_mul_div_right _ _ hs,Nat.add_mul_mod_self_right]
     exact ih (fun j hz=>h j (by omega)) (by omega)

lemma record_mod (b x k:ℕ) (hb:2≤b) : record b (dig b x) k = x%(b^k):= by
   induction k with
   | zero=>simp [record,forNat]; omega
   | succ k ih=>
     rw [next,ih,pow_succ]
     have hk : 0 < b^k:=Nat.pow_pos (by omega)
     rw [Nat.mod_mul]
     dsimp [dig]; ring
lemma equal {b k x y:ℕ}(hb:2≤b)(hx:x<b^k)(hy:y<b^k)
    (h:∀ i<k,dig b x i=dig b y i) : x=y:= by
    have he : ∀ j≤k, record b (dig b x) j=record b (dig b y) j:=by
       intro j hj; induction j with
       | zero=>rfl
       | succ j ih=> rw [next,next,ih (by omega),h _ (by omega)]
    have ht:=he k le_rfl; simpa [record_mod _ _ _ hb,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using ht

lemma dial_eq {b x k} (_:0<b):x/min (x+1) (b^k)=x/(b^k):=by
    by_cases he:b^k≤x+1
    · rw [min_eq_right he]
    rw [min_eq_left (by omega),Nat.div_eq_of_lt (by omega),Nat.div_eq_of_lt (by omega)]
lemma digK {α} [Wire α] {b x k:PT α ℕ}(h:Kn b)(e:Kn x)(f:Kn k):
    Kn (fun w a=> dig (b w a) (x w a) (k w a)):=by

    convert (e.div (Kn.cap e.succ h f)).mod h using 1
    ext w a
    by_cases he:b w a=0
    · unfold dig; rw [he]
      cases k w a <;> simp
    unfold dig; rw [dial_eq (by omega)]
end NatD

structure Rod where
   peak :ℕ

namespace Rod
variable (p:Rod)
def B:=lb p.peak
def e:=lb p.B
def n:=2^p.e
def L:=p.B/p.e+1
def M:=p.n^4
def F:=p.M^p.L
def Q:= (2:ℕ)^p.n
lemma b0 :0< p.B:=lb_pos _
lemma e0 :0< p.e:=lb_pos _
lemma e2: p.e ≤ 2*p.B:=by
   have h:=p.b0; have he:=lb_le_inc p.B
   change lb p.B≤_; omega
lemma n2:2 ≤ p.n:=by
   have h:=p.e0; simpa [n] using Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two (show 1≤p.e from h)
lemma n_hi:p.B< p.n:=below _
lemma n_low: p.n≤ 2*p.B:=above p.b0
lemma L_le:p.L≤p.n:=by
    have he:=p.n_hi; unfold L; have hx:=Nat.div_le_self p.B p.e; omega
lemma L_price:p.e*p.L ≤ 3*p.B ∧ p.B ≤ p.e*p.L:=by
    unfold L; rw [left_distrib]
    have he:= p.e2; have ht:= Nat.mod_add_div p.B p.e; have hk:=Nat.mod_lt p.B p.e0
    omega
lemma coded {x}(h:x≤p.peak): x< p.n^p.L:= by
    have hz:= Nat.pow_le_pow_right (n:=2) Nat.zero_lt_two p.L_price.2
    unfold n; rw [←pow_mul]
    exact lt_of_le_of_lt h ((below _).trans_le hz)
lemma M4 :4≤p.M:= by
   have he:=Nat.pow_le_pow_left p.n2 4
   exact le_trans (by norm_num) he
lemma costs : p.F≤caplen p.peak ^ 12:=by
   have ht:=p.L_price.1
   unfold F M n caplen
   change ((2^p.e)^4)^p.L ≤ (2^p.B)^12
   rw [←pow_mul,←pow_mul,←pow_mul]; apply Nat.pow_le_pow_right (by omega)
   nlinarith
lemma costs2: p.Q≤caplen p.peak ^ 2:=by
   have he:=p.n_low
   unfold Q caplen; rw [←pow_mul]
   exact Nat.pow_le_pow_right Nat.zero_lt_two (show p.n ≤ p.B*2 by omega)
end Rod
end ExactDerandomization.Glass

end

section

namespace ExactDerandomization.Glass
open Relay Counter Finset NatD

def shove (m:ℕ)(b:Bool)(x y:ℕ):ℕ :=
    if b then (x+y)%m else (x+m-y%m)%m
lemma enoughS {m y x} (b:Bool)(he:0< m): shove m b x y< m:=by
    unfold shove; split <;> exact Nat.mod_lt _ he

namespace Rod
variable (p:Rod)
instance nzM : NeZero p.M:=⟨Nat.ne_of_gt (by have:=p.M4; omega)⟩
private lemma equals {x y:ℕ}(hx:x < p.M)(hy:y < p.M)
    (h:(x:ZMod p.M)=(y:ZMod p.M)) : x=y := by
    have he:=congrArg ZMod.val h
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] using he
lemma cast_shove (b x y) :
    (shove p.M b x y:ZMod p.M) =
       if b then (x:ZMod p.M)+y else (x:ZMod p.M)-y := by
   unfold shove; have hm : y%p.M ≤ x+p.M:=by
      have hr:=Nat.mod_lt y (le_trans (by omega :1≤4) p.M4); omega
   cases b <;> simp [Nat.cast_sub hm]
lemma cancel (b i j) (hi:i < p.M) : shove p.M (!b) (shove p.M b i j) j =i:= by
   refine p.equals (enoughS _ (by have:=p.M4; omega)) hi ?_
   simp_rw [p.cast_shove]; cases b <;> simp

def mix (b:Bool) (u x:ℕ) :=
   record p.M (fun i=>shove p.M b (dig p.M u i) (dig p.n x i)) p.L
lemma pigment (b u x):p.mix b u x < p.F:= by
    unfold mix F; apply under; intro i _
    apply enoughS; have := p.M4; omega
lemma component (b u x) {i} (he:i < p.L):
    dig p.M (p.mix b u x) i=shove p.M b (dig p.M u i) (dig p.n x i):= by
    have h:=p.M4
    unfold mix
    exact letter (by omega) (fun j hj=> enoughS _ (by omega)) he
lemma opposite {u}(b x)(hi:u < p.F):p.mix (!b) (p.mix b u x) x=u := by
    have h:=p.M4
    apply equal (by omega:2 ≤ p.M) (p.pigment ..) hi
    intro i hi
    rw [p.component _ _ _ hi,p.component _ _ _ hi]
    apply p.cancel; exact Nat.mod_lt _ (by omega)

def hinge (x y:ℕ):=∑ i∈ range p.L, dig p.n x i*dig p.n y i
def aloft (u x:ℕ):=∑ i∈range p.L,dig p.M u i*dig p.n x i

lemma twist (u x y):
    (p.aloft (p.mix true u x) y:ZMod p.M)= ↑(p.aloft u y)+↑(p.hinge x y) := by
    unfold aloft hinge; push_cast
    rw [← sum_add_distrib]
    apply sum_congr rfl; intro i hi
    rw [p.component _ _ _ (mem_range.1 hi),p.cast_shove,ite_eq_left rfl,add_mul]

abbrev Pane := ℕ×ℕ×ℕ
def proper (v:Pane):=v.1 < p.F ∧ v.2.1 < p.M ∧ v.2.2 < p.Q

def first (b:Bool)(x:ℕ)(v:Pane):Pane :=
    (p.mix b v.1 x, shove p.M b v.2.1 (p.hinge x x),v.2.2)
def second (b:Bool)(y:ℕ)(v:Pane):Pane :=
   (v.1,shove p.M (!b) (shove p.M b v.2.1 (p.hinge y y)) (2*p.aloft v.1 y), v.2.2)
def pointR (b:Bool)(x:ℕ)(v:Pane):Pane:= (p.mix (!b) v.1 x,v.2)
def pointZ (b:Bool)(x:ℕ)(v:Pane):Pane := (v.1, shove p.M b v.2.1 (2*p.aloft v.1 x),v.2.2)

lemma stay (b x) {v}(h:p.proper v): p.proper (p.first b x v) ∧ p.proper (p.second b x v) ∧
               p.proper (p.pointR b x v) ∧ p.proper (p.pointZ b x v):=by
   have hM:=p.M4; have he:0< p.M:=by omega
   exact ⟨⟨p.pigment ..,enoughS _ he,h.2.2⟩,⟨h.1,enoughS _ he,h.2.2⟩,
           ⟨p.pigment ..,h.2⟩,⟨h.1,enoughS _ he,h.2.2⟩⟩
lemma negone (b x) {v:Pane}(h:p.proper v):
    p.first (!b) x (p.first b x v)=v ∧ p.second (!b) x (p.second b x v)=v ∧
      p.pointR (!b) x (p.pointR b x v)=v ∧ p.pointZ (!b) x (p.pointZ b x v)=v :=by
    obtain ⟨v,z,Q⟩:=v
    have hM:=p.M4
    have hs(v w i):shove p.M v w i< p.M:=enoughS _ (by omega)
    refine ⟨?_,?_,?_,?_⟩
    · dsimp only [first]; rw [p.cancel b z _ h.2.1,p.opposite _ _ h.1]
    · unfold second; refine Prod.ext rfl (Prod.ext ?_ rfl)
      apply p.equals (hs ..) h.2.1
      dsimp only; simp_rw [p.cast_shove]; cases b <;> simp <;> ring
    · unfold pointR; exact Prod.ext (p.opposite (!b) x h.1) rfl
    · unfold pointZ; exact Prod.ext rfl (Prod.ext (p.cancel b _ _ h.2.1) rfl)

def fair (x y:ℕ)(v:Pane):Pane:=p.pointZ true y (p.pointR true x (p.second true y (p.first true x v)))
def dark (x y:ℕ)(v:Pane):Pane:=p.first false x (p.second false y (p.pointR false x (p.pointZ false y v)))
lemma sepia (x y) {v} (h:p.proper v): p.proper (p.fair x y v):=
   (p.stay true y ((p.stay true x ((p.stay true y ((p.stay true x h).1)).2.1)).2.2.1)).2.2.2
lemma back (x y) {v}(h:p.proper v): p.dark x y (p.fair x y v)=v := by
   let a:=p.first true x v
   let b:=p.second true y a
   let c:=p.pointR true x b
   have h1:p.proper a:=(p.stay true x h).1
   have h2:p.proper b:=(p.stay true y h1).2.1
   have h3:p.proper c:=(p.stay true x h2).2.2.1
   have e1:p.pointZ false y (p.pointZ true y c)=c:=(p.negone true y h3).2.2.2
   have e2:p.pointR false x c=b:=(p.negone true x h2).2.2.1
   have e3:p.second false y b=a:=(p.negone true y h1).2.1
   unfold dark; change p.first false x (p.second false y (p.pointR false x (p.pointZ false y (p.pointZ true y c))))=v
   rw [e1,e2,e3]; exact (p.negone true x h).1

def moat (a b i:ℕ):=dig p.n a i-dig p.n b i+(dig p.n b i-dig p.n a i)
def hugs (a b: ℕ):=∑ i∈range p.L,(p.moat a b i)^2

lemma bows (x y) : p.hugs x y+2*p.hinge x y=p.hinge x x+p.hinge y y := by
   unfold hugs hinge; rw [mul_sum,← sum_add_distrib,← sum_add_distrib]
   apply sum_congr rfl; intro i _
   let a:=dig p.n x i; let b:=dig p.n y i
   rcases le_total a b with h|h
   · have he:p.moat x y i+a=b:=by unfold moat; change (a-b+(b-a))+a=b; omega
     change _^2+2*(a*b)=a*a+b*b; nlinarith
   have he:p.moat x y i+b=a:=by unfold moat; change (a-b+(b-a))+b=a; omega
   change _^2+2*(a*b)=a*a+b*b; nlinarith
lemma small (x y): p.hugs x y < p.M:=by
    have hu:= p.n2
    have he: p.hugs x y≤ ∑ _∈range p.L,p.n^2:= sum_le_sum fun i _=> by
       have hh (x i):dig p.n x i< p.n := Nat.mod_lt _ (by omega)
       apply Nat.pow_le_pow_left
       unfold moat; have := hh x i; have := hh y i; omega
    simp at he
    have hr:=p.L_le
    unfold M
    exact lt_of_le_of_lt he (by nlinarith [Nat.mul_le_mul_right (p.n^2) hr])
lemma paw (x y) (hx:x≤p.peak)(hy:y≤p.peak): p.hugs x y=0 ↔ x=y:=by
   constructor
   · intro h
     have he:= p.coded hx
     apply equal p.n2 he (p.coded hy)
     intro i hi
     have hz : (p.moat x y i)^2 ≤ p.hugs x y := single_le_sum
                       (f:=fun i=> (p.moat x y i)^2) (fun _ _=>Nat.zero_le _) (mem_range.2 hi)
     have hu : p.moat x y i=0:=by rw [h,Nat.le_zero] at hz; simpa using hz
     unfold moat at hu; omega
   rintro rfl; simp [hugs,moat]

lemma pupils (x y) {v}(h:p.proper v):
   p.fair x y v = (v.1, shove p.M true v.2.1 (p.hugs x y),v.2.2) := by
   have he:=p.opposite true x h.1
   apply Prod.ext
   · exact he
   refine Prod.ext ?_ rfl
   have hM:=p.M4
   apply p.equals (p.sepia x y h).2.1 (enoughS true (by omega))
   unfold fair pointZ second pointR first
   dsimp only
   change mix ..=_ at he
   simp only [show (!(true:Bool))=false from rfl] at he
   simp only [Bool.not_true, he]
   simp_rw [p.cast_shove]
   push_cast
   rw [p.twist]
   have ht:= congrArg (fun k:ℕ=>(k:ZMod p.M)) (p.bows x y)
   push_cast at ht
   apply add_right_cancel (b:=2*(p.hinge x y:ZMod p.M))
   linear_combination -ht

lemma test_eye (x y)(hx:x≤p.peak)(hy:y≤p.peak){v}(h:p.proper v):
   (p.fair x y v).2.1=v.2.1 ↔ x=y:=by
   rw [p.pupils x y h]
   have hM:=p.M4
   constructor
   · intro he
     have hs:= congrArg (fun k:ℕ=>(k:ZMod p.M)) he
     rw [p.cast_shove] at hs
     apply (p.paw x y hx hy).1
     apply p.equals (p.small ..) (by omega)
     simpa using hs
   intro he; rw [(p.paw x y hx hy).2 he]
   simp only [shove,ite_true,Nat.add_zero,Nat.mod_eq_of_lt h.2.1]
end Rod
end ExactDerandomization.Glass

end

section

namespace ExactDerandomization.Glass
open Relay Counter NatD Finset
namespace Rod
variable (p:Rod)

def line (u i:ℕ):Bool:= decide (dig 2 u i=1)
def foil (u i:ℕ)(j:ℕ):ℕ:= if j=i then 1- dig 2 u j else dig 2 u j
lemma foil_lt (u i j):foil u i j<2:=by
   unfold foil; have hx:dig 2 u j<2:=Nat.mod_lt _ (by omega); split <;> omega
def frosting (u i:ℕ):ℕ:= record 2 (foil u i) p.n
lemma freeze (u i): p.frosting u i < p.Q:=under (fun _ _=>foil_lt ..)
lemma hit (u i j)(h:j<p.n): dig 2 (p.frosting u i) j = foil u i j:= by
    unfold frosting; apply letter (by omega) (fun j _=>foil_lt ..) h
lemma frost_eq (u i j)(h:j<p.n):
    line (p.frosting u i) j = if i=j then !(line u j) else line u j:= by
   by_cases he:i=j
   · have hz:dig 2 u j<2:=Nat.mod_lt _ (by omega)
     subst i; have he:(dig 2 u j)=0∨ dig 2 u j=1:=by omega
     cases he <;> simp_all [line,p.hit u j j h,foil]
   simp [line,p.hit u i j h,foil,he,Ne.symm he]
lemma frost_c {u}(i:ℕ)(h:u < p.Q):
   p.frosting (p.frosting u i) i=u:=by
   apply equal (by omega:2 ≤2) (p.freeze ..) h
   intro j hk; rw [p.hit _ _ _ hk]
   unfold foil; rw [p.hit _ _ _ hk]; unfold foil
   split
   · have hx:dig 2 u j<2:=Nat.mod_lt _ (by omega); omega
   all_goals simp_all

def glaze (v:Pane)(j:ℕ):Pane:=
   (v.1,v.2.1,p.frosting v.2.2 (dig p.n v.2.1 j))
def ask (v:Pane)(j:ℕ):Bool:=line v.2.2 (dig p.n v.2.1 j)
lemma glaze2 (j:ℕ) {v}(h:p.proper v):p.proper (p.glaze v j) ∧ p.glaze (p.glaze v j) j=v :=
    ⟨⟨h.1,h.2.1,p.freeze ..⟩, Prod.ext rfl (Prod.ext rfl (p.frost_c _ h.2.2))⟩
lemma glass {v}(h:p.proper v)(i x y:ℕ):
   (p.ask (p.fair x y (p.glaze v i)) i ≠ p.ask (p.fair x y v) i)↔
           (dig p.n (p.fair x y v).2.1 i = dig p.n v.2.1 i):=by
   rw [p.pupils x y h,p.pupils x y (p.glaze2 i h).1]
   have hk (v i): dig p.n v i < p.n:= Nat.mod_lt _ (by have := p.n2; omega)
   dsimp only [ask,glaze]; rw [p.frost_eq _ _ _ (hk ..)]
   split <;> grind

lemma learned (x y)(hx:x≤p.peak)(hy:y≤p.peak){v}(hv:p.proper v):
   x=y ↔ ∀ i<4, p.ask (p.fair x y (p.glaze v i)) i ≠ p.ask (p.fair x y v) i:=by
   have hh(i): p.ask (p.fair x y (p.glaze v i)) i ≠ p.ask (p.fair x y v) i↔
          dig p.n (p.fair x y v).2.1 i = dig p.n v.2.1 i:=p.glass hv i x y
   simp_rw [hh,← p.test_eye x y hx hy hv]
   constructor
   · intro h i he; rw [h]
   exact equal p.n2 (p.sepia x y hv).2.1 hv.2.1

end Rod
end ExactDerandomization.Glass

end

section

namespace ExactDerandomization.Glass
open Relay Counter Finset NatD
namespace Rod

variable {α} [Wire α] {p v u t:PT α ℕ}
private abbrev toR (p:PT α ℕ ) (x:Word ) (a:α):Rod:=⟨p x a⟩
lemma nFun (h:Kn p):Kn (fun x a=> (toR p x a).n):=Kn.caplenK.comp (Kn.bl h)
lemma lFun (h:Kn p):Kn (fun x a=> (toR p x a).L) := by
   have hp := h.bl; exact (hp.div hp.bl).succ
lemma mFun (h:Kn p):Kn (fun x a=>(toR p x a).M):=Kn.power 4 (nFun h)
lemma fFun (h:Kn p):Kn (fun x a=>(toR p x a).F):=by
   convert (Kn.cap (Kn.power 12 (Kn.caplenK.comp h)) (mFun h) (lFun h)) using 1
   ext x a; exact (min_eq_right (Rod.costs _)).symm
lemma qFun (h:Kn p):Kn (fun x a=>(toR p x a).Q):=by
   convert (Kn.cap (Kn.power 2 (Kn.caplenK.comp h)) (Kn.fix 2) (nFun h)) using 1
   ext x a; exact (min_eq_right (Rod.costs2 _)).symm

lemma shoveK (b:Bool) {f:PT α ℕ}(hf:Kn f ) (h:Kn v ) (e:Kn u):
   Kn (fun x a=> shove (f x a) b (v x a) (u x a)):= by
   cases b
   · exact ((h.add hf).sub (e.mod hf)).mod hf
   · exact (h.add e).mod hf
lemma drew {f k g:PT α ℕ}(r:PT (α×ℕ) ℕ) (hr:Kn r ) (hf:Kn f ) (hk:Kn k ) (hg:Kn g)
   (hz : ∀ x a, g x a=(f x a)^(k x a)) (hs:∀ x a,2≤ f x a)
   (hh:∀ x a j,r x (a,j) < f x a):
   Kn (fun x a=> record (f x a) (fun j=> r x (a,j)) (k x a)):=by
    let A:PT (α×ℕ×ℕ) ℕ:= fun x i=> i.2.2+r x (i.1,i.2.1)*min (g x i.1 ) ((f x i.1)^(i.2.1))
    have he(x a j ) (hi:j≤k x a):
        record (f x a) (fun j=>r x (a,j)) j= forNat (fun k v=>A x (a,k,v)) 0 j:=by
       induction j with
       | zero=> rfl
       | succ j ih=>
         rw [next,ih (by omega), forNat]
         dsimp only [A]; rw [hz,min_eq_right (Nat.pow_le_pow_right (by have:=hs x a; omega) (by omega))]
    have hu:=Kn.stroll A _ _ g
            (Kn.next.right.add ((hr.comp (Kn.first.tuple Kn.next.left)).times
                 (Kn.cap (hg.comp Kn.first) (hf.comp Kn.first) Kn.next.left)))
              hk (Kn.fix 0) hg (by
           intro x a j hi; rw [← he x a j hi,hz]
           exact (under (fun k h=> hh x a k)).le.trans (Nat.pow_le_pow_right (by have:=hs x a; omega) hi))
    convert hu using 1
    ext x a
    exact he x a _ le_rfl

lemma mixK (b:Bool ) (h:Kn p ) (e:Kn v ) (f:Kn u):Kn (fun x a=> (toR p x a).mix b (v x a ) (u x a)):=by
   let m:PT α ℕ:=fun x a=>(toR p x a).M
   have hs:Kn m:=mFun h
   refine drew (fun x (w:α×ℕ)=> let a:=w.1; shove (m x a) b (dig (m x a) (v x a) w.2) (dig (toR p x a).n (u x a) w.2))
                ?_ hs (lFun h) (fFun h) (fun _ _=>rfl) (fun x a=>(Nat.le_trans (by omega) (M4 (toR p x a))))
      (fun x a j=>enoughS _ (lt_of_lt_of_le (by omega) (M4 (toR p x a))))
   exact shoveK b (hs.comp Kn.first)
       (digK (hs.comp Kn.first) (e.comp Kn.first) Kn.next)
       (digK ((nFun h).comp Kn.first) (f.comp Kn.first) Kn.next)
lemma glazeK {a:PT α Pane}(h:Kn p ) (e:Kn a ) (f:Kn u): Kn (fun x i=> (toR p x i).glaze (a x i ) (u x i)):=by
   have hf:=e.right.left; have he:= e.right.right
   let r (x i):=dig (toR p x i).n ((a x i).2.1) (u x i)
   have hr:Kn r:=digK (nFun h) hf f
   apply Kn.tuple e.left
   apply hf.tuple
   refine drew (fun x (w:α×ℕ)=> foil (a x w.1).2.2 (r x w.1) w.2)
                ?_ (Kn.fix 2) (nFun h) (qFun h) (fun _ _=>rfl)
          (fun _ _=>by omega) (fun x i j=>foil_lt ..)
   have hz := digK (Kn.fix 2) (he.comp Kn.first) Kn.next
   exact Kn.next.cond_eq (hr.comp Kn.first) ((Kn.fix _).sub hz) hz
lemma askK {a:PT α Pane}(h:Kn p ) (e:Kn a ) (f:Kn u): Kn (fun x i=> (toR p x i).ask (a x i ) (u x i)) :=
   (digK (Kn.fix 2) e.right.right (digK (nFun h) e.right.left f)).eq (Kn.fix 1)

lemma sumFun {n t:PT α ℕ} (hn:Kn n ) (hr:Kn t ) (f:PT (α×ℕ) ℕ ) (hf:Kn f)
    (hz:∀ x a j, f x (a,j)≤ t x a) :
     Kn (fun x a=> ∑ j∈range (n x a), f x (a,j)):=by
    let g:PT (α×ℕ×ℕ) ℕ:=fun x a=>a.2.2+ f x (a.1,a.2.1)
    have hs(x a j) : forNat (fun i v=>g x (a,i,v)) 0 j=∑ i∈range j,f x (a,i):=by
       induction j <;> simp_all only [forNat,sum_range_succ,g] ; simp
    simpa only [hs] using Kn.stroll g n (fun _ _=>0) (fun x a=> n x a*t x a)
             (Kn.next.right.add (hf.comp (Kn.first.tuple Kn.next.left))) hn (Kn.fix 0) (hn.times hr) (by
          intro x a i hi
          rw [hs]
          have he: ∑ j∈range i,f x (a,j)≤ ∑ _∈range i,t x a:=sum_le_sum fun j _=> hz x a j
          apply he.trans
          simpa using Nat.mul_le_mul_right (t x a) hi)
lemma shadeSumK {f g: PT α ℕ}(hf:Kn f ) (hg:Kn g)
    (he:∀ x a,1≤f x a∧1≤g x a ) (h:Kn p ) (hz:Kn v ) (hm:Kn u):
   Kn (fun x a=>∑ i∈range ((toR p x a).L),
                dig (f x a) (v x a) i * dig (g x a) (u x a) i):=
   sumFun (lFun h) (hf.times hg) _
          ((digK (hf.comp Kn.first ) (hz.comp Kn.first) Kn.next).times
                  (digK (hg.comp Kn.first ) (hm.comp Kn.first) Kn.next))
          (fun x a _=> Nat.mul_le_mul (Nat.mod_lt _ (he x a).1).le (Nat.mod_lt _ (he x a).2).le)
lemma hingeK (h:Kn p ) (hz:Kn v ) (hm:Kn u): Kn (fun x a=> (toR p x a).hinge (v x a ) (u x a)) :=
    shadeSumK (nFun h) (nFun h) (fun x a=>by have:= n2 (toR p x a); exact ⟨by omega,by omega⟩) h hz hm
lemma aloK (h:Kn p ) (hz:Kn v ) (hm:Kn u): Kn (fun x a=> (toR p x a).aloft (v x a ) (u x a)) :=
    shadeSumK (mFun h) (nFun h)
           (fun x a=>⟨Nat.le_trans (by omega) (M4 _), Nat.le_trans (by omega) (n2 _)⟩) h hz hm
lemma firstK (b:Bool ) (h:Kn p) (hs:Kn v) {g:PT α Pane} (he:Kn g):
   Kn (fun x a=> (toR p x a).first b (v x a) (g x a)) :=
    (mixK b h he.left hs).tuple ((shoveK b (mFun h) he.right.left (hingeK h hs hs)).tuple he.right.right)
lemma upzK (b:Bool ) (h:Kn p) (hs:Kn v) {g:PT α Pane} (he:Kn g):
   Kn (fun x a=> (toR p x a).pointZ b (v x a) (g x a)) :=
       he.left.tuple ((shoveK b (mFun h) he.right.left ((Kn.fix 2).times (aloK h he.left hs))).tuple
                           he.right.right)
lemma svK (b:Bool ) (h:Kn p) (hs:Kn v) {g:PT α Pane} (he:Kn g):
   Kn (fun x a=> (toR p x a).pointR b (v x a) (g x a)) :=
          (mixK (!b) h he.left hs).tuple he.right
lemma secondK (b:Bool ) (h:Kn p) (hs:Kn v) {g:PT α Pane} (he:Kn g):
   Kn (fun x a=> (toR p x a).second b (v x a) (g x a)) :=
      he.left.tuple ((shoveK (!b) (mFun h) (shoveK b (mFun h) he.right.left (hingeK h hs hs))
                              ((Kn.fix 2).times (aloK h he.left hs))).tuple he.right.right)

end Rod
end ExactDerandomization.Glass

end

section

namespace ExactDerandomization.Glass
open Relay Counter NatD Rod

abbrev Foot:=ℕ×Pane

inductive Mode where
  | push | step2 | ret | dial
  deriving DecidableEq
def pivot: Mode→Bool
  | .push| .ret=>true
  | _=>false
def pigment (p:Rod) : Mode→ Bool→ℕ→Pane→Pane
   | .push=>p.first
   | .step2=>p.second
   | .ret=>p.pointR
   | .dial=>p.pointZ

structure Eye where
    peak:Cub ℕ ℕ
    visit : Mode→Bool → Cog

namespace Eye
variable (p:Eye)
def eye (_:Word)(a:Plot):Foot:= dec a.2.2
def peg (x:Word)(a:Plot):Rod:=⟨p.peak.f x a.1⟩
def flip (k:ℕ)(x:Word)(a:Plot):Site :=
    let u:=eye x a
    (0,enc ((u.1,(p.peg x a).glaze u.2 k):Foot))
lemma flipK (k):Kn (p.flip k):=by
    have he:= p.peak.runs.comp (Kn.first (β:=Site))
    have hc:= (Kn.unpack (α:=Foot)).comp (Kn.next (α:=ℕ) (β:=Site)).right
    exact (Kn.fix _).tuple (Kn.wash.comp (hc.left.tuple (glazeK he hc.right (Kn.fix _))))
def glare (k:ℕ)(x:Word)(a:Plot):Bool:= (p.peg x a).ask (eye x a).2 k
lemma glareK (k):Kn (p.glare k):=
    askK (p.peak.runs.comp Kn.first) ((Kn.unpack (α:=Foot)).comp Kn.next.right).right (Kn.fix _)
def fairp (p:Eye)(c:Cog):Cog :=
   .seq (p.visit .push true) (.seq (p.visit .step2 true) (.seq (p.visit .ret true)
         (.seq (p.visit .dial true) c)))
def fairm (p:Eye)(c:Cog):Cog :=
   .seq (p.visit .dial false) (.seq (p.visit .ret false) (.seq (p.visit .step2 false)
           (.seq (p.visit .push false) c)))
def Glare (p:Eye)(k:ℕ):Flag:=⟨_,p.glareK k⟩
def Toggle (p:Eye)(k:ℕ):Cog:= .edit ⟨_,p.flipK k⟩
def after (p:Eye)(k:ℕ)(b:Bool)(yes no: Cog):Cog:=
    .seq (.edit ⟨_,Kn.next⟩)
     (p.fairm (.seq (p.Toggle k) (p.fairp (.bif (p.Glare k)
                        (p.fairm (if b then no else yes))
                        (p.fairm (if b then yes else no))))))
def block (p:Eye) (k:ℕ)(yes no:Cog):Cog:=
    .seq (p.Toggle k) (p.fairp (.bif (p.Glare k) (p.after k true yes no) (p.after k false yes no)))
def nexts (p:Eye) : ℕ→ Cog→ Cog→ Cog
   | 0,y,_=>y
   | k+1,y,n=>p.block k (p.nexts k y n) n

structure Mantle where
   l : Lot
   q :ℕ
   v :Level
   k:ℕ
   d:ℕ
   id:ℕ
namespace Mantle
variable (m:Mantle)
abbrev param:Rod:=⟨p.peak.f m.l.x m.q⟩
abbrev knot (v:Pane):Site:=(0,enc ((m.id,v):Foot))
abbrev wants : Cog→Site→Site→ Prop:= Lot.Mane m.l m.k m.v m.d m.q
end Mantle

structure Twirl (p:Eye)(m:Mantle)(x y:ℕ):Prop where
    walk : ∀ v,(Mantle.param p m).proper v → ∀ M b,
               m.wants (p.visit M b) (m.knot v) (m.knot
                  (pigment (Mantle.param p m) M b (if pivot M then x else y) v))

namespace Twirl
variable {p m x y} (h:p.Twirl m x y)
include h
private abbrev rod (p:Eye)(m:Mantle):Rod:=Mantle.param p m
lemma idol (v)(hv:(rod p m).proper v):m.l.state m.k m.v (m.knot v):= (h.walk v hv .push true).spots.1
lemma tint {v}(k)(hv:(rod p m).proper v):
    m.wants (p.Toggle k) (m.knot v) (m.knot ((rod p m).glaze v k)):=
   .edit (by simp [flip,eye,Mantle.knot]; rfl)
             (h.idol v hv) (h.idol _ ((rod p m).glaze2 k hv).1)
omit h in
lemma looked (v k): (p.Glare k).f m.l.x (m.q,m.knot v)=(rod p m).ask v k:=by
    simp [Glare,glare,eye,Mantle.knot]; rfl
lemma furl {v}(hv:(rod p m).proper v){c u}
    (hc:m.wants c (m.knot ((rod p m).fair x y v)) u):
    m.wants (p.fairp c) (m.knot v) u:=by
    let r:=rod p m
    let f:=r.first true x v; let g:=r.second true y f
    have he1:r.proper f:=(r.stay true x hv).1
    have he2:r.proper g:=(r.stay true y he1).2.1
    exact .seq (h.walk v hv .push true) (.seq (h.walk _ he1 .step2 true)
      (.seq (h.walk _ he2 .ret true) (.seq (h.walk _ (r.stay true x he2).2.2.1 .dial true) hc)))
lemma moot {v}(hv:(rod p m).proper v){c u}(hc:m.wants c (m.knot v) u):
    m.wants (p.fairm c) (m.knot ((rod p m).fair x y v)) u:=by
    let r:=rod p m
    let w:=r.fair x y v
    let f:=r.pointZ false y w
    let g:=r.pointR false x f
    have h0:r.proper w:=r.sepia x y hv
    have h1:r.proper f:=(r.stay false y h0).2.2.2
    have h2:r.proper g:=(r.stay false x h1).2.2.1
    have ht:m.wants c (m.knot (r.dark x y w)) u:= by rwa [r.back x y hv]
    exact .seq (h.walk w h0 .dial false) (.seq (h.walk _ h1 .ret false)
          (.seq (h.walk _ h2 .step2 false) (.seq (h.walk _ (r.stay false y h2).2.1 .push false) ht)))

lemma retina {v} (hv:(rod p m).proper v)(k){b y1 n c}
    (_:(rod p m).ask ((rod p m).fair x y ((rod p m).glaze v k)) k=b)
    (h1:b≠ (rod p m).ask ((rod p m).fair x y v) k → m.wants y1 (m.knot v) c)
    (h0:b= (rod p m).ask ((rod p m).fair x y v) k → m.wants n (m.knot v) c):
    m.wants (p.after k b y1 n) (m.knot ((rod p m).fair x y ((rod p m).glaze v k))) c:=by
   let r:=rod p m
   have hp:=(rod p m).glaze2 k hv
   have heo:=h.idol _ (r.sepia x y hp.1)
   have hz:=h.tint k hp.1
   rw [hp.2] at hz
   refine .seq (.edit rfl heo heo) (h.moot hp.1 (.seq hz (h.furl hv ?_)))
   cases he0:r.ask (r.fair x y v) k
   · apply Lot.Mane.no ((looked (p := p) (m := m) (r.fair x y v) k).trans he0)
     apply h.moot hv
     split
     · next e=> apply h1; change b≠r.ask (r.fair x y v) k; grind
     · next e=> apply h0; change b=r.ask (r.fair x y v) k; grind
   apply Lot.Mane.yes ((looked (p := p) (m := m) (r.fair x y v) k).trans he0)
   apply h.moot hv
   split
   · next e=> apply h0; change b=r.ask (r.fair x y v) k; grind
   · next e=> apply h1; change b≠r.ask (r.fair x y v) k; grind

abbrev condH (r:Rod)(x y i:ℕ)(v:Pane):Prop:=
    r.ask (r.fair x y (r.glaze v i)) i≠r.ask (r.fair x y v) i
lemma rosette {v} (hv:(rod p m).proper v)(k){y1 n c}
    (hp:condH (rod p m) x y k v → m.wants y1 (m.knot v) c)
    (he:¬condH (rod p m) x y k v → m.wants n (m.knot v) c):
    m.wants (p.block k y1 n) (m.knot v) c:=by
    apply Lot.Mane.seq (h.tint k hv)
    apply h.furl ((rod p m).glaze2 k hv).1
    let r:=rod p m
    let z:=r.fair x y (r.glaze v k)
    have hm(b:Bool)(hb:r.ask z k=b): m.wants (p.after k b y1 n) (m.knot z) c := by
       apply h.retina hv k hb
       · intro hs; rw [←hb] at hs; exact hp hs
       intro hs
       apply he; intro hf
       change r.ask z k≠_ at hf
       exact hf (hb.trans hs)
    cases e : r.ask z k
    · exact .no (((looked (p := p) (m := m)) z k).trans e) (hm _ e)
    · exact .yes (((looked (p := p) (m := m)) z k).trans e) (hm _ e)
lemma blocks {v} (hv:(rod p m).proper v)(k){y1 n c}
    (hp:(∀ i<k,condH (rod p m) x y i v) → m.wants y1 (m.knot v) c)
    (he:(∃ i<k,¬condH (rod p m) x y i v) → m.wants n (m.knot v) c):
    m.wants (p.nexts k y1 n) (m.knot v) c:=by
   induction k with
   | zero=> exact hp (by omega)
   | succ k ih=>
     apply h.rosette hv k
     · intro hb
       refine ih (fun e=>hp ?_) ?_
       · intro i hi; rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with hs|hg
         · rw [hs]; exact hb
         exact e _ hg
       · rintro ⟨i,hi,e⟩; exact he ⟨i,by omega,e⟩
     intro hb; exact he ⟨k,by omega,hb⟩
theorem done0 {v}(hv:(Mantle.param p m).proper v){y1 n c}
    (hx:x≤(Mantle.param p m).peak)(hy:y≤(Mantle.param p m).peak)
    (hp:x=y → m.wants y1 (m.knot v) c)(he:x≠y → m.wants n (m.knot v) c):
    m.wants (p.nexts 4 y1 n) (m.knot v) c:=by
   have hs := (rod p m).learned x y hx hy hv
   apply h.blocks hv 4 (fun hh=>hp (hs.2 hh))
   rintro ⟨i,hi,hv⟩
   exact he fun h=> hv (hs.1 h i hi)

end Twirl
end Eye
end ExactDerandomization.Glass

end

section

namespace ExactDerandomization.Glass
open Relay Counter

/-- A visit whose (single) optional subterminal path is delegated.
The hop tokens forward/back are determined by the selector's code,
which belongs to a short range. Its pure action compiled at leaves
can incorporate post label maps. -/
structure Vase where
    ask:Cub ℕ ℕ
    probe:Bool→ Cub Slip ℕ
    dives:Cub Slip Bool
    bud:Cub Slip ℕ
    next:Cub Plot Site

namespace Vase
variable (v:Vase)
def start :Cog:=.toss ⟨fun x a=>v.ask.f x a.1,v.ask.runs.comp Kn.first⟩
                           ⟨_,Kn.next⟩
def fork :Flag:=⟨fun x a=>v.dives.f x (a.1,a.2.1),v.dives.runs.comp (Kn.first.tuple Kn.next.left)⟩
def ahead : Cog := .toss (v.probe true)
               ⟨fun _ a=>(a.1.2,a.2.2), Kn.first.right.tuple Kn.next.right⟩
abbrev Belt:=ℕ×ℕ
def budfeed (_:Word) (a:Drain):Site := (enc ((a.1.2,a.2.1):Belt),a.2.2)
lemma budK:Kn budfeed:=(Kn.wash.comp (Kn.first.right.tuple Kn.next.left)).tuple Kn.next.right
def seed (x:Word ) (a:Plot):Site:=
   budfeed x ((a.1,a.2.1),v.next.f x a)
lemma seedK:Kn v.seed:=budK.comp ((Kn.first.tuple Kn.next.left).tuple v.next.runs)
def lance: Cog:= .bif v.fork (.toss v.bud ⟨_,budK⟩) (.edit ⟨_,v.seedK⟩)
def headQ (x:Word ) (a:Slip):ℕ:=(v.probe false).f x (a.1,(dec a.2:Belt).1)
def lastQ (_:Word ) (a:Drain):Site:= ((dec a.1.2:Belt).2,a.2.2)
lemma headK:Kn v.headQ:= (v.probe false).runs.comp
                           (Kn.first.tuple ((Kn.unpack (α:=Belt)).comp Kn.next).left)
lemma lastK:Kn lastQ := (((Kn.unpack (α:=Belt)).comp Kn.first.right).right).tuple Kn.next.right
def dawn: Cog:=.seq v.ahead (.seq v.lance (.toss ⟨_,v.headK⟩ ⟨_,lastK⟩))
def cold0:Cub Plot Bool:=⟨fun _ a=> decide (a.2.1=0), Kn.next.left.eq (Kn.fix 0)⟩
def play:Cog:=.seq v.start (.bif cold0 (.edit ⟨_,Kn.next⟩) v.dawn)

structure Den where
   l:Lot
   w:ℕ
   d:ℕ
   q:ℕ
   k:ℕ
namespace Den
variable (a:Den)
abbrev charge:=10*a.k
def good:= 4 ≤ a.k∧1 ≤ a.d∧ a.d ≤ a.w
def pull (q:ℕ):= (a.l.book q).w + a.d ≤ a.w ∧ (a.l.book q).t=0
abbrev rootD(a:Den):Level:=⟨a.w,0⟩
abbrev meets:=Lot.Mane a.l a.charge a.rootD a.d a.q
def bit (z:ℕ):=lb z ≤ a.k*a.d
abbrev atCall (q h:ℕ ) (u:Site) := Boots a.l.x a.l.F a.l.P q a.l.P (0,h) u
lemma affordable {h}(hk:a.good ) (ht:lb h ≤ 6*a.k*a.d)
    (i ) (e:i ≤ a.l.F.limit):a.l.state a.charge a.rootD (h,i):=by
   obtain ⟨p,g,f⟩:=hk
   refine ⟨e,?_⟩; unfold span; dsimp only [rootD,charge]
   nlinarith [Nat.mul_le_mul_left a.k f, show 6*a.k ≤10*a.k by omega,
           Nat.mul_le_mul_left (10*a.k*(10*a.k)) f]
lemma fit {q z}(hk:a.good ) (ht:lb z  ≤ 6*a.k*a.d ) (h:a.pull q):
     a.l.jump a.charge a.rootD a.d z q:=by
   obtain ⟨h1,h2,h3⟩:=hk; obtain ⟨ha,hb⟩:=h
   refine ⟨ha,?_⟩; change span _ (a.w-_) 0 _ _
   rw [hb]; unfold span; dsimp only [charge]
   have hw:a.d ≤ a.w-(a.l.book q).w:=by omega
   nlinarith [Nat.mul_le_mul_left (10*a.k*(10*a.k)) hw]
lemma sizeQ {x}(_:a.good ) (ht:a.bit x):lb x ≤ 6*a.k*a.d:=by unfold bit at ht; nlinarith
lemma bsize {x y:ℕ}(h:a.good ) (ht:a.bit x ) (hz:a.bit y):lb (enc ((x,y):Belt))  ≤ 6*a.k*a.d:=by
   have he : lb (enc (x,y))≤2*lb x+lb y+2:=measure_pair _ _
   unfold bit at *; obtain ⟨hx,hv,ht'⟩:=h
   nlinarith
lemma bit0 (h:a.good): a.bit 0:= by unfold bit; rw [lb_zero]; obtain ⟨hv,hx,hc⟩:=h; nlinarith
end Den

lemma perform {s:Den} (h:s.good ) (x h0:ℕ) (hc:s.bit h0)
    (he:s.pull (v.ask.f s.l.x s.q))
    (hy:s.atCall (v.ask.f s.l.x s.q) x (h0,x)):
    s.meets v.start (0,x) (h0,x):=
   let ht:=hy.fits.2.2.1
   .toss rfl rfl (s.affordable h (s.sizeQ h (s.bit0 h)) _ ht)
      (s.affordable h (s.sizeQ h hc) _ ht) (s.fit h (s.sizeQ h (s.bit0 h)) he) hy

lemma arrives {s:Den} (h:s.good){x y h0 w z i:ℕ} (ht:s.bit h0 ) (hb:s.bit i)
   (hs:s.meets v.start (0,x ) (h0,x) ) (he:h0 ≠0)
   (hf:∀ b,s.pull ((v.probe b).f s.l.x (s.q,h0)))
   (hp:s.atCall ((v.probe true).f s.l.x (s.q,h0)) x (1,y))
   (hg:s.atCall ((v.probe false).f s.l.x (s.q,h0)) z (1,w))
   (hE:v.dives.f s.l.x (s.q,h0)=true →
                s.pull (v.bud.f s.l.x (s.q,h0)) ∧ s.atCall (v.bud.f s.l.x (s.q,h0)) y (i,z))
   (hD:v.dives.f s.l.x (s.q,h0)=false → v.next.f s.l.x (s.q,h0,y)=(i,z)):
    s.meets v.play (0,x) (i,w):=by
   have hx:=s.sizeQ h ht; have hi:=s.bsize h ht hb
   have hu:=s.affordable h hx y hp.fits.2.2.1
   have hA:=s.affordable h hi z hg.fits.1.2.1
   have h1:s.meets v.ahead (h0,x ) (h0,y) :=
                 .toss rfl rfl hs.spots.2 hu (s.fit h hx (hf true)) hp
   have h2: s.meets v.lance (h0,y) (enc (h0,i),z):=by
      cases he:v.dives.f s.l.x (s.q,h0)
      · apply Lot.Mane.no he
        apply Lot.Mane.edit ?_ hu hA
        change v.seed _ _=_; unfold seed budfeed; dsimp only
        rw [hD he]
      · obtain ⟨hf,hp⟩:= hE he
        exact .yes he (.toss rfl rfl hu hA (s.fit h hx hf) hp)
   apply Lot.Mane.seq hs
   apply Lot.Mane.no (show decide (h0=0)=false by simp [he])
   refine .seq h1 (.seq h2 (.toss ?_ ?_ hA (s.affordable h (s.sizeQ h hb) _ hg.fits.2.2.1)
                       (s.fit h hi (hf false)) hg))
   · change v.headQ ..=_; simp [headQ]
   · change lastQ s.l.x _=_; simp [lastQ]

lemma failed {s:Den} {x} (hv:s.meets v.start (0,x ) (0,x)):
   s.meets v.play (0,x ) (0,x):= .seq hv (.yes rfl (.edit rfl hv.spots.2 hv.spots.2))

end Vase
end ExactDerandomization.Glass

end

end OAI
