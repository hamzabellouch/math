import OAI.Computability.Logspace.ConfigurationEvaluation
import OAI.Computability.Logspace.RowEvaluation

namespace OAI

/-!
Correctness of the numerical row-compression evaluation.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Aurora
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est
noncomputable section
open scoped Classical

/-- Arithmetic library with distinguished variable leaves -/
inductive Folk where
    | var (i:ℕ)
    | pin (a:ℕ)
    | play (p:Doop)(a b:Folk)
namespace Folk

def bind (f:ℕ → Lyric) :Folk → Lyric
    | var i => f i
    | pin a=>kohn a
    | play p a b=>bi p (bind f a) (bind f b)
def meanF (f:Folk)(a:ℕ→ℝ):ℝ:=match f with
    | var i=> a i
    | pin x=> x
    | play p b c=>p.val (b.meanF a) (c.meanF a)
lemma time (p:Folk){c T I S f A}(hS:Lu.Standard S I T)(h:∀ i:ℕ,Chor I c T S (f i) (A i)):
    Chor I c T S (bind f p) (meanF p A):=by
    induction p with
    | var i=>exact h i
    | pin a=>exact hS.rove _ _
    | play p a b i j=> exact Chor.minuet i j hS.st _
open Cambria.Wear.Paper in
lemma stamina (p:Folk){f g}(h:∀ i:ℕ,same (f i) (g i)): same (p.bind f) (p.bind g):=by
    induction p with
    | var i=>exact h i
    | pin a=> exact oneself _
    | play p x y e k=> exact same.plies e k _

abbrev sum := play .plus
abbrev diff := play .minus
abbrev times := play .prod
abbrev join := play .greater
abbrev meet := play .lesser
abbrev flop (p:Folk) := play .flip p (pin 1)
abbrev price (x:ℕ) := flop (pin x)
@[simp] lemma val0 (a v):meanF (pin a) v=a:=rfl
@[simp] lemma val1 (a b v):meanF (sum a b) v=a.meanF v+b.meanF v:=rfl
@[simp] lemma val2 (a b v):meanF (Folk.diff a b) v=a.meanF v-b.meanF v:=rfl
@[simp] lemma val3 (a b v):meanF (Folk.times a b) v =a.meanF v*b.meanF v:=rfl
@[simp] lemma val4 (a b v):meanF (join a b) v =max (a.meanF v) (b.meanF v):=rfl
@[simp] lemma val5 (a b v):meanF (meet a b) v =min (a.meanF v) (b.meanF v):=rfl
@[simp] lemma outV (a v):meanF (var a) v=v a:=rfl
lemma val6 (a v) : meanF (flop a) v=(max (a.meanF v) 1)⁻¹:=rfl
lemma borne (i:ℕ)(v)(h:0 < i): meanF (price i) v=1/(i:ℝ):=by
    rw [val6,val0,max_eq_left];simp; exact_mod_cast h

/- Surface p(x,y). -/
abbrev lo(a b x :Folk):=meet b (join a x)
abbrev tick (p:Folk):= lo (pin 0) (pin 1) p
abbrev power4(p:Folk): Folk:=let i:=Folk.times p p; Folk.times i i
def heaven(p:Folk):Folk:=power4 (tick (Folk.times (pin 2) p))
def sweetF(p:Folk):Folk:=
    Folk.times (price 2) (sum (heaven p) (Folk.diff (pin 1) (heaven (Folk.diff (pin 1) p))))
@[simp] lemma lowF(a b x v):meanF (lo a b x) v=clip (meanF a v) (meanF b v) (meanF x v):=rfl
lemma ticking(a v):meanF (tick a) v=smooth (a.meanF v):=by simp [smooth]
lemma powering(a v): meanF (power4 a) v = a.meanF v^4:=by
    unfold power4; dsimp only
    rw [val3,val3];ring
lemma art(a v):meanF (heaven a) v = smooth (2*a.meanF v)^4:=by
    unfold heaven; rw [powering,ticking,val3,val0]; norm_num
lemma sweetness(a v):meanF (sweetF a) v=fade (a.meanF v):=by
   unfold sweetF; rw [val3,val1,val2,borne 2 _ (by omega),art,art,val2,val0]; norm_num [fade];ring

abbrev powerZ :=4096*400*1000000*1000
abbrev az:=4096
abbrev az2:=4096*400
def climate (t:ℕ)(p:Folk):Folk :=
   sweetF (Folk.diff (Folk.times (pin t) p) (pin 1))
lemma town(t:ℕ)(p:Folk)(v)(h:0<t): meanF (climate t p) v=rising (1/(t:ℝ)) (2/t) (p.meanF v):=by
    unfold climate; rw [sweetness,val2,val3,val0,val0]
    unfold rising; norm_num
    congr 1
    field_simp ; ring
def vacation(p:Folk):Folk:=
    let M:=powerZ
    let r:= price M
    let v:= Folk.times (pin M) (lo (price (M*2)) r p)
    Folk.times (pin 2) (flop (Folk.times (pin 2) v))
lemma zoo : 1/(powerZ:ℝ)=zeta:=by norm_num [powerZ,zeta,At.small,Hie.delta,Hie.A]
lemma azone:1/(az:ℝ)=Hie.A:=rfl
lemma azto:1/(az2:ℝ)=delta:=by norm_num [az2,delta,Hie.A]
lemma homes(p v): (vacation p).meanF v= At.divisor (p.meanF v):=by
   let M:=powerZ
   let r:=Folk.times (pin M) (lo (price (M*2)) (price M) p)
   let x:=p.meanF v
   have he0 :0<M:=by unfold M powerZ; omega
   have hp: r.meanF v=den x:=by
       unfold r; rw [val3,val0,lowF,borne M _ he0,borne (M*2) _ (by omega)]
       have hk:1/(M:ℝ)=zeta:= zoo
       have hv:1/(((M*2:ℕ):ℝ))=zeta/2:=by rw [←hk]; push_cast; ring
       rw [hk,hv]; unfold den; rw [div_eq_mul_inv]
       rw [mul_comm]; rw [show ↑M= zeta⁻¹ by rw [←hk];simp]
       unfold x; rw [div_eq_mul_inv]
   unfold vacation; change (Folk.times _ (flop (Folk.times (pin 2) r))).meanF v=(den x)⁻¹
   rw [val3,val6,val3,hp,val0]
   have hh:= within_den x; norm_num
   rw [max_eq_left (by linarith :1 ≤ 2*den x)]
   ring_nf
def gourd(n:ℕ)(p x:Folk) :Folk:=Folk.times p (Folk.diff (pin 1) (climate (n*1000) x))
lemma tract {n:ℕ}(hn:0<n)(z:ℝ)(he:1/(n:ℝ)=z)(p x v):
   (gourd n p x).meanF v=p.meanF v*gate z (x.meanF v):=by
    unfold gourd; rw [val3,val2,val0,town _ _ _ (by omega)]
    unfold gate eta; rw [←he];push_cast;ring_nf

abbrev fever(P:Const):Folk:=pin (P.T+32)
def localq (P:Const)(x:Folk): Folk:=
    let k:=lo (pin 0) (fever P) x
    let h:=Folk.diff k (price az)
    sum (Folk.times (price az) (power4 (tick (Folk.times (pin az) h))))
             (join (pin 0) (Folk.diff h (price az)))
lemma feved(P:Const)(v):(fever P).meanF v=cap P:=by unfold fever cap; simp
lemma correctq(P:Const)(x v):(localq P x).meanF v=Qc P (x.meanF v):=by
   unfold localq; dsimp only
   rw [val1,val4,val2,val2,val3,powering,ticking,val3,lowF,feved,borne _ _ (by decide)]
   simp only [azone,val0,Nat.cast_zero,Hie.Q,Qc,Analysis.shoulder,az,Hie.A]
   norm_num; ring_nf
   rw [borne _ _ (by omega)]; norm_num [clip,cap];ring_nf

def sliceF (M i:ℕ)(p:Folk) :Folk:=
   let f:=climate 128 p
   sum (if i=0 then Folk.diff (pin 1) f else pin 0) (Folk.times f (price M))
lemma pairS {M:ℕ}(h:0<M)(i p v):(sliceF M i p).meanF v=share M i (p.meanF v):=by
    unfold sliceF share; dsimp only; rw [val1,val3,town _ _ _ (by decide),borne M _ h]
    split <;> first
    | rw [val2,val0,town _ _ _ (by decide)]; unfold slice; norm_num [bound0,bound1]; ring_nf
    | rw [val0]; unfold slice; norm_num [bound0,bound1];ring_nf
def binC(P:Const)(zero0:Bool)(j:Option ℕ)(w x:Folk):Folk:=
    let a:=lo (price 2) (fever P) x
    let h:=if zero0 then pin 1 else Folk.diff (pin 1) (climate 2 (Folk.times (price 16) a))
    let z:= Folk.times (climate 2 a) h
    let s:=match j with |none=>pin 1|some i=>sliceF P.M i (Folk.times w a)
    Folk.times (Folk.times a z) s
lemma excel (P:Const)(k l:ℕ)(j:Option ℕ)(w x v)(he:w.meanF v=rate k/rate l):
   (binC P (decide (k=0)) j w x).meanF v=bfrag P k l j (x.meanF v):=by
    unfold binC; dsimp only
    let p:= lo (price 2) (fever P) x
    have hp : p.meanF v=tone P (x.meanF v):=by unfold p; rw [lowF, feved,borne _ _ (by omega)];rfl
    have hh(x:Folk): (climate 2 x).meanF v=cut (x.meanF v):=by rw [town _ _ _ (by omega)]; unfold cut;norm_num
    rw [val3,val3,show meanF (lo _ _ _) v=_ from hp, val3,hh, hp]
    let y:= tone P (x.meanF v)
    have hu :(if decide (k=0) then pin 1 else Folk.diff (pin 1) (climate 2 (Folk.times (price 16) p))).meanF v=
            highcut k y:=by
        simp only [decide_eq_true_eq]; unfold highcut; split
        · simp only [val0,Nat.cast_one]
        rw [val2,val0,hh,val3,hp,borne _ _ (by omega)]; unfold y;norm_num;ring_nf
    unfold bfrag sw
    rw [hu]
    congr 1
    cases j
    · simp [dirShare]
    next j=>
       have hz:=P.mOK; simp only [dirShare]; erw [pairS (show 0<P.M by omega)]; rw [val3,hp,he]

end Folk
end
end ExactDerandomization.Aurora

end

section

namespace ExactDerandomization.Aurora
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
noncomputable section
open scoped Classical
structure Nick where
      king:Kind
      main:Bool
      ground:Bool
      deriving DecidableEq
namespace Nick
variable (p:Nick)
abbrev green(q:Quest):Nick:=⟨q.tag,q.main,decide (q.a=0)⟩
open Folk
def mainC (p:Nick) := (p.main && p.king.paired)
def toastC(p:Nick) : ℕ:=match p.king with
    | .chip | .slot _=>2
    | .echo ..=>Folk.az
    | .score ..=>Folk.az2
lemma realC : 1/(p.toastC:ℝ)=p.king.theta:=by
    cases h:p.king
    · simp [toastC,h,Kind.theta]
    · simp [toastC,h,Kind.theta]
    · simp [toastC,h,Kind.theta]
    norm_num [toastC,h,Kind.theta,delta,Hie.A]
lemma realD : 0<p.toastC:=by cases h:p.king <;> norm_num [toastC,h,Folk.az,Folk.az2]

def league(P:Const)(x:Folk) : Folk:=
    if p.main then
       match p.king with
       | .chip=> Folk.binC P p.ground none (var 3) x
       | .slot i =>Folk.binC P p.ground (some i) (var 3) x
       | .echo ..=>Folk.localq P x
       | .score ..=>climate Folk.az2 x
    else Folk.sweetF (Folk.diff (Folk.times (pin (4*p.toastC)) x) (pin 2))
def humor : Folk:=
    let n:= p.toastC
    Folk.gourd n (pin 1) (var 1)
def factorR(P:Const):Folk:=
    Folk.times (Folk.times (p.league P (var 0)) p.humor)
           (if p.mainC then Folk.vacation (var 2) else pin 1)
def witness(p:Nick) : Folk:=
    Folk.times (sweetF (Folk.diff (Folk.times (pin (12*p.toastC)) (var 0)) (pin 3)))
               (Folk.diff (pin 1) (Folk.climate (200*p.toastC) (var 1)))
def temple(P:Const) (b:Bool):Folk:= if b then p.witness else p.factorR P

variable {n:ℕ} [Fact n.Prime]
lemma fareC {s:Scene n} {q:Quest}(h:p=green q) (x:ℕ → ℝ)(he:x 3 = rate q.a/rate q.i):
    Folk.meanF (p.league s.P (var 0)) x = q.phi s (x 0) := by
   let y:= p.toastC; have hi:(0:ℝ)<y:=by exact_mod_cast p.realD
   have hg:1/(p.toastC:ℝ)=q.tag.theta:=by rw [p.realC,h]
   have hk := Folk.azto
   unfold league Quest.phi
   have hv:p.main=q.main:=by rw [h]
   rw [hv]
   by_cases ht : q.main=true
   · rw [ite_eq_left ht,ite_eq_left ht,h]
     rw [show (green q).king=q.tag from rfl]
     cases hl:q.tag
     · exact Folk.excel s.P q.a q.i none (var 3) (var 0) x he
     · next i=> exact Folk.excel s.P q.a q.i (some i) (var 3) (var 0) x he
     · next b i=> exact Folk.correctq s.P (var 0) x
     change (Folk.climate Folk.az2 (var 0)).meanF x = light _
     rw [Folk.town _ _ _ (by decide),hk]; unfold light; rw [← hk]
     congr 1 ; first|rfl|norm_num [Folk.az2]
   rw [ite_eq_right ht,ite_eq_right ht,Folk.sweetness,Folk.val2,Folk.val3,Folk.val0,Folk.val0,Folk.outV]
   unfold prep rising
   rw [←hg]
   change fade _ = _
   push_cast
   congr 1
   have hh : p.toastC = y:=rfl
   rw [hh];field_simp ; ring
lemma ten {s:Scene n}{q:Quest}(h:p=green q) (x:ℕ → ℝ)(he:x 3=rate q.a/rate q.i):
    Folk.meanF (p.factorR s.P) x = (q.trio s).eval (x 0) (x 1) (x 2):=by
   unfold factorR
   rw [Folk.val3,Folk.val3,p.fareC h x he]
   unfold humor; rw [Folk.tract p.realD _ p.realC,Folk.outV,Folk.val0]
   rw [Nat.cast_one,one_mul]
   have ht:p.mainC=q.two:=by rw [h];rfl
   rw [ht,h]
   cases h:q.two <;> simp [Quest.trio,h,Trio.eval,At.mainT,Folk.homes]
lemma many (x:ℕ → ℝ):
   Folk.meanF p.witness x = (suppT p.king.theta false).eval (x 0) (x 1) (x 2):=by
    unfold witness Trio.eval; rw [Folk.val3,Folk.sweetness]
    simp only [suppT,Bool.false_eq_true,ite_false,mul_one,Folk.val2,Folk.val3,Folk.outV,Folk.val0]
    rw [Folk.town _ _ _ (by have := p.realD; omega), ←p.realC,Folk.outV]
    congr 1
    · unfold rising; congr 1
      have hh: (0:ℝ)<p.toastC:= by exact_mod_cast p.realD
      push_cast; field_simp ; ring
    push_cast;ring_nf
end Nick
end
end ExactDerandomization.Aurora

end

section

namespace ExactDerandomization.Aurora
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Stem Spring
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Scroll
abbrev Profile:= (ℕ× ℕ)× Bool×Bool
def copyN(n:Nick):Profile:=(shaped n.king,n.main,n.ground)
def decodeP(n:Profile):Nick:=⟨aspect n.1,n.2.1,n.2.2⟩
lemma copyB (s:Nick):decodeP (copyN s)=s:=by cases s with
    | mk k b v=> cases k <;> first|rfl|  next z i=>cases z<;>rfl

abbrev ruler (w:Wares):ℕ:=5+w.p.T+w.p.M
def bankS(w:Wares):Finset Profile:=
    (((range (ruler w)) ×ˢ (range (ruler w)))×ˢ (univ ×ˢ univ))
lemma within {w:Wares}{q:Quest} (he:q.tag.sane w.p q.i q.a) :
    copyN (Nick.green q)∈bankS w:=by
   simp only [copyN, bankS, mem_product,mem_range,mem_univ, and_self, and_true]
   cases h:q.tag
   all_goals simp only [ruler,shaped]
   · omega
   all_goals rw [h] at he; unfold Kind.sane at he
   any_goals omega
   next b k=> cases b<;> dsimp only at * <;>omega
def checkN(c:Crt):Profile:=
   let s:=Age.styx c
   ((s.2.1,s.2.2.1),s.2.2.2,decide (s.1.2.2.1=0))
lemma checks(s:Quest)(v x j):checkN (kit v j (bitR s) x)=copyN (Nick.green s):=rfl
lemma checkedK {α}[Wire α]{f:PT α Crt} (h:Kn f):Kn (fun x a=>checkN (f x a)) :=
   let h:= h.right.right.left
   (h.right.left.tuple h.right.right.left).tuple (h.right.right.right.tuple
                                                   (h.left.right.right.left.eq (Kn.fix _)))
def book0(_:Word)(p:ℕ): Profile:= checkN (uphold (unitK p))
lemma earnK(p:Profile): Kn (fun x a=>decide (book0 x a=p)):=by
    have h:= checkedK ((Kn.unpack (α:=Crt)).comp unitK0)
    let h':=Kn.wash.comp h
    apply GK.decideK
    convert GK.eqG h' (Kn.fix (enc p)) using 1
    ext x a; exact ⟨fun h=>congrArg enc h,fun v=>(Wire.eq _).symm.trans ((congrArg dec v).trans (Wire.eq _))⟩
abbrev later (q:Profile):Flag:=⟨_,(earnK q).comp Kn.first⟩

end Scroll

namespace Fort
open Scroll
variable (r:Rock q w h)(p:MintV)

def sages(x:Word)(a:ℕ):Crt:=uphold (V x a).1
lemma sageK: Kn sages:=Kn.unpack.comp VK.left
def adj(x:Word)(a:ℕ):Coin :=
   let z:=(Age.styx (sages x a)).1
   Coin.mult (Aqua.qua (r.n x) z.2.2.1) (Aqua.dbox (r.n x) z.1)
lemma adjK:Kn (adj r):= by
    have hp:= sageK.right.right.left.left
    exact Coin.multK (Coin.invK (Aqua.dboxK r.nKn hp.right.right.left)) (Aqua.dboxK r.nKn hp.left)
abbrev ratioE(r:Rock q w h):ℕ:=4*Net.pad r.w.p
def localF(r:Rock q w h): Lyric:= .solo (ratioE r) ⟨_,(adjK r).comp Kn.first⟩
abbrev root0(p:MintV)(b:Bool) := if b then 0 else p.coin
def verse (m:Nick) (b:Bool)(a c y:Lyric):Lyric:=
    let f :ℕ→ Lyric
      | 0=>a
      | 1=>c
      | 2=>y
      | _=>localF r
    reset (Folk.bind f (Nick.temple m r.w.p b)) (root0 p b)
abbrev theta (f:Nick): Coin:=Coin.place 1 f.toastC
lemma real0 (p:Nick): (theta p).v=p.king.theta:=by
    rw [theta,Coin.place0 _ _ p.realD]; norm_num [p.realC]

abbrev stageP (_:Word)(i:ℕ):Crt:= sages [] i

def starsK (o:ℕ)(b:Bool):Sight:= by
    have h:= sageK
    have hp:= h.right.left.left
    have ht:= ((Kn.fix (3:ℕ)).tuple ((((hp.tuple hp.bl.pred)).tuple h.right.right)))
    let H:= Kn.wash.comp ht
    exact if b then ⟨_, Kn.wash.comp (H.tuple (Kn.fix (hole o 0)))⟩ else
      ⟨_,Kn.wash.comp (H.tuple (Kn.wash.comp ((Kn.fix o).tuple leftQ.runs)))⟩
abbrev voiceK(o:ℕ)(b:Bool):Cog:=Bullet.snap (starsK o b)

abbrev lengthF(r:Rock q w h):ℕ:=capacity 2 r.w.p.K 1 0
abbrev creditR (p:MintV):=p.low+5
def legion (v: Tags)(a:Nick):Cage:=
   ⟨lengthF r,r.w.p.K,p.sealR,creditR p,knob r v,voiceK 5 true,voiceK 0 false,fun b=>voiceK
        (if b then 1 else 2) false,⟨_,Kn.fix (theta a)⟩, verse r p a,root0 p⟩

def divisionB(v:Tags)(b:Nick)(n:ℕ):Cog :=
   let p:= legion r p v b
   if n=1 then p.fruit false else if n=3 then p.belt true else if n=4 then p.fruit true else p.belt false
def inner (v: Tags)(s:Nick):Cog:= Studio.arrange (divisionB r p v s) 4
def entire (v:Tags):List Profile → Cog
    | []=>Fret.Cargo.knock
    | a::t=> Cog.bif (later a) (inner r p v (decodeP a)) (entire v t)
abbrev baseTc (v:Tags):Cog:=entire r p v (bankS r.w).toList
lemma decant (v:Tags){l:Lot}{q b x y d c}{s:Nick}(h:Lot.Mane l c b d q (inner r p v s) x y)
    {a:List Profile}(he: copyN s ∈ a)(ht:book0 l.x q=copyN s): l.Mane c b d q (entire r p v a) x y:=by
    induction a with
    | nil=>contradiction
    | cons p a ih=>
       by_cases hp:p=copyN s
       · subst p; refine .yes ?_ ?_
         · change decide (book0 l.x q=_) =true;rw [ht]; simp
         rwa [copyB]
       refine .no ?_ (ih ((List.mem_cons.1 he).resolve_left (Ne.symm hp)))
       change decide (book0 l.x q=_) =false; rw [ht]; simp [Ne.symm hp]

end Fort
end
end ExactDerandomization.Aurora

end

section

namespace ExactDerandomization.Aurora
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Stem Spring Scroll
open Cambria.Wear.Paper
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Fort

variable (p:MintV) (r:Rock q w h)
abbrev priceR:=4+ Bank.hu p r+Cambria.Era.tariff r

def weightD (w:Cage)(c:ℕ):ℕ:= w.skyG + w.totalG c + c
open Cambria.Wear in
abbrev none0:=Paper.noneT

def topO (q:Profile):ℕ:= weightD (legion r p none0 (decodeP q)) (priceR p r)
def budget4:=priceR p r + ∑ i∈Scroll.bankS r.w, topO p r i
section
open Cage
lemma countLink (s t:Cage)(he:∀ b:Bool,s.firstC b=t.firstC b)(he':s.crown=t.crown)(he0:s.nest=t.nest)
    (he1:s.m=t.m)(he2:s.lo=t.lo):s.skyG=t.skyG ∧ ∀ c,s.totalG c=t.totalG c:=by
   have hf(b):s.figure b=t.figure b:=by
      unfold figure; rw [he,he,he',he0]
   have hr(b):s.realkey b=t.realkey b:=by cases b;exact he';exact he _
   have ht(b):s.Peer b=t.Peer b:=by unfold Peer; rw [hr,he2]
   constructor
   · unfold skyG Ink.prepare; rw [hf,hf,ht,ht]
   intro c
   have hJ(b): s.exitP c b=t.exitP c b:=by unfold exitP; rw [hf]
   have hH (b):s.tolls b c=t.tolls b c:=by
      unfold tolls Badge.tariff Badge.tariffStart Cage.gauge badge0; dsimp only; unfold Cage.pin; rw [hr,he2]
   unfold totalG Cage.lastP Ink.voteC OutC
   rw [hJ,hJ,hH,hH]; unfold goodz;rw [he1]
lemma flow {v W:Tags}(n:Nick): (legion r p v n).skyG=(legion r p W n).skyG ∧ ∀ c,
                       (legion r p v n).totalG c=(legion r p W n).totalG c:=
   countLink _ _ (fun _=>rfl) rfl rfl rfl rfl
lemma fungal (S T:Nick→Cage) (i:Finset Profile)(n:Nick)(c:ℕ)(hn:copyN n∈i)
   (h:(S n).skyG=(T n).skyG)(he:(S n).totalG c=(T n).totalG c):
     let q:= c+∑ j∈i,weightD (T (decodeP j)) c
     (S n).skyG ≤q∧ (S n).totalG c ≤ q:=by
   intro q
   have h0:= single_le_sum (fun j _=>Nat.zero_le (weightD (T (decodeP j)) c)) hn
   rw [copyB] at h0
   have hz:weightD (T n) c ≤ q:=le_trans h0 (Nat.le_add_left ..)
   unfold weightD at hz; omega
lemma story0 (n:Nick)(v:Tags)(hc:copyN n ∈ bankS r.w) :
         (legion r p v n).skyG ≤ budget4 p r ∧ (legion r p v n).totalG (priceR p r) ≤ budget4 p r:=
    fungal (legion r p v) (legion r p none0) (bankS r.w) n (priceR p r) hc (flow p r n).1 ((flow p r n).2 _)

end
end Fort

namespace Grape
open Line Line.Fabric
open Fort
structure Dew (u:Line (q:=q) (w:=w) (h:=h)) where
     p:MintV
     a:Fabric u
namespace Dew
open Line Line.Fabric Fret.Seats
variable (e:Dew u)
abbrev g:= Age.L e.a.m-1
abbrev f := e.a.c 9 0
abbrev bench (x:ℕ):Seats:=u.D.chord e.f x e.f
abbrev t:=e.a.t
abbrev stage0 := Nick.green e.t
abbrev court:=legion u.r e.p u.v e.stage0
abbrev cost := priceR e.p u.r
abbrev high := u.D.high e.f
abbrev T:=e.high+budget4 e.p u.r
abbrev own:= e.a.β e.g
abbrev fig(x i j:ℕ):= film (e.bench x) i j

structure Ready :Prop where
    manager: Terrain.Stone.Rector e.a e.p
    lit:e.a.activeR
    burn : budget4 e.p u.r ≤ u.v.slope
namespace Ready
variable {e:Dew u}(h0:e.Ready)
include h0
omit h0 in
lemma account: e.cost ≤ budget4 e.p u.r ∧ 4 ≤ e.cost∧Bullet.roomS ≤ e.cost :=
     ⟨Nat.le_add_right ..,by have hh:=Cambria.Era.billed u.r; unfold cost priceR;omega,
                            by have hh:=Cambria.Era.billed u.r;unfold cost priceR;omega⟩
omit h0 in
lemma now : e.g +1=Age.L e.a.m:=by unfold g Age.L;omega
omit h0 in
lemma last :u.D.D e.f=1:= e.a.ageEnd _ (by decide)
lemma fee : u.D.Suite e.f:=h0.manager.chart.rent (h0.manager.frontT h0.lit false).pos
omit h0 in
lemma toward :u.D.D e.own.dataN=1∧ u.D.W e.own.visN+1 ≤ u.D.W e.f∧ u.D.W e.own.dataN+1 ≤ u.D.W e.f:=by
   let v:=e.a
   change u.D.D (v.c 3 e.g)=1∧ u.D.W (v.c 4 e.g)+_ ≤ u.D.W (v.c 9 0)∧ u.D.W (v.c 3 e.g)+_≤_
   rw [Stone.D,Stone.W,Stone.W,Stone.W]
   have p(k:ℕ)(h:Brole k):= Age.endbirth (a:=k) (b:=9) (Ready.now (e := e)) h (by decide) (by decide)
   exact ⟨(p 3 (by decide)).1,(p 4 (by decide)).2,(p 3 (by decide)).2⟩
omit h0 in
lemma elder : e.own.m=e.court.m:=by
   unfold own Fabric.β Cage.m court legion
   dsimp only
   let m:=e.a.m
   have he : Est.gapD (Age.L m) e.g=1:= Est.gap_end ..
   change capacity 2 u.w0.p.K (Age.L m) e.g=_
   unfold lengthF capacity; rw [he]; rfl
lemma epi: copyN e.stage0 ∈ bankS u.r.w := within h0.manager.good.2.2.2.2.2.2
lemma flex: e.court.skyG ≤ budget4 e.p u.r ∧ e.court.totalG e.cost ≤ budget4 e.p u.r :=
   story0 e.p u.r e.stage0 u.v h0.epi
omit h0 in
lemma used(x:ℕ): (e.bench x).d=1:=(Ready.last (e := e))
lemma above : e.T ≤ u.D.H:=by
    unfold Dew.T
    have ht:= Studio.stayedC h0.fee (le_refl _) h0.burn
    rwa [Ready.last (e := e),mul_one] at ht
lemma hoped {x:ℕ}(he:x∈u.D.P): (e.bench x).stable e.court.kn∧ Live (e.bench x).head e.court.kn e.T:=by
    have hF:=h0.fee; have hs:=hF.shape.price
    refine ⟨Mold.knows u.r u.v u.x u.prog e.f x (of_decide_eq_true hF.stage) he hs,
                  Studio.vital _ h0.above⟩
lemma fitF {x}(h:x∈u.D.P)(i j): Lu.Standard (e.fig x i j) (campk e.court.kn) e.T:=
                       ⟨spread (h0.hoped h).1 i j, spanFilm (h0.hoped h).2 i j⟩
end Ready
end Dew
end Grape
end
end ExactDerandomization.Aurora

end

section

namespace ExactDerandomization.Aurora.Grape
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Stem Spring Scroll
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Dew
open Fort
variable (e:Dew u)
structure LensF(x:ℕ) (v:e.a.Hinge e.p e.g x):Prop where
     ready0:e.Ready
     inP:x∈u.D.P
     under0:e.a.HFine e.p e.g x v
     cert0 : ∀ j,lb (v.depot.tag j) ≤ Bank.hu e.p u.r
abbrev θ :ℝ:= e.t.tag.theta
abbrev roofG :=u.w0.ceiling u.B
namespace Ready
variable {e:Dew u}(h0:e.Ready)
include h0
lemma ankle0 : e.t.a  ≤ u.plotM.roof∧e.t.i ≤ u.plotM.roof:=by
    have hu:=h0.manager.good.2
    change e.t.ready u.plotM _ at hu
    obtain ⟨hi,hu,hk,hx,hm,hz⟩:=hu
    change _  ≤ u.plotM.roof∧ _  ≤ u.plotM.roof
    omega

omit h0 in
lemma billQ(_ _ _ _:ℕ):True:=trivial
omit h0 in
lemma bookG (i j x): let v:=sages u.x (e.fig x i j).info; v=kit 9 (e.a.m,0) (bitR e.t) (enc (Print.issued e.a.dye)):=by
    intro v; unfold v fig film panelx sages V info; dsimp only; rw [dec_round]; change (dec _ : Crt)=_
    exact dec_round ..
omit h0 in
lemma receipt(i j x o)(b:Bool): (starsK o b).f u.x (e.fig x i j).info=
             hole e.own.dataN (hole o (if b then 0 else i)):=by
   have ht:=(Ready.bookG (e := e)) i j x
   let v:= (e.fig x i j)
   change sages u.x v.info=_ at ht
   have hf : ∀ z :ℕ, enc (stint (sages u.x v.info) z e.g)= e.a.c z e.g:=by
       intro z; rw [ht]; rfl
   have hb:lb (Age.MV (sages u.x v.info))-1=e.g:=by rw [ht]; rfl
   have hx: leftQ.f u.x v.info=i:=by simp [leftQ,v,film,panelx,Fret.Seats.info,Reed.V]
   cases b
   · change hole (enc (stint (sages u.x v.info) 3 _)) (hole o (leftQ.f u.x v.info))=_
     rw [hb,hx,hf];rfl
   change hole (enc (stint (sages u.x v.info) 3 _)) (hole o 0)=_
   rw [hb,hf];rfl
lemma debt (x i j) (hx:x∈u.D.P): Chor (campk e.court.kn) e.cost e.T (e.fig x i j)
                (localF u.r) (rate e.t.a /rate e.t.i):=by
    let f:=e.fig x i j; let q:=adj u.r u.x f.info
    have hr:=h0.ankle0
    have hq :=h0.manager.chart.sc
    have ha:2^e.t.a≤u.n:=u.plotM.fits hq hr.1
    have hb:2^e.t.i≤u.n:=u.plotM.fits hq hr.2
    have hm:q.v=rate e.t.a/rate e.t.i:=by
       unfold q Fort.adj; dsimp only
       rw [(Ready.bookG (e := e))]; change (Coin.mult (Aqua.qua u.n e.t.a) (Aqua.dbox u.n e.t.i)).v=_
       rw [Coin.mul0,Aqua.priceT hb,Aqua.priceV ha,div_eq_mul_inv]
    have hk:=h0.fitF hx i j
    rw [← hm]; refine Chor.played hk.st hk.he (fun x _=>rfl) ?_
    rw [hm,abs_of_nonneg (div_nonneg (rate_pos _).le (rate_pos _).le)]; change _ ≤ massB _ ((e.bench x).d)
    rw [(Ready.used (e := e))]; unfold massB; rw [mul_one]
    exact stayed _ _ _ (Quest.ampl _ h0.manager.good.2)

end Ready
namespace LensF
variable {e:Dew u}{x:ℕ}{f:e.a.Hinge e.p e.g x}(hS:e.LensF x f)
include hS
lemma porch(i:ℕ)(hp:i<e.court.m): u.smallQ e.own.dataN i:=
   let h:=hS.ready0; let v:=h.manager.frontP h.lit e.g (by have :=(Ready.now (e := e));omega)
   v.awake (v.size0 i ((lt_of_lt_of_le hp) (le_of_eq (Ready.elder (e := e)).symm)))
lemma gotK(i:ℕ):Punct (e.bench x).head e.cost (f.depot.tag i):=by
    unfold Punct; change lb (f.depot.tag i)+1 ≤ e.cost*(e.bench x).d
    rw [(Ready.used (e := e))]; have h:=hS.cert0 i; unfold cost priceR;omega
lemma photo (i:ℕ)(hi:i<e.court.m):
   (e.fig x i 0).rite e.cost e.court.ask (f.depot.tag i):=by
     have hp:= hS.ready0; have he:=hS.under0.found.next i (hS.porch i hi)
     exact Bullet.copy u.D hp.fee (by have :=(Ready.account (e := e));omega) hS.inP (by rw [(Ready.last (e := e))];exact (Ready.toward (e := e)).2.2)
                  ((Ready.receipt (e := e)) i 0 x 0 false) (hS.gotK i) he
lemma price : e.T  ≤  u.D.high e.own.dataN:=by
     have h:= hS.ready0
     have he:u.D.W e.own.dataN+u.D.D e.f ≤ u.D.W e.f:=by rw [(Ready.last (e := e))]; exact (Ready.toward (e := e)).2.2
     have ht:= Studio.soonerC h.fee he h.burn le_rfl; rw [(Ready.last (e := e)),mul_one] at ht; exact ht
lemma surfD (i): (e.fig x i 0).band e.cost e.T e.p.sealR e.court.base f.depot.y.base:=by
     have h:= hS.ready0
     have hz:=hS.under0.at0
     let z:=e.own
     have ht:u.D.W z.dataN+u.D.D e.f  ≤ u.D.W e.f:=by rw [(Ready.last (e := e))]; exact (Ready.toward (e := e)).2.2
     apply Bullet.clef u.D h.fee (Ready.account (e := e)).2.2 hS.inP ht
                   ((Ready.receipt (e := e)) i 0 x 5 true) hS.price
     rw [(Ready.last (e := e)), ←(Ready.toward (e := e)).1]; exact hz
lemma felt (i:ℕ)(hi:i<e.court.m)(b:Bool): (e.fig x i 0).band e.cost e.T e.p.sealR (e.court.partR b)
            (Reed.sideq (f.depot.qpoint i) b):=by
     have h:= hS.ready0
     let z:=e.own
     have ht:u.D.W z.dataN+u.D.D e.f  ≤ u.D.W e.f:=by rw [(Ready.last (e := e))]; exact (Ready.toward (e := e)).2.2
     apply Bullet.clef u.D h.fee (Ready.account (e := e)).2.2 hS.inP ht
                 ((Ready.receipt (e := e)) i 0 x (if b then 1 else 2) false) hS.price
     rw [show u.D.D e.f=u.D.D e.own.dataN from (Ready.last (e := e)).trans (Ready.toward (e := e)).1.symm]; exact (hS.under0.hue b).ready _ (hS.porch i hi)

lemma sum_house(b:Bool)(v:ℕ→ℝ) : |(e.a.trio b).eval (v 0) (v 1) (v 2)| ≤ massB (root0 e.p b) 1:=by
    let a:= e.t
    cases b
    · have hs:=hS.ready0; obtain ⟨p,hp,ht⟩:=hs.manager.book.saving.money
      let h:= e.a.trio false; let X:=h.eval (v 0) (v 1) (v 2)
      have hf:TS e.θ p.T.R h:= Tonic.fee (s:=u.plotM) (q:=e.t) p.T hs.manager.good.2
      have h1:0≤ X:=hf.nn ..
      have h2:fourth X ≤ p.T.R^3:=hf.rootub ..
      change |X| ≤ _; rw [abs_of_nonneg h1,←fourth_four h1]
      exact le_trans (pow_le_pow_left₀ (fourth_nn X) h2 4) hp
    change |(suppT e.θ false).eval _ _ _| ≤ _
    obtain ⟨e1,e2⟩:=rising_mem (e.θ/4) (e.θ/3) (v 0)
    obtain ⟨h1,h2⟩:= rising_mem (e.θ/200) (e.θ/100) (v 1)
    change |rising _ _ (v 0)*(1-rising _ _ (v 1))*1| ≤ _
    have he:=mass1 (root0 e.p true) 1; rw [abs_le]; constructor <;> nlinarith

lemma express(i:ℕ)(b:Bool) :
    let k:=campk e.court.kn
    let p:=e.fig x i 0
    let v(y:Lyric):= Chor k e.cost e.T p y
    let d:=f.depot; let y:=d.y.ts (d.pos i); let r:=d.y.rk d.S e.court.k
    v (e.court.firstC true) y.1 → v e.court.crown r →v (e.court.firstC false) y.2 →
     v (e.court.figure b) (d.y.val d.S e.court.k (e.a.trio b) (d.pos i)):= by
   intro K p P d y r hA hB hC
   let s:=u.plotM
   let t:=e.t
   let V :ℕ → ℝ
     | 0=>y.1
     | 1=>r
     | 2=>y.2
     | _=>rate t.a/rate t.i
   let m:=Nick.green t; let f:=m.temple u.w0.p b
   have he:Folk.meanF f V=(e.a.trio b).eval y.1 r y.2:=by
       cases b
       · exact m.ten (s:=s) (q:=t) rfl V rfl
       exact m.many V
   let v:ℕ→Lyric
      | 0=>e.court.firstC true
      | 1=>e.court.crown
      | 2=>e.court.firstC false
      | _=>localF u.r
   have hx:= hS.ready0.fitF hS.inP i 0
   have hz(n:ℕ):Chor K e.cost e.T p (v n) (V n):=by
      match n with
      | 0=>exact hA
      | 1=>exact hB
      | 2=>exact hC
      | n+3=>exact hS.ready0.debt x i 0 hS.inP
   change Chor K e.cost e.T p (reset (Folk.bind v f) (root0 e.p b)) _
   have hr:= Folk.time f hx hz
   rw [he] at hr; refine hx.ring0 hr (root0 e.p b) ?_
   rw [show p.d=1 from (Ready.used (e := e)) x]; exact hS.sum_house b V
lemma scored :
     e.court.Ink (e.bench x) f.depot e.θ (e.a.trio) e.cost e.T :=by
   have h:=hS.ready0
   have he:= h.hoped hS.inP
   refine ⟨hS.under0.solid,he.1,fun i j=>(h.fitF hS.inP i j).1,(Ready.used (e := e)) _,
                hS.under0.card0.trans (Ready.elder (e := e)),(Ready.account (e := e)).2.1,he.2,?_ ,
               fun i=>real0 (Nick.green e.t),fun i hi=>⟨hS.photo i hi,hS.gotK i⟩,fun i _=>hS.surfD i,
               hS.felt,fun b=>rfl,fun {i} _ _ b=>hS.express i b⟩
   rw [(Ready.used (e := e))]
   have hx:=h.manager.book.saving.minutes
   have hp: delta ≤ e.θ:= Kind.lowp ..
   change (massB (e.p.low+5) 1)⁻¹ ≤_
   rw [mass_mul, mul_inv,show massB 5 1=(32:ℝ) by norm_num [massB]]
   norm_num [delta,Hie.A] at hx hp ⊢; linarith
end LensF
end Dew
end
end ExactDerandomization.Aurora.Grape

end

section

namespace ExactDerandomization.Aurora.Grape
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Stem Spring Scroll
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Dew

open Fort Depot.Trust Cage
variable (e:Dew u)
structure Dose (x:ℕ) where
     f:e.a.Hinge e.p e.g x
     stageT:Cage.Ballot f.depot
namespace Dose
variable {e:Dew u}
variable {x:ℕ}
variable (v:Dose e x)
abbrev p:=v.f.depot
abbrev codeS (b:Bool)(i:ℕ):= valN e.court v.p v.stageT b i
abbrev plex (b:Bool)(i):= v.p.pos (Style.child e.court v.p v.stageT b i)
structure Lens : Prop where
     hp:e.LensF x v.f
     part:Harvest e.court (e.bench x) v.p e.θ e.a.trio e.cost e.T v.stageT
     assigned :Studio.Parcel u e.f (baseTc u.r e.p u.v)
abbrev chargeE (b:Bool)(i:ℕ):= if v.codeS b i=0 then 0 else e.a.aimE b x (v.plex b i)

namespace Lens
variable {v:Dose e x} (hlg:v.Lens)
include hlg
lemma opted :Studio.Parcel u e.f (inner u.r e.p u.v e.stage0):=by
    have ht:= hlg.hp.ready0
    intro p b c x y hv hp
    apply hlg.assigned p b c x y hv
    apply Fort.decant
    · exact hp
    · exact Finset.mem_toList.mpr ht.epi
    unfold book0; rw [hv]
    unfold uphold Dew.f Fabric.c rowL clr; rw [Wire.eq];rfl
lemma readout {i:ℕ}(ht:u.smallQ e.f i)(b:Bool):
     u.D.swears (post e.f (e.a.terminal b).tagop i 0) x (v.codeS b i):=by
    have hs:=hlg.hp.ready0; let k:=e.a.terminal b
    have hm:= hlg.part.budget
    have hh:= hs.flex.2; have ht0:4 ≤ e.cost:=(Ready.account (e := e)).2.1
    have hv:(e.fig x i 0).rite (budget4 e.p u.r) (divisionB u.r e.p u.v e.stage0 k.tagop) (v.codeS b i):=by
       cases b <;> exact higher (hlg.part.stem i _).1 hm hh
    have h3:k.tagop ≤ 4:=by cases b<;>simp [k]
    exact Studio.echoTicket hs.fee h3 ((show k.tagop ≤ 32 from le_trans h3 (by omega))) ht (by have ht1:=(Ready.account (e := e)).1;omega) hs.burn hv hlg.opted

lemma position {b:Bool}{i:ℕ}(hp:v.codeS b i≠0) :
   let p:= v.p; let j:=Relay.mark (v.codeS b i)
   i< (e.a.terminal b).m ∧ p.live j ∧ j<p.n∧ x∈e.a.S0 ∧ p.pos j∈e.a.S1:=by
    intro p j; have hz:= hlg.part.style; have he:=hlg.hp.scored
    have ht:p.live j:= (Stem.Cage.Style.park (b:=b) (i:=i) hp).1.1
    have hQ:= hlg.hp.under0
    refine ⟨hz.many hp he,ht,hQ.solid.card0 _ ht,
              by by_contra! hn; exact hQ.kill hn _ ht,hQ.dst ▸ hQ.solid.into _ ht⟩

lemma seats (b:Bool) (i:ℕ):u.smallQ (e.a.terminal b).visN (v.codeS b i):=by
    have ht:=hlg.part.style
    have he:=hlg.hp.ready0
    have hh:=he.manager
    let p:=v.p; let k:= Relay.mark (v.codeS b i)
    have hd:u.D.D (e.a.terminal b).visN=1:=by
        cases b <;> exact (e.a.ageEnd _ (by decide))
    change lb _ ≤ u.eye.e*u.D.D _
    rw [hd,mul_one]
    by_cases hv:v.codeS b i=0
    · rw [hv,lb_zero]; have hp:=hh.book.cost0; change _ ≤ u.eye.e at hp; unfold Bank.hx Bank.hu Bank.hi at hp;omega
    have hq := Stem.Cage.Style.park (b:=b) (i:=i) hv
    let t:= ColorF.hoot p v.stageT.wt b k
    have hT: v.codeS b i=Seek.bin k (p.tag k):= hq.2.1.trans
                                       (congrArg (fun n=>Seek.bin k n) (show Cage.Game e.court p v.stageT b k=p.tag k from ite_eq_left hq.1))
    have hp0 : k < capacity 2 u.w0.p.K (Age.L e.a.m) e.g:=
         lt_of_lt_of_le (hlg.position hv).2.2.1 hlg.hp.under0.card0.le
    exact le_trans (by rw [hT]; exact hh.book.saving.office (Ready.now (e := e)) hp0 (hlg.hp.cert0 _)) hh.book.cost0

lemma journey {i:ℕ}(hi:u.smallQ e.f i)(b:Bool):
    let c:=e.a.terminal b
    u.eye.Flora u.torch.p c.visN i x (if v.codeS b i=0 then none else some (v.codeS b i,v.plex b i)):=by
   intro c; have he:= hlg.hp.ready0; have hf:=he.manager.frontT he.lit b; let z:=u.eye
   have hu : c.dataN=e.f:=rfl
   let a:=v.codeS b i; let j:= Relay.mark a
   have hh:=hlg.readout hi b
   by_cases hp:a=0
   · rw [ite_eq_left hp]; refine Cone.ConeX.Flora.abs ?_
     have ha:=hf.point0 he.manager.chart i (hf.back0 hi)
     refine ⟨ha,hlg.hp.inP,?_⟩
     rw [show u.eye.ear u.torch.p c.visN i=_ from hf.ear0 i]
     exact (u.D.identity hh).trans hp
   rw [ite_eq_right hp]
   obtain ⟨ht,hP,hJ,hL,hK⟩:=hlg.position hp
   have hz: True:= trivial
   have hF:= hlg.hp.under0
   have hG:= he.manager.frontP he.lit e.g (by have hh:=(Ready.now (e := e)); omega)
   have hS:j<e.own.m:= lt_of_lt_of_le hJ hF.card0.le
   let k:= v.plex b i
   apply he.manager.chart.Rope hf i x a j e.own.visN k (v.p.tag j) hi (hlg.seats b i) hp hlg.hp.inP _ _ _ _
        (Fabric.Good.n1 he.manager.chart he.manager.good hK) hh
        (hF.found.caseM j hP (hG.awake (hG.size0 _ hS)))
   · have hL(z:ℕ)(hh:z=10∨z=11):
             offer u.s.pave u.x (Cone.ConeX.stem (e.a.c z 0) i a)=rope e.own.visN j:=by
         unfold Mold.offer; dsimp only
         rw [Stone.roleR,ite_eq_right (by omega:z≠2),ite_eq_right (by omega:z≠4),ite_eq_right (by omega:z≠15)]
         have he:tailR (uphold (e.a.c z 0))=e.own.visN:=by
                unfold tailR uphold Fabric.c rowL clr; rw [Wire.eq];rfl
         rw [he]
     have he:c.visN=e.a.c (if b then 11 else 10) 0:=rfl
     exact he.symm ▸ hL (if b then 11 else 10) (by split<;>omega)
   · cases b<;>exact Stone.zeroR ..
   · rw [← hf.grain]; rw [hu,(Ready.last (e := e))]
     exact le_trans (Ready.toward (e := e)).2.1 ((Nat.le_add_right _ _).trans hf.price)
   rw [← hG.grain,←hf.grain,hu,(Ready.last (e := e)),(Ready.toward (e := e)).1]; omega

lemma synced {y:ℕ}(hg:x∈e.a.S0)(he:y∈e.a.S1)(b:Bool):
     e.a.aimE b x y=v.p.y.val v.p.S e.court.k (e.a.trio b) y:=by
   have hp:=hlg.hp; have hh:=hp.ready0.manager
   have hl :=hh.book.saving
   obtain ⟨v0,hv,hC⟩:=hl.money
   have hT:TS e.θ v0.T.R (e.a.trio b) :=by
      cases b
      · exact Tonic.fee (s:=u.plotM) (q:=e.t) v0.T hh.good.2
      exact v0.T.support _
   have ha:=hp.under0; have hd:=hp.ready0
   have hS:= ha.y0.set e.a (Ready.now (e := e)) hl.tested hT (Kind.highp _) hC (show y∈(e.a.marathon x).S from he)
   unfold Fabric.aimE At.Grid.pre; rw [ite_eq_left (show x∈e.a.grid.src ∧ y∈e.a.grid.dst∧ (false=false ∨ y∈e.a.grid.narrow) from ⟨hg,he,Or.inl rfl⟩)]
   rw [show v.p.y= _ from ha.ton,show v.p.S=e.a.S1 from ha.dst]
   change ((e.a.marathon x).mid _).val _ _ _ _=_
   have hc: (e.a.frame.L) =e.g+1:= (Ready.now (e := e)).symm
   rw [hc]; exact hS.symm

lemma upcoming(b:Bool)(i:ℕ):
     v.chargeE b i=Cage.spice e.court v.p i e.a.trio b v.stageT:=by
    unfold chargeE Cage.spice
    by_cases ht:v.codeS b i=0
    · rw [ite_eq_left ht]; exact (ite_eq_left ht).symm
    rw [ite_eq_right ht]; refine (hlg.synced (hlg.position ht).2.2.2.1 (hlg.position ht).2.2.2.2 b).trans ?_
    exact (ite_eq_right ht).symm

lemma secure0 {b:Bool} {i:ℕ}(ht:u.smallQ e.f i):
   u.D.Voice e.f x (hole (Fabric.heated b) i) (u.D.high e.f) (Fabric.Tscale e.p b) (v.chargeE b i):=by
   have he:= hlg.part; have hf:= hlg.hp.ready0; have hs:= he.budget
   have hn:(e.fig x i 0).band (budget4 e.p u.r) e.high (root0 e.p b)
                   (divisionB u.r e.p u.v e.stage0 (Fabric.heated b)) (v.chargeE b i):=by
      rw [hlg.upcoming]
      have hc:e.high + e.court.skyG*(e.bench x).d ≤ e.T:=by
                      rw [(Ready.used (e := e))]; exact Nat.add_le_add_left (show _  ≤  _ by have := hf.flex.1; omega) _
      cases b <;> exact Seats.flex (he.song _ _ _ hc) hs hf.flex.2 le_rfl
   have hp:Fabric.heated b ≤ 4:=by cases b <;> decide
   have hg := Studio.scoreTicket (j:=root0 e.p b) hf.fee hp (le_trans hp (by omega)) ht
                              (le_trans (by have hh:=(Ready.account (e := e)); change _  ≤  e.cost;omega) (Ready.account (e := e)).1)
                                                  hf.burn le_rfl hn hlg.opted
   rw [(Ready.last (e := e)),mul_one] at hg; exact hg

end Lens

end Dose
end Dew
end
end ExactDerandomization.Aurora.Grape

end

section

namespace ExactDerandomization.Aurora.Grape.Dew
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Stem Spring Scroll
open Line Line.Fabric Fret.Seats Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Dew u}
namespace Dose.Lens
open Depot.Trust Cage
variable {x:ℕ}{v:Dose e x}(hh:v.Lens)
include hh
abbrev panelF (v:Dose e x):=ColorF.mapG v.p v.stageT.wt
lemma roofp : 0<e.θ:=hh.hp.scored.ht0
lemma k0T: v.stageT.wt.tau=e.θ∧v.stageT.wt.K=e.court.k:=
    ⟨hh.part.style.height,hh.part.style.rightP⟩
lemma area : Blob.acc (panelF v) v.p.y v.p.S e.court.k e.θ:=by
    have hs:= hh.part.style.legally
    rw [←hh.k0T.1,←hh.k0T.2]; apply hh.hp.under0.solid.region hs
    rw [hh.k0T.1];exact hh.roofp
lemma supported(b y) :
    y∈Blob.expose e.θ (panelF v) b v.p.S ↔ ∃ i,v.codeS b i≠0 ∧ v.plex b i=y:=by
    have hp:= hh.hp.under0; have hs:=hh.part.style
    have hb:0<v.stageT.wt.tau:=by rw [hs.height]; exact hh.roofp
    rw [←hs.height,show Blob.expose _ _ _ _=_ from hp.solid.onward hs.legally hb b]
    constructor
    · intro h; obtain ⟨i,he,rfl⟩:=mem_image.1 h
      obtain ⟨j,h1,h2⟩:=Stem.Cage.Style.hears hh.hp.scored (mem_filter.1 he).2
      exact ⟨j,h1, congrArg _ h2⟩
    rintro ⟨i,hk,rfl⟩
    let g:=Relay.mark (v.codeS b i)
    have hr: ColorF.hoot v.p v.stageT.wt b g:=(Stem.Cage.Style.park (b:=b) (i:=i) hk).1
    apply mem_image.2;exact ⟨g,mem_filter.2 ⟨mem_range.2 (hp.solid.card0 g hr.1),hr⟩, rfl⟩
lemma defend(b y)(he:e.a.aimE b x y ≠0):
    ∃ i,v.codeS b i≠0 ∧ v.plex b i=y:=by
   apply (hh.supported _ _).1
   have h: x∈e.a.S0∧y∈e.a.S1:=by
        unfold Fabric.aimE At.Grid.pre at he
        split at he
        · next h=>exact ⟨h.1,h.2.1⟩
        contradiction
   rw [hh.synced h.1 h.2] at he
   have hz: y∈v.p.S:=by rw [show v.p.S=e.a.S1 from hh.hp.under0.dst]; exact h.2
   cases b
   · apply Blob.exposed_main hh.area hh.roofp hz _ _ he
     intro a h; exact Quest.wall0 e.t u.plotM h
   exact Blob.exposed_supp hh.area hh.roofp hz he
lemma blessed(i:ℕ)(hi:v.codeS false i≠0): e.a.aimE true x (v.plex false i)=1:=by
    obtain ⟨ht,hp,hz,hc,hj⟩:=hh.position hi
    rw [hh.synced hc hj]
    exact Blob.protects hh.area hh.roofp ((hh.supported false _).2 ⟨i,hi,rfl⟩)
lemma sunny(b i j)(hi:v.codeS b i≠0)(hj:v.codeS b j ≠0)(ho:v.plex b i=v.plex b j):i=j:=
    Stem.Cage.Style.lonely hh.hp.scored hi hj ho
end Dose.Lens

namespace Supply
open Dose
abbrev stageX :=∀ x:ℕ,x ∈ u.D.P → Dose e x
variable {e:Dew u}
def catalogue (f:stageX (e:=e))(b:Bool):Producer:=
   ⟨fun x i=> if h:x∈u.D.P then (f x h).codeS b i else 0,
    fun x i=> if h:x∈u.D.P then (f x h).plex b i else 0⟩
lemma sealed0 (h:e.Ready)(f:stageX (e:=e))(hc:∀ x,∀ h:x∈u.D.P,(f x h).Lens):
       e.a.Tgood e.p (catalogue f):=by
   let p:=catalogue f
   have ha{x b i}(he:(p b).awake x i): x∈u.D.P:=by
        unfold p Producer.awake catalogue at he; dsimp only at he
        split at he <;> first | assumption | contradiction
   have hz(x i)(he:x∈u.D.P)(b):
         (p b).tag x i=(f x he).codeS b i ∧ (p b).locate x i=(f x he).plex b i:=
             ⟨dite_eq_left he,dite_eq_left he⟩
   have hh{b x i}(hi:x∈u.D.P) :
       (p b).scoreF (e.a.aimE b) x i=(f x hi).chargeE b i:=by
     unfold Producer.scoreF Producer.awake; obtain ⟨ht,hq⟩:=hz x i hi b

     by_cases he:(p b).tag x i=0
     · rw [ite_eq_right (not_not_intro he)]; apply Eq.symm (ite_eq_left _); rwa [←ht]
     rw [ite_eq_left he,hq]; exact (ite_eq_right (fun h=>he (ht.trans h))).symm
   have hw:= h.manager
   constructor
   · intro b
     let t:=e.a.terminal b; let c:=p b
     refine ⟨⟨?_,?_,?_⟩,hw.frontT h.lit b,?_,?_⟩
     · intro x i hi
       have he:=ha hi; obtain ⟨ht,hq⟩:=hz x i he b
       have hl := (hc x he).position (show (f x he).codeS b i≠0 from fun e=>hi (ht.trans e))
       exact ⟨hl.2.2.2.1,hq ▸ hl.2.2.2.2⟩
     · intro x i j he hi hu
       have ht:=ha he; obtain ⟨hq,hv⟩:=hz x i ht b; obtain ⟨hb,hc0⟩:=hz x j ht b
       apply (hc x ht).sunny b i j (fun h=>he (hq.trans h)) (fun h=>hi (hb.trans h))
       exact hv.symm.trans (hu.trans hc0)
     · intro x y hY
       have he:x∈u.D.P:= by
          apply Fabric.Good.n0 hw.chart hw.good
          unfold Fabric.aimE At.Grid.pre at hY; split at hY
          · next h=> exact h.1
          contradiction
       obtain ⟨i,h1,h2⟩:= (hc x he).defend b y hY
       obtain ⟨ht,hq⟩:= hz x i he b; exact ⟨i,(fun h=>h1 (ht.symm.trans h)),hq.trans h2⟩
     · intro x hx
       let g:=hc x hx
       constructor
       · intro i hi; exact (hz x i hx b).1 ▸ g.readout hi b
       · intro i hi; exact (hz x i hx b).1 ▸ g.seats b i
       · intro i hj
         by_contra hk; obtain ⟨h1,h2⟩:=hz x i hx b
         exact (not_lt_of_ge hj) (g.position (b:=b) (i:=i) (fun h=>hk (h1.trans h))).1
       · intro i hi
         have hg:=g.journey hi b; obtain ⟨h1,h2⟩:=hz x i hx b

         rw [← h2, ←h1] at hg
         exact hg
     intro x hx
     refine ⟨fun i hi=>?_⟩
     have hx':= (hc x hx).secure0 (i:=i) (b:=b) hi
     rw [← hh hx] at hx'
     rw [show u.D.D t.dataN=1 from (Ready.last (e := e)),mul_one]
     exact hx'
   intro x i hi; have he:= ha hi; obtain ⟨ht,hq⟩:= hz x i he false
   exact hq.symm ▸ (hc x he).blessed i (fun h=>hi (ht.trans h))

theorem givenE (hh:e.Ready)
    (hp:Studio.Parcel u e.f (Fort.baseTc u.r e.p u.v))
    (hs:∀ x∈ u.D.P,∃ v, e.LensF x v): ∃ f,e.a.Tgood e.p f:=by
   have ht(x)(hx:x∈u.D.P):∃ v:Dose e x,v.Lens:=by
       obtain ⟨v,hv⟩:=hs x hx
       have hZ:e.court.skyG*(e.bench x).d ≤ e.T:=by rw [(Ready.used (e := e)),mul_one]; exact le_trans hh.flex.1 (Nat.le_add_left ..)
       obtain ⟨u,he⟩:=Cage.bloom _ _ _ _ _ _ _ hv.scored hZ
       exact ⟨⟨v,u⟩,hv,he,hp⟩
   choose f he using ht; exact ⟨_, sealed0 hh f he⟩
end Supply
end
end ExactDerandomization.Aurora.Grape.Dew

end

end OAI
