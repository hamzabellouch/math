import OAI.Computability.Logspace.AffineSampling
import OAI.Computability.Logspace.RecursivePrograms

namespace OAI

/-!
Redundant dyadic digits, signed arithmetic, and bounded-precision numerical queries.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! signed/word arithmetic -/
namespace ExactDerandomization.Relay
open Counter

def slate (a:ℤ):ℕ := bead a.toNat (-a).toNat
def stone (a b:ℕ):ℤ := (a:ℤ)-b
def scree (n:ℕ) :ℤ := stone (heed n) (readt n)

lemma screenp (x:ℤ) : scree (slate x)=x:=by
   unfold slate scree stone; rw [heed_eq,read_eq]; omega
lemma slate_stone (a b:ℕ): slate (stone a b) = bead (a-b) (b-a) :=by
   unfold slate stone; congr <;>omega
instance : Wire ℤ where
   enc:=slate
   dec:=scree
   eq:=screenp
   tidy:=by
     intro v h
     have hu:E (fun x a=> heed (v x a)):=foreE h
     have he:E (fun x a=> readt (v x a)):=(aftE h).pred
     simp only [scree,slate_stone]
     exact cordE (hu.sub he) (he.sub hu).succ

def pairInt (x:ℤ) :ℕ×ℕ :=(x.toNat,(-x).toNat)
variable {α} [Wire α]
namespace Kn
lemma splitZ : Kn (fun (_:Word) (x:ℤ)=> pairInt x):=by
   intro v h
   have he:= @identity (α:=ℤ) _ _ h
   exact he
lemma topNat {f:PT α ℤ}(h:Kn f): Kn (fun x a=>(f x a).toNat):=
   (splitZ.comp h).left
lemma negNat {f:PT α ℤ}(h:Kn f): Kn (fun x a=>(-(f x a)).toNat):=
   (splitZ.comp h).right

lemma ZofN {f:PT α ℕ}(h:Kn f): Kn (fun x a=>(f x a:ℤ)):= by
    intro v e
    have hu:= h e
    change E (fun x a=> slate (f x (dec (v x a)):ℤ))
    simp only [slate, Int.toNat_natCast]
    have he(k:ℕ):(-(k:ℤ)).toNat=0:=by omega
    simp only [he]; exact cordE hu (E.const (0+1))
lemma rock {f g:PT α ℕ}(h:Kn f)(e:Kn g): Kn (fun x a=>stone (f x a) (g x a)):=by
   intro v he
   have hu := h he; have ht:=e he
   change E (fun x a=> slate (stone _ _))
   simp only [slate_stone]
   exact cordE (hu.sub ht) (ht.sub hu).succ
variable {f g:PT α ℤ}
lemma plusZ (h:Kn f)(e:Kn g):Kn (fun x a=> f x a+g x a):=by
    convert (h.topNat.add e.topNat).rock (h.negNat.add e.negNat) using 1
    ext x a; unfold stone; omega
lemma negZ (h:Kn f):Kn (fun x a=> -(f x a)):=by
    convert h.negNat.rock h.topNat using 1
    ext x a; unfold stone; omega
lemma absN (h:Kn f):Kn (fun x a=> (f x a).natAbs):=by
    convert h.topNat.add h.negNat using 1
    ext x a; omega
lemma leZ (h:Kn f)(e:Kn g):Kn (fun x a=> decide (f x a≤g x a)):=by
    let z:=h.plusZ e.negZ
    convert z.topNat.eq (Kn.fix 0) using 1
    ext x a; simp only [decide_eq_decide]; omega
lemma prodZ (h:Kn f)(e:Kn g):Kn (fun x a=> f x a*g x a):=by
    have ha:=h.topNat; have hb:=h.negNat; have hc:=e.topNat; have hd:=e.negNat
    convert (((ha.times hc).add (hb.times hd)).rock ((ha.times hd).add (hb.times hc))) using 1
    ext x a
    let u:=f x a; let v:=g x a
    have he1:u=(u.toNat:ℤ)-(-u).toNat:=by omega
    have he2:v=(v.toNat:ℤ)-(-v).toNat:=by omega
    unfold stone
    push_cast
    change u*v=_
    rw [show u*v=((u.toNat:ℤ)-(-u).toNat)*((v.toNat:ℤ)-(-v).toNat) by rw [← he1,← he2]]
    ring
lemma minZ (h:Kn f)(k:Kn g): Kn (fun x a=> min (f x a) (g x a)):=by
   simpa only [decide_eq_true_eq,min_def] using (h.leZ k).cond h k
lemma maxZ (h:Kn f)(k:Kn g): Kn (fun x a=> max (f x a) (g x a)):=by
   simpa only [decide_eq_true_eq,max_def] using (h.leZ k).cond k h

lemma down_eq (a:ℕ) (d:ℕ) : (-(a:ℤ))/(d+1:ℕ)= -(((a+d)/(d+1):ℕ):ℤ) :=by
    let r:ℕ:=(a+d)/(d+1)
    have h1:r*(d+1)≤a+d:=Nat.div_mul_le_self _ _
    have h2:a+d < (r+1)*(d+1):=(Nat.div_lt_iff_lt_mul (by omega)).1 (by change r<r+1; omega)
    have he1:(r:ℤ)*(d+1)≤a+d:=by exact_mod_cast h1
    have he2:(a:ℤ)+d<(r+1)*(d+1):=by exact_mod_cast h2
    change _= -(r:ℤ)
    push_cast
    have he : (0:ℤ)<d+1:=by omega
    apply le_antisymm
    · apply Int.le_of_lt_add_one
      apply (Int.ediv_lt_iff_lt_mul he).mpr
      nlinarith
    apply (Int.le_ediv_iff_mul_le he).mpr
    nlinarith

lemma chop {s:PT α ℕ} (h:Kn f)(e:Kn s):
    Kn (fun x a=> f x a / ((s x a+1:ℕ):ℤ)):= by
   convert (h.topNat.div e.succ).rock ((h.negNat.add e).div e.succ) using 1
   ext x a; let u:=s x a; let z:=f x a
   change z/ ((u+1:ℕ):ℤ) = stone _ _
   by_cases hz:0≤z
   · have he:(-z).toNat=0:=by omega
     change _=stone (z.toNat/(u+1)) (((-z).toNat+u)/(u+1))
     rw [he,zero_add,Nat.div_eq_of_lt (show u<u+1 by omega)]
     unfold stone; rw [Int.natCast_ediv, Int.toNat_of_nonneg hz]; simp
   have he:z.toNat=0:=by omega
   change _=stone (z.toNat/(u+1)) (((-z).toNat+u)/(u+1))
   rw [he,Nat.zero_div]; unfold stone
   rw [show z / ((u+1:ℕ):ℤ) = (-(((-z).toNat:ℕ):ℤ))/((u+1:ℕ):ℤ) by congr 1; omega,down_eq]; simp

lemma modulus {s:PT α ℕ} (h:Kn f)(e:Kn s):
    Kn (fun x a=> f x a % ((s x a+1:ℕ):ℤ)):= by
   convert h.plusZ ((e.succ.ZofN.prodZ (h.chop e)).negZ) using 1
   ext x a
   have he:=Int.emod_add_mul_ediv (f x a) ((s x a+1:ℕ):ℤ)
   omega

end Kn
lemma Zbound (x:ℤ) {k:ℕ} (h:x.natAbs < 2^k)(hs:1≤k):
    lb (enc x)≤3*k+2:=by
   have hu:lb x.toNat≤k:=modest (by omega) hs
   have hv:lb (-x).toNat≤k:=modest (by omega) hs
   have he:lb (enc x)≤2*lb x.toNat+lb (-x).toNat+2:=bead_small _ _
   omega

end ExactDerandomization.Relay

end

section

/-! Finite-horizon redundant digit contract. -/
namespace ExactDerandomization.Rill
open Relay Counter Finset

abbrev Tape := ℕ→ℤ
def dsign (w:Tape) (t:ℕ):ℤ:= if t=0 then w t else w t- 2*w (t-1)

def Checked (w:Tape)(V:ℝ)(H:ℕ) : Prop := |V| ≤1 ∧ ∀ i≤ H,|(w i:ℝ)-2^i*V|≤2

lemma safe_d {w V H} (h:Checked w V H){t}(he:t≤H): (dsign w t).natAbs≤6 := by
    have hh := abs_le.1 (h.2 t he)
    have hv : |(dsign w t:ℝ)|≤6:= by
      cases t with
      | zero=>
        simp [dsign,pow_zero] at *
        obtain ⟨ha,hb⟩:=abs_le.1 h.1
        rw [abs_le]; constructor <;>linarith
      | succ t=>
        obtain ⟨ha,hb⟩:=abs_le.1 (h.2 t (by omega)); obtain ⟨hz,hx⟩:=hh
        rw [pow_succ] at hz hx
        simp [dsign,abs_le]; constructor <;> linarith
    have hg := abs_le.1 hv; have ht: -(6:ℤ)≤dsign w t ∧ dsign w t≤ 6:=by exact_mod_cast hg
    omega
lemma slate_le (v:ℤ){k}(h:v.natAbs ≤ k) : enc v≤bead k k:= by
    apply bead_mono <;> omega
abbrev capD := bead 6 6

abbrev History := ℕ×ℕ
def postcard (q t:ℕ): ℕ := enc ((q,t):History)
abbrev clockK {α} [Wire α] (x y: PT α ℕ) (h:Kn x)(g:Kn y) :=
    Kn.wash.comp (h.tuple g)
structure Port where
   l:Lot
   w:ℕ
   d:ℕ
   src:ℕ
   info:ℕ
namespace Port
variable (p:Port)

def OK:= 0<p.d ∧ p.d≤p.w ∧ p.src≤p.l.F.limit
abbrev comp (t c:ℕ):= Lot.Mane p.l c ⟨p.w,t⟩ p.d (postcard p.info t)
abbrev s (h:ℕ):Site:=(h,p.src)

structure Uses (P:Cog) (c H:ℕ)(w:Tape):Prop where
   digits: ∀ t≤ H,p.comp t c P (p.s 0) (p.s (enc (dsign w t)))
def Feeds (P:Cog)(c H:ℕ)(w:Tape)(V:ℝ):=Checked w V H ∧ Uses p P c H w
abbrev Tells (P: Cog)(c H:ℕ)(V:ℝ):= ∃ w,p.Feeds P c H w V

lemma alone (hp:p.OK) (t c:ℕ) {x} (_:1≤c)(h:lb x+1 ≤ c*c) :
   p.l.state c ⟨p.w,t⟩ (p.s x):=by
   refine ⟨hp.2.2,?_⟩
   have hu : 1≤p.w:=hp.1.trans_le hp.2.1
   unfold span; dsimp only; nlinarith [Nat.mul_le_mul_left (c*c) hu]

lemma stale (hp:p.OK) (t c:ℕ) (h:20≤c):
   p.l.state c ⟨p.w,t⟩ (p.s 0):=p.alone hp t c (by omega) (by rw [lb_zero]; nlinarith)

end Port

lemma sumsign (w:Tape)(H:ℕ):
    ∑ i ∈ range (H+1), dsign w i*(2:ℤ)^(H-i)= w H:=by
   induction H with
   | zero=> simp [dsign]
   | succ H ih=>
      have hu :
          ∑ i∈range (H+1),dsign w i*2^(H+1-i) = w H*2:=by
         rw [← ih,sum_mul]
         apply sum_congr rfl; intro i hi
         have hh:=mem_range.1 hi
         rw [show H+1-i=H-i+1 by omega,pow_succ,mul_assoc]
      rw [sum_range_succ,hu]
      simp [dsign]; ring

lemma suffixes (w:Tape)(H:ℕ):
    ∑ i ∈ range (H+1), dsign w (H-i)*(2:ℤ)^i=w H:=by
    rw [← sumsign w H]
    let f(i:ℕ) := dsign w i*(2:ℤ)^(H-i)
    have he : ∑ i ∈ range (H+1), f i=∑ i∈range (H+1),f (H-i):=by

       symm; simpa using sum_range_reflect f (H+1)
    rw [show ∑ i ∈ range (H+1), dsign w i*(2:ℤ)^(H-i) =∑ i∈range (H+1),f (H-i) from he]
    apply sum_congr rfl; intro i hi; have hx:= mem_range.1 hi
    simp [f,show H-(H-i)=i by omega]
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter Finset
abbrev Wgt := ℤ×ℤ
abbrev Comb := ℕ×ℕ×ℕ×Wgt
abbrev Ream := Lore Comb
abbrev DW := Bool →ℕ→Tape
abbrev EV := Bool→ℕ→ℝ
structure Oven where
    n : Bool → Cub ℕ ℕ
    route : Bool → Cub (ℕ×ℕ) ℕ
    margin : Cub ℕ ℕ
    scans : Bool → Cog

namespace Oven
variable (p:Oven)
def era (x:Word)(q:ℕ):ℕ:=let z:History:=dec q;
                           z.2+p.margin.f x z.1
lemma eraK:Kn p.era:=by
   have hz:Kn (fun (_:Word)(q:ℕ)=>(dec q:History)):=Kn.unpack
   exact hz.right.add (p.margin.runs.comp hz.left)
def still (x:Word)(a:Ream):Bool := decide (a.2.1≤ p.era x a.1)
lemma stillK:Kn p.still := Kn.next.left.le (p.eraK.comp Kn.first)
def test (b:Bool)(x:Word)(a:Ream):Bool :=
    decide (a.2.2.2.1 < (p.n b).f x (dec a.1:History).1)
lemma testK (b):Kn (p.test b):= Kn.next.right.right.left.lt
        ((p.n b).runs.comp ((Kn.unpack (α:=History)).comp Kn.first).left)

def pointer (b:Bool) (x:Word) (a:Slip) :=
    let h:Comb:=dec a.2
    postcard ((p.route b).f x ((dec a.1:History).1,h.2.2.1))
                (p.era x a.1-h.1)
lemma pointerK (b):Kn (p.pointer b):=by
   have ht : Kn (fun (_:Word)(a:Slip)=> (dec a.2:Comb)):=Kn.unpack.comp Kn.next
   have hp : Kn (fun (_:Word)(a:Slip)=> (dec a.1:History)):=Kn.unpack.comp Kn.first
   exact Kn.wash.comp (((p.route b).runs.comp (hp.left.tuple ht.right.right.left)).tuple
                      ((p.eraK.comp Kn.first).sub ht.left))

def inflate (a:Comb): ℕ×ℕ := (enc a,0)
lemma inflateK: Kn (fun (_:Word)(a:Ream)=> inflate a.2) :=
          (Kn.wash.comp Kn.next).tuple (Kn.fix _)
def plusone (b:Bool)(w:Wgt)(x:ℤ):Wgt:= if b then (w.1+x,w.2) else (w.1,w.2+x)
def score (b:Bool)(a:Comb)(d:ℤ) :Comb :=
   let (x,y,i,w):=a
   (x,y,i+1, plusone b w (y*d))
def backq (b:Bool)(_ : Word)(a:Lore (ℕ×ℕ)) :Comb :=
   score b (dec a.2.1) (dec a.2.2)
lemma backK (b): Kn (backq b) := by
    have h:Kn (fun (_:Word)(a:Lore (ℕ×ℕ))=>(dec a.2.1:Comb)):=Kn.unpack.comp Kn.next.left
    have hp:Kn (fun (_:Word)(a:Lore (ℕ×ℕ))=>(dec a.2.2:ℤ)):=Kn.unpack.comp Kn.next.right
    have hz:=h.right.left
    have hw:=h.right.right.right
    have hc := hz.ZofN.prodZ hp
    cases b
    · exact h.left.tuple (hz.tuple (h.right.right.left.succ.tuple
                   (hw.left.tuple (hw.right.plusZ hc))))
    exact h.left.tuple (hz.tuple (h.right.right.left.succ.tuple
                   ((hw.left.plusZ hc).tuple hw.right)))

def march (_:Word) (a:Ream):Comb :=
   let (i,f,_,r):=a.2
   (i+1,f*2,0,r)
lemma marchK:Kn march:=Kn.next.left.succ.tuple
                ((Kn.next.right.left.times (Kn.fix 2)).tuple ((Kn.fix _).tuple Kn.next.right.right.right))

def hoop (_:Word)(a:Ream):Comb:=(a.2.1,a.2.2.1,0,a.2.2.2.2)
lemma hoopK: Kn hoop:=Kn.next.left.tuple (Kn.next.right.left.tuple
                       ((Kn.fix _).tuple Kn.next.right.right.right))

def per (b:Bool):Cog:=
   .seq (etch _ inflateK) (.seq (Cog.focus ⟨_,p.pointerK b⟩ (p.scans b)) (etch _ (backK b)))
def throughout (b:Bool):Cog:= .loop (gear _ (p.testK b)) (p.per b)
def coal :Cog:= .seq (p.throughout true) (.seq (etch _ hoopK)
                        (.seq (p.throughout false) (etch _ marchK)))
abbrev start: Comb:=(0,1,0,(0,0))
def cold :Cog:= .loop (gear _ p.stillK) p.coal
def astir :Cog:= .seq (etch (α:=ℕ) (fun _ _=> start) (Kn.fix _)) p.cold

end Oven
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter Finset
namespace Oven
variable (p:Oven)(a:Port)

abbrev ext (t:ℕ):ℕ := t+p.margin.f a.l.x a.info
abbrev labels (b:Bool):= (p.n b).f a.l.x a.info
def rel (p:Oven)(a:Port)(b:Bool)(i:ℕ):Port := {a with info:=(p.route b).f a.l.x (a.info,i)}
structure Thaw (k T:ℕ) (w:DW)(F:EV) : Prop where
    pos:100≤k
    ht:a.OK
    low:p.margin.f a.l.x a.info≤ k*a.d
    count:∀ b,p.labels a b< (2:ℕ)^(k*a.d)
    child : ∀ b i, i<p.labels a b →
          (p.rel a b i).Feeds (p.scans b) k (p.ext a T) (w b i) (F b i)

def bank (w:ℕ→Tape)(t i z:ℕ):ℤ :=
   ∑ j∈range z, ((2:ℤ)^i)*dsign (w j) (t-i)
def sums (w:ℕ→Tape)(n t i:ℕ):ℤ :=
   ∑ r∈range i, bank w t r n
def evenH (w:DW)(b:Bool)(H i:ℕ):ℤ :=
   sums (w b) (p.labels a b) H i
def chart (w:DW) (H x :ℕ)(j i:ℕ) : Comb :=
    (x,2^x,i,
       p.evenH a w true H x+ bank (w true) H x j, p.evenH a w false H x+
                                             bank (w false) H x i)

def chT (w:DW)(H x:ℕ)(j:ℕ):Comb :=
   let (u,y,_,r):=p.chart a w H x j 0
   (u,y,j,r)
def chF (w:DW)(H x:ℕ)(i:ℕ):Comb:=p.chart a w H x (p.labels a true) i

def perch (w:DW)(H x:ℕ)(b:Bool)(i:ℕ):Comb:= if b then p.chT a w H x i else p.chF a w H x i

lemma bank_step (w:ℕ→Tape) (H x i:ℕ): bank w H x (i+1)= bank w H x i+(2:ℤ)^x*dsign (w i) (H-x):=
   sum_range_succ _ _

lemma ave (w:DW)(H x:ℕ)(b:Bool)(i:ℕ):
    p.perch a w H x b (i+1) = score b (p.perch a w H x b i) (dsign (w b i) (H-x)):=by
   cases b <;> simp [score,perch,plusone,chT,chF,chart,bank_step,add_assoc]

lemma enrol (w:DW)(H x q):
    hoop a.l.x (q,p.chT a w H x (p.labels a true))= p.chF a w H x 0:=rfl
lemma progress (w:DW)(H x q):
    march a.l.x (q,p.chF a w H x (p.labels a false))=p.chT a w H (x+1) 0:=by
   simp [march,chF,chT,chart,evenH,sums,bank,sum_range_succ,pow_succ]
lemma sum_data (w:ℕ→Tape) (n t:ℕ) :
    sums w n t (t+1)=∑ i∈range n,w i t:=by
    rw [sums]; unfold bank; rw [sum_comm]
    refine sum_congr rfl fun j hj=>?_
    simpa [mul_comm] using suffixes (w j) t
lemma finished (w:DW)(H):
   p.chT a w H (H+1) 0= (H+1,2^(H+1),0,
                ∑ i∈range (p.labels a true),w true i H, ∑ i ∈ range (p.labels a false),w false i H):= by
   simp [chT,chart,evenH,sum_data,bank]

namespace Thaw
variable {p a k w F T}(h:p.Thaw a k T w F)
include h
lemma windy {b H i m}(ht:H≤p.ext a T)(hv:m≤p.labels a b):
   |bank (w b) H i m| ≤ 6*(m:ℤ)*2^i:=by
   induction m with
   | zero=> simp [bank]
   | succ m ih=>
     have he:=ih (by omega)
     have hp := safe_d (h.child b m hv).1 (show H-i≤p.ext a T by omega)
     have hm : |dsign (w b m) (H-i)|≤(6:ℤ):= by
       rw [abs_le]; omega
     rw [bank_step]
     apply le_trans (abs_add_le _ _)
     push_cast
     rw [abs_mul,abs_of_nonneg (show 0 ≤ (2:ℤ)^i by positivity)]
     nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ (2:ℤ)^i by positivity)]

lemma timed {b H i}(ht:H≤p.ext a T):
    |p.evenH a w b H i| ≤ 6*p.labels a b*((2:ℤ)^i-1):=by
    induction i with
    | zero=>simp [evenH,sums]
    | succ i ih=>
      have hh:p.evenH a w b H (i+1) =
         p.evenH a w b H i+bank (w b) H i (p.labels a b):=sum_range_succ _ _
      rw [hh,pow_succ]
      apply le_trans (abs_add_le _ _)
      linarith [h.windy (b:=b) (i:=i) ht le_rfl]

lemma cutL {b H i n}(ht:H≤p.ext a T)(he:n≤p.labels a b):
    lb (enc (p.evenH a w b H i+bank (w b) H i n)) ≤ 3*(5+k*a.d+i)+2:= by
    let m:=p.labels a b
    let v:=p.evenH a w b H i+bank (w b) H i n
    apply Zbound _ _ (by omega)
    have hp: |v|≤12*m*(2:ℤ)^i:= by
       unfold v
       apply (abs_add_le ..).trans
       have hc: (n:ℤ) ≤ m:=by exact_mod_cast he
       have hh: |p.evenH a w b H i|≤6*m*((2:ℤ)^i-1):=h.timed ht
       nlinarith [h.windy (i:=i) ht he,mul_le_mul_of_nonneg_right hc (show 0 ≤ (2:ℤ)^i by positivity)]
    have hc: v.natAbs ≤ 12*m*2^i:=by
       have hg : ((v.natAbs:ℕ):ℤ)=|v|:=Int.natCast_natAbs v
       exact_mod_cast le_trans hg.le hp
    change v.natAbs < _
    rw [pow_add,pow_add]
    have hz:= h.count b
    change m < _ at hz
    apply hc.trans_lt
    apply Nat.mul_lt_mul_of_pos_right (show 12*m<2^5*2^(k*a.d) by omega) (by positivity)

lemma seed_size {b H i n}(ht:H≤p.ext a T)(hn:n≤p.labels a b):
    lb (enc (p.perch a w H i b n))+1 ≤ 200*(i+k*a.d):= by
   have he:k*a.d≥1:=by have hk:=h.pos; have hh:=h.ht.1; exact Nat.mul_pos (by omega) hh
   have h1:=lb_shift i; have h2:=lb_le_inc i
   have hg:=modest (lt_of_le_of_lt hn (h.count b)) he
   have hi(x y:ℤ) (he1:lb (enc x)≤3*(5+k*a.d+i)+2)(he2:lb (enc y)≤3*(5+k*a.d+i)+2):
          lb (enc ((i,2^i,n,x,y):Comb))+1 ≤ 200*(i+k*a.d):=by
     have hq0:=measure_pair x y
     have hq1:=measure_pair n (x,y)
     have hq2:=measure_pair ((2:ℕ)^i) (n,x,y)
     have hq3:=measure_pair i ((2:ℕ)^i,n,x,y)
     change Relay.measure _+1≤_
     change Relay.measure x≤_ at he1
     change Relay.measure y≤_ at he2
     change Relay.measure ((2:ℕ)^i)=_ at h1
     change Relay.measure i≤_ at h2
     change Relay.measure n≤_ at hg
     omega
   cases b
   · exact hi _ _ (h.cutL ht le_rfl) (h.cutL ht hn)
   exact hi _ _ (h.cutL ht hn) (h.cutL ht (Nat.zero_le _))

end Thaw
end Oven
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter Finset
namespace Oven

def bill (k:ℕ):=500*k
abbrev price (k:ℕ):=4*bill k
namespace Thaw

variable {p:Oven} {a:Port} {k w F T}(h:p.Thaw a k T w F)
include h
omit h in
lemma age {t}(ht:t≤T):p.ext a t≤p.ext a T:= Nat.add_le_add_right ht _

lemma mounted {b T' t i n} (ht:t≤T)(he:T'=p.ext a t)(hi:i≤T'+1) (hn:n≤p.labels a b):
    span (bill k) a.d t (T'-i) (lb (enc (p.perch a w T' i b n))+1):= by
   have hc := h.seed_size (T:=T) (ht:=he ▸ (Oven.Thaw.age (p := p) (a := a) ht)) (i:=i) hn
   have hw:= h.pos; have hs := h.low; have hp:= h.ht.1
   let j:=T'-i
   have hj:j+i ≤ t+k*a.d+1:=by
      unfold j; unfold ext at he; omega
   unfold span bill
   change _ + 500*k*j ≤ _
   have hu:200 ≤500*k:=by omega
   have hl:(500*k)*(k+2) ≤500*k*(500*k):=by nlinarith
   have hz:(500*k)*(k*a.d+1)+200*k*a.d≤(500*k)*(500*k)*a.d:=by
        nlinarith [Nat.mul_le_mul_right a.d hl,Nat.mul_le_mul_left k hp]
   nlinarith [Nat.mul_le_mul_right i hu,Nat.mul_le_mul_left (500*k) hj]
lemma admits {b H t i n} (ht:t≤T)(he:H=p.ext a t)(hi:i≤H+1)(hn:n≤p.labels a b):
    a.l.state (price k) ⟨a.w,t⟩ (a.s (enc (p.perch a w H i b n))) := by
    refine ⟨h.ht.2.2,?_⟩
    have hc0:= h.pos
    have hp:1≤bill k:=by unfold bill; omega
    apply movespan _ h.ht.2.1
    have hs:=span_mono (h.mounted ht he hi hn) (D:=price k) (by unfold price; omega) hp
    unfold span price at *
    dsimp only at *
    omega

omit h in
lemma postcardQ (t): p.era a.l.x (postcard a.info t)=p.ext a t:=by simp [era, postcard,ext]
omit h in
lemma frameon (b:Bool) (H i n:ℕ) : (p.perch a w H i b n).1=i ∧ (p.perch a w H i b n).2.2.1=n:= by
    cases b <;> simp [perch,chT,chF,chart]

lemma frequent (b:Bool) {H t i n} (ht:t≤T)(he:H=p.ext a t)(hi:i≤H)(hn:n<p.labels a b):
    a.comp t (price k) (p.per b) (a.s (enc (p.perch a w H i b n)))
                                      (a.s (enc (p.perch a w H i b (n+1)))):= by
   let o:= p.perch a w H i b n
   let z:=p.rel a b n
   let f:=p.scans b
   have hv : z.comp (H-i) k f (z.s 0) (z.s (enc (dsign (w b n) (H-i)))) :=
               (h.child b n hn).2.digits _ ((Nat.sub_le ..).trans (he ▸ (Oven.Thaw.age (p := p) (a := a) ht)))
   let g (b:Bool) :Cub Slip ℕ := ⟨p.pointer b,p.pointerK b⟩
   have hh:p.pointer b a.l.x (postcard a.info t, enc o)=postcard z.info (H-i):= by
      have hr:o.2.2.1=n:=((frameon (p := p) (a := a) (w := w)) b H i n).2
      have hz:o.1=i:=((frameon (p := p) (a := a) (w := w)) b H i n).1
      dsimp only [pointer]; rw [dec_round,hr,hz,(postcardQ (p := p) (a := a)),← he]
      simp [rel,postcard,z]
   have ht1:=h.pos
   have hw:a.comp t (price k) (Cog.focus (g b) (p.scans b))
       (hold (enc o) (z.s 0)) (hold (enc o) (z.s (enc (dsign (w b n) (H-i))))) :=
         Cog.focus_word _ hv hh (h.mounted ht he (Nat.le_trans hi (by omega)) hn.le) h.ht.2.1
           (by unfold price bill; omega) (by omega) (by unfold bill; omega)
   refine .seq ?_ (.seq hw ?_)
   · exact etches _ _ (i:=o) rfl (h.admits ht he (hi.trans (by omega)) hn.le) hw.spots.1
   refine etches _ _ (i:=((enc o,enc (dsign (w b n) (H-i))):ℕ×ℕ))
                  ?_ hw.spots.2 (h.admits ht he (show i ≤ H+1 by omega) hn)
   simp [backq,o, p.ave]

omit h in
lemma testH (b:Bool)(H i n t):
   (gear _ (p.testK b)).f a.l.x (postcard a.info t,Pause (p.perch a w H i b n) a.src)=
                  decide (n<p.labels a b):=by
   rw [gear_at]; simp [test,postcard,((frameon (p := p) (a := a) (w := w)) b H i n).2,labels]

lemma throughoutH {H t i n} (b:Bool)(ht:t≤ T) (he:H=p.ext a t)(hi:i≤H)(hn:n≤p.labels a b):
     a.comp t (price k) (p.throughout b)
       (Pause (p.perch a w H i b n) a.src)
       (Pause (p.perch a w H i b (p.labels a b)) a.src) := by
   induction hn using Nat.decreasingInduction with
   | self=> exact .stop (by rw [(testH (p := p) (a := a) (w := w))]; simp) (h.admits ht he (hi.trans (by omega)) le_rfl)
   | of_succ n hf ih=> exact .more (by rw [(testH (p := p) (a := a) (w := w))]; simp [hf])
                                  (h.frequent b ht he hi hf) ih

lemma followQ {H i t}(ht:t≤T)(he:H=p.ext a t)(hi:i≤H):
   a.comp t (price k) p.coal (Pause (p.chT a w H i 0) a.src) (Pause (p.chT a w H (i+1) 0) a.src):=by
   have hz := h.throughoutH true ht he hi (Nat.zero_le _)
   have hu := h.throughoutH false ht he hi (Nat.zero_le _)
   have hp := h.admits ht he (Nat.succ_le_succ hi) (Nat.zero_le (p.labels a true))
   refine .seq hz (.seq ?_ (.seq hu ?_))
   · exact etches _ _ (p.enrol a w H i _) hz.spots.2 hu.spots.1
   exact etches _ _ (p.progress a w H i _) hu.spots.2 hp

omit h in
lemma icy (H i t):
   (gear _ p.stillK).f a.l.x (postcard a.info t,Pause (p.chT a w H i 0) a.src)=
                       decide (i ≤ p.ext a t):=by
    rw [gear_at]; simp [still,chart,chT,(postcardQ (p := p) (a := a)) t]

lemma gloveQ {H i t}(ht:t≤T)(he:H=p.ext a t)(hi:i≤H+1):
   a.comp t (price k) p.cold (Pause (p.chT a w H i 0) a.src)
                                  (Pause (p.chT a w H (H+1) 0) a.src):= by
   induction hi using Nat.decreasingInduction with
   | self=> exact .stop (by rw [(icy (p := p) (a := a) (w := w)),he]; simp) (h.admits (b:=true) (i:=H+1) (n:=0) ht he le_rfl (Nat.zero_le (p.labels a true)))
   | of_succ i hi ih=> exact .more (by rw [(icy (p := p) (a := a) (w := w)),← he]; simp; omega)
                          (h.followQ (i:=i) ht he (by omega)) ih

lemma finds {H t}(ht:t≤T)(he:H=p.ext a t):
   a.comp t (price k) p.astir (a.s 0) (Pause (p.chT a w H (H+1) 0) a.src):= by
   have hz := h.gloveQ ht he (Nat.zero_le _)
   refine .seq (etches (α:=ℕ) (i:=0) _ _ ?_ (a.stale h.ht t (price k) ?_) hz.spots.1) hz
   · simp [start,chT,chart,evenH,bank,sums]
   · have ht:=h.pos; unfold price bill; omega

end Thaw
end Oven
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter

def codeQ (z:ℤ) := (z%32).toNat
def diffd (n m:ℕ):ℤ :=
   (((n:ℤ)-2*m+16)%32)-16
lemma rangeQ (z:ℤ) : codeQ z≤ 31:=by unfold codeQ; omega
lemma resolve {n m:ℤ} (h: (n-2*m).natAbs ≤ 6) :
    diffd (codeQ n) (codeQ m)= n-2*m:=by
   unfold codeQ diffd; omega
lemma codeK {α} [Wire α] {f:PT α ℤ}(h:Kn f):Kn (fun x a=>codeQ (f x a)):=
   ((Kn.modulus h (Kn.fix 31))).topNat

lemma sandK : Kn (fun (_:Word)(a:ℕ×ℕ)=> diffd a.1 a.2):= by
   have ht:Kn (fun (_:Word)(a:ℕ×ℕ)=>a.1):=Kn.first
   have h1 := ht.ZofN.plusZ ( ((Kn.fix 2).prodZ (Kn.ZofN Kn.next)).negZ)
   have hh := (h1.plusZ (Kn.fix 16)).modulus (Kn.fix 31)
   convert hh.plusZ (Kn.fix (-(16:ℤ))) using 1
   ext x a; simp [diffd, sub_eq_add_neg]

def earlier (_:Word)(a:Slip):ℕ:=let (u,v):History:= dec a.1;
                                  postcard u (v-1)
lemma earlyK:Kn earlier:= by
   have h:= (Kn.unpack (α:=History)).comp (Kn.first (β:=ℕ))
   exact Kn.wash.comp (h.left.tuple h.right.pred)

def highZ (_:Word)(a:Lore ℕ):Bool:=decide ((dec a.1:History).2=0)
lemma highK: Kn highZ := ((Kn.unpack (α:=History)).comp Kn.first).right.eq (Kn.fix 0)

abbrev fromQ (_:Word)(a:Lore ℕ):ℕ×ℕ := (a.2,0)
lemma fromK : Kn fromQ:= Kn.tuple (Kn.next (α:=ℕ)) (Kn.fix 0)
def aheadQ (x:Word)(a:Lore ℕ) := let b:=fromQ x a; diffd b.1 b.2
lemma prev0K:Kn aheadQ:= Kn.comp (g:=fun _ (a:ℕ×ℕ)=>diffd a.1 a.2) sandK fromK

def liftarm (q:Cog):Cog :=
    .seq q (.bif (gear _ highK) (etch _ prev0K)
             (.seq (etch (α:=ℕ) (fun _ a=>((a.2,0):ℕ×ℕ)) (Kn.next.tuple (Kn.fix _)))
             (.seq (Cog.focus ⟨_,earlyK⟩ q) (etch _ (sandK.comp Kn.next)))))

def Raised (p:Port)(c H:ℕ)(q:Cog)(w:Tape):Prop :=
   ∀ t≤H,p.comp t c q (p.s 0) (p.s (codeQ (w t)))
def powder (c:ℕ):=c+40
lemma lifting {p c H q w R}(h:p.OK)(hv:100≤ c)(hh:Raised p c H q w)(he:Checked w R H):
     p.Feeds (liftarm q) (powder c) H w R:= by
   have hz(v :ℤ) : lb (codeQ v)+1≤ 8:= by
      have he:=lb_mono (rangeQ v); rw [show lb 31=5 by rfl] at he; omega
   refine ⟨he,⟨fun t ht=>?_⟩⟩
   have hc:c ≤ powder c:=by unfold powder; omega
   have hb : 1≤c:= by omega
   let d:=dsign w t
   have hd: lb (enc d)+1 ≤ powder c * powder c:=by
      have he0:=lb_mono (slate_le _ (safe_d he ht))
      change lb (enc d)≤_ at he0
      have hh:lb capD≤20:=by decide
      change lb (bead 6 6)≤20 at hh
      nlinarith
   have hs(y:ℕ) := p.alone h t (powder c) (x:=y) (by omega)
   apply Lot.Mane.seq ((hh t ht).mono hc hb)
   by_cases hy:t=0
   · subst t
     apply Lot.Mane.yes
     · change (gear highZ highK).f _ (postcard p.info 0,Pause (codeQ (w 0)) p.src)=_
       rw [gear_at]; simp [highZ,postcard]
     · have hx:diffd (codeQ (w 0)) 0=dsign w 0:= by
           have he1:= safe_d he ht
           apply (resolve (n:=w 0) (m:=0) (by simpa [dsign] using he1)).trans
           simp [dsign]
       exact etches _ _ (i:=codeQ (w 0)) hx (((hh _ ht).mono hc hb).spots.2) (hs _ hd)
   · apply Lot.Mane.no
     · change (gear highZ highK).f _ (postcard p.info t,Pause (codeQ (w t)) p.src)=_
       rw [gear_at]; simp [highZ,postcard,hy]
     let G:Cub Slip ℕ:= ⟨_,earlyK⟩
     let a:=codeQ (w t)
     have ho:span 10 p.d t (t-1) (lb a+1):=by
        have hh:=h.1; have hz:=hz (w t)
        unfold span a; omega
     have hs0: p.comp t (powder c) (Cog.focus G q)
                 (hold a (p.s 0)) (hold a (p.s (codeQ (w (t-1))))) := by
       apply Cog.focus_word G (hh (t-1) (by omega)) ?_ ho h.2.1 (by unfold powder; omega) hb (by omega)
       simp [G,postcard,earlier]
     refine .seq ?_ (.seq hs0 ?_)
     · exact etches _ _ (i:=codeQ (w t)) rfl (((hh t ht).mono hc hb).spots.2) hs0.spots.1
     have hv := safe_d he ht
     rw [dsign,ite_eq_right hy] at hv
     exact etches _ _ (i:=((codeQ (w t),codeQ (w (t-1))):ℕ×ℕ)) ((resolve hv).trans (by simp [dsign,hy]))
                       hs0.spots.2 (hs _ hd)

end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter

abbrev Coin := ℤ×ℕ
namespace Coin
noncomputable def v (a:Coin):ℝ:=a.1/(a.2+1:ℕ)
def ofZ (a:ℤ):Coin:=(a,0)
def place (a:ℤ)(b:ℕ):Coin:=(a,b-1)
def neg (a:Coin):Coin:=(-a.1,a.2)
def join (a b:Coin):Coin:=
   place (a.1*((b.2+1:ℕ):ℤ)+ b.1*((a.2+1:ℕ):ℤ)) ((a.2+1)*(b.2+1))
def mult (a b:Coin):Coin:=place (a.1*b.1) ((a.2+1)*(b.2+1))
def inv (a:Coin) : Coin :=
    if a.1=0 then ofZ 0 else place
              (if 0≤a.1 then ((a.2+1:ℕ):ℤ) else -((a.2+1:ℕ):ℤ)) a.1.natAbs
def low (a b:Coin) := decide (a.1*((b.2+1:ℕ):ℤ) ≤ b.1*((a.2+1:ℕ):ℤ))
def minimum (a b:Coin):Coin:= if low a b then a else b
def maximum (a b:Coin):Coin:= if low a b then b else a

theorem place0 (a b)(h:1≤ b) : v (place a b)=(a:ℝ)/b:=by unfold v place; simp [show b-1+1=b by omega]
@[simp] lemma ofv (a):v (ofZ a)=(a:ℝ):=by simp [v,ofZ]
@[simp] lemma neg0 (a):v (neg a)=-v a:=by simp [v,neg,neg_div]
@[simp] lemma mul0 (a b):v (mult a b)=v a*v b:=by
    rw [mult,place0 _ _ (Nat.mul_pos (by omega) (by omega))]; simp only [v, Nat.cast_mul, Int.cast_mul]; rw [div_mul_div_comm]
@[simp] lemma add0 (a b):v (join a b)=v a+v b:=by
    rw [join, place0 _ _ (Nat.mul_pos (by omega) (by omega))]; simp only [v]; push_cast; field_simp
@[simp] lemma inv0 (a):v (inv a)=(v a)⁻¹:=by
   unfold inv; split
   · next he=> simp [he,v,ofZ]
   next he=>
     rw [place0 _ _ (by omega)]
     split
     · next h=>
       have ht: (a.1.natAbs:ℝ)=(a.1:ℝ):= by
          have he:a.1.natAbs=a.1.toNat:=by omega
          rw [he]; exact_mod_cast (show ((a.1.toNat:ℕ):ℤ)=a.1 by omega)
       rw [ht]; simp [v]
     · next h=>
       have ht: (a.1.natAbs:ℝ)=-(a.1:ℝ):= by
          have he:a.1.natAbs=(-a.1).toNat:=by omega
          rw [he]; exact_mod_cast (show (((-a.1).toNat:ℕ):ℤ)=-a.1 by omega)
       rw [ht]; simp only [v]; push_cast; field_simp
lemma low_eq (a b) : low a b=true ↔ v a ≤ v b:=by
   rw [v,v,div_le_div_iff₀ (by positivity) (by positivity),low,decide_eq_true_eq]
   norm_cast

@[simp] lemma min0 (a b):v (minimum a b)=min (v a) (v b):=by
    unfold minimum; split
    · next h=> simp [(low_eq _ _).1 h]
    · next h=> have ht:= low_eq a b; grind
@[simp] lemma max0 (a b):v (maximum a b)=max (v a) (v b):=by
    unfold maximum; split <;> have h:=low_eq a b <;> grind

def floor0 (a:Coin):ℤ:= a.1 / ((a.2+1:ℕ):ℤ)
lemma floorok (a:Coin): (floor0 a:ℝ)≤v a∧ v a ≤ (floor0 a:ℝ)+1:=by
   have h:(0:ℤ)<(a.2+1:ℕ):=by positivity
   have ht : 0<((a.2+1:ℕ):ℝ):=by positivity
   constructor
   · rw [v,le_div_iff₀ ht]
     exact_mod_cast (show floor0 a * ((a.2+1:ℕ):ℤ)≤ a.1 from (Int.le_ediv_iff_mul_le h).mp le_rfl)
   rw [v,div_le_iff₀ ht]
   have hp: a.1 < (floor0 a+1)*((a.2+1:ℕ):ℤ) := (Int.ediv_lt_iff_lt_mul h).mp (by dsimp only [floor0]; omega)
   exact_mod_cast hp.le

variable {α} [Wire α] {f g: PT α Coin}
lemma ofK {f:PT α ℤ}(h:Kn f): Kn (fun x a=>ofZ (f x a)) := h.tuple (Kn.fix 0)
lemma placeK {f:PT α ℤ}{g:PT α ℕ}(h:Kn f)(e:Kn g): Kn (fun x a=>place (f x a) (g x a)):=
    h.tuple e.pred
lemma negK (h:Kn f): Kn (fun x a=>neg (f x a)):= h.left.negZ.tuple h.right
lemma addaK (h:Kn f)(e:Kn g):Kn (fun x a=>join (f x a) (g x a)) :=
    placeK ((h.left.prodZ e.right.succ.ZofN).plusZ (e.left.prodZ h.right.succ.ZofN))
                  (h.right.succ.times e.right.succ)
lemma multK (h:Kn f)(e:Kn g):Kn (fun x a=>mult (f x a) (g x a)) :=
    placeK (h.left.prodZ e.left) (h.right.succ.times e.right.succ)
lemma lowerK (h:Kn f)(e:Kn g):Kn (fun x a=>low (f x a) (g x a)) :=
    (h.left.prodZ e.right.succ.ZofN).leZ (e.left.prodZ h.right.succ.ZofN)
lemma minK(h:Kn f)(e:Kn g):Kn (fun x a=>minimum (f x a) (g x a)):=(lowerK h e).cond h e
lemma maxK(h:Kn f)(e:Kn g):Kn (fun x a=>maximum (f x a) (g x a)):=(lowerK h e).cond e h
lemma floorK(h:Kn f):Kn (fun x a=>floor0 (f x a)):=h.left.chop h.right
lemma invK (h:Kn f):Kn (fun x a=> inv (f x a)):= by
   have he:= h.right.succ.ZofN
   convert h.left.absN.cond_eq (Kn.fix 0) (Kn.fix (ofZ 0))
           (placeK (((Kn.fix (α:=α) 0).leZ h.left).cond he he.negZ) h.left.absN) using 1
   ext x a <;> simp [inv]
end Coin
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter Finset

structure Meld where
   P:Oven
   f:Cub (ℕ×Coin×Coin) Coin

namespace Meld
variable (p:Meld)
open Oven
def result (x:Word)(a:Ream):Coin :=
   let (q,b):History:=dec a.1
   let s:=a.2.2.2.2
   let f:=a.2.2.1
   let u:=p.f.f x (q,Coin.place s.1 (f/2), Coin.place s.2 (f/2))
   Coin.mult (Coin.ofZ ((min f (2^b):ℕ):ℤ)) u

lemma resultK: Kn p.result:=by
   have ht:Kn (fun (_:Word)(a: Ream)=> (dec a.1:History)):=Kn.unpack.comp Kn.first
   have hz:Kn (fun (_:Word)(a:Ream)=>a.2):=Kn.next
   have hu:= hz.right.left
   have h1:= hu.div (Kn.fix 2)
   have h:= hz.right.right.right
   have hc:= p.f.runs.comp (ht.left.tuple ((Coin.placeK h.left h1).tuple (Coin.placeK h.right h1)))
   exact Coin.multK (Coin.ofK ((Kn.cap hu (Kn.fix 2) ht.right).ZofN)) hc

def word (x:Word)(a:Ream):ℕ := codeQ (Coin.floor0 (p.result x a))
lemma wordK:Kn p.word := codeK (Coin.floorK p.resultK)
def ran0: Cog := .seq p.P.astir (etch _ p.wordK)
def cooked := liftarm p.ran0

variable (a:Port)
def tally (F:EV)(b:Bool):ℝ :=
    ∑ i∈range (p.P.labels a b), F b i
def fp (w:DW)(H:ℕ)(b:Bool) :Coin :=
   Coin.place (∑ i∈range (p.P.labels a b),w b i H) (2^H)
abbrev plug (w:DW)(t:ℕ):Coin :=
   p.result a.l.x (postcard a.info t, p.P.chT a w (p.P.ext a t) (p.P.ext a t+1) 0)
abbrev out (w:DW):Tape := fun t=> Coin.floor0 (p.plug a w t)

structure Lip (L V:ℝ)(F:EV):Prop where
   on : |V|≤1
   ht : 1 ≤ L
   rate : L*4*(p.P.labels a true+p.P.labels a false+1:ℕ) ≤ 2^p.P.margin.f a.l.x a.info
   met : ∀ x y:Coin,
       |x.v-p.tally a F true|≤1 →
       |y.v-p.tally a F false|≤1 →
       |(p.f.f a.l.x (a.info,x,y)).v-V|≤L*(|x.v-p.tally a F true|+|y.v-p.tally a F false|)

lemma profile {T w k F} (h: p.P.Thaw a k T w F) {H} (hz:H≤p.P.ext a T)(b:Bool) :
     |(fp p a w H b).v-tally p a F b| ≤ 2*(p.P.labels a b)/(2:ℝ)^H := by
   let n:=p.P.labels a b
   have he : 0< (2:ℝ)^H:=by positivity
   have hp (j:ℕ) (hi:j<n) : |(w b j H:ℝ)/(2:ℝ)^H-F b j|≤2/(2:ℝ)^H := by
      have h1 := (h.child b j hi).1.2 H hz
      rw [div_sub' (ne_of_gt he),abs_div,abs_of_pos he,div_le_div_iff_of_pos_right he]
      simpa [mul_comm] using h1
   unfold fp tally; rw [Coin.place0 _ _ (Nat.one_le_pow _ _ (by omega))]
   push_cast; rw [sum_div,←sum_sub_distrib]
   calc
     _ ≤ _ := abs_sum_le_sum_abs ..
     _ ≤ ∑ _∈range n,2/(2:ℝ)^H:=sum_le_sum fun j hj=> hp j (mem_range.1 hj)
     _= _ := by simp [n]; ring

lemma plugv (w:DW)(t):
   (p.plug a w t).v=2^t*(p.f.f a.l.x (a.info,p.fp a w (p.P.ext a t) true,p.fp a w (p.P.ext a t) false)).v:=by
   let H:=p.P.ext a t
   unfold plug result
   rw [p.P.finished]; dsimp only
   rw [show ((dec (postcard a.info t)):History)=(a.info,t) from Wire.eq _]
   have hm: min (2^(H+1)) (2^t)=2^t:=min_eq_right
                      (Nat.pow_le_pow_right (Nat.zero_lt_two) (by unfold H Oven.ext; omega))
   have hz(h): (2^(h+1))/2=(2:ℕ)^h:=by rw [pow_succ]; omega
   change (Coin.mult (Coin.ofZ ((min (_^(H+1)) (2^t):ℕ):ℤ)) _).v=_
   rw [hm]; unfold fp; simp only [Coin.mul0,Coin.ofv,hz]; norm_cast

theorem recipe {k T w F L V}(h:p.P.Thaw a k T w F)(hl:p.Lip a L V F):
    Checked (p.out a w) V T := by
   refine ⟨hl.on,fun t ht=>?_⟩
   let H:=p.P.ext a t
   let E:= (2:ℝ)^t
   let D:= (2:ℝ)^H
   let x:=p.fp a w H true
   let y:=p.fp a w H false
   have h1 := p.profile a h (Oven.Thaw.age (p := p.P) (a := a) ht) true
   have h2 := p.profile a h (Oven.Thaw.age (p := p.P) (a := a) ht) false
   have hu:=hl.ht; have hg:=hl.rate; push_cast at hg
   let M:=(2:ℝ)^p.P.margin.f a.l.x a.info
   let n:ℝ:=p.P.labels a true; let m:ℝ:=p.P.labels a false
   let e:=|x.v-p.tally a F true|; let d:=|y.v-p.tally a F false|
   change e≤ 2*n/D at h1
   change d≤ 2*m/D at h2
   have hv:0<D:=by dsimp [D]; positivity
   have he1:1≤ E:=one_le_pow₀ (by norm_num)
   have hm:1≤ M:=one_le_pow₀ (by norm_num)
   have hn:0≤n:=by dsimp [n]; positivity
   have hn2:0 ≤ m:=by dsimp [m]; positivity
   have hp:D=E*M:=by unfold D H Oven.ext; rw [pow_add]
   change L*4*(n+m+1) ≤ M at hg
   have hh : 2*(n+m)≤D:= by nlinarith [mul_le_mul_of_nonneg_right hu (show 0≤n+m by linarith)]
   rw [le_div_iff₀ hv] at h1 h2
   have hh1:e≤1:=by nlinarith
   have hh2:d≤1:=by nlinarith
   have heq:=hl.met _ _ hh1 hh2
   let Z:=(p.f.f a.l.x (a.info,x,y)).v
   change |Z-V|≤L*(e+d) at heq
   have hr:E*(L*(e+d)) ≤ 1:=by
      have h0: E* (L*(e+d))*D ≤ E*(L*(2*n+2*m)) :=by
          have hx := mul_le_mul_of_nonneg_left
                  (show (e+d)*D≤ 2*n+2*m by linarith)
                  (show 0≤ E*L by apply mul_nonneg <;> linarith)
          nlinarith
      have hx : E*(L*(2*n+2*m)) ≤ D:= le_trans (mul_le_mul_of_nonneg_left
                  (show L*(2*n+2*m)≤ M by nlinarith) (show 0≤E by linarith)) hp.symm.le
      nlinarith
   have heq1:|E*Z-E*V|≤1:=by
        rw [←mul_sub,abs_mul,abs_of_nonneg (show 0≤E by linarith)]
        exact (mul_le_mul_of_nonneg_left heq (show 0≤E by linarith)).trans hr
   have hz:=Coin.floorok (p.plug a w t)
   rw [p.plugv] at hz
   let Y:ℝ:=p.out a w t
   change Y ≤ E*Z ∧ E*Z≤Y+1 at hz
   change |Y-E*V| ≤2
   rw [abs_le] at heq1 ⊢; constructor <;> linarith

theorem stream {k T w F L V}(h:p.P.Thaw a k T w F)(hl:p.Lip a L V F):
    a.Feeds p.cooked (powder (price k)) T (p.out a w) V := by
   have hs:=h.pos
   have hp:100≤price k:=by unfold price bill; omega
   apply lifting h.ht hp _ (p.recipe a h hl)
   intro t ht
   have hz:= h.finds ht rfl
   have hB: lb (codeQ (p.out a w t))+1≤ price k*price k:=by
     have hq:=lb_mono (rangeQ (p.out a w t))
     rw [show lb 31=5 by rfl] at hq; nlinarith
   exact .seq hz (etches _ _ rfl hz.spots.2 (a.alone h.ht t (price k) (by omega) hB))

end Meld
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter Analysis Finset

abbrev countgt (S:Finset ℕ)(p:ℕ→ℕ)(v:ℕ):ℕ:= (S.filter fun i=> v < p i).card
abbrev countge (S:Finset ℕ)(p:ℕ→ℕ)(v:ℕ):ℕ:= (S.filter fun i=> v ≤ p i).card

def emin (S:Finset ℕ)(p:ℕ→ℕ)(k i:ℕ):Prop :=
    0<p i ∧ countgt S p (p i) ≤ k ∧ k < countge S p (p i)

lemma existsN (S:Finset ℕ)(p:ℕ→ℕ)(k:ℕ) :∃ v:ℕ, (v:ℝ)=rank S (fun i=>(p i:ℝ)) k := by
    classical
    let r:= fun i=>(p i:ℝ)
    have h:= rank_member S r k
    rw [rkSet,mem_insert] at h
    rcases h with h|h
    · exact ⟨0,by change (↑(0:ℕ):ℝ)=rank S r k; rw [h]; norm_num⟩
    obtain ⟨i,hi,e⟩:=mem_image.1 (mem_filter.1 h).1
    exact ⟨p i,e⟩
noncomputable def rankN (S:Finset ℕ)(p:ℕ→ℕ)(k:ℕ) := Classical.choose (existsN S p k)

lemma rankN_v (S:Finset ℕ)(p:ℕ→ℕ)(k:ℕ):
   (rankN S p k:ℝ)=rank S (fun i=>(p i:ℝ)) k:=by unfold rankN; exact Classical.choose_spec (existsN S p k)

lemma aboveN {S p k i}:
    i < rankN S p k ↔ k < countgt S p i:= by
   classical
   have h1:= @rank_gt ℕ S (fun j=>(p j:ℝ)) k (i:ℝ) (Nat.cast_nonneg _)
   rw [←rankN_v] at h1
   simpa [countgt] using h1
lemma topN {S p k i}(h:0 < i):
    i ≤ rankN S p k ↔ k < countge S p i:= by
   classical
   have h1:= @rank_ge ℕ S (fun j=>(p j:ℝ)) k (i:ℝ) (by exact_mod_cast h)
   rw [← rankN_v] at h1
   simpa [countge] using h1

lemma earns {S p k i}(h:emin S p k i):
    p i=rankN S p k∧0<rankN S p k:=by
    have he: rankN S p k ≤ p i:=le_of_not_gt (mt aboveN.1 (not_lt_of_ge h.2.1))
    have hg: p i ≤ rankN S p k:=(topN h.1).2 h.2.2
    exact ⟨le_antisymm hg he,lt_of_lt_of_le h.1 hg⟩
lemma excels {S p k}(h:0<rankN S p k):∃ i∈S,emin S p k i:= by
   classical
   let f:=fun j=>(p j:ℝ)
   have hh:=rank_member S f k
   unfold f at hh; rw [← rankN_v] at hh
   rcases mem_insert.1 hh with h1|h1
   · have hz: (0:ℝ)<↑(rankN S p k):=by exact_mod_cast h
     linarith
   obtain ⟨i,hi,e⟩:= mem_image.1 (mem_filter.1 h1).1
   have hk:p i=rankN S p k:= by exact_mod_cast e
   refine ⟨i,hi, hk.symm ▸ h, Nat.le_of_not_lt (by
      rw [← aboveN,hk]
      simp), (topN (hk.symm ▸ h)).1 hk.le⟩

lemma scaled_rank {S:Finset ℕ} {p:ℕ→ℝ}{k:ℕ}{L:ℝ}(h:0<L):
    rank S (fun i=>L*p i) k=L*rank S p k:= by
   classical
   let a:=rank S (fun i=>L*p i) k
   let b:=rank S p k
   have h1:=rank_nn S p k
   have h2:=rank_nn S (fun i=>L*p i) k
   change a=L*b
   by_contra! hx
   rcases lt_or_gt_of_ne hx with ht|ht
   · have hz:a/L<b:=(div_lt_iff₀ h).2 (by linarith)
     have hm:= (rank_gt (div_nonneg h2 h.le)).1 hz
     simp only [div_lt_iff₀ h] at hm
     suffices a<a by linarith
     rw [show a<a↔ k<(S.filter (fun i=>a<L*p i)).card from rank_gt h2]
     simpa only [a,mul_comm L] using hm
   · have dm:L*b<a:=ht
     have hm:= (rank_gt (mul_nonneg h.le h1)).1 dm
     suffices b<b by linarith
     apply (rank_gt h1).mpr
     simpa [h] using hm

lemma clipped_rank (S:Finset ℕ)(p:ℕ→ℝ)(k:ℕ) :
    rank S (fun i=>max 0 (p i)) k=rank S p k:= by
   classical
   let a:=rank S (fun i=>max 0 (p i)) k; let b:=rank S p k
   have h1:0≤a:=rank_nn ..; have h2:0≤b:=rank_nn ..
   by_contra hn
   change a≠b at hn
   rcases lt_or_gt_of_ne hn with he|he
   · have hm:= (rank_gt h1).mp he
     apply (lt_irrefl a)
     apply (rank_gt h1).mpr
     simpa only [lt_max_iff,not_lt.mpr h1,false_or] using hm
   · have e:= show b<a from he
     have hm:= (rank_gt h2).mp e
     apply (lt_irrefl b)
     apply (rank_gt h2).mpr
     simpa only [lt_max_iff,not_lt.mpr h2,false_or] using hm

lemma sweepV {S:Finset ℕ}{f:ℕ→ Tape}{V:ℕ→ℝ}{k H}
    (h:∀ i∈S,Checked (f i) (V i) H):
    Checked (fun t=> (rankN S (fun i=> (f i t).toNat) k:ℤ)) (rank S V k) H:=by
   have hp:=rank_nn S V k
   refine ⟨by rw [abs_of_nonneg hp]; exact rank_le (by norm_num) (fun i hi=> (abs_le.1 (h i hi).1).2),
              fun t ht=>?_⟩
   let a(i):ℝ:=f i t
   have hz:= rank_lip (s:=S) (f:=a) (g:=fun i=>2^t * V i) (K:=k) (show (0:ℝ)≤2 by norm_num)
                (fun i hi=>(h i hi).2 t ht)
   have he : (fun i=>max 0 (a i))=(fun i=> ((f i t).toNat:ℝ)):=by
       ext i; by_cases hk:0≤ f i t
       · rw [max_eq_right (by dsimp [a]; exact_mod_cast hk)]
         dsimp [a]; have hz : ((f i t).toNat:ℤ)=f i t:=by omega
         exact_mod_cast hz.symm
       rw [show (f i t).toNat=0 by omega]
       have hh0 := (show a i ≤ 0 by dsimp [a]; exact_mod_cast (by omega: f i t≤0))
       simp [hh0]
   rw [← clipped_rank S a, he,scaled_rank (by positivity)] at hz
   push_cast
   rw [rankN_v]
   exact hz
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Analysis Counter Finset

abbrev Exam:= ℕ×ℕ×ℕ
abbrev Hoard:= ℕ×ℕ×Exam×ℕ
structure Survey where
   n : Cub ℕ ℕ
   K : Cub ℕ ℕ
   goal : Cub (ℕ×ℕ) ℕ
   c : Cog

namespace Survey
variable (p:Survey)
def scrutiny (A B:ℕ):Exam:=(if A<B then 1 else 0, if A≤B then 1 else 0,
                                  if A=0 then 0 else codeQ A+1)
lemma scrK {α} [Wire α](f g:PT α ℕ)(h:Kn f)(e:Kn g) :
    Kn (fun x a=> scrutiny (f x a) (g x a)) :=
       (h.cond_lt e (Kn.fix _) (Kn.fix _)).tuple ((h.cond_le e (Kn.fix _) (Kn.fix _)).tuple
                  (h.cond_eq (Kn.fix 0) (Kn.fix _) (codeK h.ZofN).succ))

abbrev Fuse:= ℕ×ℕ×ℕ
def startP (b:Bool) (x:Word)(a:ℕ×ℕ) :=
   let q:Fuse:=dec a.1
   p.goal.f x (q.1,if b then q.2.1 else q.2.2)
lemma originK (b): Kn (p.startP b):=by
   have h:= (Kn.unpack (α:=Fuse)).comp (Kn.first (β:=ℕ))
   cases b
   · exact p.goal.runs.comp (h.left.tuple h.right.right)
   exact p.goal.runs.comp (h.left.tuple h.right.left)
def light : Oven := ⟨fun _=>⟨_,Kn.fix 1⟩,fun b=>⟨_,p.originK b⟩, ⟨_,Kn.fix 0⟩, fun _=>p.c⟩
def asses (_:Word)(a:Ream): Exam :=
    let v:=a.2.2.2.2
    scrutiny v.1.toNat v.2.toNat
lemma assesK:Kn asses:=scrK _ _
          Kn.next.right.right.right.left.topNat Kn.next.right.right.right.right.topNat
def fetchOne : Cog := .seq p.light.astir (etch _ assesK)

def passQ (_:Word)(a:Slip) :=
    let r:History:=dec a.1
    let s:Hoard:=dec a.2
    postcard (enc ((r.1,s.1,s.2.1):Fuse)) r.2
lemma passK:Kn passQ:= by
   have h:Kn (fun (_:Word)(a:Slip)=> (dec a.1:History)):=Kn.unpack.comp Kn.first
   have hz:Kn (fun (_:Word)(a:Slip)=> (dec a.2:Hoard)):=Kn.unpack.comp Kn.next
   exact Kn.wash.comp ((Kn.wash.comp (h.left.tuple (hz.left.tuple hz.right.left))).tuple h.right)
def held0 (_:Word)(a:Lore Hoard):ℕ×ℕ := (enc a.2,0)
lemma held0K:Kn held0:=(Kn.wash.comp Kn.next).tuple (Kn.fix _)

def chargeQ (a:Hoard)(b:Exam):Hoard:=
   let (i,j,(u,v,_),s):=a
   (i,j+1,(u+b.1,v+b.2.1,b.2.2),s)
def regain (_:Word)(a:Lore (ℕ×ℕ)):= chargeQ (dec a.2.1) (dec a.2.2)
lemma regainK:Kn regain:= by
    have h1:Kn (fun (_:Word)(a:Lore (ℕ×ℕ))=>(dec a.2.1:Hoard)):=Kn.unpack.comp Kn.next.left
    have h2:Kn (fun (_:Word)(a:Lore (ℕ×ℕ))=>(dec a.2.2:Exam)):=Kn.unpack.comp Kn.next.right
    have he:= h1.right.right.left
    exact h1.left.tuple (h1.right.left.succ.tuple
         (((he.left.add h2.left).tuple ((he.right.left.add h2.right.left).tuple h2.right.right)).tuple
             h1.right.right.right))
def moreB (b:Bool)(x:Word)(a:Lore Hoard) :=
    decide ((if b then a.2.1 else a.2.2.1)< p.n.f x (dec a.1:History).1)
lemma moreK (b):Kn (p.moreB b) := by
   have h := p.n.runs.comp ((Kn.unpack (α:=History)).comp (Kn.first (β:=Hoard))).left
   cases b
   · exact Kn.next.right.left.lt h
   exact Kn.next.left.lt h

def totalize (p:Survey)(x:Word)(a:Lore Hoard): Hoard :=
   let (i,_,(g,h,r),s):=a.2
   let k:=p.K.f x (dec a.1:History).1
   (i+1,0,(0,0,0), if g≤ k then if k<h then if r=0 then s else r-1 else s else s)
lemma totalK: Kn p.totalize:=by
    have h:= p.K.runs.comp ((Kn.unpack (α:=History)).comp (Kn.first (β:=Hoard))).left
    have hz:=Kn.next (α:=ℕ) (β:=Hoard)
    have he:=hz.right.right.left
    have hu:=hz.right.right.right
    exact hz.left.succ.tuple ((Kn.fix 0).tuple ((Kn.fix ((0,0,0):Exam)).tuple
        (he.left.cond_le h (h.cond_lt he.right.left (he.right.right.cond_eq (Kn.fix 0)
                          hu he.right.right.pred) hu) hu)))
def per : Cog := .seq (etch _ held0K) (.seq (Cog.focus ⟨_,passK⟩ p.fetchOne) (etch _ regainK))
def pane : Cog:= .loop (gear _ (p.moreK false)) p.per
def bulb : Cog:= .loop (gear _ (p.moreK true)) (.seq p.pane (etch _ p.totalK))
abbrev zeroQ:Hoard :=(0,0,(0,0,0),0)
def rtest :Cog := .seq (etch (α:=ℕ) (fun _ _=>zeroQ) (Kn.fix _))
             (.seq p.bulb (etch (α:=Hoard) (fun _ a=>a.2.2.2.2) Kn.next.right.right.right))
def poll:= liftarm p.rtest
end Survey
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill
open Relay Counter Finset Analysis
namespace Survey
variable (p:Survey)(a:Port)
abbrev topC:=p.n.f a.l.x a.info
abbrev targetK:=p.K.f a.l.x a.info
def oper (i:ℕ) :Port:={a with info:=p.goal.f a.l.x (a.info,i)}
def nest (_:Survey)(a:Port)(i j :ℕ):Port:={a with info:=enc ((a.info,i,j):Fuse)}
def priceB (k:ℕ):=100*Oven.price k
structure Clue (c T:ℕ) (F:ℕ→ℝ) (w:ℕ→Tape):Prop where
   cp:100≤ c
   ok:a.OK
   amp:p.topC a < 2^(c*a.d)
   bench:∀ i<p.topC a,(p.oper a i).Feeds p.c c T (w i) (F i)

namespace Clue
variable {p a c T F w}(h:p.Clue a c T F w)
include h
lemma coal (i j) (hi:i<p.topC a)(hj:j<p.topC a):
    p.light.Thaw (p.nest a i j) c T
                   (fun b _=> if b then w i else w j) (fun b _=> if b then F i else F j):=by
   refine ⟨h.cp,h.ok,Nat.zero_le _,fun b=>?_,fun b l _=>?_⟩
   · have hh:1≤c*a.d:= by have ht:=h.cp; have :=h.ok.1; nlinarith
     change 1< 2^(c*a.d); exact lt_of_lt_of_le (by omega:1< c*a.d+1) (growing _)
   · cases b
     · have hp:p.light.rel (p.nest a i j) false l=p.oper a j:=by
          simp [Oven.rel,light,startP,nest,oper]
       rw [hp]; exact h.bench j hj
     · have hp:p.light.rel (p.nest a i j) true l=p.oper a i:=by simp [Oven.rel,light,startP,nest,oper]
       rw [hp]; exact h.bench i hi
omit h in
lemma tight_exam (A B:ℕ):lb (enc (scrutiny A B))+1≤300:=by
    obtain ⟨a0,a1,a2⟩:=show (scrutiny A B).1≤1 ∧ (scrutiny A B).2.1≤1 ∧ (scrutiny A B).2.2≤32 from by
       unfold scrutiny; have hs := rangeQ (A:ℤ); grind
    generalize he:scrutiny A B=f at *
    rcases f with ⟨x,y,z⟩
    have he:= measure_pair x (y,z); have hf:=measure_pair y z
    change x≤1 at a0; change y≤1 at a1; change z≤32 at a2
    have ht: Relay.measure x≤lb 1:=lb_mono a0
    have hu: Relay.measure y≤lb 1:=lb_mono a1
    have hp:Relay.measure z≤lb 32:=lb_mono a2
    change Relay.measure (x,y,z)+1≤300
    rw [lb_one] at ht hu; rw [show lb 32=6 by rfl] at hp; omega
lemma bite {i j t}(ht:t≤T)(hi:i<p.topC a)(hj:j<p.topC a):
    (p.nest a i j).comp t (Oven.price c) p.fetchOne
            (a.s 0) (Pause (scrutiny (w i t).toNat (w j t).toNat) a.src):=by
   let v: DW:= fun b _ => if b then w i else w j
   have h1:= (h.coal i j hi hj).finds ht rfl
   let z:=p.nest a i j
   apply Lot.Mane.seq h1
   have hp:300≤Oven.price c:=by have he:=h.cp; unfold Oven.price Oven.bill; omega
   refine etches _ _ ?_ h1.spots.2 (z.alone h.ok _ _ ?_ ?_)
   · rw [Oven.finished]
     simp [asses,Oven.labels,light,Oven.ext]
   · omega
   have hc:= tight_exam (w i t).toNat (w j t).toNat
   nlinarith

lemma license0 {i j t s:ℕ} {e:Exam} (hi:i≤p.topC a)(hj:j≤p.topC a)
    (g1:e.1≤p.topC a)(g2:e.2.1≤p.topC a)(g3:e.2.2≤32)(g4:s≤32):
    span (Oven.price c) a.d t t (lb (enc ((i,j,e,s):Hoard))+1):=by
    rcases e with ⟨x,y,z⟩
    change x≤_ at g1; change y≤_ at g2; change z≤_ at g3
    have hl:=h.ok.1; have hp:=h.cp
    have HA:=h.amp
    have hh {t} (h:t≤p.topC a): Relay.measure t≤ c*a.d :=
        modest (h.trans_lt HA) (by nlinarith)
    have ht {p:ℕ}(h:p≤32): Relay.measure p≤6:=lb_mono (y:=32) h
    have hz:=measure_pair x (y,z); have hx:=measure_pair y z
    have hv:=measure_pair (x,y,z) s
    have hm:=measure_pair j ((x,y,z),s)
    have hu:=measure_pair i (j,(x,y,z),s)
    have h1:=hh hi; have h2:=hh hj; have h3:=hh g1; have h4:=hh g2
    have h5:=ht g3; have h6:=ht g4
    unfold span Oven.price Oven.bill
    have he1: Relay.measure ((i,j,(x,y,z),s):Hoard)+1 ≤ 100*(c*a.d+1):=by omega
    change Relay.measure ((i,j,(x,y,z),s):Hoard)+1+_≤_
    nlinarith [Nat.mul_le_mul_right a.d (show 200*c≤2000*c*(2000*c) by nlinarith)]

lemma good0 {i j t s : ℕ} {e:Exam} (hi:i≤p.topC a)(hj:j≤p.topC a)
    (g1:e.1≤p.topC a)(g2:e.2.1≤p.topC a)(g3:e.2.2≤32)(g4:s≤32):
    a.l.state (priceB c) ⟨a.w,t⟩ (Pause ((i,j,e,s):Hoard) a.src):= by
   have hz:= h.license0 (t:=t) hi hj g1 g2 g3 g4
   have hp := h.cp
   have ht:=span_mono hz (D:=priceB c) (by unfold priceB; omega)
                           (by unfold Oven.price Oven.bill; omega)
   refine ⟨h.ok.2.2,movespan ?_ h.ok.2.1⟩
   unfold span Pause at *; dsimp only; omega

end Clue
end Survey
end ExactDerandomization.Rill

end

section

namespace ExactDerandomization.Rill.Survey
open Relay Counter Finset Analysis

def residue (A:ℕ):ℕ := if A=0 then 0 else codeQ A+1
def sec (N:ℕ→ℕ)(i j:ℕ):Exam:=(countgt (range j) N (N i),countge (range j) N (N i),
                                       if j=0 then 0 else residue (N i))
lemma swing {w:ℕ→Prop}[DecidablePred w] (j:ℕ):
    ((range (j+1)).filter w).card=((range j).filter w).card+(if w j then 1 else 0):=by
   rw [range_add_one,filter_insert]
   split
   · next hx=> simp [hx]
   next hx=> simp []
lemma volley (N:ℕ→ℕ)(i j s:ℕ):
   chargeQ (i,j,sec N i j,s) (scrutiny (N i) (N j))=(i,j+1,sec N i (j+1),s):=by
   dsimp only [chargeQ,scrutiny,sec,countgt,countge,residue]
   simp only [swing, Nat.add_one_ne_zero,ite_false]
lemma sec0 (N:ℕ→ℕ)(i:ℕ):sec N i 0=(0,0,0):=by simp [sec,countgt,countge]
lemma secb (N:ℕ→ℕ)(i j:ℕ):
   (sec N i j).1≤j ∧ (sec N i j).2.1≤j ∧ (sec N i j).2.2≤32:=by
   dsimp only [sec,countgt,countge,residue]
   refine ⟨?_,?_,?_⟩
   · simpa using card_filter_le (range j) (fun x=> N i < N x)
   · simpa using card_filter_le (range j) (fun x=> N i≤N x)
   have he:=rangeQ (N i); grind

namespace Clue
variable {p:Survey} {a:Port} {c:ℕ} { T F w}(h:p.Clue a c T F w)
include h

private abbrev N (w:ℕ→Tape) (t i:ℕ) := (w i t).toNat

lemma rootP {i j t s}(hi:i≤p.topC a)(hj:j≤p.topC a)(hs:s≤32):
    a.l.state (priceB c) ⟨a.w,t⟩ (Pause ((i,j,sec (N w t) i j,s):Hoard) a.src):=
    let g:=secb (N w t) i j
    h.good0 hi hj (g.1.trans hj) (g.2.1.trans hj) g.2.2 hs

lemma pollen {i j t s}(ht:t≤T)(hi:i<p.topC a)(hj:j<p.topC a)(hs:s≤32) :
    a.comp t (priceB c) p.per (Pause ((i,j,sec (N w t) i j,s):Hoard) a.src)
          (Pause ((i,j+1,sec (N w t) i (j+1),s):Hoard) a.src):=by
   let G:Cub Slip ℕ := ⟨_,passK⟩
   let o:Hoard:=(i,j,sec (N w t) i j,s)
   let v:= scrutiny (N w t i) (N w t j)
   have ht0:=h.bite ht hi hj
   have hh:=secb (N w t) i j
   have hg:=h.cp
   have he:a.comp t (priceB c) (Cog.focus G p.fetchOne) (hold (enc o) (a.s 0))
                                      (hold (enc o) (Pause v a.src)) := by
      apply Cog.focus_word G ht0 ?_ (h.license0 hi.le hj.le (hh.1.trans hj.le) (hh.2.1.trans hj.le) hh.2.2 hs)
                     h.ok.2.1 (by unfold priceB; omega) (by unfold Oven.price Oven.bill; omega)
                                                 (by unfold Oven.price Oven.bill; omega)
      simp [G,passQ,postcard,nest]
   refine .seq (etches _ _ (i:=o) rfl (h.rootP hi.le hj.le hs) he.spots.1) (.seq he ?_)
   exact etches _ _ (i:=((enc o,enc v):ℕ×ℕ)) (by simp [regain,o,v,volley]) he.spots.2 (h.rootP hi.le hj hs)

omit h in
lemma checkplane (t i j e s b):
   (gear _ (p.moreK b)).f a.l.x (postcard a.info t,Pause ((i,j,e,s):Hoard) a.src)=
                    decide ((if b then i else j)<p.topC a):= by
   rw [gear_at]; simp [moreB,topC,postcard]
lemma field0 {i j t s}(ht:t≤T)(hi:i<p.topC a)(hj:j≤p.topC a)(hs:s≤32):
    a.comp t (priceB c) p.pane (Pause ((i,j,sec (N w t) i j,s):Hoard) a.src)
                     (Pause ((i,p.topC a,sec (N w t) i (p.topC a),s):Hoard) a.src):=by
   induction hj using Nat.decreasingInduction with
   | self=> exact .stop (by rw [(checkplane (p := p) (a := a))]; simp) (h.rootP hi.le le_rfl hs)
   | of_succ j hj ih=> exact .more (by rw [(checkplane (p := p) (a := a))]; simp [hj]) (h.pollen ht hi hj hs) ih
noncomputable def car (p:Survey)(a:Port)(w:ℕ→Tape)(t i:ℕ):ℕ := by
    classical
    exact if ∃ j < i, emin (range (p.topC a)) (N w t) (p.targetK a) j then
       codeQ (rankN (range (p.topC a)) (N w t) (p.targetK a)) else 0
omit h in
lemma carr (t i):car p a w t i≤32:= by
    unfold car; split <;> first | omega|exact le_trans (rangeQ _) (by omega)
omit h in
lemma intensity {i t}(hi:i<p.topC a):
    p.totalize a.l.x (postcard a.info t,i,p.topC a,sec (N w t) i (p.topC a), car p a w t i)=
           (i+1,0,sec (N w t) (i+1) 0,car p a w t (i+1)):=by
   classical
   let Q(j):Prop:= emin (range (p.topC a)) (N w t) (p.targetK a) j
   have hn:p.topC a≠0:=by omega
   rw [sec0]; unfold totalize; simp only [postcard,dec_round,sec,ite_eq_right hn]
   by_cases ht:Q i
   · obtain ⟨h1,h2,h3⟩:=ht
     have he: car p a w t (i+1)=codeQ (N w t i):=by
         unfold car; rw [ite_eq_left ⟨i,by omega,show Q i from ⟨h1,h2,h3⟩⟩, (earns (show Q i from ⟨h1,h2,h3⟩)).1]
     simp only [residue,show N w t i≠0 by omega,ite_false,he]; simp_all [targetK]
   · have he: car p a w t (i+1)=car p a w t i:=by
       have hl : (∃ j < i+1,Q j) ↔ ∃ j < i,Q j:=by
          constructor
          · rintro ⟨j,e,h⟩; refine ⟨j,?_ ,h⟩
            have hg : j ≠ i:=fun h0=>by subst j; contradiction
            omega
          rintro ⟨j,e,h⟩; exact ⟨j,by omega,h⟩
       unfold car; simp_rw [show (∃ j < i+1,emin ..) ↔ _ from hl]
       simp [Q]
     unfold Q emin targetK at ht
     rw [he]; unfold residue; grind

lemma stream0 {t i}(ht:t≤T)(hi:i≤p.topC a):
    a.comp t (priceB c) p.bulb (Pause ((i,0,sec (N w t) i 0,car p a w t i):Hoard) a.src)
         (Pause ((p.topC a,0,sec (N w t) (p.topC a) 0,car p a w t (p.topC a)):Hoard) a.src):= by
   induction hi using Nat.decreasingInduction with
   | self=> exact .stop (by rw [(checkplane (p := p) (a := a))]; simp) (h.rootP le_rfl (Nat.zero_le _) ((carr (p := p) (a := a) (w := w)) t _))
   | of_succ i hi ih=>
     have hp:=h.field0 ht hi (Nat.zero_le _) ((carr (p := p) (a := a) (w := w)) t i)
     refine .more (by rw [(checkplane (p := p) (a := a))]; simp [hi]) (.seq hp (etches _ _ ((intensity (p := p) (a := a) (w := w)) hi) hp.spots.2 ih.spots.1))
                   ih

lemma tasked :
    a.Feeds p.poll (powder (priceB c)) T
       (fun t=> (rankN (range (p.topC a)) (N w t) (p.targetK a):ℤ)) (rank (range (p.topC a)) F (p.targetK a)):= by
    have hp: 100≤priceB c:=by have hg:=h.cp; unfold priceB Oven.price Oven.bill; omega
    apply lifting h.ok hp
    · intro t ht
      have he := h.stream0 ht (Nat.zero_le _)
      have hx: car p a w t (p.topC a)=codeQ (rankN (range (p.topC a)) (N w t) (p.targetK a)):= by
         unfold car
         split <;> first | rfl|
           next hh=>
              generalize hA:rankN (range (p.topC a)) (N w t) (p.targetK a)=r
              by_cases hz : 0<r
              · rw [← hA] at hz; obtain ⟨i,hi,hk⟩:=excels hz; exact (hh ⟨_,mem_range.1 hi,hk⟩).elim
              rw [show r=0 by omega]; rfl
      refine .seq (etches _ _ (i:=0) ?_ (a.stale h.ok t (priceB c) (by omega)) he.spots.1)
              (.seq he (etches _ _ hx he.spots.2 ?_))
      · simp [car,sec0,zeroQ]
      apply a.alone h.ok t (priceB c) (by omega)
      have ht : lb (codeQ (rankN (range (p.topC a)) (N w t) (p.targetK a)))≤lb 31:=lb_mono (rangeQ _)
      rw [show lb 31=5 by rfl] at ht
      change lb (codeQ (rankN (range (p.topC a)) (N w t) (p.targetK a)))+1 ≤ _
      nlinarith
    exact sweepV (fun i hi=>(h.bench i (mem_range.1 hi)).1)
end Clue
end ExactDerandomization.Rill.Survey

end

end OAI
