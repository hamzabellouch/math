import OAI.Computability.Logspace.CompressionBounds
import OAI.Computability.Logspace.QueryPrograms

namespace OAI

/-!
Programs implementing sparse endpoint pools and row compression.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Reed
noncomputable section
open Buf Analysis Hie At Finset

/-! A single update view of a pool of endpoints.
Old slots are expressed as (their two coordinates minus the current
baseline). Identity of a slot includes its walk code, implemented but
not exposed to the real arithmetic except as a bit. -/
structure Poolx where
   p:Buf.Params
   raw:Blob
   m:ℕ
   tag:ℕ→ℕ
   place:ℕ→ℕ
   chip:ℕ→ Pt

namespace Poolx
variable (v:Poolx)
abbrev P:=range v.m
abbrev valid (i:ℕ):Prop:=v.tag i≠0
abbrev joins(i y:ℕ):Prop:=v.valid i∧v.place i=y
abbrev pals(i j:ℕ):Prop:=v.valid i∧ v.joins j (v.place i)
abbrev mayor (i:ℕ):Prop:=v.valid i ∧ ∀ j∈range i,¬v.pals i j
abbrev b:=v.raw.base
abbrev S:=v.p.S
def grainp (i j:ℕ): Pt:=if v.pals i j then v.chip j else 0
def meal (i:ℕ): Pt:= line v.b + ∑ j∈v.P,v.grainp i j

structure Nice (v:Poolx):Prop where
   baseM : 0  ≤  v.b ∧ v.b  ≤  4
   atS : ∀ i∈v.P,v.valid i→v.place i∈v.S
   plan : ∀ y∈v.S, v.raw.ts y=line v.b + ∑ j∈v.P,if v.joins j y then v.chip j else 0

namespace Nice
variable {v:Poolx}(h:Nice v)
include h
lemma serves {i:ℕ}(hi:i∈v.P)(he:v.valid i): v.meal i=v.raw.ts (v.place i):=by
   unfold meal; rw [h.plan _ (h.atS i hi he)]; unfold grainp pals; dsimp [valid] at *; simp [he]
lemma deserted {y:ℕ}(he:y∈v.S) (hg:∀ i∈v.P,¬v.mayor i ∨ v.place i≠y):
    v.raw.ts y=line v.b := by
    have hh(j)(hj:j∈v.P): ¬ v.joins j y:=by
       intro ht
       let s:= v.P.filter fun i=> v.joins i y
       have hc:s.Nonempty:=⟨j,mem_filter.2 ⟨hj,ht⟩⟩
       let i:=s.min' hc
       have hf:i∈s:=min'_mem ..; obtain ⟨h1,h2,h3⟩:=mem_filter.1 hf
       have hw:= (hg i h1).resolve_right (by simp only [h3]; simp)
       apply hw
       refine ⟨h2,fun l hl hu=>?_⟩
       have hx:= mem_range.1 hl
       have hv:l∈s:=mem_filter.2 ⟨mem_range.2 (hx.trans (mem_range.1 h1)),⟨hu.2.1,hu.2.2.trans h3⟩⟩
       exact not_lt_of_ge (min'_le _ _ hv) hx
    rw [h.plan y he]
    rw [sum_eq_zero]
    · simp
    intro j hj; rw [ite_eq_right (hh j hj)]

omit h in
lemma unique {i j:ℕ} (hi:v.mayor i)(hj:v.mayor j)(he:v.place i=v.place j):i=j:=by
   rcases lt_trichotomy i j with hs|hs|hs
   · exact False.elim (hj.2 i (mem_range.2 hs) ⟨hj.1,hi.1,he⟩)
   · exact hs
   exact False.elim (hi.2 j (mem_range.2 hs) ⟨hi.1,hj.1,he.symm⟩)
lemma citizens {i:ℕ} (he:i∈v.S)(hi:v.raw.ts i≠line v.b):∃ j∈v.P,v.mayor j∧v.place j=i:= by
   by_contra! hh
   apply hi (h.deserted he (fun j hj=> or_iff_not_imp_left.mpr (by by_contra hc; grind)))

def listP (v:Poolx)(f:Pt→ℝ)(i:ℕ):ℝ:= if v.mayor i then f (v.meal i) else 0

lemma sampled (f:Pt→ℝ)(hf:f (line v.b)=v.b){x:ℝ}(hp:v.b  ≤  x):
    (v.P.filter (fun i=>x<listP v f i)).card = (v.S.filter (fun j=>x< f (v.raw.ts j))).card:=by
    let P:=v.P.filter (fun i=> x<listP v f i)
    let S:=v.S.filter (fun j=> x<f (v.raw.ts j))
    have h0(i)(hi:i∈P): v.mayor i ∧ v.meal i=v.raw.ts (v.place i) := by
        obtain ⟨hx,he⟩:=mem_filter.1 hi
        unfold listP at he
        split at he
        · next hg=> exact ⟨hg,h.serves hx hg.1⟩
        have hl:=h.baseM.1; linarith
    have hl:P.image v.place=S:= by
       ext j; constructor
       · intro hx; obtain ⟨i,he,rfl⟩:=mem_image.1 hx
         obtain ⟨ha,hb⟩:=h0 i he; obtain ⟨he,hf'⟩:=mem_filter.1 he
         refine mem_filter.2 ⟨h.atS _ he ha.1,?_⟩
         unfold listP at hf'; rw [ite_eq_left ha,hb] at hf'; exact hf'
       intro he; obtain ⟨he,hg⟩:=mem_filter.1 he
       have hv:v.raw.ts j≠line v.b:=by intro hw; rw [hw,hf] at hg; linarith
       obtain ⟨i,hi,hA,hB⟩:=h.citizens he hv
       apply mem_image.2; refine ⟨i,mem_filter.2 ⟨hi,?_⟩,hB⟩
       unfold listP; rw [ite_eq_left hA,h.serves hi hA.1,hB]; exact hg
    change P.card=S.card
    rw [← hl]; symm; apply card_image_iff.mpr
    intro i hi j hj h1
    exact (unique (v := v)) (h0 i hi).1 (h0 j hj).1 h1

lemma staged (f:Pt→ℝ)(hf:f (line v.b)=v.b)(k):
    max v.b (rank v.P (listP v f) k)=max v.b (rank v.S (fun j=> f (v.raw.ts j)) k):=by
   have h0{x:ℝ}(hx:v.b ≤ x): (x<rank v.P (listP v f) k) ↔ (x<rank v.S (fun j=>f (v.raw.ts j)) k):=by
      have ht:=h.baseM.1.trans hx
      rw [rank_gt ht,rank_gt ht,h.sampled f hf hx]
   let a:=rank v.P (listP v f) k; let b:=rank v.S (fun j=>f (v.raw.ts j)) k
   have hh{x}: (x < max v.b a) ↔ (x < max v.b b):=by
      by_cases hv:x<v.b
      · simp [lt_max_iff,hv]
      rw [lt_max_iff,lt_max_iff]; exact or_congr Iff.rfl (h0 (le_of_not_gt hv))
   change max v.b a= max v.b b
   rcases lt_trichotomy (max v.b a) (max v.b b) with he|he|he
   · exact False.elim (lt_irrefl _ (hh.mpr he))
   · exact he
   exact False.elim (lt_irrefl _ (hh.1 he))
lemma higherEnd :
   v.p.U v.raw = min 4 (max v.p.rho (max v.b (rank v.P (listP v ht) v.p.n))):=by
   rw [h.staged ht (ht_line h.baseM.1)]; rfl
lemma middleEnd:
    v.raw.rk v.S v.p.K=max v.b (rank v.P (listP v Prod.fst) v.p.K):=by
   rw [h.staged Prod.fst rfl]; unfold Blob.rk; rw [max_comm]

abbrev U (v:Poolx):=v.p.U v.raw
abbrev Z (v:Poolx):=v.p.Z v.raw
lemma whole {B:Finset ℕ} (hp:B⊆v.P)(hb:U v <4)
     (he:∀ i∈B,v.mayor i ∧ U v< ht (v.meal i)): B.card  ≤  v.p.n:=by
   have hz: (B.image v.place).card=B.card:=card_image_iff.2 fun i hi j hj hx=>
             (unique (v := v)) (he i hi).1 (he j hj).1 hx
   rw [← hz]
   apply Params.enough v.p hb
   · intro j hj
     obtain ⟨i,h1,rfl⟩:=mem_image.1 hj
     exact h.atS _ (hp h1) (he _ h1).1.1
   intro j hj; obtain ⟨i,he1,rfl⟩:=mem_image.1 hj
   obtain ⟨ht,hv⟩:=he i he1; rw [← h.serves (hp he1) ht.1]; exact hv

lemma coverHome {B:Finset ℕ}(he:∀ i∈v.P,v.mayor i → 2*U v<ht (v.meal i) → i∈ B)
    (R:ℝ)(hr:4 ≤  R){j:ℕ}(hj:j∈v.S)(ht:j∉B.image v.place):
    (struck R (v.p.push v.raw)).ts j=line (Z v):=by
   apply v.p.listed R hr _ hj ht
   intro i hi hz
   have hh:v.raw.ts i ≠ line v.b:=by
      intro hg; rw [hg,ht_line h.baseM.1] at hz
      have ha:=v.p.U_old (v:=v.raw) h.baseM.2; have hp:=v.p.U_nn v.raw
      change _ ≤ _ at ha; linarith
   obtain ⟨k,hk,hA,hB⟩:=h.citizens hi hh
   have hh:k∈B:=he k hk hA (by rw [h.serves hk hA.1,hB]; exact hz)
   exact mem_image.2 ⟨k,hh,hB⟩
end Nice
end Poolx
end
end ExactDerandomization.Reed

end

section

namespace ExactDerandomization.Reed
open Counter Relay Rill Fret Buf Analysis Hie At Finset Seats
open Poolx
abbrev Stool:=ℕ × ℕ× ℕ
def film (s:Seats)(i j:ℕ):Seats:= s.panelx (enc ((s.info,i,j):Stool))
abbrev V (_:Word)(i:ℕ):Stool:=dec i
lemma VK:Kn V:=Kn.unpack

def rootsD (k:Cub ℕ ℕ): Cub ℕ ℕ:=
   ⟨fun x a=> k.f x (V x a).1,k.runs.comp VK.left⟩
def leftQ :Cub ℕ ℕ:=⟨fun x a=>(V x a).2.1,VK.right.left⟩
def stairs (rise:Bool)(x:Word)(a:History):ℕ:=
    let b:=V x a.1
    enc (if rise then ((b.1,a.2,0):Stool) else (b.1,b.2.1,a.2))
lemma stairK (b):Kn (stairs b):=by
    have h:=VK.comp (Kn.first (β:=ℕ))
    cases b
    · exact Kn.wash.comp (h.left.tuple (h.right.left.tuple Kn.next))
    exact Kn.wash.comp (h.left.tuple (Kn.next.tuple (Kn.fix _)))
def centra (x:Word)(i:ℕ):ℕ:= enc (((V x i).1,0,0):Stool)
lemma centerK:Kn centra:=Kn.wash.comp (VK.left.tuple (Kn.fix _))
def campk (p:Knob):Knob:=⟨rootsD p.height,rootsD p.bank,rootsD p.store⟩
lemma spread {s:Seats}{p} (h:s.stable p)(i j):(film s i j).stable (campk p):=by
    intro x hx; have he:=h x hx
    refine ⟨he.1,?_,?_⟩
    · change p.height.f _ (dec (enc ((s.info,i,j):Stool)):Stool).1=_
      rw [dec_round]; exact he.2.1
    change p.bank.f _ (dec (enc ((s.info,i,j):Stool)):Stool).1=_
    rw [dec_round]; exact he.2.2
lemma spanFilm {s:Seats}{p H}(h:Live s.head p H)(i j): Live (film s i j).head (campk p) H:=by
    change (2:ℕ)^H  ≤  p.store.f _ (dec (enc ((s.info,i,j):Stool)):Stool).1
    rw [dec_round]; exact h

def sideq (p:Pt)(b:Bool) := if b then p.1 else p.2
structure Board where
    n: Cub ℕ ℕ
    kth: Bool→Cub ℕ ℕ
    I:Knob
    equal0: Cog
    pigment: Cog
    baseC:Cog
    reserveC:Cog
    pot:Bool → Cog
    inp:ℕ
    lid:ℕ
    lips:ℕ
    cup:ℕ

namespace Board
noncomputable section
variable (p:Board)
def bridgeQ (b:Bool)(k:Cub ℕ ℕ):Branch:=⟨rootsD p.n,⟨_,stairK b⟩,k,p.cup⟩
lemma backBE (s:Seats) (b:Bool) i j k a:
   (film s i j).bench (p.bridgeQ b k) a=if b then film s a 0 else film s i a:=by
   cases b <;> simp [film,bench,Branch.port,stairs,panelx,bridgeQ]

@[simp] lemma numbers (s:Seats) (c:Cub ℕ ℕ) (i j): (rootsD c).f s.l.x (film s i j).info=c.f s.l.x s.info:=by
    simp [rootsD,film,info,panelx]
@[simp] lemma centeral (s:Seats) (i j) : centra s.l.x (film s i j).info=(film s 0 0).info:=by
    simp [centra,film,info,panelx]

abbrev R (p:Board)(s:Seats):=massB p.lid s.d
def gcat (v:Poolx)(i j:ℕ):ℕ:=if v.pals i j then 1 else 0

abbrev address (v:Poolx)(i:ℕ):Prop:=i=0∨i<v.m
/-- Supply over all seats and a common work horizon. Carry lip & reservoir budget abstract. -/
structure Holds (s:Seats)(c T:ℕ)(v:Poolx):Prop where
   pri : 4  ≤  c
   ball: v.Nice
   good: s.stable p.I
   horizon:Live s.head p.I T
   N : p.n.f s.l.x s.info=v.m
   cap : (p.kth true).f s.l.x s.info=v.p.K
   carry:(p.kth false).f s.l.x s.info=v.p.n
   volume : v.m<2^(p.cup*s.d)
   coverM:Punct s.head c v.m
   clampR: 4  ≤  p.R s
   costrho:(massB p.lips s.d)⁻¹  ≤  v.p.rho ∧ v.p.rho ≤  1
   baseU :∀ i,address v i→ (film s i 0).band c T p.inp p.baseC v.raw.base
   rhoQ :∀ i,address v i→ (film s i 0).band c T p.inp p.reserveC v.p.rho
   tagM :∀ i < v.m, (film s i 0).rite c p.pigment (v.tag i)∧ Punct s.head c (v.tag i)
   both :∀ i < v.m,∀ j < v.m, (film s i j).rite c p.equal0 (gcat v i j)
   glow :∀ i < v.m,∀ j < v.m,v.pals i j → ∀ b,(film s i j).band c T p.inp (p.pot b) (sideq (v.chip j) b)

def pollStack:Branch:={p.bridgeQ false ⟨_,Kn.fix 0⟩ with n:=leftQ}
def detective:Seek:= ⟨p.pollStack,p.equal0⟩
def offer:Cog:=Cargo.choose p.detective.latch p.pigment Seats.nothingX

abbrev postC(c:ℕ):=16*(16*c)
def solar(v:Poolx)(i:ℕ):ℕ:= if v.mayor i then v.tag i else 0
lemma nowEQ(v:Poolx)(i:ℕ):solar v i≠0 ↔ v.mayor i:=by
    unfold solar; split
    · next h=>exact iff_of_true h.1 h
    next h=>simp [h]

namespace Holds
variable {s:Seats}{p c T v}(h:Holds p s c T v)
include h
lemma hpos : 1 ≤ s.d:=(stable_home h.good).1.1
lemma act (i j):hasOK (film s i j):=rocks (spread h.good i j)
lemma lenpoll (i j) k b : (film s i j).freq (p.bridgeQ b k)=v.P:=by
    change range ((rootsD _).f s.l.x (film s i j).info)=_
    rw [numbers,h.N]
lemma book {i:ℕ}(he:i<v.m):
   (film s i 0).rite (postC c) p.offer (solar v i):=by
   let f:=film s i 0
   let q:=p.detective
   have hm:q.N f=i:=by simp [q,Seek.N, detective,pollStack,f,film,leftQ,info,panelx]
   have hz:=h.act i 0; have hx:=h.pri
   have hp:=q.earns hz (by omega:2  ≤  c) (gcat v i) (by
      rw [hm]; unfold Punct; exact le_trans (Nat.add_le_add_right (lb_mono he.le) _) h.coverM) (show ∀ j<q.N f,
      _ from fun j hj=>by
         rw [hm] at hj
         constructor
         · unfold gcat
           split
           · unfold Punct; rw [lb_one]; change 1+1  ≤  c*s.d; have he:=h.hpos; nlinarith
           exact punct0 (has_home hz) (by omega)
         have hg : f.bench q.b j=film s i j:=by simp [bench,f,q,detective,pollStack,film,panelx,bridgeQ,Branch.port,stairs]
         rw [hg]; exact h.both i he j (hj.trans he))
   dsimp only at hp
   change Punct f.head (4*c) (Seek.relief (gcat v i) 0 (q.N f)).2 ∧ _ at hp
   let r:= (Seek.relief (gcat v i) 0 i).2
   rw [hm] at hp
   have hh : r=0 ↔ ∀ j∈range i,¬v.pals i j:=by
      rw [show (r=0) ↔ _ from Seek.missed]; unfold Seek.part gcat
      constructor
      · intro hg j hj ht
        have hq:0<((range i).filter (fun j=> (if v.pals i j then 1 else (0:ℕ))≠0)).card:=
          card_pos.mpr ⟨j,mem_filter.2 ⟨hj,by rw [ite_eq_left ht]; omega⟩⟩
        omega
      intro hg
      rw [le_zero_iff,card_eq_zero]
      ext j
      simp only [mem_filter,notMem_empty,iff_false]
      rintro ⟨hj,hq⟩; rw [ite_eq_right (hg _ hj)] at hq; contradiction
   apply Seats.steer hp.2
   · intro hl; have hA:=hh.1 hl
     have hu :solar v i=v.tag i:=by unfold solar; split <;> grind
     rw [hu]; exact higher (h.tagM i he).1 (by omega) (by omega)
   intro hl
   have hu:solar v i=0:=ite_eq_right (fun hv=> hl (hh.2 hv.2))
   rw [hu]; exact Seats.blankD hz (by omega)

end Holds
end
end Board
end ExactDerandomization.Reed

end

section

namespace ExactDerandomization.Reed
open Counter Relay Rill Fret Buf Analysis Hie At Finset Seats Poolx Board
open Fret.Lyric

namespace Lu
def son (n i:ℕ):Lyric:=.solo i ⟨_,Kn.fix (Coin.ofZ n)⟩
abbrev psum:= bi .plus
abbrev diff:= bi .minus
abbrev times:=bi .prod
abbrev sup:=bi .greater
abbrev inf:=bi .lesser
abbrev zeroE:=son 0 0
def kohn(n:ℕ):Lyric:=son n n
abbrev absE (x:Lyric):=Lu.sup x (diff zeroE x)
abbrev clippy (R x:Lyric):=Lu.inf R (Lu.sup (diff zeroE R) x)
abbrev reset (x:Lyric)(w:ℕ):= Lyric.duet .plus x zeroE w
noncomputable section
structure Standard (s:Seats)(p:Knob)(T:ℕ): Prop where
    st : stable s p
    he : Live s.head p T
namespace Standard
variable {s p T}(h:Standard s p T)
include h
lemma shins(c i n:ℕ) (he:(n:ℝ) ≤ massB i s.d) : Chor p c T s (son n i) (n:ℝ):=by
    have hp : (Coin.ofZ n).v=(n:ℝ):=by simp
    rw [← hp]; apply Chor.played h.st h.he (fun x _=> rfl)
    rw [hp,abs_of_nonneg (by positivity)]; exact he
lemma rove (c n):Chor p c T s (kohn n) (n:ℝ):=h.shins c n n (swellB (stable_home h.st).1.1).le
lemma sil {c}: Chor p c T s zeroE 0:=by
    convert h.shins c 0 0 (by simp [massB]) using 1; norm_num
variable {c f g x y}
lemma up0 (he:Chor p c T s f x) (hg:Chor p c T s g y):Chor p c T s (Lu.sup f g) (max x y):=
     he.minuet hg h.st .greater
lemma lo0 (he:Chor p c T s f x) (hg:Chor p c T s g y):Chor p c T s (Lu.inf f g) (min x y):=
     he.minuet hg h.st .lesser
lemma additions (he:Chor p c T s f x) (hg:Chor p c T s g y): Chor p c T s (psum f g) (x+y):=
     he.minuet hg h.st .plus
lemma dubs (he:Chor p c T s f x) (hg:Chor p c T s g y): Chor p c T s (diff f g) (x-y):=
     he.minuet hg h.st .minus
lemma mult0 (he:Chor p c T s f x) (hg:Chor p c T s g y): Chor p c T s (times f g) (x*y):=
     he.minuet hg h.st .prod
lemma neg0 (he:Chor p c T s f x) : Chor p c T s (diff zeroE f) (-x):=by
    simpa using h.dubs h.sil he
lemma absti (he:Chor p c T s f x): Chor p c T s (absE f) |x|:= by
    have hp: |x|=max x (-x):=by exact abs_eq_max_neg
    rw [hp]; exact h.up0 he (h.neg0 he)
lemma clips (he:Chor p c T s f x)(hg:Chor p c T s g y): Chor p c T s (clippy f g) (sat x y):=
     h.lo0 he (h.up0 (h.neg0 he) hg)
lemma ring0 (he:Chor p c T s f x)(w)(hb:|x|  ≤  massB w s.d):Chor p c T s (reset f w) x:=by
    have ht:Doop.val .plus x 0=x:=add_zero _
    have hu:|Doop.val .plus x 0|  ≤  massB w s.d:=by rw [ht]; exact hb
    convert Chor.doo h.st he h.sil hu using 1; exact ht.symm
end Standard
end
end Lu

namespace Board
noncomputable section
open Lu
variable (p:Board)

def music (q:Cog):Cog:=Cargo.choose q
                     (Brick.solo (campk p.I) ⟨_,Kn.fix (Coin.ofZ 0)⟩ 0)
                     (Brick.solo (campk p.I) ⟨_,Kn.fix (Coin.ofZ 1)⟩ 0)
def warmth (p:Board):Lyric:= .use 0 (p.music p.offer)
def pit0 (p:Board):Cog:= Brick.solo (campk p.I) ⟨_,Kn.fix (Coin.ofZ 0)⟩ p.inp
def pit (p:Board)(b:Bool): Cog:= Cargo.choose p.equal0 p.pit0 (p.pot b)
abbrev goalCost (c:ℕ):=postC c+200
namespace Holds
variable {s:Seats}{p c T v}(h:Holds p s c T v)
include h
abbrev Cext (p:Board)(s:Seats)(c T i j:ℕ):= Chor (campk p.I) (goalCost c) T (film s i j)
lemma stifle (i j):Standard (film s i j) (campk p.I) T:=
   ⟨spread h.good i j,spanFilm h.horizon i j⟩
lemma currency : 1  ≤  c ∧ c ≤  goalCost c ∧ 1  ≤  goalCost c:=by have:=h.pri; unfold goalCost postC; omega
lemma chorus {i}(he:i<v.m): Cext p s c T i 0 (p.warmth) (if v.mayor i then 1 else 0):=by
   let f:=film s i 0
   let b:=goalCost c
   have hp:=h.stifle i 0; have hq:=h.pri
   have hz:f.rite b p.offer (solar v i):=higher (h.book he) (by unfold postC; omega) (by unfold b goalCost; omega)
   apply Chor.byear
   apply Seats.avis hz
   · intro hl
     rw [ite_eq_right (show ¬v.mayor i by intro e; exact ((nowEQ v i).2 e) hl)]
     have ht:=sing hp.sil (h.currency.2.2) (H:=T) (by simp [tail,zeroE,son])
     exact flex ht (by change 1  ≤  powder 100; unfold powder; omega)
             (by change powder 100  ≤  goalCost c; unfold goalCost powder; omega) le_rfl
   intro hl
   rw [ite_eq_left ((nowEQ v i).1 hl)]
   have hh:Cext p s c T i 0 (son 1 0) 1:=by
      convert hp.shins b 0 1 (by simp [massB]) using 1; norm_num
   exact flex (sing hh (h.currency.2.2) (H:=T) (by simp [son,tail])) (by change 1  ≤  powder 100; unfold powder; omega)
             (by change powder 100  ≤  goalCost c; unfold goalCost powder; omega) le_rfl

lemma slices {i j:ℕ}(hi:i<v.m)(hj:j<v.m)(b:Bool):
    Cext p s c T i j (.use p.inp (p.pit b)) (sideq (v.grainp i j) b):=by
   have hp:=h.stifle i j; have he:=h.currency
   apply Chor.byear
   apply Seats.avis (higher (h.both i hi j hj) he.1 he.2.1)
   · intro hl
     have hh :¬ v.pals i j:=by intro x; unfold gcat at hl; rw [ite_eq_left x] at hl; omega
     have ht:Cext p s c T i j (son 0 p.inp) 0:=by
        convert hp.shins (goalCost c) p.inp 0 (by simp) using 1; norm_num
     unfold Poolx.grainp; rw [ite_eq_right hh]
     have hh2:sideq 0 b=0:=by cases b <;> rfl
     rw [hh2]
     exact flex (sing ht (h.currency.2.2) (H:=T) (by simp [tail,son])) (by change 1 ≤  powder 100; unfold powder; omega)
             (by change powder 100  ≤  goalCost c; unfold goalCost powder; omega) le_rfl
   intro hh
   have hz:v.pals i j:=by by_contra hc; unfold gcat at hh; rw [ite_eq_right hc] at hh; contradiction
   unfold Poolx.grainp; rw [ite_eq_left hz]
   exact flex (h.glow i hi j hj hz b) he.1 he.2.1 le_rfl
end Holds

end
end Board
end ExactDerandomization.Reed

end

section

namespace ExactDerandomization.Reed.Board
open Counter Relay Rill Fret Buf Analysis Hie At Finset Seats Poolx Poolx.Nice Lu
open Fret.Lyric
noncomputable section
variable (p:Board)

def rowB (b:Bool):Lyric:= if b then .use p.inp p.baseC else zeroE
def bites (b:Bool):Lyric:=psu b
 where psu b:= Lu.psum (p.rowB b)
                  (.heap true (p.bridgeQ false ⟨_,Kn.fix 0⟩) (.use p.inp (p.pit b)))
abbrev rawP:= p.bites true
abbrev sight:= Lu.sup (absE p.rawP) (absE (p.bites false))
abbrev starsR (b:Bool):Lyric:=
    Lu.sup (p.rowB true) (.heap false (p.bridgeQ true (rootsD (p.kth b)))
                          (Lu.times p.warmth (if b then p.rawP else p.sight)))
abbrev riseR :Lyric:= Lu.inf (kohn 4) (Lu.sup (.use p.inp p.reserveC) (p.starsR false))
abbrev zenith :Lyric:= Lu.inf (kohn 4) (Lu.sup p.riseR (Lu.inf (p.starsR true)
                                                                      (Lu.times (kohn 3) p.riseR)))
abbrev border (b:Bool):Lyric := if b then p.zenith else zeroE
abbrev shore :Lyric := Lu.times (kohn 7) (Lu.sup zeroE (Lu.diff p.sight (Lu.times (kohn 2) p.riseR)))
abbrev surf (b:Bool):Lyric:=Lu.psum (p.border b) (clippy p.shore (Lu.diff (p.bites b) (p.border b)))
def topE:Lyric:= .solo p.lid ⟨fun x a=> scaleC (campk p.I) p.lid x a.1,
                                                        (scaleK (campk p.I) p.lid).comp Kn.first⟩
abbrev guardE (b:Bool):Lyric:=reset (clippy p.topE (p.surf b)) p.lid
abbrev borderE (b:Bool):Lyric:= reset (p.border b) p.lid
abbrev harsh : Lyric:=Lu.diff (Lu.times (kohn 2) p.sight) (Lu.times (kohn 3) p.riseR)

namespace Holds
variable {s:Seats}{p c T v}(h:Holds p s c T v)
include h

lemma rowUp {i}(hi:address v i)(b):Cext p s c T i 0 (p.rowB b) (sideq (Buf.line v.b) b):=by
   cases b
   · exact (h.stifle i 0).sil
   exact .byear (flex (h.baseU i hi) h.currency.1 h.currency.2.1 le_rfl)

lemma scoopG (i j:ℕ)(b u:Bool)(k:Cub ℕ ℕ)(f:Lyric)(V:ℕ→ℝ)
    (hp:∀ a∈v.P,
          Cext p s c T (if b then a else i) (if b then 0 else a) f (V a)):
      Cext p s c T i j (.heap u (p.bridgeQ b k) f) (if u then ∑ a∈v.P,V a else
                            rank v.P V (k.f s.l.x (film s i j).head.info)):=by
    let m:=p.bridgeQ b k; let x:=film s i j
    have hh:x.freq m=v.P:= h.lenpoll i j k b
    rw [← hh]; apply Chor.little
    · exact spread h.good i j
    · change (rootsD _).f s.l.x x.info < 2^(p.cup*s.d)
      unfold x; rw [numbers]; exact h.N.symm ▸ h.volume
    intro a ha
    rw [p.backBE]
    rw [hh] at ha; cases b <;> exact hp a ha

lemma bowlC {i}(he:i<v.m)(b):Cext p s c T i 0 (p.bites b) (sideq (v.meal i) b):=by
   let m:=p.bridgeQ false ⟨_,Kn.fix 0⟩
   have hp:Cext p s c T i 0 (.heap true m (.use p.inp (p.pit b)))
                      (∑ j∈v.P,sideq (v.grainp i j) b):=h.scoopG i 0 false true ⟨_,Kn.fix 0⟩
                                   _ _ fun a ha=> h.slices he (mem_range.1 ha) b
   have hz:sideq (v.meal i) b=sideq (Buf.line v.b) b+∑ j∈v.P,sideq (v.grainp i j) b:=by
        cases b <;> simp [Poolx.meal,sideq] <;> first | exact Prod.snd_sum | exact Prod.fst_sum
   rw [hz]; exact (h.stifle i 0).additions (h.rowUp (Or.inr he) b) hp

lemma sky {i} (he:i<v.m): Cext p s c T i 0 p.sight (ht (v.meal i)):=
   let hp:=h.stifle i 0
   hp.up0 (hp.absti (h.bowlC he true)) (hp.absti (h.bowlC he false))

lemma weep {i}(he:i<v.m)(b:Bool):
    Cext p s c T i 0 (Lu.times p.warmth (if b then p.rawP else p.sight))
           (Poolx.Nice.listP v (if b then Prod.fst else ht) i):=by
    have ht:Cext p s c T i 0 (if b then p.rawP else p.sight)
          ((if b then (Prod.fst:Pt→ℝ) else Buf.ht) (v.meal i)):=by
       cases b
       · exact h.sky he
       exact h.bowlC he true
    convert (h.stifle i 0).mult0 (h.chorus he) ht using 1
    unfold listP; split <;> simp

lemma starship {i}(hi:address v i)(b:Bool):
    Cext p s c T i 0 (p.starsR b) (max v.b (rank v.S (fun j=> (if b then Prod.fst else ht) (v.raw.ts j))
                                                                (if b then v.p.K else v.p.n))):=by
   let k := if b then v.p.K else v.p.n
   let G:= if b then (Prod.fst:Pt→ℝ) else ht
   let f:=film s i 0
   let p0:= p.bridgeQ true (rootsD (p.kth b))
   have hu:(rootsD (p.kth b)).f s.l.x f.head.info=k:=by
        change (rootsD (p.kth b)).f s.l.x (film s i 0).info=k
        rw [numbers]; cases b
        · exact h.carry
        exact h.cap
   have hz:= h.scoopG i 0 true false (rootsD (p.kth b))
            _ (Poolx.Nice.listP v G) fun a ha=>h.weep (mem_range.1 ha) b
   have hr: G (Buf.line v.b)=v.b:=by
      cases b
      · exact ht_line h.ball.baseM.1
      exact rfl
   simp only [Bool.false_eq_true,ite_false] at hz
   rw [hu] at hz
   rw [← h.ball.staged G hr]; exact (h.stifle i 0).up0 (h.rowUp hi true) hz

lemma aurora {i} (hi:address v i): Cext p s c T i 0 p.riseR (U v):=by
   let z:=goalCost c; let w:=h.stifle i 0
   have hh:Cext p s c T i 0 (.use p.inp p.reserveC) v.p.rho:=
       .byear (flex (h.rhoQ i hi) h.currency.1 h.currency.2.1 le_rfl)
   have hf:Cext p s c T i 0 (kohn 4) 4:=by exact w.rove z 4
   exact w.lo0 hf (w.up0 hh (h.starship hi false))

lemma skyline {i} (hi:address v i):Cext p s c T i 0 p.zenith (Z v):=by
   let z:=goalCost c; let w:=h.stifle i 0
   have hf:Cext p s c T i 0 (kohn 4) 4:=by exact w.rove z 4
   have hg:Cext p s c T i 0 (kohn 3) 3:=by exact w.rove z 3
   have hu:Cext p s c T i 0 (p.starsR true) (v.raw.rk v.S v.p.K):=by
       unfold At.Blob.rk; rw [max_comm]; exact h.starship hi true
   have he:=h.aurora hi
   exact w.lo0 hf (w.up0 he (w.lo0 hu (w.mult0 hg he)))

lemma trench {i} (he:i<v.m): Cext p s c T i 0 p.harsh (2*ht (v.meal i)-3*U v):=
    let w:=h.stifle i 0; let z:=goalCost c
    have hz:Cext p s c T i 0 (kohn 2) 2:=by exact w.rove z 2
    have hg:Cext p s c T i 0 (kohn 3) 3:=by exact w.rove z 3
    w.dubs (w.mult0 hz (h.sky he)) (w.mult0 hg (h.aurora (Or.inr he)))

lemma blankx {i}(hi:address v i)(b):Cext p s c T i 0 (p.border b) (sideq (Buf.line (Z v)) b):=by
   cases b
   · exact (h.stifle i 0).sil
   exact h.skyline hi
lemma boardU {i}(hi:address v i)(b):Cext p s c T i 0 (p.borderE b) (sideq (Buf.line (Z v)) b):=by
   apply (h.stifle i 0).ring0 (h.blankx hi b)
   have ht : 0 ≤  Z v:=v.p.Z_nn v.raw
   have hz : Z v ≤ 4:=(v.p.Z_w v.raw).2.2
   have hp : 4 ≤ p.R s:=h.clampR
   cases b
   · change |(0:ℝ)|  ≤  p.R s; rw [abs_zero]; linarith
   change |Z v|  ≤  p.R s; rw [abs_of_nonneg ht]; linarith

lemma heights(i):Cext p s c T i 0 p.topE (p.R s):=by
   let f:=film s i 0; let w:=h.stifle i 0
   let c0:=campk p.I
   let B:=scaleC c0 p.lid s.l.x f.info
   have hz : B.v=p.R s:=scalen (stable_home w.st) p.lid
   rw [← hz]
   apply Chor.played w.st w.he (fun x _=>rfl)
   rw [hz]; exact (abs_of_pos (mass0 ..)).le

abbrev paid (p:Board)(s:Seats)(v:Poolx):Blob:= struck (p.R s) (v.p.push v.raw)
lemma foam {i} (hi:i<v.m)(he:v.mayor i)(b):
   Cext p s c T i 0 (p.guardE b) (sideq ((paid p s v).ts (v.place i)) b):=by
   let x:=v.place i
   let w:=h.stifle i 0; let z:=goalCost c
   have hz:Cext p s c T i 0 (kohn 2) 2:=by exact w.rove z 2
   have hg:Cext p s c T i 0 (kohn 7) 7:=by exact w.rove z 7
   let k:ℝ:=7*max 0 (Buf.ht (v.meal i)-2*U v)
   have he0:Cext p s c T i 0 p.shore k:=w.mult0 hg (w.up0 w.sil (w.dubs (h.sky hi)
                                                               (w.mult0 hz (h.aurora (Or.inr hi)))))
   let L:=Buf.line (Z v); let r:=sideq L b
   have hr:Cext p s c T i 0 (p.border b) r:=h.blankx (Or.inr hi) b
   have he1:=w.clips (h.heights i) (w.additions hr (w.clips he0 (w.dubs (h.bowlC hi b) hr)))
   have hA :
       sideq ((paid p s v).ts (v.place i)) b=
                       sat (p.R s) (r+sat k (sideq (v.meal i) b-r)):=by
      unfold paid struck Params.push k
      rw [h.ball.serves (mem_range.2 hi) he.1]
      cases b <;> rfl
   rw [hA]
   apply w.ring0 he1; exact sat_size (mass0 p.lid s.d).le _

end Holds
end
end ExactDerandomization.Reed.Board

end

section

namespace ExactDerandomization.Reed
open Counter Relay Rill Fret Buf Analysis Hie At Finset Seats Poolx Poolx.Nice Lu Board
open Fret.Lyric Holds
noncomputable section
namespace Test
def heated (y:ℕ) : Cub (ℕ×Coin) ℕ:=
    ⟨fun _ a=>if Coin.low a.2 (Coin.ofZ y) then 0 else 1,
                  (Coin.lowerK Kn.next (Kn.fix _)).cond (Kn.fix 0) (Kn.fix 1)⟩
abbrev draw (f:Lyric)(j:ℕ):ℕ:= f.weight+j+6
def arm (f:Lyric)(k:Knob)(u j:ℕ): Badge:=⟨choir k f,k,f.weight,draw f j,heated u⟩

abbrev extra (f:Lyric)(j) := draw f j + f.tail
lemma f_marg (d i j:ℕ)(hd:1  ≤  d):
    massB i d*2/(2:ℝ)^((i+j+6)*d) < (massB j d)⁻¹/2 := by
   change massB i d*2/massB (i+j+6) d<_
   have hi:=mass0 i d; have hj:=mass0 j d
   have hx:4 < massB 6 d:=by have h:=swellB (c:=6) hd; norm_num at h; linarith
   rw [mass_mul,mass_mul]
   field_simp; nlinarith

def seatC(f:Lyric) (c):=f.cost c +100

lemma felt {f k c T s j X} (hp:Standard s k T)(he:Chor k c T s f X)(hz:1 ≤ c)(ht:extra f j*s.d  ≤ T) (u:ℕ):
    let B:=arm f k u j
    ∃ a:ℕ,a ≤ 1∧s.rite (B.tariff (seatC f c)) B.check a ∧
             (a=0→ X  ≤  u+(massB j s.d)⁻¹/2) ∧ (a≠0→ (u:ℝ)-(massB j s.d)⁻¹/2 < X):=by
   dsimp only; let B:=arm f k u j
   let t:=B.m*s.d
   let c0:=seatC f c
   obtain ⟨w,h⟩:=flex (sing he hz (H:=t) (by unfold t B arm; unfold extra at ht; rwa [add_mul] at ht))
               (cost_hi hz) (show f.cost c  ≤  seatC f c by unfold seatC; omega) le_rfl
   let Q:Coin:=Coin.mult (scaleC k B.i s.l.x s.info) (Coin.place (w t) (2^t))
   let a:= (heated u).f s.l.x (s.info,Q)
   have hh: a=0∨a=1:=by unfold a heated; dsimp only; split <;> simp
   have hz0: Align s.head k:=stable_home hp.st
   have hd:1 ≤ s.d:=hz0.1.1
   have hx:B.i=f.weight:=rfl
   have hA:=B.accuracy (s:=s.head) hz0 (h _ s.hm).1
   change |Q.v-X|  ≤  massB f.weight s.d*2/(2:ℝ)^((f.weight+j+6)*s.d) at hA
   obtain ⟨h1,h2⟩:= abs_lt.1 (hA.trans_lt (f_marg s.d f.weight j hd))
   have hu : a=0 ↔ Q.v  ≤  u:=by
       unfold a heated
       simp only [ite_eq_left_iff,Coin.low_eq,Coin.ofv]; norm_num
   refine ⟨a,by omega,fun x hx=>?_,fun ht=>by have h:=hu.1 ht; linarith,
                                   fun ht=>by have h:=not_le.1 (mt hu.2 ht); linarith⟩
   have hM:4 ≤ c0:=by unfold c0 seatC; omega
   refine B.query (hp.st x hx) (by change 1  ≤  c0; omega) rfl  (h x hx) ?_ rfl
   · unfold Punct; change lb a+1  ≤  c0*s.d
     rcases hh with ha|ha <;> simp only [ha,lb_one,lb_zero] <;> nlinarith
end Test

namespace Board
variable (p:Board)
abbrev heatp:Badge:=Test.arm p.riseR (campk p.I) 2 0
abbrev touchp:Badge:=Test.arm p.harsh (campk p.I) 0 p.lips
def melt := transformed ⟨_,centerK⟩ p.heatp.check
abbrev keep0 :Cog:=Cargo.choose p.touchp.check nothingX p.offer

def jack :Seek:=⟨p.bridgeQ true leftQ,p.keep0⟩
def shift :Cog:=Cargo.choose p.melt p.jack.latch nothingX

def bankC (c:ℕ) := p.heatp.tariff (Test.seatC p.riseR (goalCost c)) +
         p.touchp.tariff (Test.seatC p.harsh (goalCost c)) +goalCost c
abbrev burn :=Test.extra p.riseR 0 + Test.extra p.harsh p.lips
abbrev payC(c:ℕ):=16*(16*(p.bankC c))

structure Broom (p:Board)(s:Seats)(c:ℕ)(v:Poolx) where
   hot:ℕ
   marked:ℕ → ℕ
namespace Broom
variable {p:Board}{s:Seats}{v:Poolx}{c}
def reach (b:Broom p s c v):Finset ℕ:= if b.hot=0 then Seek.part b.marked v.m else ∅
def answer (b:Broom p s c v)(i:ℕ):ℕ:= if b.hot=0 then (Seek.relief b.marked i v.m).2 else 0
structure Fell (b:Broom p s c v):Prop where
   matches0 :∀ i∈v.P,b.marked i≠0→ b.marked i=v.tag i∧v.mayor i∧U v<ht (v.meal i)
   total :∀ i∈v.P,v.mayor i→2*U v<ht (v.meal i) → b.marked i≠0
   lands :b.hot≠0→1 ≤ U v
   crests :b.hot=0→U v<4
   arrival :∀ i:ℕ, (film s i 0).rite (p.payC c) p.shift (b.answer i) ∧ Punct s.head (p.payC c) (b.answer i)

end Broom

namespace Holds
variable {p:Board}{s c T v}(h:Holds p s c T v)
include h
omit h in
private lemma pay_arc : 1 ≤ p.heatp.tariff (Test.seatC p.riseR (goalCost c))∧
                         1 ≤ p.touchp.tariff (Test.seatC p.harsh (goalCost c)):=by
    unfold Badge.tariff Oven.price Oven.bill Badge.tariffStart; omega

lemma brooms (hr:p.burn*s.d ≤ T):∃ b:Broom p s c v,b.Fell:=by
   have hf:Test.extra p.riseR 0*s.d ≤ T ∧ Test.extra p.harsh p.lips*s.d  ≤ T:=by
                           unfold burn at hr; rw [add_mul] at hr; omega
   let c0:= goalCost c; let z:=p.bankC c
   have he:=h.pri; have hP:=(pay_arc (p := p) (c := c)); have hk:=h.currency
   have hM:z≥ c0∧z≥2:=by unfold z c0 bankC goalCost; omega
   let u:=U v
   obtain ⟨a,ha,hv,hA,hB⟩:=Test.felt (h.stifle 0 0) (h.aurora (i:=0) (Or.inl rfl)) hk.2.2 hf.1 2
   have hl:a=0→u < 4:=by intro h0; specialize hA h0; norm_num [massB] at hA; change u ≤ _ at hA; linarith
   have hl' : a≠0 →1 ≤  u:=by intro h1; specialize hB h1; norm_num [massB] at hB; change _ < u at hB; linarith
   have hm (i:ℕ): (film s i 0).rite z p.melt a:=
          importD ⟨_,centerK⟩ (centeral _ i 0)
             (higher hv hP.1 (by unfold z bankC heatp; omega))
   let D:ℝ:= (massB p.lips s.d)⁻¹
   have hd:D ≤ u:=le_trans h.costrho.1 (v.p.U_rho v.raw (by linarith [h.costrho.2]))
   have hg0:0<D:=by unfold D; positivity
   have hx(i:ℕ):∃ w,i<v.m →
      (film s i 0).rite z p.keep0 w ∧ Punct s.head z w ∧
          (w≠0 → w=v.tag i ∧v.mayor i ∧ u<ht (v.meal i)) ∧
                           (v.mayor i→2*u<ht (v.meal i) → w≠0):=by
       by_cases hi:i<v.m
       · obtain ⟨e,he1,hv,hA,hB⟩:=Test.felt (h.stifle i 0) (h.trench hi) hk.2.2 hf.2 0
         let y:=ht (v.meal i)
         change _ → 2*y-3*u ≤  (0:ℕ)+D/2 at hA
         change _ → ((0:ℕ):ℝ)-D/2 < 2*y-3*u at hB
         norm_num at hA hB
         have ht:=higher hv hP.2 (show _  ≤  z by unfold z bankC touchp; omega)
         have hr:=h.tagM i hi
         by_cases hj:e=0
         · refine ⟨0,fun _=>⟨Seats.steer ht (fun _=> Seats.blankD (h.act i 0) hM.2)
                             (fun hm=> (hm hj).elim),punct0 (stable_home h.good).1 hM.2,by simp,?_⟩⟩
           intro h1 h2; change 2*u<y at h2
           have hu:v.p.rho >0:=lt_of_lt_of_le hg0 h.costrho.1
           have hZ:= hA hj; have hu0:v.p.rho ≤ u:=v.p.U_rho _ (by linarith [h.costrho.2]); linarith
         refine ⟨solar v i,fun _=>⟨Seats.steer ht (fun hm=> (hj hm).elim)
                   (fun _=>higher (h.book hi) (by unfold postC; omega)
                                   (by unfold goalCost at *; unfold c0 goalCost at hM; omega)),?_ ,?_,?_⟩⟩
         · unfold solar
           split
           · exact punct_up hr.2 (hk.2.1.trans hM.1)
           exact punct0 (stable_home h.good).1 hM.2
         · intro hw; have hu:=(nowEQ v i).1 hw
           refine ⟨ite_eq_left hu,hu,?_⟩
           have hz:=hB hj; change u<y; linarith
         intro ht _; exact (nowEQ v i).2 ht
       exact ⟨0,fun hl=> (hi hl).elim⟩
   choose w hw using hx
   let b:Broom p s c v:=⟨a,w⟩
   refine ⟨b,⟨fun i hi=>(hw i (mem_range.1 hi)).2.2.1,
               fun i hi=>(hw i (mem_range.1 hi)).2.2.2,hl',hl,fun i=>?_⟩⟩
   let f:=film s i 0
   have hh:=higher (hm i) (by omega) (show z ≤  p.payC c by unfold payC; unfold z; omega)
   have hp:=h.act i 0
   by_cases hq:a=0
   · change f.rite _ p.shift _ ∧ _
     have hmN:p.jack.N f=v.m:=by change (rootsD _).f s.l.x f.info=_; unfold f; rw [numbers]; exact h.N
     have hmK:p.jack.b.key f.head=i:=by simp [jack,Branch.key,f,bridgeQ,leftQ,film,info,panelx]
     have hz:p.bankC c=z:=rfl
     have he:=p.jack.earns hp hM.2 w (hmN ▸ (punct_up h.coverM (hk.2.1.trans hM.1)))
                         (fun j hj=>by
                            rw [hmN] at hj
                            have hg:f.bench p.jack.b j=film s j 0:= by exact p.backBE s true i 0 _ j
                            rw [hg]; exact ⟨(hw j hj).2.1,(hw j hj).1⟩)
     dsimp only at he
     have heX:b.answer i=(Seek.relief w i v.m).2:=ite_eq_left hq
     rw [hmK,hmN] at he; rw [heX]
     exact ⟨Seats.steer hh (fun _=>he.2) (fun h1=>(h1 hq).elim),punct_up he.1
                                        (by unfold payC; unfold z; omega)⟩
   have heX:b.answer i=0:=ite_eq_right hq
   have hx0: 2 ≤ p.payC c:=by unfold z at hM; unfold payC; omega
   rw [heX]; exact ⟨Seats.steer hh (fun y=> (hq y).elim)
                         (fun _=> Seats.blankD hp hx0),punct0 (stable_home h.good).1 hx0⟩
end Holds
end Board
end
end ExactDerandomization.Reed

end

section

namespace ExactDerandomization.Reed.Board
open Counter Relay Rill Fret Buf Analysis Hie At Finset Seats Poolx Poolx.Nice Lu Board
open Fret.Lyric Holds Broom
noncomputable section
variable (p:Board)

/-- Routes the packed choice back to the walk head (outer i replaced by the packed rep index). -/
def rearm (x:Word)(a:History):ℕ:= stairs true x (a.1,(dec a.2:History).1)
lemma rearmK:Kn rearm:=(stairK true).comp (Kn.first.tuple (((Kn.unpack (α:=History)).comp Kn.next).left))
abbrev scoreMood (p:Board)(b:Bool):Cog:=choir (campk p.I) (p.guardE b)
abbrev plaza (b:Bool): Cog:= transformed ⟨_,centerK⟩ (choir (campk p.I) (p.borderE b))
abbrev primary := p.plaza true
def rateMood (b:Bool):Cog:=Cargo.choose p.shift (p.plaza b)
            (Cargo.combine p.shift (scoreMood p b) ⟨_,rearmK⟩)
abbrev hills(b:Bool):=(p.guardE b).tail+(p.borderE b).tail
abbrev prompt :=p.hills true+p.hills false+p.burn
abbrev vibes (c)(b:Bool):= (p.guardE b).cost (goalCost c) + (p.borderE b).cost (goalCost c)
abbrev tuneC (c:ℕ):=p.payC c + c + p.vibes c true + p.vibes c false
abbrev totalC(c:ℕ):=4*(p.tuneC c)

lemma pays_sides {T i H}(b)(he:H+p.prompt*i ≤ T):
   H+(p.guardE b).tail*i ≤ T ∧ H+(p.borderE b).tail*i ≤ T:=by
   unfold prompt hills at he; simp only [add_mul] at he
   cases b <;> omega
lemma tune_sides {c}(b): (p.guardE b).cost (goalCost c)  ≤  p.tuneC c ∧
                  (p.borderE b).cost (goalCost c)  ≤  p.tuneC c:=by
   cases b <;> unfold tuneC vibes <;> omega

namespace Broom
variable {p:Board}{s:Seats}{v:Poolx}{c}
def product (b:Broom p s c v): Blob := if b.hot=0 then paid p s v else Run.die (paid p s v)
abbrev who (b:Broom p s c v)(i:ℕ):ℕ:=Relay.mark (b.answer i)
abbrev spot (b:Broom p s c v)(i:ℕ):ℕ:= v.place (b.who i)
def valueq (b:Broom p s c v)(i:ℕ)(a:Bool):ℝ:= if b.answer i=0 then sideq (line (Z v)) a else
                                           sideq (b.product.ts (b.spot i)) a

namespace Fell
variable {b:Broom p s c v}(g:b.Fell)
include g
lemma there {i}(hi:i∈b.reach):i∈v.P ∧ v.mayor i ∧ U v<ht (v.meal i):=by
   unfold reach at hi; split at hi
   · next e=>
     obtain ⟨ha,hb⟩:=mem_filter.1 hi
     exact ⟨ha,(g.matches0 i ha hb).2⟩
   simp at hi
lemma capacity (hv:v.Nice): b.reach.card  ≤  v.p.n:=by
    by_cases hz:b.hot=0
    · exact hv.whole (fun _ he=> (g.there he).1) (g.crests hz) (fun _ he=> (g.there he).2)
    simp [reach,hz]
lemma locale {i}(he:b.answer i≠0):
     b.hot=0 ∧ b.who i∈b.reach ∧ b.answer i=Seek.bin (b.who i) (v.tag (b.who i)) ∧
                                          (Seek.part b.marked (b.who i)).card=i:=by
    unfold answer at he
    by_cases hg:b.hot=0
    · rw [ite_eq_left hg] at he
      obtain ⟨j,h1,h2,h3⟩:= (Seek.casebook b.marked i v.m).resolve_left he
      have hu:b.answer i=Seek.bin j (b.marked j):=(ite_eq_left hg).trans h3
      have hh:b.who i=j:=by unfold who; rw [hu]; simp [Seek.bin,Relay.mark]
      have ht :=mem_filter.1 h1
      have ha :b.marked j=v.tag j :=(g.matches0 j ht.1 ht.2).1
      unfold reach; rw [hh,ite_eq_left hg]
      exact ⟨hg,h1,ha ▸ hu,h2⟩
    rw [ite_eq_right hg] at he; contradiction

omit g in
lemma allot {i}:b.answer i≠0 ↔ i< b.reach.card:=by
   unfold answer reach; split
   · simp only [ne_eq,Seek.missed,not_le]
   simp
omit g in
lemma locates {j}(he:j∈b.reach): ∃ i,b.answer i≠0 ∧ b.who i=j:= by
   unfold reach at he; split at he
   · next hg=>
     obtain ⟨h1,h2⟩:=mem_filter.1 he
     let i:=(Seek.part b.marked j).card
     have hp:b.answer i=Seek.bin j (b.marked j):=(ite_eq_left hg).trans (Seek.order (mem_range.1 h1) h2 rfl)
     refine ⟨i,?_,?_⟩
     · rw [hp]; exact ne_of_gt (Seek.binpos j _)
     unfold who; rw [hp,Relay.marked]
   simp at he
lemma sole {i j} (he:b.answer i≠0)(hz:b.answer j≠0)(_:v.Nice)
     (hk:b.spot i=b.spot j):i=j:=by
    have hh:=g.locale he; have hg:=g.locale hz
    have hm:b.who i=b.who j:=(Poolx.Nice.unique (v := v)) (g.there hh.2.1).2.1 (g.there hg.2.1).2.1 hk
    exact hh.2.2.2.symm.trans (hm.symm ▸ hg.2.2.2)
lemma framed (hv:v.Nice)(hr: 4 ≤ p.R s) (i) (hi:i∈v.S)
     (he:∀ j,b.answer j≠0→ b.spot j≠i):
     b.product.ts i=line (Z v):=by
    unfold product; split
    · next hc=>
      refine hv.coverHome (B:=b.reach) ?_ _ hr hi ?_
      · intro i hi hv hp
        unfold reach; rw [ite_eq_left hc]
        exact mem_filter.2 ⟨hi,g.total i hi hv hp⟩
      intro hd
      obtain ⟨j,hg,hj⟩:=mem_image.1 hd
      obtain ⟨m,h1,h2⟩:=(locates (b := b)) hg
      apply he m h1; unfold spot; rw [h2,hj]
    rfl

end Fell
end Broom

namespace Holds
variable {p:Board}{s:Seats} {c T v} (h:p.Holds s c T v)
include h

lemma tune1 : 1 ≤  p.tuneC c:=by have:=h.pri; unfold tuneC; omega
lemma tune0 : 1 ≤  p.payC c ∧ p.payC c ≤  p.tuneC c ∧ p.tuneC c ≤  p.totalC c:=by
   have:=tune1 h; have:=h.pri
   unfold tuneC payC bankC totalC goalCost at *
   unfold tuneC payC bankC goalCost
   omega

lemma baseHear {H}(hr:H+p.prompt*s.d ≤ T)(i:ℕ)(b): (film s i 0).band (p.tuneC c) H p.lid (p.plaza b)
                                                       (sideq (line (Z v)) b):=by
    let u:=h.boardU (i:=0) (Or.inl rfl) b
    let z:= goalCost c
    have hh : 1 ≤ z:=h.currency.2.2
    apply transportD ⟨_,centerK⟩ (centeral s i 0)
    exact flex (sing u hh (p.pays_sides b hr).2) (cost_hi hh) (p.tune_sides b).2 le_rfl

lemma turmoil {b:Broom p s c v}(g:b.Fell){H}(hr:H+p.prompt*s.d  ≤ T)(i)(a):
    (film s i 0).band (p.totalC c) H p.lid (p.rateMood a) (b.valueq i a):=by
    let C:=p.tuneC c
    have hh:=h.tune0; have hc:=h.tune1; have he:=g.arrival i
    have ht:= higher he.1 hh.1 hh.2.1
    apply Seats.avis (higher ht hc hh.2.2)
    · intro hz; rw [Broom.valueq,ite_eq_left hz]
      exact flex (h.baseHear hr i a) hc hh.2.2 le_rfl
    intro hp
    rw [Broom.valueq,ite_eq_right hp]
    obtain ⟨hu,h1,h2,h3⟩:=g.locale hp
    obtain ⟨h4,h5,h6⟩:=g.there h1
    have hz := sing (h.foam (mem_range.1 h4) h5 a) h.currency.2.2 (p.pays_sides a hr).1
    unfold Broom.product
    rw [ite_eq_left hu]
    let f:=film s i 0; let k:Cub History ℕ:=⟨_,rearmK⟩
    have hk: berth k f (b.answer i) = film s (b.who i) 0:=by simp [berth,k,panelx,f,film,
                                                   rearm,stairs,who,Relay.mark,info]
    apply advises (h.act i 0) (punct_up he.2 hh.2.1) hc ht
    rw [hk]
    exact flex hz (cost_hi h.currency.2.2) (p.tune_sides a).1 le_rfl

end Holds

/-- Package for a single executable prefix update, all higher-precision probes. -/
structure Page (s:Seats)(c T:ℕ)(v:Poolx)(b:Broom p s c v):Prop where
    fell: b.Fell
    iex:1  ≤  p.totalC c
    transact :∀ i, Punct s.head (p.totalC c) (b.answer i) ∧ (film s i 0).rite (p.totalC c) p.shift (b.answer i)
    wave :∀ i a H,H+p.prompt*s.d ≤  T →
                 (film s i 0).band (p.totalC c) H p.lid (p.rateMood a) (b.valueq i a)
    baseP :∀ i H,H+p.prompt*s.d ≤  T → (film s i 0).band (p.totalC c) H p.lid p.primary (Z v)
theorem mounted {s c T v} (h:Holds p s c T v) (hr:p.prompt*s.d ≤ T):
      ∃ b, Page p s c T v b:=by
   obtain ⟨b,hb⟩:= brooms h (by exact le_trans (Nat.mul_le_mul_right _ (by unfold prompt; omega)) hr)
   have hp:=tune0 h
   have he:=hp.2.1.trans hp.2.2
   exact ⟨b,hb,(tune1 h).trans hp.2.2,fun i=>
        ⟨punct_up (hb.arrival i).2 he,higher (hb.arrival i).1 hp.1 he⟩,
        fun i a _ hz=>turmoil h hb hz i a,fun i H hz=>
                flex (h.baseHear hz i true) (h.tune1) hp.2.2 le_rfl⟩

end
end ExactDerandomization.Reed.Board

end

end OAI
