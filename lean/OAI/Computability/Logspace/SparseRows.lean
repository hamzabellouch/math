import OAI.Computability.Logspace.CompressionPrograms
import OAI.Computability.Logspace.ProbabilityAtoms

namespace OAI

/-!
Sparse row encodings, slot selection, and virtual baselines.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Stem
open Counter Relay Rill Fret Reed Analysis Hie At Finset Seats Buf

/-- A row with bounded ports and virtual baseline. -/
structure Depot where
    S:Domain
    y:Blob
    n:ℕ
    tag:ℕ→ℕ
    pos:ℕ→ℕ
namespace Depot
noncomputable section
variable (p:Depot)
abbrev live(i:ℕ):Prop:=p.tag i≠0
def space:= (range p.n).filter p.live
def qpoint(i:ℕ):Pt:= if p.live i then p.y.ts (p.pos i) else line p.y.base
structure Trust:Prop where
    hp:0  ≤  p.y.base
    card0:∀ i,p.live i→ i < p.n
    into:∀ i,p.live i→ p.pos i∈ p.S
    uniq:∀ i j,p.live i→p.live j→p.pos i=p.pos j→i=j
    off:∀ i∈p.S,(∀ j,p.live j→p.pos j≠i) → p.y.ts i=line p.y.base
namespace Trust
variable {p:Depot}(h:p.Trust)
include h
lemma seen (i):i∈p.space ↔ p.live i:= by rw [space,mem_filter]; exact
       ⟨fun e=>e.2,fun e=>⟨mem_range.2 (h.card0 i e),e⟩⟩

lemma snatch {i} (hi:i∈p.S)(hh:p.y.ts i ≠ line p.y.base):∃ j,p.live j∧p.pos j=i:= by
   by_contra! hp
   exact hh (h.off i hi (fun j he hx=> hp j he hx))

abbrev coast (p:Depot) (K:ℕ) :=
       max (rank (range p.n) (fun i=> (p.qpoint i).1) K) p.y.base
lemma coast_true (K): p.y.rk p.S K=coast p K:= by
   let b:=p.y.base; let s:=p.space
   let f(i):=(p.qpoint i).1
   let g(i):=(p.y.ts i).1
   have hv {x:ℝ} (hx:b ≤ x):
        ((range p.n).filter (fun i=> x< f i)).card=(p.S.filter (fun i=> x< g i)).card:=by
      let l:=(range p.n).filter (fun i=>x<f i); let w:=p.S.filter (fun i=> x< g i)
      have hh (i)(hi:i∈l):p.live i ∧ f i=g (p.pos i):=by
         by_cases ht:p.live i
         · exact ⟨ht,congrArg Prod.fst (ite_eq_left ht)⟩
         have hh:f i=b:=congrArg Prod.fst (show p.qpoint i=line p.y.base from ite_eq_right ht)
         have hl:x<f i:=(mem_filter.1 hi).2; linarith
      have he: l.image p.pos=w:=by
          ext i; constructor
          · intro ht; obtain ⟨j,h1,rfl⟩:=mem_image.1 ht
            exact mem_filter.2 ⟨h.into j (hh j h1).1,(mem_filter.1 h1).2.trans_eq (hh j h1).2⟩
          intro ht; obtain ⟨ha,hb⟩:=mem_filter.1 ht
          have he:p.y.ts i ≠ line p.y.base:=fun hg=> (not_lt_of_ge hx)
                                                        (hb.trans_eq (congrArg Prod.fst hg))
          obtain ⟨j,h1,h2⟩:=h.snatch ha he
          have hs:f j=g (p.pos j):=congrArg Prod.fst (show p.qpoint j=p.y.ts (p.pos j) from ite_eq_left h1)
          rw [h2] at hs
          exact mem_image.2 ⟨j,mem_filter.2 ⟨mem_range.2 (h.card0 j h1),hb.trans_eq hs.symm⟩,h2⟩
      rw [← show l.image p.pos=p.S.filter _ from he]
      symm; refine card_image_iff.2 (fun i hi j hj hz=>h.uniq i j (hh i hi).1 (hh j hj).1 hz)
   let u:=max (rank p.S g K) b
   let v:=coast p K
   have hh(x:ℝ) : (x<u)↔ x<v:=by
      change x < max (rank p.S g K) b ↔ x < max (rank (range p.n) f K) b
      by_cases ht:b ≤ x
      · rw [lt_max_iff,lt_max_iff]; have hg:=h.hp.trans ht
        rw [rank_gt hg,rank_gt hg,hv ht]
      have ht:x<b:=by linarith
      simp [lt_max_iff,ht]
   change u=v; rcases lt_trichotomy u v with he|he|he
   · exact False.elim (lt_irrefl _ ((hh u).2 he))
   · exact he
   exact False.elim (lt_irrefl _ ((hh v).1 he))

structure ColorF (p:Depot) where
    tau:ℝ
    K:ℕ
    kth:ℝ
    pts:ℕ → ℝ
open scoped Classical
def ColorF.mapG (p:Depot)(c: ColorF p):Blob.Guess:=
    ⟨fun i=> if h:∃ j,p.live j ∧ p.pos j=i then c.pts (Classical.choose h) else (p.y.ts i).1,c.kth⟩
variable {z:ColorF p}
def GoodS(c:ColorF p):= (∀ i,p.live i→|(p.qpoint i).1 - c.pts i|  ≤  c.tau/10000)∧ |coast p c.K-c.kth|  ≤  c.tau/10000
def ColorF.hoot (p:Depot)(v:ColorF p) (b:Bool)(i:ℕ):Prop:=p.live i ∧
   if b then v.tau/5 < v.pts i ∧ v.kth < v.tau*(15/1000) else
             5*v.tau/12 < v.pts i ∧ v.kth < v.tau*(35/10000)

lemma restates {i}(he:p.live i): (ColorF.mapG p z).first (p.pos i)=z.pts i:=by
   have hh:∃ j,p.live j∧p.pos j=p.pos i:=⟨i,he,rfl⟩
   simp only [ColorF.mapG,dite_eq_left hh]
   obtain ⟨ht,hz⟩:= Classical.choose_spec hh; rw [h.uniq (Classical.choose hh) _ ht he hz]

lemma region (c:GoodS z)(he:0< z.tau):
     Blob.acc (ColorF.mapG p z) p.y p.S z.K z.tau:=by
   refine ⟨fun i hi=>?_,(h.coast_true z.K).symm ▸ c.2⟩
   unfold ColorF.mapG; dsimp only
   split
   · next hp=>
     obtain ⟨ha,hb⟩:= Classical.choose_spec hp
     have hu:=c.1 _ ha
     unfold qpoint at hu; rw [ite_eq_left ha,hb] at hu
     exact hu
   simp only [sub_self,abs_zero]; positivity

lemma onward {c:ColorF p}(z:GoodS c)(he:0<c.tau) (b:Bool):
    Blob.expose c.tau (ColorF.mapG p c) b p.S =
        ((range p.n).filter (ColorF.hoot p c b)).image p.pos:=by
    let D:= Blob.expose c.tau (ColorF.mapG p c) b p.S
    have ht {i}(hh:p.live i): p.pos i∈D↔ColorF.hoot p c b i:=by
       have he:= h.into i hh
       cases b <;> unfold D <;>
           simp only [Blob.expose,ColorF.hoot,h.restates hh,he,show (ColorF.mapG p c).kth=c.kth from rfl,mem_filter,Bool.false_eq_true,ite_false,ite_true] <;> grind
    change D=_
    ext i; constructor
    · intro hz
      have hi:i∈p.S:= Blob.expose_subset p.S _ _ _ hz
      have hF: p.y.ts i≠ line p.y.base:=by
          intro hh
          exact Blob.missing_baseline (h.region z he) he b (congrArg Prod.fst hh) hz
      obtain ⟨j,hv,rfl⟩:=h.snatch hi hF
      exact mem_image.2 ⟨j,mem_filter.2 ⟨mem_range.2 (h.card0 j hv),(ht hv).1 hz⟩,rfl⟩
    intro hi; obtain ⟨j,hv,rfl⟩:=mem_image.1 hi
    exact (ht (mem_filter.1 hv).2.1).2 (mem_filter.1 hv).2

lemma amount0 {c:ColorF p}(hc:GoodS c)(he:0<c.tau)(b:Bool):
    ((range p.n).filter (ColorF.hoot p c b)).card  ≤  c.K:=by
   have hv:=Blob.exposure_count (h.region hc he) he b
   rw [h.onward hc he b,card_image_iff.2] at hv
   · exact hv
   intro i hi j hj ht
   exact h.uniq _ _ (mem_filter.1 hi).2.1 (mem_filter.1 hj).2.1 ht
end Trust
end
end Depot
end ExactDerandomization.Stem

end

section

namespace ExactDerandomization.Stem
open Counter Relay Rill Fret Reed Analysis Hie At Finset Seats Buf Lu Depot.Trust
open Lyric
noncomputable section
/- main (b=false) weight argument o. b=true witness uses score I,
not the upper guarding score. -/
structure Cage where
     m: ℕ
     k:ℕ
     powe: ℕ
     lo:ℕ
     kn:Knob
     base:Cog
     ask : Cog
     partR : Bool → Cog
     theta:Cub ℕ Coin
     nest:Bool→ Lyric→Lyric→ Lyric → Lyric
     root : Bool → ℕ

namespace Cage
variable (p:Cage)
abbrev firstC(b:Bool):Lyric:=.use p.powe (p.partR b)
abbrev fellow (k:Cub ℕ ℕ):Branch:=⟨⟨_,Kn.fix p.m⟩,⟨_,stairK true⟩,k,p.m+2⟩
abbrev relay0:=p.fellow ⟨_,Kn.fix p.k⟩
abbrev crown:Lyric:= Lu.sup (.use p.powe p.base) (.heap false p.relay0 (p.firstC true))
abbrev figure (b:Bool):Lyric:=p.nest b (p.firstC true) p.crown (p.firstC false)

variable (s: Seats) (d:Depot)(θ:ℝ)(o:Bool→Trio) (c T:ℕ)
/-- birth chamber precondition -/
structure Ink : Prop where
     ok:d.Trust
     align:s.stable p.kn
     goodF : ∀ i j, (film s i j).stable (campk p.kn)
     hi:s.d=1
     mp:d.n=p.m
     hc:4 ≤ c
     expire:Live s.head p.kn T
     θp : (massB p.lo s.d)⁻¹  ≤  θ/20000
     θq : ∀ i,(p.theta.f s.l.x (film s i 0).info).v=θ
     get:∀ i<p.m,(film s i 0).rite c p.ask (d.tag i) ∧ Punct s.head c (d.tag i)
     srcT :∀ i,i=0∨i<p.m → (film s i 0).band c T p.powe p.base d.y.base
     hues :∀ i<p.m,∀ b,(film s i 0).band c T p.powe (p.partR b) (sideq (d.qpoint i) b)
     seats0:∀ b,(p.figure b).weight=p.root b
     composition :∀ {i} (_:i<p.m),d.live i→ ∀ b,
          Chor (campk p.kn) c T (film s i 0) (p.firstC true) (d.y.ts (d.pos i)).1 →
          Chor (campk p.kn) c T (film s i 0) p.crown (d.y.rk d.S p.k) →
          Chor (campk p.kn) c T (film s i 0) (p.firstC false) (d.y.ts (d.pos i)).2 →
          Chor (campk p.kn) c T (film s i 0) (p.figure b) (d.y.val d.S p.k (o b) (d.pos i))

abbrev ratioX (b f:Bool):Coin:=
    if b then if f then Coin.place 1 5 else Coin.place 15 1000 else
      if f then Coin.place 5 12 else Coin.place 35 10000
def probeX (b f:Bool)(x:Word)(a:ℕ×Coin):ℕ:=
   let k:=Coin.mult (p.theta.f x a.1) (ratioX b f)
   if (if f then Coin.low a.2 k else Coin.low k a.2) then 0 else 1
lemma probeK (b f):Kn (p.probeX b f):=by
    have ht:Kn (fun x (a:ℕ×Coin)=>Coin.mult (p.theta.f x a.1) (ratioX b f)):=
                                  Coin.multK (p.theta.runs.comp Kn.first) (Kn.fix _)
    cases f
    · exact ((Coin.lowerK ht Kn.next).cond (Kn.fix 0) (Kn.fix 1))
    exact ((Coin.lowerK Kn.next (Coin.multK (p.theta.runs.comp Kn.first)
                                        (Kn.fix _))).cond (Kn.fix 0) (Kn.fix 1))
abbrev realkey(f:Bool):Lyric:= if f then p.firstC true else p.crown
abbrev pin (p:Cage)(f:Bool):=Reed.Test.draw (p.realkey f) p.lo
def badge0 (b f:Bool):Badge:=
   let k:=campk p.kn
   let u:=p.realkey f
   ⟨u.choir k,k,u.weight,p.pin f,⟨_,p.probeK b f⟩⟩

namespace Ink
variable {p s d θ o c T}(h:Ink p s d θ o c T)
include h
private lemma crew (i j) : Lu.Standard (film s i j) (campk p.kn) T:=
    ⟨h.goodF i j,spanFilm h.expire ..⟩

omit h in
lemma fix0(i j a): (film s i j).bench (p.relay0) a=film s a 0:=by
                simp [film,bench,Branch.port,panelx,stairs]
lemma crowny {i} (he:i=0∨i<p.m):Chor (campk p.kn) c T (film s i 0) p.crown (d.y.rk d.S p.k) := by
    have hv : (film s i 0).freq p.relay0=range d.n:=by rw [h.mp]
    let F:=fun i=>(d.qpoint i).1
    have he0 : Chor (campk p.kn) c T (film s i 0) (.heap false p.relay0 (p.firstC true)) (rank (range d.n) F p.k):=by
       rw [← hv]
       apply Chor.little (h.goodF i 0)
       · change p.m < 2^((p.m+2)*s.d)
         rw [h.hi,mul_one]; have hz:= Relay.growing (p.m+2); omega
       intro a hz
       rw [hv,h.mp] at hz
       rw [(fix0 (p := p) (s := s))]
       exact .byear (h.hues a (mem_range.1 hz) true)
    rw [h.ok.coast_true]
    unfold coast; rw [max_comm]
    exact (h.crew ..).up0 (.byear (h.srcT i he)) he0

lemma sculpt {i} (hi:d.live i) (b):
    Chor (campk p.kn) c T (film s i 0) (p.figure b) (d.y.val d.S p.k (o b) (d.pos i)) := by
   have hn:i<p.m:=(h.ok.card0 i hi).trans_eq h.mp
   have ht : d.qpoint i=d.y.ts (d.pos i):= ite_eq_left hi
   apply h.composition hn hi b _ (h.crowny (Or.inr hn)) _
   · rw [← ht]; exact .byear (h.hues i hn true)
   rw [← ht]; exact .byear (h.hues i hn false)
end Ink

abbrev Peer(f:Bool):= Test.extra (p.realkey f) p.lo
abbrev gauge (f:Bool)(c:ℕ):= (Test.seatC (p.realkey f) c)
abbrev goodz (c:ℕ):= c + p.m + 8
abbrev tolls (f:Bool)(c:ℕ):= (p.badge0 false f).tariff (p.gauge f c)
abbrev OutC(c:ℕ) :=p.goodz c+p.tolls false c+p.tolls true c

def voice (p:Cage)(b:Bool) := Cargo.choose
        (transformed ⟨_,centerK⟩ (p.badge0 b false).check)
        Seats.nothingX (Cargo.choose (p.badge0 b true).check Seats.nothingX p.ask)
namespace Ink
variable {p s d θ o c T}(h:Ink p s d θ o c T)
include h
omit h in
private lemma probeB (b f:Bool) (i x):p.probeX b f s.l.x ((film s i 0).info,x)  ≤ 1:=by
   cases f <;> simp [probeX] <;> grind
lemma orb {f q}(hq:Test.extra (p.realkey f) p.lo*s.d ≤ T){X:ℝ}
   (hx:Chor (campk p.kn) c T (film s q 0) (p.realkey f) X):
    ∃ a:Coin, |X-a.v|  ≤  θ/10000 ∧ ∀ b,(film s q 0).rite (p.tolls f c) (p.badge0 b f).check
                                              (p.probeX b f s.l.x ((film s q 0).info,a)):=by
   let m:=film s q 0; let v:=p.realkey f
   have hM:1 ≤ c:=by have:=h.hc; omega
   let C:= p.gauge f c; let H:=p.pin f*s.d
   obtain ⟨w,h0⟩:=flex (sing hx hM (H:=H) (by
         unfold Test.extra at hq; rw [add_mul] at hq; exact hq))
          (Lyric.cost_hi hM) (show v.cost c ≤ C by unfold C gauge Test.seatC v; omega) le_rfl
   let Y:=Coin.mult (scaleC (campk p.kn) v.weight m.l.x m.info) (Coin.place (w H) (2^H))
   have hm:= (h.crew q 0).st; have hi:=stable_home hm
   have hz:(p.badge0 true f).i=v.weight:=rfl
   have ht:= (p.badge0 true f).accuracy hi (h0 _ m.hm).1
   change |Y.v-X|  ≤  massB v.weight s.d*2/(2:ℝ)^H at ht
   have hd:1 ≤ s.d := h.hi.ge
   have he : |Y.v-X| < (massB p.lo s.d)⁻¹/2:= lt_of_le_of_lt ht (Test.f_marg s.d v.weight p.lo hd)
   have hg := h.θp; have hp:0<(massB p.lo s.d)⁻¹ :=by positivity
   refine ⟨Y,?_,fun b x hh=>?_⟩
   · rw [abs_sub_comm]; linarith
   let i:=p.probeX b f s.l.x (m.info,Y)
   have hP : lb i  ≤ 1:= by exact lb_mono ((probeB (p := p) (s := s)) b f q Y)
   have hv:4 ≤ C:=by unfold C gauge Test.seatC; omega
   exact (p.badge0 b f).query (hm x hh) (by  omega)
                    (t:=H) rfl (h0 x hh) (show Punct (m.seat x) C i by
                         unfold Punct; change _+_ ≤ C*s.d; nlinarith) rfl
lemma asks {q v b f}:
      p.probeX b f s.l.x ((film s q 0).info,v)≠0 ↔
        if f then θ*(ratioX b f).v < v.v else v.v < θ*(ratioX b f).v:=by
   cases f <;> unfold probeX <;> simp [Coin.low_eq,h.θq]

end Ink
end Cage
end
end ExactDerandomization.Stem

end

section

namespace ExactDerandomization.Stem.Cage
open Counter Relay Rill Fret Reed Analysis Hie At Finset Seats Buf Lu Depot.Trust
open Lyric
noncomputable section
open scoped Classical
variable (p:Cage) (s:Seats) (d:Depot)(θ:ℝ)(o:Bool→Trio) (c T:ℕ)

structure Ballot where
    wt : ColorF d
def Game (_:Cage)(d:Depot)(u:Ballot d)(b:Bool)(i:ℕ):ℕ:= if ColorF.hoot d u.wt b i then d.tag i else 0
def shaft (b:Bool):Seek:=⟨p.fellow leftQ,p.voice b⟩
abbrev belt (b:Bool):Cog:=(p.shaft b).latch
abbrev valN(p:Cage)(d:Depot)(u:Ballot d)(b:Bool)(i:ℕ):ℕ:=(Seek.relief (Game p _ u b) i p.m).2

structure Style(u:Ballot d):Prop where
   rightP:u.wt.K=p.k
   height:u.wt.tau=θ
   legally: GoodS u.wt
   serve:∀ i<p.m,∀ b,(film s i 0).rite (p.OutC c) (p.voice b) (Game p d u b i)∧
                                                Punct s.head (p.OutC c) (Game p d u b i)
namespace Ink
variable {p s d θ o c T}(h:Ink p s d θ o c T)
include h
lemma ht0 : 0<θ:=by
   have hp:0<(massB p.lo s.d)⁻¹:=by positivity
   have hv:=h.θp; linarith
lemma colorBlock {i} (v w: Coin)(b:Bool){z:Ballot d}(hp:z.wt.tau=θ)(hf:z.wt.kth=w.v)(hy:z.wt.pts i=v.v):
   z.wt.hoot d b i ↔
     d.live i ∧ p.probeX b true s.l.x ((film s i 0).info,v)≠0
                ∧ p.probeX b false s.l.x ((film s 0 0).info,w)≠0:=by
   rw [h.asks (q:=i),h.asks (q:=0)]
   unfold ColorF.hoot
   rw [hp,hf,hy]
   cases b
   · simp only [Bool.false_eq_true,ite_false,ite_true,ratioX]
     rw [Coin.place0 _ _ (by norm_num),Coin.place0 _ _ (by norm_num)]; norm_num; ring_nf; simp
   simp only [ite_true,ratioX, Bool.false_eq_true,ite_false]
   rw [Coin.place0 _ _ (by norm_num),Coin.place0 _ _ (by norm_num)]; norm_num; ring_nf; simp

lemma cost_vol(b:Bool):1 ≤  c∧c ≤ p.OutC c∧2 ≤ p.OutC c∧1  ≤ p.tolls b c∧p.tolls b c  ≤ p.OutC c:=by
   have hz:=h.hc
   cases b <;> unfold OutC goodz tolls Badge.tariff Oven.price Oven.bill Badge.tariffStart <;> omega

abbrev prepare(p:Cage):=p.Peer false+p.Peer true
lemma chose (hp:prepare p*s.d ≤ T):∃ u,Style p s d θ c u:= by
    let f(i:ℕ):=(d.qpoint i).1
    let v:= coast d p.k
    have hP:p.Peer false*s.d ≤ T ∧ p.Peer true*s.d ≤ T:=by unfold prepare at hp; rw [add_mul] at hp; omega
    have hs:Chor (campk p.kn) c T (film s 0 0) (p.realkey false) v:=by
       unfold v; rw [← h.ok.coast_true p.k]; exact h.crowny (Or.inl rfl)
    obtain ⟨w,hU,hW⟩:=h.orb (f:=false) hP.1 hs
    have he(i:ℕ):∃ w:Coin,i<p.m→ |f i-w.v|  ≤  θ/10000 ∧ ∀ b,(film s i 0).rite (p.tolls true c)
                                    (p.badge0 b true).check (p.probeX b true s.l.x ((film s i 0).info,w)):=by
       by_cases hi:i<p.m
       · obtain ⟨w,h⟩:=h.orb (f:=true) (X:=f i) hP.2 (Chor.byear (h.hues i hi true))
         exact ⟨w,fun _=>h⟩
       exact ⟨Coin.ofZ 0,fun h=> (hi h).elim⟩
    choose wt hw using he
    let u:Ballot d:=⟨⟨θ,p.k,w.v,fun i=>(wt i).v⟩⟩
    refine ⟨u,rfl,rfl,⟨fun i hi=>(hw i ((h.ok.card0 i hi).trans_eq h.mp)).1,hU⟩,fun i hi b=>?_⟩
    let x:=film s i 0
    have hg:= h.get i hi
    have hz:= (h.colorBlock (wt i) w b (z:=u) (i:=i) rfl rfl rfl)
    have hl:= h.cost_vol false; have hr:=h.cost_vol true
    have ha:x.rite (p.OutC c) (transformed ⟨_,centerK⟩ (p.badge0 b false).check)
                  (p.probeX b false s.l.x ((film s 0 0).info,w)):=importD _ (Board.centeral s i 0)
                                     (higher (hW b) hl.2.2.2.1 hl.2.2.2.2)
    have hb:=higher ((hw i hi).2 b) hr.2.2.2.1 hr.2.2.2.2
    have hh:= Seats.blankD (rocks (h.goodF i 0)) hl.2.2.1
    unfold Game; split
    · next e=>
      obtain ⟨h1,h2,h3⟩:=hz.mp e
      exact ⟨steer ha (fun he=> (h3 he).elim) (fun hi=>steer hb (fun he=> (h2 he).elim)
                                     (fun _=> higher hg.1 hl.1 hl.2.1)),punct_up hg.2 hl.2.1⟩
    next e=>
      refine ⟨steer ha (fun _=>hh) (fun hA=>steer hb (fun _=>hh) ?_),punct0 (stable_home h.align).1 hl.2.2.1⟩
      intro hC
      have h1: d.tag i=0:=by by_contra he; apply e (hz.2 ⟨he,hC,hA⟩)
      rw [h1] at hg; exact higher hg.1 hl.1 hl.2.1

abbrev voteC(p:Cage)(c:ℕ):=16*(16*p.OutC c)
lemma shoots {u:Ballot d}(he:Style p s d θ c u)(i:ℕ)(b:Bool):
     let v:= valN p _ u b i
     (film s i 0).rite (voteC p c) (p.belt b) v ∧ Punct s.head (voteC p c) v:=by
    dsimp only
    let m:=p.OutC c
    let S:=film s i 0
    have hl:= (h.cost_vol true).2.2.1
    let q:=p.shaft b
    have hu : q.b.key S.head=i:=by simp [q,shaft,Branch.key,fellow,leftQ,S,film,info,panelx]
    have hz : Punct S.head m (q.N S):=by
       have he1:= lb_le_inc p.m
       change lb p.m +1 ≤ p.OutC c*s.d
       unfold OutC goodz; rw [h.hi]; omega
    have hA:= q.earns (rocks (h.goodF i 0)) hl (Game p d u b) hz (fun j hj=>by
         have hv:S.bench q.b j=film s j 0:=by
             simp [S,bench,film,q,shaft,fellow,Branch.port,panelx,stairs]
         rw [hv]; exact ⟨(he.serve j hj b).2,(he.serve j hj b).1⟩)
    dsimp only at hA
    rw [hu] at hA
    exact ⟨hA.2,punct_up hA.1 (by unfold voteC; omega)⟩

end Ink

namespace Style
variable {p s d θ c u}(h:Style p s d θ c u)
include h
omit h in
lemma markers {o T} (hx:p.Ink s d θ o c T)(b): Seek.part (Game p _ u b) p.m=
         (range d.n).filter (ColorF.hoot d u.wt b):=by
   unfold Seek.part; rw [hx.mp]; ext i; simp only [mem_filter]
   by_cases hp:ColorF.hoot d u.wt b i
   · have hs:d.tag i≠0:=hp.1
     unfold Game; rw [ite_eq_left hp]; simp only [hp]; tauto
   unfold Game; rw [ite_eq_right hp]; simp only [hp]; simp
lemma ck {o T} (hx:p.Ink s d θ o c T)(b):(Seek.part (Game p _ u b) p.m).card ≤ p.k:=by
    rw [(markers (u := u)) hx,← h.rightP]; exact hx.ok.amount0 h.legally (h.height.symm ▸ hx.ht0) b

abbrev child(p:Cage)(d:Depot)(u:Ballot d)(b:Bool)(i:ℕ):ℕ:=Relay.mark (valN p _ u b i)
def listed(p:Cage)(d:Depot)(u:Ballot d)(b:Bool)(i:ℕ):Prop:= valN p d u b i≠0
omit h in
lemma park {b i}(hi:listed p d u b i):
     let k:=child p _ u b i
     ColorF.hoot d u.wt b k ∧ valN p d u b i=Seek.bin k (Game p _ u b k)∧(Seek.part (Game p d u b) k).card=i:=by
    let v:=Game p d u b
    obtain ⟨j,hj,hr,hg⟩:= (Seek.casebook v i p.m).resolve_left hi
    have hs:child p d u b i=j:=by change Relay.mark ((Seek.relief v i p.m).2)=_; rw [hg]; simp [Seek.bin,Relay.mark]
    have hh:v j≠0:=(mem_filter.1 hj).2
    dsimp only; rw [hs]
    unfold v Game at hh; split at hh
    · exact ⟨by assumption,hg,hr⟩
    contradiction
lemma many {b i}(hi:listed p d u b i){T o}(hx:p.Ink s d θ o c T):i<p.k:=by
    have ht:= not_le.1 (mt Seek.missed.2 (show (Seek.relief (Game p _ u b) i p.m).2≠0 from hi))
    exact ht.trans_le (h.ck hx b)
omit h in
lemma hears {T o b i} (hx:p.Ink s d θ o c T)(he:ColorF.hoot d u.wt b i):∃ j,listed p d u b j∧child p d u b j=i:=by
    let v:=Game p d u b; let u0:=(Seek.part v i).card
    have ha : v i≠0:=by unfold v Game; rw [ite_eq_left he]; exact he.1
    have hg:valN p d u b u0=Seek.bin i (v i):=Seek.order ((hx.ok.card0 i he.1).trans_eq hx.mp) ha rfl
    refine ⟨u0,?_,?_⟩
    · unfold listed; rw [hg]; exact ne_of_gt (Seek.binpos ..)
    unfold child; rw [hg]; simp [Seek.bin,Relay.mark]
omit h in
lemma lonely {T o b i j}(hx:p.Ink s d θ o c T)
    (ht:listed p d u b i)(he:listed p d u b j)(hp:d.pos (child p d u b i)=d.pos (child p d u b j)): i=j:=by
   have ha:=(park (p := p) (d := d) (u := u)) ht; have hz:=(park (p := p) (d := d) (u := u)) he
   dsimp only at ha hz
   have hb:=hx.ok.uniq _ _ ha.1.1 hz.1.1 hp
   rw [hb,hz.2.2] at ha; exact ha.2.2.symm
end Style
end
end ExactDerandomization.Stem.Cage

end

section

namespace ExactDerandomization.Stem.Cage
open Counter Relay Rill Fret Reed Analysis Hie At Finset Seats Buf Lu Depot.Trust Ink
open Lyric
noncomputable section
open scoped Classical
variable (p:Cage) (s:Seats)(d:Depot)(θ:ℝ)(o:Bool→Trio)(c T:ℕ)
abbrev zbase (b:Bool):Lyric:= Lu.son 0 (p.root b)
abbrev rearmM(x:Word)(i:History):ℕ:= stairs true x (i.1,Relay.mark i.2)
lemma rearmK : Kn rearmM:= (stairK true).comp (Kn.first.tuple (((Kn.unpack (α:=History)).comp Kn.next).left))
abbrev fruit (b:Bool) :=let v:=campk p.kn
                         let q:=p.belt b
                         Cargo.choose q ((p.zbase b).choir v)
                           (Cargo.combine q ((p.figure b).choir v) ⟨_,rearmK⟩)
abbrev exitP (c:ℕ)(b:Bool):= (p.figure b).cost c
abbrev lastP (c:ℕ):= voteC p c+200+p.exitP c true+p.exitP c false
abbrev totalG(c:ℕ):=4*p.lastP c
abbrev skyG:=prepare p+(p.figure true).tail+(p.figure false).tail

abbrev spice (p:Cage)(d:Depot)(i:ℕ)(o:Bool→Trio)(b:Bool) (u:Ballot d):ℝ:=
    if valN p d u b i=0 then 0 else d.y.val d.S p.k (o b) (d.pos (Style.child p d u b i))

namespace Ink
variable {p s d θ o c T}(h:Ink p s d θ o c T)
include h
lemma spaceG: 1  ≤  voteC p c ∧ voteC p c ≤ p.lastP c ∧ p.lastP c  ≤ p.totalG c:=by
    have he:=(h.cost_vol true).2.2.1; unfold lastP totalG; unfold lastP voteC at *; omega
theorem fruitage {u:Ballot d}(hs:Style p s d θ c u)(i b) (H:ℕ)
   (hk:H+p.skyG*s.d ≤ T):
    (film s i 0).band (p.totalG c) H (p.root b) (p.fruit b) (spice p d i o b u):=by
   have ⟨hC,hD,hH⟩:=h.spaceG
   let q:=p.belt b; let j:=valN p d u b i; let C:= p.lastP c
   have hu:=h.shoots hs i b
   have hp:= h.goodF i 0
   have hj: (film s i 0).rite C q j:= higher hu.1 hC hD
   have hc:1 ≤  C:=hC.trans hD; have hm:1 ≤ c:=by have:=h.hc; omega
   have hA:H+(p.figure b).tail*s.d  ≤  T:=by
       have he:(p.figure b).tail  ≤  p.skyG:=by cases b <;> unfold skyG <;> omega
       exact (Nat.add_le_add_left (Nat.mul_le_mul_right s.d he) H).trans hk
   apply Seats.avis (higher hj hc hH)
   · intro hz
     unfold spice; rw [ite_eq_left hz]
     let f:=p.zbase b
     have hf: Chor (campk p.kn) c T (film s i 0) f 0:=by
        have ht:Lu.Standard (film s i 0) (campk p.kn) T:=⟨hp,spanFilm h.expire i 0⟩
        convert ht.shins c (p.root b) 0 (by simp) using 1; norm_num
     exact flex (sing hf hm (H:=H) (by have he:H  ≤  T:= (Nat.le_add_right ..).trans hA
                                       simpa only [f,zbase,tail,son,zero_mul,add_zero]))
             (Lyric.cost_hi hm) (by change powder 100  ≤  4*(p.lastP c); unfold lastP powder; omega) le_rfl
   intro hj0
   let a:=Style.child p d u b i
   have ht : Style.listed p d u b i:= hj0
   have hh:d.live a:=(Style.park ht).1.1
   have ha:berth ⟨_,rearmK⟩ (film s i 0) j= film s a 0:=by
       simp only [berth,j,a,film,info,panelx,Style.child,rearmM,stairs,Reed.V,dec_round,ite_true]
   apply advises (rocks hp) (punct_up hu.2 hD) hc hj
   rw [ha]
   unfold spice; rw [ite_eq_right hj0,←h.seats0 b]
   apply flex (sing (h.sculpt hh b) hm hA) (cost_hi hm) _ le_rfl
   change p.exitP c b  ≤  C; unfold C lastP; cases b <;> omega
end Ink

structure Harvest (u:Ballot d):Prop where
    style:Style p s d θ c u
    budget:1 ≤ p.totalG c
    stem :∀ i b, (film s i 0).rite (p.totalG c) (p.belt b) (valN p d u b i) ∧
                                       Punct s.head (p.totalG c) (valN p d u b i)
    song:∀ i b H,H+p.skyG*s.d  ≤  T→
                (film s i 0).band (p.totalG c) H (p.root b) (p.fruit b) (spice p d i o b u)

lemma bloom (h:Ink p s d θ o c T) (hp:p.skyG*s.d ≤ T):∃ u,Harvest p s d θ o c T u:=by
   obtain ⟨u,hv⟩:= h.chose (show _ from (Nat.mul_le_mul_right _ (show prepare p  ≤  p.skyG by unfold skyG; omega)).trans hp)
   obtain ⟨h1,h2,h3⟩:=h.spaceG
   exact ⟨u,hv,h1.trans (h2.trans h3),fun i b=>⟨higher (h.shoots hv i b).1 h1 (h2.trans h3),
            punct_up (h.shoots hv i b).2 (h2.trans h3)⟩,h.fruitage hv⟩

end
end ExactDerandomization.Stem.Cage

end

end OAI
