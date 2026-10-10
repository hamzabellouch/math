import OAI.Computability.Logspace.RowEvaluation

namespace OAI

/-!
Programs evaluating transitions and the next level of the probability hierarchy.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Tiber
open Analysis Counter Relay Rill Fret Finset Mint Swirl Grain Net At Est Hie Stage
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Chime Scheme
open Dome Cone ConeX Glass Glass.Rod
open Reed Fret.Seats SiteX Terrain Bank Arena Song
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Sky

def whichSide (b:Bool) (x:Word)(a:ℕ):ℕ:= if b then (V x a).2.1 else (V x a).2.2
lemma whoK(b):Kn (whichSide b):=by cases b;exact VK.right.right;exact VK.right.left
def pre (k o:ℕ) (f:Cub ℕ ℕ)(x:Word)(a:ℕ):ℕ:=
   hole (pointer (V x a).1 k) (hole o (f.f x a))
abbrev pK(k:ℕ):Kn (fun x a=>pointer (V x a).1 k):=
    Kn.wash.comp ((Kn.fix k).tuple ((Kn.unpack (α:=Crt)).comp VK.left).right)
def seek (k o:ℕ)(f:Cub ℕ ℕ): Sight:=
     ⟨_,Kn.wash.comp ((pK k).tuple (Kn.wash.comp ((Kn.fix o).tuple f.runs)))⟩
abbrev tag(k o:ℕ)(b:Bool):Cog:=Dome.Bullet.snap (seek k o ⟨_,whoK b⟩)

def rocket (_:Rock q w h)(k : Mode)(b:Bool):Sight:=
   let v:NoteM:= Helix.Torch.waxy (Helix.Torch.charm k b)
   ⟨_,Kn.wash.comp ((pK 2).tuple (Kn.wash.comp ((whoK (pivot k)).tuple (Kn.fix v))))⟩
def globe (r:Rock q w h) :Glass.Eye:= ⟨⟨_,r.nKn⟩,fun k b=>Bullet.snap (rocket r k b)⟩
def queryEq (r:Rock q w h) :Cog:=
    let a:= globe r
    let u:= Flash.plumb 1
    let b:= tag 1 0
    let f:=Flash.demand (b false) (a.nexts 4 u Cargo.knock)
    Flash.demand (b true) f

def rimN (k:Knob)(u:ℕ):Sight:=⟨_,Kn.power u k.bank.runs⟩
def spilt (p:Knob)(i:ℕ):Cub CoinQuery Coin:=
    ⟨_,Coin.invK ((scaleK (campk p) i).comp Kn.first)⟩

variable (p:MintV) (r:Rock q w h) (v: Tags)
def stadium: Board:=
   let k:= Mold.knob r v
   { n:=rimN k p.vol
     I:=k, kth:=fun b=> if b then ⟨_,Kn.fix r.w.p.K⟩ else rimN k (Rain.CarryE r.w)
     reserveC:=Brick.solo (campk k) (spilt k (fexpo 2)) p.inputH
     equal0:=queryEq r
     pigment:= tag 1 0 true
     baseC:=Bullet.snap (seek 1 5 ⟨_,Kn.fix 0⟩)
     pot:=fun b=>tag 1 (if b then 1 else 2) false
     inp:=p.inputH,lid:=p.sealR
     lips:= fexpo 2,cup:=p.vol+1 }
abbrev wafer(k):= stadium p r k
def bodyP (i:ℕ):Cog:=
    let s:=stadium p r v
    if i=0 then s.shift else if i=1 ∨ i=2 then s.rateMood (i==1) else s.primary
abbrev progP := Studio.arrange (bodyP p r v) 5
abbrev coverC :ℕ:=p.vol+Cambria.Era.tariff r+4

abbrev baseC :Board:= stadium p r ⟨0,0,0,0,0,0⟩
def festival (w:Board)(c:ℕ):ℕ:=c+w.prompt+w.totalC c
def budget0 :ℕ:=
    let w:=baseC p r; let c:=coverC p r; festival w c
namespace Estate
open Board Fret.Lyric Cambria.Wear.Paper Fret.Lyric Holds Lu
lemma pile (b:Bool)(p q:Branch)(he:p.e=q.e){f g:Lyric}(h:same f g):
    same (.heap b p f) (.heap b q g):=by
    obtain ⟨ha,hb,hc⟩:=h
    simp only [Cambria.Wear.Paper.same,Lyric.weight,Lyric.tail,Lyric.cost,he,ha,hb,hc,Branch.reserve,Branch.foldC]; simp

lemma sta {f:Board}{g:Board}
   (hi:f.inp=g.inp)(hl:f.lid=g.lid)(hc:f.cup=g.cup)(he:f.lips=g.lips):
    f.prompt = g.prompt ∧ ∀ c,f.totalC c =g.totalC c:=by
   have h1(b:Bool):same (f.rowB b) (g.rowB b):=by
     cases b
     · exact oneself _
     unfold rowB; rw [hi]; exact use _ _ _
   have h2(b:Bool):same (f.bites b) (g.bites b):=by
     refine (h1 b).plies (pile _ _ _ hc ?_) _
     rw [hi]; exact use _ _ _
   have hX {x y:Lyric}(h:same x y):same (Lu.absE x) (Lu.absE y):=
        h.plies ((oneself _).plies h _) _
   have h3:same f.sight g.sight:= (hX (h2 true)).plies (hX (h2 false)) _
   have h4(b):same (f.starsR b) (g.starsR b):=by
        refine (h1 true).plies (pile _ _ _ hc ((use _ _ _).plies ?_ Doop.prod)) _
        cases b; exact h3; exact h2 true
   have h5:same f.riseR g.riseR:=by
        apply same.plies (oneself _)
           (same.plies (show same (.use f.inp f.reserveC) (.use g.inp g.reserveC)
                                              from by rw [hi];exact use ..) (h4 false) Doop.greater)
   have h6:same f.shore g.shore:=
      (oneself _).plies ((oneself _).plies (h3.plies ((oneself _).plies h5 _) _) _) _
   have hz:same f.zenith g.zenith:=
      (oneself _).plies (h5.plies ((h4 true).plies ((oneself _).plies h5 _) _) _) _
   have h7(b):same (f.border b) (g.border b):=by cases b; exact oneself _; exact hz
   have hu:same f.harsh g.harsh := ((oneself _).plies h3 _).plies ((oneself _).plies h5 _) _
   have OK{x y u v:Lyric}(h:same x y)(e:same u v) : same (Lu.clippy x u) (Lu.clippy y v) :=
           h.plies (((oneself _).plies h _).plies e _) _
   have h8(b):same (f.surf b) (g.surf b):= (h7 b).plies (OK h6 ((h2 b).plies (h7 b) _)) _
   have hg:same f.topE g.topE:=by unfold Board.topE; refine ?_; cases f; cases g; dsimp only at hl; subst_vars; exact everF
   have hr(b):same (f.guardE b) (g.guardE b):=by unfold guardE; rw [hl]; exact (OK hg (h8 b)).stow _
   have hy(b):same (f.borderE b) (g.borderE b):=by unfold borderE;rw [hl];exact (h7 b).stow _
   have hm(b): f.hills b=g.hills b:=by unfold hills; rw [(hr b).2.1,(hy b).2.1]
   have hV(c b): f.vibes c b=g.vibes c b:=by unfold vibes; rw [(hr b).2.2,(hy b).2.2]
   refine ⟨?_,fun c=>?_⟩
   · unfold Board.prompt Board.burn Test.extra Test.draw
     rw [hm,hm,h5.1,h5.2.1,he,hu.1,hu.2.1]
   unfold Board.totalC tuneC payC Board.bankC Badge.tariff Badge.tariffStart Test.seatC
   change 4*(16*(16*(4*Oven.price (_ + Test.draw f.riseR 0 +100)+4*Oven.price (_ +Test.draw f.harsh f.lips+100)+_))+_+_+_)=_
   simp only [Board.heatp,Board.touchp,Test.arm,Test.draw,h5.1,h5.2.2,hu.1,hu.2.2,he,hV]
end Estate
lemma booster(a b c d e:ℕ)(h:a=d)(hp:b=e) : c ≤ c+d+e∧a ≤ c+d+e∧b ≤ c+d+e:=by omega
lemma swamp (f g:Board)(c:ℕ) (hi:f.inp=g.inp)(hl:f.lid=g.lid)(hc:f.cup=g.cup)(he:f.lips=g.lips):
       c ≤ festival g c∧f.prompt ≤ festival g c∧f.totalC c ≤ festival g c:=by
   have ⟨h1,h2⟩:=Estate.sta hi hl hc he
   rw [h1,h2];unfold festival; omega

lemma funded :
   coverC p r  ≤ budget0 p r ∧ (stadium p r v).prompt ≤ budget0 p r ∧
                           (stadium p r v).totalC (coverC p r) ≤ budget0 p r:=
    swamp (stadium p r v) (baseC p r) (coverC p r) rfl rfl rfl rfl
end Sky

namespace SliceD
open Line Line.Fabric Sky
structure Fire (u:Line (q:=q) (w:=w) (h:=h)) where
    p:MintV
    v:Fabric u
    i:ℕ
    x:ℕ
namespace Fire
variable (v:Fire u)
abbrev inc := v.v.α v.p v.i
abbrev bud:= v.v.β v.i
abbrev frame := stadium v.p u.r u.v
abbrev cost := coverC v.p u.r
abbrev a:= v.bud.dataN
abbrev pond:= Studio.dockA u v.a v.x
abbrev d := v.pond.d
abbrev μ := gap v.v.m v.i
abbrev h0 := u.D.high v.a
abbrev H := v.h0 + budget0 v.p u.r * v.d
abbrev pan(i j):=film v.pond i j
structure Lamp0(v:Fire u) : Prop where
    he:Terrain.Stone.Rector v.v v.p
    hz :v.i < Age.L v.v.m
    ha:v.v.activeR
    hx:v.x∈u.D.P
    veil:u.wick0.Veil u.torch v.inc.visN
    heat: budget0 v.p u.r ≤ u.v.slope

namespace Lamp0
variable {v:Fire u} (h0:v.Lamp0)
include h0

lemma againC : v.inc.Front u:= h0.he.frontI h0.ha v.i h0.hz
lemma primal : v.bud.Front u := h0.he.frontP h0.ha v.i h0.hz
lemma aimD : u.D.Suite v.a := h0.he.chart.rent h0.primal.pos
omit h0 in
lemma jump : u.D.D v.inc.dataN=v.d ∧ u.D.W v.inc.visN+v.d ≤ u.D.W v.a ∧ u.D.W v.inc.dataN+v.d ≤ u.D.W v.a:= by
    change u.D.D (v.v.c 1 v.i)=u.D.D (v.v.c 3 v.i)∧ u.D.W (v.v.c 2 v.i)+u.D.D (v.v.c 3 v.i) ≤ u.D.W (v.v.c 3 v.i)∧
                                  u.D.W (v.v.c 1 v.i)+u.D.D (v.v.c 3 v.i)≤_
    rw [Terrain.Stone.D,Terrain.Stone.D,Terrain.Stone.W,Terrain.Stone.W,Terrain.Stone.W]
    exact ⟨rfl,Age.sooner rfl (by omega) (by omega), Age.sooner rfl (by omega) (by omega)⟩
omit h0 in
lemma price :4 ≤ v.cost∧ Bullet.roomS ≤ v.cost∧powder 100≤ v.cost ∧ Cambria.Era.tariff u.r ≤ v.cost:=by
    have hr:= Cambria.Era.billed u.r
    unfold cost coverC;omega
omit h0 in
lemma height0 : v.d=v.μ:= by
    change u.D.D (v.v.c 3 _) =_
    rw [Terrain.Stone.D];rfl
lemma stored(i j) : Reed.Lu.Standard (v.pan i j) (campk v.frame.I) v.H:=by
    have ht:v.H ≤ u.D.H:= Studio.stayedC h0.aimD le_rfl h0.heat
    exact ⟨Studio.positioned h0.aimD h0.hx i j,spanFilm (Studio.vital (u:=u) v.H ht) i j⟩
omit h0 in
lemma urn (i j) (b:Bool)(k):
     (seek 1 k ⟨_,whoK b⟩).f (v.pan i j).l.x (v.pan i j).info=
                           hole v.inc.dataN (hole k (if b then i else j)):=by
   change Sky.pre 1 k _ _ _=_
   unfold Sky.pre whichSide pan Seats.l film
   cases b <;> simp only [Reed.V, Seats.info, dec_round]
   · rw [show pointer v.pond.info 1=v.inc.dataN from Stone.pointing ..]
   rw [show pointer v.pond.info 1=v.inc.dataN from Stone.pointing ..]

omit h0 in
lemma quoted(i j)(p:Mode)(b:Bool):
    (rocket u.r p b).f u.x (v.pan i j).info =
             hole v.inc.visN (enc ((if pivot p then i else j),Helix.Torch.waxy (Helix.Torch.charm p b))):=by
   let z:=v.pan i j
   change hole (pointer (Reed.V u.x z.info).1 2) (enc (whichSide (pivot p) u.x z.info , _))=_
   have hp:Reed.V u.x z.info=(v.pond.info,i,j):=dec_round ..
   rw [show whichSide _ u.x z.info= (if pivot p then i else j) from ?_,hp]
   · rw [show pointer v.pond.info 2=v.inc.visN from Stone.pointing ..]
   unfold whichSide;rw [hp]

omit h0 in
lemma moderate (p:Mode)(b:Bool):u.wick0.Ok (Helix.Torch.waxy (Helix.Torch.charm p b)):=by
    have hi:=NeZero.pos u.n
    apply And.intro _ ⟨hi,Nat.zero_le _⟩
    exact Helix.Torch.housed u.r u.v u.x (by change Helix.Torch.innate p ≤ 16; cases p<;>decide) (Nat.zero_le _) (Nat.zero_le _)
               (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
end Lamp0
end Fire
end SliceD
end
end ExactDerandomization.Tiber

end

section

namespace ExactDerandomization.Tiber.SliceD.Fire
open Analysis Counter Relay Rill Fret Finset Mint Swirl Grain Net At Est Hie Stage
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Chime Scheme
open Dome Cone ConeX Glass Glass.Rod
open Reed Fret.Seats SiteX Terrain Bank Arena Song
open Tiber.Sky Line Line.Fabric
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {v: Fire u}
structure Bindq (q:v.v.Yolk v.p v.i v.x):Prop where
   lamp:v.Lamp0
   money:v.v.YFine v.p v.i v.x q
   tagB:∀ i,q.raw.tag i  ≤ Cambria.Era.budget u.r

namespace Bindq
variable {f:v.v.Yolk v.p v.i v.x} (hf:Bindq f)
include hf
lemma fits (i:ℕ)(hi:i<f.raw.m):u.smallQ v.inc.dataN i:= hf.lamp.againC.awake (hf.lamp.againC.size0 _ (by rwa [← hf.money.ns]))
lemma trunk(i a b:ℕ):Punct (v.pan a b).head v.cost (f.raw.tag i):=by
    have he := hf.tagB i; have ht:= lb_le_inc (f.raw.tag i)
    have hp:4+Cambria.Era.budget u.r ≤ v.cost:=by
                 have hz:=(Lamp0.price (v := v)).2.2.2; unfold Cambria.Era.tariff at hz; omega
    have hd:1≤ v.d:= hf.lamp.aimD.well.1; change _ +_ ≤ _ *v.d;nlinarith

lemma stepC (b:Bool) (i j:ℕ)(hi:(if b then i else j)< f.raw.m):
    (v.pan i j).rite v.cost (tag 1 0 b) (f.raw.tag (if b then i else j)):=by
      let n:= if b then i else j
      have ht:= hf.lamp
      have hq:=ht.againC
      have hs:u.smallQ v.inc.dataN n:=hf.fits _ hi
      have hm:=hf.money.found.next n hs
      apply Bullet.copy u.D ht.aimD ((by omega:2 ≤ 4).trans (Lamp0.price (v := v)).1) ht.hx (Lamp0.jump (v := v)).2.2 _ (hf.trunk n i j) hm
      exact (Lamp0.urn (v := v)) i j b 0

lemma glows (m:Mode) (b:Bool) (i j:ℕ) (hi:(if pivot m then i else j) < f.raw.m)
    (hv:f.raw.valid (if pivot m then i else j)){c:Pane}(hz:u.D.r.proper c):
   let x:=v.pan i j; let q:= x.seat (glove c v.x)
   let e:= f.raw.place (if pivot m then i else j)
   q.comp 0 v.cost ((globe u.r).visit m b) (0,q.src) (0,glove (pigment u.D.r m b e c) v.x):=by
    dsimp only
    let n:=if pivot m then i else j; let c' := Helix.Torch.charm m b
    let p:= Helix.Torch.waxy c'
    let e:= f.raw.place n
    let D:=u.D
    have hT:= hf.money.found
    have hs:= hf.lamp; have ht:= (Lamp0.moderate (u := u)) m b
    have hk:= hT.road n (hf.fits n hi)
    rw [ite_eq_right hv] at hk
    have hc := hs.veil _ _ ht v.x _ hk _ hz
    let f':= pigment D.r m b e c
    have ho:e ≤ u.n:=Nat.le_of_lt_succ (mem_range.1 (hT.places n hv (hf.fits _ hi)))
    have hg:u.torch.lit u.x p e c=(false,f'):=by
       rw [Helix.Torch.litwax u.r u.v u.x (coneX u.r u.s.pave) c' c e ho,Helix.Torch.litmode]
       rfl
    have hb:u.wick0.state u.torch p v.x (some (f.raw.tag n,e)) c=(0,glove f' v.x):=by
         unfold Harp.Wick.state; change (enc (u.torch.lit u.x p e c).1,glove (u.torch.lit u.x p e c).2 v.x)=_; rw [hg];rfl
    have hp:D.talk (Harp.quoteQ v.inc.visN n p) (glove c v.x) (0,glove f' v.x):= hb ▸ hc
    have he:D.r.proper f':=by
        have he: u.D.r.proper (u.torch.lit u.x p e c).2 := (Helix.Torch.life u.r u.v u.x u.prog
                                    (coneX u.r u.s.pave) hs.aimD.shape.price).sober p ht _
                                    (mem_range.2 (Nat.lt_succ_of_le ho)) _ hz
        rwa [hg] at he
    have hP:= hs.aimD; have hh: 2 ≤ v.cost:= (le_trans (by decide) (Lamp0.price (v := v)).1)
    exact Bullet.past D hP hh hs.hx (Lamp0.jump (v := v)).2.1 (Lamp0.quoted (v := v) i j m b) 0 0 v.x hs.hx
                     (Arena.Pier.seal0 _ hP hh (q:=(v.pan i j).info)) hz he hp

set_option maxHeartbeats 800000 in
lemma equalityP (i j:ℕ)(hi:i < f.raw.m)(hj:j<f.raw.m):
    (v.pan i j).rite v.cost (queryEq u.r) (Reed.Board.gcat f.raw i j):=by
   let s:=v.pan i j
   let R:= hf.lamp.aimD; have hc : 2 ≤ v.cost:= (le_trans (by decide) (Lamp0.price (v := v)).1)
   let a:=f.raw.tag i; let b:=f.raw.tag j
   let x:= f.raw.place i; let y:=f.raw.place j
   let t :ℕ:= if x=y then 1 else 0
   have hp: Reed.Board.gcat f.raw i j = Flash.win a (Flash.win b t):= by
       dsimp only [Reed.Board.gcat,Flash.win,t,a,b,x,y]; unfold Poolx.pals Poolx.joins Poolx.valid; grind
   rw [hp]
   apply Flash.wanted u.D R hf.lamp.hx hc a (Flash.win b t) (hf.stepC true i j hi)
   intro h
   apply Flash.wanted u.D R hf.lamp.hx hc b t (hf.stepC false i j hj); intro h'
   rintro n ⟨p,hp,rfl⟩
   let r:=globe u.r
   let q:=postcard s.info 0
   let m:Eye.Mantle:=⟨u.D.l,q,⟨u.D.W v.a,0⟩,v.cost,v.d,v.x⟩
   have hs:Eye.Twirl r m x y:=by
        constructor
        intro e he k b
        let i':= if pivot k then i else j
        have hl:i'<f.raw.m:=by unfold i'; split <;> assumption
        have hv:f.raw.valid i':=by unfold i';split
                                   · exact h
                                   exact h'
        have ht:= hf.glows k b i j hl hv he
        cases hq : pivot k <;> simp only [hq,ite_false,ite_true,Bool.false_eq_true] at *
        · exact ht
        exact ht
   have hx(v:ℕ)(hv:v<f.raw.m)(hm:f.raw.valid v) :
          f.raw.place v  ≤ u.n:= Nat.le_of_lt_succ (mem_range.1 (hf.money.found.places v hm (hf.fits _ hv)))
   let l:=glove p v.x
   apply hs.done0 hp (hx i hi h) (hx j hj h')
   · intro hh
     change (s.seat l).comp 0 _ _ _ (t,l); rw [show t=1 from ite_eq_left hh]
     exact Flash.pureQ u.D R hf.lamp.hx hc 1 (Pier.seal1 _ R hc (q:=s.info)) l ⟨p,hp,rfl⟩
   intro hh; change (s.seat l).comp 0 _ _ _ (t,l); rw [show t=0 from ite_eq_right hh]
   exact blankD (R.pit hf.lamp.hx _) hc _ ⟨p,hp,rfl⟩

end Bindq
end
end ExactDerandomization.Tiber.SliceD.Fire

end

section

namespace ExactDerandomization.Tiber.SliceD.Fire
open Analysis Counter Relay Rill Fret Finset Mint Swirl Grain Net At Est Hie Stage
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Chime Scheme
open Dome Cone ConeX Glass Glass.Rod
open Reed Fret.Seats SiteX Terrain Bank Arena Song
open Tiber.Sky Line Line.Fabric Fret.Lyric
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {v: Fire u}

lemma bolt {s:Seats}{I:Knob}(H i T:ℕ)(h: Lu.Standard s (campk I) H):
   let w:= (massB i s.d)⁻¹
   Chor (campk I) 1 H s (.solo T (spilt I i)) w:=by
   intro w
   let k:=campk I
   let v:=scaleC k i s.l.x s.info
   have ht:w=(Coin.inv v).v:=by unfold w v; rw [Coin.inv0]; rw [show (scaleC k i s.l.x s.info).v=massB i s.d from scalen (stable_home h.st) _]
   rw [ht]; apply Chor.played h.st h.he (fun _ _=>rfl)
   rw [Coin.inv0,show v.v=massB i s.d from scalen (stable_home h.st) _,abs_inv,abs_of_pos (mass0 ..)]
   exact le_trans (inv_le_one_of_one_le₀ (mass1 ..)) (mass1 ..)

namespace Bindq
variable {f:v.v.Yolk v.p v.i v.x}(hf:Bindq f)
include hf
lemma amp :v.pond.stable v.frame.I ∧ Live v.pond.head v.frame.I v.H:=by
    let r:= v.frame; let a:=v.a
    have h:=hf.lamp
    have he:= h.aimD
    have hp: v.H ≤ u.D.H:=Studio.stayedC he le_rfl h.heat
    exact ⟨Mold.knows u.r u.v u.x u.prog a v.x (of_decide_eq_true he.stage) h.hx he.shape.price,Studio.vital _ hp⟩
omit hf in
lemma qpres(i): (seek 1 5 ⟨_,Kn.fix 0⟩).f u.x (v.pan i 0).info=hole v.inc.dataN (hole 5 0):= by
   let a:=V u.x (v.pan i 0).info
   have hz:a=(v.pond.info,i,0):=dec_round ..
   change hole (pointer a.1 _) _=_
   rw [hz]; exact congrArg (fun a=>hole a (hole 5 0)) (Stone.pointing _ _ _ _)
lemma qcall(i): (v.pan i 0).band v.cost v.H v.p.inputH v.frame.baseC f.raw.b:=by
    have hp:= hf.lamp
    have hz:= hp.aimD
    obtain ⟨hd,he,hx⟩:= (Lamp0.jump (v := v))
    have hv:=hf.money.baseX
    rw [show v.v.c 1 v.i=v.inc.dataN from rfl,hd] at hv
    apply Bullet.clef u.D hz (Lamp0.price (v := v)).2.1 hp.hx hx ((Bindq.qpres (v := v)) i) (Studio.soonerC hz hx hp.heat le_rfl) hv
lemma qstamp {b:Bool}(i j:ℕ)(hj:j<f.raw.m):
     (v.pan i j).band v.cost v.H v.p.inputH (v.frame.pot b) (Reed.sideq (f.raw.chip j) b):=by
    have hp:=hf.lamp
    have hz:=hp.aimD
    obtain ⟨hd,he,hx⟩:=(Lamp0.jump (v := v))
    have hv:=(hf.money.hue b).ready j (hf.fits j hj)
    rw [hd] at hv
    let k:= if b then 1 else 2
    exact Bullet.clef u.D hz (Lamp0.price (v := v)).2.1 hp.hx hx ((Lamp0.urn (v := v)) i j false k) (Studio.soonerC hz hx hp.heat le_rfl) hv

lemma leadX : f.raw.p.K=u.w0.p.K∧ f.raw.p.rho = (massB (fexpo 2) v.d)⁻¹∧
                                      f.raw.p.n=v.v.Snum v.i:=by
    rw [hf.money.params,(Lamp0.height0 (v := v))];exact ⟨rfl,rfl,rfl⟩
set_option maxRecDepth 6000 in
lemma leafC (i j:ℕ) : (v.pan i j).band v.cost v.H v.p.inputH v.frame.reserveC f.raw.p.rho:= by
   have hp:= hf.lamp.stored i j
   let k:=fexpo 2
   let K:= campk (knob u.r u.v)
   let q:Lyric:=.solo v.p.inputH (spilt (knob u.r u.v) k)
   let s:=v.pan i j
   have he1:= stable_home hp.st
   let w:= f.raw.p.rho
   have he:w=(massB k v.d)⁻¹:=hf.leadX.2.1
   apply Seats.flex (c:=powder 100) ?_ (show 1 ≤ powder 100 from by unfold powder;omega)
                           (Lamp0.price (v := v)).2.2.1 le_rfl
   have h :Chor (campk v.frame.I) 1 v.H s q w:=by
        rw [he]; exact bolt (s:=s) v.H (fexpo 2) _ hp
   exact Lyric.sing h (by omega) (by unfold q; simp [tail])

lemma sizes0 :let c:=v.frame; let _:=stable_home hf.amp.1
    c.n.f u.x v.pond.info=f.raw.m ∧ (c.kth false).f u.x v.pond.info=f.raw.p.n :=by
   intro c h
   have hp:v.frame.I.bank.f u.x v.pond.info=2^v.d:=h.2.2
   have hh1: ∀ i,(v.frame.I.bank.f u.x v.pond.info)^i=2^(i*v.d):=fun i=> by rw [hp,← pow_mul,Nat.mul_comm]
   have he: c.n.f u.x v.pond.info=2^(v.p.vol*v.d):=hh1 v.p.vol
   have hh:(c.kth false).f u.x v.pond.info= 2^(Rain.CarryE u.w0*v.d):=hh1 (Rain.CarryE u.w0)
   rw [he,hh,hf.money.ns,hf.leadX.2.2,(Lamp0.height0 (v := v))]
   exact ⟨rfl,(Bank.Green.capacityE u.w0 v.v.m v.i).symm⟩
theorem offeredR : v.frame.Holds v.pond v.cost v.H f.raw:=by
   have hp:= hf.lamp
   have hs:= hp.aimD
   have ha:= hp.he.book.saving
   have he1:1 ≤ v.d:= hp.aimD.well.1
   refine ⟨(Lamp0.price (v := v)).1,hf.money.nice,hf.amp.1,hf.amp.2,hf.sizes0.1,hf.leadX.1.symm,
                       hf.sizes0.2,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
   · rw [hf.money.ns]
     have hL:v.inc.m = 2^(v.p.vol*v.d):=by rw [(Lamp0.height0 (v := v))];rfl
     change v.inc.m<2^((v.p.vol+1)*v.d)
     rw [hL]
     exact Nat.pow_lt_pow_right (by omega) (by nlinarith)
   · rw [hf.money.ns]; unfold Punct
     rw [show v.inc.m=2^(v.p.vol*v.d) from by rw [(Lamp0.height0 (v := v))]; rfl,lb_shift]
     have hc:v.p.vol+2 ≤ v.cost:=by unfold cost coverC;omega
     change _ ≤ v.cost*v.d; nlinarith [Nat.mul_le_mul_right v.d hc]
   · exact le_trans (show (4:ℝ) ≤ 16 by norm_num) (v.p.fluc ha.tested he1)
   · rw [hf.leadX.2.1]; exact ⟨le_rfl, inv_le_one_of_one_le₀ (mass1 ..)⟩
   · exact fun i _=> hf.qcall _
   · exact fun i _=> hf.leafC _ _
   · intro i hi; exact ⟨hf.stepC true i 0 hi,hf.trunk i i 0⟩
   · exact fun i hi j hj=>hf.equalityP _ _ hi hj
   exact fun i _ j he _ b=> hf.qstamp i j he
end Bindq
end
end ExactDerandomization.Tiber.SliceD.Fire

end

section

namespace ExactDerandomization.Tiber.SliceD.Fire
open Analysis Counter Relay Rill Fret Finset Mint Swirl Grain Net At Est Hie Stage
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Chime Scheme
open Dome Cone ConeX Glass Glass.Rod
open Reed Fret.Seats SiteX Terrain Bank Arena Song Stem Buf
open Tiber.Sky Line Line.Fabric Fret.Lyric Reed.Board
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {v: Fire u}

namespace Bakin
variable (f:v.v.Yolk v.p v.i v.x)
abbrev Basket:= Broom v.frame v.pond v.cost f.raw
variable (b: Basket f)
def trackQ: HistoryC v.v v.p v.x (v.i+1):= ⟨fun i=>if v.i=i then decide (b.hot≠0) else f.hist.kap i⟩
def readP : Stem.Depot := ⟨v.v.S1,b.product,v.bud.m,b.answer,b.spot⟩
def cookP :v.v.Hinge v.p v.i v.x:=⟨trackQ f b,readP f b⟩
structure Receives (b:Basket f) :Prop where
    knows : Bindq f
    cap : Reed.Board.Page v.frame v.pond v.cost v.H f.raw b
    fixed:Studio.Parcel u v.a (progP v.p u.r u.v)
namespace Receives
variable {f:v.v.Yolk v.p v.i v.x}{b:Basket f}(he:Receives f b)
include he
omit he in
lemma beforeK {i:ℕ}(hi:i ≤ v.i): HistoryC.actual v.v (trackQ f b) i=HistoryC.actual v.v f.hist i:=by
    unfold HistoryC.actual; induction i with
    | zero=>rfl
    | succ i ih=>
      rw [Run.actual_push,Run.actual_push,ih (by omega),trackQ]
      dsimp only;rw [ite_eq_right (by omega)]
lemma earn0 :HistoryC.actual v.v (trackQ f b) (v.i+1)=b.product :=by
   have ht:= he.knows.money; have hd:= (Lamp0.height0 (v := v)); let v0:=v.v.marathon v.x
   change v0.actual _ _ _=_
   rw [Run.actual_push]
   rw [show v0.actual _ (trackQ f b).kap v.i= _ from (beforeK) le_rfl]
   have hp:v0.pm v.i=f.raw.p:=ht.params.symm
   have hw:HistoryC.R v.p v.v v.i=v.frame.R v.pond:=by
       change _=massB _ v.d; rw [hd]; rfl
   unfold Broom.product trackQ; dsimp only
   unfold Run.taken
   have hh:v0.shifted v.i (HistoryC.actual v.v f.hist v.i)=f.raw.raw:=ht.posed.symm
   rw [hp, hw, hh]
   by_cases hh':b.hot=0 <;> simp only [hh'] <;> first | rfl| simp ; grind

lemma lawful0: HistoryC.Compared v.v (trackQ f b):=by
    have ht:= he.knows.money
    constructor
    · intro i hi h
      rw [(beforeK) (show i ≤ v.i by omega)]
      by_cases he0:v.i=i
      · subst i
        rw [←ht.params,← ht.posed]
        have hb:b.hot ≠ 0:=by unfold trackQ at h; simpa using h
        exact he.cap.fell.lands hb
      exact ht.compared.cooling _ (by omega) (by unfold trackQ at h;simpa [he0] using h)
    intro i hi
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with hh|hh
    · rw [hh]; exact ht.cap
    exact ht.compared.shield _ hh

omit he in
lemma salary : v.h0+v.frame.prompt*v.d  ≤  v.H∧ v.frame.totalC v.cost ≤ budget0 v.p u.r:=
   let H:=funded v.p u.r u.v
   ⟨Nat.add_le_add_left (Nat.mul_le_mul_right v.d H.2.1) _,H.2.2⟩

abbrev coinC(v:Fire u):= budget0 v.p u.r
lemma amount :2 ≤ coinC v ∧ coinC v ≤ u.v.slope:=
   ⟨le_trans (b:=v.cost) ((by omega:2 ≤ 4).trans (Lamp0.price (v := v)).1)
                                (funded _ _ u.v).1,he.knows.lamp.heat⟩

lemma boot (i:ℕ)(hi:u.smallQ v.a i):
   u.D.swears (post v.a 0 i 0) v.x (b.answer i):=by
   have hv:= he.cap
   have hp: rite (v.pan i 0) (coinC v) (bodyP v.p u.r u.v 0) (b.answer i):=
                             higher (hv.transact i).2 hv.iex (salary).2
   exact Studio.echoTicket he.knows.lamp.aimD (by omega:(0:ℕ) ≤ 5) (by omega) hi
          he.amount.1 he.amount.2 hp he.fixed

lemma corded (i:ℕ)(hi:u.smallQ v.a i)(a:Bool):
   u.D.Voice v.a v.x (hole (if a then 1 else 2) i) (u.D.high v.a) (v.p.sealR*u.D.D v.a) (b.valueq i a):=by
   have hv:= he.cap
   let k:= if a then 1 else 2
   have hp:(v.pan i 0).band (coinC v) v.h0 v.p.sealR (bodyP v.p u.r u.v k) (b.valueq i a):=by
       cases a <;> exact Seats.flex (hv.wave _ _ _ (salary).1) hv.iex (salary).2 le_rfl
   have hk:k ≤ 5:=by unfold k;split<;>omega
   exact Studio.scoreTicket he.knows.lamp.aimD hk (by omega) hi he.amount.1 he.amount.2 le_rfl hp he.fixed

omit he in
lemma bare0: b.product.base=Poolx.Nice.Z f.raw := by unfold Broom.product; split <;> rfl
private lemma baseP_band:
    (v.pan 0 0).band (coinC v) v.h0 v.p.sealR
      (bodyP v.p u.r u.v 5) (Poolx.Nice.Z f.raw):=by
    have hp : bodyP v.p u.r u.v 5 = v.frame.primary := by
      simp only [bodyP, show (5:ℕ) ≠ 0 by decide, show ¬((5:ℕ)=1 ∨ 5=2) by decide,
        ite_false]
    rw [hp]
    exact Seats.flex (he.cap.baseP 0 v.h0 (salary).1) he.cap.iex (salary).2 le_rfl

lemma baseP :
    u.D.Voice v.a v.x (hole 5 0) (u.D.high v.a) (v.p.sealR*u.D.D v.a) b.product.base:=by
    rw [(bare0)]
    exact Studio.scoreTicket (u := u) (a := v.a) (x := v.x) (i := 0) (j := v.p.sealR)
      (c := coinC v) (o := 5) (m := 5) (H := v.h0) (f := bodyP v.p u.r u.v)
      he.knows.lamp.aimD (by omega) (by omega)
      (he.knows.lamp.he.wide0 3 v.i) he.amount.1 he.amount.2 le_rfl he.baseP_band he.fixed
lemma taxed(i:ℕ): lb (b.answer i) ≤ Bank.hu v.p u.r*v.μ:=by
     by_cases ht:b.answer i=0
     · rw [ht,lb_zero]
       have hh:0 < Bank.hu v.p u.r:=by unfold Bank.hu Bank.hi; omega
       have he:0<v.μ:=Age.gap_pos ..
       nlinarith
     have hh:=he.cap.fell
     obtain ⟨hc,hA,hB,hW⟩:= hh.locale ht
     conv_lhs=> rw [hB]
     apply he.knows.lamp.he.book.saving.bill0 (Age.gap_pos ..) _ (he.knows.tagB ..)
     have hp:= mem_range.1 (hh.there hA).1
     exact lt_of_lt_of_le hp (le_of_eq he.knows.money.ns)
lemma costed(i:ℕ):u.smallQ v.bud.visN (b.answer i):=by
     have hp:=he.knows.lamp
     apply hp.primal.back0
     change lb (b.answer i) ≤ u.eye.e*v.d
     rw [(Lamp0.height0 (v := v))]; exact le_trans (he.taxed i) (Nat.mul_le_mul_right _ (le_trans
                    (show Bank.hu v.p u.r  ≤ Bank.hx v.p u.r by unfold Bank.hx;omega) hp.he.book.cost0))
lemma harvest0 (i:ℕ)(hi:b.answer i≠0):
     i< v.bud.m∧ f.raw.valid (b.who i)∧b.spot i∈v.v.S1:=by
    have hv:=he.cap.fell
    obtain ⟨ht,hb,hc,hk⟩:=hv.locale hi
    obtain ⟨hr,hh,hs⟩:=hv.there hb; have hl:=he.knows.money
    have hm: f.raw.S=v.v.S1:=by unfold Poolx.S; rw [hl.params];rfl
    have hz:=hl.nice
    refine ⟨lt_of_lt_of_le (Broom.Fell.allot.1 hi) ((hv.capacity hz).trans ?_),hh.1,
                                               hm ▸ hz.atS _ hr hh.1⟩
    exact (le_of_eq he.knows.leadX.2.2)
lemma vault : (readP f b).Trust:=by
    let p:= readP f b
    have hp:= he.knows; have hf:=he.cap.fell
    refine ⟨?_,fun i hi=> (he.harvest0 i hi).1,fun i hi=>(he.harvest0 i hi).2.2,?_ ,?_⟩
    · change 0 ≤ b.product.base
      rw [← he.earn0]; exact (v.v.marathon v.x).actual_closed .. |>.1
    · intro i j hi hj hk; exact hf.sole hi hj hp.money.nice hk
    intro i hi hh
    have hA:4 ≤ v.frame.R v.pond:=hp.offeredR.clampR
    change b.product.ts i=line b.product.base
    rw [(bare0)]; apply hf.framed hp.money.nice hA i _ hh
    unfold Poolx.S
    rw [hp.money.params]; exact hi

lemma pegged(i:ℕ)(hi:u.smallQ v.bud.dataN i):
    u.eye.Flora u.torch.p v.bud.visN i v.x (if b.answer i=0 then none else some (b.answer i,b.spot i)):=by
    have hp:=he.knows.lamp; have hz:=he.boot i hi
    have hW:u.D.swears (post v.bud.dataN v.bud.tagop i 0) v.x (b.answer i):=hz
    let p:=v.bud
    by_cases hh:b.answer i=0
    · rw [ite_eq_left hh]; apply Flora.abs
      have hx:=hp.primal.point0 hp.he.chart i (hp.primal.back0 hi)
      refine ⟨hx,hp.hx,?_⟩
      rw [show u.eye.ear u.torch.p _ _ =_ from hp.primal.ear0 i]
      exact (u.D.identity hW).trans hh
    rw [ite_eq_right hh]
    let z:=b.who i; have hv:=he.cap.fell
    obtain ⟨hX,hL,hT,hO⟩:= he.cap.fell.locale hh
    have hr:z<f.raw.m:=mem_range.1 (hv.there hL).1
    have hk:= he.knows.money.found.caseM z (he.harvest0 i hh).2.1 (he.knows.fits z hr)
    have hc:p.visN=v.v.c 4 v.i:=rfl
    apply hp.he.chart.Rope hp.primal i v.x (b.answer i) z v.inc.visN (b.spot i) _ hi (he.costed i) hh
            hp.hx _ _ _ _ (Fabric.Good.n1 hp.he.chart hp.he.good (he.harvest0 i hh).2.2) hW hk
    · unfold Mold.offer; dsimp only
      rw [Stone.roleR, ite_eq_right (by decide:(4:ℕ)≠ 2),ite_eq_left rfl]
      exact congrArg (fun a=>rope a z) (Stone.pointing ..)
    · exact Stone.zeroR ..
    · rw [← hp.primal.grain]
      exact le_trans (Lamp0.jump (v := v)).2.1 ((Nat.le_add_right ..).trans hp.primal.price)
    rw [←hp.primal.grain,←hp.againC.grain,(Lamp0.jump (v := v)).1]; change v.d ≤ 2*v.d;omega

omit he in
lemma plates (i:ℕ)(a):b.valueq i a= Reed.sideq ((readP f b).qpoint i) a:=by
   unfold Broom.valueq Stem.Depot.qpoint; split
   · next h=> rw [ite_eq_right (show ¬(readP f b).live _ from by change ¬b.answer i≠0; rw [h]; simp)]
              rw [←(bare0)]; rfl
   next h=> rw [ite_eq_left (show (readP f b).live i from h)]; rfl

lemma tucked : v.v.HFine v.p v.i v.x (cookP f b):=by
   have hp:= he.knows
   refine ⟨he.lawful0,he.earn0.symm,rfl,rfl,he.vault,?_,?_,he.baseP,?_⟩
   · refine ⟨fun i hi=>he.boot i hi,fun i _=>he.costed i,?_,fun i hi=>he.pegged i hi⟩
     intro i hi
     by_contra hn; exact Nat.not_lt_of_ge hi (he.harvest0 i hn).1
   · intro a; refine ⟨?_⟩; intro i hi
     have hn:=he.corded i hi a; rw [plates] at hn;exact hn
   intro h i hk
   exact (he.harvest0 i hk).2.1 (hp.money.night h _)
end Receives

theorem beam0 {f:v.v.Yolk v.p v.i v.x} (h:Bindq f)(he:Studio.Parcel u v.a (progP v.p u.r u.v)):
    ∃ b, v.v.HFine v.p v.i v.x b ∧ ∀ j, lb (b.depot.tag j)  ≤  Bank.hu v.p u.r*v.μ:=by
    have ht:= funded v.p u.r u.v
    have hp:v.frame.prompt*v.d  ≤ v.H:=by
         unfold H; exact le_trans (Nat.mul_le_mul_right _ ht.2.1) (Nat.le_add_left ..)
    obtain ⟨b,hv⟩:= Reed.Board.mounted v.frame h.offeredR hp
    have hq: Receives f b:=⟨h,hv,he⟩
    exact ⟨cookP f b,hq.tucked,fun i=>hq.taxed i⟩
end Bakin
end
end ExactDerandomization.Tiber.SliceD.Fire

end

end OAI
