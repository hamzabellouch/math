import OAI.Computability.Logspace.ConfigurationEvaluation

namespace OAI

/-!
Correctness and space bounds of recursive hierarchy evaluation.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Chron
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Good
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
structure Moon (u:Line (q:=q) (w:=w) (h:=h))where
    p:MintV
    v:Fabric u
    i:ℕ
    base:Cog
namespace Moon
variable (e:Moon u)
abbrev cageX:=e.v.α e.p e.i
abbrev a:=e.cageX.dataN
abbrev d:= gap e.v.m e.i
abbrev c :Crt :=owner e.v e.i
abbrev sE:= year e.v
abbrev s:= u.plotM
structure Lo :Prop where
   majors:Stone.Rector e.v e.p
   s1:e.v.activeR
   s2:e.i< Age.L e.v.m
   term:Lily.poseX u.r=u.s.pave
   money:Wear.Paper.budgetD e.p u.r ≤ u.v.slope
   hot:Studio.Parcel u e.a (Lily.prog u.r u.v e.p e.base)
   pays: ∀ b,u.D.active b →  u.D.W b+u.D.D e.a  ≤ u.D.W e.a  →  u.wick0.Veil u.torch b
lemma baseD:u.D.D e.a=e.d:=by rw [show e.a=e.v.c 1 _ from rfl,Stone.D]; rfl
namespace Lo
variable {e:Moon u}(he:e.Lo)
include he
lemma ed:e.cageX.Front u:=he.majors.frontI he.s1 _ he.s2
lemma wpaid:u.D.Suite e.a:=he.majors.chart.rent he.ed.pos
lemma test {v:ℕ}(h:v<e.cageX.m):u.smallQ e.a v:= he.ed.awake (he.ed.size0 v h)
end Lo
def stash (E:Embellish)(x:ℕ)(beginP:Stars) (endP:ℕ  →  Stars): Nest u:=by
    let s:= E.1; let t:= E.2; let q:=enc ((e.a,E.1,E.2):GridY)
    exact ⟨⟨e.cageX, Wear.skyG,s,q,Era.tariff u.r,Era.budget u.r,x,beginP,endP⟩,t,e.p⟩

lemma heap {e:Moon u} (he:e.Lo)(q:Embellish){x}(hx:x∈u.D.P)(b f):
    let s:=e.stash q x b f
    s.ray.Good:=by
   let s:=e.stash q x b f
   apply Era.educated s.ray he.majors.book he.ed he.majors.chart rfl le_rfl hx
   change (dec (enc _):GridY).2.1=_
   rw [Wire.eq]; rfl
lemma cam {e:Moon u}(he:e.Lo)(q:Embellish) (x b f)
   (h:(e.stash q x b f).ray.Arrived):
     (e.stash q x b f).Good:=⟨h,rfl,rfl,rfl,rfl,he.money⟩
lemma loomF {e:Moon u}(he:e.Lo)(q:Embellish)(x b f)
    (h:(e.stash q x b f).Good){j}(hs:Lily.arms u.r u.x (e.a,j)=q):
      Lily.Service.Fits (e.stash q x b f) e.v e.i j:=⟨h,rfl,congrArg (fun q=> ((e.a,q):GridY)) hs,
                                                               he.term.symm⟩

end Moon

structure Coinage where
    verge : Stars
    dye:Pt
namespace Coinage
abbrev i(a:Coinage):ℕ:= iris a.verge
abbrev p(a:Coinage):ℕ:=pointE a.verge
abbrev fired (a:Coinage):Prop:=a.i≠0
def pigment (a:Coinage)(x:ℕ):Pt:= if a.fired∧ a.p=x then a.dye else 0
def dies : Coinage:=⟨none,0⟩
end Coinage
namespace Moon
variable (e:Moon u)(x j:ℕ) (g:Coinage)
structure Spend:Prop where
    below :g.i ≤ Era.budget u.r
    into :g.fired → x∈e.v.S0∧g.p∈e.v.S1
    zero0 : g.i=0 → g.verge=none∧g.dye=0
    sizes: u.smallQ e.a j →  u.smallQ e.cageX.visN g.i
    key :u.smallQ e.a j →  u.D.swears (post e.a 0 j 0) x g.i
    faith:u.smallQ e.a j →  u.eye.Flora u.torch.p e.cageX.visN j x (if g.i=0 then none else some (g.i,g.p))
    stats:u.smallQ e.a j → ∀ b,u.D.Voice e.a x (hole (if b then 1 else 2) j) (u.D.high e.a)
                                      (e.p.inputH*u.D.D e.a) (Reed.sideq g.dye b)
namespace Spend
variable {e:Moon u} {x j:ℕ} {g:Coinage}
lemma briefly (h:e.Spend x j g):g.verge=(if g.i=0 then none else some (g.i,g.p)):=by
   by_cases he:g.i=0
   · rw [ite_eq_left he]; exact (h.zero0 he).1
   rw [ite_eq_right he]; cases hv:g.verge
   · exact False.elim (he (by unfold Coinage.i; rw [hv]; rfl))
   unfold Coinage.i Coinage.p; rw [hv]; rfl
end Spend
lemma cold (e:Moon u) (s:Nest u)(l:e.Lo){x b f y E i}
    (h:s=e.stash E x b f) (he:s.Good)(hx:Lily.arms u.r u.x (e.a,i)=E)
    (ho:∀ b:Bool, Nest.Good.gross s b (Reed.sideq y b))(hn:title s=0 →  y=0)
    (hz:title s≠0 →  x∈ e.v.S0 ∧ pointE s.ray.outR∈e.v.S1):
    Spend e x i ⟨s.ray.outR,y⟩:=by
   subst s
   have ht:=loomF l E x b f he hx; let s:=e.stash E x b f
   have hv:= he.grip.wreath.1
   have hf : title s=0  →  s.ray.outR=none:=by
         intro ha; cases hX:s.ray.outR <;> try rfl
         next a=> obtain ⟨i,j⟩:=a; obtain ⟨-,k,x,b,m,h1,h2,h3,h4,h5⟩:=spark hX
                  unfold title at ha; rw [hX] at ha; change i=0 at ha; omega
   exact ⟨hv,hz,fun h=>⟨hf h,hn h⟩,fun _=>he.grip.stable.caps _ hv,
            fun hu=>ht.supplies e.base l.hot hu,fun hu=>by
             have hh:=ht.portraits e.base l.hot hu
             change u.eye.Flora u.torch.p e.cageX.visN i x (s.ray.outR) at hh
             by_cases hr:title s=0
             · change u.eye.Flora u.torch.p e.cageX.visN i x (if title s=0 then _ else _)
               rw [hf hr] at hh; rw [ite_eq_left hr]; exact hh
             change u.eye.Flora u.torch.p e.cageX.visN i x (if title s=0 then _ else _); rw [ite_eq_right hr]
             have h2 : s.ray.outR=some (title s,pointE s.ray.outR):=by
                  cases hz:s.ray.outR
                  · exact (hr (by unfold title; rw [hz]; rfl)).elim
                  next a=> unfold title; rw [hz]; rfl
             rw [← h2]; exact hh,
            fun h b=>ht.beams e.base l.hot h b (Reed.sideq y b) (ho b)⟩

lemma dun (e:Moon u){x i:ℕ}(l:e.Lo)(hx:x∈u.D.P)(h:Lily.arms u.r u.x (e.a,i)=bald):
     Spend e x i Coinage.dies:=by
    let s:=e.stash bald x none fun _=>none
    have he0:s.ray.lampQ=false:=by
       change (decide (x<0) && _)=false
       simp
    have he:s.Good:= cam l bald x none _ ⟨heap l _ hx ..,
                fun h=>by change s.ray.lampQ=true at h; simp only [he0,reduceCtorEq] at h,fun _ _ h=>by change s.ray.lampQ=true at h; simp only [he0,reduceCtorEq] at h⟩
    have hp:s.ray.outR=none:= by unfold Crew.outR collect; rw [ite_eq_right (show ¬s.ray.lampQ=true by simp [he0])]
    have hu:title s=0:=by unfold title; rw [hp];rfl
    have hh:=cold e s l (y:=0) (b:=none) rfl he h (fun b=>by cases b <;> exact he.torn hu _) (fun _=>rfl)
                                                               (fun h=> (h hu).elim)
    rw [hp] at hh; exact hh
end Moon
end
end ExactDerandomization.Chron

end

section

namespace ExactDerandomization.Chron
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}

namespace Moon
variable (e:Moon u)
abbrev tideC(b:Bool)(q:Rill.History):Hull:=HullT.tides u.r u.x e.c b q
abbrev ny(b:Bool):ℕ:=if b then e.v.t.a else e.v.t.t
abbrev zone (b:Bool):Domain:= if b then e.v.S1 else e.v.S2
lemma formQ (e:Moon u)(b:Bool)(q:Rill.History):e.tideC b q=
   ((Aqua.tally u.r u.x e.v.t.i,e.v.t.u,e.ny b),q,Print.issued e.v.dye):=by
   unfold tideC HullT.tides ExactDerandomization.Chron.Moon.c owner; simp [kit,Age.env,ny,HullT.determine,greenY,stageQ,params,bitR,fence]
abbrev played (b:Bool)(x:ℕ)(p:Rill.History)(c:Bool):Bool:=
   Print.touched c u.n e.v.t.u (e.ny b) x p.1 p.2 (Print.issued e.v.dye)
lemma parked (b c:Bool)(x:ℕ): e.played b x (0,0) c=true := by
   unfold played
   unfold Print.touched
   rw [Print.flowed]; rfl
def walking (x y:ℕ)(b:Bool)(p:Rill.History):Bool:=
  Env.live e.v.t.u (e.ny b) (↑x) (↑y) (w:=0) (d:=0) le_rfl
                              (Print.queue p.1 p.2).1 (Print.queue p.1 p.2).2 e.v.dye
lemma sunny (b x y p):e.walking x y b p=true ↔ e.played b x p true=true ∧ e.played b y p false=true:=
    Print.exactHit ..

lemma zeda (b): e.zone b=retain (e.ny b) (u.plotM.stage e.v.t.i).S e.v.dye.2.1:=by cases b <;> rfl
lemma zedo (e:Moon u):e.v.S0=retain e.v.t.u (u.plotM.stage e.v.t.i).S e.v.dye.1:=rfl

namespace Lo
variable {e:Moon u}(h0:e.Lo)
include h0
lemma zenith : e.v.t.u ≤ u.plotM.roof ∧ ∀ b,e.ny b ≤ u.plotM.roof:=by
   have he:= h0.majors.good.2
   rw [Quest.ready] at he
   refine ⟨by omega, fun b=>?_⟩; cases b <;> unfold ny <;> simp <;> omega

lemma city {s:Surf}(b:Bool)(j:Rill.History) (he:s.1=e.tideC b j) (x:ℕ):
      s.frontC u.n x=true ↔ x∈e.v.S0 ∧ e.played b x j true=true:=by
    unfold Surf.frontC Surf.flareQ Surf.heatC Surf.green Surf.chartQ Surf.days Surf.dye Surf.mx
    rw [he,e.formQ]; dsimp only
    simp only [Bool.and_eq_true,decide_eq_true_eq,← mem_range,e.zedo,
                                      Aqua.room h0.majors.chart h0.majors.good.2.1]
    simp only [ite_true,Print.issued,Print.shoots]
    unfold retain; rw [mem_filter]; exact (and_assoc ..).symm
omit h0 in
lemma ending {s:Surf}(b:Bool)(j:Rill.History)(he:s.1=e.tideC b j) (x:ℕ)(hp:s.windC x∈ (u.plotM.stage e.v.t.i).S):
      s.finalC u.n x=true ↔ s.windC x∈e.zone b ∧ e.played b (s.windC x) j false=true:=by
    unfold Surf.finalC Surf.flareQ Surf.heatC Surf.green Surf.chartQ Surf.days Surf.dye
    rw [he,e.formQ]; dsimp only
    simp only [Bool.and_eq_true]
    simp only [Bool.false_eq_true,ite_false, Print.issued,Print.shoots]
    rw [e.zeda]; unfold retain; rw [mem_filter]; simp only [hp,true_and]; rfl

lemma equinox {s:Surf}(b:Bool)(j:Rill.History)(he:s.1=e.tideC b j)
   (h:s.sunset.2.1 ≤ u.n)(hp:s.sunset.2.2 ≤ u.n)
   (ht:j.1 ≤ u.w0.ell*u.limitM)(hv:j.2 ≤ 2^(planets u.r u.x*u.v.e)):
   Era.Spell s u:=by
    have hf:s.days=(e.v.t.u,e.ny b):=by unfold Surf.days; rw [he,e.formQ]
    have hg:s.chartQ=j:=by unfold Surf.chartQ; rw [he,e.formQ]
    have hz:s.dye=Print.issued e.v.dye:=by unfold Surf.dye; rw [he,e.formQ]
    refine ⟨?_,?_,?_,?_,?_,h,hp⟩
    · rw [hf]; exact h0.zenith.1
    · rw [hf]; exact h0.zenith.2 _
    · rw [hg]; exact ht
    · rw [hg]; exact hv
    rw [hz]; exact (Print.boxbound _).le

lemma terra {s:Surf}(h:s.1=e.tideC true (0,0))(hp:s.sunset=(Was.atom 0,1,0)):∀ b,u.wick0.Ok (Mica.cube b s):=by
    have he:1 ≤ u.n:=by have hk:= NeZero.pos u.n;omega
    intro b
    apply Era.overly _ b
    refine h0.equinox true (0,0) h ?_ ?_ (Nat.zero_le _) (Nat.zero_le _)
    · rw [hp]; exact he
    rw [hp]; exact Nat.zero_le _

lemma join {b:Bool} {x:ℕ}(he:x∈e.zone b): x∈e.v.S1:=by
   cases b
   · change x∈e.v.S2 at he
     obtain ⟨ht,hQ⟩:= mem_filter.1 he
     exact mem_filter.2 ⟨ht, contained _ _ h0.majors.good.2.2.2.1 hQ⟩
   exact he
end Lo
lemma armleg (e:ExactDerandomization.Chron.Moon u){q:Seed}(hp:ace u.w0 e.c q):
   Lily.arms u.r u.x (e.a,enc q)= Lily.recruit u.r u.x (e.c,q):=by
    have he :(dec e.a:Crt)=e.c:=therein ..
    unfold Lily.arms; have hh: clean u.w0 (e.a,enc q)=true:=by unfold clean; simp only [Wire.eq,he,decide_eq_true_eq]; exact ⟨trivial,hp⟩
    rw [ite_eq_left hh,he,Wire.eq]

end Moon
end
end ExactDerandomization.Chron

end

section

namespace ExactDerandomization.Chron.Moon
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}

structure Weather (e:Chron.Moon u)where
    b:Bool
    r:Census.Arc
namespace Weather
variable {e:Chron.Moon u}
variable (c:Weather e)
abbrev φ:= Census.drops e.sE c.b c.r
abbrev raysQ:= c.r.1
abbrev scroll : Rill.History:=(c.φ.tick u.w0,c.φ.event)
abbrev spark0 := c.φ.budget (m e.c)
abbrev job0 := ashes e.v c.b
abbrev d0 := gridR e.v c.b
abbrev hullC:= e.tideC c.b c.scroll
abbrev lane0 (i j:ℕ):=Seed.along c.φ i j
abbrev windP (x y:ℕ):= Census.wind e.sE c.job0 c.d0 e.v.dye x y c.r
abbrev α:= RowD.startF u.r u.x e.c c.φ
abbrev β:= RowD.scaleB u.r u.x e.c c.φ
def arcQ : Pool u.n:=
   Env.go c.d0.u c.d0.a (d:=0) (w:=0) le_rfl (Print.queue c.scroll.1 c.scroll.2).1
                                  (Print.queue c.scroll.1 c.scroll.2).2 e.v.dye
def forced:= e.Lo∧ c.r ∈ area e.v c.b e.i
abbrev vol:= Census.h e.sE c.r.2.1

lemma helm0: RowD.dock u.r u.x e.c c.φ=c.hullC:=rfl
lemma spokenE : RowD.skies u.r u.x e.c c.φ=Print.issued c.arcQ:=by
   let t:=Print.issued e.v.dye
   have h: (dec (Age.env e.c):Issue)=t:=dec_round ..
   unfold RowD.skies
   rw [h,Print.unpacked]
   cases hb:c.b
   · unfold arcQ;
     have hi : (params e.c).2.1=c.d0.u:=by unfold d0 gridR; rw [hb];rfl
     have hh : HullT.determine e.c c.φ.first0=c.d0.a:=by change (if c.b then e.v.t.a else e.v.t.t)=_;
                                                           unfold d0 gridR; rw [hb];rfl
     rw [hi,hh]
   unfold arcQ
   have hi : (params e.c).2.1=c.d0.u:=by unfold d0 gridR; rw [hb];rfl
   have hh : HullT.determine e.c c.φ.first0=c.d0.a:=by change (if c.b then e.v.t.a else e.v.t.t)=_;
                                                         unfold d0 gridR; rw [hb];rfl
   rw [hi,hh]

namespace forced
open Env
variable {c:Weather e}(h0:c.forced)
include h0
lemma house : c.φ.habitat u.w0 e.sE.key.a e.sE.M e.i c.job0.rays∧ c.φ.ray e.sE.key.a=c.raysQ∧
      c.φ.slackM e.sE.M=c.r.2.1:= Census.grange e.sE rfl _ h0.2
lemma step0 : c.raysQ∈ c.job0.rays∧ c.r.2.1∈ e.sE.layers c.raysQ.1 e.i∧
          c.φ.event< Print.rad^c.vol:=by exact (Census.pat ..).1 h0.2
lemma cost0 : e.d ≤ c.φ.sig∧ e.sE.cut c.raysQ.1 ≤ c.φ.sig∧ c.φ.sig < 2*e.d:=by
    have ht:=h0.step0.2.1
    exact ⟨(e.sE.full ht h0.1.s2).1,(e.sE.cheap (mem_Ico.1 ht).2).2.1,(e.sE.full ht h0.1.s2).2⟩
lemma cards : c.spark0+e.d ≤ e.v.m ∧ c.spark0 ≤ e.v.m-e.sE.cut c.raysQ.1:=by
    let y:= c.φ.sig
    have hz:e.d  ≤ y ∧ e.sE.cut c.raysQ.1 ≤ y:= ⟨h0.cost0.1,h0.cost0.2.1⟩
    let i:=c.r.2.1
    have hs:i+1<e.v.m:= (e.sE.cheap (mem_Ico.1 h0.step0.2.1).2).2.2
    have ht:y=e.v.m-(i+1):= rfl
    unfold spark0 Fog.budget
    rw [show c.φ.slackM (m e.c)=i from h0.house.2.2]
    split <;> omega
lemma early0 : c.spark0<e.v.m:=by have :=h0.cards.1; have ht:0< e.d:=Age.gap_pos ..; omega

lemma sigmas : c.φ.tick u.w0  ≤  u.w0.ell*u.limitM:=by
    let y:=c.r.2.1
    have hs : c.φ.sig=e.v.m-(y+1):= rfl
    have hp:=h0.1.majors.good.1
    unfold Fog.tick; rw [hs];gcongr;omega
lemma sphere {s:Surf} (he:s.1=c.hullC)
   (h:s.sunset.2.1 ≤ u.n)(hp:s.sunset.2.2 ≤ u.n): Era.Spell s u:=by
   apply h0.1.equinox _ _ he h hp h0.sigmas
   have ht:= h0.step0.2.2
   have hv : ↑(c.φ.event:ℕ) ≤  2^(planets u.r u.x *u.v.e):=by
      refine le_trans ht.le (le_trans (Nat.pow_le_pow_left (below Print.rad).le _) ?_)
      rw [← pow_mul]; apply Nat.pow_le_pow_right (by omega)
      let l:=lb Print.rad
      have hs : c.vol ≤ u.w0.ell*u.limitM := h0.sigmas
      have he1 : u.limitM ≤ planets u.r u.x:=by unfold planets; change Helix.Moon.M u.r u.x ≤ _; omega
      have hx:u.w0.ell*l  ≤  u.v.e:=by
         have hk:=h0.1.majors.book
         have h1:Pass.reserve u.w0+0 ≤ e.p.vol:=by have ht:(4+Pass.reserve u.w0) ≤ e.p.vol:=hk.saving.power; omega
         have h2:=hk.cost0; unfold Pass.reserve passport at h1; unfold Bank.hx at h2
         have he2 : u.w0.ell * lb Print.rad ≤ passport u.w0:=by unfold passport; nlinarith
         unfold l; unfold passport at he2; omega
      change l*c.vol ≤ _
      nlinarith [Nat.mul_le_mul_left l hs, Nat.mul_le_mul_right u.limitM hx,Nat.mul_le_mul_right u.v.e he1]
   exact hv

lemma stanza : c.α.v=(if c.r.2.2.1 then 1 else -1)* Env.weight^c.vol:=by
   have hv:=WindY.rains u.r u.x h0.sigmas
   unfold α RowD.startF
   change (if c.r.2.2.1 then WindY.shower u.r u.x (c.φ.tick u.w0) else _).v=_
   cases he:c.r.2.2.1
   · simp only [Bool.false_eq_true,ite_false,Coin.neg0,hv]
     rw [neg_one_mul]; rfl
   simp only [ite_true,hv];rw [one_mul];rfl
lemma humid (x y:ℕ) :
    c.windP x y = if e.walking x y c.b c.scroll then
        c.α.v * (c.job0.lines c.raysQ).seq c.spark0 c.arcQ x y else 0:=by
   have hr:c.scroll=(e.sE.lam*e.sE.slack c.r.2.1,c.r.2.2.2):=rfl
   unfold windP Census.wind; rw [h0.stanza]
   have hu: c.d0.u=e.v.t.u:=by cases h:c.b <;> simp [d0,gridR,h]; all_goals rfl
   have hv: c.d0.a=e.ny c.b:=by cases h:c.b <;> simp [d0,gridR,h,ny]; all_goals rfl
   have hh : c.spark0=(if c.r.2.2.1 then c.r.2.1+1 else c.r.2.1):=by
        unfold spark0 Fog.budget
        rw [show c.φ.slackM (m e.c)=c.r.2.1 from h0.house.2.2]; rfl
   dsimp only
   rw [hh]; unfold walking arcQ
   rw [hu,hv]; rfl

lemma braid (i j)(hi:i<e.v.Rslots)(hj:j<e.v.Rslots):
    atmos u.w0 e.c (c.lane0 i j):=
    Fen.sauna e.v (i:=e.i) (z:=(c.r,i,j)) (b:=c.b) (mem_product.2
                                   ⟨h0.2,mem_product.2 ⟨mem_range.2 hi,mem_range.2 hj⟩⟩)
lemma itemized (i j)(hi:i<e.v.Rslots)(hj:j<e.v.Rslots):
    Lily.arms u.r u.x (e.a,enc (c.lane0 i j))=RowD.pickA u.r u.x e.c (c.lane0 i j):=by
    rw [armleg e (Or.inl (h0.braid i j hi hj))]; rfl

lemma calm : |c.α.v| ≤ 1:=by
   rw [h0.stanza,abs_mul]
   simp only [abs_of_nonneg (WindY.careful c.vol).1]
   split <;> simpa only [abs_one,abs_neg,one_mul] using (WindY.careful c.vol).2
lemma shareq {k:ℕ} (hf:c.raysQ.1=k)(h:2^nar e.v.t.a k ≤ u.n):
     c.β.v=c.α.v*loaded u.n e.v.t.a k:=by
     unfold α β RowD.scaleB; rw [Coin.mul0]
     rw [show c.φ.ray (Garden.greenY e.c)=c.raysQ from h0.house.2.1,hf]; change _*(Aqua.quo u.n e.v.t.a k).v=_; rw [Aqua.pureG h]
lemma sharesC {k:ℕ}(he:c.raysQ.1=k)(h:2^nar e.v.t.a k ≤ u.n):
     |c.β.v|  ≤  massB 12 e.d:=by
   have hx:= h0.calm
   rw [h0.shareq he h,abs_mul,abs_of_pos (cost_pos ..)]
   apply le_trans (mul_le_mul_of_nonneg_right hx (cost_pos ..).le)
   rw [one_mul]; apply le_trans (burden h)
   have hm:=h0.cost0
   have hz:4*distn e.v.t.a k  ≤  8*e.d:=by
          subst k
          have hv:distn e.v.t.a c.raysQ.1+1 ≤  c.φ.sig:=hm.2.1;omega
   have hl : 4+4*distn e.v.t.a k ≤ 12*e.d:=by have hs:1≤e.d:=gap_pos ..; omega
   rw [show (16:ℝ)=Est.box 4 by norm_num [Est.box],← boxP]; exact box_mono hl
end forced

end Weather

namespace FogX
lemma plain {f g:ℝ}(h:0≤g)(_:f ≤ g) : |g|=g:=abs_of_nonneg h
lemma alleG(M:MintV){u v w z:ℝ}{d:ℕ}(he:1 ≤ d)(hu:|u| ≤ massB 12 d)(hv:|v| ≤ range0 M)
   (hw:|w| ≤ range0 M)(hz:|z| ≤ 1): |u*v*w*z| ≤ massB M.prism d:=by
    have hl:range0 M≤ massB M.coin d:=by unfold range0 massB; apply pow_le_pow_right₀ (by norm_num); nlinarith
    simp only [abs_mul]
    apply le_trans (mul_le_mul (mul_le_mul (mul_le_mul hu (hv.trans hl) (abs_nonneg _) (mass0 ..).le)
                     (hw.trans hl) (abs_nonneg _) (mul_pos (mass0 ..) (mass0 ..)).le) hz (abs_nonneg _) (by positivity))
    rw [mul_one,← mass_mul,← mass_mul]
    exact mass_mono (by unfold MintV.prism; omega) _
end FogX
end
end ExactDerandomization.Chron.Moon

end

section

namespace ExactDerandomization.Chron.Moon.Weather
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Chron.Moon u}

structure Ship(e:Chron.Moon u)where
    s:Fabric u
    f:Producer
namespace Ship
variable (p:Ship e)
abbrev cage:=p.s.leaveE
abbrev src:=p.cage.dataN
abbrev aimP:=p.s.finalE
abbrev scholar(x j:ℕ):ℝ:= p.f.scoreF p.aimP x j
structure Armed (p:Ship e) :Prop where
    good:p.s.Good
    sturdy:p.s.Efine e.p p.f
    dawn : p.s.m+e.d ≤ e.v.m
namespace Armed
variable {p:Ship e}(hT:p.Armed)
include hT
lemma mom (j:ℕ):u.D.W (p.s.c j 0)+u.D.D e.a ≤ u.D.W e.a:=by
    rw [show e.a=e.v.c 1 _ from rfl,Stone.W,Stone.W,Stone.D]
    exact Age.renewal hT.dawn
lemma here1 :u.D.W p.cage.visN+u.D.D e.a ≤ u.D.W e.a:= hT.mom _
lemma here0 :u.D.W p.src+u.D.D e.a ≤ u.D.W e.a:=hT.mom _
lemma pricey {j:ℕ}(hj:j<p.s.Rslots):u.smallQ p.src j:=by
    have hi:=hT.sturdy.sector.suit.coil; exact hi.awake (hi.size0 _ hj)
lemma tempo {x j:ℕ}(hx:x∈u.D.P)(hj:j<p.s.Rslots):
     u.D.Voice p.src x (hole 1 j) (u.D.high p.src) e.p.coin (p.scholar x j):=by
    have hh:=(hT.sturdy.sector.suit.voices x hx).ready j (hT.pricey hj)
    rw [show u.D.D p.cage.dataN=1 from p.s.ageEnd _ (by decide),mul_one] at hh
    exact hh
lemma stop {x j:ℕ}(hx:x∈u.D.P)(hj:j<p.s.Rslots): |p.scholar x j|≤ Wear.range0 e.p:=by
    obtain ⟨v,hp,hT⟩:=hT.tempo hx hj
    have h:=hp.1; rw [abs_div,abs_of_pos (show 0 < (2:ℝ)^e.p.coin by positivity),div_le_one (show 0 < (2:ℝ)^e.p.coin by positivity)] at h;exact h
end Armed
end Ship

/-- One fixed incoming port/s station op, varying endpoint ray index j of second. First score
and MAX-prefix values supplied whenever first starts. Not depending on j. -/
structure Pale (e:Chron.Moon u)where
   k:Weather e
   x:ℕ
   p:ℕ
   A:Rill.History
   b: Stars
   F:Ship e
   o :ℕ× Arch
   α:Coin
   U:ℕ
   V:ℕ
   alphaQ:Vec
   betaQ:ℕ → Vec
namespace Pale
variable (v:Pale e)

def surf (j:ℕ):Surf:=(v.k.hullC,v.A,(v.F.cage.visN,j),v.o)
abbrev warm:ℝ:= v.α.v
abbrev astro (x:ℕ): ℝ:= boost (Nest.Good.maxs (fun i=> v.betaQ i x) u.w0.p.T)
def prodQ (j x:ℕ):ℝ:=v.warm * v.alphaQ x * v.F.scholar x j * v.astro x
abbrev crop(x:ℕ):=v.o.2.1*x+v.o.2.2
abbrev front := (v.surf 0).frontC u.n v.x
abbrev ash(j:ℕ):Embellish:=
    (v.surf j,(2,v.k.b),v.α,v.U,(v.F.src,j),v.V)
def rest(j:ℕ): Nest u:=e.stash (v.ash j) v.x v.b (fun m=> v.F.f.coversF m j)
abbrev medal(j:ℕ):ℕ:=title (v.rest j)
abbrev harvest0(j:ℕ):Pt:=spread (v.k.b) (prodQ v j (pointE v.b))
where spread(b:Bool)(i:ℝ):Pt:=if b then (i,0) else (0,i)
def grade0(j:ℕ):Coinage:=
     ⟨(v.rest j).ray.outR,if v.medal j=0 then 0 else v.harvest0 j⟩

structure Span (v:Pale e):Prop where
     helm:v.k.forced
     source :v.x∈u.D.P
     pre : v.p < u.w0.p.K
     fin : v.F.Armed
     lex :∀ j,Rain.Seed.y (v.k.lane0 v.p j)=j
     step :∀ j < e.v.Rslots,Lily.arms u.r u.x (e.a,enc (v.k.lane0 v.p j))=v.ash j
     dims: v.o.2.1 ≤ u.n∧v.o.2.2 ≤ u.n
     win : v.o.2.2 < v.o.2.1
     esc :∀ a j,v.F.f.awake a j→LiftQ u (v.surf j) e.a (v.F.f.locate a j)∧
                                                    v.crop (v.F.f.locate a j)∈ (u.plotM.stage e.v.t.i).S
structure Kin (v:Pale e) :Prop where
     geography : Span v
     flew :∀ j<e.v.Rslots,(v.rest j).Good
     paid : |v.warm| ≤ massB 12 e.d
     fees:∀ k m,v.front=true→v.b=some (k,m)→
         |v.alphaQ m| ≤ Wear.range0 e.p ∧
         ∀ j<e.v.Rslots,let s:=v.rest j;
                         (v.U≠0→s.VoiceS v.x v.U e.p.coin (v.alphaQ m))∧
                         (v.U=0 → v.alphaQ m=1)∧
                         (∀ i<u.w0.p.T,v.V≠0→s.VoiceS m (s.catshot i) 0 (v.betaQ i m))∧
                         (v.V=0→∀ i<u.w0.p.T,v.betaQ i m=1)

namespace Span
variable {v:Pale e}(h0:v.Span)
include h0
lemma forming {j:ℕ}(hj:j<e.v.Rslots){x:ℕ}(hx:x∈u.D.P):Partner u (v.surf j) e.a x (v.F.f.coversF x j):=by
    let s:=v.surf j
    have ht:= h0.helm.1
    have he:=h0.fin
    have hp:= he.sturdy.sector.suit
    apply Partner.leaf
    · exact Age.cpos _
    · exact ht.pays _ hp.coil.path he.here1
    · exact fun b=> Era.overly (h0.helm.sphere (s:=s) rfl h0.dims.1 h0.dims.2) b
    · exact he.here1
    · have hz:u.D.D s.U.1=1:=v.F.s.ageEnd _ (by decide); rw [show u.D.D (v.surf j).U.1=1 from hz]
      have hX:=ht.wpaid.well.1; omega
    · exact hp.orbit hj hx
    intro i y h; unfold Producer.coversF at h
    split at h
    · next hi=> simp only [Option.some.injEq,Prod.mk.injEq] at h
                rw [←h.2]; exact (h0.esc x j hi).1
    contradiction

/-- Successful captures and their time-independent guard conditions. -/
lemma launch  :
    v.front=true ↔ v.x ∈ e.v.S0∧e.played v.k.b v.x v.k.scroll true=true:=h0.helm.1.city _ _ rfl _
lemma leading {j i:ℕ}(h:v.F.f.awake i j):
    let g:=v.F.f.locate i j
    (v.surf j).finalC u.n g=true ↔ v.crop g∈e.zone v.k.b ∧ e.played v.k.b (v.crop g) v.k.scroll false=true:=
    (Lo.ending (e := e) (s := v.surf j)) _ _ rfl _ (h0.esc i j h).2
omit h0 in
lemma harvest {j k y:ℕ}:
    (v.rest j).ray.outR=some (k,y)↔ v.front=true ∧ ∃ a m, v.b=some (a,m) ∧
      v.F.f.awake m j ∧ k=a+1∧v.crop (v.F.f.locate m j)=y∧ (v.surf j).finalC u.n (v.F.f.locate m j)=true:=by
    let s:=v.surf j
    constructor
    · intro h
      obtain ⟨ht,a,i,b,z,h0,h1,h2,h3,h4⟩:= spark h
      change v.F.f.coversF _ _=_ at h1
      unfold Producer.coversF at h1
      split at h1
      · next hh=>
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        refine ⟨ht,a,i,h0,hh,h2,?_,?_⟩
        · rw [show v.F.f.locate i j=z from h1.2]; exact h3.symm
        rw [show v.F.f.locate i j=z from h1.2]; exact h4
      contradiction
    rintro ⟨hf,a,m,hw,hp,hs,hr,hq⟩
    change collect s u.n v.x v.b _=_
    unfold collect; rw [ite_eq_left (show s.frontC u.n v.x=true from hf),hw]
    dsimp only
    rw [show (v.rest j).ray.exit0 m= v.F.f.coversF m j from rfl]; unfold Producer.coversF
    simp only [ite_eq_left hp]
    rw [ite_eq_left (show s.finalC _ _=true from hq),hs,← hr]; rfl
omit h0 in
lemma mayor {j:ℕ}(h:v.medal j≠0) :
    v.front=true∧∃ a m, v.b=some (a,m) ∧
      v.F.f.awake m j ∧ v.medal j=a+1∧pointE (v.rest j).ray.outR=v.crop (v.F.f.locate m j)∧
                                       (v.surf j).finalC u.n (v.F.f.locate m j)=true:=by
    cases he:(v.rest j).ray.outR
    · exact False.elim (h (by unfold medal title;rw [he];rfl))
    next t=>
      obtain ⟨k,y⟩:=t
      obtain ⟨hp,a,m,hh,hf,hg,hT,hL⟩:= (Pale.Span.harvest (v := v)).1 he
      exact ⟨hp,a,m,hh,hf,by unfold medal title; rw [he]; exact hg, hT.symm,hL⟩
end Span
end Pale
end
end ExactDerandomization.Chron.Moon.Weather

end

section

namespace ExactDerandomization.Chron.Moon.Weather.Pale
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Chron.Moon u}
abbrev boltQ (i:Bool)(x:ℝ):Pt:=harvest0.spread i x
lemma meterB(i x) : ht (boltQ i x)=|x|:=by
    unfold Buf.ht boltQ harvest0.spread; cases i <;> simp
variable (v:Pale e)
abbrev screenP (y:ℕ): Prop:=v.x∈ e.v.S0 ∧ y∈ e.zone v.k.b ∧ e.walking v.x y v.k.b v.k.scroll=true
abbrev peel (y:ℕ):ℕ:= y/v.o.2.1
abbrev goodY (y:ℕ):=y%v.o.2.1=v.o.2.2

def till(x y:ℕ):ℝ:= v.warm*v.alphaQ x*v.F.aimP x (v.peel y)*v.astro x
def seekR(y:ℕ): Pt:=if v.screenP y ∧ v.goodY y then
                    (match v.b with | none=>0 | some (_,x)=> boltQ v.k.b (v.till x y)) else 0

namespace Span
variable {v:Pale e}(h0:v.Span)
include h0
lemma fee {j w k}(he:(v.rest j).ray.outR=some (k,w)):
   k≠0 ∧ v.screenP w:=by
    obtain ⟨h,a,m,hb,hc,rfl,ht,hj⟩:=(Pale.Span.harvest (v := v)).mp he
    obtain ⟨hs,hL⟩:=h0.launch.mp h
    obtain ⟨he0,hH⟩:=h0.leading hc|>.mp hj
    subst w
    exact ⟨by omega,hs,he0,(e.sunny ..).2 ⟨hL,hH⟩⟩

lemma upG(y:ℕ):v.goodY (v.crop y) ∧ v.peel (v.crop y)=y:=by
   have hh:=fromrad v.o.2.1 y v.o.2.2 h0.win
   rw [show radix _ _ _ = v.crop y by unfold crop radix;omega] at hh; exact ⟨hh.2,hh.1⟩
omit h0 in
lemma downG(y:ℕ)(h:v.goodY y): v.crop (v.peel y)=y:=by
    unfold crop peel; rw [Nat.add_comm,← show y % v.o.2.1=v.o.2.2 from h]; exact Nat.mod_add_div ..

lemma fizzle {y:ℕ}(h:¬(v.screenP y ∧ v.goodY y)):
    ∀ j,(v.grade0 j).pigment y=0:=by
    intro j; unfold Coinage.pigment; split
    · next hc=>
      change v.medal j≠0∧ pointE (v.rest j).ray.outR=y at hc
      obtain ⟨ht,a,m,hh,hm,hz,hp,hc'⟩:=(Pale.Span.mayor (v := v)) hc.1
      have hv:v.crop (v.F.f.locate m j)=y:=hp.symm.trans hc.2
      have he : (v.rest j).ray.outR=some (a+1,y):=
                        (Pale.Span.harvest (v := v)).mpr ⟨ht,a,m,hh,hm,rfl,hv,hc'⟩
      exact (h ⟨(h0.fee he).2,hv ▸ (h0.upG _).1⟩).elim
    rfl
omit h0 in
lemma haze (h:v.b=none):∀ j, v.medal j=0:=by
    intro j; by_contra hc; obtain ⟨-,a,m,h1,-,-,-,-⟩:=(Pale.Span.mayor (v := v)) hc; rw [h] at h1; contradiction
lemma dueP {y:ℕ} (h:v.screenP y ∧ v.goodY y){k m:ℕ}(hp:v.b=some (k,m))(j:ℕ):
    (v.grade0 j).pigment y=
       if v.F.f.locate m j=v.peel y then boltQ v.k.b (v.prodQ j m) else 0 :=by
   unfold Coinage.pigment
   have hf:v.front=true:= (h0.launch).mpr
                           ⟨h.1.1,((e.sunny ..).1 h.1.2.2).1⟩
   have hg : (v.grade0 j).fired∧ (v.grade0 j).p=y ↔ v.F.f.locate m j=v.peel y∧ v.F.f.awake m j:=by
        constructor
        · intro he; change v.medal j≠0∧ pointE (v.rest j).ray.outR=y at he
          obtain ⟨_,a,l,h1,h2,h3,h4,h5⟩:=(Pale.Span.mayor (v := v)) he.1
          have hh:m=l:=congrArg Prod.snd (Option.some.inj (hp.symm.trans h1))
          subst m
          exact ⟨(h0.upG _).2.symm.trans (congrArg _ (h4.symm.trans he.2)),h2⟩
        rintro ⟨hC,hE⟩
        have hb :v.crop (v.F.f.locate m j)=y:=by rw [hC,(Pale.Span.downG (v := v)) _ h.2]
        have hT:(v.surf j).finalC u.n (v.F.f.locate m j)=true:=by
             apply (h0.leading hE).mpr; rw [hb]; exact ⟨h.1.2.1,((e.sunny ..).1 h.1.2.2).2⟩
        have hv: (v.rest j).ray.outR=some (k+1,y):=(Pale.Span.harvest (v := v)).mpr ⟨hf,k,m,hp,hE,rfl,hb,hT⟩
        change (iris (v.rest j).ray.outR≠0 ∧ pointE (v.rest j).ray.outR=y); rw [hv]; exact ⟨Nat.succ_ne_zero _,rfl⟩
   by_cases hc:v.F.f.locate m j=v.peel y
   · rw [ite_eq_left hc]
     split
     · next hh=>
       have he:= hh.1
       change v.medal j ≠ 0 at he
       change (if v.medal j=0 then _ else _)=_
       rw [ite_eq_right he]; unfold harvest0; rw [hp]; rfl
     next hh=>
       have hp:¬v.F.f.awake m j:= fun k=>hh (hg.mpr ⟨hc,k⟩)
       have hu:v.F.scholar m j=0:=ite_eq_right hp
       unfold prodQ; rw [hu,mul_zero,zero_mul]
       cases v.k.b <;> rfl
   rw [ite_eq_right hc,ite_eq_right (fun h=>hc (hg.mp h).1)]

lemma architect {y}: ∑ j∈range e.v.Rslots,(v.grade0 j).pigment y=v.seekR y:=by
   unfold seekR
   split
   · next h=>
     cases hs:v.b with
     | none=>
       apply sum_eq_zero; intro j hj; apply ite_eq_right; intro hc
       exact hc.1 ((Pale.Span.haze (v := v)) hs j)
     | some r=>
       obtain ⟨k,m⟩:=r
       simp_rw [h0.dueP h hs]
       by_cases he:m∈u.D.P
       · have hf:= h0.fin.sturdy.sector.supply m (v.peel y) he
         unfold till
         rw [← show ∑ j∈range e.v.Rslots,(if v.F.f.locate m j=v.peel y then v.F.scholar m j else 0)=v.F.aimP m (v.peel y) from hf]
         unfold prodQ; simp only [mul_sum,sum_mul]
         have hh(j):v.warm*v.alphaQ m * (if v.F.f.locate m j=v.peel y then v.F.scholar m j else 0)*v.astro m=
                      if v.F.f.locate m j=v.peel y then v.warm*v.alphaQ m*v.F.scholar m j *v.astro m else 0:= by split<;> simp
         simp_rw [hh]
         apply boltLemma _ _ _ (fun x=> v.F.f.locate m x=v.peel y)
       have hf:∀ j,¬v.F.f.awake m j:=by
             intro j hp; exact he ((Fabric.Good.n0 h0.helm.1.majors.chart h0.fin.good)
                                                         (h0.fin.sturdy.sector.light.insured m j hp).1)
       have hu:v.F.aimP m (v.peel y)=0:=by
             by_contra hn
             obtain ⟨i,hi,_⟩:= h0.fin.sturdy.sector.light.defend _ _ hn; exact hf i hi
       unfold till; rw [hu,mul_zero,zero_mul, boltzero _]
       apply sum_eq_zero; intro j hj; split
       · unfold prodQ; rw [show v.F.scholar m j=0 from ite_eq_right (hf j),mul_zero,zero_mul]; exact boltzero _
       rfl
   next hm=> exact sum_eq_zero fun j _=> h0.fizzle hm j
 where
    boltzero (b:Bool): boltQ b 0=0:=by cases b<;> rfl
    boltLemma (M:ℕ)(b:Bool)(A:ℕ → ℝ)(p:ℕ → Prop)[DecidablePred p]:
         ∑ j∈range M,(if p j then boltQ b (A j) else 0)=boltQ b (∑ j∈range M,(if p j then A j else 0)):=by
          classical
          induction M with
          | zero=> simp [boltzero]
          | succ i ih=> rw [sum_range_succ,sum_range_succ,ih]
                        cases b <;> split <;> simp [boltQ,harvest0.spread]
end Span

namespace Kin
variable {v:Pale e}(h0:v.Kin)
include h0
lemma worn {j:ℕ}(hj:j<e.v.Rslots): ht (v.grade0 j).dye  ≤ massB e.p.prism e.d:=by
   have hp:= h0.geography
   have he:= h0.flew j hj; let s:= v.rest j
   change ht (if v.medal j=0 then _ else _ ) ≤ _
   split
   · rw [show ht (0:Pt)=0 by simp [Buf.ht]]; exact (mass0 ..).le
   next h=>
   obtain ⟨hf,a,m,hA,hg,hj0,hL,h2⟩:=(Pale.Span.mayor (v := v)) h
   unfold harvest0; rw [hA]
   change ht (boltQ _ (v.prodQ j m)) ≤_
   rw [meterB]
   obtain ⟨hPa,hC,H⟩:= he.grip.tours a m hf hA
   have hh:= (hPa.ready.swaps _ hPa.holds _ hPa.xem _ _ hC).1
   have hv : |v.astro m| ≤ 1:= by
        have ht:in01 (v.astro m):=rising_mem ..
        rw [abs_of_nonneg ht.1];exact ht.2
   exact FogX.alleG _ (gap_pos ..) h0.paid (h0.fees a m hf hA).1 (hp.fin.stop hh hj) hv

lemma draft {j:ℕ}(hj:j<e.v.Rslots):
     Spend e v.x (enc (v.k.lane0 v.p j)) (v.grade0 j):=by
   have hp:= h0.geography
   have he:= h0.flew j hj; let s:= v.rest j
   have hs:= hp.helm.1
   let t:=(v.grade0 j).dye
   have hz:title s=0→ t=0:=fun h=> ite_eq_left h
   have hT:= h0.worn hj
   refine e.cold s hs (y:=t) (b:=v.b) rfl he (hp.step _ hj) ?_ hz ?_
   · intro b
     by_cases hh:title s=0
     · rw [hz hh]; cases b <;> exact he.torn hh _
     obtain ⟨hf,a,m,hA,hg,hj0,hL,h2⟩:=(Pale.Span.mayor (v := v)) hh
     have hh0: t=boltQ v.k.b (v.prodQ j m):=by
         unfold t grade0; dsimp only; rw [ite_eq_right hh]
         unfold harvest0; rw [hA]; rfl
     rw [hh0]
     have hu :s.optic=(2,v.k.b):=rfl
     by_cases hX : b=v.k.b
     · subst b
       have ht:Reed.sideq (boltQ v.k.b (v.prodQ j m)) v.k.b=v.prodQ j m:=by cases v.k.b <;> rfl
       rw [ht]
       have hR:s.optic.1=2:=congrArg Prod.fst hu
       refine he.youngYes hh (by rw [hR];omega) (congrArg Prod.snd hu)
                    (fun e=>by rw [hR] at e; contradiction) (fun _=>?_) ?_
       · obtain ⟨ha,hb,hh2⟩:=he.grip.tours a m hf hA
         have hA1 :s.Etude a m:= ⟨ha,hb⟩
         have hPA:= h0.fees a m hf hA
         obtain ⟨hU,hV,hQ,hg1⟩:=hPA.2 j hj
         have hz :m∈u.D.P:= (ha.ready.swaps a ha.holds _ ha.xem _ _ hb).1
         rw [show title s=a+1 from hj0]
         apply he.salutation hA1 (fun i=> v.betaQ i m) (v.alphaQ m) _ ?_ hU hV ?_ hQ hg1
         · have h : 12  ≤  s.t.prism:=by unfold MintV.prism;omega
           exact le_trans (e.baseD.symm ▸ h0.paid) (mass_mono h _)
         exact ⟨v.F.src,hole 1 j, rfl,hp.fin.here0,hp.fin.tempo hz hj⟩
       apply Cambria.Rime.Nest.Good.shekel hs.majors.book.saving rfl; rw [show u.D.D s.a=e.d from e.baseD]
       change Buf.ht t ≤ _ at hT
       rw [hh0,meterB] at hT; exact hT
     have ht:Reed.sideq (boltQ v.k.b (v.prodQ j m)) b=0:=by
                            cases hm:v.k.b <;> cases b <;> first|rfl| (exact (hX hm.symm).elim)
     rw [ht]; exact he.youngNo hh (by rw [hu];change 2≠(0:ℕ);decide) (by rw [hu]; exact Ne.symm hX)
   intro h
   obtain ⟨hf,a,m,hA,hg,hj0,hL,h2⟩:=(Pale.Span.mayor (v := v)) h
   refine ⟨(hp.launch.mp hf).1,?_⟩
   change pointE (v.rest j).ray.outR∈_
   rw [hL]; exact hs.join (hp.leading hg|>.mp h2).1
end Kin
end
end ExactDerandomization.Chron.Moon.Weather.Pale

end

section

namespace ExactDerandomization.Chron.Moon.Weather
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Pale
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable (e:Chron.Moon u)
/-- recursive premises needed for one order data/pulses. -/
structure Crude : Prop where
     lane:e.Lo
     milk : ∀ a:Fabric u,a.Good→a.m+e.d ≤ e.v.m→∃ f:Producer,a.Efine e.p f
     span :∀ t:Peek,∀ m w,m ≤ u.limitM→ t.ready u.plotM m→m+e.d ≤ e.v.m→
         let q:=u.vecL t m 17 0 w
         ∀ x∈u.D.P,u.D.Voice q x (hole 1 0) (u.D.high q) 0 ((forecast u.plotM m).outV t w x)

namespace Crude
variable {e:Chron.Moon u}(hc:Crude e){b:Weather e}
include hc
lemma taken (hp:b.forced)(q:Quest)(s:Pool u.n)(he:q.ready u.plotM b.spark0):
   ∃ p:Producer, let v:Fabric u:=⟨q,b.spark0,s⟩
                 Ship.Armed (⟨v,p⟩:Ship e):=by
    let f:Fabric u:=⟨q,b.spark0,s⟩
    have hw:f.Good:=⟨le_trans hp.early0.le hc.lane.majors.good.1,he⟩
    obtain ⟨p,h⟩:=hc.milk f hw hp.cards.1
    exact ⟨p,hw,h,hp.cards.1⟩
lemma caul {x i wM t}(hp:b.forced)(h:i=b.spark0)(he:t.ready u.plotM i)(hz:x∈u.D.P):
     let q:=u.vecL t i 17 0 wM
     u.D.W q+u.D.D e.a ≤ u.D.W e.a ∧
       u.D.Voice q x (hole 1 0) (u.D.high q) 0 (e.v.roll i |>.outV t wM x):=by
     subst i
     dsimp only
     have ht : e.v.roll b.spark0 = forecast u.plotM b.spark0:= vault _ _ hp.early0
     rw [ht]
     refine ⟨?_,hc.span t b.spark0 wM (le_trans hp.early0.le hc.lane.majors.good.1) he hp.cards.1 x hz⟩
     rw [show e.a=e.v.c 1 _ from rfl,Stone.W,Stone.D]
     change Age.W _+_  ≤ _
     rw [vecL,u.rolfe]
     exact Age.renewal hp.cards.1
end Crude

variable {e:Chron.Moon u}
namespace Pale

namespace Span
variable {v:Pale e}(h0:v.Span)
include h0
lemma regionQ {j:ℕ}(_:j<e.v.Rslots):
   (v.rest j).ray.Good:= heap h0.helm.1 _ h0.source ..
lemma simple {i}(hp:v.A=(Was.atom i,0))
    (he:i ≤ u.v.bonus)(hs:∀ a x,v.front=true→(v.b=some (a,x) ↔ a<Era.budget u.r∧ Was.Flight u.r u.x i a v.x x)):
    ∀ j<e.v.Rslots,(v.rest j).Good:=by
   intro j hj
   let s:=v.rest j
   have hw:=h0.helm.1
   apply cam hw
   apply Era.basePort (h0.regionQ hj) hp (Stone.zeroR ..) he
                         (Nat.add_le_add_right hw.majors.book.coinbook 1) hs
   intro b i hs0 ht
   have hf:= (hs b _ hs0).mp ht
   exact h0.forming hj (mem_range.2 (Nat.lt_succ_of_le hf.2.2.1))
lemma listP (hp:v.A=(Was.atom 0,0))(he:v.b=some (0,v.x)):
   ∀ j<e.v.Rslots,(v.rest j).Good:=by
    have hx:v.x ≤ u.n:= Nat.le_of_lt_succ (mem_range.1 h0.source)
    apply h0.simple hp (Nat.zero_le _)
    intro a b _
    unfold Was.Flight
    have ht:0<Era.budget u.r:=Nat.zero_lt_succ _
    rw [he]; simp only [Option.some.injEq,Prod.mk.injEq, ite_true]; change (0=a ∧ v.x=b) ↔ _∧v.x≤u.n∧b≤u.n∧_; grind
end Span
lemma boostOne (p:Pale e) (i:ℕ) (h:∀ j< u.w0.p.T,p.betaQ j i=1):
   p.astro i=1:=by
    have he : ∀ j≤u.w0.p.T,Nest.Good.maxs (fun j=>p.betaQ j i) j=(if j=0 then 0 else 1):=by
       intro j; induction j with
       | zero=>simp [Nest.Good.maxs]
       | succ j ih=>
         intro hk; rw [Nest.Good.maxs,ih (by omega),h j (by omega),ite_eq_right (show j+1 ≠ 0 by omega)]
         split <;> norm_num
    unfold astro; rw [he _ le_rfl,ite_eq_right (Nat.ne_of_gt u.w0.p.tOK.1)]
    apply rising_top <;>norm_num
lemma windId {p:Pale e}(h:p.o=Crest.postN) (y:ℕ) :p.goodY y ∧ p.peel y=y:=by
    unfold goodY peel; rw [h]; simp []; omega
end Pale

/- Bucket equations sum over endpoint for each first port, then firsts. -/
def prize(v:Weather e)(x y:ℕ):Pt:=
   if x∈e.v.S0∧y∈ e.zone v.b then boltQ v.b (v.windP x y) else 0
lemma worth {v:Weather e}(hp:v.forced)(x y:ℕ):
    prize v x y=(if x∈e.v.S0 ∧ y∈e.zone v.b ∧ e.walking x y v.b v.scroll=true then
      boltQ v.b (v.α.v*(v.job0.lines v.raysQ).seq v.spark0 v.arcQ x y) else 0):=by
    have hz:boltQ v.b 0=0:=by cases v.b <;> rfl
    unfold prize; rw [hp.humid]
    split <;> grind
structure Carnival (v:Weather e) (x:ℕ) (f:ℕ → ℕ → Coinage):Prop where
    earns:∀ i < e.v.Rslots,∀ j< e.v.Rslots,e.Spend x (enc (v.lane0 i j)) (f i j)
    stamp:∀ i < e.v.Rslots,∀ j<e.v.Rslots, ht (f i j).dye ≤ massB e.p.prism e.d
    fund:∀ y, ∑ i∈range e.v.Rslots,∑ j∈range e.v.Rslots,(f i j).pigment y=prize v x y

abbrev creditD(v:Pale e):ℕ → ℕ → Coinage := fun i j=> if i=0 then v.grade0 j else Coinage.dies

lemma only0(x): Coinage.dies.pigment x=0:=ite_eq_right (fun h=>h.1 rfl)
lemma solace {v:Pale e}(he:v.p=0)(h:v.Kin)
    (hp:∀ i < u.w0.p.K,i≠0→∀ j < u.w0.p.K,Lily.arms u.r u.x (e.a,enc (v.k.lane0 i j))=bald)
    (hq:∀ y,v.seekR y=prize v.k v.x y):
   Carnival v.k v.x (creditD v):=by
    have hE:=h.geography
    constructor
    · intro i hi hz hs
      unfold creditD; split
      · next hh=> rw [hh,←he];exact h.draft hs
      next hh=>exact dun e hE.helm.1 hE.source (hp _ hi hh _ hs)
    · intro i hi j hj
      unfold creditD; split
      · exact h.worn hj
      rw [Coinage.dies]; simp only; rw [show ht (0:Pt)=0 from by simp [Buf.ht]]; positivity
    intro y
    rw [sum_eq_single 0]
    · unfold creditD; simp only [ite_true,h.geography.architect,hq]
    · intro i _ h; unfold creditD; simp only [ite_eq_right h,only0,sum_const_zero]
    intro hv; have hc:=mem_range.2 (he ▸ hE.pre); exact False.elim (hv hc)

lemma festival {k:Weather e}{p:ℕ → Pale e}{x:ℕ}
     (hs:∀ i, (p i).k=k)(he:∀ i,(p i).x=x)
     (hM:∀ i<u.w0.p.K,(p i).p=i∧ (p i).Kin)
     (hq:∀ y,∑ i∈range u.w0.p.K,(p i).seekR y=prize k x y):
   Carnival k x (fun i j=> (p i).grade0 j):=by
    constructor
    · intro i hi j hj
      rw [← he i,←hs i]
      have hx:=(hM i hi).2.draft hj; rwa [(hM i hi).1] at hx
    · exact fun i hi j hj=> (hM i hi).2.worn hj
    intro y; rw [←hq]; apply sum_congr rfl
    intro i hi; exact (hM i (mem_range.1 hi)).2.geography.architect

end
end ExactDerandomization.Chron.Moon.Weather

end

section

namespace ExactDerandomization.Chron.Moon.Weather
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Pale
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Chron.Moon u}
namespace Single

structure Aim (c:Weather e) (f:Ship e) (a:Coin):Prop where
    chart:c.forced
    been : f.Armed
    season : f.s.m=c.spark0
    per : (u.plotM.stage f.s.t.i).S=(u.plotM.stage e.v.t.i).S
    fare : |a.v| ≤ massB 12 e.d
    via : ∀ i<e.v.Rslots,∀ j<e.v.Rslots,Lily.arms u.r u.x (e.a,enc (c.lane0 i j))=
                       if i=0 then Crest.ordinary c.hullC c.b c.spark0 j (bitR f.s.t) (Print.issued f.s.dye) a else bald
    ship :∀ x y,c.α.v*(c.job0.lines c.raysQ).seq c.spark0 c.arcQ x y=a.v*f.aimP x y

def nave (c:Weather e)(f:Ship e)(a:Coin)(x:ℕ):Pale e:=
    ⟨c,x,0,(Was.atom 0,0),some (0,x),f,Crest.postN,a,0,0,fun _=>1,fun _ _=>1⟩
variable {c:Weather e}{f:Ship e}{a:Coin}

namespace Aim
variable (hS:Aim c f a)
include hS
lemma bears {x:ℕ}(hx:x∈u.D.P): (nave c f a x).Kin:=by
   let v:=nave c f a x; let s:=hS.chart.1
   have hb:v.Span:=by
      have hp:u.D.W 0+u.D.D e.a ≤ u.D.W e.a:= Stone.zeroR ..
      refine ⟨hS.chart,hx,Kpos _,hS.been,fun _=>rfl,?_,?_,(show 0<(1:ℕ) by omega),?_⟩
      · intro j hj; change Lily.arms u.r u.x (e.a,enc (c.lane0 0 j))=v.ash j; rw [hS.via _ (Kpos _) _ hj,ite_eq_left rfl,← hS.season]
        rfl
      · exact ⟨(NeZero.pos u.n),Nat.zero_le _⟩
      intro b j hl
      have hm := (hS.been.sturdy.sector.light.insured _ _ hl).2
      have hi:=Fabric.Good.n1 s.majors.chart hS.been.good hm
      refine ⟨Era.orn s.majors.chart hp hi rfl,?_⟩
      change 1*f.f.locate b j+0∈_
      rw [←hS.per,one_mul,add_zero]
      exact (mem_filter.1 hm).1
   have he:v.A=(Was.atom 0,0):=rfl
   refine ⟨hb,hb.listP rfl rfl,hS.fare,?_⟩
   intro k m hi ht
   have hz(k:ℕ):0≠k → k≥1:=by omega
   refine ⟨by change |(1:ℝ)| ≤ _ ; rw [abs_one]; exact one_le_pow₀ (by norm_num),?_⟩
   intro j _
   exact ⟨fun h=> (h rfl).elim,fun _=>rfl, fun i _ h=> (h rfl).elim,fun _ _ _=>rfl⟩

lemma partake (x y:ℕ):
   (nave c f a x).seekR y=prize c x y:=by
    let v:= nave c f a x
    rw [worth hS.chart, Pale.seekR]
    have he:v.astro x=1:=Pale.boostOne v x (fun _ _=> rfl)
    have hf:= windId (p:=v) rfl y
    by_cases h:v.screenP y
    · rw [ite_eq_left (show v.screenP y ∧ v.goodY y from ⟨h,hf.1⟩),ite_eq_left (show x∈e.v.S0 ∧ y∈e.zone c.b ∧ e.walking x y c.b c.scroll=true from h)]
      change boltQ _ (v.warm*1*f.aimP _ (v.peel y) * v.astro x) = _
      rw [he,hS.ship,hf.2,mul_one,mul_one]
      rfl
    rw [ite_eq_right (fun hz=>h hz.1),ite_eq_right (show ¬(x∈e.v.S0 ∧ y∈e.zone c.b ∧ e.walking x y c.b c.scroll=true) from h)]

lemma festival1 {x:ℕ}(hx:x∈u.D.P) :
     Carnival c x (creditD (nave c f a x)) :=
   solace rfl (hS.bears hx) (fun i hi hh j hj=>by
       exact (hS.via i hi j hj).trans (ite_eq_right hh)) (hS.partake x)

end Aim

lemma companion {c:Weather e}(he:c.forced)(h:c.b=false)(hv:Crude e) (x:ℕ)(hx:x∈u.D.P):
     ∃ f, Carnival c x f :=by
    let q:=e.v.t; let s:=u.plotM; let v:=q.fore
    let b:= c.job0
    have hp:=he.1
    have hh := hp.majors.good.2
    have ho:= he.step0.1
    have ht : c.raysQ∈ (q.companion s e.v.roll).rays:=by
         simpa only [job0,ashes,h,Bool.false_eq_true,ite_false] using ho
    have hQ:v.ready s c.spark0:=by
        unfold v Quest.fore Quest.ready
        have he2:c.spark0 ≤ e.v.m:= he.early0.le
        change _ ≤ s.height∧_ ≤ _∧ _ ≤ _∧ q.u+_ ≤ s.roof∧q.t+c.spark0 ≤ s.roof∧q.tag.sane s.P q.i q.a
        change q.ready s e.v.m at hh; obtain ⟨h1,h2,h3,h4,h5,h6⟩:=hh; exact ⟨h1,h2,h3,by omega,by omega,h6⟩
    obtain ⟨p,hP⟩:= hv.taken he v c.arcQ hQ
    let f:Ship e:=⟨⟨v,c.spark0,c.arcQ⟩,p⟩
    let A:= Coin.mult c.α Aqua.zet
    have he1:Aim c f A:=by
       refine ⟨he,hP,rfl,rfl,?_,?_,?_⟩
       · rw [show A.v=c.α.v*zeta from by simp [A,Aqua.coinZ],abs_mul]
         have hm:|zeta| ≤ 1:=by norm_num [zeta,At.small,delta,Hie.A]
         apply le_trans (mul_le_mul he.calm hm (abs_nonneg _) (by norm_num))
         simpa only [mul_one] using mass1 12 e.d
       · intro i hi j hj
         have hs : (c.lane0 i j).fog.first0=false:=h
         rw [he.itemized i j hi hj]
         unfold RowD.pickA
         dsimp only; rw [ite_eq_right (show ¬(c.lane0 i j).fog.first0=true from by rw [hs];decide)]
         change (if i=0 then _ else _)=_
         split
         · rw [h, show RowD.skies u.r u.x e.c (c.lane0 i j).fog=Print.issued f.s.dye from c.spokenE]
           rfl
         rfl
       intro x y
       have hu:e.v.roll c.spark0=forecast u.plotM c.spark0:= vault _ _ he.early0
       change c.α.v*_ = A.v*(forecast s c.spark0).outR v c.arcQ x y
       rw [←hu,show A.v=c.α.v*zeta from by simp [A,Aqua.coinZ]]
       unfold job0 ashes
       rw [h]
       change c.α.v*(zeta*_)=_
       rw [mul_assoc]
    exact ⟨_,he1.festival1 hx⟩

end Single
end
end ExactDerandomization.Chron.Moon.Weather

end

section

namespace ExactDerandomization.Chron.Moon.Weather
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Pale Quest
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}

variable {e:Chron.Moon u}
namespace Pore

structure MillX (c:Weather e) (b:Quest.Batch):Prop where
     health:c.forced
     way:c.b=true
     M:Befit u.plotM e.v.t b
variable {c:Weather e}{b:Batch}
namespace MillX
variable (hC:MillX c b)
include hC
lemma cash : c.job0 = e.v.t.pipe u.plotM e.v.roll b e.v.m := by
    unfold job0 ashes Quest.start
    rw [hC.way,ite_eq_left rfl]
    obtain ⟨ha,hh|⟨he,hb⟩⟩|⟨ha,hb,hk,j,hj⟩:=hC.M
    · rw [hh]; conv_rhs=> rw [show b=⟨b.pilot,b.count,false⟩ from by cases b;grind]
    · rw [he]; dsimp only; congr <;>grind
    rw [hj]; dsimp only; congr <;> grind
lemma circle : c.raysQ∈e.v.t.company u.plotM b e.v.m:=by
    have hh:=hC.health.step0.1; rw [hC.cash] at hh; exact hh
lemma safe (h:c.raysQ.2<2): c.raysQ.1∈ e.v.t.tray u.plotM e.v.t.i e.v.m:=by
    have he:=hC.circle
    unfold company at he
    rcases mem_union.1 he with hz|hz
    · exact (mem_product.1 hz).1
    split at hz
    · next hc=> have he:c.raysQ=(e.v.t.i,2):=mem_singleton.1 hz;rw [he] at h; omega
    simp only [notMem_empty] at hz
lemma joint (h:c.raysQ.2=1): 0<b.count := by
    have he:=hC.circle
    unfold company at he
    by_contra! hc; rw [ite_eq_left (by omega:b.count=0)] at he
    obtain hm|hm:=mem_union.1 he
    · have ht:=mem_range.1 (mem_product.1 hm).2;omega
    split at hm
    · next hj=> have hw:c.raysQ=(e.v.t.i,2):=mem_singleton.1 hm
                rw [hw] at h; omega
    contradiction
lemma chop(h:2 ≤ c.raysQ.2): c.raysQ.2=2∧ b.trim=true ∧ c.raysQ.1=e.v.t.i :=by
    have he:=hC.circle
    unfold company at he; obtain hm|hm:=mem_union.1 he
    · have hr:=mem_range.1 (mem_product.1 hm).2;split at hr <;>omega
    split at hm
    · next hj=> have hw:c.raysQ=(e.v.t.i,2):=mem_singleton.1 hm
                rw [hw]; exact ⟨rfl,hj,rfl⟩
    contradiction
lemma door (h:c.raysQ.2<2)(p _ : ℕ)(hu:p ≤ e.v.t.u)(hi:e.v.t.i≤p) :
    (binReq e.v.t p c.raysQ.1).ready u.plotM c.spark0:=
     Quest.eddy hC.health.1.majors.good.2 (hC.safe h) hC.health.cards.2 hi hu
lemma spiral (h:c.raysQ.2<2) :
     2^nar e.v.t.a c.raysQ.1 ≤ u.n:=by
    let s:=u.plotM
    have he:= hC.health.1; have hv := he.majors.good.2
    have hp := e.v.t.trayBudget s hv (hC.safe h) hC.health.cards.2
    apply s.fits he.majors.chart.sc
    omega

lemma potC :
    origin e.c≠0 :=by
    change (shaped e.v.t.tag).1 ≠0
    obtain ⟨-,hh|⟨he,_⟩⟩|⟨-,-,-,j,hj⟩:=hC.M
    · rw [hh]; cases b.pilot <;>simp [shaped]
    · rw [he]; exact Nat.ne_of_gt (by change 0<4;omega)
    rw [hj]; exact Nat.ne_of_gt (by change 0<1;omega)
lemma wing(n:ℕ):
   RowD.hinge u.w0 e.c n=bitR (e.v.t.bend b n):=by
    have hP(o:Quest)(b:Batch)(u0 g i z:ℕ)(hw:Befit u.plotM o b):
      RowD.hinge u.w0 (kit i (u0,g) (bitR o) z) n=bitR (o.bend b n):=by
         obtain ⟨j,k,t,v,a,h⟩:=o
         obtain ⟨z,m,l⟩:=b; unfold Befit at hw; dsimp only at hw
         obtain ⟨hl,hr|⟨hr,hs⟩⟩|⟨hl,hs,hx,w,hr⟩:=hw
         · subst a; cases z <;> rfl
         · subst a; subst z; rfl
         subst a; subst z; subst m; rfl
    exact hP e.v.t b e.v.m e.i (1:ℕ) (Age.env e.c) hC.M
omit hC in
lemma beams(b:Bool)(k:ℕ):
    RowD.school e.c k b=bitR (e.v.t.binReq (if b then e.v.t.i else e.v.t.u) k):=rfl

lemma actor (he:c.raysQ.2=0)(hT:Crude e)(x:ℕ)(hx:x∈u.D.P) :
    ∃ f, Carnival c x f:=by
    let k:=c.raysQ.1
    let p:=e.v.t
    let q:=p.binReq p.u k
    have hp:=hC.health.1
    have hh:=hp.majors.good.2
    have h0:c.raysQ.2<2:=by omega
    obtain ⟨f,hf⟩:=hT.taken hC.health q c.arcQ (hC.door h0 p.u 0 le_rfl hh.2.1)
    let v:Ship e:=⟨⟨q,c.spark0,c.arcQ⟩,f⟩
    have hr:= hC.spiral h0
    have HA:Single.Aim c v c.β:=by
      refine ⟨hC.health,hf,rfl,rfl,hC.health.sharesC (k:=k) rfl hr,?_,?_⟩
      · intro i hi j hj
        rw [hC.health.itemized i j hi hj]
        unfold RowD.pickA; dsimp only
        let s:= c.lane0 i j
        have hp:s.fog.first0=true:=hC.way
        have hm:(s.fog.ray (greenY e.c))=c.raysQ:=hC.health.house.2.1
        rw [ite_eq_left hp,ite_eq_right hC.potC,
            ite_eq_left (show s.fog.cell0.2.1=0 from (congrArg Prod.snd hm).trans he),
            show (c.lane0 i j).fog.k (greenY e.c)=k from congrArg Prod.fst hm,
            hC.way]
        change (if i=0 then _ else _)=_
        rw [show RowD.skies u.r u.x e.c (c.lane0 i j).fog=Print.issued c.arcQ from (show RowD.skies u.r u.x e.c (c.lane0 i j).fog=_ from c.spokenE), (Pore.MillX.beams (e := e))]
        rfl
      intro i j
      rw [hC.cash,hC.health.shareq (k:=k) rfl hr]
      have hm:e.v.roll c.spark0=forecast u.plotM c.spark0:= vault _ _ hC.health.early0
      dsimp only [pipe,sign]
      rw [ite_eq_left he]
      change _*(loaded u.n e.v.t.a k*(e.v.roll c.spark0).outR q c.arcQ i j)=_
      rw [hm,mul_assoc]
    exact ⟨_,HA.festival1 hx⟩

lemma lastC (he:2 ≤ c.raysQ.2)(hT:Crude e)(x:ℕ)(hx:x∈u.D.P) :
    ∃ f,Carnival c x f:=by
   let p:=e.v.t
   let i:=p.i
   let n:=max p.a p.i
   let s:=u.plotM
   have hp:=hC.health.1
   have hh:=hp.majors.good.2
   obtain ⟨h1,h2,h3⟩:=hC.chop he
   let q:=p.bend b n
   have hl:= hC.M.count hh
   have hg:= hC.M.pos h2
   have hf: q.ready s c.spark0:= Quest.BendOK hC.M hh hg (le_max_right ..) (by
             have hi0:=hC.health.early0; obtain ⟨_,hv,ht,hb,hw,hQ⟩:=hh
             unfold n p; change _ ≤ u.plotM.roof; omega) hC.health.early0.le
   have hw:2^nar p.a i  ≤ u.n:= s.fits hp.majors.chart.sc (by
            have he := hf.2.2.2.2.1
            change nar p.a i+c.spark0 ≤ _ at he; omega)
   obtain ⟨f,hf⟩:=hT.taken hC.health q c.arcQ hf
   let v:Ship e:=⟨⟨q,c.spark0,c.arcQ⟩,f⟩
   let C:=Coin.neg c.β
   have HA:Single.Aim c v C:=by
      refine ⟨hC.health,hf,rfl,rfl,?_,?_,?_⟩
      · unfold C; rw [Coin.neg0,abs_neg]; exact hC.health.sharesC h3 hw
      · intro i hi j hj
        rw [hC.health.itemized i j hi hj]
        unfold RowD.pickA; dsimp only
        let t:= c.lane0 i j
        have hp:t.fog.first0=true:=hC.way
        have hm:t.fog.ray (greenY e.c)=c.raysQ:=hC.health.house.2.1
        have hi : t.fog.cell0.2.1 =2:=(congrArg Prod.snd hm).trans h1
        rw [ite_eq_left hp,ite_eq_right hC.potC,ite_eq_right (by omega:t.fog.cell0.2.1≠0),ite_eq_right (by omega:t.fog.cell0.2.1≠1),hC.way]
        rw [hC.wing, show RowD.skies u.r u.x e.c (c.lane0 i j).fog=Print.issued c.arcQ from (show RowD.skies u.r u.x e.c (c.lane0 i j).fog=_ from c.spokenE)]; rfl
      intro x y
      rw [hC.cash,show C.v=-c.β.v from Coin.neg0 c.β,hC.health.shareq h3 hw]
      have hm:e.v.roll c.spark0=forecast u.plotM c.spark0:= vault _ _ hC.health.early0
      dsimp only [pipe,sign]
      rw [ite_eq_right (by omega:c.raysQ.2≠0),ite_eq_right (by omega:c.raysQ.2≠1)]
      change _* (-(loaded u.n p.a i*(e.v.roll c.spark0).outR q c.arcQ x y))=_
      rw [hm,mul_neg,neg_mul,mul_assoc]
   exact ⟨_,HA.festival1 hx⟩
end MillX
end Pore
end
end ExactDerandomization.Chron.Moon.Weather

end

section

namespace ExactDerandomization.Chron.Moon.Weather
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Pale Quest
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Chron.Moon u}
namespace Pairing
abbrev ahead (p:Ship e)(i:ℕ):= (hole (p.s.c 12 0) i, Crest.op p.src 0 i)
def servants (c:Weather e) (p q:Ship e)(g:Coin)(x i:ℕ):Pale e:=
    ⟨c,x,i,ahead p i,p.f.coversF x i,q,Crest.postN,g,Crest.op p.src 1 i,0,
                                                  fun _=> p.scholar x i, fun _ _=>1⟩

structure Union4 (c:Weather e)(p q:Ship e) (a:Coin):Prop where
    loft:c.forced
    fitp:p.Armed
    fitq:q.Armed
    front:p.s.govern=true
    land:(u.plotM.stage q.s.t.i).S=(u.plotM.stage e.v.t.i).S
    coin0: |a.v| ≤ massB 12 e.d
    cue :∀ x i,i<e.v.Rslots→∀ j<e.v.Rslots,Lily.arms u.r u.x (e.a,enc (c.lane0 i j))=
                                                         (servants c p q a x i).ash j
    focus :∀ x y, c.α.v*(c.job0.lines c.raysQ).seq c.spark0 c.arcQ x y=
           a.v*∑ j∈p.s.S1,p.aimP x j*q.aimP j y

variable {p t:Ship e} {c:Weather e}{a:Coin}
namespace Union4
variable (hC:Union4 c p t a)
include hC
lemma forms {x i:ℕ}(hx:x∈u.D.P)(hi:i<e.v.Rslots):
   let v:= servants c p t a x i
   v.Kin:=by
   let v:= servants c p t a x i; have hp:=hC.loft.1
   have hc12:= hC.fitp.here0
   have hZ:v.Span:=by
      have hl:u.D.W 0+u.D.D e.a ≤ u.D.W e.a:= Stone.zeroR ..
      refine ⟨hC.loft,hx,hi,hC.fitq,fun _=>rfl,hC.cue x i hi,
                         ⟨(NeZero.pos u.n),Nat.zero_le _⟩,(show (0:ℕ)<1 by decide),?_⟩
      intro k j hf
      have hg := (hC.fitq.sturdy.sector.light.insured k j hf).2
      have hv:= Fabric.Good.n1 hp.majors.chart hC.fitq.good hg
      refine ⟨Era.orn hp.majors.chart hl hv rfl,?_⟩
      change 1*t.f.locate k j+0∈ _
      rw [one_mul, add_zero,←hC.land]
      exact (mem_filter.1 hg).1
   refine ⟨hZ,?_,hC.coin0,?_⟩
   · intro j hj
     apply cam hp
     have H:=hZ.regionQ hj
     refine Era.echoPort H hC.fitp.sturdy hC.front hi rfl
                             hc12 (hC.fitp.mom 12) ?_ ?_ ?_
     · change clim u.w0.p+1  ≤ Era.budget u.r
       unfold Era.budget bootC; change clim u.r.w.p+1 ≤ _; omega
     · intro m j h; change p.f.coversF x i=some (m,j)↔m≠0 ∧ p.f.tag x i=m∧ p.f.locate x i=j
       unfold Producer.coversF Producer.awake
       split
       · next h=> simp only [Option.some.injEq,Prod.mk.injEq]; grind
       next h=> simp only [reduceCtorEq,false_iff]; grind
     intro m b _ hh; change p.f.coversF x i=some _ at hh
     unfold Producer.coversF at hh; split at hh
     · next he=>
                simp only [Option.some.injEq,Prod.mk.injEq] at hh
                have hT := (hC.fitp.sturdy.sector.light.insured _ _ he).2
                have hs:b∈u.D.P:=hh.2 ▸ Fabric.Good.n1 hp.majors.chart hC.fitp.good hT
                exact hZ.forming hj hs
     contradiction
   intro m l h hp
   have hr:= hC.fitp
   refine ⟨hr.stop hx hi,fun j _=>?_⟩
   refine ⟨fun _=>⟨p.src,hole 1 i,rfl,hc12,hr.tempo hx hi⟩,?_,?_,fun h x _=>rfl⟩
   · intro h
     exact False.elim ((Nat.ne_of_gt (Seek.binpos p.src (hole 1 i))) h)
   intro x h hp; exact (hp rfl).elim

lemma royalty(x y:ℕ)(hx:x∈u.D.P) :
     ∑ i∈range u.w0.p.K,(servants c p t a x i).seekR y =prize c x y := by
    let v(i):=servants c p t a x i
    rw [worth hC.loft]
    by_cases he:(v 0).screenP y
    · rw [ite_eq_left (show x∈e.v.S0 ∧ y∈e.zone c.b∧e.walking x y c.b c.scroll=true from he),hC.focus ..]
      let f(k):ℝ:=p.scholar x k*t.aimP (p.f.locate x k) y
      let P:=p.s.S1
      have hm : ∑ j∈P,p.aimP x j*t.aimP j y=∑ i∈range u.w0.p.K,f i:= by
         let S:=range u.w0.p.K
         have hs : ∑ j∈P,p.aimP x j*t.aimP j y=
              ∑ j∈P, ∑ k∈S,(if p.f.locate x k=j then p.scholar x k else 0)*t.aimP j y:=by
            apply sum_congr rfl; intro j hj
            rw [←sum_mul]; exact congrArg (fun a=>a*_) (hC.fitp.sturdy.sector.supply x j hx).symm
         rw [hs,sum_comm]
         apply sum_congr rfl; intro j hj
         let a0:= p.f.locate x j
         rw [sum_eq_single a0]
         · rw [ite_eq_left rfl]
         · intro i _ he; rw [ite_eq_right (Ne.symm he),zero_mul]
         intro ht
         have hh :¬p.f.awake x j:=fun e=>ht (hC.fitp.sturdy.sector.light.insured _ _ e).2
         rw [show p.scholar x j=0 from ite_eq_right hh]; split<;>rw [zero_mul]
      have hu(i): (v i).seekR y=boltQ c.b (a.v*f i):=by
           have hv:(v i).o=Crest.postN:=rfl
           have hp:(v i).screenP y:=he
           unfold Pale.seekR; rw [ite_eq_left ⟨hp,(Pale.windId hv y).1⟩]
           change (match p.f.coversF x i with | none=> _| some (k,w)=> boltQ c.b ((v i).till w y))=_
           unfold Producer.coversF
           by_cases hl:p.f.awake x i
           · rw [ite_eq_left hl]; dsimp only
             have hh: (v i).peel y=y:= (Pale.windId hv y).2
             unfold Pale.till; rw [hh,Pale.boostOne (v i) _ (by intro; intros; rfl)]
             unfold f; rw [mul_one,mul_assoc]; rfl
           rw [ite_eq_right hl]
           unfold f
           rw [show p.scholar x i=0 from ite_eq_right hl]; simp only [zero_mul,mul_zero]; cases c.b <;> rfl
      rw [show ∑ i∈p.s.S1,_ = _ from hm,mul_sum]
      have hL (i:ℕ) : ∑ j∈range i,boltQ c.b (a.v*f j)=boltQ c.b (∑ j∈range i,a.v*f j):=by
           induction i with
           | zero=>simp only [range_zero,sum_empty]; cases c.b <;> rfl
           | succ i ih=> rw [sum_range_succ,sum_range_succ,ih]; cases c.b <;> simp [boltQ,harvest0.spread]
      change ∑ i∈range _,(v i).seekR y=_
      simp_rw [hu]; exact hL _
    rw [ite_eq_right (show ¬ (x∈e.v.S0 ∧ y∈e.zone c.b∧e.walking x y c.b c.scroll=true) from he)]; apply sum_eq_zero; intro i _
    have hh:¬(v i).screenP y:=he
    exact ite_eq_right (fun hx=> hh hx.1)

lemma bills(x:ℕ)(he:x∈u.D.P):
   ∃ f, Carnival c x f:=
   ⟨_,festival (p:=fun i=>servants c p t a x i) (fun _=>rfl) (fun _=>rfl)
                                          (fun _ hi=>⟨rfl,hC.forms he hi⟩)
                                                (fun y=>hC.royalty x y he)⟩

end Union4
end Pairing
end
end ExactDerandomization.Chron.Moon.Weather

end

section

namespace ExactDerandomization.Chron.Moon.Weather.Pore.MillX
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Pale Quest Pairing
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Chron.Moon u}
variable {c:Weather e}{b:Batch}
lemma mix4 (hC:MillX c b)(he:c.raysQ.2=1)(hT:Crude e){x:ℕ}(hx:x∈u.D.P):
    ∃ f, Carnival c x f:=by
   let q:= e.v.t; let k:=c.raysQ.1
   let i:= q.i
   let p:= q.bend b i
   let g:= q.binReq i k
   let A:= c.arcQ
   have hp:= hC.health
   have ha:=hp.1
   have hh:=ha.majors.good.2
   have hz:i+c.spark0  ≤  u.plotM.roof:=by
        have h0:=hp.early0; have ht:=hh.2.1;have hw:=hh.2.2.2.1; unfold i q; omega
   have hP:p.ready u.plotM c.spark0:=Quest.BendOK hC.M hh (hC.joint he) le_rfl hz hp.early0.le
   have hQ:g.ready u.plotM c.spark0:=hC.door (by omega) _ 0 hh.2.1 le_rfl
   obtain ⟨f,hf⟩:= hT.taken hp p (leftP A) hP
   obtain ⟨s,hs⟩:= hT.taken hp g (rightP A) hQ
   let v:Ship e:=⟨⟨p,c.spark0,leftP A⟩,f⟩
   let w:Ship e:=⟨⟨g,c.spark0,rightP A⟩,s⟩
   let a:= Coin.mult c.β (Aqua.rawcoins u.n i)
   have h0:= hC.spiral (by omega)
   have hY:2^i ≤ u.n:= u.plotM.fits ha.majors.chart.sc (by omega)
   have hx':a.v=c.β.v*peeler u.n i:= by unfold a; rw [Coin.mul0,Aqua.raw _ hY]
   have HK:Union4 c v w a:= by
      refine ⟨hp,hf,hs,rfl,rfl,?_,?_,?_⟩
      · rw [hx',abs_mul]
        have ht:=hC.health.sharesC (k:=k) rfl h0
        have he:= Est.spins hY
        rw [abs_of_nonneg he.1]
        exact le_trans (mul_le_mul_of_nonneg_left he.2 (abs_nonneg _)) (by rwa [mul_one])
      · intro x j hj t ht
        rw [hp.itemized _ _ hj ht]
        unfold RowD.pickA; dsimp only
        let r:= c.lane0 j t
        have hm:r.fog.cell0.2.1=1 :=he
        rw [ite_eq_left (show r.fog.first0=true from hC.way),ite_eq_right hC.potC,
             ite_eq_right (show r.fog.cell0.2.1≠0 by omega),ite_eq_left hm,
             show (c.lane0 j t).fog.k (greenY e.c)=k from congrArg Prod.fst hp.house.2.1,(Pore.MillX.beams (e := e))]
        rw [show RowD.skies u.r u.x e.c r.fog=Print.issued A from c.spokenE]
        have hU:RowD.hinge u.r.w e.c (stageQ e.c)=bitR p:=hC.wing _
        rw [hU]

        unfold Pale.ash; rw [show (servants c v w a x j).k.b=true from hC.way]
        rfl
      intro x y
      rw [hC.cash,hx',hp.shareq (k:=k) rfl h0]
      simp only [pipe,sign,ite_eq_right (show c.raysQ.2≠0 by omega),ite_eq_left he]
      have he:= vault (s:=u.plotM) _ _ hp.early0
      let D:= q.plan u.plotM
      change c.α.v*(loaded u.n e.v.t.a k*(peeler u.n i*
        ∑ j∈D.midpoint i c.arcQ,(e.v.roll c.spark0).outR p (leftP c.arcQ) x j*(e.v.roll c.spark0).outR g (rightP c.arcQ) j y))=_
      rw [show e.v.roll c.spark0=_ from he]
      change c.α.v*(loaded u.n e.v.t.a k*(peeler u.n i*∑ j∈v.s.S1,v.aimP x j*w.aimP j y))=_
      ring
   exact HK.bills _ hx
end
end ExactDerandomization.Chron.Moon.Weather.Pore.MillX

end

section

namespace ExactDerandomization.Chron.Moon.Weather
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Pale Quest
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Chron.Moon u}
namespace Royal
abbrev M (u:Line (q:=q) (w:=w) (h:=h)):=u.w0.p.M
def stain(_:Chron.Moon u)(i x:ℕ):Stars:=
     if x%M u=i then some (0,x/M u) else none
abbrev wreath (f:Ship e) (l j:ℕ):ℕ:= u.vecL (detector l j) f.s.m 17 0 f.s.dye
def lace(e:Chron.Moon u)(f:Ship e)(l i j x:ℕ):ℝ:=
   if i=0 then 1 else (e.v.roll f.s.m).outV (detector l j) f.s.dye x
def pick(e:Chron.Moon u)(f:Ship e)(l i x:ℕ):ℝ:= Net.carrier u.plotM e.v.roll f.s.m l i f.s.dye x
def ratchet (c: Weather e)(f:Ship e)(l i j:ℕ)(x:ℕ):Pale e:=
   ⟨c,x,0,Crest.portN 0 (Was.downX u.r i),stain e i x,f,(Was.atom (3+j),M u,j),
                 c.β,0,if i=0 then 0 else wreath f l 0,fun _=>1,fun j x=> lace e f l i j x⟩

structure Corona (c:Weather e)(f:Ship e)(l i j :ℕ):Prop where
      start:c.forced
      pp : Crude e
      posI:i<M u
      posJ:j<M u
      fuel:f.Armed
      momento : c.spark0=f.s.m
      hop : l+1=e.v.t.i∧ l=f.s.t.i
      fair : |c.β.v|  ≤ massB 12 e.d
      front:∀ x,∀ r<e.v.Rslots,∀ s<e.v.Rslots,
                Lily.arms u.r u.x (e.a,enc (c.lane0 r s)) = if r=0 then (ratchet c f l i j x).ash s else bald
      shape:∀ x y, c.α.v*(c.job0.lines c.raysQ).seq c.spark0 c.arcQ x y=
                   (if x%M u=i∧ y%M u=j then c.β.v*f.aimP (x/M u) (y/M u)*pick e f l i (x/M u) else 0)

namespace Corona
variable {c:Weather e}{f:Ship e}{l i j:ℕ}(h0:Corona c f l i j)
include h0
lemma tokenM : (u.plotM.stage e.v.t.i).S=copyZone (M u) (u.plotM.stage f.s.t.i).S:= by
   obtain ⟨hl,hb⟩:=h0.hop
   rw [←hl, Scene.mature, Stg.next]
   change copyZone _ _=_
   rw [u.plotM.aligned,hb]; rfl
lemma cardK : M u < u.n :=h0.start.1.majors.chart.sc.radix_small
lemma alive {b:ℕ}(hi:b<u.w0.p.T): (detector l b).ready u.plotM f.s.m:=by
   have hx:=h0.fuel.good.2
   unfold Quest.ready at hx
   have hL:=h0.hop.2
   unfold Peek.ready detector
   dsimp only
   exact ⟨by omega,le_rfl,by omega,rfl,hi⟩

omit h0 in
lemma cornea (x z:ℕ): (ratchet c f l i j x).astro z=pick e f l i z:=by
    let v:= ratchet c f l i j x
    unfold pick
    by_cases h:i=0
    · apply Eq.trans (v.boostOne z (by intro j hj; exact ite_eq_left h))
      unfold carrier; rw [ite_eq_left h]
    unfold carrier; rw [ite_eq_right h]
    let r:= fun a=> (e.v.roll f.s.m).outV (detector l a)
    have he(n:ℕ) : Nest.Good.maxs (fun j=>v.betaQ j z) n=Maxer r n f.s.dye z:= by
      induction n with
      | zero=> rfl
      | succ n ih=>exact congrArg₂ max ih (show lace e f l i n z=_ from ite_eq_right h)
    exact congrArg boost (he _)

lemma labour {x:ℕ}(hx:x∈u.D.P): (ratchet c f l i j x).Kin := by
    let v:=ratchet c f l i j x; let m:=M u
    have hg:0 < m:=by have hj:=h0.posI;dsimp only [m];omega
    have hh:=(h0.start.1).majors; let S:= (u.plotM.stage f.s.t.i).S
    have hp:u.D.W 0+u.D.D e.a ≤ u.D.W e.a:= Stone.zeroR ..
    have hZ:v.Span:=by
      refine ⟨h0.start,hx,Kpos _,h0.fuel,fun _=>rfl,?_,?_,h0.posJ,?_⟩
      · intro j hj
        exact (h0.front x 0 (Kpos _) j hj).trans (ite_eq_left rfl)
      · exact ⟨h0.cardK.le,(h0.posJ.trans h0.cardK).le⟩
      intro b k h
      have hz:= (h0.fuel.sturdy.sector.light.insured _ _ h).2
      let y:=f.f.locate b k; have ht:y∈u.D.P:= Fabric.Good.n1 hh.chart h0.fuel.good hz
      have hc : v.crop y=radix m y j:=by unfold crop radix; change m*y+j=j+m*y; omega
      have hy:radix m y j∈ (u.plotM.stage e.v.t.i).S:=by
         rw [h0.tokenM];exact Hie.inside (mem_filter.1 hz).1 h0.posJ
      have hf := Fabric.Good.encs hh.chart hh.good hy
      refine ⟨Era.oust hh.chart hh.book hp ht h0.posJ rfl (mem_range.2 (Nat.lt_succ_of_le hf.le)),?_⟩
      change v.crop y∈_
      rwa [hc]
    refine ⟨hZ,hZ.simple rfl ?_ ?_,h0.fair,?_⟩
    · refine le_trans ?_ hh.book.coinbook
      unfold Was.downX Was.fan bootC; have ht : i<u.r.w.p.M:=h0.posI; unfold Was.radixG;omega
    · intro b y hs
      let p:=v.surf 0
      unfold Was.Flight
      change (if x%m=i then some _ else none)=_ ↔ _∧ x ≤ u.n ∧ y ≤ u.n ∧
                     (if 3+(i+m)=0 then _ else if 3+(i+m)=1∨3+(i+m)=2 then _ else _)
      have he:i < m:=h0.posI
      have hr:x≤u.n:= Nat.le_of_lt_succ (mem_range.1 hx)
      have hq:y%m < m:=Nat.mod_lt _ hg
      have H(y): radix m y i /m=y∧radix m y i%m=i:= fromrad _ _ _ he
      have hE:3+(i+m)-3=i+m:=by omega
      have hW: ¬ ((3+(i+m)=1) ∨ (3+(i+m)=2)):=by omega
      have hQ:¬(3+(i+m)=0):=by omega
      change (if x%m=i then some ((0,x/m):Rill.History) else none)=some (b,y) ↔
                 b<Era.budget u.r ∧ x≤u.n ∧ y≤u.n ∧ if 3+(i+m)=0 then x=y∧b=0 else if 3+(i+m)=1∨3+(i+m)=2 then _ else b=0 ∧ if 3+(i+m)-3 < m then _ else 3+(i+m)-3-m < m∧ x=radix m y (3+(i+m)-3-m)
      simp only [ite_eq_right hQ,ite_eq_right hW,hE,ite_eq_right (by omega: ¬ i+m < m),show i+m-m=i by omega]
      constructor
      · intro hv; split at hv
        · next hw=>
          simp only [Option.some.injEq, Prod.mk.injEq] at hv
          have hy:y ≤ x:=by rw [←hv.2];exact Nat.div_le_self ..
          refine ⟨?_,hr,hy.trans hr,hv.1.symm,he,?_⟩
          · rw [←hv.1]; exact Nat.zero_lt_succ _
          unfold radix; rw [←hv.2,←hw,Nat.mod_add_div]
        contradiction
      rintro ⟨-,hc,hu,hD,hi,hT⟩;rw [hD,hT,(H y).1,(H y).2,ite_eq_left rfl]
    intro b y hs hL; have h1:v.Span:=hZ
    have hc:(if x%m=i then some ((0,x/m):Rill.History) else none)=some (b,y):=hL
    split at hc
    · next hv=>
               simp only [Option.some.injEq,Prod.mk.injEq] at hc
               have hy:y ≤ u.n:=by rw [←hc.2]; exact le_trans (Nat.div_le_self ..)
                                           (Nat.le_of_lt_succ (mem_range.1 hx))
               refine ⟨?_, fun z hz=>⟨?_,fun h=> rfl,?_,?_⟩⟩
               · change |(1:ℝ)| ≤  _
                 rw [abs_one]; exact one_le_pow₀ (by norm_num)
               · intro h; exact (h rfl).elim
               · intro a ha h
                 have hm:i≠0:=fun e=> h (by show (if i=0 then _ else _) = 0;rw [ite_eq_left e])
                 have HE:= h0.pp.caul (wM:=f.s.dye) h0.start h0.momento.symm (h0.alive ha)
                                 (show y∈u.D.P from mem_range.2 (Nat.lt_succ_of_le hy))
                 let s:=v.rest z
                 refine ⟨wreath f l a,hole 1 0,?_,HE.1,?_⟩
                 · unfold Nest.catshot
                   have hk:s.capV=wreath f l 0:=ite_eq_right hm
                   change rate0 (dec s.capV) a=_; rw [hk]
                   unfold wreath vecL clr; rw [dec_round]
                   rfl
                 change u.D.Voice _ _ _ _ _ (lace e f l i a _)
                 unfold lace; rw [ite_eq_right hm]; exact HE.2
               intro h b _
               have hl:i=0:=by
                  change (if i=0 then 0 else _) = 0 at h; split at h; assumption; exact False.elim (Age.cpos _ h)
               exact ite_eq_left hl
    contradiction

lemma royale (x y:ℕ) :(ratchet c f l i j x).seekR y=prize c x y:= by
     let m:= M u
     let v:=ratchet c f l i j x
     rw [worth h0.start]
     unfold Pale.seekR
     by_cases hp:v.screenP y
     · rw [ite_eq_left (show x∈e.v.S0∧ y∈e.zone c.b∧e.walking x y c.b c.scroll=true from hp),h0.shape]
       by_cases hz:v.goodY y
       · rw [ite_eq_left (show v.screenP y∧ v.goodY y from ⟨hp,hz⟩)]
         change (match (if x%m=i then some ((0,x/m):Rill.History)else none) with
                 |none=>_
                 |some (k,w)=>boltQ c.b (v.till w y))=_
         by_cases hc :x%m=i
         · rw [ite_eq_left hc,ite_eq_left (show x%M u=i∧y%M u=j from ⟨hc,hz⟩)]
           change boltQ _ (_*1*_ * v.astro (x/m))=_
           rw [show v.astro (x/m)=pick e f l i (x/m) from (Royal.Corona.cornea (c := c) (f := f) (l := l) (i := i) (j := j) x (x/m)),mul_one];rfl
         rw [ite_eq_right hc,ite_eq_right (show ¬ (x%M u=i∧ y%M u=j) from fun he=>hc he.1)]; cases c.b <;> rfl
       rw [ite_eq_right (fun e=>hz e.2),ite_eq_right (fun e=>hz e.2)]; cases c.b<;> rfl
     rw [ite_eq_right (show ¬(x∈e.v.S0∧ y∈e.zone c.b∧e.walking x y c.b c.scroll=true) from hp),ite_eq_right (fun h=>hp h.1)]
lemma spiral {x:ℕ}(hx:x∈u.D.P):∃ u, Carnival c x u:=by
    let v:=ratchet c f l i j x
    refine ⟨creditD v,solace rfl (h0.labour hx) ?_ (h0.royale x)⟩
    intro b hb hh v hv; exact (h0.front x _ hb _ hv).trans (ite_eq_right hh)
end Corona
end Royal
end
end ExactDerandomization.Chron.Moon.Weather

end

section

namespace ExactDerandomization.Chron.Moon.Weather
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Pale Quest
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Chron.Moon u}

namespace Royal
lemma roadCrew {c:Weather e}(h:c.forced)(hb:c.b=true)(hc:Crude e)(ht:e.v.t.tag=.chip)
    {x:ℕ} (hx:x∈u.D.P):
    ∃ f, Carnival c x f:=by
    let p:=e.v.t
    let s:=u.plotM
    have he:= h.step0.1
    have hP:c.job0=p.start s e.v.roll e.v.m:=by unfold job0 ashes; rw [hb]; rfl
    cases hI:p.i with
    | zero=> rw [hP] at he
             unfold Quest.start at he; rw [show p.tag=.chip from ht, hI] at he
             exact False.elim ((notMem_empty c.raysQ) he)
    | succ l=>
       have hh:c.job0=p.agency s e.v.roll l e.v.m:=by
                           rw [hP]; unfold Quest.start; rw [show p.tag=.chip from ht,hI]
       let q:=c.raysQ; let m:=s.P.M
       have hf:q∈p.fleet s l e.v.m:= by rw [hh] at he;exact he
       let i:=q.2/m; let j:=q.2%m
       have hp :0 < m:=by have hh:=s.P.mOK; unfold m;omega
       obtain ⟨ha,hW⟩:=mem_product.mp hf
       have hi:i < m:=(Nat.div_lt_iff_lt_mul hp).2 (mem_range.1 hW)
       have hj:j < m:=Nat.mod_lt _ hp
       have ht0 :l≤ q.1+pad s.P:= (mem_filter.1 ha).2
       let u0:=p.briq l j q.1
       have hS:p.ready s e.v.m:= h.1.majors.good.2
       have hk:=h.cards.2
       have hk0:= p.trayBudget s hS ha hk
       have hL: u0.ready s c.spark0:= by
          obtain ⟨hv,hb,he,hD,hR,hF⟩:=hS
          have hm:=h.early0
          exact ⟨show l≤ s.height by omega,show l ≤ p.u by omega,
                  le_max_right ..,show p.u+c.spark0 ≤ s.roof by omega,hk0,ht0,hj⟩
       let E:= pane m i j c.arcQ
       obtain ⟨f,hf⟩:=hc.taken h u0 E hL
       let F:Ship e:= ⟨⟨u0,c.spark0,E⟩,f⟩
       have hr:2^nar p.a q.1 ≤ u.n:=by
           apply s.fits h.1.majors.chart.sc; omega
       have ht1:m<u.n:= h.1.majors.chart.sc.radix_small
       have hg:Corona c F l i j:=by
          refine ⟨h,hc,hi,hj,hf,rfl,⟨hI.symm,rfl⟩,h.sharesC (k:=q.1) rfl hr,?_,?_⟩
          · intro x a ha b hh0
            rw [h.itemized _ _ ha hh0]
            let v:=c.lane0 a b
            unfold RowD.pickA; dsimp only
            have he:origin e.c=0:=by change (shaped _).1=0;rw [ht]; rfl
            have hj:v.fog.first0=true:=hb
            have hD:v.fog.ray (greenY e.c)=q:=h.house.2.1
            rw [ite_eq_left hj,ite_eq_left he]
            change (if a=0 then _ else _)=_
            split
            · rw [show (c.lane0 a b).fog.k (greenY e.c)=q.1 from congrArg Prod.fst hD,show stageQ e.c=l+1 from hI, Nat.add_sub_cancel]
              have hE:Prism.swap u.n m i j (RowD.skies u.r u.x e.c c.φ)=Print.issued E:=
                      (congrArg (Prism.swap u.n m i j) c.spokenE).trans (Prism.masked hp ht1 ..)
              have hr :RowD.coral e.c q.1 j=bitR u0:=by
                   unfold RowD.coral;rw [show stageQ e.c=l+1 from hI,Nat.add_sub_cancel];rfl
              change Crest.twins _ _ b (RowD.coral e.c q.1 j) i j m l u.n (RowD.skies u.r u.x e.c c.φ) c.β=_
              rw [hr]
              unfold Crest.twins
              rw [hE]
              unfold Pale.ash
              rw [show (ratchet c F l i j x).k.b=true from hb]
              rfl
            rfl
          intro x y
          rw [hh,h.shareq (k:=q.1) rfl hr]
          unfold agency; dsimp only
          change _*(loaded u.n p.a q.1 * pep _ _ _ _ _ x y)=_
          unfold pep markM
          have hx:e.v.roll c.spark0 = forecast u.plotM c.spark0:=vault _ _ h.early0
          change _*(_*(if _ then _ else _))=_
          split
          · next ha=>
             rw [ite_eq_left (show x%M u=i∧y%M u=j from ha)]
             unfold honor pick
             let g:=fun r=>carrier s e.v.roll r l i E (x/m)
             change c.α.v*(loaded u.n p.a q.1*((e.v.roll c.spark0).outR u0 E (x/m) (y/m)*g c.spark0))=
               c.α.v*loaded u.n p.a q.1*(forecast s c.spark0).outR u0 E (x/m) (y/m)*g c.spark0
             rw [← show e.v.roll c.spark0=forecast s c.spark0 from hx]; ring
          next ha=> rw [ite_eq_right (show ¬(x%M u=i∧ y%M u=j) from ha)]; ring
       exact hg.spiral hx

end Royal

lemma rally {c:Weather e}(h:c.forced)(hv:Crude e){x:ℕ}(hx:x∈u.D.P):
   ∃ f, Carnival c x f:=by
    cases hB:c.b
    · exact Single.companion h hB hv _ hx
    by_cases he:e.v.t.tag=.chip
    · exact Royal.roadCrew h hB hv he hx
    have hh:∃ b:Batch, Pore.MillX c b:=by
        cases hI:e.v.t.tag
        · contradiction
        · next j=> exact ⟨⟨false,u.plotM.P.T,true⟩,h,hB,Or.inr ⟨rfl,rfl,rfl, j,hI⟩⟩
        · next b k=> exact ⟨⟨b,k,false⟩,h,hB,Or.inl ⟨rfl,Or.inl hI⟩⟩
        next k=> exact ⟨⟨true,k,false⟩,h,hB,Or.inl ⟨rfl,Or.inr ⟨hI,rfl⟩⟩⟩
    obtain ⟨b,hp⟩:=hh
    by_cases ht:c.raysQ.2=0
    · exact hp.actor ht hv x hx
    by_cases hs:c.raysQ.2=1
    · exact hp.mix4 hs hv hx
    exact hp.lastC (by omega) hv x hx

end
end ExactDerandomization.Chron.Moon.Weather

end

section

namespace ExactDerandomization.Chron.Moon
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}

variable (e:ExactDerandomization.Chron.Moon u)

abbrev rear0 (j:ℕ):Seed:= Seed.old true j
abbrev firstG (j:ℕ) :=Seed.old false j
namespace Recent
variable {e:ExactDerandomization.Chron.Moon u}
open Surf Fabric Stem

structure Ink (e:ExactDerandomization.Chron.Moon u)(l x:ℕ):Type where
     t: e.v.Hinge e.p l x
namespace Ink
variable {l x:ℕ}(q:Ink e l x)
abbrev u0 := q.t.depot
abbrev frame0(j):= q.u0.tag j
abbrev pos(j):= q.u0.pos j
def pulse(j:ℕ):Stars:= if q.u0.live j then some (q.frame0 j, q.pos j) else none
abbrev word (e:ExactDerandomization.Chron.Moon u)(j:ℕ):Embellish:= Crest.bronze e.c (e.tideC true (0,0)) j
abbrev s (q:Ink e l x)(j:ℕ):Nest u:=e.stash (word e j) x (some (0,x)) (fun _=> q.pulse j)
structure Prints(q:Ink e l x):Prop where
    east:e.Lo
    step:e.i=l+1
    target:x∈ u.D.P
    insight:e.v.HFine e.p l x q.t

namespace Prints
variable {q:Ink e l x}(hA:q.Prints)
include hA
lemma turn0 (j:ℕ)(hj:j<q.u0.n): retired u.w0 e.c (rear0 j):=by
    refine ⟨rfl,?_,?_⟩
    · change e.i≠0; rw [hA.step]; omega
    change j< e.v.Snum (e.i-1)
    rw [hA.step,Nat.add_sub_cancel]
    exact hA.insight.card0 ▸ hj
lemma board (j:ℕ)(hj:j<q.u0.n):
    Lily.arms u.r u.x (e.a,enc (rear0 j))= word e j:=by
     rw [armleg e (Or.inr (Or.inl (hA.turn0 j hj)))]
     rfl

lemma teeth (a:ℕ): Crest.pastC e.c a=e.v.c a l:=by
    unfold Crest.pastC
    refine congrArg enc (Prod.ext rfl (Prod.ext ?_ rfl))
    exact Prod.ext rfl (by change e.i-1=l;rw [hA.step,Nat.add_sub_cancel])

lemma history (o)(he:Brole o):
   u.D.W (e.v.c o l)+u.D.D e.a ≤ u.D.W e.a ∧ u.D.D (e.v.c o l)=2*u.D.D e.a:=by
   let q:=e.c; have ht:l+1<Age.L e.v.m:= hA.step ▸ hA.east.s2
   change u.D.W _+u.D.D (e.v.c 1 e.i) ≤ u.D.W (e.v.c 1 e.i)∧ u.D.D _=2*u.D.D (e.v.c 1 e.i)
   rw [Stone.W,Stone.W,Stone.D,Stone.D,hA.step]
   refine ⟨Age.oldpay ht (by decide:Brole 1) he,?_⟩
   simp only [slackT,he, (by decide:Brole 1),ite_true, gap_step ht]

lemma legacy (j)(hj:j<q.u0.n): (q.s j).Good:=by
    let R:= e.v.β l
    let c:=(q.s j).ray
    let s:= c.t
    have hf:s.sunset=(Was.atom 0,1,0):=rfl
    have hg:s.1=e.tideC true (0,0):=rfl
    have hp:=hA.east.majors
    have hh:= heap hA.east (word e j) hA.target (some (0,x)) (fun _=> q.pulse j)
    have h1:u.D.W 0+u.D.D e.a  ≤ u.D.W e.a:= Stone.zeroR e.v 1 e.i
    have ht:x ≤ u.n:= Nat.le_of_lt_succ (mem_range.1 hA.target)
    have hx:Was.Flight u.r u.x 0 0 x x:= by simp [Was.Flight,ht]
    apply cam hA.east
    apply Era.basePort hh rfl h1 (Nat.zero_le _) (Nat.add_le_add_right hp.book.coinbook 1)
    · intro b i hs
      change some ((0,x):Rill.History)=some (b,i)↔_
      unfold Was.Flight; change _↔ b<Era.budget u.r ∧ _
      constructor
      · intro he; have h5:= Option.some.inj he; have h2:b=0:= (congrArg Prod.fst h5).symm; have h3:i=x:=(congrArg Prod.snd h5).symm
        rw [h2,h3]; exact ⟨Nat.zero_lt_succ _,hx⟩
      rintro ⟨_,hl,hu,h⟩; simp only [ite_true] at h; exact congrArg some (Prod.ext h.2.symm h.1)
    intro b i hs ha
    change some ((0,x):Rill.History)=some _ at ha
    simp only [Option.some.injEq,Prod.mk.injEq] at ha
    obtain ⟨hh2,hh3⟩:=ha; subst i; subst b
    have hz:s.U=(R.visN,j):=by
       change (Crest.pastC e.c 4,j)=_
       rw [hA.teeth 4]
    have h2 :l<Age.L e.v.m:=by have h:=hA.east.s2; rw [hA.step] at h; omega
    have ho:= hp.frontP hA.east.s1 l h2
    have he:=hA.history 4 (by decide)
    apply Partner.leaf
    · change s.U.1≠0
      rw [hz]; exact Age.cpos _
    · change u.wick0.Veil u.torch s.U.1; rw [hz]; exact hA.east.pays _ ho.path he.1
    · exact hA.east.terra hg hf
    · change u.D.W s.U.1+_ ≤ _; rw [hz]; exact he.1
    · change u.D.D s.U.1 ≤ _; rw [hz, show R.visN=e.v.c 4 l from rfl,he.2]; exact le_rfl
    · change u.eye.Flora u.torch.p s.U.1 s.U.2 x (q.pulse j)
      rw [hz]
      have hh':= hA.insight.found.road j (ho.awake (ho.size0 j (show j < e.v.Snum l from hA.insight.card0 ▸ hj)))
      unfold pulse
      by_cases hm:q.u0.live j
      · rw [ite_eq_left hm]; rw [ite_eq_right (show q.u0.tag j≠0 from hm)] at hh'; exact hh'
      rw [ite_eq_right hm]; rwa [ite_eq_left (show q.u0.tag j=0 from by
                        unfold Depot.live at hm;exact not_not.1 hm)] at hh'
    intro i y hy; change (if q.u0.live j then _ else none)=some _ at hy
    split at hy
    · next h=> simp only [Option.some.injEq, Prod.mk.injEq] at hy
               have ht:y∈e.v.S1:= hA.insight.dst ▸ hy.2 ▸ hA.insight.solid.into j h
               exact Era.orn hp.chart h1 (Fabric.Good.n1 hp.chart hp.good ht) hf
    contradiction

lemma harvested (j):
    (q.s j).ray.outR=(if q.u0.live j then some (1,q.u0.pos j) else none):=by
    let s:=(q.s j).ray.t
    have hc:s.1=e.tideC true (0,0):=rfl
    change collect s u.n x _ _=_
    unfold collect
    by_cases hi:q.u0.live j
    · have hp: x∈e.v.S0:=by by_contra! hz; exact hA.insight.kill hz j hi
      have hf:s.frontC u.n x=true:= (hA.east.city true (0,0) hc x).mpr ⟨hp,e.parked true true _⟩
      have he:q.u0.pos j∈e.v.S1:= hA.insight.dst ▸ hA.insight.solid.into j hi
      let y:=q.u0.pos j
      have ht:s.windC y=y:=by change 1*y+0=y; omega
      have h1:s.windC y∈e.zone true:= by rw [ht];exact he
      have h2 := h1
      rw [e.zeda] at h1
      have hv:s.finalC u.n y=true:= ((Lo.ending (e := e)) true (0,0) hc y (mem_filter.1 h1).1).mpr
                                                 ⟨h2,e.parked true false _⟩
      rw [ite_eq_left hi,ite_eq_left hf]; change (match q.pulse j with|none=>none|some (a,y1)=> if s.finalC u.n y1 then some ((0+1,s.windC y1):Rill.History) else none)=some (1,y)
      unfold pulse; rw [ite_eq_left hi]; change (if s.finalC u.n y then _ else none)=_
      rw [ite_eq_left hv,ht]
    have he:q.pulse j=none:=ite_eq_right hi
    rw [ite_eq_right hi]
    split; change (match q.pulse j with|none=>none|some (a,y1)=> if s.finalC u.n y1 then some ((0+1,s.windC y1):Rill.History) else none)=none; rw [he]
    rfl

end Prints
end Ink
end Recent
end
end ExactDerandomization.Chron.Moon

end

section

namespace ExactDerandomization.Chron.Moon
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Was
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable (e:ExactDerandomization.Chron.Moon u)
namespace Local
def ready(e:ExactDerandomization.Chron.Moon u):Prop:=e.i=0∧e.v.t.tag=.chip ∧ e.v.t.i=0
abbrev seed (i:ℕ):= Crest.newelf u.n e.v.t.a (e.tideC true (0,0)) i

def interim (x i:ℕ): Stars:= by
   let h(z:Rill.History):Prop:=Flight u.r u.x (i+1) z.1 x z.2
   exact if v:∃ z,h z then some (Classical.choose v) else none
abbrev ucanon (x i:ℕ):Nest u:= e.stash (seed e i) x (interim (u:=u) x i) (fun p=>some (0,p))
lemma knows(x i b y:ℕ):
    interim (u:=u) x i=some (b,y) ↔ Flight u.r u.x (i+1) b x y:=by
   unfold interim; dsimp only
   split
   · rename_i h
     let k:= Classical.choose h
     have he: Flight u.r u.x (i+1) k.1 x k.2:= Classical.choose_spec h
     refine ⟨fun e=>?_,fun e=>?_⟩
     · change some k=some _ at e; rw [Option.some.inj e] at he; exact he
     obtain ⟨hk,hz⟩:=fly_pair _ he e
     change some k=some (b,y)
     rw [← hk,←hz]
   next h=> exact iff_of_false (by simp) (fun v=>h ⟨(b,y),v⟩)
lemma seekRead (e:ExactDerandomization.Chron.Moon u) {j}(he:ready e) (h:j<2):
       began e.c (firstG j) := by
   obtain ⟨hi,h1,h2⟩:=he
   refine ⟨rfl,hi,?_,h2,h⟩
   change (shaped e.v.t.tag).1=0
   rw [h1]; rfl
lemma flair (e:ExactDerandomization.Chron.Moon u){j} (he:ready e)(h:j<2):
     Lily.arms u.r u.x (e.a,enc (firstG j))=seed e j:=by
    rw [armleg _ (Or.inr (Or.inr (seekRead e he h)))]; rfl

abbrev trueW(x y:ℕ):ℝ:=(Aqua.sbase u.n e.v.t.a).v*(u.r.P.edge u.x x y:ℝ)
def sell (x y:ℕ):Coinage:=
     let s:= (ucanon e x y).ray.outR
     ⟨s, if iris s=0 then 0 else (trueW e x (pointE s),0)⟩

namespace Ready
variable {e:ExactDerandomization.Chron.Moon u}(h0:e.Lo)(he:ready e)
include h0 he
omit h0 in
lemma home0 : (u.plotM.stage e.v.t.i).S=u.r.P.dom u.x:=by rw [he.2.2]; rfl
lemma truthX (x y:ℕ) : (ashes e.v true).base x y=trueW e x y:=by
    let a:= e.v.t.a
    have hh:2^a≤u.n:=u.plotM.fits h0.majors.chart.sc (h0.zenith.2 true)
    rw [trueW,Aqua.seed _ hh]
    unfold ashes Quest.start
    rw [he.2.1,he.2.2]
    unfold Quest.question
    simp only [he.2.1, he.2.2]
    change (((u.r.P.S u.x x y):ℚ):ℝ)/rate a=_
    unfold Base.Source.S
    push_cast
    change (u.r.P.edge u.x x y:ℝ)/2 / _=_
    ring
omit h0 he in
lemma extentA (e:ExactDerandomization.Chron.Moon u)(l:e.Lo) (ht:e.i=0):
       2*e.v.t.a ≤ e.v.m ∧ e.v.m ≤ 2*e.d:=by
    have h1:=l.s1
    unfold Fabric.activeR onQ at h1
    have he:= of_decide_eq_true h1; change 2*e.v.t.a+_+_ < _ at he
    refine ⟨by omega,?_⟩
    unfold ExactDerandomization.Chron.Moon.d; unfold gap Age.L
    rw [ht,show e.v.m.log2+1-1-0=e.v.m.log2 by omega]
    have ha : e.v.m < 2^(e.v.m.log2+1):=Nat.lt_log2_self; rw [pow_succ] at ha;omega
lemma cash :
   |(Aqua.sbase u.n e.v.t.a).v| ≤ massB (e.p.prism-1) (u.D.D e.a):=by
    let a:=e.v.t.a
    have hh:2^a≤u.n:=u.plotM.fits h0.majors.chart.sc (h0.zenith.2 true)
    rw [Aqua.seed a hh,e.baseD]
    unfold rate
    let d:= e.d
    have hz :4*a ≤ (e.p.prism-1)*d:=by
      have hh:=extentA e h0 he.1
      have hv:20 ≤ e.p.prism:=by unfold MintV.prism; omega
      have ht:4  ≤ e.p.prism-1:=by omega
      exact le_trans (show 4*a  ≤ 4*d by unfold d a; omega) (Nat.mul_le_mul_right d ht)
    refine le_trans ?_ (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) hz)
    rw [abs_of_pos (by positivity)]
    rw [←inv_pow,inv_inv,show 4*a=a*4 by omega,pow_mul]; nlinarith [show 0 ≤ ((2:ℝ)^a)^4 by positivity]
lemma minted (x y:ℕ):
    |trueW e x y|≤ massB e.p.prism (gap e.v.m e.i):=by
    have hp := h0.s2
    let d:= e.d
    have hs:1 ≤ d:=gap_pos ..
    let q:=e.p.prism-1
    have hi:q+1=e.p.prism:=by unfold q MintV.prism; omega
    have hz:0  ≤  massB q d:= (mass0 ..).le
    have ht : (2:ℝ)  ≤ massB 1 d:=by norm_num [massB]; exact_mod_cast le_trans (show 2≤ (d+1) by omega) (exp_big d)
    let W:=u.r.P.edge u.x x y; have hw: W  ≤  2:=by unfold W Base.Source.edge; grind
    unfold trueW; rw [abs_mul]
    change _  ≤ massB e.p.prism d
    rw [← hi,mass_mul]
    apply mul_le_mul
    · change _ ≤ massB _ e.d; rw [←e.baseD]; exact cash h0 he
    · rw [abs_of_nonneg (by positivity)]; apply le_trans _ ht; exact_mod_cast hw
    · exact abs_nonneg _
    exact hz

omit he in
lemma illustrious {x:ℕ}(hx:x∈u.D.P){i:ℕ}(hi:i<2): (ucanon e x i).Good:=by
    let s:=ucanon e x i; let q:=s.ray.t
    have hf:q.sunset=(atom 0,1,0):=rfl
    have hp:=h0.majors
    have hh:= heap h0 (seed e i) hx (interim (u:=u) x i) (fun j=> (some (0,j):Stars))
    have h1:u.D.W 0+u.D.D e.a  ≤ u.D.W e.a:= Stone.zeroR ..
    apply cam h0
    apply Era.basePort hh rfl h1 (le_trans (show i+1 ≤ bootC u.r by unfold bootC; omega) hp.book.coinbook)
                                                             (Nat.add_le_add_right hp.book.coinbook 1)
    · intro b j hs; rw [show (s.ray.entrance=some (b,j)) ↔ _ from knows x i b j]
      refine ⟨fun he=>?_,And.right⟩
      refine ⟨?_,he⟩
      have hL:=he
      unfold Flight at hL
      simp only [Nat.add_one_ne_zero,show (i+1=1∨i+1=2) from by omega,ite_true] at hL
      have ht:air u.r u.x x j:=hL.2.2.1
      have hz:= (passage _ _ _ _ ht).2; change b<Era.budget u.r
      have hm:b=bright u.r u.x false j x+1:= hL.2.2.2.2
      unfold Era.budget bootC;omega
    intro b j hs ho
    have hT:= (knows x i b j).1 ho; apply Partner.soil rfl; apply Era.orn h0.majors.chart h1 _ hf
    exact mem_range.2 (Nat.lt_succ_of_le hT.2.1)

lemma kindness {x i j:ℕ}(_:x∈u.D.P)(hi:i<2){k} (he1:(sell e x i).verge=some (k,j)):
    x∈ e.v.S0∧ j∈ e.v.S1 ∧ k≠0 ∧ Flight u.r u.x (i+1) (k-1) x j:=by
    let s:=(ucanon e x i).ray.t
    have hf:s.1=e.tideC true (0,0):=rfl
    change (ucanon e x i).ray.outR=some (k,j) at he1
    obtain ⟨hh,b,m,a,n,hr,ht,rfl,hc,hL⟩:=spark he1
    have hn:n=m:=by change some ((0,m):Rill.History)=some _ at ht; exact (congrArg Prod.snd (Option.some.inj ht)).symm
    subst n
    have hk:s.windC m=m:=by change 1*m+0=m; omega
    change j=s.windC m at hc; rw [hk] at hc; subst j
    have hv:=(knows x i b m).1 hr
    have hh0:=hv
    unfold Flight at hh0; simp only [Nat.add_one_ne_zero,show (i+1=1∨i+1=2) from by omega,ite_true] at hh0
    have hG:= (birth u.r u.x _ _ hh0.2.2.1).2
    have he0:= (((Lo.ending (e := e)) true (0,0) hf m (by rw [hk,home0 he]; exact hG)).mp hL).1
    rw [hk] at he0
    exact ⟨((h0.city true (0,0) hf x).mp hh).1,he0,(by omega),by simpa using hv⟩

lemma crystal {x:ℕ}(hx:x∈u.D.P){i:ℕ}(hi:i<2):
    Spend e x (enc (firstG i)) (sell e x i) ∧
             ht (sell e x i).dye ≤ massB e.p.prism e.d:=by
    let s:=ucanon e x i
    let a:=sell e x i
    have hs:=illustrious h0 hx hi
    have hY :title s ≠0 →∃ k j,title s=k∧s.ray.outR=some (k,j):=by
       intro h; cases hh:s.ray.outR
       · exact False.elim (h (by unfold title; rw [hh];rfl))
       next z=> obtain ⟨k,j⟩:=z; exact ⟨k,j,by unfold title; rw [hh];rfl,rfl⟩
    have hz:title s=0→a.dye=0:=by
       intro h; exact ite_eq_left h
    have hp {k j}(h:title s=k)(hf:s.ray.outR=some (k,j)):
        a.dye=(trueW e x j,0):=by
         have hh:= kindness h0 he hx hi (show (sell e x i).verge = _ from hf)
         change (if title s=0 then _ else _)=_
         rw [ite_eq_right (h.symm ▸ hh.2.2.1),hf]
         rfl
    have hn : ht a.dye ≤ massB e.p.prism e.d:=by
       by_cases hh:title s=0
       · rw [hz hh,show ht (0:Pt)=0 by simp [Buf.ht]]; positivity
       obtain ⟨k,j,h,hf⟩:=hY hh
       rw [hp h hf]
       simpa [Buf.ht] using minted h0 he x j
    refine ⟨?_,hn⟩
    apply cold e s h0 (y:=a.dye) (b:=_) (by rfl) hs (flair e he hi) _ hz
    · intro h
      obtain ⟨k,j,h,hf⟩:=hY h; rw [hf]
      have hh:= kindness h0 he hx hi (show (sell e x i).verge = _ from hf)
      exact ⟨hh.1,hh.2.1⟩
    intro c
    by_cases hh:title s=0
    · rw [hz hh]; cases c <;> exact hs.torn hh ..
    obtain ⟨k,j,h,hf⟩:=hY hh
    have hq:=minted h0 he x j
    rw [hp h hf]; cases c
    · exact hs.youngNo hh (by show 1≠(0:ℕ);omega) Bool.noConfusion
    apply hs.youngYes hh (by show 1≠(0:ℕ);omega) rfl _ (fun h=>False.elim (h rfl))
                  (Cambria.Rime.Nest.Good.shekel h0.majors.book.saving rfl (e.baseD.symm ▸ hq))
    intro _
    have hp := kindness h0 he hx hi (show (sell e x i).verge = _ from hf)
    have hv:title s=k-1+1:=by omega
    rw [hv]
    apply hs.lecture rfl hp.2.2.2
    apply (cash h0 he).trans; exact mass_mono (show e.p.prism-1 ≤ e.p.prism by omega) _
end Ready
end Local
end
end ExactDerandomization.Chron.Moon

end

section

namespace ExactDerandomization.Chron
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Quest ExactDerandomization.Chron.Moon.Weather
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Moon
variable (e:ExactDerandomization.Chron.Moon u)

def basepart (x y:ℕ):Pt:=
    if Local.ready e∧ x∈e.v.S0 ∧ y∈e.v.S1 then ((ashes e.v true).base x y,0) else 0
lemma basef (b:Bool)(x y) :
    (if x∈e.v.S0 ∧ y∈ e.zone b ∧ e.i=0 then (ashes e.v b).base x y else 0)=Reed.sideq (e.basepart x y) b:=by
   cases b
   · unfold basepart Reed.sideq ashes companion
     simp; split<;>rfl
   unfold basepart
   by_cases h:x∈e.v.S0 ∧ y∈e.zone true∧e.i=0
   · rw [ite_eq_left h]
     split
     · rfl
     next ht=>
       change _ = 0; unfold ashes
       simp only [ite_true]
       unfold Quest.start
       cases he:e.v.t.tag <;> first | rfl| skip
       next =>
        cases hs:e.v.t.i
        · exact (ht ⟨⟨h.2.2,he,hs⟩,h.1,h.2.1⟩).elim
        rfl
   rw [ite_eq_right h, ite_eq_right (fun h0=> h ⟨h0.2.1,h0.2.2,h0.1.1⟩)]
   rfl

namespace Local.Ready
variable {e:ExactDerandomization.Chron.Moon u}(h0:e.Lo)(he:Local.ready e)
include h0 he
omit he in
lemma remits {x i y:ℕ} (_:x∈u.D.P) (_:i<2)(hh:x∈e.v.S0)(hy:y∈e.v.S1){b:ℕ}
    (h:Was.Flight u.r u.x (i+1) b x y):(sell e x i).verge=some (b+1,y):=by
   let s:=(ucanon e x i).ray.t
   have hf:s.1=e.tideC true (0,0):=rfl
   have hp:s.frontC u.n x=true:= (h0.city true (0,0) hf x).mpr ⟨hh,e.parked ..⟩
   have hs:s.windC y=y:=by change 1*y+0=y;omega
   have hk:s.windC y∈e.zone true:=hs.symm ▸ hy
   have hc:=hk; rw [e.zeda] at hc
   have hz:s.finalC u.n y=true:= ((Lo.ending (e := e)) true (0,0) hf _ (mem_filter.1 hc).1).mpr ⟨hk,e.parked ..⟩
   change collect s u.n x (interim _ i) (fun p=>some (0,p))=_
   unfold collect; rw [ite_eq_left hp,(knows ..).2 h]
   dsimp only; rw [ite_eq_left hz,hs]
lemma taunted {x y j:ℕ}(hx:x∈u.D.P)(hj:j<2) :
    ((sell e x j).fired∧(sell e x j).p=y) ↔
       x∈e.v.S0∧y∈e.v.S1∧∃ b,Was.Flight u.r u.x (j+1) b x y:=by
    let s:=sell e x j
    constructor
    · intro h; change s.fired ∧ s.p=y at h
      have hm:= ((crystal h0 he hx hj).1).briefly
      rw [ite_eq_right h.1,show (sell e x j).p=y from h.2] at hm
      obtain ⟨h1,h2,_,hp⟩:=kindness h0 he hx hj hm
      exact ⟨h1,h2,_,hp⟩
    rintro ⟨h1,h2,b,ha⟩; have hc:= remits h0 hx hj h1 h2 ha
    unfold Coinage.fired Coinage.i Coinage.p; rw [hc]
    exact ⟨Nat.succ_ne_zero _,rfl⟩
lemma total {x:ℕ}(hx:x∈u.D.P)(y):
     ∑ i∈range 2,(sell e x i).pigment y=e.basepart x y:=by
    by_cases hm:x∈e.v.S0 ∧ y∈e.v.S1
    · rw [basepart,ite_eq_left ⟨he,hm⟩,truthX h0 he]
      let p:= u.r.P
      let i:=Was.bright u.r u.x true x y
      have hc: x ≤ u.n∧ y ≤ u.n:=by
         have ht:= (Fabric.Good.n1 h0.majors.chart h0.majors.good hm.2)
         exact ⟨Nat.le_of_lt_succ (mem_range.1 hx),Nat.le_of_lt_succ (mem_range.1 ht)⟩
      by_cases hs:Was.air u.r u.x x y
      · have ht:i<2:= (Was.passage u.r u.x x y hs).1
        rw [sum_eq_single i]
        · have hv:Was.Flight u.r u.x (i+1) (Was.bright u.r u.x false y x +1) x y:=by
                   unfold Was.Flight
                   refine ⟨hc.1,hc.2,?_⟩
                   rw [ite_eq_right (Nat.succ_ne_zero _),ite_eq_left (by omega)]
                   exact ⟨hs,rfl,rfl⟩
          have hg:= (taunted h0 he hx ht (y:=y)).mpr ⟨hm.1,hm.2,_,hv⟩
          unfold Coinage.pigment; rw [ite_eq_left hg]
          change (if _ then _ else _)=_
          change iris (ucanon e x i).ray.outR≠0∧pointE (ucanon e x i).ray.outR=y at hg; rw [ite_eq_right hg.1,hg.2]
        · intro j hj hz
          apply ite_eq_right; intro h
          replace hj:=mem_range.1 hj
          obtain ⟨hx,hy,a,he⟩:= (taunted h0 he hx hj).mp h
          unfold Was.Flight at he
          rw [ite_eq_right (Nat.succ_ne_zero _),ite_eq_left (by omega)] at he
          exact hz (by have hm:= he.2.2.2.1; change j+1=i+1 at hm; omega)
        intro he; exact False.elim (he (mem_range.2 ht))
      rw [show trueW e x y=0 from ?_]
      · apply sum_eq_zero; intro j hj; replace hj:=mem_range.1 hj
        apply ite_eq_right; intro hm
        obtain ⟨_,_,a,he⟩:= (taunted h0 he hx hj).mp hm
        unfold Was.Flight at he
        rw [ite_eq_right (Nat.succ_ne_zero _),ite_eq_left (by omega)] at he; exact hs he.2.2.1
      unfold Was.air at hs; unfold trueW; rw [show _=0 from Nat.eq_zero_of_not_pos hs]; simp
    rw [basepart,ite_eq_right (fun h=>hm h.2)]
    apply sum_eq_zero; intro i hi; apply ite_eq_right; intro h
    obtain ⟨hp,hx,_⟩:= (taunted h0 he hx (mem_range.1 hi)).1 h
    exact hm ⟨hp,hx⟩
end Local.Ready

lemma rains0 (b:Bool)(x y:ℕ):
   let _:= (ashes e.v b)
   Reed.sideq ((e.v.marathon x).inc e.i y) b=
       Reed.sideq (basepart e x y) b + ∑ i∈area e.v b e.i,Reed.sideq
                                                      (prize (⟨b,i⟩:Weather e) x y) b :=by
    intro q
    let d:= gridR e.v b
    let P:=area e.v b e.i
    have hz:Reed.sideq ((e.v.marathon x).inc e.i y) b=q.bundle e.sE d e.i e.v.dye x y:= by
          cases b <;> rfl
    have hl(x:ℝ):Reed.sideq (Weather.Pale.boltQ b x) b=x:=by cases b<;>rfl
    have hb:Reed.sideq 0 b=0:=by cases b <;> rfl
    have hp: ∀ i:Census.Arc, Reed.sideq (prize (⟨b,i⟩:Weather e) x y) b =
                 if x∈e.v.S0 ∧ y∈ e.zone b then Census.wind e.sE q d e.v.dye x y i else 0:=by
       intro i; unfold prize; split
       · exact hl _
       exact hb
    rw [hz,← basef e b]
    simp_rw [hp]
    unfold Flame.bundle
    rw [Census.humid]
    by_cases h:x∈ e.v.S0∧y∈ e.zone b
    · have hr:x∈src d.S d.u e.v.dye∧y∈dst d.S d.a e.v.dye:=by cases b <;> exact h
      have h1:x∈e.v.S0:=h.1; have h2:=h.2
      rw [ite_eq_left hr]; simp only [h1,h2,true_and,ite_true]
      exact add_comm _ _
    have hh : ¬(x∈src d.S d.u e.v.dye∧y∈dst d.S d.a e.v.dye):=by cases b <;> exact h
    have he:¬(x∈e.v.S0∧y∈e.zone b ∧ e.i=0):=fun p=> h ⟨p.1,p.2.1⟩
    simp only [ite_eq_right h,ite_eq_right hh,ite_eq_right he,sum_const_zero,add_zero]
end Moon
end
end ExactDerandomization.Chron

end

section

namespace ExactDerandomization.Chron.Moon
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Fabric Stem
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable (e:ExactDerandomization.Chron.Moon u)

namespace Recent.Ink
variable {e:ExactDerandomization.Chron.Moon u} {l x:ℕ} (q:Ink e l x)
def diffq (j:ℕ):Pt:= q.u0.qpoint j-line q.u0.y.base
def turns (j:ℕ):Coinage:=
       ⟨(q.s j).ray.outR,q.diffq j⟩
namespace Prints
variable {q:Ink e l x}(hA:q.Prints)
include hA

lemma existent (j:ℕ): title (q.s j)=(if q.u0.live j then 1 else 0):=by rw [title,hA.harvested]; split <;> rfl

lemma teach (j:ℕ)(hj:j<q.u0.n):Spend e x (enc (rear0 j)) (q.turns j):=by
    let s:=q.s j
    let m:=e.i
    let p:=q.u0
    let u0:=e.p
    let v:=s.diploma
    let t:=2*u0.sealR
    have h1:=hA.east
    have hr:=hA.history 3 (by decide)
    let w:= e.v.β l
    have hx:= hA.east.majors.frontP hA.east.s1 l (by have :=h1.s2;have:=hA.step;omega)
    have he:=hx.awake (hx.size0 _ (hA.insight.card0 ▸ hj))
    have hg:w.dataN=s.addr2.1:=(hA.teeth 3).symm
    have hn:s.addr2.2=j:=rfl
    have hS:s.Good:=hA.legacy j hj
    have hI:= hA.insight
    have hd:u.D.D w.dataN= 2*u.D.D s.a:= hr.2
    have hp:e.p.sealR*u.D.D w.dataN=t*u.D.D s.a:=by rw [hd]; unfold t u0;ring
    let b:Pt:=q.diffq j
    have hz:title s=0→b=0:=by
       intro h
       have hm:¬q.u0.live j:=by
            rw [show title s=_ from hA.existent j] at h
            intro ht; rw [ite_eq_left ht] at h; omega
       unfold b diffq Depot.qpoint; simp [hm]
    apply e.cold s hA.east (b:=_) (by rfl) hS (hA.board j hj) _ hz
    · intro h
      have hl:q.u0.live j:=by
           rw [show title s=_ from hA.existent j] at h
           split at h
           · assumption
           contradiction
      have hz:x∈e.v.S0:=by by_contra! hs; exact hA.insight.kill hs j hl
      refine ⟨hz,?_⟩
      change pointE (q.s j).ray.outR∈ _
      rw [hA.harvested,ite_eq_left hl]
      exact hA.insight.dst ▸ hA.insight.solid.into j hl
    intro B

    by_cases hb:title s=0
    · rw [hz hb,show Reed.sideq 0 B=0 by cases B <;> rfl]
      exact hS.torn hb _
    have ht(B:Bool) : s.VoiceS s.ray.x (s.addr3 (if B then 1 else 2))
            (t*u.D.D s.a) (Reed.sideq (q.u0.qpoint j) B):=by
       refine ⟨w.dataN,hole (if B then 1 else 2) j,by rw [addr3,hg,hn],hr.1,?_⟩
       exact hp ▸ (hI.hue B).ready _ he
    have hZ:s.VoiceS s.ray.x (hole s.addr2.1 (hole 5 0))
          (t*u.D.D s.a) q.u0.y.base:= by rw [←hg]; exact ⟨w.dataN,_,rfl,hr.1,hp ▸ hI.at0⟩
    apply hS.partOld hb rfl (hS.biast _ _ B ht hZ)
    let C:= massB t (u.D.D s.a)
    have hw0(f:ℕ)(A:ℝ)(hr:s.VoiceS s.ray.x f (t*u.D.D s.a) A):|A|≤C:=by
        obtain ⟨b,i,ht,hc,w,hz,hq⟩:=hr

        have hv:= hz.1
        rw [abs_div,abs_of_pos (show 0 < (2:ℝ)^(t*u.D.D s.a) by positivity),div_le_one (show 0 < (2:ℝ)^(t*u.D.D s.a) by positivity)] at hv; exact hv
    let d:=u.D.D s.a
    have hh: |Reed.sideq b B| ≤ C+C:=by
          have h:=hw0 _ _ (ht B)
          have hx:=hw0 _ _ hZ
          unfold b diffq
          cases B
          · change |(q.u0.qpoint j).2-0|  ≤  _
            rw [sub_zero]; change |(q.u0.qpoint j).2|≤ C at h; linarith [abs_nonneg (q.u0.qpoint j).2]
          change |(q.u0.qpoint j).1-q.u0.y.base| ≤ _
          exact (abs_sub ..).trans (add_le_add h hx)
    apply hh.trans; change C+C ≤ massB (3*u0.sealR) d
    rw [show 3*u0.sealR=t+u0.sealR by unfold t; ring, mass_mul]
    change C+C ≤ C*massB u0.sealR d
    have hl :16 ≤ u0.roofX d:= u0.fluc h1.majors.book.saving.tested hS.primary.well.1
    nlinarith [(mass0 t d)]

lemma total (j:ℕ) (hj:j∈e.v.S1):
    ∑ i∈range q.u0.n,(q.turns i).pigment j=q.u0.y.ts j-line q.u0.y.base:=by
   let s:=q.u0
   have he (i:ℕ) :
     (q.turns i).pigment j=if s.live i∧ s.pos i=j then s.y.ts j-line s.y.base else 0:=by
         unfold turns
         rw [hA.harvested]
         by_cases hp:s.live i
         · rw [ite_eq_left hp]
           have hg:i=i:=rfl
           by_cases hk:s.pos i=j
           · rw [ite_eq_left ⟨hp,hk⟩]; rw [Coinage.pigment, ite_eq_left (by change 1 ≠ (0:ℕ) ∧ q.u0.pos i=j; exact ⟨by decide,hk⟩)]
             unfold diffq Depot.qpoint; rw [ite_eq_left hp,hk]
           rw [ite_eq_right (fun h=>hk h.2)]
           exact ite_eq_right fun h=>hk h.2
         rw [ite_eq_right hp,ite_eq_right (fun h=>hp h.1)]
         exact ite_eq_right fun h=>h.1 rfl
   have hp:j∈s.S:=hA.insight.dst ▸ hj
   by_cases hl:∃ i,s.live i∧ s.pos i=j
   · obtain ⟨i,hi,hj'⟩:=hl
     rw [sum_eq_single i]
     · rw [he,ite_eq_left ⟨hi,hj'⟩]
     · intro b hb ht
       rw [he]; exact ite_eq_right fun h=>ht (hA.insight.solid.uniq b i h.1 hi (h.2.trans hj'.symm))
     intro h; exact False.elim (h (mem_range.mpr (hA.insight.solid.card0 i hi)))
   have hf : s.y.ts j=line s.y.base:=hA.insight.solid.off j hp (fun i hi e=>hl ⟨i,hi,e⟩)
   change _=s.y.ts j-line s.y.base
   rw [hf,sub_self]; apply sum_eq_zero
   intro i _; rw [he,ite_eq_right (fun h=>hl ⟨_,h⟩)]

end Prints
end Recent.Ink
end
end ExactDerandomization.Chron.Moon

end

section

namespace ExactDerandomization.Chron
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Quest ExactDerandomization.Chron.Moon.Weather
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Moon

structure Fields where
    T:Finset Seed
    f: Seed → Coinage
namespace Fields
variable (l:Fields)
def rain(y:ℕ):Pt:= ∑ i∈l.T,(l.f i).pigment y
def meet (p:Fields):Fields:=⟨l.T∪p.T,fun x=> if x∈l.T then l.f x else p.f x⟩
def empty:Fields:=⟨∅,fun _=>Coinage.dies⟩
lemma flooded (p:Fields)(he:Disjoint l.T p.T)(y):
   (l.meet p).rain y=l.rain y+p.rain y:=by
   unfold meet rain; dsimp only; rw [sum_union he]
   congr 1
   · exact sum_congr rfl fun i hi=>congrArg (fun t:Coinage=> t.pigment y) (ite_eq_left hi)
   exact sum_congr rfl fun i hi=>congrArg (fun t:Coinage=> t.pigment y) (ite_eq_right (fun ht=>Finset.disjoint_left.1 he ht hi))

variable (e:Chron.Moon u)(x:ℕ)
def fine : Prop:=∀ i∈l.T,ht (l.f i).dye ≤ massB e.p.prism e.d
structure Good (l:Fields)(P:Seed → Prop)(e:Chron.Moon u)(x:ℕ): Prop where
    mem(i):i∈l.T ↔ P i
    sound:∀ i∈l.T,e.Spend x (enc i) (l.f i)
namespace Good
variable {e:Chron.Moon u} {x:ℕ} {l t:Fields}{p f : Seed → Prop}
lemma fused (h:l.Good p e x) (he:t.Good f e x)(hh:Disjoint l.T t.T):
     (meet l t).Good (fun i=>p i∨ f i) e x:=by
   constructor
   · intro i; simp only [meet,mem_union,h.mem,he.mem]
   intro i hi; obtain hx|hx:=mem_union.1 hi
   · change e.Spend _ _ (if i∈l.T then _ else _); rw [ite_eq_left hx];exact h.sound _ hx
   change e.Spend _ _ (if i∈l.T then _ else _)
   rw [ite_eq_right (fun ht=>Finset.disjoint_left.1 hh ht hx)]; exact he.sound _ hx
lemma apart (h:l.Good p e x) (he:t.Good f e x)(hh:∀ i,p i→¬f i) :Disjoint l.T t.T:=
    Finset.disjoint_left.2 fun {i} hp hf=>hh _ ((h.mem i).mp hp) ((he.mem i).mp hf)
lemma fairM (h:l.fine e)(ht:t.fine e): (meet l t).fine e:=by
     intro i hi
     unfold meet; dsimp only; split
     · exact h _ (by assumption)
     next hc=>exact ht i ((mem_union.1 hi).resolve_left hc)
end Good

variable {α:Type}

def meadow (S:Finset α)(f:α → Seed)(g:α → Coinage):Fields:=
    ⟨S.image f,fun i=>if h:∃ j∈S,f j=i then g (Classical.choose h) else Coinage.dies⟩
lemma meadowed {S:Finset α}{f:α → Seed}{v:α}(g:α → Coinage)(h:Set.InjOn f S)(he:v∈S):
    (meadow S f g).f (f v)=g v:=by
    unfold meadow; dsimp only; have hz:∃ j∈S,f j=f v:=⟨_,he,rfl⟩
    rw [dite_eq_left hz]; exact congrArg _ (h (Classical.choose_spec hz).1 he (Classical.choose_spec hz).2)
lemma parkS {S:Finset α}{f:α → Seed}(g:α → Coinage)(h:Set.InjOn f S)(y): (meadow S f g).rain y=
              ∑ j∈S,(g j).pigment y:=by
   unfold rain; rw [show (meadow S f g).T=S.image f from rfl]
   rw [sum_image (show ∀ i∈S,∀ j∈S, f i=f j → i=j from fun _ h0 _ h1 he=>h h0 h1 he)]
   exact sum_congr rfl fun i hi=>by rw [meadowed _ h hi]
lemma floraC {S:Finset α}{f:α → Seed}{g:α → Coinage}(h:Set.InjOn f S){k:Seed → Prop}
   (he:∀ i,i∈(S.image f) ↔ k i )(hm:∀ i∈S, e.Spend x (enc (f i)) (g i)):
    (meadow S f g).Good k e x:=by
   refine ⟨he,?_⟩
   intro i hi; obtain ⟨t,hb,rfl⟩:=mem_image.1 hi; rw [meadowed g h hb]; exact hm _ hb
lemma flushed {S:Finset α}{f:α → Seed}{g:α → Coinage}(h:Set.InjOn f S)(hp:∀ i∈S,ht (g i).dye ≤ massB e.p.prism e.d):
   (meadow S f g).fine e:=by
     intro i hi; obtain ⟨i,he,rfl⟩:=mem_image.1 hi; rw [meadowed g h he]; exact hp _ he
end Fields

variable (e:Chron.Moon u)
abbrev signE (b:Bool)(p:Seed):Prop:=atmos u.w0 e.c p ∧ p.fog.first0=b
structure Spirit(x:ℕ)(l:Fields)(b:Bool) : Prop where
    gear:l.Good (e.signE b) e x
    fees:l.fine e
    tell :∀ y,l.rain y=∑ j∈area e.v b e.i,prize (⟨b,j⟩: Weather e) x y

namespace Spirit
open Fields
variable {e:Chron.Moon u}
lemma lamp (hc:Weather.Crude e)(b:Bool){x:ℕ}(hp:x∈u.D.P) :
    ∃ t:Fields, Spirit e x t b:=by
   have hh(r:Arc):∃ f, r∈area e.v b e.i→Carnival (⟨b,r⟩:Weather e) x f := by
       by_cases hr:r∈area e.v b e.i
       · obtain ⟨f,h⟩:=rally (c:=⟨b,r⟩) ⟨hc.lane,hr⟩ hc hp
         exact ⟨f,fun _=>h⟩
       exact ⟨fun _ _=>Coinage.dies,fun h=> (hr h).elim⟩
   choose p he using hh
   let P:=area e.v b e.i
   let q(z:Arc×ℕ×ℕ):=p z.1 z.2.1 z.2.2
   let S:=fanD e.v e.i b
   let f:=chenille e.v b
   have hm:Set.InjOn f S:=Fen.meadow ..
   let l:=Fields.meadow S f q
   have hs(i)(hi:i∈S):i.1∈P∧ i.2.1<e.v.Rslots∧i.2.2<e.v.Rslots:=by
                                              simpa [S,fanD,P] using hi
   refine ⟨l,floraC e x hm (fun v=>skyfell ..)
                      (fun k hk=>by obtain ⟨h1,h2,h3⟩:= hs k hk; exact (he k.1 h1).earns _ h2 _ h3),flushed e hm
                      (fun k hk=>by obtain ⟨h1,h2,h3⟩:=hs k hk;exact (he k.1 h1).stamp _ h2 _ h3),?_⟩
   intro y; rw [show l.rain y=_ from parkS _ hm _]
   unfold S fanD; rw [sum_product]
   apply sum_congr rfl; intro j hj; rw [sum_product]; exact (he _ hj).fund y
end Spirit

lemma reties (t b:Bool) {u _:ℕ} (_: b=t):0≤u :=Nat.zero_le _
structure Rise (x:ℕ)(l:Fields):Prop where
    gear :l.Good (began e.c) e x
    fee : l.fine e
    life:∀ y,l.rain y=e.basepart x y
lemma appears {x:ℕ}(h:e.Lo)(hx:x∈u.D.P):
    ∃ l,Rise e x l:=by
   by_cases he:Local.ready e
   · let S:= range 2
     have hr:Set.InjOn (firstG) S:=fun _ _ _ _ h=> (Seed.old_inj.1 h).2
     let q:=Local.sell e x
     refine ⟨Fields.meadow S firstG q,Fields.floraC e x hr ?_
          (fun _ hp=>(Local.Ready.crystal h he hx (mem_range.1 hp)).1),Fields.flushed e hr
                          (fun _ hp=> (Local.Ready.crystal h he hx (mem_range.1 hp)).2),fun y=>
         (Fields.parkS q hr y).trans (Local.Ready.total h he hx y)⟩
     intro i
     constructor
     · rintro hd; obtain ⟨j,hA,rfl⟩:=mem_image.1 hd; exact Local.seekRead e he (mem_range.1 hA)
     intro h; exact mem_image.2 ⟨i.x,mem_range.2 h.2.2.2.2,h.1.symm⟩
   refine ⟨Fields.empty,⟨?_,fun _ hi=>False.elim (notMem_empty _ hi)⟩,fun _ hi=>False.elim (notMem_empty _ hi),?_⟩
   · intro q
     constructor
     · intro h; exact False.elim (notMem_empty _ h)
     intro h; refine False.elim (he ⟨h.2.1,?_,h.2.2.2.1⟩)
     have hp: (shaped e.v.t.tag).1=0:=h.2.2.1
     cases ht:e.v.t.tag
     · rfl
     · rw [ht,shaped] at hp; contradiction
     · next b i=>cases b <;> simp only [ht,shaped] at hp <;> omega
     rw [ht,shaped] at hp;contradiction
   intro y; unfold Fields.empty Fields.rain basepart; dsimp only; rw [sum_empty,ite_eq_right]; exact fun h=>he h.1

structure Frolic (l:Fields)(x:ℕ):Prop where
    gear:l.Good (fun i=>atmos u.w0 e.c i ∨ began e.c i) e x
    fees:l.fine e
    bloom:∀ y,l.rain y=(e.v.marathon x).inc e.i y

lemma smeared (b:Bool){α:Type}[DecidableEq α](g:α → Pt)(s:Finset α):
   Reed.sideq (∑ i∈s,g i) b=∑ i∈s,Reed.sideq (g i) b:=by
   induction s using Finset.induction_on with
   | empty=> cases b <;> simp only [sum_empty]<;>rfl
   | @insert i s hi ih=>
     rw [sum_insert hi,sum_insert hi,← ih]; cases b <;> rfl
lemma frolic {e:Chron.Moon u}(hc:Weather.Crude e)(x:ℕ)(hx:x∈u.D.P): ∃ l,Frolic e l x:=by
    obtain ⟨t,hT⟩:=Spirit.lamp hc true hx; obtain ⟨f,hF⟩:=Spirit.lamp hc false hx; obtain ⟨v,h⟩:=appears e hc.lane hx
    have hd:=hT.gear.apart hF.gear (fun i ht hz=> by have he:=ht.2.symm.trans hz.2; contradiction)
    let l:=t.meet f; let r:=l.meet v
    have hp:l.Good (atmos u.w0 e.c) e x:=by
       convert hT.gear.fused hF.gear hd using 1
       ext i; cases he:i.fog.first0 <;> simp [signE,he]
    have hD:=hp.apart h.gear (fun i ha hb=> Seed.old_not _ _ _ _ _ (hb.1.symm.trans ha.1))
    refine ⟨r,hp.fused h.gear hD,Fields.Good.fairM (Fields.Good.fairM hT.fees hF.fees) h.fee,?_⟩
    intro y
    have ht :∀ b:Bool,∀ j:Arc, Reed.sideq (Weather.prize (⟨b,j⟩:Weather e) x y) (!b)=0:=by
       intro b j; unfold Weather.prize; split <;> cases b <;> rfl
    have hh(b): Reed.sideq (r.rain y) b=Reed.sideq ((e.v.marathon x).inc e.i y) b:=by
       unfold r l
       rw [Fields.flooded _ _ hD,Fields.flooded _ _ hd,hT.tell,hF.tell,h.life,e.rains0]
       have he(v z:Pt):Reed.sideq (v+z) b=Reed.sideq v b+Reed.sideq z b:=by cases b<;>rfl
       rw [he,he,smeared,smeared]
       cases b
       · erw [sum_eq_zero (fun j _=> ht true j)]
         ring
       erw [sum_eq_zero (f:=fun i=>Reed.sideq (Weather.prize (⟨false,i⟩:Weather e) x y) true)
                                             (fun j _=>ht false j)]
       ring
    exact Prod.ext (hh true) (hh false)
end Moon
end
end ExactDerandomization.Chron

end

section

namespace ExactDerandomization.Chron
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Amber Song Reed.Lu Fret.Seats Fret.Lyric
noncomputable section
open scoped Classical
variable {q w h:ℕ}
namespace Bevel
abbrev proofL:Cub ℕ Crt:= ⟨_, (Kn.unpack (α:=Crt)).comp Reed.VK.left⟩
def Thurs:Cub ℕ Bool:=
    ⟨_,proofL.runs.right.left.right.eq (Kn.fix (0:ℕ))⟩
def supplyC:Cub ℕ ℕ:=by
    let h:= (Spring.Blade.Crest.pastK proofL.runs 3)
    exact ⟨_,Kn.wash.comp (h.tuple (Kn.fix (hole 5 0)))⟩
abbrev June (p:MintV)(k:Knob):Lyric:=past k p supplyC
def sky (p:MintV)(k:Knob) :Cog:=
     Song.pleas Thurs (snow k p.inputH) (roost k (June p k) p.inputH)
abbrev headK(r:Rock q w h)(v:Tags):= Reed.campk (knob r v)
abbrev rentG (p:MintV)(r:Rock q w h)(v:Tags):Cog:= sky p (headK r v)
open Wear.Paper
def median(p:MintV)(r:Rock q w h):ℕ:=
   Era.tariff r+money0 p (June p (knob r noneT)) (Era.tariff r)
lemma estate (r:Rock q w h)(p:MintV)(k:Knob):
    let t:= Era.tariff r
    t  ≤  median p r∧ (reset (June p k) p.inputH).cost t ≤ median p r∧
                       (reset (June p k) p.inputH).tail ≤ median p r:=by
   intro t
   have he: Paper.same (June p k) (June p (knob r noneT)):=Paper.same.plies
                                     (Paper.use _ _ _) Paper.everF Doop.prod
   have hf:=he.stow p.inputH
   unfold median money0; dsimp only; unfold t; rw [hf.2.1,hf.2.2]; omega
end Bevel

variable {u:Line (q:=q) (w:=w) (h:=h)}
namespace Moon
variable (e:Chron.Moon u)
open Bevel
abbrev homeE (x:ℕ):Fret.Seats:=Studio.stk u e.a x 0
abbrev serve (x:ℕ)(b:ℝ):Prop:= u.D.Voice e.a x (hole 5 0) (u.D.high e.a) (e.p.inputH*u.D.D e.a) b
structure Back (x:ℕ)(l:Fields)(c: e.v.HistoryC e.p x e.i): Prop where
    gear:l.Good (retired u.w0 e.c) e x
    acomp:c.Compared e.v
    bounds: serve e x (HistoryC.actual e.v c e.i).base
    vita:∀ y∈e.v.S1,l.rain y=(HistoryC.actual e.v c e.i).ts y-line (HistoryC.actual e.v c e.i).base

structure Spire :Prop where
   lo:e.Lo
   core: e.base=rentG e.p u.r u.v
   fuel: median e.p u.r  ≤  u.v.slope
namespace Spire
variable {e:Chron.Moon u}(h0A:e.Spire)
include h0A
abbrev C (e:Chron.Moon u):= median e.p u.r
abbrev k0(_:Chron.Moon u):=headK u.r u.v
abbrev tB(e:Chron.Moon u):=u.D.high e.a+C e*u.D.D e.a
lemma stableA {x:ℕ}(hx:x∈u.D.P):Standard (e.homeE x) (k0 e) (tB e):=by
   have he:=h0A.lo.wpaid; let p:=Studio.dockA u e.a x
   have hz:= Studio.stayedC he (le_refl _) h0A.fuel
   exact ⟨Studio.positioned he hx _ _, Reed.spanFilm (Studio.vital _ hz) ..⟩
omit h0A in
lemma pin (x): proofL.f (e.homeE x).l.x (e.homeE x).info=e.c:=by
   change (dec (dec (enc ((_,_,_):Reed.Stool)) : Reed.Stool).1:Crt)=_
   rw [dec_round]; exact therein ..
omit h0A in
lemma tips(x): Thurs.f (e.homeE x).l.x (e.homeE x).info=decide (e.i=0):=by
    change decide (Age.g (proofL.f _ _)=0)=_
    rw [pin (e := e) x]
lemma echoU {b x} (hh:(e.homeE x).band (median e.p u.r) (u.D.high e.a) e.p.inputH e.base b):
    e.serve x b:=by
   have hf := (Era.billed u.r); have hk:Era.tariff u.r  ≤ median e.p u.r:= (Bevel.estate _ _ (k0 e)).1
   have he:= h0A.lo
   exact Studio.scoreTicket he.wpaid (by omega: (5:ℕ) ≤ 5) (by omega) (he.majors.wide0 1 e.i)
           (le_trans (le_trans (by omega) hf.1) hk) h0A.fuel le_rfl hh he.hot

lemma blank {x:ℕ}(ho:e.i=0)(hx:x∈u.D.P):e.serve x 0:=by
    apply h0A.echoU; rw [h0A.core]; apply Song.pinTrue Thurs _
    · have hp:= h0A.stableA hx
      have hz := (Bevel.estate u.r e.p (k0 e)).1
      have hb:= Era.billed u.r
      apply flex (steam _ _ hp (le_trans hb.2.2 hz)) ?_ le_rfl ?_
      · exact le_trans (le_trans (by omega) hb.1) hz
      unfold tB;omega
    rw [(Spire.tips (e := e)),ho]; decide
open Recent
lemma ante {j x:ℕ}{p:Ink e j x}(hp:p.Prints):
    e.serve x p.u0.y.base:=by
   let b:= (k0 e); let s:=e.homeE x; let v:=p.u0.y.base
   let t:=e.v.β j; let c:= Era.tariff u.r
   have hs:= h0A.stableA hp.target
   obtain ⟨h1,h2,h3⟩:= Bevel.estate u.r e.p b
   have ht:= Era.billed u.r
   have hn:=hp.history 3 (by decide)
   have hz: e.p.sealR*u.D.D t.dataN = (2*e.p.sealR)*u.D.D e.a :=by
          rw [hn.2]; ring
   have hm : supplyC.f s.l.x s.info = hole t.dataN (hole 5 0) :=by
      change hole (Spring.Blade.Crest.pastC (proofL.f s.l.x s.info) 3) (hole 5 0)=_
      rw [pin (e := e) x,hp.teeth]
   have hT:=Studio.soonerC h0A.lo.wpaid hn.1 h0A.fuel le_rfl
   have hw: s.band c (tB e) 0 (Bullet.snap supplyC) (v/massB (2*e.p.sealR) s.d):=
       Amber.normalizeF h0A.lo.wpaid supplyC ht.2.1 hp.target hm hn.1
                (hz ▸ hp.insight.at0) hT
   have ha:Chor b c (tB e) s (June e.p b) v:=Amber.cast (p:=u.D) (a:=e.a) (q:=s.info) (x:=x) (k:=b) (r:=2*e.p.sealR) (j:=2*e.p.sealR*u.D.D e.a) hs hw (scalingF (p:=u.D) (a:=e.a) (x:=x) (q:=s.info) (k:=b) (stable_home hs.st) _) le_rfl
   have hk:|v|  ≤ massB e.p.inputH s.d:=by
      have hl:= hw
      have hy:= Seats.maxv hw
      have hf:0 < massB (2*e.p.sealR) s.d:=mass0 ..
      change |_ / _| ≤ (2:ℝ)^_ at hy
      change |v/massB (2*e.p.sealR) s.d| ≤ (2:ℝ)^(0*s.d) at hy
      rw [abs_div,abs_of_pos hf,Nat.zero_mul,pow_zero,div_le_one hf] at hy; exact hy.trans
        (mass_mono (by unfold MintV.inputH; omega) _)
   apply h0A.echoU; rw [h0A.core]
   apply Song.pinFalse Thurs _
   · apply Amber.onQ b (June _ _) _ hs ha (by unfold c;omega) _ h2 hk
     exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h3) _
   rw [(Spire.tips (e := e)) x,hp.step]; simp
lemma projectB {x:ℕ}(hx:x∈u.D.P)
    (hE:∀ j,e.i=j+1→∃ t:e.v.Hinge e.p j x,e.v.HFine e.p j x t):
   ∃ l c,e.Back x l c :=by
    by_cases he:e.i=0
    · let q:e.v.HistoryC e.p x e.i:=⟨fun _=>false⟩
      have h0 : HistoryC.actual e.v q e.i= At.Blob.mk (0:ℝ) (fun _=>0):=by unfold HistoryC.actual; dsimp only [q]; rw [he]; rfl
      refine ⟨Fields.empty,q,⟨fun i=>?_,fun _ h0A=> False.elim (notMem_empty _ h0A)⟩,⟨fun _ hs=>False.elim ?_,
                                         fun _ hs=>False.elim ?_⟩,?_,?_⟩
      · apply iff_of_false (notMem_empty _) (fun e=>e.2.1 he)
      · omega
      · omega
      · rw [h0]; exact h0A.blank he hx
      intro y hy; rw [h0]; simp [Fields.empty,Fields.rain,Buf.line]; rfl
    obtain ⟨j,h1⟩:= Nat.exists_eq_succ_of_ne_zero he
    obtain ⟨q,hv⟩:= hE j h1
    let p:Ink e j x:= ⟨q⟩; have hP:p.Prints:=⟨h0A.lo,h1,hx,hv⟩
    let S:= range p.u0.n
    let f:= Fields.meadow S (rear0) p.turns
    let r:e.v.HistoryC e.p x e.i:=⟨q.hist.kap⟩
    have hf:r.Compared e.v:=by
       refine ⟨?_ ,?_⟩
       · intro i hi; exact hv.y0.cooling _ (by omega)
       intro i hi; exact hv.y0.shield _ (by omega)
    have hm:Set.InjOn rear0 S:= fun _ _ _ _ h0A=> (Seed.old_inj.1 h0A).2
    have hz : p.u0.y=HistoryC.actual e.v r e.i:=by
       have hb: (e.v.marathon x).actual _ q.hist.kap e.i= (e.v.marathon x).actual (HistoryC.R e.p e.v) r.kap (j+1):= congrArg (fun i=> (e.v.marathon x).actual (HistoryC.R e.p e.v) r.kap i) h1
       exact hv.ton.trans hb.symm
    refine ⟨f,r,Fields.floraC e x hm ?_ (fun i hi=>hP.teach i (mem_range.1 hi)),hf,
                                        hz ▸ h0A.ante hP,?_⟩
    · intro i
      constructor
      · intro he; obtain ⟨i,hi,rfl⟩:=mem_image.1 he; exact hP.turn0 _ (mem_range.1 hi)
      intro he; apply mem_image.2; refine ⟨i.x,mem_range.2 ?_,he.1.symm⟩
      rw [show p.u0.n=e.v.Snum j from hP.insight.card0]
      have hh:=he.2.2
      change i.x < e.v.Snum (e.i-1) at hh; rwa [h1,Nat.succ_sub_one] at hh
    intro y hy; rw [←hz]
    exact (Fields.parkS p.turns hm _).trans (hP.total y hy)
end Spire
end Moon
end
end ExactDerandomization.Chron

end

section

namespace ExactDerandomization.Chron.Moon
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain Cambria Cambria.Wear Terrain Bank
open Spring Garden Blade Fen BadgeX Mica Rime Nest Nest.Good Surf Fabric Census
open Arena Pier Quest ExactDerandomization.Chron.Moon.Weather
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable (e:ExactDerandomization.Chron.Moon u)

namespace Moonlit
open Fields

lemma genc : Function.Injective (fun x:Seed=>enc x):= fun _ _ he => (Wire.eq _).symm.trans ((congrArg dec he).trans (Wire.eq _))
def limit (F:Fields):Finset ℕ:= F.T.image enc
lemma koa (F:Fields):(limit F).card=F.T.card:=card_image_of_injective _ genc

def spread (F:Fields)(i:ℕ):Coinage:= if i∈limit F then F.f (dec i) else Coinage.dies
variable {e}
lemma kinship (F:Fields) {x:ℕ}(h:F.Good (ace u.w0 e.c) e x) (_:e.Lo) :
     ∀ i, i∈limit F ↔ clean u.w0 (e.a,i)=true:= by
   intro i
   simp only [clean,decide_eq_true_eq,show (dec e.a : Crt)=e.c from therein ..]
   unfold limit; rw [mem_image]; constructor
   · intro ht;obtain ⟨j,hj,rfl⟩:=ht;rw [Wire.eq]; exact ⟨rfl,(h.mem _).mp hj⟩
   intro hp;exact ⟨dec i,(h.mem _).2 hp.2,hp.1⟩

lemma begins(F:Fields){x:ℕ}(h:F.Good (ace u.w0 e.c) e x)(he:e.Lo):limit F⊆ range e.cageX.m:=by
    intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.1 hi
    exact mem_range.2 (Fen.GardenV.windowN _ he.s2 he.majors.book.saving ((h.mem _).1 hj))
lemma summer (F:Fields){x:ℕ}(h:F.Good (ace u.w0 e.c) e x) (he:e.Lo)(y:ℕ):
    ∑ i∈range e.cageX.m,(spread F i).pigment y= F.rain y:=by
   rw [←sum_subset (begins _ h he) ?_]
   · unfold limit; rw [sum_image (show ∀ i∈F.T,∀ j∈F.T,enc i=enc j → i=j from fun _ _ _ _ h=>genc h)]
     apply sum_congr rfl; intro i hi; unfold spread; rw [ite_eq_left (show enc i ∈ limit F from mem_image_of_mem _ hi),Wire.eq]
   intro i _ hA; unfold spread; rw [ite_eq_right hA]
   exact Weather.only0 _

lemma emits (F:Fields){x:ℕ}(hx:x∈u.D.P)(h:F.Good (ace u.w0 e.c) e x)
    (he:e.Lo)(i:ℕ):e.Spend x i (spread F i):=by
    unfold spread; split
    · next hg=> obtain ⟨j,hj,rfl⟩:=mem_image.1 hg;rw [Wire.eq]; exact h.sound _ hj
    next hm=>
    have hs: ¬clean u.w0 (e.a,i)=true:= fun he0=>hm ((kinship F h he i).2 he0)
    exact dun e he hx (ite_eq_right hs)
lemma terminal {α:Type}[DecidableEq α](f:α→Pt)(s:Finset α):
       ht (∑ i∈s,f i) ≤ ∑ i∈s,ht (f i):=by
   induction s using Finset.induction_on with
   | empty=>simp [Buf.ht]
   | @insert i s hi ih=>
     rw [sum_insert hi,sum_insert hi]; exact le_trans (ht_add ..) (add_le_add_right ih _)
lemma cloud (F L:Fields)(hp:L.T⊆F.T)
    {x:ℕ}(h:F.Good (ace u.w0 e.c) e x)(he:e.Lo)(hi:L.fine e)(y):
   ht (L.rain y)  ≤  massB e.p.tokenH e.d:=by
     have hx := le_trans (card_le_card hp)
                                (show F.T.card ≤ e.cageX.m from by
                                   rw [← koa]; exact (card_le_card (begins F h he)).trans_eq (card_range ..))
     let R:=massB e.p.prism e.d
     have ht :∀ i∈L.T, ht ((L.f i).pigment y)≤ R:= by
          intro i hi'; unfold Coinage.pigment
          split
          · exact hi _ hi'
          simp [Buf.ht]; positivity
     refine (terminal _ _).trans ((sum_le_sum ht).trans ?_)
     simp only [sum_const,nsmul_eq_mul]
     rw [mass_mul]
     refine mul_le_mul_of_nonneg_right ?_ (mass0 ..).le
     change (L.T.card:ℝ) ≤ _
     unfold massB; exact_mod_cast hx

lemma enrolled (h:Weather.Crude e)(x:ℕ)(hx:x∈u.D.P){c:e.v.HistoryC e.p x e.i}
   {l:Fields}(hh:e.Back x l c):
   ∃ b:e.v.Yolk e.p e.i x,e.v.YFine e.p e.i x b∧∀ j,b.raw.tag j ≤ Era.budget u.r :=by
   obtain ⟨F,hF⟩:= frolic h x hx
   let p:= l.meet F
   have hd:Disjoint l.T F.T :=by
      apply hh.gear.apart hF.gear
      intro i hi ht
      rcases ht with hP|hP
      · exact Seed.old_not _ _ _ _ _ (hi.1.symm.trans hP.1)
      have hs:=(Seed.old_inj.1 (hi.1.symm.trans hP.1)).1; contradiction
   have hp:p.Good (ace u.w0 e.c) e x:=by
      convert hh.gear.fused hF.gear hd using 1
      ext i; unfold ace; tauto
   let a := spread p; have ha(i):e.Spend x i (a i):= emits p hx hp h.lane i
   let z:= HistoryC.actual e.v c e.i
   let r:= e.v.marathon x
   let w:=r.shifted e.i z
   let g:Reed.Poolx:=
      ⟨r.pm e.i,w,e.cageX.m,fun i=>(a i).i,fun i=>(a i).p,fun i=>(a i).dye⟩
   refine ⟨⟨c,g⟩,⟨hh.acomp,rfl,rfl,rfl,?_,?_,?_,hh.bounds,?_,?_⟩,fun i=>(ha i).below⟩
   · refine ⟨?_, fun i _ ht=>(ha i).into ht|>.2, ?_⟩
     · exact r.actual_closed (HistoryC.R e.p e.v) c.kap e.i
     intro y hy
     change z.ts y+r.inc e.i y = line z.base+ ∑ i∈range e.cageX.m,(a i).pigment y
     rw [show ∑ i∈range _,(a i).pigment y = p.rain y from summer p hp h.lane _,
          show p.rain y=l.rain y+F.rain y from Fields.flooded _ _ hd y,hF.bloom _,hh.vita y hy]; abel
   ·
     refine ⟨fun i hi=>(ha i).key hi,fun i hi=> (ha i).sizes hi,?_,fun i hi=>?_⟩
     · intro i hi; have he: i∉limit p:= fun hx=>Nat.not_lt_of_ge hi (mem_range.1 (begins p hp h.lane hx))
       change (spread p i).i=0; rw [spread,ite_eq_right he];rfl
     exact (ha i).faith hi
   · intro b; exact ⟨fun j hj=> (ha j).stats hj b⟩
   · intro y _
     rw [←hF.bloom]; exact cloud p F subset_union_right hp h.lane hF.fees _
   intro hQ i
   by_contra hi
   exact hQ ((ha i).into hi).1

end Moonlit

/-- instruction-bound local derivation. -/
lemma nursery (h:Weather.Crude e)(hs:e.Spire)
     (ho:∀ x∈u.D.P,∀ j,e.i=j+1→∃ t:e.v.Hinge e.p j x,e.v.HFine e.p j x t):
   ∀ x∈u.D.P,∃ t:e.v.Yolk e.p e.i x,e.v.YFine e.p e.i x t∧∀ j,t.raw.tag j ≤ Era.budget u.r:=by
    intro x hx
    obtain ⟨b,c,ht⟩:=hs.projectB hx (ho x hx)
    exact Moonlit.enrolled h _ hx ht

end
end ExactDerandomization.Chron.Moon

end

end OAI
