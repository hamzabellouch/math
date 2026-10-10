import OAI.Computability.Logspace.CompressionEvaluation
import OAI.Computability.Logspace.DiagonalEvaluation
import OAI.Computability.Logspace.TerminalEvaluation
import OAI.Computability.Logspace.TransitionEvaluation

namespace OAI

/-!
Simultaneous correctness of one uniform estimator program on all inputs.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Umbra
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Vessel Gamut
noncomputable section
open scoped Classical
variable {q w h:ℕ}
namespace Codex
variable (p:MintV)(r:Rock q w h)(v:Tags)
def atlas : Pose:= Lily.poseX r
abbrev mdi:= BevelP p r v where
   BevelP:= Chron.Bevel.rentG
abbrev boxI0:=Lily.prog r v p (mdi p r v)
abbrev boxI1:=Tiber.Sky.progP p r v
abbrev boxT:= Aurora.Fort.baseTc r p v
abbrev boxE:= Gyre.Term.fullD r v p
abbrev capT:=Line.Fabric.capprog r v (atlas r)
abbrev rankT1:=Line.Fabric.Stand.score0 (Pond.reapT r.w) r v (atlas r)
abbrev rankE1:=Line.Fabric.Stand.score0 (Pond.reapE r.w) r v (atlas r)
abbrev VI := Sun.scheduleR p (knob r v) (PrintV.shell r p v)
abbrev VF := Ma.promptV p r v

def produce (k:ℕ):Cog :=
   match k with
   | 1=>boxI0 p r v
   | 3=>boxI1 p r v
   | 9=>boxT p r v
   | 12=>capT r v
   | 13=>rankT1 r v
   | 14=>boxE p r v
   | 16=>rankE1 r v
   | 5=>VI p r v
   | 17=>VF p r v
   | _=> Cargo.knock
abbrev pages :Stash:=⟨atlas r,produce p r v⟩

abbrev hcap := v.A*(2*v.A+40)
abbrev compass (s:Fabric.Stand)(v:Tags):ℕ:=powder (v.A*(2*v.A+40)+6*(s.k+50))
abbrev coins3:= GoodF.treasury p r
abbrev debit3:= Sun.priceC r p (coins3 p r)

structure Paying (p:MintV)(r:Rock q w h)(v:Tags) :Prop where
    h1:Cambria.Wear.Paper.budgetD p r ≤ v.slope
    h2:Chron.Bevel.median p r≤v.slope
    h3:Tiber.Sky.budget0 p r≤v.slope
    h4:Aurora.Fort.budget4 p r≤v.slope
    h5:hcap v ≤ v.slope
    h6:compass (Pond.reapT r.w) v≤v.slope
    h7:compass (Pond.reapE r.w) v≤ v.slope
    h8:Gyre.Term.Budget0.cost r v p ≤ v.slope
    h9:debit3 p r+ coins3 p r ≤ v.slope
    he:Ma.render p≤ v.slope
def sump(p:MintV)(r:Rock q w h)(v:Tags):ℕ:=
    Cambria.Wear.Paper.budgetD p r+ Chron.Bevel.median p r+Tiber.Sky.budget0 p r+
    Aurora.Fort.budget4 p r+ hcap v + compass (Pond.reapT r.w) v+compass (Pond.reapE r.w) v+
    Gyre.Term.Budget0.cost r v p+ (debit3 p r+coins3 p r)+Ma.render p
lemma liable (ht: sump p r v ≤ v.slope):Paying p r v:=by
    unfold sump at ht
    constructor <;>omega

structure Fortune (r:Rock q w h)(p:MintV)(v:Tags)(κ:ℕ):Prop where
    funds:Paying p r v
    t0:Turf p r v
    coast0:max 6 (10*v.e) ≤ v.slope
    earth0:100 ≤ κ∧ lb capD ≤ κ∧100*v.e ≤ κ
    boom:1000*κ^2 ≤ v.A
    city:v.A ≤ v.slope
    cargo:r.w.p.K ≤ κ

lemma enacted (t:ℕ) (e:r.w.Proof):∃ p v κ, Fortune r p v κ ∧ v.extra=t:=by
    obtain ⟨p,hp⟩:= Bank.greenUp (r:=r) e
    let x:=hx p r
    let B:=bootC r
    let κ:=100 + lb capD +100*x+r.w.p.K
    let A:=1000*κ^2
    let f(s):Tags:=⟨x,A,s,t,B,0⟩
    let b:=max 6 (10*x)
    let k:=sump p r (f 0) + A+b
    have ht:sump p r (f k)=sump p r (f 0):=rfl
    have hh:sump p r (f k)≤k:=by rw [ht]; exact le_trans (Nat.le_add_right ..) (Nat.le_add_right ..)
    have ha:A ≤ k:= le_trans (Nat.le_add_left ..) (Nat.le_add_right ..)
    exact ⟨p,f k,κ,⟨liable _ _ _ hh,⟨hp,le_rfl,le_rfl⟩,(show b ≤ k from Nat.le_add_left ..),
                  ⟨(by unfold κ;omega),(by unfold κ;omega),by change 100*x≤κ; unfold κ;omega⟩,le_rfl,ha,(by unfold κ;omega)⟩,rfl⟩
end Codex

variable {u:Line (q:=q) (w:=w) (h:=h)}

structure TrustQ(u:Line (q:=q) (w:=w) (h:=h)) (p:MintV)(κ:ℕ):Prop where
    plan:Codex.Fortune u.r p u.v κ
    page:u.s=Codex.pages p u.r u.v
    chart:u.Chart
namespace TrustQ
variable {p:MintV}{k:ℕ}(he:TrustQ u p k)
include he
lemma owns(v:Fabric u)(hp:v.Good):Stone.Rector v p:=⟨he.plan.t0,he.chart,hp⟩
lemma ownsV(v:OrbitV u)(hp:v.estate):v.Counsel p:=⟨he.chart,hp,he.plan.t0⟩
lemma grants(v:Fabric u):v.Mantle k:=by
    have hh:=he.plan
    refine ⟨he.chart,hh.earth0.1,hh.earth0.2.1,hh.earth0.2.2,hh.boom,hh.city,?_⟩
    intro i hi; exact le_trans (le_trans (lb_le_inc i) (Nat.succ_le_of_lt hi)) hh.cargo

lemma scripted(i):u.s.scripted i=Codex.produce p u.r u.v i:=by rw [he.page]
lemma stock:u.s.pave=Codex.atlas u.r:=by rw [he.page]
lemma capdraw:u.s.scripted 12=Line.Fabric.capprog u.r u.v u.s.pave:=by rw [he.scripted,he.stock]; rfl

lemma pearls {a i:ℕ}(hp:u.D.active a)(hm:a≠0)(hk:(uphold a).1=i)
      (hz:i≠0)(he1:∀ k,k=2∨k=4∨k=10∨k=11∨k=15→i≠k):
   Studio.Parcel u a (Codex.produce p u.r u.v i):= by
     have hx:=he.chart
     apply Studio.stationed
     all_goals first|exact hp|exact hx|exact hm|skip
     · rw [hk]; exact ⟨hz,he1⟩
     rw [hk]; exact he.scripted i

lemma pearlR (v: Fabric u)(i j:ℕ)(h:u.D.active (v.c i j))(hz:i≠0)(he1:∀ k,k=2∨k=4∨k=10∨k=11∨k=15→i≠k):
   Studio.Parcel u (v.c i j) (Codex.produce p u.r u.v i):=
      he.pearls h (Age.cpos _) (Stone.roleR ..) hz he1
lemma pearlV (v: OrbitV u)(i j:ℕ)(h:u.D.active (v.channel i j))(hz:i≠0)(he1:∀ k,k=2∨k=4∨k=10∨k=11∨k=15→i≠k):
   Studio.Parcel u (v.channel i j) (Codex.produce p u.r u.v i):=
      he.pearls h (Age.cpos _) (show (uphold (v.channel i j)).1=i from by simp [uphold,OrbitV.channel,vecL,clr,Foil.kit]) hz he1

lemma insures (v:Fabric u)(h:v.Good): Pond.Books p v k:=by
    have H:=he.plan.funds
    refine ⟨he.owns v h,he.grants v,H.h6,H.h7,?_,?_⟩
    · rw [he.scripted,he.stock]; rfl
    rw [he.scripted,he.stock];rfl
end TrustQ

end
end ExactDerandomization.Umbra

end

section

namespace ExactDerandomization.Umbra
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Vessel Gamut
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}

namespace Elect
variable (p:MintV) (v:Fabric u)
abbrev Birth (i:ℕ) :Prop :=∀ x∈u.D.P,∃ a:v.Yolk p i x,v.YFine p i x a∧
                                                    ∀ j,a.raw.tag j ≤ Cambria.Era.budget u.r
abbrev Mark (i:ℕ):Prop:=∀ x∈u.D.P,∃ a:v.Hinge p i x,v.HFine p i x a∧
                                  ∀ j,lb (a.depot.tag j) ≤ Bank.hu p u.r * gap v.m i
abbrev CeilingR (p:MintV)(v:Fabric u):Prop:=
           ∃ f:Bool → Producer, ∃ tb, v.Tgood p f ∧ v.Profession (f false) tb
/-- Specific contract per version, Good row assumed.Pulse.EI at any m scoreboard.
If inactive potential, no TC or T services. End serves zeros. -/
structure Covenant (u:Line (q:=q) (w:=w) (h:=h))(p:MintV)(a:ℕ):Prop where
    θ:∀ v:Fabric u,v.Good→v.activeR→∀ i<Age.L v.m,v.c 1 i=a→ Birth p v i
    φ:∀ v:Fabric u,v.Good→v.activeR→∀ i<Age.L v.m,v.c 3 i=a→ Mark p v i
    T0:∀ v:Fabric u,v.Good→v.activeR→v.c 9 0=a→∃ f,v.Tgood p f
    ψ:∀ v:Fabric u,v.Good→v.activeR→v.govern=true → v.c 12 0=a→ CeilingR p v
    ω:∀ v:Fabric u,v.Good→v.activeR→v.govern=true →v.c 13 0=a→ Pond.TracedR v
    R0:∀ v:Fabric u,v.Good→v.c 14 0=a→∃ f,v.Efine p f
    IN:∀ v:Fabric u,v.Good→ v.t.main=true→ (∃ k,v.t.tag=.score k) →v.c 16 0=a→Pond.TracedE p v
    ζ:∀ v:OrbitV u,v.estate→v.works→∀ i<Age.L v.m,v.channel 5 i=a→∀ x∈u.D.P,v.Earn p i x
    ε:∀ v:OrbitV u,v.estate→v.channel 17 0=a→v.FEnd

structure FullV (u:Line (q:=q) (w:=w) (h:=h))(p:MintV)(i:ℕ):Prop where
    old:Covenant u p i
    wick:u.wick0.Veil u.torch i
    ear:u.D.Ears0 i
def Promised (u:Line (q:=q) (w:=w) (h:=h))(p:MintV)(i:ℕ):Prop:=
   ∀ j,u.D.active j→u.D.W j<u.D.W i→FullV u p j

lemma glacial (v:Fabric u): delta0 (bitR v.t) ↔ v.govern=true:=by
    unfold Line.Fabric.govern bitR delta0
    cases v.t.tag
    all_goals simp [shaped,Kind.narrow]
    all_goals split <;> simp_all
lemma ruddy(v:Fabric u) {k}(h:v.t.main=true)(hp:v.t.tag=.score k):redV (bitR v.t):=by
   unfold redV bitR; rw [h,hp]; exact ⟨rfl,rfl⟩
lemma haze (v:OrbitV u)(a i:ℕ):(uphold (v.channel a i)).1=a:=by
   simp [uphold,OrbitV.channel,vecL,clr,Foil.kit]

namespace Covenant
variable {p:MintV} {k:ℕ}(h0:TrustQ u p k)
include h0
omit h0 in
lemma mute {a:ℕ}(_:u.D.active a)(hk:a≠0)(j:ℕ)(hQ:(uphold a).1=j)
    (hh:¬ (j=1∨j=3∨j=9∨j=12∨j=14)) :
    u.D.Ears0 a:=Shift.free u hk hQ (fun i t=>by unfold taps colorQ omegaQ;omega) (by omega)

lemma fandom (w:Fabric u)(i j:ℕ)(h:u.D.active (w.c i j))(hp:Covenant u p (w.c i j)):
    u.D.Ears0 (w.c i j):=by
   have hs:=h0.chart
   have hf:= hs.rent h
   obtain ⟨h1,h2,h3,h4⟩:= ((Line.Chart.courseR (u := u)) w.dye).1 h
   have hz:w.Good:= ⟨h1,h4⟩
   have hc : i=1∨i=3∨i=9 → w.activeR:=by
       intro he
       apply w.workR.2
       rcases h3.2 with hk|hk; exact hk.2
       omega
   have hh:i=1∨i=3→j<Age.L w.m:=by
       intro hi; rwa [Period,ite_eq_left (by unfold Brole;omega)] at h2
   have hh':i≥9→j=0:=by
       intro hi; rw [Period,ite_eq_right (by unfold Brole;omega)] at h2; omega
   by_cases h:i=1
   · subst i; apply Shift.earsTag u w 1 j (by omega)
     intro x hx i hi
     obtain ⟨b,hb,_⟩:=hp.θ w hz (hc (by omega)) j (hh (by omega)) rfl x hx
     exact ⟨_,hb.found.next i hi⟩
   by_cases h':i=3
   · subst i; apply Shift.earsTag u w 3 j (by omega)
     intro x hx i hi
     obtain ⟨b,hb,_⟩:=hp.φ w hz (hc (by omega)) j (hh (by omega)) rfl x hx
     exact ⟨_,hb.found.next i hi⟩
   by_cases hT:i=9
   · have ht:=hh' (show 9 ≤ i from by omega)
     subst i; subst j
     obtain ⟨f,he⟩:=hp.T0 w hz (hc (by omega)) rfl
     exact Shift.terminal u w p f he
   by_cases hR:i=12
   · have ht:=hh' (show 9 ≤ i from by omega)
     subst i;subst j
     have hk:w.govern=true:=by
        apply (glacial w).1
        have hm:=h3.2
        unfold Bob at hm; grind
     apply Shift.court u w hf
     intro i hi; by_cases hQ:w.activeR
     · obtain ⟨f,tb,h1,h2⟩:=hp.ψ w hz hQ hk rfl
       have hc:1 ≤ clim u.w0.p:=by unfold clim; omega
       exact ⟨_,(h2.guide 0 (mem_range.2 (Nat.zero_lt_succ _)) i hi 1 Nat.zero_lt_one hc).2.1⟩
     exact ⟨_,Line.Fabric.desert12 i hz hQ hf hs h0.capdraw⟩
   by_cases hU:i=14
   · have ht:=hh' (show 9 ≤ i from by omega)
     subst i;subst j
     obtain ⟨f,he⟩:=hp.R0 w hz rfl
     exact Shift.eventE u w p f he
   apply mute ‹u.D.active (w.c i j)› (Age.cpos _) i (Stone.roleR ..)
   omega

lemma orchard {a:ℕ}(h:Covenant u p a)(he:u.D.active a):u.D.Ears0 a:=by
    by_cases hk:a=0
    · subst a; exact Shift.basic u h0.chart
    rcases (Line.Chart.parse (u := u)) he hk with ⟨P,m,i,j,w,rfl⟩|⟨P,m,i,j,w,rfl⟩
    · exact fandom h0 (⟨P,m,w⟩:Fabric u) i j he h
    let f:OrbitV u:=⟨m,P,w⟩
    apply mute he hk i (haze f ..)
    have h4:= (((Line.Chart.courseV (u := u)) w).1 he).2.2.1.2; omega
end Covenant

namespace Promised
variable {p:MintV}{i:ℕ}(hg:Promised u p i)
include hg
lemma seeking:u.D.Heard i:=fun _ he hi _=> (hg _ he hi).ear
lemma sooner {b}(hi:u.D.active b)(hp:u.D.W b+u.D.D i ≤ u.D.W i)(he:u.D.Suite i):FullV u p b:=
   hg b hi (by have := he.well.1; omega)
end Promised
end Elect

end
end ExactDerandomization.Umbra

end

section

namespace ExactDerandomization.Umbra
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Vessel Gamut Spring
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Elect
namespace TrustQ
variable {p:MintV}{k:ℕ}(hQ:TrustQ u p k)
include hQ

lemma stara (v:Fabric u) (i:ℕ) (hp:v.Good)(hi:v.activeR)(hj:i<Age.L v.m)
     (hc:Promised u p (v.c 1 i)):Birth p v i:=by
    let e:Chron.Moon u:=⟨p,v,i,Codex.mdi p u.r u.v⟩
    have ht:=hQ.owns v hp
    have hs:= (ht.midUnits hi 1 i (Or.inl ⟨by omega,by omega,hj⟩))
    have he:e.Lo:= ⟨ht,hi,hj,hQ.stock.symm,hQ.plan.funds.h1,hQ.pearlR v 1 i hs.stage (by omega)
                                                                               (by intro j;omega),
                               fun b h hh=>(hc.sooner h hh hs).wick⟩
    have hS:e.Spire:=⟨he,rfl,hQ.plan.funds.h2⟩
    have hf:Chron.Moon.Weather.Crude e:=by
        refine ⟨he,?_,?_⟩
        · intro a h hk
          have hl:u.D.W (a.c 14 0)+u.D.D (v.c 1 i) ≤ u.D.W (v.c 1 i):=by rw [Stone.W,Stone.D,Stone.W];exact Age.renewal hk
          have ha:= (hQ.owns a h).endUnits 14 (Or.inl rfl)
          exact (hc.sooner ha.stage hl hs).old.R0 a h rfl
        intro t m w hl hy hk
        let x:OrbitV u:=⟨m,t,w⟩
        have hf:x.estate:=⟨hl,hy⟩
        have ha: u.D.W (x.channel 17 0)+u.D.D (v.c 1 i) ≤ u.D.W (v.c 1 i):=by
              rw [show u.D.W (x.channel 17 0)=Age.weight m 17 0 from u.rolfe ..,Stone.D,Stone.W]
              exact Age.renewal hk
        exact (hc.sooner (hQ.ownsV x hf).unitV.stage ha hs).old.ε x hf rfl
    apply e.nursery hf hS
    intro x hx j he1
    have hh:i=j+1:=he1
    have hl:j+1<Age.L v.m:= hh ▸hj
    have hm:u.D.W (v.c 3 j)+u.D.D (v.c 1 i) ≤ u.D.W (v.c 1 i):=by
            rw [Stone.W,Stone.D,Stone.W,hh];exact Age.oldpay hl (by decide) (by decide)
    have hk:= (hc.sooner (ht.midUnits hi 3 j (Or.inl ⟨by decide,by decide,by omega⟩)).stage hm hs).old
    obtain ⟨a,ha,hf⟩:=hk.φ v hp hi j (by omega) rfl x hx
    exact ⟨a,ha⟩

lemma starb (v:Fabric u)(i:ℕ)(hp:v.Good)(hi:v.activeR)(hj:i<Age.L v.m)
      (hc:Promised u p (v.c 3 i)):Mark p v i:=by
    intro x hx
    let s:Tiber.SliceD.Fire u:=⟨p,v,i,x⟩
    have ht:=hQ.owns v hp
    have h2(k:ℕ)(he:k=1∨k=2∨k=3):= ht.midUnits hi k i (Or.inl ⟨by omega,by omega,hj⟩)
    have hs:=h2 3 (by omega)
    have h1(k:ℕ)(hh:k=1∨k=2):FullV u p (v.c k i):=by
       apply hc.sooner (h2 k (by omega)).stage ?_ hs
       rw [Stone.W,Stone.D,Stone.W]
       apply Age.sooner ?_ (by omega) (by omega)
       rcases hh with hh|hh <;> rw [hh] <;> rfl
    obtain ⟨f,hf,he⟩:=(h1 1 (by omega)).old.θ v hp hi i hj rfl x hx
    apply Tiber.SliceD.Fire.Bakin.beam0 (v:=s) (f:=f)
    · exact ⟨⟨ht,hj,hi,hx,(h1 2 (by omega)).wick,hQ.plan.funds.h3⟩,hf,he⟩
    exact hQ.pearlR v 3 i hs.stage (by omega) (by intro i;omega)

lemma stard (v:Fabric u)(hp:v.Good)(hi:v.activeR)
      (hc:Promised u p (v.c 9 0)):∃ f,v.Tgood p f:=by
    let s:Aurora.Grape.Dew u:=⟨p,v⟩
    have ht:=hQ.owns v hp
    have hs:= ht.midUnits hi 9 0 (Or.inr ⟨rfl,Or.inl (by omega)⟩)
    have he:s.Ready:=⟨ht,hi,hQ.plan.funds.h4⟩
    let j:=s.g
    have hm:j<Age.L v.m:=by have hh:j+1=Age.L v.m:=(Aurora.Grape.Dew.Ready.now (e := s)); omega
    apply Aurora.Grape.Dew.Supply.givenE he (hQ.pearlR v 9 0 hs.stage (by omega) (by intro i; omega))
    intro x hx
    have hn :u.D.W (v.c 3 j)+u.D.D (v.c 9 0) ≤ u.D.W (v.c 9 0):=by
         rw [show u.D.D (v.c 9 0)=1 from (Aurora.Grape.Dew.Ready.last (e := s))]; exact (Aurora.Grape.Dew.Ready.toward (e := s)).2.2
    have hl:= hc.sooner (ht.midUnits hi 3 j (Or.inl ⟨by decide,by decide,hm⟩)).stage hn hs
    obtain ⟨a,h1,hA⟩:= hl.old.φ v hp hi j hm rfl x hx
    refine ⟨a,he,hx,h1,fun i=>?_⟩
    have hh:= hA i; rwa [show gap v.m j=1 from (by unfold gap; rw [show Age.L v.m=j+1 from (Aurora.Grape.Dew.Ready.now (e := s)).symm]; simp),mul_one] at hh

end TrustQ

end
end ExactDerandomization.Umbra

end

section

namespace ExactDerandomization.Umbra
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Vessel Gamut
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Elect
namespace TrustQ
variable {p:MintV}{k:ℕ}(hr:TrustQ u p k)
include hr

omit hr in
lemma promiseE {v:Fabric u}{i j:ℕ}(h:Promised u p (v.c j 0))(hi:5 < i)(he:i<j)(hp:j ≤ 64)
    (h1:u.D.active (v.c i 0)):
    FullV u p (v.c i 0):= h (v.c i 0) h1 (v.parentL (by unfold Brole;omega) he hp)
lemma earlierT (v:Fabric u)(j:ℕ)(h:Promised u p (v.c j 0))(he: v.Good)(hu :v.activeR)
    (hj:9<j)(hk:j ≤ 64):∃ f,v.Tgood p f :=
       (TrustQ.promiseE h (show 5<(9:ℕ) by omega) hj hk
                 ((hr.owns v he).midUnits hu 9 0 (Or.inr ⟨rfl,Or.inl (by omega)⟩)).stage).old.T0 v he hu rfl

lemma crownC (v:Fabric u)(he:v.Good)(hp:v.govern=true): u.D.Suite (v.c 12 0):=
       (hr.owns v he).endUnits _ (Or.inr (Or.inr (Or.inl ⟨rfl,(glacial v).2 hp⟩)))

lemma deputed (v:Fabric u)(h:Promised u p (v.c 12 0))(he: v.Good)(hu:v.activeR)(hp:v.govern=true):
    CeilingR p v:=by
       obtain ⟨f,hf⟩:=hr.earlierT v 12 h he hu (by omega) (by omega)
       have hs:=hr.crownC v he hp
       obtain ⟨g,hg⟩:= Line.Fabric.tribunal (hf.secure false) (hr.grants v) he hs h.seeking hu hr.plan.funds.h5 hr.capdraw
       exact ⟨f,g,hf,hg⟩

lemma starR (v:Fabric u)(h:Promised u p (v.c 13 0))(he:v.Good)(hu:v.activeR)(hp:v.govern=true):
     Pond.TracedR v:=by
       obtain ⟨f,hf⟩:=hr.earlierT v 13 h he hu (by omega) (by omega)
       have hq:=hr.insures v he
       exact hq.echoR hf (hq.iris.midUnits hu _ _ (Or.inr ⟨rfl,Or.inr ⟨rfl,(glacial v).2 hp⟩⟩)) h.seeking

lemma staE (v:Fabric u)(h: Promised u p (v.c 16 0))(he:v.Good)
   (hk:v.t.main = true) (hh:∃ k,v.t.tag=.score k):
     Pond.TracedE p v:=by
       obtain ⟨i,hi⟩:=hh
       have hq:=hr.insures v he
       obtain ⟨f,hf⟩:= ((TrustQ.promiseE h (show 5< (14:ℕ) by omega) (by omega) (by omega)
                                      (hq.iris.endUnits _ (Or.inl rfl)).stage).old.R0 v he rfl)
       exact hq.echoE hf (hq.iris.endUnits _ (Or.inr (Or.inr (Or.inr ⟨rfl,ruddy v hk hi⟩)))) h.seeking

open Gyre Gyre.OrbitR
abbrev pr(t:MintV)(v:Fabric u): Prism u:=⟨v,t⟩
lemma upK (v:Fabric u)(he:v.Good): (pr p v).Ace:=by
       have hm:= (hr.owns v he)
       have hq:=hr.plan.funds.h8
       have hp:= (Gyre.Term.Budget0.fareE u.r u.v p 0).1
       refine ⟨⟨hm,hp.trans hq⟩,hq,?_⟩
       exact hr.pearlR v 14 0 (hm.endUnits 14 (Or.inl rfl)).stage (by omega) (by intro i;omega)
lemma sovereign(v:Fabric u)(he:v.Good) (hu:v.activeR)(h:Promised u p (v.c 14 0)):
     ∃ f tb,(pr p v).Enabled f tb:=by
       have hh:=hr.upK v he
       cases hp:v.govern
       · obtain ⟨f,hf⟩:=hr.earlierT v 14 h he hu (by omega) (by omega)
         refine ⟨f,fun _ _=>0,hh.he,hu,hf,fun ht=>?_⟩
         change v.govern=true at ht; simp [hp] at ht
       obtain ⟨f,g,h1,h2⟩:= ((TrustQ.promiseE h (show 5<(12:ℕ) by omega) (by omega) (by omega)
                                        (hr.crownC v he hp).stage).old.ψ v he hu hp rfl)
       exact ⟨f,g,hh.he,hu,h1,fun _=>h2⟩
open Gyre.OrbitR.Prism

omit hr in
lemma hstep(v:Fabric u)(h:v.t.ready u.plotM v.m) :
   v.t.steps u.plotM ≤ u.w0.p.T:=by
     have hm:=h.2.2.2.2.2
     unfold Quest.steps
     cases hq : v.t.tag <;> rw [hq] at hm <;> first|exact Nat.zero_le _| skip
     next b i=>
       have hp:i< u.w0.p.T:=hm.2
       cases b <;> first | exact le_rfl | exact hp
lemma umbrella (v:Fabric u)(he:v.Good)(hu:v.activeR)(h:Promised u p (v.c 14 0))
       (j:ℕ) (hh:j<heightR (pr p v)) :
       let e:=pr p v
       ∀ y∈u.D.P, u.D.Voice (e.stationE j) y (hole 1 0) (u.D.high (e.stationE j)) 0 (e.paintE j y):=by
       intro e y hy
       have hm:0<v.m:=by
          have hq:=hu; unfold Fabric.activeR Net.onQ at hq
          by_contra hn; simp [Nat.eq_zero_of_not_pos hn] at hq
       let f:OrbitV u:=⟨e.vale,e.euro j,e.across⟩
       have hx:f.m+1=v.m:=by change v.m-1+1=_; omega
       have hz:e.heightR≤v.t.steps u.plotM:=by
           unfold heightR;split;exact le_rfl;exact Nat.zero_le _
       have hT:j<u.w0.p.T:= lt_of_lt_of_le hh (hz.trans (TrustQ.hstep v he.2))
       have hF:f.estate:=by
          have hL:=he.1;obtain ⟨h1,h2,h3,h4,h5,h6⟩:=he.2
          exact ⟨by omega,h1,le_rfl,by change v.t.i+f.m≤u.plotM.roof;omega,rfl,hT⟩
       have hJ:=hr.ownsV f hF
       have ht:= (hr.owns v he).endUnits _ (Or.inl (show (14:ℕ)=14 from rfl))
       have hk:u.D.W (f.channel 17 0)+u.D.D (v.c 14 0) ≤ u.D.W (v.c 14 0):=by
          rw [Vessel.OrbitV.Counsel.costZ,Stone.D,Stone.W]; exact Age.renewal hx.le
       have hv := (h.sooner hJ.unitV.stage hk ht).old.ε f hF rfl
       rw [paintE,ite_eq_left (show j<e.heightR from hh)]
       have hh:e.s.roll e.vale= forecast u.plotM e.vale:=vault _ _ (show e.vale<e.s.m from by change f.m<v.m; omega)
       rw [hh]; exact hv y hy

lemma terrarium (v:Fabric u)(he:v.Good)(h:Promised u p (v.c 14 0)):
    ∃ f,v.Efine p f:=by
       let e:=pr p v
       have hx:= hr.upK v he
       have ht:=hx.he.season
       by_cases hu:v.activeR
       · obtain ⟨f,g,hf⟩:=hr.sovereign v he hu h
         have hh : Court e f g:=by
             refine ⟨hf,hx.hC,?_ ,?_ ,fun _ j hj=>hr.umbrella v he hu h j hj⟩
             · apply (TrustQ.promiseE h (show 5<(10:ℕ) by omega) (by omega) (by omega)
                            (ht.midUnits hu _ _ (Or.inr ⟨rfl,Or.inl (by omega)⟩)).stage).wick
             intro hk
             have ha:= (ht.midUnits hu 13 0 (Or.inr ⟨rfl,Or.inr ⟨rfl,(glacial v).2 hk⟩⟩))
             exact ((TrustQ.promiseE h (show 5<(13:ℕ) by omega) (by omega) (by omega) ha.stage).old.ω v he hu hk rfl)
         exact ⟨_,hh.plants hx⟩
       exact ⟨_,hx.water hu hr.capdraw⟩

end TrustQ
end
end ExactDerandomization.Umbra

end

section

namespace ExactDerandomization.Umbra
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Vessel Gamut
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Elect
namespace TrustQ
variable {p:MintV}{k:ℕ}(ht:TrustQ u p k)
include ht
open Ferry Basket
abbrev bread(p:MintV)(v:OrbitV u)(i:ℕ):Basket.Sack u:= ⟨v,p,i,Codex.coins3 p u.r, PrintV.shell u.r p u.v⟩
lemma sunken(v:OrbitV u) (i:ℕ)(hi:i<Age.L v.m)(hv:v.estate)(he:v.works):
     Ferry.TorchE (bread p v i):=by
        let s:= bread p v i
        have hs:= ht.ownsV v hv
        have hx:=hs.pred0 hi he
        have hz:s.wallet+s.c ≤ u.v.slope:= ht.plan.funds.h9
        refine ⟨⟨hs,he,hi,le_trans (Nat.le_add_right ..) hz,?_,ht.pearlV v 5 i hx.stage (by omega)
                                                                                          (by intro i;omega)⟩,rfl,hz,rfl⟩
        have hh:=GoodF.estimated p u.r u.v; have hl:GoodF.hour p u.r≤ s.c:=hh.2.2.1
        have hM:=Cambria.Era.billed u.r; have hM0:Cambria.Era.tariff u.r ≤ s.c:=le_trans (Nat.le_add_right ..) hl
        exact ⟨hM.2.2.trans hM0,hM.1.trans hM0,hM.2.1.trans hM0⟩

lemma relicV(v:OrbitV u)(i:ℕ)(hi:i<Age.L v.m)(hv:v.estate)(he:v.works)
   (hh:Promised u p (v.channel 5 i)):Ferry.Wells (bread p v i):=by
      have hb:=ht.sunken v i hi hv he
      have hp:= hb.may.hc
      have hc:= hp.pred0 hi he
      refine ⟨hb,?_,?_,?_⟩
      · intro a ha hV
        have hj:=ht.ownsV a ha
        have hs:FullV u p (a.channel 17 0):=by
           apply hh.sooner hj.unitV.stage _ hc
           rw [show u.D.D (v.channel 5 i)=gap v.m i from Vessel.OrbitV.Counsel.heightZ ..,
             show u.D.W (v.channel 5 i)=Age.weight v.m 5 i from Vessel.OrbitV.Counsel.costZ ..,Vessel.OrbitV.Counsel.costZ]
           exact Age.renewal (show a.m+slackT v.m 5 i ≤ v.m from hV)
        exact hs.old.ε a ha rfl
      · intro a ha hV
        have hj:=(ht.owns a ha).endUnits _ (Or.inl (show (14:ℕ)=14 from rfl))
        exact (hh.sooner hj.stage ((Vessel.OrbitV.Counsel.foreign (v := v)) a hV _ _) hc).old.R0 a ha rfl
      intro a ha hV ht' ho
      obtain ⟨j,hj⟩:=ho
      have hx:= (ht.owns a ha).endUnits 16 (Or.inr (Or.inr (Or.inr ⟨rfl,ruddy a ht' hj⟩)))
      exact (hh.sooner hx.stage ((Vessel.OrbitV.Counsel.foreign (v := v)) a hV _ _) hc).old.IN a ha ht' ⟨j,hj⟩ rfl

lemma treasuryV (v:OrbitV u) (i:ℕ)(hi:i<Age.L v.m)(hv:v.estate)(he:v.works)
   (hh:Promised u p (v.channel 5 i)) (x:ℕ)(hx:x∈u.D.P):
    v.Earn p i x:=by
       have hb:= ht.relicV v i hi hv he hh
       have hp:=ht.ownsV v hv
       apply hb.cockpit x hx
       intro j hj
       change i=j+1 at hj; have hk:j<Age.L v.m:=by omega
       have hm:u.D.W (v.channel 5 j)+u.D.D (v.channel 5 i) ≤ u.D.W (v.channel 5 i):=by
            rw [Vessel.OrbitV.Counsel.costZ,Vessel.OrbitV.Counsel.heightZ,Vessel.OrbitV.Counsel.costZ,hj]
            exact Age.oldpay (by omega) (by decide) (by decide)
       have ha:=hh.sooner (hp.pred0 hk he).stage hm (hp.pred0 hi he)
       exact ha.old.ζ v hv he j hk rfl x hx

lemma auraV (v:OrbitV u)(hv:v.estate)(h:Promised u p (v.channel 17 0)):
    v.FEnd:=by
       have hs:=ht.ownsV v hv
       have hx:=hs.unitV
       apply hs.knownEnd ht.plan.funds.he (ht.pearlV v 17 0 hx.stage (by omega)
                                                                        (by intro i;omega))
       intro hb j hj
       have hi:j<Age.L v.m:=by omega
       have hm:u.D.W (v.channel 5 j)<u.D.W (v.channel 17 0):=by
            rw [Vessel.OrbitV.Counsel.costZ,Vessel.OrbitV.Counsel.costZ]
            exact (Age.endbirth hj (by decide) (by decide) (by decide)).2
       exact (h _ (hs.pred0 hi hb).stage hm).old.ζ v hv hb j hi rfl

lemma earned {a:ℕ}(h:Promised u p a):
    Covenant u p a := by
       refine ⟨fun v hp he i hi hm=> ht.stara v i hp he hi (hm.symm ▸ h),
               fun v hp he i hi hm=> ht.starb v i hp he hi (hm.symm ▸ h),
               fun v hp he hm=> ht.stard v hp he (hm.symm ▸ h),
               fun v hp he hQ hm=> ht.deputed v (hm.symm ▸ h) hp he hQ,
               fun v hp he hQ hm=> ht.starR v (hm.symm ▸ h) hp he hQ,
               fun v hp hm=> ht.terrarium v hp (hm.symm ▸ h),
               fun v hp hx he hm=> ht.staE v (hm.symm ▸ h) hp hx he,
               fun v he hp i hj hm=> ht.treasuryV v i hj he hp (hm.symm ▸ h),
               fun v hp hm=> ht.auraV v hp (hm.symm ▸ h)⟩
/-- full version closure. -/
theorem coverage (u0:ℕ) (hx:u.D.active u0):
    FullV u p u0:=by
      have hh (j:ℕ):∀ i,u.D.W i=j→ u.D.active i→FullV u p i:=by
         induction j using Nat.strong_induction_on with
         | h j ih=>
           intro i hi he
           have hp:Promised u p i:= fun b hb hx=> ih _ (hi ▸hx) b rfl hb
           have hg:=ht.earned hp
           have hm:= ht.chart.chamber he hp.seeking fun b hb hx _=> (hp b hb hx).wick
           exact ⟨hg,hm,Covenant.orchard ht hg he⟩
      exact hh _ u0 rfl hx

end TrustQ
end
end ExactDerandomization.Umbra

end

section

namespace ExactDerandomization.Umbra
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Night Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Vessel Gamut
noncomputable section
open scoped Classical
variable {q w h:ℕ}
open Elect
namespace Scope
variable (p:MintV) (r:Rock q w h) (v:Tags)
abbrev selfS := Codex.pages p r v
abbrev Dscope(x:Word):Line (q:=q) (w:=w) (h:=h):=⟨r,v,selfS p r v,x⟩
abbrev prog0 :Cog:=Mold.woven r v (selfS p r v)
def cosmos(x:Word)(i:ℕ):ℕ:=
     enc (Foil.kit 17 (r.w.top (r.B x),0) (bitV (prizep (r.B x) (r.B x))) i)
abbrev request (x:Word)(i t:ℕ):ℕ:=post (cosmos r x i) 1 0 t
abbrev U (x:Word):ℕ:= Night.fRock r v x+ (2:ℕ)^charge v.slope (planets r x) (Moon.T r v x)
abbrev shield(x:Word):ℕ:= Dome.glove Dome.clearG (r.camp x)
def study(t:ℕ)(x:Word)(i:ℕ) : Grid.Job:=((U r v x,request r x i t),(0,shield r x))
def chop0(f:PT Grid.Job Site)(x:Word)(i t:ℕ):ℤ:=dec (f x (study r v t x i)).1
def dustF(f:PT Grid.Job Site)(j:ℕ)(x:Word)(i:ℕ):ℤ :=
   ∑ t∈range j,(chop0 r v f x i t)*(2:ℤ)^(6-t)
abbrev solve(f:PT Grid.Job Site)(x:Word)(i:ℕ):ℕ:= (dustF r v f 7 x i).toNat

lemma cosmosK:Kn (cosmos r):=by
   have hp:= r.BKn (α:=ℕ)
   let s:=(hp.tuple (hp.tuple (Kn.fix ((0,0):Rill.History)))).tuple (Kn.fix ((5,0,false):ChoiceX))
   exact Kn.wash.comp ((Kn.fix _).tuple (((topK _ hp).tuple (Kn.fix _)).tuple (s.tuple Kn.identity)))
lemma UK {α}[Wire α]:Kn (fun x (_:α)=>U r v x):=by
    have hf:Kn (fun x (_:α)=>(2:ℕ)^charge v.slope (planets r x) (T r v x)):=by
         convert ((stationK r v (α:=α)).power v.slope).times (upclock r (v.slope*v.slope)) using 1
         ext x a; rw [← pow_mul,← pow_add]; congr 1; unfold charge; ring
    exact (Night.fRockK r v).add hf
lemma studyK(t): Kn (study r v t):=by
    let a := Kn.wash.comp ((cosmosK r).tuple (Kn.fix (hole 1 0)))
    let q:=Kn.wash.comp (a.tuple (Kn.fix t))
    have hp:= Kn.wash.comp ((r.campK (α:=ℕ)).tuple (Kn.fix clearG))
    exact ((UK r v).tuple q).tuple ((Kn.fix 0).tuple hp)
lemma shake {f:PT Grid.Job Site}(hf:Kn f):Kn (solve r v f):=by
    have hs(j:ℕ):Kn (dustF r v f j):=by
       induction j with
       | zero=>have hh:dustF r v f 0=fun _ _=>0:=by ext; simp [dustF]
               exact hh ▸ Kn.fix _
       | succ j ih=>
          have he:= (Kn.unpack (α:=ℤ)).comp (hf.comp (studyK r v j)).left
          convert ih.plusZ (he.prodZ (Kn.fix ((2:ℤ)^(6-j)))) using 1
          ext x a;unfold dustF; rw [sum_range_succ]; rfl
    exact (hs 7).topNat

structure Sane (r:Rock q w h)(p:MintV)(v:Tags)(k:ℕ) : Prop where
    funds:Codex.Fortune r p v k
    stake:6 ≤ v.extra
    proofM :∀ x, (Dscope p r v x).Chart

abbrev Page(p:MintV)(r:Rock q w h)(v:Tags)(x:Word)(s:Pool (r.n x)):OrbitV (Dscope p r v x):=
   ⟨r.w.top (r.B x),prizep (r.B x) (r.B x),s⟩
namespace Sane
variable {r:Rock q w h} {p:MintV}{v:Tags}{k:ℕ} (he:Sane r p v k)
include he
omit he in
lemma stableQ (x:Word) (s:Pool (r.n x)):
   let u:=Dscope p r v x
   let P:=Page p r v x s
   P.m=u.limitM ∧ P.estate:=by
       intro u P
       exact ⟨rfl,le_rfl,(r.matter0 x).reachesB⟩
lemma swept(x:Word): TrustQ (Dscope p r v x) p k:=⟨he.funds,rfl,he.proofM x⟩
omit he in
lemma date0 (x:Word)(s:Pool (r.n x)):
   cosmos r x (r.printid x s)=(Page p r v x s).channel 17 0:=rfl
abbrev stalkC (r:Rock q w h)(x:Word)(s:Pool (r.n x)):ℕ:= cosmos r x (r.printid x s)
lemma suiteV(x:Word)(s:Pool (r.n x)):
    (Dscope p r v x).D.Suite (stalkC r x s) :=
     ((he.swept x).ownsV (Page p r v x s) ((stableQ (r := r) (p := p) (v := v)) x s).2).unitV

lemma calend (x:Word)(s:Pool (r.n x)):
    6 ≤ (Dscope p r v x).D.high (stalkC r x s):=by
      let u:= Dscope p r v x
      let a:= stalkC r x s; let D:=u.D
      have hz := he.suiteV x s
      have hm :D.W a ≤ planets r x:= by
           have ht:=he.proofM x
           exact Orbit.licensedW _ ((Line.Chart.auth (u := u) a).1 hz.stage)
      have hs:= he.stake
      change 6  ≤  T r v x-v.slope*D.W a
      have hh:=Nat.mul_le_mul_left v.slope hm
      rw [T]; rw [Nat.mul_add]; omega

lemma money0 (x:Word)(s:Pool (r.n x)) (i:ℕ)(hi:i ≤ 6):
   let u:= Dscope p r v x; let Q:= request r x (r.printid x s) i
   (2:ℕ)^(u.D.F.meter Q) ≤ U r v x ∧ u.D.F.limit ≤ U r v x:=by
      intro u Q
      have hs:=he.proofM x; let a:=stalkC r x s
      have h0:=he.suiteV x s
      have hm:u.D.W a ≤ planets r x:= Orbit.licensedW _ ((Line.Chart.auth (u := u) a).1 h0.stage)
      have ht:i ≤ T r v x:=cap_time r v x u.prog a i (hi.trans (he.calend ..))
      refine ⟨le_trans (b:=(2:ℕ)^charge v.slope (planets r x) (T r v x)) ?_ (Nat.le_add_left ..),
                                                                Nat.le_add_right ..⟩
      apply Nat.pow_le_pow_right (by omega)
      rw [h0.shape.rateC]
      rw [show u.D.l.book Q=⟨u.D.W a,i⟩ from h0.shape.bookB _ _ _]
      unfold charge; dsimp only; change v.slope*i+v.slope*v.slope*u.D.W a ≤_; gcongr

def Agent(f:PT Grid.Job Site)(r:Rock q w h)(p:MintV)(v:Tags):Prop:=
   ∀ {x U F q a b}, let c:=prog0 p r v;
                    (2:ℕ)^(Fare.meter F q)  ≤  U → Fare.limit F ≤ U → Boots x F c q c a b →
                                                    f x ((U,q),a)=b
lemma bells0 (x:Word)(s:Pool (r.n x))(hS:r.P.Space){
   f:PT Grid.Job Site}(hf:Agent f r p v):
       let m:=r.matter0 x
       let Z:=m.oracleV s m.i
       |(dustF r v f 7 x (r.printid x s):ℝ)- (2:ℝ)^6*Z| ≤ 2:=by
       intro m Z
       let u:= Dscope p r v x; let a:=stalkC r x s; let D:=u.D
       let P:=Page p r v x s
       have hv:=he.suiteV x s
       have hs:=he.proofM x
       have hZ : m.i ∈ u.D.P:=by
            have hh:=hs.sc
            have hq:= hh.ids (r.B x) le_rfl (m.origin hS)
            exact mem_range.2 ((mem_range.1 hq).trans (by change r.n x<r.n x+1; omega))
       have hk:P.FEnd:= ((he.swept x).coverage a hv.stage).old.ε P ((stableQ (r := r) (p := p) (v := v)) x s).2 rfl
       obtain ⟨w,hb,hP⟩:= hk m.i hZ
       have ht:Checked w Z (u.D.high a):=by
            change Checked w (Z/(2:ℝ)^0) (u.D.high a) at hb; simpa only [pow_zero,div_one] using hb
       have h6 :6 ≤ u.D.high a := he.calend x s
       have hh:dustF r v f 7 x (r.printid x s)=w 6:=by
            unfold dustF; rw [←sumsign w 6]; apply sum_congr rfl
            intro i hi; have hi0:i≤6:=Nat.le_of_lt_succ (mem_range.1 hi)
            have heE:= hP i (hi0.trans h6) Dome.clearG u.D.cleared
            have hv:= he.money0 x s i hi0
            have hp:=hf hv.1 hv.2 heE
            have hl: f x (study r v i x (r.printid x s))=(enc (dsign w i), Dome.glove Dome.clearG m.i):=by
                 unfold study shield; rw [r.camps x]; exact hp
            unfold chop0; rw [hl]; dsimp only; rw [dec_round]
       rw [hh]; exact ht.2 _ h6
end Sane

end Scope
end
end ExactDerandomization.Umbra

end

end OAI
