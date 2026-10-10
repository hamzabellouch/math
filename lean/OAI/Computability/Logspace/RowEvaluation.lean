import OAI.Computability.Logspace.EstimatorMachine
import OAI.Computability.Logspace.EstimatorParameters
import OAI.Computability.Logspace.QueryCombinators

namespace OAI

/-!
Evaluation of row scores, ranks, and compressed numerical values.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Cambria
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon
open SiteX SiteX.Line Terrain Terrain.Bank Glass Glass.Rod Helix.Was
open Arena Fret.Seats Pier Arena.Flash
noncomputable section
open scoped Classical

abbrev Hull := (ℕ×ℕ×ℕ) × (History × Issue)
abbrev Helm := (ℕ×ℕ) × History × (ℕ×Arch)

abbrev Surf:=Hull×Helm
namespace Surf
abbrev mx (t:Surf):=t.1.1.1
abbrev days(t:Surf):=t.1.1.2
abbrev chartQ(t:Surf):=t.1.2.1
abbrev dye(t:Surf):=t.1.2.2
abbrev A (t:Surf):=t.2.1
abbrev U (t:Surf):=t.2.2.1
abbrev sunset (t:Surf):=t.2.2.2
abbrev windC (t:Surf)(y:ℕ) :ℕ:= t.sunset.2.1*y+t.sunset.2.2
abbrev priceC (t:Surf)(h:ℕ): Aide:= ((t.A.1,h-1),(decide (t.U.1≠0),t.U),t.sunset)
def green(t:Surf)(b:Bool)(n x:ℕ):Bool:=
    if b then Print.shoot n t.days.1 x t.dye.1 else Print.shoot n t.days.2 x t.dye.2.1
def heatC (t:Surf)(b:Bool)(n x:ℕ):Bool:=
    Print.touched b n t.days.1 t.days.2 x t.chartQ.1 t.chartQ.2 t.dye
def flareQ (t:Surf)(b:Bool)(n x:ℕ):Bool:= t.green b n x && t.heatC b n x
def frontC (t:Surf) (n x:ℕ):Bool := decide (x<t.mx) && t.flareQ true n x
def finalC (t:Surf)(n x:ℕ):Bool:= t.flareQ false n (t.windC x)

namespace Prep
variable {α}[Wire α]{n i:PT α ℕ}{s:PT α Surf}
lemma windK (hp:Kn s)(hr:Kn i):Kn (fun x a=> (s x a).windC (i x a)):=
    let p:= hp.right.right.right.right
    (p.left.times hr).add p.right
lemma headF (hn:Kn n)(hi:Kn i)(hs:Kn s) (b:Bool):Kn (fun x a=> (s x a).green b (n x a) (i x a)):=by
   have h:=hs.left.right.right; have hf:=hs.left.left.right
   cases b
   · exact Print.shootK hn hf.right hi h.right.left
   exact Print.shootK hn hf.left hi h.left
lemma chapter (hn:Kn n)(hi:Kn i)(hs:Kn s) (b:Bool):Kn (fun x a=> (s x a).flareQ b (n x a) (i x a)):=
    let h:=hs.left.left.right
    let q:=hs.left.right
    Print.both (headF hn hi hs b) (Print.touchedK b hn h.left h.right hi q.left.left q.left.right q.right)
lemma facet (hn:Kn n)(hi:Kn i)(hs:Kn s): Kn (fun x a=> (s x a).frontC (n x a) (i x a)):=
   Print.both (hi.lt hs.left.left.left) (chapter hn hi hs true)
lemma aideK (hs:Kn s) (hi:Kn i): Kn (fun x a=> (s x a).priceC (i x a)):=by
   have h:= hs.right.right.left; let k:= GK.decideK (GK.notG (GK.eqG h.left (Kn.fix 0)))
   exact (hs.right.left.left.tuple hi.pred).tuple ((k.tuple h).tuple hs.right.right.right)
end Prep
end Surf

abbrev PondQ:=Cub ℕ Surf
variable {q w h:ℕ}

namespace Hood
variable (r:Rock q w h)

abbrev codeE(x:Word)(t i j:ℕ):ℕ:= unitN r x (walkq (Scheme.inside t) j true i)
def spill (x:Word)(t i:ℕ):ℕ → ℕ
   | 0=>0
   | j+1=> if codeE r x t i j=0 then spill x t i j else j+1
lemma ankle {x:Word}{t i m:ℕ}:spill r x t i m  ≤  m:=by
    induction m with
    | zero=>rfl
    | succ m ih=> unfold spill; split;omega;rfl
variable {α}[Wire α]{i t:PT α ℕ}
lemma bloomK (he:Kn t)(hv:Kn i)(j):Kn (fun x a=>codeE r x (t x a) (i x a) j):=
    let k:= ((Kn.unpack (α:=History)).comp he).right
    (unitKN r).comp (((k.tuple (Kn.fix j)).tuple (Kn.fix _)).tuple hv)
lemma fledK (he:Kn t)(hv:Kn i)(j): Kn (fun x a=> spill r x (t x a) (i x a) j):=by
    induction j with
    | zero=> exact Kn.fix 0
    | succ j ih=> exact (bloomK r he hv j).cond_eq (Kn.fix 0) ih (Kn.fix _)

def saute (v:PondQ)(g:ℕ):Cog:=
   Arena.Flash.search ⟨_,fledK r (v.runs.comp Kn.first).right.left.left Kn.next g⟩

lemma codePos {x:Word}{t i j y:ℕ}:
   codeE r x (Was.atom t) i j=y+1↔Flight r x t j i y:=by
    have hg:= travel r x t j true i y
    unfold stopped at hg
    have hf: Scheme.inside (Was.atom t)=t:=by simp [Scheme.inside,Was.atom,hole]
    unfold codeE
    rw [hf, ← show (if unitN r x _=0 then none else some (unitN r x _-1))=some _↔Flight r x t j i y from hg]
    split <;> grind
lemma lastE {x:Word}{t i j m:ℕ}(hm:j < m):
   spill r x (Was.atom t) i m=j+1↔ ∃ y,Flight r x t j i y:=by
    induction m with
    | zero=>omega
    | succ m ih=>
      unfold spill
      cases he:codeE r x (Was.atom t) i m with
      | zero=>
        by_cases hi:j=m
        · simp only [ite_true]; have hp:=ankle r (x:=x) (m:=m) (t:=Was.atom t) (i:=i)
          refine iff_of_false (by omega) ?_
          rintro ⟨y,h⟩; have hc:=(codePos r).2 h; rw [hi,he] at hc; omega
        simpa only [ite_true] using ih (by omega)
      | succ y=>
        rw [ite_eq_right (by omega: y+1 ≠ 0)]
        have ha:=(codePos r).1 he
        refine ⟨fun e=>⟨y,(show j=m by omega) ▸ ha⟩,?_⟩
        rintro ⟨y',ht⟩
        have hp:=fly_pair r ha ht; omega
lemma dawn {x:Word}{t i m:ℕ}: spill r x (Was.atom t) i m=0↔∀ j < m,∀ y,¬ Flight r x t j i y:=by
   refine ⟨fun h j hj y he=>?_,fun h=>?_⟩
   · have ht:= (lastE r hj).2 ⟨y,he⟩; omega
   have hz:= ankle r (x:=x) (m:=m) (t:=Was.atom t) (i:=i)
   by_contra hc
   generalize he: spill r x (Was.atom t) i m=k at *
   cases k with
   | zero=> contradiction
   | succ k=> obtain ⟨y,hp⟩:= (lastE r (by omega)).1 he; exact h k (by omega) _ hp
end Hood

namespace Keel
open Surf

variable (r:Rock q w h)
def early (p:PondQ):Cog:=Flash.search
     ⟨_,Kn.wash.comp (Surf.Prep.facet (r.nKn) Kn.next (p.runs.comp Kn.first))⟩
def foilT (p:PondQ):Sight:=⟨_,p.runs.right.left.left⟩
def quarry (p:PondQ):Sight:=⟨_,p.runs.right.left.right⟩
def cream(x:ℕ):ℕ:= if x=0 then 0 else x+1
lemma creamK{α}[Wire α]{f:PT α ℕ}(h:Kn f):Kn (fun x a=>cream (f x a)):=
      h.cond_eq (Kn.fix 0) (Kn.fix 0) h.succ
def renew (f:Sight):Cog:=.seq (Dome.Bullet.snap f)
                  (etch (α:=ℕ) (fun _ a=>cream a.2) (creamK Kn.next))
abbrev Tor(g:Sight) : Flag:=⟨_,(g.runs.comp (tokenK.left.comp Kn.first)).eq (Kn.fix 0)⟩
def broom(p:PondQ) (m:ℕ) : Cog :=
    .bif (Tor (quarry p)) (Hood.saute r p m) (renew (quarry p))
def frontQ(p:PondQ)(m:ℕ): Cog:= demand (early r p) (broom r p m)

section
variable {u:Line (q:=q) (w:=w) (h:=h)}
variable (g:PondQ){t x s c:ℕ}
variable (he:u.D.Suite t)(hp:2 ≤ c)(hx:x∈u.D.P)
variable {q:Surf}(hf:g.f u.x s=q)
include he hp hx hf
lemma answer :
    (u.D.chord t x s).rite c (early u.r g) (enc (q.frontC u.n x)) := by
   refine found u.D he hx hp ?_ (seal_bit u.D he hp (q:=s) _)
   change enc ((g.f _ _).frontC u.n x)=_
   rw [show g.f u.D.x _=q from hf]
lemma tome {b:ℕ}(hk:q.A.2=0)
     (hr: StampX s (Hood.spill u.r u.x q.A.1 x b) u.D t c):
   (u.D.chord t x s).rite c (broom u.r g b) (Hood.spill u.r u.x q.A.1 x b):=by
    intro n hn
    apply Lot.Mane.yes _ ((found u.D he hx hp ?_ hr) _ hn)
    · change decide ((g.f u.x ((Scheme.token (postcard s 0)).1)).A.2=0)=true
      simp [token,postcard,hf,hk]
    change Hood.spill u.r u.x (g.f u.x s).A.1 x b=_
    rw [hf]
lemma summons {b m y z:ℕ}(hh:u.D.W b+u.D.D t ≤ u.D.W t) (hk:q.A.2=hole b m)
     (hv:u.D.swears (bell b m 0) x z)(hs:StampX s z u.D t c)(hr:StampX s (cream z) u.D t c)(hc:q.A.2 ≠ 0):
   (u.D.chord t x s).rite c (broom u.r g y) (cream z):=by
    intro n hn
    have hf' : (quarry g).f u.D.x s=hole b m:=
                          (congrArg (fun a:Surf=>a.A.2) hf).trans hk
    have hu:= Bullet.copy u.D he hp hx hh hf' hs hv n hn
    have hm := he.pit hx s _ hn
    refine Lot.Mane.no ?_ (.seq hu (etches _ _ (i:=z) rfl hu.spots.2 (plight hr hm (by omega))))
    change decide ((g.f u.x ((Scheme.token (postcard s 0)).1)).A.2=0)=false
    simp [token,postcard,hf,hc]
end
end Keel

end
end ExactDerandomization.Cambria

end

section

namespace ExactDerandomization.Cambria
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Terrain Terrain.Bank Glass Glass.Rod
open Arena Fret.Seats Pier Arena.Flash
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Mica
open Surf
variable (r:Rock q w h)
def cube (b:Bool) (q:Surf):NoteM :=
    let s:=enc q.dye
    (q.sunset.2,enc (if b then trail q.days.2 s else measureL q.days.1 q.days.2 q.chartQ.1 q.chartQ.2 s))
lemma cubeK {α}[Wire α]{p:PT α Surf}(h:Kn p)(b:Bool):Kn (fun x a=>cube b (p x a)):= by
    have he:=h.right.right.right.right
    have hp:=h.left.left.right
    have hv:=h.left.right
    have hm:=Kn.wash.comp hv.right
    cases b
    · exact he.tuple (Kn.wash.comp ((Kn.fix _).tuple (hp.tuple (hv.left.tuple hm))))
    exact he.tuple (Kn.wash.comp ((Kn.fix _).tuple (((Kn.fix _).tuple hp.right).tuple ((Kn.fix _).tuple hm))))
def giz (b:Bool)(q:PondQ):Cub ℕ (ℕ×ℕ×NoteM):=
    let h:=q.runs.right.right.left
    ⟨_,h.left.tuple (h.right.tuple (cubeK q.runs b))⟩
abbrev clue (q:PondQ)(b:Bool):Cog:= Bullet.snap (garnish (giz b q))
abbrev invite (q:PondQ):Cog:= demand (clue q true) (clue q false)
def leafC (g:PondQ):Cog:= by
    let h:=g.runs.comp (Kn.first (β:=ℕ))
    exact search ⟨_,Kn.wash.comp (Surf.Prep.chapter r.nKn (Surf.Prep.windK h Kn.next) h false)⟩
abbrev ole (g:PondQ):Sight:=⟨_,g.runs.right.right.left.left⟩
def moth (g:PondQ):Cog := Cog.bif (Keel.Tor (ole g)) (leafC r g) (invite g)
abbrev host (r:Rock q w h)(g:PondQ)(c:ℕ):Gate:= ⟨Keel.frontQ r g c,c,Keel.foilT g,moth r g⟩
section
variable {u:Line (q:=q) (w:=w) (h:=h)}
variable (g:PondQ)
variable (s:Surf)

structure LiftQ (u:Line (q:=q) (w:=w) (h:=h))(s:Surf)(a:ℕ)(y:ℕ):Prop where
     launch : y∈ u.D.P
     attr : s.windC y∈ u.D.P
     dual:u.D.dual s.sunset.1 0
     bond:u.D.W (cell s.sunset.1)+u.D.D a ≤ u.D.W a
     aims:u.D.curve s.sunset.1 0 true y=some (s.windC y)

abbrev Stars:= Option History
inductive Partner(u:Line (q:=q) (w:=w) (h:=h))(s:Surf)(a:ℕ)(x:ℕ):Stars → Prop
   | soil (h:s.U.1=0) (hg:LiftQ u s a x) : Partner u s a x (some (0,x))
   | leaf {f:Stars}(h:s.U.1≠0)
          (he:u.wick0.Veil u.torch s.U.1)
          (hq:∀ b,u.wick0.Ok (cube b s))
          (hp:u.D.W s.U.1+u.D.D a ≤ u.D.W a)
          (hd:u.D.D s.U.1  ≤ 2*u.D.D a)
          (ht:u.eye.Flora u.torch.p s.U.1 s.U.2 x f)
          (hl:∀ {i y},f=some (i,y)→LiftQ u s a y): Partner u s a x f
def census (s:Surf)(b:Bool)(n:ℕ)(e:Stars): Bool:=
    match e with
    | none=>false
    | some (_,y) => if b then s.green false n (s.windC y) else s.heatC false n (s.windC y)
def exitE (s:Surf)(n:ℕ)(e:Stars):Bool:= census s true n e && census s false n e
lemma exitJ (s:Surf)(n i j:ℕ):exitE s n (some (i,j))=s.finalC n j:=rfl

variable {g s a x c i}
lemma glow0 (b:Bool)(f:Pane){m:ℕ}(h:s.windC m∈ u.D.P):
      u.torch.lit u.D.x (cube b s) m f=(census s b u.n (some (0,m)),f):=by
    have he:s.windC m  ≤  u.n:=Nat.le_of_lt_succ (mem_range.1 h)
    have hr: ray0 (u.torch.port u.D.x) (cube b s).1 m=s.windC m:=min_eq_right he
    unfold Harp.lit; rw [hr]; cases b
    · change Helix.Torch.lamp u.r u.x ((_,_),f)=_
      simp [lamp,ray,cube,census,Surf.heatC,measureL]
    · change Helix.Torch.lamp u.r u.x ((_,_),f)=_
      simp [Helix.Torch.lamp,Helix.Torch.ray,cube,census,Surf.green,trail]
lemma theEnd (hr:u.D.Suite a)(hx:x∈u.D.P)(hf:g.f u.x i=s)(hv:2 ≤ c){f:Stars}
     (hz:Partner u s a x f):
  (u.D.chord a x i).rite c (moth u.r g) (enc (exitE s u.n f)):=by
   cases hz with
   | soil h hg=>
     intro n hn
     refine Lot.Mane.yes ?_ ((found u.D hr hx hv ?_
                          (seal_bit u.D hr hv (q:=i) (exitE s u.n (some (0,x))))) n hn)
     · change decide ((g.f u.x ((token (postcard i 0)).1)).U.1=0)=true
       simp only [token,postcard,dec_round,hf,h]; rfl
     change enc ((g.f u.x i).finalC u.n x)=_
     rw [hf]; rfl
   | @leaf f hm he hq hp hd ht hl=>
     have hh (b:Bool):(u.D.chord a x i).rite c (clue g b) (enc (census s b u.n f)):=by
        let c0:=s.U
        have hk:(giz b g).f u.x i=(c0.1,c0.2,cube b s):=
             congrArg (fun x:Surf=> (x.U.1,x.U.2,cube b x)) hf
        apply Arena.Flash.maskB hr hx hv hp he hk (hq b) ht
        cases f
        · rfl
        next p=> rcases p with ⟨j,y⟩
                 intro p h
                 exact glow0 b p (hl (show some (j,y)=some (j,y) from rfl)).attr
     have hu: (u.D.chord a x i).rite c (invite g) (enc (exitE s u.n f)):=by
        rw [exitE,← Arena.Flash.brilliant]
        apply wanted u.D hr hx hv _ _ (hh true); exact fun _=>hh false
     intro n hn
     refine Lot.Mane.no ?_ (hu n hn)
     change decide ((g.f u.x ((token (postcard i 0)).1)).U.1=0)=false
     simp only [token,postcard,dec_round,hf]; simp [hm]
end
end Mica
end
end ExactDerandomization.Cambria

end

section

namespace ExactDerandomization.Cambria
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Terrain Terrain.Bank Glass Glass.Rod
open Arena Fret.Seats Pier Arena.Flash Surf Mica
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace BadgeX
def iris : Stars → ℕ
    | none=>0
    | some z=>z.1
def portM : Stars → ℕ
    | none=>0
    | some z=>z.1+1
def pointE:Stars → ℕ
    | none=>0
    | some z=>z.2
def collect (t:Surf)(n x:ℕ)(g:Stars)(m:ℕ → Stars):Stars:=
    if t.frontC n x then match g with
    | none=>none
    | some (k,i)=>match m i with
                  | none=>none
                  | some (_,j)=> if t.finalC n j then some (k+1,t.windC j) else none
    else none
lemma iris_le (t:Surf)(n x g m): iris (collect t n x g m) ≤ portM g:=by
    unfold collect
    split; grind [iris,portM]
    cases g <;> simp [iris,portM]
lemma spark {t:Surf}{n x w z g m}(h:collect t n x g m=some (w,z)):
     t.frontC n x=true ∧ ∃ a i b j,g=some (a,i) ∧m i=some (b,j) ∧
                                                w=a+1∧ z=t.windC j∧ t.finalC n j=true:=by
    unfold collect at h
    split at h <;> try contradiction
    rename_i hc
    refine ⟨hc,?_⟩
    cases g <;> try contradiction
    next v=> rcases v with ⟨a,i⟩
             cases he:m i with
             | none=> simp only [he,reduceCtorEq] at h
             | some q=> rcases q with ⟨b,j⟩
                        simp only [he] at h
                        split at h
                        · next hv=> simp only [Option.some.injEq,Prod.mk.injEq] at h; exact ⟨_,_,_,_,rfl,he,h.1.symm,h.2.symm,hv⟩
                        contradiction

variable {u: SiteX.Line (q:=q) (w:=w) (h:=h)}

structure Crew(u:Line (q:=q) (w:=w) (h:=h)) where
    cage :CageQ
    g:PondQ
    t:Surf
    info:ℕ
    c:ℕ
    bound:ℕ
    x:ℕ
    entrance:Stars
    exit0:ℕ → Stars
namespace Crew
variable (p:Crew u)
abbrev outR := collect p.t u.n p.x p.entrance p.exit0
abbrev src := p.cage.dataN
abbrev skill (x:ℕ):=u.D.chord p.src x p.info
abbrev stationP :=p.skill p.x
abbrev host0:= host u.r p.g p.bound
abbrev lampQ := p.t.frontC u.n p.x
structure Good (p:Crew u):Prop where
    pro:p.cage.Front u
    chart:u.Chart
    capcost : 4 ≤ p.c
    ix:p.x ∈ u.D.P
    fiat:p.g.f u.x p.info=p.t
    capw : ∀ i:ℕ,i ≤ p.bound→StampX p.info i u.D p.src p.c
    caps : ∀ i:ℕ,i ≤ p.bound→u.smallQ p.cage.visN i

abbrev hitP (p:Crew u)(k:ℕ):Prop:=Liaison u.D p.x p.cage.dataN p.t.A.1 k
structure Arrived(p:Crew u) :Prop where
    stable:p.Good
    next : p.lampQ=true →
          portM p.entrance ≤ p.bound ∧ p.stationP.rite p.c (Keel.broom u.r p.g p.bound) (portM p.entrance)
    tours :∀ k i,p.lampQ=true→p.entrance=some (k,i)→p.hitP k∧u.D.curve p.t.A.1 k true p.x=some i∧
                                            Partner u p.t p.src i (p.exit0 i)

namespace Arrived
variable {p:Crew u}(hp:p.Arrived)
include hp
lemma throng : p.host0.Crest u.D p.src p.info p.c p.x
                                 (if p.lampQ then portM p.entrance else 0):=by
   let i:=portM p.entrance
   have hb:(if p.lampQ then i else 0) ≤ p.bound:=by
      split
      · next hv=> exact (hp.next hv).1
      omega
   have hs:= hp.stable
   have hg:= hs.chart.rent hs.pro.pos; have hk:=hs.capcost
   refine ⟨?_,hb,hg,hs.ix,by omega,hs.capw _ hb⟩
   have hf: win (enc p.lampQ) i=(if p.lampQ then i else 0):=by cases he:p.lampQ<;>rfl
   rw [← hf]
   apply Flash.wanted u.D hg hs.ix (by omega) (enc p.lampQ) i
           (Keel.answer _ hg (by omega) hs.ix hs.fiat)
   intro h
   exact (hp.next (by cases ht:p.lampQ; rw [ht] at h; exact False.elim (h rfl); rfl)).2

lemma wreath :
   iris p.outR ≤ p.bound ∧ p.stationP.rite p.c (p.host0.garden u.D.s) (iris p.outR):=by
    have hh:=hp.throng
    by_cases hz:p.lampQ=true
    · rw [ite_eq_left hz] at hh
      refine ⟨le_trans (iris_le ..) (hp.next hz).1,?_⟩
      cases h:p.entrance with
      | none=>
        rw [h] at hh
        change p.stationP.rite p.c _ (iris (collect _ _ _ _ _))
        rw [collect.eq_def,ite_eq_left hz,h]; exact hh.asleep
      | some s=>
        obtain ⟨k,i⟩:=s
        rw [h] at hh
        obtain ⟨he,hz0,h1⟩:=hp.tours k i hz h
        have hx:=(he.ready.swaps k he.holds p.x he.xem true i hz0).1
        have hr :portM (some (k,i))-1=k:=by simp [portM]
        have hg: win (enc (exitE p.t u.n (p.exit0 i))) (portM (some (k,i)))=iris p.outR:=by
             unfold outR collect
             rw [ite_eq_left hz,h]
             dsimp only
             cases ht:p.exit0 i with
             | none => rfl
             | some r=>
                obtain ⟨w,v⟩:=r
                rw [exitJ p.t]
                cases hn:p.t.finalC u.n v <;> simp only [hn,Bool.false_eq_true,ite_true,ite_false] <;> rfl
        have hs:= hp.stable; have hb:=hs.capcost
        rw [← hg]
        apply hh.morning (by simp [portM]) (t:=p.t.A.1) _ (hr ▸ he) (hr ▸hz0)
             (Mica.theEnd (hs.chart.rent hs.pro.pos) hx hs.fiat (by omega) h1)
        exact congrArg (fun a:Surf=>a.A.1) hs.fiat
    rw [ite_eq_right hz] at hh
    unfold outR collect; rw [ite_eq_right hz]; exact ⟨Nat.zero_le _,hh.asleep⟩

lemma paths {i:ℕ} (he:u.smallQ p.src i)
    (hv:u.D.swears (post p.src p.cage.tagop i 0) p.x (iris p.outR))
    (hr:offer u.s.pave u.x (stem p.cage.visN i (iris p.outR))=p.t.priceC (iris p.outR)):
   u.eye.Flora u.torch.p p.cage.visN i p.x p.outR :=by
    let N:=p.cage.visN; let z:=u.eye; let q:=u.torch.p
    have hb:=hp.stable; have hs:= hb.pro
    have hx:=hs.point0 hb.chart i (hs.back0 he)
    have hh: u.D.echo (u.eye.ear u.torch.p N i) p.x=iris p.outR:=by
             rw [show u.eye.ear u.torch.p N i = _ from hs.ear0 i]; exact u.D.identity hv
    cases hg:p.outR with
    | none=> apply Flora.abs; rw [hg] at hh; exact ⟨hx,hb.ix,hh⟩
    | some r=>
      obtain ⟨k,j⟩:=r
      obtain ⟨hm,a,w,b,y,hg0,hf0,rfl,rfl,ht⟩:= spark hg
      apply Flora.wet
      obtain ⟨ha,hi,hF⟩:= hp.tours _ _ hm hg0
      rw [hf0] at hF
      have H: a+1 ≤ p.bound:=by have h:=(hp.next hm).1; rw [hg0] at h; exact h
      let K:=a+1; let c:=p.t
      have hU : z.h0 q N i K=c.A.1 ∧ z.ip q N i K=a ∧ z.f0 q N i K=c.sunset.1 ∧
           z.b1 q N i K=decide (c.U.1 ≠0) ∧ z.s1 q N i K=c.U.1 ∧ z.i1 q N i K=c.U.2 ∧
                                                q.shift.f z.D.x (stem N i K)=c.sunset.2:=by
        let E:=offer u.s.pave u.x (stem N i K)
        have he:E=c.priceC K:=by rw [hg] at hr; exact hr
        change E.1.1=_∧E.1.2=a∧E.2.2.1=_∧E.2.1.1=_∧E.2.1.2.1=_∧E.2.1.2.2=_∧E.2.2.2=_
        simp [he,K,priceC]
      obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩:=hU
      have hh0 (hl:LiftQ u c p.src y):z.Point q N i K p.x w y (c.windC y):=by
         have hs':u.D.D N=u.D.D p.src:=hs.grain.symm
         have hS:=hs.price
         have HD:i=i:=rfl
         have hpost(v)(hr:u.D.W (cell v)+u.D.D p.src ≤ u.D.W p.src):u.D.W (cell v)+z.n N ≤ u.D.W N:=
              le_trans (by rw [show z.n N=u.D.D p.src from hs']; exact hr)
                 ((Nat.le_add_right (u.D.W p.src) _).trans hS)
         have he:N=N:=rfl
         refine ⟨hx,Nat.succ_ne_zero _,?_,hb.caps _ H,?_,?_,?_,hb.ix,
             (ha.ready.swaps a ha.holds _ ha.xem _ _ hi).1,hl.launch,hl.attr,?_,?_,?_⟩
         · rw [hg] at hh; exact hh
         · rw [h2]; exact hb.caps _ (by omega)
         · rw [h1,h2]; exact ⟨ha.holds,hpost _ ha.pays⟩
         · rw [h3]; exact ⟨hl.dual,hpost _ hl.bond⟩
         · rw [h1,h2]; exact hi
         · rw [h3]; exact hl.aims
         rw [h7]; exact min_eq_right (show c.windC y ≤ u.n from Nat.le_of_lt_succ (mem_range.1 hl.attr))
      cases hF with
      | soil hz hL=> exact Pond.leaf (hh0 hL) (by rw [h4,show c.U.1=0 from hz]; rfl)
      | leaf hC he hq ho hd hh hr=>
         cases hh with
         | wet ht=>
             refine Pond.born (hh0 (hr rfl)) ?_ ?_ ?_ (h':=b) ?_
             · rw [h4]; simp [show c.U.1≠0 from hC]
             · rw [h5, show z.n N = u.D.D p.src from hs.grain.symm]
               exact ho.trans ((Nat.le_add_right _ _).trans hs.price)
             · rw [h5, show z.n N = u.D.D p.src from hs.grain.symm]; exact hd
             · rw [h5,h6]; exact ht
end Arrived
end Crew
end BadgeX

end
end ExactDerandomization.Cambria

end

section

namespace ExactDerandomization.Cambria
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Terrain Terrain.Bank Glass Glass.Rod
open Arena Fret.Seats Pier Arena.Flash Surf Mica BadgeX
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Era

variable {u:Line (q:=q) (w:=w) (h:=h)}
def budget (r:Rock q w h):ℕ:=bootC r+1
def tariff (r:Rock q w h):ℕ:=budget r+powder 100+Bullet.roomS+16
lemma billed (r:Rock q w h): 4≤ tariff r∧Bullet.roomS  ≤ tariff r∧powder 100  ≤  tariff r:=by
    unfold tariff; omega
lemma educated (p:Crew u) {v:MintV}(hB:Bank.Turf v u.r u.v)
   (h:p.cage.Front u)(he:u.Chart)(hb:p.bound=budget u.r)(hc:tariff u.r ≤ p.c)
   (hu:p.x∈u.D.P)(hg:p.g.f u.x p.info=p.t):p.Good:=by
      have hM:= (he.rent h.pos).well.1
      refine ⟨h,he,(billed _).1.trans hc,hu,hg,fun i hv=>?_,fun i hv=>?_⟩
      · have hz:= lb_le_inc i
        have hs:i+2 ≤  p.c:=by rw [hb] at hv; unfold tariff at hc; omega
        unfold StampX Punct; change lb i+1 ≤ p.c*u.D.D p.cage.dataN
        nlinarith
      have hs: i+1 ≤ Bank.hx v u.r:=by rw [hb] at hv; unfold Bank.hx Bank.hu hi; unfold budget at hv; omega
      have hl:= lb_le_inc i
      have ht: i+1 ≤ u.eye.e:=hs.trans hB.cost0
      rw [h.grain] at hM; change lb i ≤ u.eye.e*u.D.D p.cage.visN; nlinarith
lemma orn {g:Surf}{v x:ℕ}(h:u.Chart)(hk:u.D.W 0+u.D.D v ≤ u.D.W v)(hx:x∈u.D.P)
     (hp:g.sunset=(Was.atom 0,1,0)): LiftQ u g v x :=by
   have hs:g.windC x=x:=by simp [windC,hp]
   have he:x ≤ u.n:=Nat.le_of_lt_succ (mem_range.1 hx)
   refine ⟨hx,hs.symm ▸ hx,?_,?_,?_⟩
   · rw [hp]; exact (Line.Chart.voteRoot (u := u)) (Nat.zero_le _) (Nat.zero_le _)
   · rw [hp]; exact (show u.D.W (cell (Was.atom 0))+_≤_ from by
                                   rw [show cell (Was.atom 0)=0 from by simp [cell,Was.atom,hole]]; exact hk)
   rw [hs,hp]
   exact h.basic0 (show Was.Flight u.r u.x 0 0 x x by simp [Was.Flight,he]) (Nat.zero_le _) (Nat.zero_le _)
lemma oust {g:Surf}{v x i:ℕ}(h:u.Chart){p:MintV}(hB:Turf p u.r u.v)
     (hk:u.D.W 0+u.D.D v ≤ u.D.W v)(hx:x∈u.D.P)
     (hi:i<u.w0.p.M) (hp:g.sunset=(Was.atom (3+i),u.w0.p.M,i))
     (hf:radix u.w0.p.M x i∈u.D.P):
   LiftQ u g v x:=by
   let y:= radix u.w0.p.M x i
   have hs:g.windC x=y:=by simp [radix,y,windC,hp,Nat.add_comm]
   have he:x ≤ u.n:=Nat.le_of_lt_succ (mem_range.1 hx)
   have hy:y ≤ u.n:=Nat.le_of_lt_succ (mem_range.1 hf)
   have hv:3+i ≤ u.v.bonus:= (show 3+i  ≤  bootC u.r by unfold bootC; change i < u.r.w.p.M at hi;omega).trans hB.coinbook
   refine ⟨hx,hs.symm ▸ hf,?_,?_,?_⟩
   · rw [hp]; exact (Line.Chart.voteRoot (u := u)) hv (Nat.zero_le _)
   · rw [hp]; exact (show u.D.W (cell (Was.atom (3+i)))+_≤_ from by
                                   rw [show cell (Was.atom (3+i))=0 from by simp [cell,Was.atom,hole]]; exact hk)
   rw [hp]
   apply h.basic0 _ hv (Nat.zero_le _)
   have hq:¬(3+i=1∨3+i=2):=by omega
   have ht:=Nat.ne_of_gt (show 0<3+i by omega)
   have hL:3+i-3=i:=by omega
   rw [hs]
   simp only [Was.Flight,hq,ht,hL,ite_false,he,hy,show i<u.r.w.p.M from hi, ite_true]; refine ⟨?_,?_,?_,?_⟩ <;> first|rfl|trivial

structure Spell (s:Surf) (u:Line (q:=q) (w:=w) (h:=h)) :Prop where
     a : s.days.1 ≤ roof u.r u.x
     b : s.days.2 ≤ roof u.r u.x
     c0 : s.chartQ.1 ≤ u.r.w.ell*Moon.M u.r u.x
     c1:s.chartQ.2 ≤ 2^(planets u.r u.x*u.v.e)
     d : enc s.dye  ≤ WaresCap u.r u.x
     t : s.sunset.2.1  ≤ u.n∧s.sunset.2.2 ≤ u.n
lemma overly {s:Surf}(h:Spell s u)(b:Bool) :u.wick0.Ok (cube b s):=by
   refine ⟨?_,h.t⟩
   cases b
   · exact Helix.Torch.housed u.r u.v u.x (by decide: (5:ℕ) ≤ 16) h.a h.b h.c0 h.c1 h.d
   exact Helix.Torch.housed u.r u.v u.x (by decide: (4:ℕ) ≤ 16)
                           (Nat.zero_le _) h.b (Nat.zero_le _) (Nat.zero_le _) h.d

open Was

lemma basePort {p:Crew u}(h:p.Good) {i:ℕ}(ha:p.t.A=(Was.atom i,0))
   (hh:u.D.W 0+u.D.D p.src ≤ u.D.W p.src)(hb:i ≤ u.v.bonus)(hr:p.bound ≤ u.v.bonus+1)
   (hf:∀ k j,p.lampQ=true→ (p.entrance=some (k,j)↔ k<p.bound∧Flight u.r u.x i k p.x j))
   (hv:∀ k j,p.lampQ=true→ p.entrance=some (k,j)→ Partner u p.t p.src j (p.exit0 j)):
   p.Arrived:=by
     have h1:p.t.A.1=atom i:=by rw [ha]
     have h2:p.t.A.2=0:=by rw [ha]
     let m:= Hood.spill u.r u.x p.t.A.1 p.x p.bound
     refine ⟨h, fun e=>?_,fun k j e hz=>?_⟩
     · have hx:m=portM p.entrance:=by
           unfold m; rw [h1]
           cases hh:p.entrance with
           | none=> exact (Hood.dawn _).2 fun j hj v he=>by have hp:=(hf j v e).2 ⟨hj,he⟩; simp [hp] at hh
           | some s=>
             rcases s with ⟨k,b⟩
             obtain ⟨he,hp⟩:=(hf _ _ e).1 hh
             exact (Hood.lastE u.r he).2 ⟨b,hp⟩
       rw [←hx]; have ht:m ≤ p.bound:=Hood.ankle u.r
       exact ⟨ht,Keel.tome p.g (h.chart.rent h.pro.pos) ((by omega:2 ≤ 4).trans h.capcost) h.ix h.fiat h2 (h.capw m ht)⟩
     obtain ⟨ht,hp⟩:=(hf _ _ e).1 hz
     have hk:k ≤ u.v.bonus:=by omega
     refine ⟨?_,?_,hv k j e hz⟩
     · unfold Crew.hitP; rw [h1]
       exact ⟨by rw [show cell (atom i)=0 from by simp [cell,atom,hole]]; exact hh,
              h.ix,(Line.Chart.voteRoot (u := u)) hb hk,(h.chart.bootsBasic _).canonicalS⟩
     rw [h1]; exact h.chart.basic0 hp hb hk

lemma echoPort {p:Crew u} {w:Fabric u}{f:Producer}{s:MintV}(h:p.Good) (h0:w.Efine s f)
    (hg:w.govern=true){i:ℕ}(hi:i<w.Rslots)
    (he:p.t.A=(w.slotWord i,hole w.leaveE.dataN (hole 0 i)))
    (hA:u.D.W w.leaveE.dataN+u.D.D p.src ≤ u.D.W p.src)
    (hW:u.D.W (w.c 12 0)+u.D.D p.src ≤  u.D.W p.src)
    (hk:clim u.w0.p+1  ≤  p.bound)
    (hh:∀ k j,p.lampQ=true → (p.entrance=some (k,j) ↔ k≠0 ∧ f.tag p.x i=k∧ f.locate p.x i=j))
    (hv:∀ k j,p.lampQ=true→ p.entrance=some (k,j)→ Partner u p.t p.src j (p.exit0 j)):
    p.Arrived:=by
    have h1:p.t.A.1=w.slotWord i:=by rw [he]
    have h2:p.t.A.2=hole w.leaveE.dataN (hole 0 i):=by rw [he]
    have h3:w.leaveE.tagop=0:=rfl
    let K:=f.tag p.x i
    refine ⟨h, fun e=>?_,fun k j e hz=>?_⟩
    · have hm:=h0.sector.suit
      have hf:K  ≤  clim u.w0.p:=by
          by_cases hl:K=0; rw [hl]; omega
          exact h0.tin hg _ _ hl
      have hX:portM p.entrance=Keel.cream K:=by
         cases hq:p.entrance with
         | none=> have hj :K=0:=by by_contra hc; have hp:= (hh K (f.locate p.x i) e).2 ⟨hc,rfl,rfl⟩; simp [hp] at hq
                  unfold Keel.cream; rw [hj]; rfl
         | some r=>obtain ⟨k,j⟩:=r; obtain ⟨hv,hw,_⟩:=(hh _ _ e).1 hq; unfold Keel.cream K; rw [hw,ite_eq_right hv]; rfl
      rw [hX]
      have hu:Keel.cream K ≤ p.bound:=by unfold Keel.cream; split<;>omega
      refine ⟨hu,Keel.summons p.g (h.chart.rent h.pro.pos) ((by omega:2 ≤ 4).trans h.capcost)
                h.ix h.fiat hA h2 ?_ (h.capw K (by omega)) (h.capw _ hu) ?_⟩
      · exact (hm.trace p.x h.ix).next i (hm.coil.awake (hm.coil.size0 _ hi))
      rw [h2]; exact ne_of_gt (Fret.Seek.binpos w.leaveE.dataN _)
    obtain ⟨hl,hk0,hj⟩:= (hh k j e).1 hz
    have hy:k ≤ clim u.w0.p:=by rw [← hk0]; exact h0.tin hg _ _ (by show f.tag _ _≠0; rw [hk0]; exact hl)
    obtain ⟨he,hq,hx⟩:=h0.source hg i hi k (Nat.pos_of_ne_zero hl) hy
    refine ⟨?_,?_,hv k j e hz⟩
    · unfold Crew.hitP; rw [h1]
      exact ⟨by rw [show cell (w.slotWord i)=w.c 12 0 from by simp [Fabric.slotWord,cell,hole]]; exact hW,
                             h.ix,he,hq⟩
    rw [h1,hx p.x h.ix,ite_eq_left hk0,hj]

end Era
end
end ExactDerandomization.Cambria

end

section

namespace ExactDerandomization.Cambria
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Terrain Terrain.Bank Glass Glass.Rod
open Arena Fret.Seats Pier Arena.Flash Surf Mica BadgeX
open Fret.Lyric Reed.Lu Arena.Song Arena.Amber
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Wear

abbrev Rus:= (ℕ × Bool) × Coin × ℕ × History × ℕ
abbrev GridY:=ℕ×Surf×Rus
abbrev allQ : Cub ℕ GridY:=⟨_,Kn.unpack⟩
abbrev skyG:PondQ:=⟨_,allQ.runs.right.left⟩
abbrev rx:Cub ℕ Rus:=⟨_,allQ.runs.right.right⟩
def shelf(k:Knob):Knob:=
   let p(a:Cub ℕ ℕ):Cub ℕ ℕ:= ⟨_,a.runs.comp allQ.runs.left⟩
   ⟨p k.height,p k.bank,p k.store⟩
def tin : Tear := Amber.first0 ⟨_,rx.runs.right.left⟩
abbrev pin1 : Sight:= ⟨_,rx.runs.right.right.left⟩
abbrev pin2:Kiwi:=⟨_,rx.runs.right.right.right.left⟩
abbrev packC:Sight:=⟨_,rx.runs.right.right.right.right⟩
def tone (old:Bool) (o:ℕ):Sight:=
     let H:=rx.runs.right.right.right.left
     if old then ⟨_,Kn.wash.comp (H.left.tuple (Kn.fix (hole o 0)))⟩ else
                 ⟨_,Kn.wash.comp (H.left.tuple (Kn.wash.comp ((Kn.fix o).tuple H.right)))⟩
def pitch (p:Crt)(i:ℕ):Crt:=
     let q:= Age.styx p
     let s:Scout:=(q.1,q.2.1,i,q.2.2.2)
     (p.1,p.2.1,s,Age.env p)
abbrev rate0(u:Crt)(b:ℕ):ℕ:= hole (enc (pitch u b)) (hole 1 0)
def prefixD (b:ℕ):Sight:=
     let p:= (Kn.unpack (α:=Crt)).comp packC.runs
     let q:=p.right.right.left
     let s:= q.left.tuple (q.right.left.tuple ((Kn.fix b).tuple q.right.right.right))
     let t:=p.left.tuple (p.right.left.tuple (s.tuple p.right.right.right))
     ⟨_,Kn.wash.comp ((Kn.wash.comp t).tuple (Kn.fix (α:=ℕ) (hole 1 0)))⟩

lemma prefD(a i x): (prefixD a).f x i=rate0 (dec (packC.f x i)) a:=rfl

abbrev Health (p:MintV): Coin:=Coin.ofZ (2^p.coin)
abbrev range0 (p:MintV):= (2:ℝ)^p.coin
def powerF (p:MintV):Tear:= syrup (Health p)
def falls (p:Sight) :Cub ℕ Bool:=⟨_,p.runs.eq (Kn.fix 0)⟩

abbrev visitAt (p:ℕ):Kiwi:= Flash.clan (Keel.foilT skyG) (p-1)
def spreadC (f:Sight)(k:Knob)(c:Coin): Cog:=
    Song.pleas (falls f) (choir k (.solo 0 ⟨_,Kn.fix c⟩)) (Bullet.snap f)
def dose (k:Knob)(p:MintV): Lyric:= Amber.shade (spreadC pin1 k (Coin.inv (Health p))) p.coin (powerF p)
def puff (i n:ℕ)(k:Knob)(s:Scheme):Lyric:=
    let f:Sight:=prefixD n
    let e:Lyric:= .solo 0 ⟨_,Kn.fix (Coin.ofZ 1)⟩
    .use 0 (Pier.escort s (visitAt i) (Song.pleas (falls packC) (choir k e) (Bullet.snap f)))
def nook (i:ℕ)(k:Knob)(s:Scheme):ℕ → Lyric
   | 0=>zeroE
   | j+1=> Reed.Lu.sup (nook i k s j) (puff i j k s)
def gemini (i:ℕ)(k:Knob)(s:Scheme)(p:MintV)(T:ℕ):Lyric:=
    let h:= times (Amber.moonF tin p.prism) (dose k p)
    let v:= Amber.blossoms (visitAt i) s (Wear.tone false 1) p.coin (powerF p)
    times (times h v) (boostR (nook i k s T))

abbrev markR(r:Rock q w h)(i:ℕ): Tear:= by
    let k:= (skyG.runs.right.left.left).comp (Kn.first (β:=ℕ))
    have ht:= Was.edgeK r Kn.next (Hood.bloomK r k Kn.next (i-1)).pred
    exact ⟨_,Coin.ofK ht.ZofN⟩
abbrev moss (p:MintV) (i:ℕ)(r:Rock q w h) :Lyric :=
       times (Amber.moonF tin p.prism) (Amber.moonF (markR r i) 2)
abbrev past (k:Knob) (p:MintV) (f:Sight):Lyric:=
    Amber.petal f (2*p.sealR) (awry k (2*p.sealR))
def bia (b:Bool)(p:MintV)(k:Knob):Lyric:=
   let l:= past k p (Wear.tone false (if b then 1 else 2))
   if b then diff l (past k p (Wear.tone true 5)) else l

abbrev shapeC (k:ℕ): Cub ℕ Bool:=⟨_,rx.runs.left.left.eq (Kn.fix k)⟩
abbrev sourceB (b:Bool) : Cub ℕ Bool:= by
   let h:=rx.runs.left.right
   cases b
   · exact ⟨_,h.cond (Kn.fix false) (Kn.fix true)⟩
   exact ⟨_,h⟩

/-- mask kind2 and kind1 use lit-only pricing. -/
def coast (p:MintV)(c:Knob)(r:Rock q w h)(s:Scheme)(b:Bool)(i:ℕ):Cog:=
    let t:= p.inputH
    let v:= Song.pleas (shapeC 1) (roost c (moss p i r) t) (roost c (gemini i c s p r.w.p.T) t)
    let e:= snow c t
    if i=0 then e else Song.pleas (shapeC 0) (roost c (bia b p c) t)
                                  (Song.pleas (sourceB b) v e)
def hub (r:Rock q w h):Gate:= Mica.host r skyG (Era.budget r)
abbrev grainq (p:MintV)(k:Knob)(r:Rock q w h)(s:Scheme)(b:Bool):Cog:=
     (hub r).openE s (coast p k r s b)

namespace Paper
def same (x y : Lyric):Prop:= x.weight=y.weight∧ x.tail=y.tail ∧ ∀ c, Lyric.cost x c=Lyric.cost y c
lemma oneself (x:Lyric): same x x:=⟨rfl,rfl,fun _=>rfl⟩
lemma use (f g:Cog) (i:ℕ):same (.use i f) (.use i g):=⟨rfl,rfl,fun _=>rfl⟩
lemma everF {i:ℕ}{x y:Cub CoinQuery Coin}:same (.solo i x) (.solo i y):=⟨rfl,rfl,fun _=>rfl⟩
namespace same
lemma stronger {x y m n:Lyric}(h:same x y)(e:same m n)(v:Doop)(b:ℕ):same (.duet v x m b) (.duet v y n b):=by
   obtain ⟨_,_,_⟩:=h; obtain ⟨_,_,_⟩:=e
   simp_all [same,Lyric.weight,Lyric.cost,Lyric.tail]
lemma plies {x y m n:Lyric}(h:same x y)(e:same m n)(v:Doop):same (bi v x m) (bi v y n):=by
   unfold bi; rw [h.1,e.1]; exact h.stronger e v _
lemma score0 {x y}(h:same x y):same (Song.sQ x) (Song.sQ y):=
     (oneself _).plies ((oneself _).plies h _) _
lemma txt {x y}(h:same x y):same (takeF x) (takeF y):=
     let e:= ((oneself _).plies h Doop.prod).score0
     (e.plies e _).plies (e.plies e _) _
lemma rosebud {x y}(h:same x y):same (faded x) (faded y):=
    (h.txt.plies ((oneself _).plies ((oneself _).plies h Doop.minus).txt _) _).plies (oneself _) _
lemma red {x y}(h:same x y):same (boostR x) (boostR y):=
     (((oneself _).plies h Doop.prod).plies (oneself _) Doop.minus).rosebud
lemma stow {x y}(h:same x y)(i):same (reset x i) (reset y i):= h.stronger (oneself _) _ _
end same
lemma reed (i j k q s p u):same (Wear.nook i k s u) (Wear.nook j q p u):=by
   induction u with
   | zero=> exact oneself _
   | succ u ih=> exact ih.plies (use _ _ _) _
lemma reedX (i j k q s p M c):same (gemini i k s M c) (gemini j q p M c):=
     (((oneself _).plies ((use _ _ _).plies (oneself _) _) _).plies
             ((use _ _ _).plies (oneself _) _) _).plies (reed ..).red _
lemma biaS (p k s) (b:Bool):same (bia b p k) (bia b p s):= by
   have h (v:Sight):same (past k p v) (past s p v):= (use _ _ _).plies everF _
   cases b
   · exact h _
   exact (h _).plies (h _) _
lemma backS (v:MintV)(r:Rock q w h)(i j):same (moss v i r) (moss v j r):=
       (oneself _).plies everF _

abbrev noneT : Tags:=⟨0,0,0,0,0,0⟩
def money0 (p:MintV)(f:Lyric)(c:ℕ):ℕ:=
   let r:=reset f p.inputH
   Lyric.cost r c+ Lyric.tail r
def budgetD (p:MintV)(r:Rock q w h):ℕ:=
   let k:=knob r noneT
   let s:= schedule r noneT
   let c:=Era.tariff r
   let v(f):= money0 p f c
   c+v (bia true p k)+v (bia false p k)+v (gemini 1 k s p r.w.p.T)+v (moss p 1 r)
lemma eras (p:MintV)(r:Rock q w h) (s:Scheme) (k:Knob) (b:Bool) (i:ℕ):
   Era.tariff r ≤ budgetD p r ∧ ∀ f, f=bia b p k∨ f=gemini i k s p r.w.p.T∨f=moss p i r →
       (reset f p.inputH).cost (Era.tariff r) ≤ budgetD p r ∧
          (reset f p.inputH).tail ≤ budgetD p r:=by
    let c:= Era.tariff r
    let t:=p.inputH
    have hh {f g:Lyric}(h:same f g)(he:money0 p f c ≤ budgetD p r):
        Lyric.cost (reset g t) c ≤ budgetD p r ∧ Lyric.tail (reset g t) ≤ budgetD p r:=by
       have hg:=same.stow h t; unfold money0 at he; unfold t at *; obtain ⟨-,hz,hz2⟩:=hg
       dsimp only at he; rw [hz,hz2] at he; omega
    refine ⟨?_,fun g h=>?_⟩
    · unfold budgetD; dsimp only; omega
    rcases h with rfl|rfl|rfl
    · apply hh (biaS p (knob r noneT) k b)
      cases b <;> unfold budgetD c <;> dsimp only <;> omega
    · apply hh (reedX 1 i (knob r noneT) _ (schedule r noneT) _ p _)
      unfold budgetD c; dsimp only; omega
    apply hh (backS p r 1 _); unfold budgetD c; dsimp only; omega
end Paper
end Wear
end
end ExactDerandomization.Cambria

end

section

namespace ExactDerandomization.Cambria
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Terrain Terrain.Bank Glass Glass.Rod
open Arena Fret.Seats Pier Arena.Flash Surf Mica BadgeX
open Fret.Lyric Reed.Lu Arena.Song Arena.Amber Wear Wear.Paper
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Rime
structure Nest(u:Line (q:=q) (w:=w) (h:=h)) where
    snow0: Crew u
    diploma:Rus
    tune:MintV

namespace Nest
variable {u:Line (q:=q) (w:=w) (h:=h)}
variable (s:Nest u)
abbrev ray:=s.snow0
abbrev krod (u:Line (q:=q) (w:=w) (h:=h)):=shelf (knob u.r u.v)
abbrev a:=s.ray.src
abbrev v:=s.ray.info
abbrev t:=s.tune
abbrev H:=u.D.high s.a
abbrev T:=s.H+budgetD s.t u.r*u.D.D s.a
abbrev home:=s.ray.stationP
abbrev whereF(x:ℕ):=s.ray.skill x
abbrev beaming := Chor (krod u) (Era.tariff u.r) s.T s.home
abbrev optic := s.diploma.1
abbrev addr1:= s.diploma.2.2.1
abbrev addr2:= s.diploma.2.2.2.1
abbrev capV:=s.diploma.2.2.2.2
abbrev cut := s.diploma.2.1
def addr3(o:ℕ):ℕ:=hole s.addr2.1 (hole o s.addr2.2)
def catshot(i:ℕ):ℕ:= rate0 (dec s.capV) i
structure Good (s:Nest u):Prop where
    grip:s.ray.Arrived
    matches0:s.ray.g=skyG
    earning:s.ray.c=Era.tariff u.r
    scores:s.v=enc ((s.ray.src,s.ray.t,s.diploma):GridY)
    arch:s.ray.bound=Era.budget u.r
    large0:budgetD s.t u.r ≤ u.v.slope

/-- score service at another location.W-clock sufficient. power j normalizer. -/
def VoiceS(x y j:ℕ)(A:ℝ): Prop := ∃ b m,
    y=hole b m∧ u.D.W b+u.D.D s.a ≤ u.D.W s.a∧
                 u.D.Voice b x m (u.D.high b) j A
def Loom0 (x y:ℝ) := min x y

structure Etude (s:Nest u)(k i:ℕ):Prop where
    low:Liaison u.D s.ray.x s.a s.ray.t.A.1 k
    yoke:u.D.curve s.ray.t.A.1 k true s.ray.x=some i

namespace Good
variable {s:Nest u} (hp:s.Good)
include hp
lemma primary : u.D.Suite s.a :=
     hp.grip.stable.chart.rent hp.grip.stable.pro.pos

set_option maxRecDepth 6000 in
lemma nested {x:ℕ} (he:x∈u.D.P): Align ((s.whereF x).head) (krod u) ∧
                                           Standard (s.whereF x) (krod u) s.T:=by
    have hx:= hp.primary
    have hT:= Studio.positioned (u:=u) hx he 0 0
    have hf: (s.whereF x).stable (krod u):=by
        intro j hj
        have H:= Mold.knows u.r u.v u.x u.prog s.a x (of_decide_eq_true hx.stage) he
                                  hp.primary.shape.price
        have hm:=H j hj
        have hh : (dec s.v:GridY).1=s.a:=by rw [hp.scores,dec_round]
        refine ⟨hm.1,?_,?_⟩
        · change (knob u.r u.v).height.f u.x (dec s.v:GridY).1=_
          rw [hh]; exact hm.2.1
        change (knob u.r u.v).bank.f u.x (dec s.v:GridY).1=_
        rw [hh]; exact hm.2.2
    refine ⟨stable_home hf,hf,?_⟩
    change 2^s.T ≤ 2^u.D.H
    apply Nat.pow_le_pow_right (by omega)
    exact Studio.stayedC hx le_rfl hp.large0
lemma born0 :Standard s.home (krod u) s.T:= (hp.nested hp.grip.stable.ix).2
lemma press {b:ℕ}(h:u.D.W b+u.D.D s.a ≤ u.D.W s.a):s.T ≤ u.D.high b:=Studio.soonerC hp.primary h hp.large0 le_rfl
lemma ru : rx.f u.x s.v=s.diploma :=by
    rw [hp.scores]; change (dec (enc _) : GridY).2.2=_
    rw [Wire.eq]
lemma shade0 : skyG.f u.x s.v=s.ray.t :=by rw [hp.scores]; change (dec (enc _) : GridY).2.1=_; rw [Wire.eq]
lemma visE0(k): (visitAt (k+1)).f u.x s.v=(s.ray.t.A.1,k):=by
      change ((skyG.f u.x s.v).A.1,k+1-1)=_
      rw [hp.shade0]; simp

lemma sell0 {f:Sight}{x j y}{A:ℝ} (hr:s.VoiceS x y j A)(he:f.f u.x s.v=y)(hx:x∈u.D.P):
    (s.whereF x).band (Era.tariff u.r) s.T 0 (Bullet.snap f) (A/(2:ℝ)^j):=by
   obtain ⟨b,m,hv,hb,hR⟩:=hr
   exact Amber.normalizeF hp.primary f (Era.billed ..).2.1 hx (he.trans hv) hb hR (hp.press hb)

omit hp in
lemma keep0 (_ b:Bool) : provided (sourceB b)=provided (sourceB b):=rfl
lemma scales : range0 s.t ≤ massB s.t.coin s.home.d:= by
    unfold massB
    apply pow_le_pow_right₀ (by norm_num)
    have hx:1 ≤ s.home.d:= hp.primary.well.1; nlinarith
omit hp in
lemma trueL : ((powerF s.t).f u.x (s.v,s.ray.x)).v=range0 s.t:=by simp [powerF,syrup,Health,range0]
lemma scrys (v:Coin){x i:ℕ}(he:x∈u.D.P)(hb:|v.v|  ≤  massB i (u.D.D s.a)):
   (s.whereF x).band (Era.tariff u.r) s.T i (choir (krod u) (.solo i ⟨_,Kn.fix v⟩)) v.v:=by
    have h:= (hp.nested he).2
    have hx:Chor (krod u) 1 s.T (s.whereF x) (.solo i ⟨_,Kn.fix v⟩) v.v:= .played h.st h.he (fun _ _=>rfl) hb
    exact flex (sing hx (by omega) (by simp [tail]))
           (cost_hi (p:=.solo i ⟨_,Kn.fix v⟩) (by omega :1 ≤ 1)) (Era.billed u.r).2.2 le_rfl
lemma barre {V:ℝ}(he:s.addr1 ≠ 0→s.VoiceS s.ray.x s.addr1 s.t.coin V) (hy:s.addr1=0 → V=1):
   s.beaming (dose (krod u) s.t) V :=by
    apply Amber.cast hp.born0 (j:=s.t.coin) ?_ (trueL (s := s)) hp.scales
    have hf: pin1.f s.home.l.x s.home.info=s.addr1:=congrArg (fun a:Rus=> a.2.2.1) hp.ru
    by_cases ht:s.addr1=0
    · apply Song.pinTrue (falls pin1) _
      · rw [hy ht]
        let g:=Coin.inv (Health s.t); have hh:g.v=1/(2:ℝ)^s.t.coin:=by simp [g,Health]
        have hb:|g.v| ≤ massB 0 s.home.d:=by
            rw [hh,abs_of_pos (by positivity)]; unfold massB
            simp only [Nat.zero_mul,pow_zero]
            apply (div_le_one (by positivity)).2; exact one_le_pow₀ (by norm_num)
        rw [←hh]; exact hp.scrys g hp.grip.stable.ix hb
      change decide (pin1.f s.home.l.x s.home.info=0)=true
      rw [hf];simp [ht]
    apply Song.pinFalse (falls pin1) _ (hp.sell0 (he ht) hf hp.grip.stable.ix)
    change decide (pin1.f s.home.l.x s.home.info =0)=false
    rw [hf];simp [ht]
lemma salve {k m:ℕ}(e:s.Etude k m){f:Sight}{j y}{A:ℝ} (hr:s.VoiceS m y j A)(he:f.f u.x s.v=y):
   s.home.band (Era.tariff u.r) s.T 0 (Pier.escort u.D.s (visitAt (k+1)) (Bullet.snap f)) (A/(2:ℝ)^j):=by
    have hm:2 ≤ Era.tariff u.r:= ((by omega: 2 ≤ 4).trans (Era.billed _).1)
    exact Pier.bowls hp.primary hm e.low (Era.billed _).2.1 (hp.visE0 k) e.yoke _
                                 (hp.sell0 hr he (Pier.street e.low e.yoke).xem)
lemma waltz {k m:ℕ}(e:s.Etude k m){A:ℝ} (hr:s.VoiceS m (s.addr3 1) s.t.coin A):
    s.beaming (Amber.blossoms (visitAt (k+1)) u.D.s (Wear.tone false 1) s.t.coin (powerF s.t)) A:=
   Amber.cast hp.born0 (hp.salve e hr (congrArg (fun a:Rus=>hole a.2.2.2.1.1 (hole 1 a.2.2.2.1.2)) hp.ru))
                                              (trueL (s := s)) hp.scales

set_option maxHeartbeats 1200000 in
lemma upso {i k m:ℕ}(e:s.Etude k m){A:ℝ} (hr:s.capV≠0→s.VoiceS m (s.catshot i) 0 A)(hy:s.capV=0→A=1) :
    s.beaming (puff (k+1) i (krod u) u.D.s) A:=by
    have hm:2 ≤ Era.tariff u.r:= ((by omega:2 ≤ 4).trans (Era.billed _).1)
    have hg:= (hp.nested (Pier.street e.low e.yoke).xem)
    refine Chor.byear (Pier.bowls hp.primary hm e.low (Era.billed _).2.1 (hp.visE0 k) e.yoke _ ?_)
    have hf: packC.f ((s.whereF m).l.x) (s.whereF m).info=s.capV:=congrArg (fun a:Rus=> a.2.2.2.2) hp.ru
    by_cases hz:s.capV=0
    · apply Song.pinTrue (falls packC) _
      · rw [hy hz]
        have hh : (Coin.ofZ 1).v=1:=by simp
        rw [←hh]; apply hp.scrys _ (Pier.street e.low e.yoke).xem
        simp [massB]
      change decide (packC.f ((s.whereF m).l.x) (s.whereF m).info=0)=true
      rw [hf];simp [hz]
    apply Song.pinFalse (falls packC) _
    · have hp0 : (prefixD i).f u.x s.v=s.catshot i:=
           by rw [prefD]; change rate0 (dec (packC.f ((s.whereF m).l.x) (s.whereF m).info)) i=_; rw [hf]; rfl
      simpa only [pow_zero,div_one] using hp.sell0 (hr hz) hp0 (Pier.street e.low e.yoke).xem
    change decide (packC.f ((s.whereF m).l.x) (s.whereF m).info=0)=false
    rw [hf];simp [hz]

def maxs (t:ℕ → ℝ):ℕ → ℝ
    | 0=>0
    | i+1=> max (maxs t i) (t i)
lemma carmen {k m:ℕ}(e:s.Etude k m) (A:ℕ → ℝ)(d:ℕ)
    (hx:∀ i<d,s.capV≠0→s.VoiceS m (s.catshot i) 0 (A i))(hl:s.capV=0→∀ i<d,A i=1):
   s.beaming (Wear.nook (k+1) (krod u) u.D.s d) (maxs A d):=by
    induction d with
    | zero=> exact hp.born0.sil
    | succ d ih=> exact hp.born0.up0 (ih (fun i h=>hx i (by omega)) (fun k i h=>hl k i (by omega)))
                        (hp.upso e (hx _ (by omega)) (fun h=>hl h d (by omega)))

omit hp in
lemma tensorB (b:Bool){_:ℕ}(hk:b=true):b=true:=hk
lemma warm (hs:|s.cut.v| ≤ massB s.t.prism (u.D.D s.a)):
     s.beaming (moonF tin s.t.prism) s.cut.v:=
    Amber.occlude hp.born0 _ _ (congrArg (fun a:Rus=>(a.2.1:Coin).v) hp.ru) hs
lemma salutation {k m:ℕ}(e:s.Etude k m)(A:ℕ → ℝ)(x y:ℝ)
    (hs:|s.cut.v| ≤ massB s.t.prism (u.D.D s.a))
    (he:s.addr1≠0→s.VoiceS s.ray.x s.addr1 s.t.coin x)(hy:s.addr1=0→x=1)
    (hr:s.VoiceS m (s.addr3 1) s.t.coin y)
    (hx:∀ i<u.w0.p.T,s.capV≠0→s.VoiceS m (s.catshot i) 0 (A i))(hl:s.capV=0→∀ i<u.w0.p.T,A i=1):
   s.beaming (gemini (k+1) (krod u) u.D.s s.t u.w0.p.T)
                    (s.cut.v*x*y*boost (maxs A u.w0.p.T)) :=
    hp.born0.mult0 (hp.born0.mult0 (hp.born0.mult0 (hp.warm hs) (hp.barre he hy)) (hp.waltz e hr))
                  (Song.Paint.boosted hp.born0 (hp.carmen e A _ hx hl))

lemma lecture {k i m:ℕ}(he:s.ray.t.A.1=Was.atom i)(hA:Was.Flight u.r u.x i k s.ray.x m)
    (hs:|s.cut.v| ≤ massB s.t.prism (u.D.D s.a)):
   s.beaming (moss s.t (k+1) u.r) (s.cut.v*(u.r.P.edge u.x s.ray.x m:ℝ)):=by
   let q:=u.r.P.edge u.x s.ray.x m
   have hz:q ≤ 2:=by unfold q Base.Source.edge; grind
   apply hp.born0.mult0 (hp.warm hs)
   apply occlude hp.born0
   · let g:= (skyG.f u.x s.v).A.1
     change (Coin.ofZ (u.r.P.edge u.x s.ray.x (_-1):ℤ)).v=_
     simp only [Coin.ofv,Int.cast_natCast]
     congr 2
     rw [show Hood.codeE u.r ..=m+1 from ?_]; omega
     change Hood.codeE u.r u.x (skyG.f u.x s.v).A.1 s.ray.x (k+1-1)=m+1
     rw [show skyG.f u.x s.v=s.ray.t from hp.shade0,he,show k+1-1=k from by omega]
     exact (Hood.codePos u.r).2 hA
   · change |(q:ℝ)|  ≤ _
     rw [abs_of_nonneg (by positivity)]
     exact le_trans (by exact_mod_cast hz) (swellB hp.primary.well.1).le
end Good
end Nest
end Rime
end
end ExactDerandomization.Cambria

end

section

namespace ExactDerandomization.Cambria.Rime.Nest
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Terrain Terrain.Bank Glass Glass.Rod
open Arena Fret.Seats Pier Arena.Flash Surf Mica BadgeX
open Fret.Lyric Reed.Lu Arena.Song Arena.Amber Wear Wear.Paper
noncomputable section
open scoped Classical
variable {q w h:ℕ}
variable {u:Line (q:=q) (w:=w) (h:=h)}
variable {s:Nest u}
namespace Good
variable (hp:s.Good)
include hp

lemma valueOld {A:ℝ}{f:Sight}{y}
   (hr:s.VoiceS s.ray.x y (2*s.t.sealR*u.D.D s.a) A)
   (he:f.f u.x s.v=y): s.beaming (past (krod u) s.t f) A:=
   Amber.cast hp.born0 (hp.sell0 hr he hp.grip.stable.ix)
       (Amber.scalingF (x:=s.ray.x) (q:=s.v) (hp.nested hp.grip.stable.ix).1 _) le_rfl

lemma biast (A:Pt)(y:ℝ)(b:Bool)
   (hr:∀ b:Bool,s.VoiceS s.ray.x (s.addr3 (if b then 1 else 2)) (2*s.t.sealR*u.D.D s.a) (Reed.sideq A b))
   (he:s.VoiceS s.ray.x (hole s.addr2.1 (hole 5 0)) (2*s.t.sealR*u.D.D s.a) y):
   s.beaming (bia b s.t (krod u)) (Reed.sideq (A-line y) b):=by
    have hp1(b):s.beaming (past (krod u) s.t (Wear.tone false (if b then 1 else 2))) (Reed.sideq A b):=
        hp.valueOld (hr b) (congrArg (fun (a:Rus)=>hole a.2.2.2.1.1 (hole (if b then 1 else 2) a.2.2.2.1.2)) hp.ru)
    have hp2:s.beaming (past (krod u) s.t (Wear.tone true 5)) y:=
        hp.valueOld he (congrArg (fun a:Rus=>hole a.2.2.2.1.1 (hole 5 0)) hp.ru)
    cases b
    · change s.beaming _ (A.2-0)
      rw [sub_zero]; exact hp1 false
    exact hp.born0.dubs (hp1 true) hp2
lemma knows0:hub u.r=s.ray.host0:=by
    unfold Crew.host0 hub; rw [hp.matches0,hp.arch]

abbrev C0 (s:Nest u):=budgetD s.t u.r
abbrev title (s:Nest u):=iris s.ray.outR
abbrev capsum (s:Nest u)(v:ℝ):= |v| ≤ massB s.t.inputH (u.D.D s.a)
abbrev sailed(s:Nest u)(f:Cog)(X:ℝ):=
     s.home.band (C0 s) s.H s.t.inputH f X
abbrev holding(s:Nest u)(b:Bool)(X:ℝ):=
     sailed s (coast s.t (krod u) u.r u.D.s b (title s)) X
abbrev gross(s:Nest u)(b:Bool)(X:ℝ):=
    sailed s (grainq s.t (krod u) u.r u.D.s b) X

lemma home0: s.home.rite (C0 s) ((hub u.r).garden u.D.s) (title s):=by
    rw [hp.knows0]
    have he:=hp.grip.wreath.2; rw [hp.earning] at he
    exact higher he (le_trans (by omega) (Era.billed ..).1)
              (eras s.t u.r u.D.s (krod u) true (title s)).1
lemma inoculates(b:Bool)(X:ℝ) (h:holding s b X):gross s b X:=
    Iris.parcel (by rw [hp.knows0]; exact hp.grip.wreath.1)
                                hp.home0 h
lemma lame : sailed s (snow (krod u) s.t.inputH) 0:=by
    have ht:= steam (krod u) s.t.inputH hp.born0 (Era.billed u.r).2.2
    have hz :1 ≤ Era.tariff u.r := by have := (Era.billed u.r).1; omega
    apply flex ht hz (eras s.t u.r u.D.s (krod u) true (title s)).1; unfold Nest.T; omega

lemma zen0(b:ℕ): (shapeC b).f s.home.l.x s.home.info=decide (s.optic.1=b):=
     congrArg (fun a:Rus=> decide (a.1.1=b)) hp.ru
lemma help0(b:Bool): (sourceB b).f s.home.l.x s.home.info=decide (s.optic.2=b):=by
   have he:s.diploma.1.2=s.optic.2:=rfl
   cases b
   · change (if (rx.f u.x s.v).1.2 then false else true)=_
     rw [hp.ru,he]; cases s.optic.2 <;> rfl
   change (rx.f u.x s.v).1.2=_
   rw [hp.ru,he]; cases s.optic.2 <;> rfl
lemma stellar (b:Bool)(X:ℝ){f:Lyric}
     (h:f=bia b s.t (krod u)∨ f=gemini (title s) (krod u) u.D.s s.t u.r.w.p.T∨f=moss s.t (title s) u.r)
     (hu:s.beaming f X)(he:capsum s X):
     sailed s (roost (krod u) f s.t.inputH) X:=by
   obtain ⟨hr,hs⟩:=(eras s.t u.r u.D.s (krod u) b (title s)).2 f h
   apply Amber.onQ _ _ _ hp.born0 hu (by have :=(Era.billed u.r);omega) _ hr he
   exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hs) _

lemma torn (hx:title s=0)(b:Bool): gross s b 0:=by
   apply hp.inoculates; unfold holding coast
   dsimp only; rw [ite_eq_left hx]; exact hp.lame
lemma partOld {b X}(hr:title s≠0)(hs:s.optic.1=0)(ht:s.beaming (bia b s.t (krod u)) X)
    (he:capsum s X): gross s b X:=by
   apply hp.inoculates b X
   unfold holding coast; dsimp only; rw [ite_eq_right hr]
   apply Song.pinTrue _ _ (hp.stellar b X (Or.inl rfl) ht he)
   rw [hp.zen0,hs]; rfl

lemma youngNo {b}(hr:title s≠0)(hs:s.optic.1≠0)(ht:s.optic.2≠b):
    gross s b 0:=by
   apply hp.inoculates b 0
   unfold holding coast; dsimp only; rw [ite_eq_right hr]
   refine Song.pinFalse _ ?_ (Song.pinFalse _ ?_ hp.lame)
   · rw [hp.zen0]; simp [hs]
   rw [hp.help0]; simp [ht]
lemma youngYes {b X}(hr:title s≠0)(hs:s.optic.1≠0)(ht:s.optic.2=b)
    (hT : s.optic.1=1 → s.beaming (moss s.t (title s) u.r) X)
    (hA : s.optic.1≠1 → s.beaming (gemini (title s) (krod u) u.D.s s.t u.r.w.p.T) X)
    (he:capsum s X): gross s b X:=by
   apply hp.inoculates b X
   unfold holding coast; dsimp only; rw [ite_eq_right hr]
   refine Song.pinFalse (shapeC 0) (by rw [hp.zen0]; simp [hs]) (Song.pinTrue (sourceB b) (by rw [hp.help0];simp [ht]) ?_)
   · by_cases hv:s.optic.1=1
     · apply Song.pinTrue _ _ (hp.stellar b X (Or.inr (Or.inr rfl)) (hT hv) he)
       rw [hp.zen0]; simp [hv]
     apply Song.pinFalse _ _ (hp.stellar b X (Or.inr (Or.inl rfl)) (hA hv) he)
     rw [hp.zen0]; simp [hv]
omit hp in
lemma shekel {x:ℝ}{p:MintV}(h:Green u.r p)(ht:p=s.t) (he:|x| ≤  massB p.prism (u.D.D s.a)):
   capsum s x:= by
   subst p
   have hr:=h.honest
   exact he.trans (mass_mono (by unfold MintV.tokenH at hr; unfold MintV.inputH; omega) _)
end Good
end
end ExactDerandomization.Cambria.Rime.Nest

end

end OAI
