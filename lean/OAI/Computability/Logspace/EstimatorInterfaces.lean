import OAI.Computability.Logspace.BoundedTours
import OAI.Computability.Logspace.CatalyticComparison
import OAI.Computability.Logspace.CompressionPrograms

namespace OAI

/-!
Typed estimator requests, traversal interfaces, and terminal configurations.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset

/-- Each statistical unit offers several opaque services. -/
structure Scheme where
    mass : Cub ℕ ℕ
    slack : Cub ℕ ℕ
    admiss : Cub ℕ Bool
    listen : Cub ℕ Bool
    vote : Cub History Bool
    loc : Bool → Cub History ℕ
    hoard : Cub ℕ ℕ
namespace Scheme

def hole (u v:ℕ):ℕ:= enc ((u,v):History)
def bell (u v t:ℕ):ℕ:=postcard (hole u v) t
def token (q:ℕ):History:=dec q
def cell (r:ℕ): ℕ:=(dec r:History).1
def inside (r:ℕ):ℕ:=(dec r:History).2
def unitK (q:ℕ):ℕ:=cell (token q).1
def which (q:ℕ):ℕ:= inside (token q).1
def date (q:ℕ):ℕ:= (token q).2
lemma tokenK : Kn (fun (_:Word) q=>token q):=Kn.unpack
lemma cellK : Kn (fun (_:Word) q=>cell q):= tokenK.left
lemma unitK0:Kn (fun (_:Word) q=>unitK q):=cellK.comp tokenK.left

@[simp] lemma markB (u v t):token (bell u v t)=(enc ((u,v):History),t):=by simp [token,bell,postcard,hole]
@[simp] lemma bellU (u v t):unitK (bell u v t)=u:=by simp [unitK,markB,cell]
@[simp] lemma bellT (u v t):date (bell u v t)=t:=by simp [date,markB]
@[simp] lemma bellV (u v t):which (bell u v t)=v:=by simp [which,markB,inside]
variable (p:Scheme)
def ofclock (_:Word)(q:ℕ):ℕ:=date q
def ofword (x:Word)(q:ℕ):ℕ:=p.mass.f x (unitK q)
def based (x:Word)(q:ℕ):Level:=⟨p.ofword x q,ofclock x q⟩
def before (b:Bool)(x:Word)(r:History):ℕ:=bell (cell r.1) ((p.loc b).f x r) 0
lemma beforeK (b):Kn (p.before b):= Kn.wash.comp
       ((Kn.wash.comp ((cellK.comp Kn.first).tuple (p.loc b).runs)).tuple (Kn.fix 0))

def vent : Valve :=
    let h: Cub ℕ ℕ:= ⟨_,p.mass.runs.comp unitK0⟩
    let c: Cub ℕ ℕ:=⟨_,tokenK.right⟩
    ⟨h,c,⟨_,Kn.fix 1⟩,h,c,p.listen,p.vote,fun b=>⟨_,p.beforeK b⟩,p.hoard⟩
lemma born (u v t x) : p.based x (bell u v t)=⟨p.mass.f x u,t⟩:=by
    unfold based ofclock ofword; simp

end Scheme
open Scheme

structure Dome where
    spec : Scheme
    l:Lot
    peak:ℕ
    slope:ℕ
    H:ℕ
namespace Dome
variable (p:Dome)
abbrev s := p.spec
abbrev F:=p.l.F
abbrev x:=p.l.x
abbrev r:Rod:=⟨p.peak⟩
abbrev P:= range (p.peak+1)
abbrev active (u:ℕ):=p.s.admiss.f p.x u=true
abbrev W (u:ℕ):ℕ:=p.s.mass.f p.x u
abbrev D (u:ℕ):ℕ:=p.s.slack.f p.x u
abbrev loadC (u t:ℕ):ℕ:= t+p.slope*p.W u
abbrev won (u t:ℕ):Prop:=p.loadC u t  ≤  p.H
abbrev high (u:ℕ):ℕ:=p.H-p.slope*p.W u

lemma till (u t):p.won u t ↔ t ≤ p.high u∧ p.won u 0:=by unfold won loadC high; omega
lemma hiwon {u t}(h:p.won u t):t ≤ p.high u:=(p.till u t).1 h|>.1
lemma future {u}(h:p.won u 0):p.won u (p.high u):=(p.till ..).2 ⟨le_rfl,h⟩

open Rod
abbrev glove (a:Pane)(i:ℕ):ℕ:= enc ((i,a):Foot)
abbrev clearG :Pane:= (0,0,0)
lemma cleared:p.r.proper clearG:=by
   have he:=p.r.M4; refine ⟨?_,?_,?_⟩
   · change 0 < p.r.M ^ _; positivity
   · change 0 < p.r.M; exact lt_of_lt_of_le (by omega) he
   change 0 < 2 ^ _; positivity
abbrev audible (q:ℕ):Prop := p.s.listen.f p.x q=true
abbrev dual (q z:ℕ):Prop:= p.s.vote.f p.x (q,z)=true

/-- analytic clocks and polynomial choices are separated from the running program. -/
structure Shape : Prop where
    strut: ∀ q,p.l.book q=p.s.based p.x q
    rateC: ∀ q,p.F.meter q=charge p.slope (p.l.book q).w (p.l.book q).t
    price: 2  ≤  p.slope
    auth:∀ q,p.audible q→ p.active (unitK q)
    may :∀ q z,p.dual q z→ p.active (cell q)
    account:∀ i∈p.P,∀ a,p.r.proper a → glove a i  ≤  p.F.limit

lemma Shape.bookB {p} (h:Shape p)(u v t): p.l.book (bell u v t)=⟨p.W u,t⟩:=by rw [h.strut,p.s.born]

lemma Shape.migrate {p}(h:Shape p){u t c k q d a}
    (hp:p.won u t)(he:p.l.jump c ⟨p.W u,t⟩ d a q)
    (hq:k=unitK q)(hz:1 ≤ c)(hw:c  ≤  p.slope): p.won k (date q):=by
    rcases he with ⟨hk,hb⟩; rw [h.strut q] at hk hb
    have hr:=acock hb hz
    subst k
    change p.W (unitK q)+d ≤ p.W u at hk
    have hx :(p.W u-p.W (unitK q))+p.W (unitK q)=p.W u:=by omega
    change date q  ≤  t+c*(p.W u-p.W (unitK q)) at hr
    unfold won loadC at *; nlinarith [Nat.mul_le_mul_right (p.W u-p.W (unitK q)) hw]

abbrev talk (q h:ℕ)(u:Site):Prop:= Boots p.x p.F p.l.P q p.l.P (0,h) u

lemma aon {x F P q f a b}(h:Boots x F P q f a b){z}(e:Boots x F P q f a z):b=z:=by
    induction h generalizing z <;> cases e <;> grind
noncomputable def cand (q v:ℕ):Site := by
    classical
    exact if h:∃ w,p.talk q v w then Classical.choose h else (0,0)
lemma grab {q v w}(h:p.talk q v w):p.cand q v=w:=by
    unfold cand; have he : ∃ w,p.talk q v w:=⟨_,h⟩
    rw [dite_eq_left he]
    exact aon (Classical.choose_spec he) h

noncomputable def echo (q i:ℕ):ℕ:=(p.cand q (glove clearG i)).1
def swears(q i v:ℕ):=∀ a,p.r.proper a → p.talk q (glove a i) (v,glove a i)
lemma identity {q i v} (h:p.swears q i v):p.echo q i=v:=congrArg Prod.fst (grab p (h clearG p.cleared))

end Dome
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod
namespace Dome
variable (p:Dome)

abbrev pulseQ(t i:ℕ)(b:Bool):ℕ:=p.s.before b p.x (t,i)
lemma pulseB (t i:ℕ)(b):unitK (p.pulseQ t i b)=cell t := bellU ..
lemma day(t i:ℕ)(b):date (p.pulseQ t i b)=0:= bellT ..

noncomputable section
open scoped Classical
abbrev Tide:=ℕ→Bool→ℕ→Option ℕ
def pour(t:ℕ):Tide:=fun z b i=>
    if p.dual t z ∧ i∈p.P then
       let r:=p.cand (p.pulseQ t z b) (glove clearG i)
       if r.1=0 then none else some (dec r.2:Foot).1
    else none
def curve(t:ℕ):Tide:=fun z b i=>
    if !b ∨ ∀ u w,p.pour t u b i=some w→u=z then p.pour t z b i
    else none
lemma uniquely {t i z y a b} (he:p.curve t z true i=some a)(hv:p.curve t y true i=some b): z=y:=by
    unfold curve at *
    split at he <;> split at hv <;> grind

def AtM (v:Option ℕ)(a:Pane)(i:ℕ):Site :=
    match v with
    | none=>(0,glove a i)
    | some q=>(1,glove a q)

structure Streams (t:ℕ)(f:Tide):Prop where
    runs:∀ z,p.dual t z→∀ i∈p.P,∀ b a,p.r.proper a→p.talk (p.pulseQ t z b) (glove a i)
                                     (AtM (f z b i) a i)
    swaps:∀ z,p.dual t z→∀ i∈p.P,∀ b u,f z b i=some u→ u∈p.P ∧ f z (!b) u=some i
    uniq:∀ i∈p.P,∀ z,p.dual t z→∀ y,p.dual t y→∀ a b,f z true i=some a→f y true i=some b→ z=y

namespace Streams
variable {p:Dome}{t f} (h:p.Streams t f)
include h
lemma throve {z}(hz:p.dual t z){i}(hi:i∈p.P)(b:Bool):p.pour t z b i=f z b i:=by
   unfold pour
   rw [ite_eq_left ⟨hz,hi⟩,p.grab (h.runs z hz i hi b clearG p.cleared)]
   cases he:f z b i <;> simp [AtM]
lemma lines {z}(hz:p.dual t z){i}(hi:i∈p.P)(b:Bool):p.curve t z b i=f z b i:=by
   unfold curve
   by_cases he : f z b i=none
   · rw [h.throve hz hi,he]; split<;> rfl
   rw [ite_eq_left ?_,h.throve hz hi]
   cases b
   · left; rfl
   right; intro u w hh
   by_cases hm : p.dual t u
   · rw [h.throve hm hi] at hh
     cases h0:f z true i with
     | none=> contradiction
     | some a=> exact h.uniq i hi u hm z hz w a hh h0
   unfold pour at hh; rw [ite_eq_right (fun e=>hm e.1)] at hh; contradiction
lemma canonicalS : p.Streams t (p.curve t):=by
   constructor
   · intro z hz i hi b a ha; rw [h.lines hz hi]; exact h.runs z hz i hi b a ha
   · intro z hz i hi b u he
     rw [h.lines hz hi] at he; obtain ⟨hk,hA⟩:=h.swaps z hz i hi b u he; exact ⟨hk,(h.lines hz hk _).trans hA⟩
   intro i hi z hz j hj a b ha hb; exact p.uniquely ha hb
end Streams

def fuel (q:ℕ)(a:Pane): Mill.Fuel :=
   ⟨p.l,q,p.P,glove a,p.echo,p.curve⟩

structure Ears0 (u:ℕ):Prop where
   hum :∀ q,unitK q=u→p.audible q→date q  ≤  p.high u→∀ i∈p.P,∃ v,p.swears q i v
   rate :∀ t,cell t=u→ (∃ z,p.dual t z)→ ∃ f,p.Streams t f
/-- Artificial terminal configurations get only replies already covered
by the W induction. -/
def Heard (u:ℕ): Prop:= ∀ v:ℕ,p.active v→p.W v<p.W u→p.won v 0→p.Ears0 v
lemma ascent (r:Rune){A q t:ℕ}{w:Pane} (h:p.Shape) (ha:1  ≤  A)(hb:A  ≤  p.slope)
      (hp:p.won (unitK q) (date q))(he:(Mill.mk A r p.s.vent).entitled (p.fuel q w) t):
    p.won (unitK t) (date t) ∧ p.W (unitK t) < p.W (unitK q):=by
   rcases he with ⟨v,hk,hl⟩
   have hu:p.l.jump A ⟨p.W (unitK q),date q⟩ 1 v t:=by
       unfold Lot.jump; rw [h.strut]; exact ⟨hk,hl⟩
   change p.W (unitK t)+1  ≤  p.W (unitK q) at hk
   exact ⟨h.migrate hp hu rfl ha hb,hk⟩
lemma fires (r:Rune){A q:ℕ} (h:p.Shape) (ha:1 ≤ A)(hb:A ≤ p.slope)
      (he:p.won (unitK q) (date q)) (hp:p.Heard (unitK q))(hh:1 ≤ p.W (unitK q))
      {a}(hw:p.r.proper a):
    (Mill.mk A r p.s.vent).Fires (p.fuel q a) := by
    refine ⟨ha,hh,(fun q=>h.strut q),fun i hi=>h.account i hi a hw,?_ ,?_,fun {_ _ _ _ _ _} e f =>p.uniquely e f⟩
    · intro t ht hu i hi
      obtain ⟨hk,hl⟩:=p.ascent r h ha hb he hu
      have hP:=p.till (unitK t) (date t)|>.1 hk
      obtain ⟨v,hv⟩:= (hp _ (h.auth t ht) hl hP.2).hum t rfl ht hP.1 i hi
      change p.talk t (glove a i) (p.echo t i,glove a i)
      rw [p.identity hv]; exact hv a hw
    intro t z hz ht i hi b
    obtain ⟨hk,hl⟩:=p.ascent r h ha hb he (ht b)
    change p.won (unitK (p.pulseQ t z b)) (date (p.pulseQ t z b)) at hk
    change p.W (unitK (p.pulseQ t z b)) < _ at hl
    rw [p.pulseB,p.day] at hk; rw [p.pulseB] at hl
    obtain ⟨f,hp⟩:= (hp _ (h.may t z hz) hl hk).rate t rfl ⟨z,hz⟩
    have he0:= hp.canonicalS
    exact ⟨he0.runs z hz i hi b a hw,he0.swaps z hz i hi b⟩
end
end Dome
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod
open Seats
namespace Dome
variable (p:Dome)

def chord (u:ℕ)(i x:ℕ) : Seats :=
      { head:={l:=p.l,w:=p.W u,d:=p.D u,src:=glove clearG i,info:=x}
        pass0:=fun n=>∃ a,p.r.proper a∧n=glove a i
        hm:= ⟨clearG,p.cleared,rfl⟩ }
abbrev orch (u i x:ℕ):Seats:=p.chord u i (hole u x)
structure Suite (u:ℕ):Prop where
    shape:p.Shape
    stage:p.active u
    paid:p.won u 0
    well:0 < p.D u∧p.D u ≤  p.W u

structure Sings (u i x c v:ℕ):Prop where
    within:Punct (p.orch u i x).head c v
    ovation:p.swears (bell u x 0) i v

structure StageW (u i x H j:ℕ)(V:ℝ)(w:Tape): Prop where
   scored:Checked w (V/(2:ℝ)^j) H
   glad:∀ t ≤ H,p.swears (bell u x t) i (enc (dsign w t))
abbrev Voice (p:Dome)(u i x H j:ℕ)(V:ℝ):= ∃ w,p.StageW u i x H j V w

namespace Suite
variable {p:Dome}{u}(h:p.Suite u)
include h
lemma pit {i}(hi:i∈p.P)(q):hasOK (p.chord u i q):=by
    rintro n ⟨a,hp,rfl⟩
    exact ⟨h.well.1,h.well.2,h.shape.account i hi a hp⟩
/-- Issue after inserting a command in the main program. -/
lemma hired (f:ℕ)(t:ℕ)(hl:bell u f t ≤ p.F.limit){i b c}
    (he:1  ≤  c)(hh:c ≤ p.slope)
    (hg:Lot.Mane p.l c ⟨p.W u,t⟩ (p.D u) (bell u f t) p.l.P (0,i) b):
    p.talk (bell u f t) i b:= by
   refine (hg.mono hh he).issue ?_ hl h.shape.rateC
   rw [h.shape.bookB]

lemma concert {i q c v} (he:1 ≤  c)(hh:c ≤ p.slope)(hk:Punct (p.orch u i q).head c v)
   (hf:bell u q 0 ≤ p.F.limit) (hp: rite (p.orch u i q) c p.l.P v) :
    p.Sings u i q c v:=by
   refine ⟨hk,fun a ha=> h.hired q 0 hf he hh ?_⟩
   exact hp (glove a i) ⟨a,ha,rfl⟩

lemma dance {i q c f H v}(he:1 ≤  c)(hh:c ≤ p.slope)(hr : band (p.orch u i q) c H f p.l.P v)
   (hp:∀ j ≤ H,bell u q j ≤ p.F.limit):
   p.Voice u i q H (f*p.D u) v:=by
   obtain ⟨w,hw⟩:=hr
   refine ⟨w, (hw _ (hm ..)).1, fun t ht a ha=>h.hired q t (hp t ht) he hh ?_⟩
   exact (hw (glove a i) ⟨a,ha,rfl⟩).2.digits t ht

lemma descend {v:ℕ}(hk:p.W v+p.D u  ≤  p.W u): p.won v 0 ∧
                 p.high u+p.slope*p.D u ≤ p.high v:= by
   have h0:=p.future h.paid
   have hp:=Nat.mul_le_mul_left p.slope hk
   have hr:p.loadC v (p.high u+p.slope*p.D u) ≤  p.H:= by unfold won loadC at *; nlinarith
   obtain ⟨hz,hh⟩:= (p.till ..).1 hr; exact ⟨hh,hz⟩

lemma pull_shot {v:ℕ} (hk:p.W v+p.D u ≤ p.W u)(i t q)
     {c z:ℕ}(hz:Punct (p.chord u i q).head c z)(hm:1 ≤ c)(x:ℕ):p.l.jump c ⟨p.W u,t⟩ (p.D u) z (bell v x t):=by
   unfold Lot.jump; rw [h.shape.bookB v]
   dsimp only; refine ⟨hk,movespan (punctspan hz hm (p:=(p.chord u i q).head)) ?_⟩
   change p.D u ≤ _; omega

end Suite

/- virtual underlying p.chord, map info to hole for the external shot. -/
namespace Bullet
def lookup (P:Cub ℕ ℕ)(x:Word)(a:Slip):ℕ :=
   let v:History:=dec a.1
   postcard (P.f x v.1) v.2
lemma lookupK(P):Kn (lookup P):=by
   have h:= (Kn.unpack (α:=History)).comp (Kn.first (β:=ℕ))
   exact Kn.wash.comp ((P.runs.comp h.left).tuple h.right)
def snap (f:Cub ℕ ℕ) : Cog := .toss ⟨_,lookupK f⟩ ⟨_,Kn.next⟩
lemma past (p:Dome){u v q y:ℕ}{f:Cub ℕ ℕ}{c i:ℕ}
     (he : p.Suite u)(hm:2 ≤ c)(hz:i∈p.P)
     (hh:p.W v+p.D u ≤ p.W u)(hr:f.f p.x q=hole v y)
     (t b j:ℕ)(h1:j∈p.P)(ht:Punct (p.chord u i q).head c b)
     {a a':Pane}(ha:p.r.proper a)(ha':p.r.proper a')
     (hv:p.talk (bell v y t) (glove a i) (b,glove a' j)):
    Lot.Mane p.l c ⟨p.W u,t⟩ (p.D u) (postcard q t) (snap f)
            (0,glove a i) (b,glove a' j):=by
   let sr (a:Pane)(j:ℕ):=(p.chord u j q).seat (glove a j)
   have hph (j) (e:j∈p.P)(a)(ha:p.r.proper a):(sr a j).OK:=he.pit e q (glove a j) ⟨a,ha,rfl⟩
   apply Lot.Mane.toss (q':=bell v y t) (a':=(b,glove a' j)) _ rfl _ _ _ hv
   · change lookup f p.x _=_; simp only [lookup,postcard,dec_round,hr,bell]
   · exact plight (punct0 (hph i hz a ha) hm) (hph _ hz _ ha) (le_trans (by omega) hm)
   · exact plight (p:=sr a' j) ht (hph j h1 _ ha') (by omega)
   apply he.pull_shot hh i t q _ (by omega)
   exact punct0 (has_home (he.pit hz q)) hm

lemma copy (p:Dome){u v q y:ℕ}{f:Cub ℕ ℕ}{c i:ℕ}
     (he : p.Suite u)(hm:2 ≤ c)(hz:i∈p.P)
     (hh:p.W v+p.D u ≤ p.W u)(hr:f.f p.x q=hole v y)
     {t b:ℕ}(ht:Punct (p.chord u i q).head c b)(hv:p.swears (bell v y t) i b):
    hear (p.chord u i q) t c (snap f) 0 b:=by
   rintro x ⟨a,ha,rfl⟩
   exact past p he hm hz hh hr t b i hz ht ha ha (hv a ha)

abbrev roomS:=lb capD+4
lemma clef (p:Dome){u v q y:ℕ}{f:Cub ℕ ℕ}{c i:ℕ}
     (he:p.Suite u)(hm:roomS ≤ c)(hz:i∈p.P)
     (hh:p.W v+p.D u ≤ p.W u)(hr:f.f p.x q=hole v y)
     {H E S}(ht:S ≤ H){X:ℝ}(hv:p.Voice v i y H (E*p.D u) X):
   band (p.chord u i q) c S E (snap f) X:= by
   obtain ⟨w,hA,hv⟩:=hv
   refine ⟨w,fun x hx=>⟨⟨hA.1,fun t hg=> hA.2 t (hg.trans ht)⟩,⟨fun t hg=>?_⟩⟩⟩
   have he1:=safe_d hA (hg.trans ht)
   have hl : Punct (p.chord u i q).head c (enc (dsign w t)):=by
      unfold Punct; have hh : lb (enc (dsign w t)) ≤  lb capD:=lb_mono (slate_le _ he1)
      have hi:=he.well.1; change _+_ ≤  c*p.D u
      unfold roomS at hm; nlinarith
   exact copy p he (by unfold roomS at hm; omega) hz hh hr hl (hv t (hg.trans ht)) x hx

end Bullet
end Dome
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod Dome _root_.OAI.ExactDerandomization.Sub

/-- Shared interface of the instructions at a pointer. alpha is the
unit ultimately offering the visit (test tag offered by another unit).
Knot is a pure capped append on designated paths. -/
structure Cone where
   limit : Cub ℕ ℕ
   pad : Cub ℕ ℕ
   spur : Cub Mint.Node ℕ
   head : Cub Bean ℕ
   tail0 : Cub Bean ℕ
   bud : Cub Bean ℕ
   nest : Cub Bean ℕ
   splitQ : Cub Bean Bool
   tip : Cub Bean ℕ
   ispath0 : Cub ℕ Bool
   shift : Cub Bean History
structure Road where
   start:Cub ℕ ℕ
   ports:Cub ℕ ℕ
   steps:Cub ℕ ℕ
   chant:Cub Bean ℕ
   clockG:Cub Mint.Node ℕ

namespace Cone
variable (p:Cone)
def bow (v:Road):Sub.Bow:=⟨v.start,p.limit,v.ports,v.steps,v.chant,v.clockG,p.pad,p.spur,p.head,p.tail0,p.bud,p.nest,p.splitQ⟩

structure ConeX where
    D:Dome
    N:ℕ
    e:ℕ
namespace ConeX
variable (r:ConeX)
abbrev ear (a i:ℕ):ℕ:=p.spur.f r.D.x (a,i)
abbrev stem (a i h:ℕ) :Bean:= (a,i,h)
abbrev h0 (a i h:ℕ):=p.head.f r.D.x (stem a i h)
abbrev f0 (a i h:ℕ):=p.tail0.f r.D.x (stem a i h)
abbrev s1 (a i h:ℕ):=p.bud.f r.D.x (stem a i h)
abbrev i1 (a i h:ℕ):=p.nest.f r.D.x (stem a i h)
abbrev b1 (a i h:ℕ):=p.splitQ.f r.D.x (stem a i h)
abbrev ip (a i h:ℕ):=p.tip.f r.D.x (stem a i h)
abbrev n (a:ℕ):=r.D.D a
def GoodX (a:ℕ) := r.D.active a ∧ 1 ≤ r.n a ∧ r.n a ≤ r.D.W a ∧ a ≤ r.N
abbrev less (a q:ℕ):=r.D.W (unitK q)+r.n a ≤ r.D.W a
abbrev wideQ (a v:ℕ):=lb v ≤ r.e*r.n a

structure BaseX (a i:ℕ):Prop where
   posX :4 ≤  r.e
   lowp : r.GoodX a
   under0:r.wideQ a i
   value:p.pad.f r.D.x a=2^(r.n a)
   onQ : r.D.audible (r.ear p a i)
   clock0 : date (r.ear p a i)=0
   cheap:r.less a (r.ear p a i)
   tokenpoint:p.ispath0.f r.D.x a=true
def Allow(a t h:ℕ):=r.D.dual t h ∧ r.D.W (cell t)+r.n a ≤ r.D.W a
noncomputable section
structure Point (a i h x m m' y:ℕ):Prop where
   baseX :BaseX p r a i
   bornD:h≠0
   spoken:r.D.echo (r.ear p a i) x=h
   wid0:r.wideQ a h
   lid:r.wideQ a (r.ip p a i h)
   vHead:r.Allow a (r.h0 p a i h) (r.ip p a i h)
   vTail:r.Allow a (r.f0 p a i h) 0
   hx:x∈r.D.P
   hm:m∈r.D.P
   hm':m'∈r.D.P
   hy:y∈r.D.P
   face:r.D.curve (r.h0 p a i h) (r.ip p a i h) true x=some m
   left:r.D.curve (r.f0 p a i h) 0 true m'=some y
   station:min r.D.peak ((p.shift.f r.D.x (stem a i h)).1*m'+(p.shift.f r.D.x (stem a i h)).2)=y

inductive Pond : ℕ→ℕ→ℕ→ℕ→ℕ→Prop
    | leaf {a i h x m y} (h0:r.Point p a i h x m m y) (h1:r.b1 p a i h=false): Pond a i h x y
    | born {a i h h' x m m' y} (h0:r.Point p a i h x m m' y)(h1:r.b1 p a i h=true)
             (hp:r.D.W (r.s1 p a i h)+r.n a  ≤  r.D.W a)
             (he:r.n (r.s1 p a i h)  ≤  2*r.n a)
             (hh:Pond (r.s1 p a i h) (r.i1 p a i h) h' m m') : Pond a i h x y
def dry(a i x:ℕ):=r.BaseX p a i∧ x∈r.D.P∧ r.D.echo (r.ear p a i) x=0
inductive Flora (a i x:ℕ):Option (ℕ×ℕ)→Prop
   | abs (h:r.dry p a i x):Flora a i x none
   | wet {h y}(hz:r.Pond p a i h x y):Flora a i x (some (h,y))

def pen (v:Road)(A k q:ℕ)(f:Pane): Quill:= ⟨p.bow v, r.D.s.vent,r.D.fuel q f,k,A,r.n,r.D.W⟩
abbrev ambient (a i h z j:ℕ):Jet:=(j,i,h,z,p.pad.f r.D.x a)

lemma little {v A k q f}(ht:100*r.e ≤ k){a i h z j:ℕ}(hm:r.BaseX p a i)(he:r.wideQ a h)(hx:r.wideQ a z)
     (hr:j ≤ 5):
    (r.pen p v A k q f).little a (r.ambient p a i h z j):=by
    have he4:=hm.posX
    have hd:1 ≤ r.n a:=hm.lowp.2.1
    let u:= p.pad.f r.D.x a
    let e:=enc (z,u); let w:=enc (h,e); let m:=enc (i,w); let n:=enc (j,m)
    have hL(r s:ℕ) : lb s ≤ lb (enc (r,s)) ∧ lb (enc (r,s)) ≤  2*lb r+lb s+2:=
                  ⟨Quill.rightP r s,measure_pair ..⟩
    have hp:lb u= r.n a+1:= by unfold u; rw [hm.value,lb_shift]
    have h1: lb u ≤ lb e ∧ lb e ≤  2*lb z+lb u+2:=hL z u
    have h2: lb e ≤ lb w ∧ lb w ≤ 2*lb h+lb e+2:=hL h e
    have h3: lb w ≤ lb m ∧ lb m ≤ 2*lb i+lb w+2:=hL i w
    have h4: lb m ≤ lb n ∧ lb n ≤ 2*lb j+lb m+2:=hL j m
    have hc:=lb_le_inc j
    change r.n a  ≤  lb n ∧ lb n  ≤  k*r.n a
    have hz: lb i  ≤  r.e*r.n a:=hm.under0
    unfold wideQ at *
    refine ⟨by omega,?_⟩
    nlinarith [Nat.mul_le_mul_right (r.n a) ht]
lemma award {v A k q f}(ht:100*r.e ≤ k)(hb:r.N ≤ p.limit.f r.D.x q){a i}(he:r.BaseX p a i):
    (r.pen p v A k q f).Rating a i:=by
    have h1:=he.posX; have hh:1 ≤ r.n a:=he.lowp.2.1
    have hz : r.wideQ a 0:=by unfold wideQ; rw [lb_zero]; nlinarith
    exact ⟨he.lowp.2.2.2.trans hb,he.lowp.2.1,he.lowp.2.2.1,r.little p ht he hz hz (Nat.zero_le _),he.onQ,he.clock0,he.cheap⟩
lemma orderly {a t z} (h:r.Allow a t z)(v A k q f):
     (r.pen p v A k q f).Orders a t z:=by
   refine ⟨h.1,fun b=>?_⟩
   let u:=r.D.pulseQ t z b
   change date u=0 ∧ r.D.W (unitK u)+r.n a ≤ _
   rw [show unitK u=cell t from r.D.pulseB ..,r.D.day]; exact ⟨rfl,h.2⟩
lemma targeted {v A k q f}(ht:100*r.e ≤ k)(hb:r.N ≤ p.limit.f r.D.x q) {a i h x m m' y}
    (hz:r.Point p a i h x m m' y):
     (r.pen p v A k q f).Chess a i h (r.ip p a i h) x m m' y:=by
    have he:=hz.baseX
    have h1:=he.posX; have hh:1  ≤  r.n a:=he.lowp.2.1
    have h0:r.wideQ a 0:=by unfold wideQ; rw [lb_zero]; nlinarith
    refine ⟨r.award p ht hb he,?_,hz.hx,hz.hm,hz.hm',hz.hy,hz.spoken,hz.bornD,hz.face,hz.left⟩
    exact ⟨r.little p ht he hz.wid0 h0 (by omega:1 ≤ (5:ℕ)),fun i hi=>r.little p ht he hz.wid0 hz.lid hi,
                        r.orderly p hz.vHead ..,r.orderly p hz.vTail ..⟩
lemma archway {v A k q f}(ht:100*r.e ≤ k)(hb:r.N ≤ p.limit.f r.D.x q) {a i h x y}
    (hz:r.Pond p a i h x y):
     (r.pen p v A k q f).Herd a i x h (r.ip p a i h) y:=by
   induction hz with
   | leaf he hp=> exact .solo (r.targeted p ht hb he) hp
   | born he hp hx hy _ ih=> exact .pair (r.targeted p ht hb he) hp hx hy ih
lemma coronet {v A k q f}(ht:100*r.e ≤ k)(hb:r.N ≤ p.limit.f r.D.x q) {a i x L}
    (hz:r.Flora p a i x L):
    (r.pen p v A k q f).Lane a i x (L.map Prod.snd):=by
    cases hz with
    | abs h=>exact .dry (r.award p ht hb h.1) h.2.1 h.2.2
    | wet h=>exact .born (r.archway p ht hb h)

end
end ConeX
end Cone
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod Dome Cone Cone.ConeX
/-! A visit can apply a pure lamp at its endpoint. The affine suffix
is threaded through its delegation. Saturating in the composition here
means all absolute requests use a fixed polynomial ceiling. -/
abbrev Arch:=ℕ×ℕ
abbrev NoteM:= Arch×ℕ
abbrev Face:=ℕ×NoteM
abbrev Pr:=History × Pane
def ray0 (M:ℕ)(a:Arch)(x:ℕ):ℕ:=min M (a.1*x+a.2)
def concatJ (M:ℕ)(a b:Arch):Arch:=(min M (a.1*b.1), ray0 M a b.2)
lemma sofJ (M:ℕ)(a b:Arch)(x:ℕ):ray0 M (concatJ M a b) x=ray0 M a (ray0 M b x):=by
    have he (p q): min M (p+min M q)=min M (p+q):=by omega
    have hp (p q r): min M (min M p*q+r)=min M (p*q+r):=by
        by_cases h:p ≤ M
        · simp [h]
        by_cases hu:q=0
        · simp [hu]
        rw [min_eq_left (show M ≤ p by omega)]
        have h1:M ≤ M*q+r:=by nlinarith [Nat.one_le_iff_ne_zero.mpr hu]
        have h2:M ≤ p*q+r:=by nlinarith [Nat.one_le_iff_ne_zero.mpr hu]
        rw [min_eq_left h1,min_eq_left h2]
    dsimp only [ray0,concatJ]
    rw [he,hp,mul_comm a.1 (min M _),hp]
    congr 1; ring
structure Harp where
   p:Cone
   S:Scheme
   cap: Cub ℕ ℕ
   lamp : Cub Pr (Bool × Pane)

namespace Harp
variable (v:Harp)
abbrev quoteQ(a i:ℕ)(q:NoteM):ℕ := bell a (enc ((i,q):Face)) 0
def keys (_:Word)(q:ℕ):Face:=dec (which q)
lemma keysK:Kn keys:=Kn.unpack.comp ((((Kn.unpack (α:=History)).comp tokenK.left)).right)
def rim0 (_:Word)(q:ℕ):Mint.Node:=(unitK q,(keys [] q).1)
lemma rimK:Kn rim0:= unitK0.tuple keysK.left
def fillQ(x:Word)(q:ℕ):ℕ:=v.p.spur.f x (rim0 x q)
lemma fillK:Kn v.fillQ:=v.p.spur.runs.comp rimK
def roads (x:Word)(q:Slip):Bean:=(unitK q.1,(keys x q.1).1,q.2)
lemma roadsK:Kn roads:=(unitK0.comp Kn.first).tuple ((keysK.comp Kn.first).left.tuple Kn.next)
def hopX(b:Bool)(x:Word)(q:Slip):ℕ:=v.S.before b x (v.p.head.f x (roads x q),v.p.tip.f x (roads x q))
lemma hopK(b):Kn (v.hopX b):=(v.S.beforeK b).comp ((v.p.head.runs.comp roadsK).tuple (v.p.tip.runs.comp roadsK))

variable {α}[Wire α]
lemma rayK {i:PT α ℕ}{p:PT α Arch}{j:PT α ℕ}(hi:Kn i)(hs:Kn p)(hj:Kn j):
   Kn (fun x a=>ray0 (i x a) (p x a) (j x a)):=hi.small ((hs.left.times hj).add hs.right)
lemma concatK {i:PT α ℕ}{p q:PT α Arch}(hi:Kn i)(hs:Kn p)(ht:Kn q):
   Kn (fun x a=>concatJ (i x a) (p x a) (q x a)):=(hi.small (hs.left.times ht.left)).tuple (rayK hi hs ht.right)
def port (x:Word):ℕ:=v.cap.f x 0
lemma portK : Kn (fun x (_:α)=> v.port x):= v.cap.runs.comp (Kn.fix 0)
def thru (x:Word)(a:Bean)(m:NoteM):NoteM:=(concatJ (v.port x) m.1 (v.p.shift.f x a),m.2)
def mapJ (x:Word)(q:Slip):NoteM:= v.thru x (roads x q) (keys x q.1).2
lemma mapK:Kn v.mapJ:=by
   have h:= (keysK.comp (Kn.first (β:=ℕ))).right
   exact (concatK v.portK h.left (v.p.shift.runs.comp roadsK)).tuple h.right
def pen0 (x:Word)(q:Slip):ℕ:=quoteQ (v.p.bud.f x (roads x q)) (v.p.nest.f x (roads x q)) (v.mapJ x q)
lemma penK:Kn v.pen0:=by
   have h:= Kn.wash.comp ((v.p.bud.runs.comp roadsK).tuple (Kn.wash.comp ((v.p.nest.runs.comp roadsK).tuple v.mapK)))
   exact Kn.wash.comp (h.tuple (Kn.fix _))

def lit(x:Word)(q:NoteM)(i:ℕ)(p:Pane):Bool×Pane:=v.lamp.f x ((q.2,ray0 (v.port x) q.1 i),p)
def handle (x:Word)(q:Plot):Site:=
    let a:=v.mapJ x (q.1,q.2.1)
    let (i,p):Foot:= dec q.2.2
    let b:=v.lit x a i p
    (enc b.1, glove b.2 i)
lemma handleK:Kn v.handle:=by
   have h:= v.mapK.comp ((Kn.first (β:=Site)).tuple Kn.next.left)
   have hp:= (Kn.unpack (α:=Foot)).comp (Kn.next (α:=ℕ) (β:=Site)).right
   have he:= v.lamp.runs.comp ((h.right.tuple (rayK v.portK h.left hp.left)).tuple hp.right)
   exact (Kn.wash.comp he.left).tuple (Kn.wash.comp (hp.left.tuple he.right))

def cueV : Vase :=
    ⟨⟨_,v.fillK⟩,fun b=>⟨_,v.hopK b⟩,⟨_,v.p.splitQ.runs.comp roadsK⟩,⟨_,v.penK⟩,⟨_,v.handleK⟩⟩

@[simp] lemma keyp (x a i p): keys x (quoteQ a i p)=(i,p):=by simp [keys,quoteQ]
@[simp] lemma path0 (x a i p z) : roads x (quoteQ a i p,z)=stem a i z:=by simp [roads,quoteQ]
lemma again (x:Word)(q:Bean)(j:NoteM)(t i:ℕ)(e:ray0 (v.port x) (v.p.shift.f x q) i=t)(p:Pane):
    v.lit x (v.thru x q j) i p=v.lit x j t p:=by simp only [thru,lit,sofJ,e]
end Harp
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod Dome Cone Cone.ConeX

namespace Harp
noncomputable section
variable (p:Harp)
structure Wick where
    r:ConeX
    admit0:ℕ
namespace Wick
variable (z:Wick)
abbrev d:=z.r.D
def Ok(q:NoteM):=q.2  ≤  z.admit0 ∧q.1.1  ≤  z.d.peak∧ q.1.2  ≤  z.d.peak
def state (q:NoteM)(i:ℕ) (h:Option (ℕ×ℕ))(a:Pane):Site:=
    match h with
    | none=>(0,glove a i)
    | some v=>
       let b:=p.lit z.d.x q v.2 a
       (enc b.1,glove b.2 i)
def Veil (a:ℕ) :=∀ i q,z.Ok q→∀ x n,z.r.Flora p.p a i x n→∀ f,z.d.r.proper f→
         z.d.talk (quoteQ a i q) (glove f x) (z.state p q x n f)
abbrev den0 (a i:ℕ)(q:NoteM):Vase.Den :=
    ⟨z.d.l,z.d.W a,z.d.D a,quoteQ a i q,z.r.e⟩
structure Life : Prop where
    stage0 : z.d.Shape
    peak : p.port z.d.x=z.d.peak
    sig : p.S=z.d.s
    sober : ∀ q,z.Ok q→∀ i∈z.d.P,∀ a,z.d.r.proper a→ z.d.r.proper (p.lit z.d.x q i a).2

namespace Life
variable {p:Harp}{z:Wick}(h:z.Life p) {u:ℕ}(he:z.d.Suite u)(hz:z.d.Heard u)
include h he hz

omit h hz in
private lemma den_good {i}(hs:z.r.BaseX p.p u i) (q): (den0 z u i q).good:=
   ⟨hs.posX,he.well⟩

omit h in
private lemma lower0 {v:ℕ}(hh:z.d.active v)(hs:z.d.W v+z.d.D u  ≤   z.d.W u):z.d.Ears0 v:= by
    have hv:= he.well.1
    exact hz v hh (by omega) (he.descend hs).1
lemma announce {i x f}(hs:z.r.BaseX p.p u i)(hh:x∈z.d.P)(a:ℕ)(hk:z.r.wideQ u a)
      (hf:z.d.echo (z.r.ear p.p u i) x=a)(ha:z.d.r.proper f)(q) :
      (z.den0 u i q).meets p.cueV.start (0,glove f x) (a,glove f x):=by
   let t:=z.r.ear p.p u i; let C:=z.den0 u i q
   have hu:z.d.Ears0 (unitK t):=lower0 he hz (h.stage0.auth t hs.onQ) hs.cheap
   have ht:p.cueV.ask.f z.d.x C.q=t:=by simp [cueV,C,rim0,fillQ,quoteQ,t,ear,keys]
   apply Vase.perform _ (den_good he hs q) _ _ hk
   · change _+_  ≤  _ ∧ _
     change (z.d.l.book (p.cueV.ask.f z.d.x C.q)).w+_  ≤  _ ∧ (z.d.l.book _).t=_
     rw [ht,h.stage0.strut]
     exact ⟨hs.cheap,hs.clock0⟩
   change z.d.talk (p.cueV.ask.f z.d.x C.q) (glove f x) _
   rw [ht,← hf]
   obtain ⟨v,hp⟩:= hu.hum t rfl hs.onQ (le_trans (le_of_eq hs.clock0) (Nat.zero_le _)) x hh
   rw [z.d.identity hp]; exact hp f ha

private lemma emerges {i h0 x y q f m m'} (w:z.r.Point p.p u i h0 x m m' y)
    (hr:z.Ok q)(hw:z.d.r.proper f)
    (hR:z.r.b1 p.p u i h0=true → z.d.W (z.r.s1 p.p u i h0)+ z.r.n u   ≤   z.d.W u ∧
             ∃ e,z.d.talk
                  (quoteQ (z.r.s1 p.p u i h0) (z.r.i1 p.p u i h0) (p.thru z.d.x (stem u i h0) q))
                  (glove f m) (z.state p (p.thru z.d.x (stem u i h0) q) m (some (e,m')) f))
    (hD:z.r.b1 p.p u i h0=false → m=m'):
   (z.den0 u i q).meets p.cueV.play (0,glove f x) (z.state p q x (some (h0,y)) f):=by
   let r:= z.r; let P:=z.d
   let v:=p.cueV; let d:= z.den0 u i q
   let t:=r.h0 p.p u i h0; let e:=r.ip p.p u i h0
   have hg:=den_good he w.baseX q
   let vk:=p.lit z.d.x q y f
   have hl:z.d.r.proper vk.2:=h.sober q hr y w.hy f hw
   have hb:d.bit (enc vk.1):=by
      have hk:lb (enc vk.1)=1:=by cases vu:vk.1 <;> rfl
      have hx := he.well.1; have ha:=w.baseX.posX
      unfold Vase.Den.bit; rw [hk]; change 1  ≤  z.r.e*z.d.D u; nlinarith
   have ht:=w.vHead
   have hp : P.Ears0 (cell t):=lower0 he hz (h.stage0.may _ _ ht.1) ht.2
   obtain ⟨f1,hF⟩:=hp.rate t rfl ⟨e,ht.1⟩
   have hu := hF.canonicalS
   have hQ(b:Bool): (v.probe b).f z.d.x (d.q,h0)=P.pulseQ t e b:=by
           simp only [v,d,cueV,hopX,path0,h.sig]; rfl
   have hv:v.dives.f z.d.x (d.q,h0)=r.b1 p.p u i h0 :=by
           simp only [v,d,cueV,path0]; rfl
   have hc:P.curve t e false m=some x:= (hu.swaps e ht.1 x w.hx true m w.face).2
   let R:= stem u i h0
   have hal:p.lit z.d.x (p.thru z.d.x R q) m' f=vk:=
           p.again z.d.x R q y m' (by rw [ray0,h.peak]; exact w.station) f
   apply v.arrives hg w.wid0 hb (h.announce he hz w.baseX w.hx _ w.wid0 w.spoken hw q) w.bornD
                (y:=glove f m) (z:=glove vk.2 m)
   · intro b
     change (z.d.l.book ((v.probe b).f z.d.x (d.q,h0))).w+_   ≤  _ ∧ (z.d.l.book _).t=_
     rw [hQ,h.stage0.strut]
     change P.W (unitK (P.pulseQ t e b))+_  ≤  _∧ date (P.pulseQ t e b)=0
     rw [P.pulseB]; exact ⟨ht.2,P.day ..⟩
   · have he:=hu.runs e ht.1 x w.hx true f hw
     rw [w.face] at he
     change P.talk ((v.probe true).f z.d.x (d.q,h0)) _ _
     rw [hQ]; exact he
   · have hh:=hu.runs e ht.1 m w.hm false vk.2 hl
     rw [hc] at hh
     change P.talk ((v.probe false).f z.d.x (d.q,h0)) _ _
     rw [hQ]; exact hh
   · intro hh
     obtain ⟨hk,b,hy⟩:= hR (hv.symm.trans hh)
     let V:=r.s1 p.p u i h0; let n:= r.i1 p.p u i h0
     have hw':v.bud.f z.d.x (d.q,h0)=quoteQ V n (p.thru z.d.x R q):=by
             simp only [v,cueV,d,pen0,mapJ,path0,keyp]; rfl
     change ((z.d.l.book (v.bud.f z.d.x (d.q,h0))).w+d.d  ≤   _∧ (z.d.l.book _).t=0)∧
                 P.talk (v.bud.f z.d.x (d.q,h0)) _ _
     rw [hw',h.stage0.bookB]; refine ⟨⟨hk,rfl⟩,?_⟩
     have hX : z.state p (p.thru z.d.x R q) m (some (b,m')) f=(enc vk.1,glove vk.2 m):=by
                dsimp only [state]; rw [hal]
     rw [hX] at hy; exact hy
   intro hh
   have hm:m=m':=hD (hv.symm.trans hh)
   subst m'
   simp only [v,cueV,handle,mapJ,path0,keyp,glove,dec_round]
   change (enc (p.lit z.d.x (p.thru z.d.x R q) m f).1,_)=_
   rw [hal]
set_option maxHeartbeats 800000 in
theorem offers {q i x n f} (hs:z.Ok q)(hh:z.r.Flora p.p u i x n)(ha:z.d.r.proper f)
     (hm:∀ v,z.d.active v→z.d.W v < z.d.W u→z.d.won v 0→z.Veil p v):
   (z.den0 u i q).meets p.cueV.play (0,glove f x) (z.state p q x n f):=by
    cases hh with
    | abs h0=>
      obtain ⟨h1,h2,h3⟩:=h0
      have hp:=den_good he h1 q
      exact Vase.failed _ (announce h he hz h1 h2 0 (Vase.Den.bit0 _ hp) h3 ha q)
    | wet h0=>
      rename_i hi0 hi1
      cases h0 with
      | leaf hA hD=>
        exact emerges h he hz hA hs ha (fun hm=>by rw [hD] at hm; contradiction) (fun _=>rfl)
      | @born a i h3 e x j l y hA hB hC hD h0=>
        refine emerges h he hz hA hs ha ?_ (fun h=>by rw [hB] at h; contradiction)
        intro _
        refine ⟨hC,e,?_⟩
        let m:=z.r.s1 p.p u i hi0
        have hF:z.d.active m:=by cases h0 with
                         | leaf h1 h2=> exact h1.baseX.lowp.1
                         | born h1 h2 _ _ _=> exact h1.baseX.lowp.1
        have hN:z.d.W m < z.d.W u:=by have hl : z.d.W m+z.d.D u  ≤  z.d.W u:=hC; have:=he.well.1; omega
        apply hm m hF hN (he.descend hC).1 _ _ _ j _ (.wet h0) f ha
        change _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
        unfold thru concatJ ray0
        rw [h.peak]
        exact ⟨hs.1, min_le_left .., min_le_left ..⟩

/- entering via authorized control branch: use for visit-ops Units. -/

lemma veiled (hm:∀ v,z.d.active v→z.d.W v < z.d.W u→z.d.won v 0→z.Veil p v)
     (hl:Vase.Den.charge (z.den0 u 0 ((0,0),0))  ≤  z.d.slope)
     (hx:∀ i q,z.Ok q→ z.r.BaseX p.p u i→quoteQ u i q ≤ z.d.F.limit)
     (hc:∀ i q,z.Ok q→ z.r.BaseX p.p u i→ ∀ v w,(z.den0 u i q).meets p.cueV.play v w→
                          (z.den0 u i q).meets z.d.l.P v w):z.Veil p u:=by
     intro i q hv x n f a ht
     have hr : z.r.BaseX p.p u i:=by
        cases f with
        | abs h=>exact h.1
        | wet h=>cases h with
             | leaf h1 _=>exact h1.baseX
             | born h1 _ _ _ _=>exact h1.baseX
     have ht:= offers h he hz hv f ht hm
     have hz0 :1  ≤  Vase.Den.charge (z.den0 u i q):=by
        change 1 ≤ 10*z.r.e; have hr := hr.posX; omega
     exact he.hired _ _ (hx i q hv hr) hz0 hl (hc i q hv hr _ _ ht)
end Life
end Wick
end
end Harp
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod Dome Cone Cone.ConeX _root_.OAI.ExactDerandomization.Sub
noncomputable section

structure Ember where
    r:ConeX
    p:Cone
    R:Road
    a:ℕ
    slots:ℕ
    k:ℕ
    A:ℕ
    u:ℕ
    slotv:ℕ
    φ: ℕ → ℕ → Option (ℕ×ℕ)
namespace Ember
variable (e:Ember)
abbrev D:=e.r.D
abbrev Q(t:ℕ):=bell e.u e.slotv t
abbrev q(t)(b:Pane):=e.r.pen e.p e.R e.A e.k (e.Q t) b
abbrev fav :ℕ → ℕ → Option ℕ:= fun x i=> (e.φ x i).map Prod.snd

/-- Input ring geometry. -/
structure Trust : Prop where
     supply:e.D.Suite e.u
     prepay:e.D.Heard e.u
     face:e.D.D e.u=1
     core:e.D.D e.a=1
     entry:e.D.W e.a  ≤  e.D.W e.u
     skeleton:100  ≤  e.k
     inner:100*e.r.e  ≤  e.k
     budget:1000*e.k^2  ≤  e.A
     ear:e.A ≤ e.D.slope
     boundp:∀ i<e.slots,lb i ≤  e.k
     plan:∀ i∈e.D.P,∀ j<e.slots,e.r.Flora e.p e.a j i (e.φ i j)
structure Bridge (t:ℕ):Prop where
     allowed: t ≤ e.D.high e.u
     anointed:e.R.start.f e.D.x (e.Q t)=e.a
     roomQ:e.r.N  ≤  e.p.limit.f e.D.x (e.Q t)
     slotm:e.R.ports.f e.D.x (e.Q t)=e.slots
     warms:e.R.steps.f e.D.x (e.Q t) ≤ t+e.k
     enc0: 2^(charge e.A (e.D.W e.u) t)  ≤  e.D.s.hoard.f e.D.x (e.Q t)
namespace Bridge
variable {e:Ember}{t:ℕ}(h:e.Bridge t)(p:e.Trust)
include h p

lemma lit (b:Pane)(hb:e.D.r.proper b): (e.q t b).Tidy:=by
    let z:=e.q t b
    have heB:z.B= ⟨e.D.W e.u,t⟩:=e.D.s.born e.u e.slotv t e.D.x
    have hev:z.child=e.a:=h.anointed
    have hA:1 ≤  e.A:=by have h0:=p.budget; have h1:=p.skeleton; nlinarith
    have hz:e.D.won (unitK (e.Q t)) (date (e.Q t)):=by
                rw [bellU,bellT]; exact (e.D.till ..).2 ⟨h.allowed,p.supply.paid⟩
    refine ⟨e.D.fires _ p.supply.shape hA p.ear hz ?_ ?_ hb,p.skeleton,p.budget,?_,rfl,?_,?_,?_⟩
    · rw [bellU]; exact p.prepay
    · rw [bellU]; exact le_trans p.supply.well.1 p.supply.well.2
    · change 2^(charge z.A z.B.w z.B.t)  ≤  _
      rw [heB]; exact h.enc0
    · change z.H  ≤  z.B.t+_
      rw [heB]; exact h.warms
    · change e.D.D z.child=1; rw [hev,p.core]
    change e.D.W z.child ≤ z.B.w; rw [heB,hev]; exact p.entry

lemma grove {b:Pane}{i x:ℕ}(hi:x∈e.D.P)(hp:i < e.slots):
                       (e.q t b).Lane (e.q t b).child i x (e.fav x i):=by
   rw [show (e.q t b).child=e.a from h.anointed]
   exact e.r.coronet e.p p.inner h.roomQ (p.plan x hi i hp)

end Bridge
end Ember

end
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod Dome Cone Cone.ConeX _root_.OAI.ExactDerandomization.Sub Plaza
noncomputable section

namespace Ember
variable (e:Ember)
structure Quilt:Prop where
    h:e.Trust
    p:e.Bridge 0
    level0:e.R.steps.f e.D.x (e.Q 0)=0
    scent0:e.R.clockG.f e.D.x (e.Q 0,1)=0
def pie (l:ℕ→List Gem)(b:Pane):Deck:=⟨e.q 0 b,e.fav,l⟩
namespace Quilt
variable {e:Ember}(h:e.Quilt)
include h
private lemma lotc(b:Pane):
     let z:=e.q 0 b
     z.Suite e.fav∧ z.H=0∧ z.Stringent (sealG z):=by
   let z:=e.q 0 b
   have h1:z.H=0:=h.level0
   have h2:sealG z=0:=h.scent0
   have hz:z.Stringent (sealG z):=by
       unfold Quill.Stringent; rw [h1,h2]
       rw [lb_zero]; have he:=h.h.skeleton
       change _ ≤ _∧_ ≤  e.k*_; omega
   refine ⟨⟨fun a ha i hi=>⟨h.p.grove h.h ha (show i<e.slots by
       change i<e.R.ports.f e.D.x (e.Q 0) at hi; rw [h.p.slotm] at hi; exact hi),?_⟩⟩,h1,hz⟩
   have hu:z.b.ports.f z.x0 z.q=e.slots:= h.p.slotm
   have hh (j:ℕ) (ht:j<z.H): False:=by omega
   have hb:i<e.slots:=hi.trans_le hu.le
   have hp:z.Gown i a:= ⟨h.h.boundp i hb,hi,fun j hj=>(hh j hj).elim,fun j hj=>(hh j hj).elim,by
             unfold Quill.scent; rw [h1]; exact hz⟩
   exact hp

theorem quilted :∃ l:ℕ→ List Gem,∀ b:Pane,∀ hb:e.D.r.proper b,
             (e.pie l b).Licence (h.p.lit h.h b hb):=by
   obtain ⟨h1,h2,hz⟩:=h.lotc clearG
   let z:=e.q 0 clearG; have hs:z.Tidy:=h.p.lit h.h _ e.D.cleared
   classical
   have hx(i:ℕ):∃ l,i∈e.D.P → z.Wheel hs e.fav (sealG z) i l:=by
       by_cases he:i∈e.D.P
       · obtain ⟨l,h0⟩:=z.beat hs h1 hz he; exact ⟨l,fun _=>h0⟩
       exact ⟨[],fun h=> (he h).elim⟩
   choose l hl using hx
   exact ⟨l,fun b hb=>⟨(h.lotc b).2.1,(h.lotc b).2.2,(h.lotc b).1,fun i hi=>z.past (hl i hi) (w:=Dome.glove b)
                         (show (z.gloved (Dome.glove b)).Tidy from h.p.lit h.h b hb)⟩⟩
end Quilt

abbrev stepC (A:ℕ):= A*(2*A+40)
variable (l:ℕ→List Gem)
structure Mouth (h:e.Quilt):Prop where
   fitL:∀ b:Pane,∀ hb:e.D.r.proper b,(e.pie l b).Licence (h.p.lit h.h b hb)
abbrev cutWay (p:Cone)(r:Road)(v:Scheme)(A:ℕ)(k i j:ℕ)(b:Bool):Cog:=
   let u:= p.bow r
   let m:Mill := ⟨A,u.Rune0,v.vent⟩
   if b then Plaza.forwardp u m k i j else Plaza.reversep u m k i j
def pathOp (b:Bool) (k i j:ℕ)(a c:ℕ):Prop:=
   if b then (e.pie l clearG).takes k i j a c else (e.pie l clearG).takes k i j c a
open scoped Classical
def valueOf (k i:ℕ): Dome.Tide:= fun j b a=>
    if h:∃ c,e.pathOp l b k i j a c then some (Classical.choose h) else none
namespace Mouth
variable {e l h}(s:Mouth e l h)
include s
lemma disp {b k i j a c}: e.valueOf l k i j b a=some c ↔ pathOp e l b k i j a c :=by
   let d:=e.pie l clearG
   have hz:=s.fitL clearG e.D.cleared
   have hm:∀ u,pathOp e l b k i j a u → pathOp e l b k i j a c → u=c:=by
      intro u hu hc
      cases b
      · exact (d.back0 hu hc).1
      exact (hz.agree hu hc).1
   unfold valueOf; split
   · next e0=>
     obtain hu:=Classical.choose_spec e0
     constructor
     · intro v; rwa [← Option.some.inj v]
     exact fun hk=>congrArg some (hm _ hu hk)
   next e0=>exact ⟨fun v=>by contradiction,fun h=> (e0 ⟨_,h⟩).elim⟩
lemma sole {b k i j a z} (hp:Deck.atpred (pathOp e l b k i j a) z):
    z=e.valueOf l k i j b a:=by
   have hh (w):z=some w↔_:= (hp w).symm.trans s.disp.symm
   cases e1:z <;> cases e2:e.valueOf l k i j b a <;> grind

lemma pointIn {b k i j a c}(he:pathOp e l b k i j a c):
      c∈e.D.P ∧ a∈e.D.P :=by
   have hz:=s.fitL clearG e.D.cleared
   let d:=e.pie l clearG
   have hh {u v}: d.takes k i j u v → u∈d.dom := by exact fun ha=> ((hz.traceL ha.1).1 (Deck.rimmem ha.2.2).1).1
   cases b
   · change d.takes .. at he; exact ⟨hh he,he.1⟩
   change d.takes .. at he; exact ⟨he.1,hh he⟩

omit s in
lemma exchange0 {k i j a c} (b:Bool):pathOp e l b k i j a c ↔ pathOp e l (!b) k i j c a:=by cases b <;> rfl
lemma unique0 {k i j a c x y} (h1:e.valueOf l k i j true a=some c)(he:e.valueOf l k i x true a= some y):
    x=j:=by
   have hz:=s.fitL clearG e.D.cleared
   exact (hz.agree (s.disp.1 he) (s.disp.1 h1)).2

theorem clearsWay (k:ℕ)(i:ℕ) (hi:i< e.slots)(r:ℕ)(b:Bool){a f} (he:a∈e.D.P)(hf:e.D.r.proper f) :
    Lot.Mane e.D.l (stepC e.A) ⟨e.D.W e.u,0⟩ 1 (e.Q 0) (cutWay e.p e.R e.D.s e.A k i r b)
                      (0,glove f a) (AtM (e.valueOf l k i r b a) f a):=by
   let d:=e.pie l f
   have hz:= s.fitL f hf
   have hk : stepC e.A=d.u.p.price:= rfl
   have hw : d.u.B=⟨e.D.W e.u,0⟩ := e.D.s.born ..
   cases b
   · obtain ⟨v,ht,hq⟩:=d.beam (k:=k) (r:=r) (i:=i) _ hz he
     have he' : v=e.valueOf l k i r false a:=s.sole (b:=false) ht
     rw [← he']
     change Lot.Mane e.D.l d.u.p.price _ _ _ _ _ _
     rw [←hw]
     cases v <;> exact hq
   obtain ⟨v,ht,hq⟩:=d.era (k:=k) (r:=r) (i:=i) _ hz he (lt_of_lt_of_eq hi h.p.slotm.symm)
   have he' : v=e.valueOf l k i r true a:=s.sole (b:=true) ht
   rw [← he']
   change Lot.Mane e.D.l d.u.p.price _ _ _ _ _ _
   rw [←hw]
   cases v <;> exact hq
end Mouth
end Ember
end
end ExactDerandomization.Chime

end

section

namespace ExactDerandomization.Chime
open Counter Relay Rill Glass Fret Mint Swirl Finset Scheme Glass.Rod Dome Cone Cone.ConeX _root_.OAI.ExactDerandomization.Sub Plaza
open Analysis
noncomputable section
namespace Ember

structure Forest (e:Ember) where
    topk : PowerTop
    H:ℕ
    k:ℕ
    F:ℕ → ℕ → ℝ
    w:ℕ → ℕ → Tape
variable {e:Ember}
namespace Forest
variable (v:Forest e)
abbrev q(_v:Forest e)(t i j:ℕ):ℕ:=e.R.chant.f e.D.x (e.Q t,i,j)
structure Archive:Prop where
   h:e.Trust
   p:∀ t ≤ v.H,e.Bridge t
   safe:∀ i< e.slots,∀ a∈e.D.P,0 ≤  v.F a i∧ Checked (v.w a i) (v.F a i) v.H
   lit :∀ t ≤ v.H,v.topk.f e.D.x (e.Q t)=2^t
   crest:∀ t ≤ v.H,e.R.steps.f e.D.x (e.Q t)= t+1
   seals :e.R.clockG.f=padValue v.topk
   space : lb capD  ≤  e.k
   lamp :∀ t ≤ v.H,∀ i<e.slots,∀ j ≤ t,
           let q:=v.q t i j
           e.D.audible q∧ date q ≤ t-j∧ e.D.W (unitK q)<e.D.W e.u ∧
                ∀ x∈ e.D.P,e.D.echo q x= enc (dsign (v.w x i) (t-j))

abbrev S (e:Ember)(c:ℕ):Finset ℕ := ((e.D.P ×ˢ range e.slots).filter
               (fun a=> e.fav a.1 a.2=some c)).image enc
def teaN (t i:ℕ):ℕ:= let a:History:=dec i; tagsA (2^t) (v.w a.1 a.2) t
abbrev V0(i:ℕ):ℝ:= let a:History:=dec i; v.F a.1 a.2
abbrev scoreRank (x:ℕ):ℝ:= rank (S e x) v.V0 v.k
abbrev scoreTape (x:ℕ):Tape:=fun t=> rankN (S e x) (v.teaN t) v.k

namespace Archive
variable {v:Forest e}(h:v.Archive)
include h
lemma stage0 {t}(ht:t ≤  v.H)(i x b)(hx:x∈ e.D.P)(hi:i < e.slots):
       let q:=e.q t b
       q.scent i x=(2^t)+v.teaN t (hole x i) := by
   let q:=e.q t b
   have hh:q.H=t+1:=h.crest t ht
   have he:= (h.safe i hi x hx).2
   have hu : Checked (v.w x i) (v.F x i) t:=⟨he.1,fun j hj=> he.2 j (hj.trans ht)⟩
   have hr : q.chainR i x (t+1)= mesh (rakeword (v.w x i) t) :=
                         chaints (fun j hj=> (h.lamp t ht i hi j hj).2.2.2 x hx)
   change e.R.clockG.f e.D.x (e.Q t,q.chainR i x q.H)=_
   rw [hh,hr,h.seals]
   simp only [padValue,cutcorrect e.D.x hu,h.lit t ht,teaN,hole,dec_round,tagsA]

lemma gears {t}(ht:t ≤ v.H){b}(hb:e.D.r.proper b):
                  (e.q t b).Suite e.fav:= by
   let q:=e.q t b
   have ht0:=h.p t ht; have hk:q.Tidy:= ht0.lit h.h b hb
   refine ⟨fun i hi j hj=> ?_⟩
   have hx:i∈e.D.P:=hi
   have hm:j<e.slots:=lt_of_lt_of_eq hj ht0.slotm
   have hh:q.H=t+1:=h.crest t ht
   refine ⟨ht0.grove h.h hx hm, ⟨h.h.boundp _ hm,hj,?_,?_,?_⟩⟩
   · intro l hl
     change l<q.H at hl
     have hz:l ≤ t:=by omega
     change lb (e.D.echo (v.q t j l) i)  ≤ e.k
     rw [(h.lamp t ht j hm l hz).2.2.2 i hx]
     apply le_trans (lb_mono (slate_le _ (safe_d (h.safe j hm i hx).2 (by omega)))) h.space
   · intro l hl; change l<q.H at hl; have hz:l ≤ t:=by omega
     have hp:q.B= ⟨e.D.W e.u,t⟩ := e.D.s.born ..
     obtain ⟨h1,h2,h3,h4⟩:= h.lamp t ht j hm l hz
     change _+_ ≤ q.B.t+_∧_+1 ≤ q.B.w ∧_
     rw [hp]; refine ⟨?_,h3,h1⟩
     change l+date (v.q t j l)  ≤  t+_; omega
   change q.Stringent (q.scent j i)
   rw [h.stage0 ht _ i _ hx hm]
   exact stringentQ hk hh (min_le_left ..)

omit h in
lemma unsealed {i c:ℕ}(hi:i∈ S e c):
   let a:History:=dec i
   a.1∈e.D.P ∧ a.2 < e.slots ∧ i=enc a∧ e.fav a.1 a.2=some c := by
    obtain ⟨j,hj,rfl⟩:=mem_image.1 hi
    dsimp only; rw [dec_round]
    obtain ⟨ha,hb⟩:=mem_filter.1 hj; obtain ⟨hz,hv⟩:=mem_product.1 ha
    exact ⟨hz,mem_range.1 hv,rfl,hb⟩

lemma estimated (c:ℕ):Checked (v.scoreTape c) (v.scoreRank c) v.H:=by
    let X:=S e c
    have hk(i:ℕ)(hi:i∈X):0  ≤  v.V0 i∧Checked
                            (v.w (token i).1 (token i).2) (v.V0 i) v.H :=
          h.safe _ ((unsealed (e := e)) hi).2.1 _ ((unsealed (e := e)) hi).1
    have hp: |v.scoreRank c| ≤ 1:= show |v.scoreRank c|  ≤  1 from by
       rw [abs_of_nonneg (rank_nn ..)]; exact rank_le (by norm_num) (fun i hi=>(abs_le.1 (hk i hi).2.1).2)
    refine ⟨hp,fun t ht=>?_⟩
    have he : |((rankN X (v.teaN t) v.k):ℝ)- 2^t*scoreRank v c| ≤ 2:=by
       rw [rankN_v,scoreRank,← scaled_rank (by positivity)]; apply rank_lip (by norm_num)
       intro i hi; obtain ⟨h1,h2,h3⟩:=hk i hi
       exact tag_est h1 ⟨h2,fun l hl=> h3 l (hl.trans ht)⟩
    unfold scoreTape; push_cast; exact he

lemma counted {t}(ht:t ≤ v.H){c o b}{l:List Gem}{hp:(e.q t b).Tidy}
       (_:c∈e.D.P)(_:o ≤ (2:ℕ)^t)(hz:(e.q t b).Wheel hp e.fav (2^t+o) c l) :
    tinc (S e c) (v.teaN t) o=l.length:=by
   classical
   let U:=(S e c).filter (fun i=> teaN v t i =o)
   let f(i:ℕ):Gem:=pledge (token i).1 (token i).2
   have he:l.toFinset=U.image f:=by
      ext w; rw [List.mem_toFinset,hz.members]; constructor
      · rintro ⟨a,ha,i,hm,hq,hx,hy⟩
        have h1:i<e.slots:=lt_of_lt_of_eq hm (h.p t ht).slotm
        have hu : hole a i∈S e c:=mem_image.2 ⟨(a,i),mem_filter.2
                                      ⟨mem_product.2 ⟨ha,mem_range.2 h1⟩,hx⟩,rfl⟩
        have he:teaN v t (hole a i)=o:=by
             rw [h.stage0 ht _ _ _ ha h1] at hy; omega
        exact mem_image.2 ⟨hole a i,mem_filter.2 ⟨hu,he⟩,by rw [hq]; simp only [f,token,hole,dec_round]; rfl⟩
      rintro hh; obtain ⟨i,he,rfl⟩:=mem_image.1 hh
      obtain ⟨ha,hb⟩:=mem_filter.1 he
      obtain ⟨hf,hg,hk,hL⟩:=(unsealed (e := e)) ha
      have hz' : i=hole (token i).1 (token i).2:=hk
      exact ⟨(token i).1,hf,(token i).2,lt_of_lt_of_eq hg (h.p t ht).slotm.symm,
             rfl,hL,by rw [h.stage0 ht (token i).2 (token i).1 b hf hg,← hz',hb]⟩
   have hp:(U.image f).card= U.card:=card_image_iff.2 fun i hi j hj hh=>by
      have hu:= pledge_eq.1 hh
      have hk : token i=token j :=Prod.ext hu.1 hu.2
      apply Eq.trans ((unsealed (e := e)) (mem_filter.1 hi).1).2.2.1
      change enc (token i)=j; rw [hk]; exact ((unsealed (e := e)) (mem_filter.1 hj).1).2.2.1.symm
   change U.card=l.length
   rw [← hp, ← he,List.toFinset_card_of_nodup hz.unique]

end Archive
abbrev Bcost:= e.A*(2*e.A+40)+6*(v.k+50)
abbrev trackG (p:Cone)(r:Road)(s:Scheme)(A:ℕ)(P:PowerTop)(k:ℕ):Cog:=
    (WheelTop.mk ⟨A,(p.bow r).Rune0,s.vent⟩ P k).track
abbrev engine :=liftarm (trackG e.p e.R e.D.s e.A v.topk v.k)

namespace Archive
variable {v:Forest e}(h:v.Archive)
include h
lemma digit {t}(ht:t ≤ v.H){x}(hx:x∈e.D.P){b}(hb:e.D.r.proper b):
       Lot.Mane e.D.l v.Bcost ⟨e.D.W e.u,t⟩ 1 (e.Q t) (trackG e.p e.R e.D.s e.A v.topk v.k) (0,glove b x)
                        (codeQ (v.scoreTape x t),glove b x):=by
   classical
   let q:=e.q t b
   have h1:q.H=t+1:=h.crest t ht; have h2:=h.gears ht hb; have hp:q.Tidy:=(h.p t ht).lit h.h b hb
   have hs(i:ℕ)(hi:i ≤ (2:ℕ)^t):q.Stringent (2^t+i):=stringentQ hp h1 hi
   have he(i:ℕ):∃ l,i ≤ (2:ℕ)^t→q.Wheel hp e.fav (2^t+i) x l:=by
       by_cases hk:i ≤ (2:ℕ)^t
       · obtain ⟨l,h⟩:=q.beat hp h2 (hs i hk) hx; exact ⟨l,fun _=>h⟩
       exact ⟨[],fun h=> (hk h).elim⟩
   choose l hl using he
   let f:Isle:=⟨q,e.fav,l,x,S e x,v.teaN t,v.topk,v.k⟩
   have hc:f.P=(2:ℕ)^t:= h.lit t ht
   have hk:f.Wrap hp:=by
       refine ⟨hx,fun i hi=>?_,fun i hi=> by change q.Stringent (f.P+i); rw [hc]; exact hs i (hi.trans hc.le),fun i hi hz=>?_ ,fun i hi=>?_⟩
       · change q.Wheel hp e.fav (f.P+i) x (l i)
         rw [hc]; exact hl i (hi.trans hc.le)
       · exact h.counted ht hx (hi.trans hc.le) (hl i (hi.trans hc.le))
       exact le_trans (min_le_left ..) hc.ge
   have hb0:q.B=⟨e.D.W e.u,t⟩:= e.D.s.born ..
   rw [← hb0]
   have hp0 : v.Bcost=f.pay:=by unfold Bcost Isle.pay Isle.pay1 Isle.speed; change _=e.A*(2*e.A+40)+3*(v.k+50)+3*(v.k+50); omega
   rw [hp0]; exact hk.cash

lemma fullplan {i}(hi:i∈e.D.P):
     (e.D.orch e.u i e.slotv).loud (powder v.Bcost) v.H 0 v.engine (v.scoreRank i) (v.scoreTape i):=by
   rintro a ⟨b,hb,rfl⟩
   let p:Port:=(e.D.orch e.u i e.slotv).seat (glove b i)
   have hg:p.OK:=h.h.supply.pit hi (hole e.u e.slotv) _ ⟨_,hb,rfl⟩
   have he:100 ≤  v.Bcost:=by unfold Bcost; omega
   apply lifting hg he
   · intro t ht
     have hp:=h.digit ht hi hb
     change Lot.Mane _ _ _ (e.D.D e.u) _ _ _ _
     rw [h.h.face]
     exact hp
   · have hp:=h.estimated i; simpa only [Fret.massB,Nat.zero_mul,pow_zero,div_one] using hp

end Archive
end Forest
end Ember
end
end ExactDerandomization.Chime

end

end OAI
