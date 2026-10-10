import OAI.Computability.Logspace.EstimatorInterfaces

namespace OAI

/-!
Finite query combinators and transparent Bernoulli operations.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Arena
open Counter Relay Rill Glass Fret Mint Swirl Finset Chime Scheme Glass.Rod
open Fret.Seats Chime.Dome

/-! Small combinators on Dome requests. All queries renormalized to
a local "info" origin. External typing covers any wind. -/

abbrev Sight:=Cub ℕ ℕ
abbrev Kiwi:=Cub ℕ History

namespace Pier
noncomputable section

variable (p:Dome)
variable {u q x y c z t:ℕ}
abbrev StampX (x:ℕ)(h:ℕ)(r:Dome)(u c:ℕ):= Fret.Punct (r.chord u 0 x).head c h
lemma seal0 (he:p.Suite u)(hi:2  ≤  c):StampX q 0 p u c:= by
   have hs:=he.well.1; unfold StampX Fret.Punct; rw [lb_zero]; change 1+1 ≤ c*p.D u
   nlinarith
lemma seal1 (he:p.Suite u)(hi:2 ≤ c) :StampX q 1 p u c:= by
   have hs:=he.well.1; unfold StampX Fret.Punct; rw [lb_one]; change 1+1  ≤  c*p.D u
   nlinarith
lemma seal_bit (he:p.Suite u)(hi:2 ≤ c) (b:Bool):StampX q (enc b) p u c:=by
   cases b
   · exact seal0 p he hi
   exact seal1 p he hi
lemma seal_mark {H:ℕ}{w:Tape}{V:ℝ}(he:p.Suite u)(hi:Dome.Bullet.roomS ≤ c)
   (hv:Checked w V H){t:ℕ}(hh:t ≤ H): StampX q (enc (dsign w t)) p u c:=by
   have hr:= lb_mono (slate_le _ (safe_d hv hh))
   unfold StampX Fret.Punct; change _+1  ≤ c*p.D u
   unfold Dome.Bullet.roomS at hi; have he1:=he.well.1; nlinarith

/-- A reserved opaque motion; synaptic grab may also return "no".
(motion called only at address clock=0; enclosing data operations
strip their shot clock while keeping bounded record). -/
structure Liaison (x:ℕ) (u:ℕ)(t i:ℕ) : Prop where
   pays: p.W (cell t)+p.D u ≤ p.W u
   xem:x∈p.P
   holds:p.dual t i
   ready:p.Streams t (p.curve t)

def onyx (f:Kiwi) (s:Scheme)(b:Bool)(x:Word)(a:Slip):ℕ:=
      s.before b x (f.f x (Scheme.token a.1).1)
lemma onyxK(f:Kiwi)(s:Scheme)(b):Kn (onyx f s b):=
      (s.beforeK b).comp (f.runs.comp (tokenK.left.comp Kn.first))
def walk (s:Scheme)(f:Kiwi)(b:Bool)(m:Bool):Cog :=
      .toss ⟨_,onyxK f s b⟩ (if m then ⟨_,Kn.next⟩ else ⟨_,Kn.first.right.tuple Kn.next.right⟩)

section
variable {p:Dome} {u i x y t q z c:ℕ}{f:Kiwi}
  (hu:p.Suite u)(hc:2 ≤ c)(he:Liaison p x u t i)
include hu hc he

lemma shares (b:Bool)(a:Pane)(hp:p.r.proper a)(hs:f.f p.x q=(t,i)):
     ((p.chord u x q).seat (glove a x)).comp 0 c (walk p.s f b true) (0,glove a x)
                                (AtM (p.curve t i b x) a x):= by
   let P:=fun x=> (p.chord u x q).seat (glove a x)
   have hz (x:ℕ)(h:x∈p.P):(P x).OK:=hu.pit h q _ ⟨a,hp,rfl⟩
   have hy := hu.pull_shot he.pays x 0 q (seal0 p hu hc (q:=q)) (by omega:1 ≤ c) ((p.s.loc b).f p.x (t,i))
   refine Lot.Mane.toss (q':=p.pulseQ t i b) (a':=AtM (p.curve t i b x) a x) ?_ rfl
               (plight (p:=P x) (seal0 p hu hc (q:=q)) (hz _ he.xem) (by omega))
               ?_ hy (he.ready.runs i he.holds x he.xem b a hp)
   · change onyx f p.s b p.x (postcard q 0,0)=_
     unfold onyx; simp only [Scheme.token,postcard,dec_round,hs]
   cases hh:p.curve t i b x with
   | none=> exact plight (p:=P x) (seal0 p hu hc (q:=q)) (hz _ he.xem) (by omega)
   | some v=> exact plight (p:=P v) (seal1 p hu hc (q:=q)) (hz _ (he.ready.swaps i he.holds x he.xem b v hh).1) (by omega)

lemma stroll {j n:ℕ}(hr:StampX q n p u c) (b:Bool)(a:Pane)(hp:p.r.proper a)
     (hs:f.f p.x q=(t,i)) (hz:p.curve t i b x=some y):
    ((p.chord u x q).seat (glove a x)).comp j c (walk p.s f b false) (n,glove a x) (n,glove a y):= by
   let P:=fun x=>(p.chord u x q).seat (glove a x)
   have hl(x:ℕ)(h:x∈p.P):(P x).OK:=hu.pit h q _ ⟨a,hp,rfl⟩
   have hy:=he.ready.swaps i he.holds x he.xem b y hz
   refine Lot.Mane.toss (q':=p.pulseQ t i b) (a':=(1,glove a y)) ?_ rfl
          (plight (p:=P x) hr (hl _ he.xem) (by omega)) (plight (p:=P y) hr (hl _ hy.1) (by omega)) ?_ ?_
   · change onyx f p.s b p.x (postcard q j,n)=_
     unfold onyx; simp only [Scheme.token,postcard,dec_round,hs]
   · have hx:=hu.pull_shot he.pays x 0 q hr (by omega: 1 ≤ c) ((p.s.loc b).f p.x (t,i))
     refine ⟨hx.1,le_trans hx.2 ?_⟩; change c*0+c*c*(p.W u-(p.l.book _).w) ≤ c*j+c*c*(p.W u-(p.l.book (p.pulseQ t i b)).w)
     rw [mul_zero,zero_add]; exact Nat.le_add_left _ _
   have hz' := he.ready.runs i he.holds x he.xem b a hp; rw [hz] at hz'; exact hz'

omit hu hc in
lemma street (hz:p.curve t i true x=some y):Liaison p y u t i :=
    ⟨he.pays,(he.ready.swaps i he.holds x he.xem true y hz).1, he.holds,he.ready⟩
end

def escort (s:Scheme) (f:Kiwi) (q:Cog) : Cog:=
     .seq (walk s f true false) (.seq q (walk s f false false))
variable {p:Dome}{u i x y t q z c:ℕ}{f:Kiwi}
  (hu:p.Suite u)(hc:2 ≤ c)(he:Liaison p x u t i)
include hu hc he
lemma cups (hs:f.f p.x q=(t,i))(hz:p.curve t i true x=some y) (g:Cog)
     {H v:ℕ}(hv: StampX q v p u c)(hr:(p.chord u y q).hear H c g 0 v):
    (p.chord u x q).hear H c (escort p.s f g) 0 v:= by
   rintro _ ⟨f,hf,rfl⟩
   exact .seq (stroll hu hc he (seal0 p hu hc) true f hf hs hz) (.seq
              (hr _ ⟨f,hf,rfl⟩) (stroll hu hc (street he hz)
                  hv false f hf hs (he.ready.swaps i he.holds x he.xem true y hz).2))

lemma bowls (hi: Bullet.roomS ≤ c)
     (hs:f.f p.x q=(t,i))(hz:p.curve t i true x=some y) (g:Cog)
     {H v:ℕ}{V:ℝ}(hr:(p.chord u y q).band c H v g V):
    (p.chord u x q).band c H v (escort p.s f g) V:=by
    obtain ⟨w,h⟩:=hr
    have hb:Checked w (V/massB v (p.D u)) H:= (h _ ⟨clearG,p.cleared,rfl⟩).1
    have hp (t:ℕ)(ht:t ≤ H): hear (p.chord u y q) t c g 0 (enc (dsign w t)):= fun x hx=>
                                                 (h _ hx).2.digits t ht
    exact ⟨w,fun a ha=> ⟨hb,⟨fun t ht=> cups hu hc he hs hz g (seal_mark _ hu hi hb ht)
                                                      (hp t ht) _ ha⟩⟩⟩
end
end Pier

/- local switch after a small tag. cost raised simultaneously. -/
namespace Iris
variable {p:Seats}{k m c:ℕ}{v:ℕ → Cog}{C:Cog}

abbrev matchQ (i:ℕ) : Flag:= ⟨_,Kn.next.left.eq (Kn.fix i)⟩
def through (p:ℕ → Cog):ℕ → Cog
    | 0=>.seq Cargo.knock (p 0)
    | i+1=>.bif (matchQ (i+1)) (.seq Cargo.knock (p (i+1))) (through p i)
def dial (u:Cog)(p:ℕ → Cog)(i:ℕ):Cog:=
    .seq (Cog.ren ⟨_,Cargo.stripK⟩ u) (through p i)

lemma remise (q:Port){c k a t m:ℕ}{v:ℕ → Cog}(h:k ≤ m)
    (hi:q.l.state c ⟨q.w,t⟩ (k,q.src))(he:q.comp t c (v k) (q.s 0) (q.s a)):
    q.comp t c (through v m) (q.s k) (q.s a):=by
    have hf:q.comp t c (.seq Cargo.knock (v k)) (q.s k) (q.s a):=
            .seq (etches _ _ (i:=k) rfl hi he.spots.1) he
    induction m with
    | zero=>have hv:k=0:=by omega
            subst k; exact hf
    | succ i ih=> by_cases hh:k=i+1
                  · subst k; exact .yes (show decide (i+1=i+1)=true by simp) hf
                  exact .no (show decide (k=i+1)=false by simp [hh]) (ih (by omega))

lemma rosary {t y:ℕ}(h:k ≤ m)(hp:p.rite c C k)(he:p.hear t c (v k) 0 y):
        p.hear t c (dial C v m) 0 y:=by
    intro x hx; have hz:=Cargo.expands (p:=p.seat x) (t:=t) (hp x hx)
    exact .seq hz (remise (p.seat x) h hz.spots.2 (he x hx))
lemma parcel {H v0:ℕ}{V:ℝ}(h:k ≤ m)(hp:p.rite c C k)(he:p.band c H v0 (v k) V):
        p.band c H v0 (dial C v m) V:=by
   obtain ⟨w,hq⟩:=he
   have he(t:ℕ)(hr:t ≤ H): p.hear t c (v k) 0 (enc (dsign w t)):= fun x hx=> (hq x hx).2.digits t hr
   exact ⟨w,fun _ hx=> ⟨(hq _ hx).1,⟨fun t ht=> rosary h hp (he t ht) _ hx⟩⟩⟩
end Iris

end ExactDerandomization.Arena

end

section

namespace ExactDerandomization.Arena
open Counter Relay Rill Glass Fret Mint Swirl Finset Chime Scheme Glass.Rod
open Fret.Seats Chime.Dome Pier
noncomputable section
open scoped Classical

namespace Flash

/-- Probe a pure function of (info, cursor) before any descent. -/
def search (g:Cub (ℕ×ℕ) ℕ):Cog :=
    let h:= (g.runs.comp ((tokenK.left.comp Kn.first).tuple
                                 (((Kn.unpack (α:=Foot)).comp Kn.next.right)).left))
    Cog.edit ⟨_,h.tuple Kn.next.right⟩

variable (p:Dome) {u c q x:ℕ}
lemma found (hu:p.Suite u)(hx:x∈p.P)(hc:2 ≤ c)
   {g:Cub (ℕ×ℕ) ℕ}{m:ℕ}(hg:g.f p.x (q,x)=m)(hp:StampX q m p u c):
   (p.chord u x q).rite c (search g) m:=by
    rintro _ ⟨a,ha,rfl⟩
    let S:= (p.chord u x q).seat (glove a x)
    have hf:S.OK:=hu.pit hx _ _ ⟨a,ha,rfl⟩
    refine Lot.Mane.edit ?_ (plight (p:=S) (seal0 p (q:=q) hu hc) hf (by omega)) (plight (p:=S) hp hf (by omega))
    change (g.f _ ((Scheme.token _).1,(dec _:Foot).1),_)=_
    simp only [token,postcard,glove,dec_round]; exact congrArg (fun i=> (i,enc (x,a))) hg
def plumb (m:ℕ):Cog:= etch (α:=ℕ) (fun _ _=>m) (Kn.fix m)
lemma pureQ (hu:p.Suite u)(hx:x∈p.P)(hc:2 ≤ c)
   (m:ℕ)(hp:StampX q m p u c) : (p.chord u x q).rite c (plumb m) m:= by
    exact pointed0 (hu.pit hx q) hc (seal0 p (q:=q) hu hc) hp
abbrev chose (g:Cog)(w:ℕ):Cog:=Cargo.choose g Cargo.knock (plumb w)
abbrev win(a n:ℕ):ℕ:= if a=0 then 0 else n
lemma picks (hu:p.Suite u)(hx:x∈p.P)(hc:2 ≤ c)(a n:ℕ){g:Cog}
    (hg:(p.chord u x q).rite c g a)(hp:StampX q n p u c) :
    (p.chord u x q).rite c (chose g n) (win a n):=by
    apply Seats.steer hg
    · intro h; unfold win; rw [ite_eq_left h]; exact Seats.blankD (hu.pit hx q) hc
    intro h; unfold win; rw [ite_eq_right h]; exact pureQ p hu hx hc _ hp

abbrev demand (g w:Cog):Cog:=Cargo.choose g Cargo.knock w
lemma wanted (hu:p.Suite u)(hx:x∈p.P)(hc:2 ≤ c)(a n:ℕ){g w:Cog}
    (hg:(p.chord u x q).rite c g a)(hw:a≠0→(p.chord u x q).rite c w n) :
    (p.chord u x q).rite c (demand g w) (win a n):=by
    apply Seats.steer hg
    · intro h; unfold win; rw [ite_eq_left h]; exact Seats.blankD (hu.pit hx q) hc
    intro h; unfold win; rw [ite_eq_right h]; exact hw h
lemma win_stamped (hu:p.Suite u)(hc:2 ≤ c)(a n:ℕ)(he:StampX q n p u c):
     StampX q (win a n) p u c:= by unfold win; split; exact seal0 p hu hc; exact he
lemma brilliant(p b:Bool) : win (enc p) (enc b)=enc (p&&b):=by cases p <;> cases b <;> rfl

/-- Two threshold constants compiled as motions.Literal recipes are
regenerated without using the cursor. -/
lemma gild (u v:ℕ)(_:u ≤ v):1 ≤  v+1:= Nat.le_add_left _ _
abbrev clan (f:Sight)(w:ℕ):Kiwi:=⟨_, f.runs.tuple (Kn.fix w)⟩

abbrev garnish (P:Cub ℕ (ℕ×ℕ×NoteM)): Sight:=
   let h:= Kn.wash.comp (P.runs.left.tuple (Kn.wash.comp P.runs.right))
   ⟨_,h⟩
/-- one visit interpreted as a boolean at the endpoint, payload already rebased. -/
lemma maskB {h:Harp}{v:Harp.Wick}{b i x q:ℕ}{f:Option (ℕ×ℕ)}{C:Cub ℕ (ℕ×ℕ×NoteM)}
    (hu:v.d.Suite u)(hx:x∈v.d.P)(hc:2 ≤ c)(hh:v.d.W b+v.d.D u ≤ v.d.W u)
    (hz:v.Veil h b){m:NoteM}(hr:C.f v.d.x q=(b,i,m))(he:v.Ok m)
    (hf:v.r.Flora h.p b i x f)(a:Bool)
    (ha:match f with
        | none=>a=false
        | some (_,y) => ∀ p,v.d.r.proper p→ h.lit v.d.x m y p=(a,p)):
   (v.d.chord u x q).rite c (Dome.Bullet.snap (garnish C)) (enc a) :=by
   have hg:(garnish C).f v.d.x q=hole b (enc (i,m)):=by
            change enc ((C.f _ _).1,enc (C.f _ _).2)=_
            rw [hr]; rfl
   apply Bullet.copy v.d hu hc hx hh hg (t:=0) (seal_bit _ hu hc (q:=q) a)
   intro p hp
   have ht:= hz _ _ he _ _ hf p hp
   change v.d.talk _ _ _
   cases f with
   | none=> have hs:a=false:=ha
            subst a; exact ht
   | some g=> obtain ⟨t,y⟩:=g
              dsimp only [Harp.Wick.state] at ha ht
              rw [ha p hp] at ht; exact ht

end Flash

structure Gate where
    grab:Cog
    top:ℕ
    hue:Sight
    loyal:Cog
namespace Gate
variable (g:Gate)
open Flash
abbrev reach (k:ℕ):Kiwi:=clan g.hue (k-1)
def garden (s:Scheme):Cog:=
    let w(k):= if k=0 then Cargo.knock else
                       Pier.escort s (g.reach k) (chose g.loyal k)
    Iris.dial g.grab w g.top
def openE (s:Scheme)(f:ℕ → Cog) : Cog :=
    Iris.dial (g.garden s) f g.top

variable (p:Dome)
structure Crest (p:Dome) (u q c x i:ℕ):Prop where
    safe:(p.chord u x q).rite c g.grab i
    upper0:i ≤ g.top
    east:p.Suite u
    fine:x∈p.P
    tall:2 ≤ c
    nice:StampX q i p u c
namespace Crest
variable {p:Dome}{g:Gate}{u q c x y i z:ℕ}
lemma asleep (h:g.Crest p u q c x 0):
     (p.chord u x q).rite c (g.garden p.s) 0:=by
    apply Iris.rosary (t:=0) h.upper0 h.safe
    exact blankD (h.east.pit h.fine q) h.tall
lemma morning (h:g.Crest p u q c x i)(he:i≠0){t:ℕ}(hc:g.hue.f p.x q=t)
    (ht:Liaison p x u t (i-1))(hz:p.curve t (i-1) true x=some y)
    (hp:(p.chord u y q).rite c g.loyal z):
    (p.chord u x q).rite c (g.garden p.s) (win z i):=by
   apply Iris.rosary h.upper0 h.safe
   rw [ite_eq_right he]
   apply cups h.east h.tall ht ?_ hz _ (win_stamped p h.east h.tall z i h.nice)
          (picks p h.east (street ht hz).xem h.tall z i hp h.nice)
   exact congrArg (fun m=> (m,i-1)) hc
end Crest
end Gate
end
end ExactDerandomization.Arena

end

section

namespace ExactDerandomization.Arena
open Counter Relay Rill Glass Fret Mint Swirl Finset Chime Scheme Glass.Rod
open Fret.Seats Chime.Dome Pier Fret.Lyric Reed.Lu
noncomputable section
open scoped Classical

namespace Amber
/-- Enter a transparent Bernoulli coin (pure rational expression). -/
abbrev Tear:=Cub History Coin
abbrev here (g:Tear) :Cub CoinQuery Coin :=
    ⟨_,g.runs.comp (Kn.first.tuple (((Kn.unpack (α:=Foot)).comp Kn.next).left))⟩
abbrev moonF (g:Tear)(c:ℕ):Lyric:=.solo c (here g)
abbrev opaque0(f:Sight)(i:ℕ):Lyric:=.use i (Bullet.snap f)
abbrev syrup (g:Coin):Tear:=⟨_,Kn.fix g⟩
abbrev first0 (g:Cub ℕ Coin):Tear:=⟨_,g.runs.comp Kn.first⟩
abbrev awry(p:Knob)(i:ℕ):Tear:= first0 ⟨_,scaleK p i⟩

variable {p:Dome} {a q x y T H n:ℕ} {c d m:ℕ} {k:Knob}
lemma occlude (he:Standard (p.chord a x q) k H)(g:Tear)(r:ℕ)
   {v:ℝ}(hh:(g.f p.x (q,x)).v=v)(hb:|v|  ≤  massB r (p.D a)):
   Chor k c H (p.chord a x q) (moonF g r) v:=by
   subst v
   apply Chor.played he.st he.he ?_ hb
   rintro _ ⟨a,ha,rfl⟩
   change g.f _ (_,(dec (glove _ _):Foot).1)=_
   rw [glove,dec_round]; rfl
lemma scalingF (he:Align (p.chord a x q).head k)(r:ℕ):
   ((awry k r).f p.x (q,x)).v=massB r (p.D a):= scalen he ..

lemma normalizeF (u:p.Suite a)(r:Sight)(hc:Bullet.roomS ≤ c)(hi:x∈p.P)
   {b n t j:ℕ}(hf:r.f p.x q = hole b n)(he:p.W b+p.D a ≤ p.W a)
   {v:ℝ}(hg:p.Voice b x n t j v)(hh:H ≤ t):
   band (p.chord a x q) c H 0 (Bullet.snap r) (v/(2:ℝ)^j):=by
   refine Bullet.clef p u hc hi he hf hh ?_
   obtain ⟨w,h,hv⟩:=hg; refine ⟨w,?_,hv⟩; simpa only [Nat.zero_mul,pow_zero,div_one] using h

abbrev shade (f:Cog)(c:ℕ)(g:Tear):Lyric:= times (.use 0 f) (moonF g c)
abbrev petal(r:Sight)(c:ℕ)(g:Tear):Lyric:= shade (Bullet.snap r) c g
abbrev blossoms(f:Kiwi)(s:Scheme)(r:Sight)(c:ℕ)(g:Tear):Lyric := shade (Pier.escort s f (Bullet.snap r)) c g
lemma cast {f:Cog}{g:Tear}{j r:ℕ}(he:Standard (p.chord a x q) k H)
    {v:ℝ}(hh:band (p.chord a x q) c H 0 f (v/(2:ℝ)^j))
    (hb:(g.f p.x (q,x)).v=(2:ℝ)^j)(hr:(2:ℝ)^j ≤ massB r (p.D a)):
    Chor k c H (p.chord a x q) (shade f r g) v:=by
    have hf:=occlude (c:=c) he g r hb (by rwa [abs_of_pos (by positivity)])
    convert he.mult0 (Chor.byear hh) hf using 1; field_simp
lemma pour (u:p.Suite a)(r:Sight)(hc:Bullet.roomS ≤ c)(hi:x∈p.P)
   {b n t j:ℕ}(hf:r.f p.x q = hole b n)(he:p.W b+p.D a ≤ p.W a)
   {v:ℝ}(hg:p.Voice b x n t j v)(hh:H ≤ t)
   (h0: Standard (p.chord a x q) k H){g:Tear}{d:ℕ}(hv:(g.f p.x (q,x)).v=(2:ℝ)^j)
   (hl:(2:ℝ)^j ≤ massB d (p.D a)):Chor k c H (p.chord a x q) (petal r d g) v :=
   cast h0 (normalizeF u r hc hi hf he hg hh) hv hl
lemma seeds {f:Kiwi}(u:p.Suite a)(r:Sight)(hc:Bullet.roomS ≤ c){ψ m:ℕ}
    (h:Liaison p x a ψ m) (hs:f.f p.x q=(ψ,m))
    (hz:p.curve ψ m true x=some y)
   {b n t j:ℕ}(hf:r.f p.x q = hole b n)(he:p.W b+p.D a ≤ p.W a)
   {v:ℝ}(hg:p.Voice b y n t j v)(hh:H ≤ t)
   (h0: Standard (p.chord a x q) k H){g:Tear}{d:ℕ}(hv:(g.f p.x (q,x)).v=(2:ℝ)^j)
   (hl:(2:ℝ)^j ≤ massB d (p.D a)):Chor k c H (p.chord a x q) (blossoms f p.s r d g) v :=by
   have hr:2 ≤ c:=by unfold Bullet.roomS at hc; omega
   apply cast h0 _ hv hl
   apply bowls u hr h hc hs hz
   exact normalizeF u r hc (street h hz).xem hf he hg hh

/-- Ballot compilation including explicit reset to desired output exponent.
(Called only on successful gate, fallback zero separately). -/
abbrev roost (r:Knob)(f:Lyric)(v:ℕ) : Cog:= Lyric.choir r (reset f v)
lemma onQ {s:Seats} (r:Knob)(f:Lyric)(v:ℕ)(ht: Standard s r T)
   {x:ℝ}(hp:Chor r c T s f x)(hc:1  ≤  c) (he:H+(tail (reset f v))*s.d  ≤  T)
   (hs:(cost (reset f v) c) ≤ d) (hr:|x|  ≤  massB v s.d) :
   s.band d H v (roost r f v) x:= Seats.flex (sing (ht.ring0 hp _ hr) hc he)
                                       (cost_hi (p:=reset f v) hc) hs le_rfl

abbrev snow (r:Knob)(v:ℕ) : Cog:= Lyric.choir r (son 0 v)
lemma steam {s:Seats} (r:Knob)(v:ℕ)(ht:Standard s r H)
   (hs:powder 100 ≤ c): s.band c H v (snow r v) 0:= by
   have hp:Chor r 2 H s (son 0 v) 0:=by simpa only [Nat.cast_zero] using ht.shins 2 v 0 (by simp)
   exact flex (sing hp (by omega) (by simp [son,tail])) (cost_hi (p:=son 0 v) (c:=2) (by omega)) hs le_rfl
end Amber
end
end ExactDerandomization.Arena

end

section

namespace ExactDerandomization.Arena
open Hie Analysis Counter Relay Rill Glass Fret Mint Swirl Finset Chime Scheme Glass.Rod
open Fret.Seats Chime.Dome Pier Fret.Lyric Reed.Lu
noncomputable section
open scoped Classical
namespace Song

variable (a:Cub ℕ Bool) {P:Seats}
abbrev provided :Flag:= ⟨_,a.runs.comp (tokenK.left.comp Kn.first)⟩
def pleas (p q:Cog):Cog:= Cog.bif (provided a) p q
lemma picked {b _ _ _ _:ℕ}:0≤b:=Nat.zero_le _
lemma park {t c:ℕ} {f g:Cog}{r s:Site}{v:Port}
    (hp:a.f v.l.x v.info=true)(he:v.comp t c f r s):v.comp t c (pleas a f g) r s:=
    Lot.Mane.yes (by change a.f _ ((token (postcard _ _)).1)=_; rw [token,postcard,dec_round]; exact hp) he
lemma parks {t c:ℕ} {f g:Cog}{r s:Site}{v:Port}
    (hp:a.f v.l.x v.info=false)(he:v.comp t c g r s):v.comp t c (pleas a f g) r s:=
    Lot.Mane.no (by change a.f _ ((token (postcard _ _)).1)=_; rw [token,postcard,dec_round]; exact hp) he
lemma pinTrue {i T c:ℕ}{v:ℝ}{f g} (hp:a.f P.l.x P.info=true)(ht:P.band c T i f v):
    P.band c T i (pleas a f g) v:=by
    obtain ⟨w,h⟩:=ht
    exact ⟨w,fun x hx=> ⟨(h _ hx).1,⟨fun t ht=>park a hp ((h _ hx).2.digits t ht)⟩⟩⟩
lemma pinFalse {i T c:ℕ}{v:ℝ}{f g} (hp:a.f P.l.x P.info=false)(ht:P.band c T i g v):
    P.band c T i (pleas a f g) v:=by
    obtain ⟨w,h⟩:=ht
    exact ⟨w,fun x hx=> ⟨(h _ hx).1,⟨fun t ht=>parks a hp ((h _ hx).2.digits t ht)⟩⟩⟩

/-- Constant scalar polymer. fourth powers of rising -/
abbrev ein:= kohn 1
abbrev deuce:=kohn 2
abbrev divN (f:Lyric)(n:ℕ) : Lyric := times f (bi .flip (kohn n) zeroE)
def sQ (f:Lyric) : Lyric:= Reed.Lu.inf ein (Reed.Lu.sup zeroE f)
def quat (f:Lyric):Lyric:= let q:=times f f; times q q
def takeF(f:Lyric):Lyric:= quat (sQ (times deuce f))
def faded (f:Lyric):Lyric:= divN (psum (takeF f) (diff ein (takeF (diff ein f)))) 2

def boostR (f:Lyric): Lyric:= faded (diff (times (kohn 4) f) ein)
def gammaR (f:Lyric): Lyric:= diff ein (faded (divN (diff (times (kohn 10) f) (kohn 5)) 3))

namespace Paint
variable {k s T c f} {x:ℝ} (h:Standard s k T) (he:Chor k c T s f x)
include h he
lemma divideF (i:ℕ)(hi:1 ≤ i): Chor k c T s (divN f i) (x/(i:ℝ)):=by
    have hz := (h.rove c i).minuet h.sil h.st Doop.flip
    apply Eq.mp _ (h.mult0 he hz)
    rw [show Doop.val .flip _ 0 = (i:ℝ)⁻¹ from ?_,div_eq_mul_inv]
    change (max (i:ℝ) 1)⁻¹=(i:ℝ)⁻¹; rw [max_eq_left]; exact_mod_cast hi
lemma between0 : Chor k c T s (sQ f) (smooth x):=by
    exact h.lo0 (by simpa only [Nat.cast_one]  using h.rove c 1) (h.up0 h.sil he)
lemma quadrat:Chor k c T s (quat f) (x^4):=by
    convert h.mult0 (h.mult0 he he) (h.mult0 he he) using 1 <;> first | rfl | ring
lemma tapS : Chor k c T s (takeF f) (smooth (2*x)^4):=by
    apply quadrat h; apply between0 h
    exact h.mult0 (h.rove c 2) he
lemma went : Chor k c T s (faded f) (fade x):=by
    have hs:Chor k c T s ein 1:= by simpa only [Nat.cast_one]  using h.rove c 1
    apply divideF h _ 2 (by omega)
    exact h.additions (tapS h he) (h.dubs hs (tapS h (h.dubs hs he)))
lemma boosted : Chor k c T s (boostR f) (boost x):=by
    have hs := went h (h.dubs (h.mult0 (h.rove c 4) he) (h.rove c 1))
    convert hs using 1 <;> first | rfl | unfold boost rising; ring_nf
lemma gammed : Chor k c T s (gammaR f) (gamma x):=by
    have hs:=h.dubs (h.rove c 1) (went h (divideF h (h.dubs (h.mult0 (h.rove c 10) he)
                                  (h.rove c 5)) 3 (by omega)))
    convert hs using 1 <;> first | rfl | unfold gamma rising; ring_nf
end Paint
end Song

end
end ExactDerandomization.Arena

end

end OAI
