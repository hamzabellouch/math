import OAI.Computability.Logspace.EstimatorMachine
import OAI.Computability.Logspace.TransitionEvaluation

namespace OAI

/-!
Evaluation of terminal estimator requests and their approximation guarantees.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Gyre
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}

namespace Term
variable (r:Rock q w h)
abbrev selfC:Sight:=⟨_,VK.left⟩
abbrev header:Cub ℕ Crt:=⟨_,(Kn.unpack (α:=Crt)).comp VK.left⟩
abbrev spirit:Cub ℕ Scout:=⟨_,header.runs.right.right.left⟩
def ahead(i:ℕ):Sight:= ⟨_,Tiber.Sky.pK i⟩
def stomp (x:Word)(p:ℕ):Bool:=
    let q:= spirit.f x p
    decide (Foil.delta0 q)
def ebit : Cub ℕ Bool:=
    let p:= spirit.runs.right.left
    ⟨_, GK.decideK (GK.orG (GK.eqG p (Kn.fix 2)) (GK.eqG p (Kn.fix 3)))⟩
def avail (r:Rock q w h):Cub ℕ Bool :=
    let p:= header.runs
    ⟨_, GK.decideK (Foil.onRK r.w p.right.right.left p.right.left.left)⟩
def fire (r:Rock q w h) :Cub ℕ Bool:=⟨_,leftQ.runs.lt (Kn.fix r.w.p.K)⟩
abbrev te(k:ℕ):Kiwi :=
    Flash.clan (⟨_, Kn.wash.comp ((ahead 12).runs.tuple leftQ.runs)⟩) k

def rally (p:Scheme) :ℕ → Cog
   | 0=> Cargo.knock
   | k_tube+1=>.seq (Pier.walk p (te (k_tube+1)) true true)
              (.bif Cargo.flag0 (rally p k_tube)
                              (.seq (Pier.walk p (te (k_tube+1)) false false) (Flash.plumb (k_tube+1))))

def ent (r:Rock q w h)(v:Tags) :Cog :=
   let p:=Song.pleas ebit
                 (Song.pleas (fire r) (rally (schedule r v) (clim r.w.p)) Cargo.knock)
                 (Flash.chose (tag 9 0 true) 1)
   Song.pleas (avail r) p Cargo.knock

end Term
namespace OrbitR
open Term
structure Prism(u:Line (q:=q) (w:=w) (h:=h))where
     s:Fabric u
     p:MintV
namespace Prism
variable (e:Prism u)
abbrev v :=e.s
abbrev origin := e.v.leaveE
abbrev src :=e.origin.dataN
abbrev target(x):=Studio.dockA u e.src x
abbrev screen (x j):=Studio.stk u e.src x j
abbrev fare(r:Rock q w h)(v:Tags) :=Cambria.Era.tariff r+v.e+50
structure Ready (e:Prism u) :Prop where
     season : Stone.Rector e.v e.p
     spend : fare u.r u.v ≤ u.v.slope

namespace Ready
variable {e:Prism u}(he:e.Ready)
include he
lemma motto : u.D.Suite e.src := he.season.endUnits _ (Or.inl rfl)
omit he in
lemma crown :u.D.D e.src=1:= e.v.ageEnd _ (by decide)
lemma includes0 : e.origin.Front u:=he.season.frontE
omit he in
lemma price0: Cambria.Era.tariff u.r ≤ fare u.r u.v:=by unfold fare;omega
omit he in
lemma price2:4 ≤ fare u.r u.v∧ clim u.w0.p+2 ≤ fare u.r u.v ∧ u.v.e+20 ≤ fare u.r u.v:=by
    unfold fare Cambria.Era.tariff Cambria.Era.budget bootC
    change _∧clim u.r.w.p+2 ≤_∧_; omega
omit he in
lemma playsC (x j):(Term.spirit.f u.x (e.screen x j).info)=bitR e.s.t:=by
    change Age.styx (Term.header.f _ _)=_
    change ((dec (dec _ :Stool).1:Crt).2.2.1)=_
    change ((dec (dec (enc ((_,_,_):Stool)):Stool).1:Crt).2.2.1)=_
    rw [dec_round];change (Age.styx (dec (enc _)))=_
    rw [dec_round]
omit he in
lemma toneC (x j) :
    Term.ebit.f u.x (e.screen x j).info=e.v.govern∧
    (Term.avail u.r).f u.x (e.screen x j).info=decide e.v.activeR∧
    (Term.fire u.r).f u.x (e.screen x j).info=decide (j<e.origin.m):=by
    let s:=e.screen x j
    have hp: Term.spirit.f u.x s.info=bitR e.s.t:=Ready.playsC (e := e) x j
    refine ⟨?_,?_,?_⟩
    · change decide ((Term.spirit.f u.x s.info).2.1=2∨ (Term.spirit.f u.x s.info).2.1=3)=_
      have hQ:=congrArg (fun a:Scout=> decide (a.2.1=2∨ a.2.1=3)) hp
      apply hQ.trans
      change _= e.s.t.tag.narrow
      unfold bitR
      cases e.s.t.tag
      · rfl
      · rfl
      · next b h=> cases b <;> rfl
      · rfl
    · have hh: Age.MV (Term.header.f u.x s.info)=e.s.m:=by
           change Age.MV (dec (dec (enc ((_,_,_):Stool)):Stool).1)=_
           rw [dec_round];change Age.MV (dec (enc _))=_
           rw [dec_round]
      change decide (operateR u.r.w (Age.MV _) (Term.spirit.f u.x s.info))=_
      rw [hh,hp]
      simp only [decide_eq_decide]
      exact e.v.workR.symm
    change decide (leftQ.f _ _ < _)=_
    rw [show leftQ.f u.x s.info=j by simp [s,leftQ,film,info,panelx]]
omit he in
lemma gem (b a:ℕ)(x j): (Tiber.Sky.seek a b ⟨_,Tiber.Sky.whoK true⟩).f
                                        u.x (e.screen x j).info=hole (e.v.c a 0) (hole b j):=by
    have h: Reed.V u.x (e.screen x j).info=(e.src,j,0):=dec_round ..
    change hole (pointer (Reed.V u.x _).1 _) (hole _ _)=_
    unfold Tiber.Sky.whichSide;rw [h]
    have hs:pointer e.src a=e.v.c a 0:=Stone.pointing ..
    rw [hs]; change hole _ (hole _ (Reed.V u.x (e.screen x j).info).2.1)=_
    rw [h]
omit he in
lemma spinC (i x j): (Term.te i).f u.x (e.screen x j).info=
                       (e.v.slotWord j,i):=by
    have h: Reed.V u.x (e.screen x j).info=(e.src,j,0):=dec_round ..
    have hs:pointer e.src 12=e.v.c 12 0:=Stone.pointing ..
    change (hole (pointer (Reed.V u.x _).1 12) (leftQ.f u.x _),i)=_
    have hb:leftQ.f u.x (e.screen x j).info=j:=by change (Reed.V u.x (e.screen x j).info).2.1=j;rw [h]
    rw [h,hb,hs];rfl
end Ready

def lifted (e:Prism u)(f:Producer) (tb:ℕ→ℕ→ℕ) :Producer :=
   { tag:= fun x i=> if e.v.govern then tb x i else if f.awake x i then 1 else 0
     locate:= f.locate }
structure Enabled (e:Prism u)(f:Bool→Producer)(tb:ℕ→ℕ→ℕ) :Prop where
   ready:e.Ready
   onR : e.v.activeR
   report : e.v.Tgood e.p f
   allocate : e.v.govern = true → e.v.Profession (f false) tb

end Prism
end OrbitR
end
end ExactDerandomization.Gyre

end

section

namespace ExactDerandomization.Gyre.OrbitR.Prism
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky Term Producer
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Prism u}{f:Bool→Producer}{tb:ℕ→ℕ→ℕ}
abbrev rankF (u:Line (q:=q) (w:=w) (h:=h)):= fare u.r u.v
lemma chooses {a:Cub ℕ Bool}{v:Seats}{p f:Cog}{c:ℕ}{i:ℕ}(h:a.f v.l.x v.info=true)
    (he:v.rite c p i):v.rite c (pleas a p f) i :=
    fun _ hx=>Song.park a h (he _ hx)
lemma doesno {a:Cub ℕ Bool}{v:Seats}{p f:Cog}{c:ℕ}{i:ℕ}(h:a.f v.l.x v.info=false)
    (he:v.rite c f i):v.rite c (pleas a p f) i :=
    fun _ hx=>Song.parks a h (he _ hx)
namespace Enabled
variable (he:Enabled e f tb)
include he
abbrev core12(e:Prism u):=e.v.c 12 0
abbrev frame(e:Prism u):=e.v.terminal false
lemma capR (h:e.v.govern=true){i:ℕ}(hi:i<e.v.Rslots){t x:ℕ}(ht:0<t)(hs:t ≤ clim u.w0.p)
    (hx:x∈u.D.P):
    Pier.Liaison u.D x e.src (e.v.slotWord i) t ∧
    u.D.curve (e.v.slotWord i) t true x = if tb x i=t then some ((f false).locate x i) else none:=by
    obtain ⟨hd,hp,hv⟩:= (he.allocate h).guide x hx i hi t ht hs
    refine ⟨⟨?_,hx,hd,hp⟩,hv⟩
    rw [show cell (e.v.slotWord i)=e.v.c 12 0 by simp [Fabric.slotWord,hole,cell],(Ready.crown (e := e))]
    exact Fabric.parentL e.v (by decide) (by decide) (by decide)

lemma roves (h:e.s.govern=true){i:ℕ}(hi:i< e.v.Rslots)
    {x:ℕ}(hx:x∈u.D.P)(a:ℕ) (ha:a ≤ clim u.w0.p):
   let c:=rankF u
   (e.screen x i).rite c (rally u.D.s a) (if tb x i ≤ a then tb x i else 0):=by
    intro c
    let S:=e.screen x i
    let b:=tb x i
    let p:= e.v.slotWord i
    have hp:= he.ready
    have hs:=hp.motto
    have hm:4 ≤ c∧ clim u.w0.p+2 ≤ c:=⟨(Ready.price2 (u := u)).1,(Ready.price2 (u := u)).2.1⟩
    have hW:2≤c:=by omega
    induction a with
    | zero=>
      have ht:(if tb x i ≤ 0 then tb x i else 0)=0:=by split<;>omega
      rw [ht]; exact Fret.Seats.blankD (hs.pit hx S.info) hW
    | succ a ih=>
      let d:=a+1
      have hj:=he.capR h hi (show 0<d by unfold d;omega) ha hx
      have hz := (Ready.spinC (e := e)) d x i
      rintro _ ⟨f',hf,rfl⟩
      have hQ := Pier.shares hs hW hj.1 true f' hf hz
      have hc':u.D.s=u.D.s:=rfl
      by_cases hc:b=d
      · rw [ite_eq_left (show tb x i ≤ a+1 from hc.le)]
        rw [hj.2,ite_eq_left hc] at hQ
        let y:= (f false).locate x i; let r:=u.D
        have hF:r.curve p d true x=some y:=hj.2.trans (ite_eq_left hc)
        have hv := (hj.1.ready.swaps d hj.1.holds x hx true y hF)
        have hR:= Pier.stroll hs hW (Pier.street hj.1 hF) (Pier.seal1 r (q:=S.info) hs hW)
                                       (j:=0) false f' hf hz hv.2
        apply Lot.Mane.seq hQ

        refine Lot.Mane.no ?_ (Lot.Mane.seq hR ?_)
        · exact (show decide (1= (0:ℕ))=false from rfl)
        have hL:= hs.pit hx S.info (glove f' x) ⟨f',hf,rfl⟩
        have hl : Punct S.head c (tb x i):=by
             unfold Punct;change lb b+1 ≤ c*u.D.D e.src
             have h1:=lb_le_inc d; have h2:d≤ clim u.w0.p:=ha
             rw [(Ready.crown (e := e)),hc]; omega
        exact etches _ _ (i:=1) hc.symm hR.spots.2 (plight hl hL (by omega))
      rw [hj.2,ite_eq_right hc] at hQ
      have hq:(if tb x i  ≤ d then tb x i else 0)=if tb x i ≤ a then tb x i else 0:=by
                   unfold b d at *; split <;> split <;> omega
      rw [hq]
      exact Lot.Mane.seq hQ (Lot.Mane.yes (show decide (0 =(0:ℕ))=true from rfl)
                                    (ih (by omega) (glove f' x) ⟨_,hf,rfl⟩))

lemma mounted (x:ℕ) (hx:x∈u.D.P)(i:ℕ)(ht:u.smallQ e.src i) :
    let g:= e.lifted (f false) tb
    let c:=rankF u
    (e.screen x i).rite c (Term.ent u.r u.v) (g.tag x i):=by
   intro g c; let s:=e.screen x i
   let t:= clim u.w0.p
   have h0:= he.ready; have hC:= (he.report.secure false)
   have h2:e.v.activeR:=he.onR
   have hp:=h0.motto
   have h3:4 ≤ c ∧t+2 ≤ c∧u.eye.e+20 ≤ c:=(Ready.price2 (u := u))
   have hk:=(Ready.toneC (e := e)) x i
   apply chooses (hk.2.1.trans (decide_eq_true h2))
   by_cases hz:e.v.govern=true
   · have hm:g.tag x i=tb x i:=ite_eq_left hz
     rw [hm]
     apply chooses (hk.1.trans hz)
     by_cases hu:i< e.v.Rslots
     · apply chooses (hk.2.2.trans (decide_eq_true hu))
       have he0:tb x i ≤ t:=by
          by_cases hb:tb x i=0; rw [hb];omega
          exact ((he.allocate hz).bound x i hb).2
       have he1:= he.roves hz hu hx t le_rfl
       change s.rite c _ (if tb x i ≤ t then _ else 0) at he1
       rwa [ite_eq_left he0] at he1
     apply doesno (hk.2.2.trans (decide_eq_false hu))
     have hh:tb x i=0:=by by_contra hp; apply hu (hC.suit.lacks hx ((he.allocate hz).bound x i hp).1)
     rw [hh]; exact Fret.Seats.blankD (hp.pit hx s.info) (by omega)
   apply doesno (hk.1.trans (by cases h:e.v.govern; rfl; contradiction))
   let w:= e.v.terminal false
   have hg:g.tag x i=Flash.win ((f false).tag x i) 1:=by
        unfold g lifted
        dsimp only; rw [ite_eq_right hz]; unfold Flash.win Producer.awake; split <;> simp_all
   rw [hg]; apply Flash.picks u.D hp hx (by omega) _ _ _ (Pier.seal1 _ hp (by omega) (q:=s.info))
   have hv := hC.suit
   have hd:u.D.D w.dataN=1:=e.v.ageEnd _ (by decide)
   have heD:u.D.D w.visN=1:=by rw [← hv.coil.grain]; exact hd
   have hm:u.smallQ w.dataN i:=by
        change lb i ≤ u.eye.e*u.D.D w.dataN;rw [hd,←(Ready.crown (e := e))]; exact ht
   let z:=(f false).tag x i
   have hP : Punct s.head c z:=by
         have hf:= (hv.trace _ hx).fits i hm
         change lb z ≤ u.eye.e*u.D.D w.visN at hf;rw [heD] at hf
         unfold Punct;change lb z+1 ≤ c*u.D.D e.src; rw [(Ready.crown (e := e))];omega
   apply Bullet.copy u.D hp (by omega) hx _ ((Ready.gem (e := e)) 0 9 x i)
                                    hP ((hv.trace _ hx).next i hm)
   rw [(Ready.crown (e := e))];exact e.v.parentL (by decide) (by decide) (by decide)

lemma ancestor {y x:ℕ}(h:e.v.govern=true)(he1 : e.v.finalE x y≠0):
    ∃ i,(f false).awake x i∧ (f false).locate x i=y ∧tb x i≠0:=by
    have hu:= he.report.secure false
    have hv : e.v.aimE false x y ≠0 := by
         intro hk
         apply he1
         unfold Fabric.finalE forecast current; dsimp only
         rw [ite_eq_left (show Net.onQ u.plotM.gap e.v.m (e.v.t.key u.plotM)=true from he.onR)]
         change e.v.grid.pre e.v.grains (e.v.trio false) e.v.t.two x y*_*_=_
         rw [show e.v.grid.pre e.v.grains (e.v.trio false) e.v.t.two x y=0 from ?_];ring
         change e.v.grid.pre e.v.grains (e.v.trio false) false x y=0 at hk
         unfold At.Grid.pre at hk ⊢
         split at hk <;> split <;> grind
    obtain ⟨i,hi,hq⟩:=hu.light.defend x y hv
    refine ⟨i,hi,hq,?_⟩
    apply ((he.allocate h).quota _ _ hi).2
    rw [hq]
    by_contra! h0
    let d:=e.v.grid
    have hk : 1  ≤ d.rankin e.v.grains y:=by
         apply (Analysis.rank_ge (show (0:ℝ)<1 by norm_num)).mpr
         apply lt_of_lt_of_le h0 (card_le_card _)
         intro x hx; obtain ⟨hx,i,hi,hj⟩:=mem_filter.1 hx
         refine mem_filter.2 ⟨(hu.light.insured _ _ hi).1, Eq.ge ?_⟩
         exact hj ▸ he.report.seat x i hi
    apply he1
    unfold Fabric.finalE forecast current; dsimp only; rw [ite_eq_left (show Net.onQ u.plotM.gap e.v.m (e.v.t.key u.plotM)=true from he.onR)]
    have hz :d.incG e.v.grains y=0:=by unfold At.Grid.incG;rw [ite_eq_left (show d.sp=true from h), shutoff_zero (by linarith)]
    change _ * d.incG e.v.grains y * _=0
    rw [hz];ring
end Enabled
end
end ExactDerandomization.Gyre.OrbitR.Prism

end

section

namespace ExactDerandomization.Gyre.Term
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky
noncomputable section
open scoped Classical
variable {q w h:ℕ}

abbrev need :Cub ℕ Bool:=
   let h:=spirit.runs
   ⟨_, (h.right.left.eq (Kn.fix 4)).cond (Kn.fix false) h.right.right.right⟩
def noteQ: Cub ℕ (ℕ×ℕ×NoteM):=
    let h:=header.runs.right.right
    let k:= h.left.left.right.right.right
    let g:=Kn.wash.comp ((Kn.fix ((4,false):ℕ×Bool)).tuple (((Kn.fix 0).tuple k).tuple ((Kn.fix ((0,0):ℕ×ℕ)).tuple h.right)))
    ⟨_, (ahead 10).runs.tuple (leftQ.runs.tuple ((Kn.fix ((1,0):Arch)).tuple g))⟩
abbrev sees:Cog:= Bullet.snap (Flash.garnish noteQ)

variable (r:Rock q w h)
def portals (x:Word)(a:ℕ):ℕ:=
   let q:= Term.spirit.f x a
   if q.2.2.2 then (if q.2.1=2 then q.2.2.1+1 else r.w.p.T) else 0
lemma portalsK: Kn (portals r):=
    let h:=spirit.runs.right
    h.right.right.cond (h.left.cond_eq (Kn.fix 2) h.right.left.succ (Kn.fix r.w.p.T)) (Kn.fix 0)
def candle(j:ℕ): Cub ℕ Bool:= ⟨_,(Kn.fix j).lt (portalsK r)⟩
def changeP (i j:ℕ): Scout:=bitV (detector i j)
lemma changeK {α}[Wire α]{p:PT α ℕ}(h:Kn p)(j): Kn (fun x a => changeP (p x a) j) :=
    (h.tuple (h.tuple (Kn.fix _))).tuple (Kn.fix ((6,j,false):ChoiceX))
def atlas (j:ℕ)(x:Word)(a:ℕ):ℕ:=by
    let v:= Term.header.f x a
    let z:Issue:=dec (Age.env v)
    exact hole (enc (kit 17 (MV v-1,0) (changeP (Age.styx v).1.1 j)
                                       (enc ((z.2.1,z.1,z.2.2):Issue)))) (hole 1 0)
lemma atlasK(j):Kn (atlas j) :=
    let h:= Term.header.runs; let p:= (Kn.unpack (α:=Issue)).comp h.right.right.right
    let w:=Kn.wash.comp (p.right.left.tuple (p.left.tuple p.right.right))
    let g:= (Kn.fix 17).tuple ((h.right.left.left.pred.tuple (Kn.fix 0)).tuple
                          ((changeK h.right.right.left.left.left j).tuple w))
    Kn.wash.comp ((Kn.wash.comp g).tuple (Kn.fix _))

variable (v:Tags)(p:MintV)
abbrev b0:=campk (knob r v)
abbrev bright(k j:ℕ): Lyric:=
    let f:= Pier.escort (schedule r v) (te k) (Bullet.snap ⟨_,atlasK j⟩)
    Lyric.use 0 (pleas (candle r j) f (snow (b0 r v) 0))
def tuneE(k:ℕ) : ℕ → Lyric
   | 0=>zeroE
   | i+1=> Lu.sup (tuneE k i) (bright r v k i)

abbrev originC := tag 9 1 true
def summit(k:ℕ): Cog :=
      Pier.escort (schedule r v) (te k)
        (Bullet.snap (seek 13 1 ⟨_,Kn.fix 0⟩))
def double(k:ℕ):Lyric:=
    let h:=Lu.diff Song.ein (Song.boostR (.use 0 (summit r v k)))
    times (Lu.times (.use p.coin originC) h) (Song.gammaR (tuneE r v k r.w.p.T))

def melody(k:ℕ):Cog:=
    let K:=b0 r v
    let g:=snow K p.coin
    let f:= Song.pleas Term.ebit (roost K (double r v p k) p.coin) originC
    if k=0 then g else
       Song.pleas need (Cargo.choose sees g f) f
def costamp:Cog:=
    let g:= clim r.w.p+1
    Arena.Iris.dial (Term.ent r v) (melody r v p) g
def endC(i:ℕ):Cog:= if i=0 then Term.ent r v else costamp r v p
abbrev fullD:= Studio.arrange (endC r v p) 1
namespace Budget0
open Cambria.Wear
abbrev H (r:Rock q w h)(v:Tags)(p:MintV)(k:ℕ): Lyric:= reset (double r v p k) p.coin
abbrev wallet (r:Rock q w h)(u:Tags):ℕ:= OrbitR.Prism.fare r u
def cost (r:Rock q w h)(u:Tags)(p:MintV):ℕ:=
    let c:=wallet r u
    let v:=H r noneT p 0
    c+v.cost c + v.tail
lemma mantis (r:Rock q w h)(p:MintV)(u v:Tags)(i j:ℕ):Paper.same (H r u p i) (H r v p j):=by
    let a:= tuneE r u i
    let b:= tuneE r v j
    have h0(x):Paper.same (a x) (b x):=by
       induction x with
       | zero=>exact oneself _
       | succ x ih=>exact same.plies ih (Paper.use ..) _
    have h:= h0 r.w.p.T
    have hg : Paper.same (Song.gammaR (a r.w.p.T)) (Song.gammaR (b r.w.p.T)):= by
           apply Paper.same.plies (oneself _)
           apply Paper.same.rosebud
           apply Paper.same.plies _ (Paper.oneself _) Doop.prod
           exact ((oneself _).plies h _).plies (oneself _) _
    apply Paper.same.stow
    exact (((oneself _).plies ((oneself _).plies (Paper.same.red (Paper.use ..)) _) _).plies hg _)
lemma fareE (r:Rock q w h)(v:Tags)(p:MintV)(k:ℕ):
    let h:= H r v p k; let c:=wallet r v
    c  ≤ Budget0.cost r v p∧ h.cost c ≤ Budget0.cost r v p∧h.tail  ≤ Budget0.cost r v p:=by
    intro h c
    have he:= mantis r p v noneT k 0
    change same h _ at he
    obtain ⟨h1,h2,h3⟩:=he
    rw [h2,h3]; unfold Budget0.cost; dsimp only; unfold c; omega

end Budget0
end
end ExactDerandomization.Gyre.Term

end

section

namespace ExactDerandomization.Gyre.OrbitR.Prism
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky Term Producer
open Helix.Torch
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Prism u}{f:Bool → Producer}{tb:ℕ→ℕ→ℕ}
abbrev LampT (e:Prism u):= e.s.t
abbrev Hx (e:Prism u):=u.D.high e.src
abbrev Tc (e:Prism u):= e.Hx + Budget0.cost u.r u.v e.p

abbrev across (e:Prism u):=crossP e.s.dye
abbrev heightR(e:Prism u) := if e.s.t.main then e.s.t.steps u.plotM else 0
abbrev vale (e:Prism u):=e.s.m-1
abbrev euro(e:Prism u)(j:ℕ):Peek:=detector e.s.t.i j
abbrev stationE(e:Prism u)(j:ℕ):ℕ:=u.vecL (e.euro j) e.vale 17 0 e.across
abbrev paintE (e:Prism u)(j y:ℕ):ℝ:= if j<e.heightR then (e.s.roll e.vale).outV (e.euro j) e.across y else 0
abbrev outV (r:Fabric u)(x:ℕ):ℝ:=rank r.S0 (fun i=>r.aimE true i x) (clim u.w0.p)
structure Court (e:Prism u)(f:Bool → Producer)(tb:ℕ→ℕ→ℕ):Prop where
    step0:e.Enabled f tb
    stake: Budget0.cost u.r u.v e.p ≤ u.v.slope
    may : u.wick0.Veil u.torch (e.s.c 10 0)
    rank0: e.s.govern=true → ∀ x∈u.D.P,
        let p:=e.v.c 13 0
        u.D.Voice p x (hole 1 0) (u.D.high p) 0 (outV e.v x)
    tower0:e.s.govern=true→∀ j<e.heightR,
       ∀ y∈u.D.P, u.D.Voice (e.stationE j) y (hole 1 0) (u.D.high (e.stationE j)) 0 (e.paintE j y)

namespace Court
variable (h0:Court e f tb)
include h0

omit h0 in
lemma skewed(x j): Term.header.f u.x (e.screen x j).info=kit 14 (e.v.m,0) (bitR e.v.t) (enc (Print.issued e.v.dye)):=by
    change (dec (Reed.V _ _).1:Crt)=_
    have hp: Reed.V u.x (e.screen x j).info=(e.src,j,0):=dec_round ..
    rw [hp]; exact Wire.eq _

lemma readyK : 4 ≤ rankF u∧powder 100 ≤ rankF u∧Bullet.roomS ≤ rankF u:= by
    have h:=h0.step0.ready
    have hp:= (Ready.price0 (u := u))
    exact ⟨(Ready.price2 (u := u)).1,le_trans (Cambria.Era.billed ..).2.2 hp,le_trans (Cambria.Era.billed ..).2.1 hp⟩
lemma stake0{x:ℕ}(hx:x∈u.D.P)(j): Lu.Standard (e.screen x j) (b0 u.r u.v) e.Tc:=by
   let W:= Budget0.cost u.r u.v e.p; let p:= e.target x
   have hs:=h0.step0.ready
   have ht:e.Tc ≤ u.D.H := by
        have hk:=Studio.stayedC hs.motto le_rfl h0.stake
        rw [(Ready.crown (e := e)),mul_one] at hk; exact hk
   exact ⟨Studio.positioned hs.motto hx j 0,spanFilm (Studio.vital (u:=u) _ ht) ..⟩
omit h0 in
lemma invoice(x j:ℕ)(a:ℕ)(hb:e.v.govern=true):
    Term.portals u.r u.x (e.screen x j).info=e.heightR ∧
      Term.atlas a u.x (e.screen x j).info=hole (e.stationE a) (hole 1 0) :=by
    let k:=e.screen x j
    have hp:=(Court.skewed (e := e)) x j
    have hh:= (Ready.playsC (e := e)) x j
    refine ⟨?_,?_⟩
    · unfold portals heightR; rw [hh]
      unfold Fabric.govern at hb
      unfold bitR Quest.steps
      cases he:e.s.t.tag <;> rw [he] at hb <;> first|contradiction|skip
      next b i=> cases b <;> rfl
    unfold Term.atlas; rw [hp]
    dsimp only [kit,Age.env,Age.styx,Age.MV]
    rw [dec_round]; rfl

omit h0 in
lemma seeks(x j):need.f u.x (e.screen x j).info=e.v.t.two:=by
    let s:= Term.spirit.f u.x (e.screen x j).info
    change (if decide (s.2.1=4) then false else s.2.2.2)=_
    have hq:s=bitR e.v.t:=Ready.playsC (e := e) x j
    rw [hq]
    unfold bitR Quest.two
    cases h:e.v.t.tag
    · simp [shaped,Kind.paired]
    · simp [shaped,Kind.paired]
    · next b u=> cases b <;> simp [shaped,Kind.paired]
    simp [shaped,Kind.paired]

lemma realm {a}(h:u.D.W a+1 ≤ u.D.W e.src):e.Tc ≤ u.D.high a:=by
    have hs:=h0.step0.ready
    have ht:= Studio.soonerC hs.motto ((Ready.crown (e := e)).symm ▸ h) h0.stake le_rfl
    rw [(Ready.crown (e := e)),mul_one] at ht; exact ht

abbrev lampC(e:Prism u)(y:ℕ):Bool:=Print.shoot u.n e.s.t.t y (Print.badge e.s.dye.2.1)
lemma seesR {x j y:ℕ}(hx:x∈u.D.P)(hi:(f false).awake x j)(hq:(f false).locate x j=y):
    let v:=e.screen x j
    v.rite (rankF u) sees (enc (lampC e y)):=by
   subst y
   let y:=(f false).locate x j
   let s:=e.screen x j; let h:=(h0.step0.report.secure false)
   let v:=e.v.terminal false
   let p0:= enc (Print.issued e.s.dye); let p:=trail e.s.t.t p0
   let hP:NoteM:=Helix.Torch.waxy p
   have hv : Term.noteQ.f u.x s.info=(v.visN,j,hP):=by
         change (pointer (Reed.V u.x _).1 10,(leftQ.f _ _),_)=_
         have hu:= (Court.skewed (e := e)) x j
         have he: Reed.V u.x s.info=(e.src,j,0):=dec_round ..
         rw [show pointer (Reed.V u.x s.info).1 10 = v.visN from ?_,show leftQ.f u.x s.info=j from
                    congrArg (fun x:Stool=>x.2.1) he]
         · let v0:Crt:=Term.header.f u.x s.info
           change (v.visN,j,( (1,0),enc (trail (Age.styx v0).1.2.2.2 (Age.env v0))))=_
           rw [show v0=_ from hu]; rfl
         rw [he]; exact Stone.pointing ..
   have hs:=h0.step0.ready
   have hr:u.wick0.Ok hP:=by
          have hk:= hs.season.good.2.2.2.2.2.1
          refine ⟨Helix.Torch.housed u.r u.v u.x (by decide:(4:ℕ) ≤16) (Nat.zero_le _) ?_ (Nat.zero_le _) (Nat.zero_le _) (Print.boxbound _).le,
                                 NeZero.pos u.n,Nat.zero_le _⟩
          change e.s.t.t≤ roof u.r u.x
          exact le_trans (Nat.le_add_right ..) hk
   have ht :u.D.W v.visN+u.D.D e.src ≤ u.D.W e.src:=by
        rw [(Ready.crown (e := e))];exact Fabric.parentL e.v (by decide) (by decide) (by decide)
   have hk:u.eye.Flora u.torch.p v.visN j x (some ((f false).tag x j,y)):=by
         have hf:=h.suit.orbit (h.suit.lacks hx hi) hx
         unfold Producer.coversF at hf; rw [ite_eq_left hi] at hf; exact hf
   refine Arena.Flash.maskB hs.motto hx (by have:= h0.readyK;omega) ht h0.may hv hr hk _ ?_
   intro z hp
   have hh:y ≤ u.n:=Nat.le_of_lt_succ (mem_range.1 (Fabric.Good.n1 hs.season.chart hs.season.good
                                                            (h.light.insured _ _ hi).2))
   change u.torch.lit u.D.x hP y z = (lampC e y,z)
   rw [show u.torch.lit u.D.x hP y z=_ from Helix.Torch.litwax u.r u.v u.x _ p z y hh]
   unfold Helix.Torch.ray
   dsimp only [p,Helix.Torch.trail]
   simp only [ite_eq_right (by decide: ¬ (4:ℕ)<4), ite_true,p0,dec_round]; rfl

end Court
end
end ExactDerandomization.Gyre.OrbitR.Prism

end

section

namespace ExactDerandomization.Gyre.OrbitR.Prism.Court
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky Term Producer
open Helix.Torch
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Prism u}{f:Bool → Producer}{tb:ℕ→ℕ→ℕ}
variable (hp:Court e f tb)
include hp

abbrev okY(e:Prism u)(y:ℕ):Bool:= if e.v.t.two then lampC e y else true
lemma awakeY {x j:ℕ}(h:(f false).awake x j):
   let y:=(f false).locate x j
   e.v.grid.pre e.v.grains (e.v.trio false) e.v.t.two x y=
         if okY e y then (f false).scoreF (e.v.aimE false) x j else 0 :=by
   intro y; let s:=e.v
   have hv:=hp.step0; have ht:= (hv.report.secure false).light.insured _ _ h
   unfold scoreF; rw [ite_eq_left h]
   have hj : y ∈ (s.world.S).filter (fun _=>True):= mem_filter.2 ⟨(mem_filter.1 ht.2).1,trivial⟩
   have he: e.v.aimE false x y= (s.grains x).val s.S1 s.Rslots (s.trio false) y:=ite_eq_left
                       ⟨ht.1,ht.2,Or.inl (rfl : (false:Bool)=false)⟩
   have hh : lampC e y=true ↔ y∈s.S2:=by
       unfold lampC
       rw [Print.shoots]
       unfold Fabric.S2 Spray.dst1
       simp only [dst,retain,mem_filter]; apply (iff_and_self.mpr ?_)
       exact fun _=>(mem_filter.1 ht.2).1
   unfold okY; cases hC:e.v.t.two
   · simp only [Bool.false_eq_true,ite_false,ite_true];rfl
   simp only [ite_true]; rw [show (f false).locate x j=y from rfl,he]
   by_cases hY:y∈s.S2
   · rw [ite_eq_left (hh.2 hY)]; exact ite_eq_left ⟨ht.1,ht.2,Or.inr hY⟩
   rw [ite_eq_right (mt hh.mp hY)]
   exact ite_eq_right fun h=>hY (h.2.2.resolve_left (by decide))

lemma tinted {x i y:ℕ}(he:(e.lifted (f false) tb).awake x i)(hq:(f false).locate x i=y):
   let q:=e.v
   (e.lifted (f false) tb).scoreF q.finalE x i=
          ((if okY e y then (f false).scoreF (q.aimE false) x i else 0)*
                  q.grid.incG q.grains y)*q.t.tower u.plotM q.roll q.m e.across y :=by
    intro v; unfold scoreF; rw [ite_eq_left he]
    have ht:v.activeR:=hp.step0.onR
    have hm:(f false).awake x i:=by
       change (if v.govern then _ else _) ≠ 0 at he
       split at he
       · next hc=> exact ((hp.step0.allocate hc).bound x i he).1
       split at he
       · assumption
       contradiction
    change v.finalE x ((f false).locate x i)=_
    unfold Fabric.finalE forecast current; dsimp only; rw [ite_eq_left (show Net.onQ u.plotM.gap v.m (v.t.key u.plotM)=true from ht)]
    change e.v.grid.pre e.v.grains (e.v.trio false) e.v.t.two x _ * v.grid.incG _ _ * _ = _
    subst y; rw [hp.awakeY hm];rfl

abbrev bill(e:Prism u):= Budget0.cost u.r u.v e.p
omit hp in
lemma sharp(k:ℕ) : rankF u ≤ bill e ∧
   (Budget0.H u.r u.v e.p k).cost (rankF u) ≤ bill e ∧
   (Budget0.H u.r u.v e.p k).tail ≤ bill e:=Budget0.fareE ..

lemma frail{x i:ℕ}(h:x∈u.D.P)(hi:(f false).awake x i):
   let s:= e.screen x i
   s.band (rankF u) e.Tc e.p.coin originC ((f false).scoreF (e.v.aimE false) x i):=by
    intro s
    let k:=Enabled.frame e
    have he:= hp.step0; have h0:=he.ready
    have hs := (he.report.secure false).suit
    have hs' :=hs.coil
    have hf:u.D.W k.dataN+1 ≤ u.D.W e.src:=e.v.parentL (by decide) (by decide) (by decide)
    have hj:=(hs.voices x h).ready i (hs'.awake (hs'.size0 i (hs.lacks h hi)))
    have hn:u.D.D k.dataN=u.D.D e.src:=(e.v.ageEnd _ (by decide:¬Brole 9)).trans (Ready.crown (e := e)).symm
    rw [show (e.v.terminal false).dataN=k.dataN from rfl,hn] at hj
    apply Bullet.clef u.D h0.motto hp.readyK.2.2 h (by rw [(Ready.crown (e := e))];exact hf)
                 ((Ready.gem (e := e)) 1 9 x i) (hp.realm hf) hj

lemma summitR {x i:ℕ}(hx:x∈u.D.P)(he:e.v.govern=true)(hz:tb x i≠0):
    let b:=f false; let y:=b.locate x i
    let j:=tb x i; let s:=e.screen x i
    s.band (rankF u) e.Tc 0 (summit u.r u.v j) (outV e.v y):=by
    intro b y j s
    have hv:= hp.step0; have hs:=hv.allocate he
    have hm:=hs.bound x i hz
    have hb:= hv.ready
    have ht:= hv.capR he ((hv.report.secure false).suit.lacks hx hm.1) (Nat.pos_of_ne_zero hz) hm.2 hx
    obtain ⟨hR,hq⟩:=ht
    have hP:= hR.ready
    have hg:u.D.curve (e.v.slotWord i) (tb x i) true x= some y:= hq.trans (ite_eq_left rfl)
    have hf: y∈u.D.P := (hP.swaps _ hR.holds x hx true y hg).1
    have hw:u.D.W (e.v.c 13 0)+1 ≤ u.D.W e.src := e.v.parentL (by decide) (by decide) (by decide)
    have hL: (seek 13 1 ⟨_,Kn.fix 0⟩).f s.l.x s.info=hole (e.v.c 13 0) (hole 1 0):=by
        have h1: Reed.V u.x s.info=(e.src,i,0):=dec_round ..
        change hole (pointer (Reed.V u.x s.info).1 13) (hole 1 0)=_
        rw [h1,show pointer e.src 13=e.v.c 13 0 from Stone.pointing ..]
    apply Pier.bowls hb.motto ((by omega: 2 ≤ 4).trans hp.readyK.1) hR hp.readyK.2.2 ((Ready.spinC (e := e)) j x i) hg
    apply Bullet.clef u.D hb.motto hp.readyK.2.2 hf (by rw [(Ready.crown (e := e))]; exact hw) hL (hp.realm hw)
    simpa only [Nat.zero_mul] using hp.rank0 he y hf

lemma prompter {x i:ℕ}(hx:x∈u.D.P)(he:e.v.govern=true)(hz:tb x i≠0)(k:ℕ):
    let b:=f false; let y:=b.locate x i
    let j:=tb x i; let s:=e.screen x i
    Chor (b0 u.r u.v) (rankF u) e.Tc s (bright u.r u.v j k) (paintE e k y):=by
   intro b y j s; have hr:= hp.step0
   have hm:2 ≤ rankF u:= (by omega: 2 ≤ 4).trans hp.readyK.1
   obtain ⟨hH,hA⟩:= Court.invoice (e := e) x i k he
   have ha:(Term.candle u.r k).f s.l.x s.info=decide (k<e.heightR):=
                congrArg (fun j=> decide (k<j)) hH
   apply Chor.byear
   by_cases hW:k<e.heightR
   · apply Song.pinTrue _ (ha.trans (decide_eq_true hW))
     have hh:=(hr.allocate he).bound x i hz
     let p:=hr.report.secure false
     obtain ⟨ht,hk⟩:=hr.capR he (p.suit.lacks hx hh.1) (Nat.pos_of_ne_zero hz) hh.2 hx
     have hg: u.D.curve (e.v.slotWord i) (tb x i) true x=some y:= hk.trans (ite_eq_left rfl)
     have hy: y∈u.D.P := (ht.ready.swaps _ ht.holds x hx true y hg).1
     apply Pier.bowls hr.ready.motto hm ht hp.readyK.2.2 ((Ready.spinC (e := e)) j x i) hg
     have hpv: u.D.W (e.stationE k)+1 ≤ u.D.W e.src:=by
       let K:=e.v; have he2:0<K.m:=by
               have hm:K.activeR:=hp.step0.onR; unfold Fabric.activeR Net.onQ at hm; by_contra hn; simp [Nat.eq_zero_of_not_pos hn] at hm
       change Age.W _+1 ≤ Age.W _
       unfold stationE vecL; rw [Line.rolfe]; change Age.weight e.vale 17 0+1 ≤ u.D.W (e.v.c 14 0)
       rw [Stone.W]; exact Age.renewal (a:=14) (i:=0) (n:=K.m) (m:=K.m-1) (by change K.m-1+1 ≤ K.m;omega)
     apply Bullet.clef u.D hr.ready.motto hp.readyK.2.2 hy (by rw [(Ready.crown (e := e))];exact hpv) hA (hp.realm hpv)
     simpa only [Nat.zero_mul] using hp.tower0 he k hW y hy
   apply Song.pinFalse _ (ha.trans (decide_eq_false hW))
   unfold paintE; rw [ite_eq_right hW]
   exact Amber.steam _ _ (hp.stake0 hx i) hp.readyK.2.1

end
end ExactDerandomization.Gyre.OrbitR.Prism.Court

end

section

namespace ExactDerandomization.Gyre.OrbitR.Prism.Court
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky Term Producer
open Helix.Torch
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Prism u}{f:Bool → Producer}{tb:ℕ→ℕ→ℕ}
variable (hp:Court e f tb)
include hp
def sumR (v:ℕ→ℝ):ℕ→ℝ
    | 0=>0
    | k_stack+1=>max (sumR v k_stack) (v k_stack)
omit hp in
lemma pg(x:ℕ){v:ℕ→ℝ}:0 ≤ sumR v x:=by induction x with
                                         | zero=>rfl
                                         | succ x ih=>exact le_trans ih (le_max_left ..)
lemma towerQ (he:e.s.govern=true) (x):
    e.v.t.tower u.plotM e.v.roll e.v.m e.across x=gamma (sumR (fun k=>paintE e k x) u.w0.p.T):=by
    have hG:=hp.step0
    let m:= e.heightR
    let H(n):= sumR (fun k=> e.paintE k x) n
    have hh(d):m  ≤ d→ H d=H m :=by
       induction d with
       | zero=> intro h; exact (show m=0 by omega) ▸ rfl
       | succ n ih=>
                      intro hn; by_cases hs:m=n+1; rw [hs]
                      have ht :m ≤ n:=by omega
                      unfold H; rw [sumR,paintE,ite_eq_right (show ¬ n < m by omega)]
                      change max (H n) 0=_
                      rw [ih ht,max_eq_left (show 0  ≤ H m from by exact pg _)]
    unfold Quest.tower
    let v:=e.s.t
    cases he0:v.main
    · simp only [Bool.false_and,Bool.false_eq_true,ite_false]
      have hz:m=0:=by unfold m heightR; rw [show e.s.t.main=false from he0];rfl
      change 1=gamma (H _)
      rw [hh u.w0.p.T (by omega),hz]; exact (gamma_full (x:=0) (by norm_num)).symm
    have hm:m=v.steps u.plotM:= ite_eq_left he0
    have hT:m ≤ u.w0.p.T:=by
        rw [hm]
        have hs:= hG.ready.season.good.2.2.2.2.2.2
        unfold Quest.steps
        cases h:v.tag <;> first| exact Nat.zero_le _|skip
        next b i=>rw [show _=v.tag from rfl,h] at hs; cases b<;> dsimp only <;> first|exact le_rfl| exact hs.2
    let s:= fun j=> (e.v.roll e.vale).outV (e.euro j)
    have hb(d): d ≤ m→ H d= Maxer s d e.across x:=by
         induction d with
         | zero=>exact fun _=>rfl
         | succ d ih=> intro h;exact congrArg₂ max (ih (by omega))
                                 (show paintE e d x=_ from ite_eq_left (by change d < m; omega))
    rw [ite_eq_left (show (true && e.v.t.tag.narrow) = true from by rw [show e.v.t.tag.narrow=true from he];rfl)]
    rw [show sumR (fun k=>e.paintE k x) u.w0.p.T=_ from hh u.w0.p.T hT,hb m le_rfl,hm]
    rfl

lemma warmV {j x i:ℕ}(hx:x∈u.D.P)(he:e.v.govern=true)(hz:tb x i≠0):
    let b:=f false; let y:=b.locate x i; let s:=e.screen x i
    Chor (b0 u.r u.v) (rankF u) e.Tc s (tuneE u.r u.v (tb x i) j) (sumR (fun k=>paintE e k y) j):=by
   intro b y s
   induction j with
   | zero=> exact (hp.stake0 hx i).sil
   | succ j ih=> exact (hp.stake0 hx i).up0 ih (hp.prompter hx he hz j)

abbrev showR (e:Prism u)(y:ℕ) :ℝ:= e.v.grid.incG e.v.grains y* e.v.t.tower u.plotM e.v.roll e.v.m e.across y

attribute [local irreducible] tuneE
set_option maxHeartbeats 900000 in
lemma earnsR {i x:ℕ}(hx:x∈u.D.P)(he:e.v.govern=true)(hz:tb x i≠0):
   let b:=f false; let y:=b.locate x i; let s:=e.screen x i
   let X:= b.scoreF (e.v.aimE false) x i
   s.band (bill e) (Hx e) e.p.coin (roost (b0 u.r u.v) (double u.r u.v e.p (tb x i)) e.p.coin) (X*showR e y):=by
   intro b y s X
   let k:=b0 u.r u.v
   have hp0:=hp.step0
   have ht:= hp.stake0 hx i
   have h1:= hp0.allocate he
   have hc:= hp.readyK.1
   have he0:=hp0.report.secure false
   let r:=outV e.v y
   have hv:e.v.grid.incG e.v.grains y=shutoff r:=ite_eq_left he
   let A:=sumR (fun k=> e.paintE k y) u.w0.p.T
   have ha:e.v.t.tower u.plotM e.v.roll e.v.m e.across y=gamma A:=hp.towerQ he y
   have hh0 :=hp.frail hx (h1.bound x i hz).1
   have hU :Chor k (rankF u) e.Tc s (double u.r u.v e.p (tb x i)) (X*showR e y):=by
       have hjp := Song.Paint.boosted ht (Chor.byear (hp.summitR hx he hz))
       have hw:= Song.Paint.gammed ht (hp.warmV (j:=u.w0.p.T) hx he hz)
       have hP: Chor k (rankF u) e.Tc s Song.ein 1 :=by simpa using ht.rove (rankF u) 1
       unfold showR; rw [hv,ha,←mul_assoc]
       exact ht.mult0 (ht.mult0 (Chor.byear hh0) (ht.dubs hP hjp)) hw
   have hu:= (Court.sharp (e := e)) (tb x i)
   let h:=Budget0.H u.r u.v e.p (tb x i)
   have he0:e.Hx+h.tail*s.d ≤ e.Tc:=by
       rw [show s.d=1 from (Ready.crown (e := e)),mul_one]; exact Nat.add_le_add_left hu.2.2 _
   have he1: |showR e y| ≤ 1:=by
       have hr:{x y:ℝ}→in01 x→in01 y→|x*y| ≤ 1:=by
            rintro x y ⟨h1,h2⟩ ⟨h3,h4⟩; rw [abs_le]; constructor <;> nlinarith only [h1,h2,h3,h4]
       unfold showR; rw [ha]
       exact hr (e.v.grid.incG_bounds e.v.grains y) (gamma_mem A)
   have hs:|X*showR e y| ≤ massB e.p.coin s.d:=by
       rw [abs_mul]; refine le_trans (mul_le_mul_of_nonneg_left he1 (abs_nonneg _)) ?_
       rw [mul_one]; exact Seats.maxv hh0
   exact Amber.onQ _ _ _ ht hU (show 1  ≤  rankF u by omega) he0 hu.2.1 hs

lemma plain {i x:ℕ}(hx:x∈u.D.P)(hi:(f false).awake x i)(he:e.s.govern=false):
   let y:=(f false).locate x i; let s:=e.screen x i;let X:=(f false).scoreF (e.v.aimE false) x i
   s.band (bill e) (Hx e) e.p.coin originC (X*showR e y):=by
   intro y s X
   have ha:e.v.grid.incG e.v.grains y=1:=ite_eq_right (by rw [show e.v.grid.sp=e.s.govern from rfl,he];decide)
   have hz:e.v.t.tower u.plotM e.v.roll e.v.m e.across y=1:=by
                         unfold Quest.tower; rw [show e.v.t.tag.narrow=false from he]; simp
   unfold showR; rw [ha,hz,mul_one,mul_one]
   apply flex (hp.frail hx hi) (by have :=hp.readyK;omega) ((Court.sharp (e := e)) 0).1; unfold Tc; omega
lemma salmon (x:ℕ)(hx:x∈u.D.P)(i:ℕ):
     (e.screen x i).band (bill e) (Hx e) e.p.coin (snow (b0 u.r u.v) e.p.coin) 0:=by
   apply flex (steam _ _ (hp.stake0 hx i) hp.readyK.2.1) (by have:=hp.readyK;omega)
              ((Court.sharp (e := e)) 0).1
   unfold Tc; omega

lemma choirR(x:ℕ)(hx:x∈u.D.P)(i:ℕ)(hk:u.smallQ e.src i):
    let g:=e.lifted (f false) tb
    (e.screen x i).band (bill e) (Hx e) e.p.coin
                                 (costamp u.r u.v e.p) (g.scoreF e.v.finalE x i):=by
    intro g; let s:=e.screen x i
    let r:=g.tag x i
    have he:=hp.step0; have hs:= he.ready
    have hm:= he.mounted x hx i hk
    have hw:= higher hm (by have hp:=hp.readyK;omega) ((Court.sharp (e := e)) r).1
    let X:=g.scoreF e.v.finalE x i
    let f0:=f false
    have hc : ebit.f s.l.x s.info=e.v.govern:= ((Ready.toneC (e := e)) x i).1
    have hr : r=(if e.v.govern then tb x i else if f0.awake x i then 1 else 0):=rfl
    have hR:r ≤ clim u.w0.p+1:=by
        rw [hr]; split
        · next ht=>
                   by_cases h:tb x i=0; rw [h]; omega
                   exact ((he.allocate ht).bound x i h).2.trans (by omega)
        split <;> omega
    apply Iris.parcel hR hw
    unfold Term.melody; dsimp only
    by_cases hz:r=0
    · rw [ite_eq_left hz]; unfold Producer.scoreF; rw [ite_eq_right (not_not_intro hz)]
      exact hp.salmon x hx i
    rw [ite_eq_right hz]
    let q:= f0.scoreF (e.v.aimE false) x i; let y:=f0.locate x i
    have hh:f0.awake x i:=by
         rw [hr] at hz; split at hz
         · next hc=> exact ((he.allocate hc).bound x i hz).1
         split at hz; assumption; contradiction
    let Q:=Song.pleas Term.ebit (roost (b0 u.r u.v) (double u.r u.v e.p r) e.p.coin) originC
    have hN: s.band (bill e) e.Hx e.p.coin Q (q*showR e y):=by
       cases hV:e.v.govern
       · exact Song.pinFalse ebit (hc.trans hV) (hp.plain hx hh hV)
       · have hW:r=tb x i:=hr.trans (ite_eq_left hV)
         apply Song.pinTrue _ (hc.trans hV)
         rw [hW]; exact hp.earnsR hx hV (hW ▸hz)
    let a:=lampC e y
    have hY: need.f s.l.x s.info=e.v.t.two:=Court.seeks (e := e) x i
    rw [show g.scoreF _ x i = _ from hp.tinted hz rfl]
    cases ht:e.v.t.two
    · apply Song.pinFalse need (hY.trans ht)
      have hb:okY e y=true:=ite_eq_right (by rw [ht];decide)
      rw [ite_eq_left hb,mul_assoc];exact hN
    apply Song.pinTrue need (hY.trans ht)
    have hO:okY e y=a:=ite_eq_left ht
    have hk:= hp.seesR hx hh rfl
    apply Seats.avis (higher hk (by have :=hp.readyK;omega) ((Court.sharp (e := e)) r).1)
    · intro hj; have hv:a=false:=by
            change enc a=0 at hj; cases ht:a; rfl; rw [ht] at hj; change 1=0 at hj; contradiction
      rw [ite_eq_right (by rw [hO,hv];decide),zero_mul,zero_mul];exact hp.salmon x hx i
    intro hj; have hv:a=true:=by
       change enc a≠0 at hj
       cases he:a
       · rw [he] at hj; exact False.elim (hj rfl)
       rfl
    rw [ite_eq_left (hO.trans hv),mul_assoc];exact hN
end
end ExactDerandomization.Gyre.OrbitR.Prism.Court

end

section

namespace ExactDerandomization.Gyre.OrbitR.Prism
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky Term Producer
open Helix.Torch
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Prism u}{f:Bool → Producer}{tb:ℕ→ℕ→ℕ}

structure Ace (e:Prism u):Prop where
   he:e.Ready
   hC : Court.bill e ≤ u.v.slope
   hd: Studio.Parcel u e.src (fullD u.r u.v e.p)

namespace Ace
variable (hA:e.Ace)
include hA
omit hA in
lemma price : rankF u ≤ Court.bill e∧4 ≤ rankF u∧powder 100 ≤ rankF u:=
    ⟨(Budget0.fareE u.r u.v e.p 0).1,(Ready.price2 (u := u)).1,
       le_trans (Cambria.Era.billed _).2.2 (Ready.price0 (u := u))⟩
lemma emits {x i}(hp:u.smallQ e.src i){h:ℕ}(hv:(e.screen x i).rite (rankF u) (ent u.r u.v) h):
   u.D.swears (post e.src 0 i 0) x h:=
    Studio.echoTicket hA.he.motto (by omega:(0:ℕ) ≤ 1) (by omega) hp (by have :=(Ace.price (e := e));omega)
        (le_trans (Ace.price (e := e)).1 hA.hC) hv hA.hd
lemma songT {x i}(hv:u.smallQ e.src i){X:ℝ}
   (hp:(e.screen x i).band (Court.bill e) e.Hx e.p.coin (Term.costamp u.r u.v e.p) X):
   u.D.Voice e.src x (hole 1 i) e.Hx (e.p.coin*u.D.D e.src) X:=
     Studio.scoreTicket hA.he.motto (show (1:ℕ) ≤ 1 from by omega) (by omega) hv (by have :=(Ace.price (e := e));omega)
                              hA.hC le_rfl hp hA.hd
lemma kingdom {i:ℕ}(h:i≤clim u.w0.p+1): u.smallQ e.origin.visN i:=by
    have ht:=lb_le_inc i; have hf:=hA.he.season.book.cost0
    change lb i ≤ u.eye.e*u.D.D _
    rw [show u.D.D e.origin.visN=1 from hA.he.includes0.grain ▸ (Ready.crown (e := e)),mul_one]
    apply ht.trans
    apply le_trans _ hf
    unfold Bank.hx Bank.hu Bank.hi bootC; change i≤clim u.r.w.p+1 at h;omega
lemma deadgate (x i:ℕ)(hx:x∈u.D.P)(hi:u.smallQ e.src i)(ht:u.D.swears (post e.src 0 i 0) x 0):
     u.eye.Flora u.torch.p e.origin.visN i x none:=by
    have hf:=hA.he.includes0
    refine Cone.ConeX.Flora.abs ⟨hf.point0 hA.he.season.chart i (hf.back0 hi),hx,?_⟩
    rw [show u.eye.ear u.torch.p _ _ = post e.src 0 i 0 from hf.ear0 i]
    exact u.D.identity ht
end Ace

namespace Court
variable (hp:Court e f tb)
include hp
abbrev tribe(e:Prism u)(f:Bool→Producer)(tb):=e.lifted (f false) tb

lemma matter : (tribe e f tb).Light e.v.finalE e.v.S0 e.v.S1:=by
    let g:=tribe e f tb; have hr:=hp.step0; let h:=f false
    have ht:= (hr.report.secure false).light
    have he(k j:ℕ)(hh:g.awake k j):h.awake k j:=by
           change (if _ then _ else _)≠0 at hh
           change (if e.v.govern then tb k j else _)≠0 at hh
           split at hh
           · next hi=> exact ((hr.allocate hi).bound k j hh).1
           split at hh; assumption;contradiction
    refine ⟨fun i j hh=> ht.insured _ _ (he _ _ hh),fun x i j hm hn hQ=> ht.fair _ _ _ (he _ _ hm) (he _ _ hn) hQ,?_⟩
    intro x y ho
    cases hG:e.v.govern
    · have hu: e.v.aimE false x y≠0 := by
          intro hn
          apply ho
          unfold finalE forecast current; dsimp only
          rw [ite_eq_left (show Net.onQ u.plotM.gap e.v.m (e.v.t.key u.plotM)=true from hr.onR)]
          change e.v.grid.pre e.v.grains (e.v.trio false) e.v.t.two x y * e.v.grid.incG e.v.grains y * _=0
          have he: e.v.grid.pre e.v.grains (e.v.trio false) e.v.t.two x y=0:=by
                change e.v.grid.pre e.v.grains (e.v.trio false) false x y=0 at hn
                unfold At.Grid.pre at *; grind
          rw [he];ring
      obtain ⟨i,hi,hx⟩:=ht.defend x y hu
      refine ⟨i,?_,hx⟩
      show (if e.v.govern then _ else if h.awake x i then 1 else 0)≠0
      rw [hG,ite_eq_left hi]; exact Nat.ne_of_gt Nat.one_pos
    obtain ⟨i,ha,hb,hC⟩:= hr.ancestor hG ho
    exact ⟨i,(show (if e.v.govern then _ else _)≠0 from (by rw [ite_eq_left hG];exact hC)),hb⟩
lemma roy {x i:ℕ}: let g:=tribe e f tb
   g.tag x i ≤ clim u.w0.p +1 ∧ (g.awake x i→(f false).awake x i):=by
    intro g; have hr:= hp.step0
    unfold Producer.awake g tribe lifted; dsimp only
    split
    · next he=>
      have hf:= (hr.allocate he).bound x i
      by_cases hh:tb x i=0; simp [hh]
      exact ⟨(hf hh).2.trans (Nat.le_add_right ..),fun _=>(hf hh).1⟩
    split <;> grind
set_option maxHeartbeats 700000 in
lemma plants(hA:e.Ace): e.v.Efine e.p (tribe e f tb):=by
   let g:=tribe e f tb
   have hp0:=hp.step0;have hs:=hp0.ready; have hc:= hs.season; let f0:= f false
   have ht:=hp0.report.secure false
   let N:= e.origin
   refine ⟨⟨hp.matter, hs.includes0,?_,?_⟩,?_,?_,?_⟩
   · intro x hx
     have he(i:ℕ)(hi:u.smallQ e.src i): u.D.swears (post e.src 0 i 0) x (g.tag x i):=
                         hA.emits hi (hp0.mounted x hx _ hi)
     refine ⟨fun i hh=> he _ hh,fun i _=>hA.kingdom hp.roy.1,fun i hA=>?_,fun i hB=>?_⟩
     · by_contra hk
       have hv:= ht.suit.lacks hx (hp.roy.2 (show g.awake x i from hk))
       exact not_lt_of_ge hA hv
     change u.eye.Flora u.torch.p e.origin.visN i x (if g.tag x i=0 then _ else _)
     by_cases hf:g.tag x i=0
     · have he0:= he i hB
       rw [hf] at he0; rw [ite_eq_left hf]; exact hA.deadgate x i hx hB he0
     rw [ite_eq_right hf]
     let p:=e.v.terminal false; let F:=p.visN; let y:=g.locate x i
     have hg:f0.awake x i:= hp.roy.2 (show g.awake x i from hf)
     have hl:= ht.suit.coil
     apply hs.season.chart.Rope hs.includes0 i x (g.tag x i) i F y (f0.tag x i) hB (hA.kingdom hp.roy.1) hf
                  hx _ _ _ _ (Fabric.Good.n1 hc.chart hc.good (ht.light.insured x i hg).2)
                  (he _ hB) ((ht.suit.trace x hx).caseM i hg (hl.awake (hl.size0 i (ht.suit.lacks hx hg))))
     · unfold Mold.offer; dsimp only
       rw [Stone.roleR,ite_eq_right (by decide:(15:ℕ)≠ 2),ite_eq_right (by decide:(15:ℕ)≠4),ite_eq_left rfl]
       exact congrArg (fun v=>rope v i) (Stone.pointing ..)
     · exact Stone.zeroR ..
     · rw [show u.D.D e.origin.visN=1 from e.v.ageEnd _ (by decide)]
       exact e.v.parentL (by decide) (by decide) (by decide)
     rw [show u.D.D e.origin.visN=1 from e.v.ageEnd _ (by decide),show u.D.D F=1 from e.v.ageEnd _ (by decide)];omega
   · intro x hx; exact ⟨fun i hi=>hA.songT hi (hp.choirR x hx i hi)⟩
   · cases hV:e.v.govern
     · exact Or.inr rfl
     exact Or.inl (hp0.allocate hV).t1
   · intro he x i hi
     have hu:g.tag x i=tb x i:=ite_eq_left he
     exact hu.symm ▸ ((hp0.allocate he).bound x i (fun h=>hi (hu.trans h))).2
   intro h i hi t he hr
   have hv:= hp0.allocate h
   have hc:=hv.guide
   have hm : 0∈u.D.P:=mem_range.2 (Nat.zero_lt_succ ..)
   refine ⟨(hc 0 hm i hi t he hr).1,(hc 0 hm i hi t he hr).2.1,fun x hx=>?_⟩
   have hw:= (hc x hx i hi t he hr).2.2
   rw [hw]
   change _=(if g.tag x i=t then _ else _)
   rw [show g.tag x i=tb x i from ite_eq_left h]; rfl
end Court

end
end ExactDerandomization.Gyre.OrbitR.Prism

end

section

namespace ExactDerandomization.Gyre.OrbitR.Prism
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX
open Line Line.Fabric Fret.Seats
open Cambria.Wear.Paper
open Glass Glass.Rod Tiber.Sky Term Producer
open Helix.Torch
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {e:Prism u}

namespace Ace
variable (hb:e.Ace)(hc:¬e.v.activeR)
include hb hc
def flat:Producer:=⟨fun _ _=>0,fun _ _=>0⟩
omit hb in
lemma past : e.v.finalE=fun _ _=>0:=by
    unfold finalE forecast current; dsimp only
    rw [ite_eq_right (show ¬ (Net.onQ u.plotM.gap e.v.m (e.v.t.key u.plotM))=true from hc)]
lemma mark0(x i:ℕ)(hx:x∈u.D.P): (e.screen x i).rite (rankF u) (ent u.r u.v) 0:=by
    let v:= e.screen x i
    have ht: (avail u.r).f v.l.x v.info=false:= ((Ready.toneC (e := e)) x i).2.1.trans (decide_eq_false hc)
    exact doesno ht (blankD (hb.he.motto.pit hx _) (by have :=(Ace.price (e := e));omega))
lemma seed0(x i:ℕ)(hx:x∈u.D.P)(_:u.smallQ e.src i):
   (e.screen x i).band (Court.bill e) e.Hx e.p.coin (Term.costamp u.r u.v e.p) 0:=by
   have hs:=hb.he.motto
   have ht:=(Ace.price (e := e))
   have hm := higher (hb.mark0 hc x i hx) (by omega) ht.1
   have hd:e.Hx≤u.D.H:=by unfold Hx high;omega
   have hp: Standard (e.screen x i) (b0 u.r u.v) e.Hx:=⟨Studio.positioned hs hx i 0,
                          spanFilm (Studio.vital (u:=u) _ hd) ..⟩
   apply Iris.parcel (Nat.zero_le _) hm
   unfold melody; dsimp only; rw [ite_eq_left rfl]
   exact steam _ _ hp (le_trans ht.2.2 ht.1)
omit hb hc in
lemma deltaP (e:Prism u)(hp:e.v.govern=true): Foil.delta0 (bitR e.v.t):=by
    unfold delta0 bitR
    unfold govern at hp
    cases h:e.v.t.tag <;> rw [h] at hp <;> first| contradiction| skip
    next b i=> cases b <;> simp [shaped]
lemma water (hd:u.s.scripted 12=Line.Fabric.capprog u.r u.v u.s.pave):e.v.Efine e.p flat:=by
    let f:=e.origin
    have hx:=hb.he;have he:=hx.season
    have hp(h:e.v.govern=true):= he.endUnits 12 (Or.inr (Or.inr (Or.inl ⟨rfl,Ace.deltaP e h⟩)))
    constructor
    · refine ⟨?_,hx.includes0,fun x hm=>?_,fun x hm=>?_⟩
      · exact ⟨fun _ _ h=> (h rfl).elim,fun _ _ _ h _ _=> (h rfl).elim,
                       fun x y h=>(h ((Ace.past (e := e)) hc ▸ rfl)).elim⟩
      · have he0(i)(hz:u.smallQ e.src i):= hb.emits hz (hb.mark0 hc x i hm)
        exact ⟨he0,fun i h=>hb.kingdom (show 0 ≤ _ from Nat.zero_le _),fun _ _=>rfl,fun i hi=>by
            have hs:=hb.deadgate x i hm hi (he0 i hi)
            exact hs⟩
      exact ⟨fun i hi=>by
         have hr :flat.scoreF e.v.finalE x i=0:=ite_eq_right (fun h=>h rfl)
         rw [hr]
         exact hb.songT hi (hb.seed0 hc x i hm hi)⟩
    · cases h:e.v.govern; exact Or.inr rfl
      exact Or.inl (hp h).stage
    · intro h x i hd; exact (hd rfl).elim
    intro h i hi t ht hj
    have hl :=hp h
    have he0:u.D.dual (e.v.slotWord i) t:= (Line.Fabric.cap_dual hl).2
                                                         ⟨hi,Nat.one_le_iff_ne_zero.2 (by omega),hj⟩
    have hq:= Line.Fabric.desert12 (v:=e.v) i he.good hc hl he.chart hd
    exact ⟨he0,hq.canonicalS,fun x h=>by rw [hq.lines he0 h];exact (ite_eq_right (Nat.ne_of_lt ht)).symm⟩

end Ace
end
end ExactDerandomization.Gyre.OrbitR.Prism

end

end OAI
