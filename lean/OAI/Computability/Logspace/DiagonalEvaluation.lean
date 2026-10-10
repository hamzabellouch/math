import OAI.Computability.Logspace.EstimatorMachine
import OAI.Computability.Logspace.HierarchyEvaluation

namespace OAI

/-!
Diagonal estimator evaluation, inherited queries, and resource bounds.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line
open Rain
noncomputable section
open scoped Classical

variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
/-- Prism for diagonal, endpoint channel frozen nevertheless read. -/
structure OrbitV (u:Line (q:=q) (w:=w) (h:=h)) where
   m:ℕ
   p:Peek
   dye:Pool u.n
namespace OrbitV
variable (p:OrbitV u)
abbrev tire := p.p.stair u.plotM p.m
abbrev r := rolls u.plotM p.m
abbrev s := Peek.weave u.plotM p.p p.r
abbrev d := p.p.plan u.plotM
abbrev ds := p.d.narrowed 0
abbrev S:=src p.d.S p.d.u p.dye
abbrev channel(q i:ℕ):ℕ:= u.vecL p.p p.m q i p.dye
def works:Prop:= Net.onQ u.plotM.gap p.m (p.p.key u.plotM)=true
def estate:Prop:=p.m ≤ u.limitM ∧ p.p.ready u.plotM p.m
abbrev fwd0:= (forecast u.plotM p.m).outV p.p p.dye
abbrev raw0(x i:ℕ):ℝ:=if x∈p.S then p.s.prefixR p.tire p.ds i p.dye x x else 0
abbrev chipV(x i:ℕ):ℝ :=if x∈p.S then p.s.portion p.tire p.ds i p.dye x x else 0
lemma goal0(x:ℕ)(h:p.works):p.fwd0 x=smooth (p.raw0 x p.tire.L):=by
    have he:p.fwd0 x=(Peek.activeV u.plotM p.p p.r p.m p.dye) x:=by
        exact congrArg (fun u:Paint _=> u p.dye x) (ite_eq_left h)
    rw [he]
    by_cases he:x∈p.S
    · change (if x∈p.S then _ else _)=_; rw [ite_eq_left he]; unfold raw0; rw [ite_eq_left he]
    change (if x∈p.S then _ else _)=_
    rw [ite_eq_right he]; unfold raw0; rw [ite_eq_right he]; simp [smooth]

lemma pos0(x:ℕ):p.raw0 x 0=0:=by unfold raw0;rw [Flame.prefix0];split<;>rfl
lemma next0(x i) : p.raw0 x (i+1)=p.raw0 x i+p.chipV x i:=by
   unfold raw0 chipV; rw [← Flame.next]; split;rfl;norm_num

abbrev actual(p:OrbitV u)(k:MintV)(x:ℕ):ℕ→ℝ
   | 0=>0
   | i+1=> sat (k.shellQ p.m (i+1)) (actual p k x i+p.chipV x i)
lemma pays(k:MintV)(x i):
   |p.actual k x (i+1)| ≤ k.roofX (gap p.m i):=by rw [actual,k.shore]; apply Buf.sat_size; exact (mass0 ..).le
abbrev VoteM(p:OrbitV u)(k:MintV)(x i:ℕ):Prop:=
    ∀ j < i,|p.chipV x j| ≤ massB k.tokenH (gap p.m j)
lemma clamp0(k:MintV)(x i)(h:k.fine)(hj:i ≤ Age.L p.m)(ho:p.VoteM k x i):
     p.actual k x i=sat (k.shellQ p.m i) (p.raw0 x i):=by
   induction i with
   | zero=> rw [p.pos0]; exact (Buf.sat_id (by simp only [abs_zero];unfold MintV.shellQ;positivity)).symm
   | succ i ih=>
     rw [actual,p.next0]
     let s:=k.shellQ p.m i
     have hz:0≤ s:=by unfold s MintV.shellQ; positivity
     have hf:p.actual k x i=sat s (p.raw0 x i):= ih (by omega) (fun j hh=> ho j (by omega))
     have hx: |p.actual k x i| ≤ s:=by rw [hf]; exact Buf.sat_size hz _
     apply Buf.sat_add ?_ ((Buf.sat_id hx).trans hf)
                            (by rw [k.shore]; exact (mass0 ..).le)
     have hr :=ho i (by omega)
     let y:=p.chipV x i
     have hy : Buf.ht (Buf.line y)=|y|:=by simp [Buf.ht]
     exact hy ▸ k.decor h (by omega) _ (hy.symm ▸ hr)
lemma settle {x k}(h:p.VoteM k x (Age.L p.m))(hc:p.works)(ht:k.fine):
     p.fwd0 x=smooth (p.actual k x (Age.L p.m)):= by
   let H:=k.shellQ p.m (Age.L p.m)
   have he := p.clamp0 k x (Age.L p.m) ht le_rfl h
   have hr :1 ≤ H:=by unfold H MintV.shellQ; exact mass1 ..
   rw [p.goal0 x hc,he]; change smooth _ = smooth (sat H (p.raw0 x p.tire.L))
   unfold sat clip smooth; grind

structure Counsel (v:OrbitV u)(k:MintV): Prop where
   hp:u.Chart
   he:v.estate
   till:Turf k u.r u.v
namespace Counsel
variable {v:OrbitV u}{k:MintV} (h0:Counsel v k)
include h0
lemma unitV : u.D.Suite (v.channel 17 0):=by
   apply h0.hp.rent
   exact ((Line.Chart.courseV (u := u)) v.dye).2 ⟨h0.he.1,(show 0<(1:ℕ) from Nat.one_pos),⟨rightV _,Or.inr rfl⟩,h0.he.2⟩
lemma pred0 {i:ℕ}(he:i < Age.L v.m)(hp:v.works):
     u.D.Suite (v.channel 5 i):=by
   have hw:operateV u.w0 v.m (bitV v.p):=by
       unfold operateV; rw [recovered]; exact of_decide_eq_true hp
   apply h0.hp.rent
   exact ((Line.Chart.courseV (u := u)) _).2 ⟨h0.he.1,he,⟨rightV _,Or.inl ⟨rfl,hw⟩⟩,h0.he.2⟩
omit h0 in
lemma heightZ (a i):u.D.D (v.channel a i)=slackT v.m a i:=u.rolff ..
omit h0 in
lemma costZ (a i):u.D.W (v.channel a i)= Age.weight v.m a i:=u.rolfe ..
omit h0 in
lemma foreign (s:Fabric u){i:ℕ}(h:s.m+gap v.m i ≤ v.m) (a g):
      u.D.W (s.c a g)+u.D.D (v.channel 5 i) ≤ u.D.W (v.channel 5 i):=by
    rw [Vessel.OrbitV.Counsel.heightZ,Vessel.OrbitV.Counsel.costZ,Stone.W]
    exact Age.renewal h

end Counsel

structure Earn (e:OrbitV u)(k:MintV)(i x:ℕ):Prop where
   plan : VoteM e k x (i+1)
   untilX:
    let a:=e.channel 5 i
    u.D.Voice a x (hole 1 0) (u.D.high a) (k.sealR*u.D.D a) (e.actual k x (i+1))
def FEnd (p:OrbitV u) :Prop:=
   ∀ x∈u.D.P,let a:=p.channel 17 0;
              u.D.Voice a x (hole 1 0) (u.D.high a) 0 (p.fwd0 x)
end OrbitV
end
end ExactDerandomization.Vessel

end

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line
open Rain Spring
noncomputable section
open scoped Classical

namespace PlanV
variable (w:Wares)
open Rain Garden

abbrev x(C:Crt) := stageQ C
abbrev sensor(C:Crt) := Garden.origin C=6
abbrev j(C:Crt) := (fence C).2.2.1
def trees (a:Crt) : Finset Ray:=
    if sensor a then {(x a,0)}
    else if x a=0 then ∅ else ({x a}:Finset ℕ)×ˢ range (2*w.p.M)
def lead (a:Crt)(s:Seed):Prop:=
    ¬sensor a∧ Age.g a=0 ∧ stageQ a=0∧s= Seed.old false 0

abbrev radius (a:Crt) :Est.Stair:=⟨Age.MV a,0,⟨stageQ a,0,0⟩,w.ell⟩
def beats(a:Crt)(s:Seed):Prop:=
   let z:=s.fog
   s= Seed.along z s.x 0 ∧ s.x<w.p.K ∧ z.first0=true∧
           z.habitat w (x a) (m a) (Age.g a) (trees w a)
def validV (v:Crt)(s:Seed):= lead v s ∨ beats w v s

section
variable {α}[Wire α]{b:PT α Crt}{s:PT α Seed}
open GK
lemma treeC {r:PT α Ray}(h:Kn b)(e:Kn r):GK (fun x a=> r x a ∈ trees w (b x a)):= by
   have hs:=h.right.right.left
   have ht:= hs.left.left
   let p:= (eqG e.left ht).andG (ltG e.right (Kn.fix (2*w.p.M)))
   convert ifG (Garden.Plot.wall e (ht.tuple (Kn.fix 0))) ((eqG ht (Kn.fix 0)).notG.andG p)
                            hs.right.left (Kn.fix 6) using 1
   ext x a; unfold trees sensor; split
   · simp
   split <;> simp_all ; grind
lemma playG(h:Kn b)(hf:Kn s):
   GK (fun x p=> beats w (b x p) (s x p)):=by

    have hp:=h.right.right.left.left.left; let e:=hf.right
    let a:=hf.left.right.left;let g:=e.left.right
    let p:=(g.left.left.cond (hp.add g.left.right) (hp.sub g.left.right))
    let k:= h.right.left; let S:= k.left
    let I:=(S.sub g.right.right).pred
    let u:=(leG (Garden.Plot.yokeK w S k.right hp p) I).andG (ltG I (Garden.Plot.reachK w S k.right hp p))
    let v:=eqG (S.sub I.succ) g.right.right
    let V:= Garden.Plot.wall g.left (hp.cond_le p ((Kn.fix true).tuple (p.sub hp))
                                              ((Kn.fix false).tuple (hp.sub p)))
    let w':= Garden.Plot.countEat e.right.right ((Kn.fix w.ell).times g.right.right) Print.rad
    let H:=(treeC w h (p.tuple g.right.left)).andG (u.andG (v.andG (V.andG w')))
    convert (Garden.Plot.wall hf (((Kn.fix (2:ℕ)).tuple (a.tuple (Kn.fix 0))).tuple e)).andG
                            ((ltG a (Kn.fix w.p.K)).andG ((forth e.left.left).andG H)) using 1
    ext x a; unfold beats Fog.habitat Stair.layers; simp only [mem_Ico]; rfl
lemma formVK (h:Kn b)(he:Kn s):GK (fun x a=> validV w (b x a) (s x a)):=
    let hp:=h.right.right.left
    (((eqG hp.right.left (Kn.fix 6)).notG).andG ((eqG h.right.left.right (Kn.fix 0)).andG
                   ((eqG hp.left.left (Kn.fix 0)).andG (Garden.Plot.wall he (Kn.fix (Seed.old false 0)))))).orG
                   (playG w h he)
end
end PlanV

variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace OrbitV
variable (p:OrbitV u)
abbrev c(j:ℕ):Crt:=Foil.kit 5 (p.m,j) (bitV p.p) (enc (Print.issued p.dye))
abbrev areaV(g:ℕ):Finset Census.Arc:=Census.tracks p.tire p.s.rays g
abbrev grounds (r:Census.Arc)(i:ℕ):Seed:= Seed.along (Census.drops p.tire true r) i 0
lemma agroV(j): p.s.rays= PlanV.trees u.w0 (p.c j):=by
   unfold OrbitV.s Peek.weave PlanV.trees
   cases he:p.p.ask
   · have ht:¬PlanV.sensor (p.c j):=by unfold PlanV.sensor Garden.origin; simp [c, Foil.kit, Garden.fence, bitV, he]
     rw [ite_eq_right ht]
     change _=(if p.p.i=0 then _ else _)
     cases hk:p.p.i with
     | zero=>rfl
     | succ a=> simp only [Peek.roy,hk,Nat.succ_ne_zero,ite_false]; rw [←hk];rfl
   next k=>
   have ht:PlanV.sensor (p.c j):=by unfold PlanV.sensor Garden.origin; simp [c, Foil.kit, Garden.fence,bitV,he]
   rw [ite_eq_left ht];rfl

lemma awakeV {g:ℕ}{r:Census.Arc}(h:r∈p.areaV g) (i:ℕ)(hi:i<u.w0.p.K):
   PlanV.beats u.w0 (p.c g) (p.grounds r i):= by
   refine ⟨rfl,hi,rfl,?_⟩
   rw [←p.agroV]; exact (Census.grange p.tire (w:=u.w0) rfl true h).1
lemma fuel (s:Ray)(h:s∈ p.s.rays): s.2 ≤ u.w0.p.M^2+2*u.w0.p.M+2:=by
   rw [p.agroV 0] at h; unfold PlanV.trees at h
   split at h
   · next he=> rw [show s= _ from mem_singleton.1 h]; dsimp only; omega
   split at h; simp only [notMem_empty] at h
   have hz:= mem_range.1 (mem_product.1 h).2; omega

end OrbitV
end
end ExactDerandomization.Vessel

end

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
noncomputable section
open scoped Classical

namespace Sun
variable (p:MintV)(f:Knob)
def appear (f:Knob)(p:MintV):Branch:=
   ⟨rootsD (⟨_,Kn.power p.vol f.bank.runs⟩),
        ⟨_,stairK true⟩,⟨_,Kn.fix 0⟩,p.vol+1⟩
def festival (x:Word)(a:ℕ):ℕ:=
   let s : Crt:=dec (Reed.V x a).1
   Blade.Crest.pastC s 5
def trigger: Cub ℕ Bool :=
   let h:= (Kn.unpack (α:=Crt)).comp VK.left
   ⟨_,h.right.left.right.eq (Kn.fix (0:ℕ))⟩

def crystal :Sight:=
    let h:= (Kn.unpack (α:=Crt)).comp VK.left
    ⟨_,Kn.wash.comp ((Blade.Crest.pastK h 5).tuple (Kn.fix (hole 1 0)))⟩
abbrev prior (p:MintV):ℕ:=2*p.sealR
def velvet(f:Knob)(p:MintV):Cog:=
    Song.pleas trigger (snow (campk f) (prior p)) (Bullet.snap crystal)
abbrev sail(p:MintV)(g:Cog):Lyric:= .use p.prism g

def chest(f:Knob)(p:MintV)(g:Cog):Lyric:=
    let h:= Lu.psum (.use (prior p) (velvet f p)) (.heap true (appear f p) (sail p g))
    Lu.clippy (.solo p.sealR ⟨_,(scaleK (campk f) p.sealR).comp Kn.first⟩) h
def pasty(g:Cog): Cog:=
       roost (campk f) (chest f p g) p.sealR
abbrev scheduleR (p:MintV)(f:Knob)(g:Cog):Cog:=Studio.arrange (fun _=> pasty p f g) 1
abbrev script (f:Knob)(p:MintV)(g:Cog) := reset (chest f p g) p.sealR

variable {q w h:ℕ}
def priceC(r:Rock q w h)(p:MintV)(c:ℕ):ℕ:=
   let f:= Mold.knob r Cambria.Wear.Paper.noneT
   let x:= script f p Cargo.knock
   c+x.cost c+x.tail
namespace Script
open Cambria.Wear Cambria.Wear.Paper
lemma invar(p:MintV)(f g:Knob)(l n:Cog): same (script f p l) (script g p n):=by
   have hf:same (.heap true (appear f p) (sail p l)) (.heap true (appear g p) (sail p n)):=⟨rfl,rfl,fun _=>rfl⟩
   let a:= Lu.psum (.use (prior p) (velvet f p)) (.heap true (appear f p) (sail p l))
   let b:= Lu.psum (.use (prior p) (velvet g p)) (.heap true (appear g p) (sail p n))
   have ha:same a b:=same.plies (Paper.use ..) hf _
   have he: ∀ {x y:Lyric},same x y → same (Lu.clippy x a) (Lu.clippy y b) :=
        fun h=> same.plies h (same.plies (same.plies (Paper.oneself _) h _) ha _) _
   exact (he (x:=_) everF).stow _
lemma estimate(r:Rock q w h)(f:Knob)(p:MintV)(g:Cog)(c:ℕ):
    let s:=script f p g
    let P:= priceC r p c
    c ≤ P ∧ s.cost c ≤ P ∧s.tail ≤ P:=by
   intro s P
   have h:=invar p f (knob r Cambria.Wear.Paper.noneT) g Cargo.knock
   change same s _ at h; obtain ⟨-,hx,hp⟩:=h
   rw [hx,hp]; unfold P priceC;dsimp only; omega
end Script
end Sun
namespace Basket
open Sun

variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
structure Sack(u:Line (q:=q) (w:=w) (h:=h))where
    v:OrbitV u
    k:MintV
    i:ℕ
    c:ℕ
    g:Cog
namespace Sack
variable (s:Sack u)
abbrev a := s.v.channel 5 s.i
abbrev d:=gap s.v.m s.i
abbrev Pn:=s.k.rangeN s.d
abbrev h0:=u.D.high s.a
abbrev wallet := Sun.priceC u.r s.k s.c
abbrev τ:=s.h0+s.wallet*s.d
abbrev urn(x:ℕ):=Studio.dockA u s.a x
abbrev home(x i:ℕ):= Studio.stk u s.a x i
abbrev I(u: Line (q:=q) (w:=w) (h:=h)):=Mold.knob u.r u.v
structure Ground (s:Sack u):Prop where
     hc:s.v.Counsel s.k
     ha:s.v.works
     hk:s.i<Age.L s.v.m
     pay : s.wallet ≤u.v.slope
     pawl: powder 100  ≤  s.c ∧ 4 ≤ s.c ∧ Bullet.roomS ≤ s.c
     cargo:Studio.Parcel u s.a (scheduleR s.k (I u) s.g)
def priorE (s:Sack u)(x:ℕ): Prop:=
     ∀ i,s.i=i+1 → s.v.Earn s.k i x

structure harvest (s:Sack u)(x:ℕ)(f:ℕ → ℝ): Prop where
    matchesV: ∑ i∈range s.Pn,f i = s.v.chipV x s.i
    limb : ∀ i<s.Pn, Seats.band (s.home x i) s.c s.τ s.k.prism s.g (f i)
namespace Ground
variable {s:Sack u}(he:s.Ground)
include he
omit he in
lemma wages:u.D.D s.a=s.d:=Vessel.OrbitV.Counsel.heightZ ..
lemma pro : u.D.Suite s.a:=he.hc.pred0 he.hk he.ha
lemma guest {x:ℕ}(hx:x∈u.D.P)(j): Standard (s.home x j) (campk (I u)) s.τ:=by
   have hs:s.τ  ≤  u.D.H:=by
       unfold τ; rw [←(Vessel.Basket.Sack.Ground.wages (s := s))]; exact Studio.stayedC he.pro le_rfl he.pay
   exact ⟨Studio.positioned he.pro hx _ _, spanFilm (Studio.vital _ hs) ..⟩
omit he in
lemma phase0 (x j:ℕ): Reed.V u.x (s.home x j).info=((s.a,j,0):Stool):=Wire.eq _
omit he in
lemma deco0: (dec (s.a):Crt)=s.v.c s.i :=by unfold a OrbitV.channel vecL clr;rw [Wire.eq]
end Ground
end Sack
end Basket
end
end ExactDerandomization.Vessel

end

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear
noncomputable section
open scoped Classical

variable {q w h:ℕ}
namespace Fort
abbrev MeterQ := (Cambria.Hull × (ℕ×ℕ)) × Coin× ℕ ×ℕ × History

abbrev Manta:=ℕ×MeterQ
namespace MeterQ
abbrev h0 (p:MeterQ):Hull:=p.1.1
abbrev headQ(p:MeterQ):ℕ:=p.1.2.1
abbrev i(p:MeterQ):ℕ:=p.1.2.2
abbrev value(p:MeterQ):Coin:=p.2.1
abbrev ago(p:MeterQ):ℕ:=p.2.2.1
abbrev hereP(p:MeterQ):ℕ:=p.2.2.2.1
abbrev pt(p:MeterQ):History:=p.2.2.2.2
end MeterQ
variable (r:Rock q w h)
abbrev tea:Cub ℕ MeterQ:=⟨_, (Kn.unpack (α:=Manta)).right⟩
abbrev whoseK0:Sight:=⟨_, (Kn.unpack (α:=Manta)).left⟩
def osky (I:Knob):Knob:=
    let f(k:Cub ℕ ℕ):Cub ℕ ℕ:=⟨_,k.runs.comp whoseK0.runs⟩
    ⟨f I.height,f I.bank,f I.store⟩
def surf(c:MeterQ):Surf:=(c.h0,(default,default),default,(0,1,0))
def light (n M x:ℕ)(p:MeterQ):Bool:=
    decide (0<p.headQ ∧ (p.headQ<3∨ x%M=p.i)) && (surf p).frontC n x && (surf p).finalC n x
lemma lightK :Kn (fun x (a:History)=>light (r.n x) r.w.p.M a.2 (tea.f x a.1)) :=by
   have hM:= tea.runs.comp (Kn.first (β:=ℕ)); let e:= hM.left.right
   have hp: Kn (fun x (v:History)=> surf (tea.f x v.1)):= hM.left.left.tuple (Kn.fix _)
   have he:Kn (fun x (v:History)=>(surf (tea.f x v.1)).flareQ false (r.n x) ((surf (tea.f x v.1)).windC v.2)):=
       Surf.Prep.chapter r.nKn (Surf.Prep.windK hp Kn.next) hp false
   exact Print.both (Print.both (GK.decideK ((GK.ltG (Kn.fix _) e.left).andG ((GK.ltG e.left (Kn.fix _)).orG
                        (GK.eqG (Kn.next.mod (Kn.fix _)) e.right)))) (Surf.Prep.facet r.nKn Kn.next hp)) he
def nearC:Cog:= Flash.search ⟨_,Kn.wash.comp (lightK r)⟩

abbrev atQ(o:Cub ℕ ℕ)(b:ℕ):Sight:=⟨_,Kn.wash.comp (o.runs.tuple (Kn.fix (hole b 0)))⟩
abbrev hereId:Sight:=⟨_,tea.runs.right.right.right.left⟩
abbrev presentQ:Cog:=Bullet.snap (atQ hereId 1)
abbrev upQ: Sight:=⟨_,tea.runs.right.right.left⟩
abbrev elder:Kiwi:=⟨_,tea.runs.right.right.right.right⟩
abbrev stampF(k:ℕ):Sight:=⟨_,Kn.wash.comp (elder.runs.left.tuple
                                     (Kn.wash.comp ((Kn.fix k).tuple elder.runs.right)))⟩
abbrev leave(k:ℕ) : Cog := Bullet.snap (stampF k)
def secondC (k:ℕ):Kiwi:=by
   let p:=(Kn.unpack (α:=Crt)).comp elder.runs.left
   let F:=Kn.wash.comp ((Kn.fix 12).tuple p.right)
   exact Flash.clan ⟨_,Kn.wash.comp (F.tuple elder.runs.right)⟩ k
def premier(r:Rock q w h):Kiwi:=by
   let p:=tea.runs.left.right.right
   let s:=p.add (Kn.fix r.w.p.M)
   let t:=Kn.wash.comp ((Kn.fix 0).tuple ((Kn.fix 3).add s))
   exact Flash.clan ⟨_,t⟩ 0
def chip(p:MintV): Lyric:= .solo p.prism (⟨_,(tea.runs.right.left).comp Kn.first⟩)
abbrev priorF(k:ℕ):Sight:=by
    let p:= ((Kn.unpack (α:=Crt)).comp upQ.runs)
    let q:=p.right.right.left
    let s:=q.left.tuple (q.right.left.tuple ((Kn.fix k).tuple q.right.right.right))
    let w:=p.left.tuple (p.right.left.tuple (s.tuple p.right.right.right))
    exact atQ ⟨_,Kn.wash.comp w⟩ 1

def boost0 (I:Knob)(i:ℕ):Lyric:=
    let p:= choir I (.solo 0 (⟨_,Kn.fix (Coin.ofZ 1)⟩))
    .use 0 (Song.pleas (Wear.falls upQ) p (Bullet.snap (priorF i)))
def bootsY (I:Knob):ℕ → Lyric
    | 0=> Lu.zeroE
    | nX+1=> Lu.sup (bootsY I nX) (boost0 I nX)

variable (p:MintV)(v: Tags)
abbrev P :Knob:=osky (Mold.knob r v)
def genus : Lyric:= times (chip p) (Amber.shade presentQ p.coin (Wear.powerF p))
abbrev starC (n:ℕ): Cub ℕ Bool:=⟨_,tea.runs.left.right.left.eq (Kn.fix n)⟩
def actorP :Lyric:= boostR (bootsY (P r v) r.w.p.T)
def fresh : Lyric:= times (times (chip p) (actorP r v)) (.use 0 presentQ)
def mixC(k:ℕ):Lyric:=
   let t:Lyric:=.use 0 (Pier.escort (Helix.Orbit.schedule r v) (secondC k) presentQ)
   times (times (Lu.times (chip p) (actorP r v)) (Amber.shade (leave 1) p.coin (Wear.powerF p))) t
def syncC:Cog:=
   let u:=p.prism; let f(k:ℕ):Cog:= if k=0 then snow (P r v) u else roost (P r v) (mixC r p v k) u
   Iris.dial (leave 0) f (clim r.w.p)
def drill :Cog:=
    let f:= pleas (starC 3) (roost (P r v) (fresh r p v) p.prism) (syncC r p v)
    Pier.escort (schedule r v) (premier r) f

def base :Lyric:=by
    let g:Cub History Coin:=⟨fun x a=>Coin.ofZ (if r.P.fin x a.2 then 1 else 0),?_⟩
    · exact Amber.moonF g 0
    let p:PT History ℕ:=fun x a=> if r.P.fin x a.2 then 1 else 0
    have hf:Kn p:=by
        intro g hg
        exact Counter.Pick.ite (r.P.eReward ((Kn.next (α:=ℕ) (β:=ℕ)) hg)) (Counter.E.const _) (Counter.E.const _)
    convert Coin.ofK hf.ZofN using 1; funext x a; unfold p; split <;>rfl
def radiate : Cog :=
    let k:=P r v; let g:=snow k p.prism
    let m:=pleas (starC 1) (roost k (base r) p.prism)
                                 (pleas (starC 2) (roost k (genus p) p.prism) (drill r p v))
    Cargo.choose (nearC r) g m
end Fort
end
end ExactDerandomization.Vessel

end

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical

variable {q w h:ℕ}
namespace PrintV
open PlanV

def topHull (r:Rock q w h)(s:Word)(p:Crt)(l:History):Cambria.Hull:=
     ((Aqua.tally r s (stageX p),p0 p,0),l,dec (Age.env p))
 where stageX p:=PlanV.x p
       p0 p:=(Garden.params p).2.1

section
variable {α}[Wire α]{c:PT α Crt}{p:PT α History}
lemma topK(r:Rock q w h)(hf:Kn c)(he:Kn p): Kn (fun x a=> topHull r x (c x a) (p x a)):=
     let t:=hf.right.right.left.left
     ((Aqua.tallyK r t.left).tuple (t.right.left.tuple (Kn.fix 0))).tuple (he.tuple (Kn.unpack.comp hf.right.right.right))
end
abbrev sh(u k:ℕ):Scout:=bitV (prizep u k)
abbrev vshot(u k:ℕ):Scout:=bitV (detector u k)
abbrev dshot(u k:ℕ):Scout:=bitR (Peek.score u k)
abbrev eshot(w:Wares)(u k:ℕ):Scout:=bitR (Quest.mk u k u u (.echo false (w.p.T-1)) true)

def detectors (p:Hull)(i k t:ℕ)(s:Issue)(c:Coin):MeterQ:=
   ((p,(2,0)),c,0,Blade.Crest.launch 16 t (dshot i k) (Prism.crossE s),0,0)
def roy (h:Hull)(n M:ℕ)(w:Wares)(i k l z t:ℕ)(b:Bool)(p:Issue)(c:Coin): MeterQ:=
    let s:= Prism.swap n M i 0 p
    let H:=if i=0 then 0 else Blade.Crest.launch 17 t (vshot l 0) s
    if b then
       ((h,(3,i)),c,H,Blade.Crest.launch 17 t (sh l k) s,0,0)
    else
       ((h,(4,i)),Coin.mult c (Aqua.rawcoins n l),H,Blade.Crest.launch 17 t (sh l l) (Prism.rightE s),
                     Blade.Crest.launch 14 t (eshot w l k) (Prism.leftE s),z)
abbrev dawn(h:Hull): MeterQ:= ((h,(1,0)),Coin.ofZ 0,0,0,0,0)
abbrev black : MeterQ:=default

variable (r:Rock q w h)
def model (x:Word)(a:Crt)(p:Seed):MeterQ:=
   let b:=r.w; let q:=Garden.origin a; let k:=PlanV.x a
   let u:=(Garden.params a).2.1
   if p.1.1=1 then dawn (topHull r x a (0,0)) else
    let t:=p.fog
    let z := (t.ray k).2
    let i:=t.budget (Garden.m a)
    let h:= (t.tick b,t.event)
    let c:=RowD.startF r x a t
    let s:= Print.stepout (r.n x) u 0 h.1 h.2 (dec (Age.env a))
    let v:= topHull r x a h
    if q=6 then if p.x=0 then detectors v k (PlanV.j a) i s c else black
    else
     let M:=b.p.M
     if z < M then if p.x=0 then roy v (r.n x) M b z u (k-1) p.x i true s c else black
     else roy v (r.n x) M b (z-M) u (k-1) p.x i false s c

section
variable {α}[Wire α]{i j v n a b:PT α ℕ}{s:PT α Issue}{h0:PT α Cambria.Hull}{u:PT α Coin}
lemma shK(p:Kn i)(h:Kn j):Kn (fun x a=> sh (i x a) (j x a)) :=
    (p.tuple (h.tuple (Kn.fix _))).tuple (Kn.fix ((5,0,false):ChoiceX))
lemma vhK(p:Kn i)(j):Kn (fun x a=> vshot (i x a) j) :=
    (p.tuple (p.tuple (Kn.fix _))).tuple (Kn.fix ((6,j,false):ChoiceX))
lemma dhK(p:Kn i)(h:Kn j):Kn (fun x a=> dshot (i x a) (j x a)) :=
    (p.tuple (p.tuple (p.tuple p))).tuple ((Kn.fix 4).tuple (h.tuple (Kn.fix _)))
lemma ehK(p:Kn i)(h:Kn j)(w):Kn (fun x a=> eshot w (i x a) (j x a)) :=
    (p.tuple (h.tuple (p.tuple p))).tuple (Kn.fix ((3,w.p.T-1,true):ChoiceX))
lemma dewK (ht:Kn h0)(p:Kn i)(h:Kn j)(ha:Kn v)(hv:Kn s)(hc:Kn u):
     Kn (fun x a=> detectors (h0 x a) (i x a) (j x a) (v x a) (s x a) (u x a)) :=
    let w:= hv.right.left.tuple (hv.left.tuple hv.right.right)
    let H:=Blade.Crest.orbitK 16 ha (dhK p h) w
    (ht.tuple (Kn.fix _)).tuple (hc.tuple ((Kn.fix _).tuple (H.tuple (Kn.fix _))))
lemma royp (ht:Kn h0)(M:ℕ)(w:Wares)(hn:Kn n)(p:Kn i)(h:Kn j)(hf:Kn a)(he:Kn b)(ha:Kn v)(d:Bool)(hv:Kn s)(hc:Kn u):
    Kn (fun x y=> roy (h0 x y) (n x y) M w (i x y) (j x y) (a x y) (b x y) (v x y) d (s x y) (u x y)):=by
   have hp:=Prism.swapK hn p (Kn.fix 0) hv M
   have hS:=p.cond_eq (Kn.fix 0) (Kn.fix 0) (Blade.Crest.orbitK 17 ha (vhK hf 0) hp)
   have hl:=hp.left.tuple (hp.right.right.tuple hp.right.left); have hr:=hp.right.right.tuple (hp.right.left.tuple hp.left)
   cases d
   · exact (ht.tuple ((Kn.fix 4).tuple p)).tuple
                 ((Coin.multK hc (Aqua.rawK hn hf)).tuple (hS.tuple
                    ((Blade.Crest.orbitK 17 ha (shK hf hf) hr).tuple
                            ((Blade.Crest.orbitK 14 ha (ehK hf h w) hl).tuple he))))
   exact (ht.tuple ((Kn.fix _).tuple p)).tuple
                         (hc.tuple (hS.tuple ((Blade.Crest.orbitK 17 ha (shK hf h) hp).tuple (Kn.fix _))))
variable {q:PT α Crt}{p:PT α Seed}
lemma modelK(hf:Kn q)(he:Kn p):Kn (fun x a=>model r x (q x a) (p x a)):=by
   have hp:= hf.right.right; have hT:=hp.left.left; have hg:=hT.left
   have hh:= he.right; have h:= he.left
   have ha:= ((Kn.fix r.w.ell).times hh.left.right.right.right).tuple hh.right.right
   have ht:=hf.right.left.left
   let k:= (ht.sub hh.left.right.right.right).pred
   have hb:= hh.right.left.cond k.succ k
   let v:= topK r hf ha
   let E:= hp.left.right
   let i:= h.right.left
   have hu:=r.nKn (α:=α)
   let p:=hT.right.left
   have hL:= Print.stepK hu p (Kn.fix 0) ha.left ha.right (Kn.unpack.comp hp.right)
   have hC:=RowD.startK r hf hh
   let z:= hh.left.right.right.left
   let w:=Kn.fix (α:=α) r.w.p.M
   exact h.left.cond_eq (Kn.fix _) (((topK r hf (Kn.fix _)).tuple (Kn.fix _)).tuple (Kn.fix _))
     (E.left.cond_eq (Kn.fix _) (i.cond_eq (Kn.fix 0)
               (dewK v hg E.right.left hb hL hC) (Kn.fix black))
         (z.cond_lt w (i.cond_eq (Kn.fix _) (royp v _ r.w hu z p hg.pred i hb true hL hC)
                                                  (Kn.fix black))
                         (royp v _ _ hu (z.sub w) p hg.pred i hb false hL hC)))
end
def garment (x:Word) (p:ℕ):ℕ:=
    let h:= Reed.V x p
    let a:=h.1
    let j:=h.2.1
    let c:Crt:=dec a
    let s:Seed:=dec j
    enc ((a,(if enc s=j ∧ validV r.w c s then model r x c s else black)):Manta)
lemma garmentK : Kn (garment r):=by
    have hp:=VK.right.left; have hv:=VK.left
    have ht:=(Kn.unpack (α:=Seed)).comp hp
    have he:=(Kn.unpack (α:=Crt)).comp hv
    have hh:= GK.decideK ((GK.eqG (Kn.wash.comp ht) hp).andG (formVK r.w he ht))
    let t:= Kn.wash.comp (hv.tuple (hh.cond (modelK r he ht) (Kn.fix black)))
    convert t using 1; funext x a; simp [garment]

def shell (p:MintV)(v:Tags):Cog:= Fret.Seats.transformed ⟨_,garmentK r⟩ (Fort.radiate r p v)
end PrintV
end
end ExactDerandomization.Vessel

end

section

namespace ExactDerandomization.Gamut
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Night Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats _root_.OAI.ExactDerandomization.Sub
open Rain Spring
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}

namespace Shift
variable (u:Line (q:=q) (w:=w) (h:=h))
lemma audible {i:ℕ}(he:u.D.audible i):
   unitK i≠0∧ i=post (unitK i) (opt i) (posn i) (date i) ∧
                  Orbit.taps (dec (unitK i):Crt).1 (opt i) (date i)∧ u.smallQ (unitK i) (posn i):=by
   obtain ⟨h1,h2,h3,h4,h5⟩:= of_decide_eq_true he
   exact ⟨h1,h3,h4,h5⟩

lemma motion {v t:ℕ}(he:u.D.dual v t):v=hole (cell v) (Scheme.inside v)∧
     (if cell v=0 then Scheme.inside v ≤ u.v.bonus ∧ t ≤ u.v.bonus else (uphold (cell v)).1=12):=by
   obtain ⟨ha,hb⟩:= of_decide_eq_true he
   constructor
   · exact ha
   split
   · next h=>
     change (if cell v=0 then Scheme.inside v ≤ u.v.bonus ∧ t ≤ u.v.bonus else _) at hb
     rwa [ite_eq_left h] at hb
   next h=>
   change (if cell v=0 then _ else licensed _ _ _ ∧ _ ) at hb
   rw [ite_eq_right h] at hb; exact hb.2.1

/-- Hear open units by two predicates. -/
lemma asked(a) (hm : ∀ i j o,a≠0→Orbit.taps (uphold a).1 o j→u.smallQ a i→j  ≤  u.D.high a→
                    ∀ x∈u.D.P,∃ z,u.D.swears (post a o i j) x z)
     (hc :∀ i t,u.D.dual (hole a i) t→ ∃ f,u.D.Streams (hole a i) f) :
   u.D.Ears0 a:=by
    constructor
    · intro q h hp hv x hx
      obtain ⟨ht,h1,h2,h3⟩:= Shift.audible _ hp; rw [h] at h1 h2 h3 ht
      obtain ⟨z,hz⟩:=hm _ _ _ ht h2 h3 hv _ hx
      exact ⟨z, h1.symm ▸ hz⟩
    intro p hf ⟨z,he⟩
    have ht:p=hole a (Scheme.inside p):=(motion u he).1.trans (congrArg (fun i=>hole i (Scheme.inside p)) hf)
    obtain ⟨b,hb⟩:=hc (Scheme.inside p) z (ht ▸ he)
    refine ⟨b,?_⟩; rwa [ht]
lemma incline {a:ℕ}(ha:a≠0)(hp:(uphold a).1≠12):∀ i t,u.D.dual (hole a i) t →
        ∃ f,u.D.Streams (hole a i) f:=by
    intro i t h
    have hz:=(motion u h).2
    rw [show cell (hole a i)=a from by simp [cell,hole],ite_eq_right ha] at hz
    contradiction
lemma free {a r:ℕ}(he:a≠0)(ht:(uphold a).1=r)(hk:∀ i t,¬ Orbit.taps r i t) (h:r≠12):u.D.Ears0 a:=
    asked _ a (fun _ t i _ hu=>False.elim (hk i t (ht ▸ hu))) (incline _ he (ht.symm ▸ h))

lemma basic(hp:u.Chart):u.D.Ears0 0 :=
    asked _ _ (fun _ _ _ h=>False.elim (h rfl)) (fun i _ _=>⟨_,hp.bootsBasic i⟩)

open Line.Fabric
lemma earsTag(p:Fabric u)(a i:ℕ)
    (he:a=1∨a=3)
    (hr:∀ x∈u.D.P,∀ j,u.smallQ (p.c a i) j →∃ b,u.D.swears (post (p.c a i) 0 j 0) x b):
     u.D.Ears0 (p.c a i):=by
   apply asked
   · intro j k o h0 ht hk hy x hx
     rw [Stone.roleR] at ht
     have hx':o=0∧k=0:=by unfold taps colorQ omegaQ at ht;omega
     rw [hx'.1,hx'.2]; exact hr x hx j hk
   apply incline _ (Age.cpos _); simp [uphold,Foil.kit] ; omega

lemma terminal(p:Fabric u)(k:MintV)(f)(hp:p.Tgood k f):
    u.D.Ears0 (p.c 9 0) :=by
     apply asked
     · intro i j t hl h hi hh x hx
       rw [Stone.roleR] at h
       have hv(b:Bool):= (hp.secure b).suit
       obtain h|h:=h
       · have hz:j=0:=h.2.2
         subst j
         unfold omegaQ at h
         rcases h.2.1 with h|⟨-,h⟩
         · subst t; exact ⟨_,((hv false).trace x hx).next i hi⟩
         subst t; exact ⟨_,((hv true).trace x hx).next i hi⟩
       have he:t=4:=by unfold colorQ at h;omega
       subst t
       obtain ⟨w,hE⟩:= ((hv true).voices x hx).ready i hi
       exact ⟨_, hE.glad j hh⟩
     apply incline _ (Age.cpos _); simp [uphold,Foil.kit]
lemma eventE(p:Fabric u)(k:MintV)(f)(hp:p.Efine k f):
    u.D.Ears0 (p.c 14 0):=by
     apply asked
     · intro i j t hl h hi hh x hx
       rw [Stone.roleR] at h
       have hv:=hp.sector.suit
       obtain h|h:=h
       · have hz:t=0∧j=0:=by unfold omegaQ at h;omega
         rw [hz.1,hz.2]; exact ⟨_,(hv.trace x hx).next i hi⟩
       have he:t=1:=by unfold colorQ at h;omega
       subst t
       obtain ⟨w,hE⟩:= (hv.voices x hx).ready i hi
       exact ⟨_,hE.glad j hh⟩
     apply incline _ (Age.cpos _);simp [uphold,Foil.kit]

lemma court(p:Fabric u) (hs:u.D.Suite p.core12)(hr:∀ i<p.Rslots,∃ f,u.D.Streams (p.slotWord i) f):
    u.D.Ears0 p.core12:=by
     apply asked
     · intro i j t he hu
       rw [show (uphold p.core12).1=12 from Stone.roleR ..] at hu
       unfold taps colorQ omegaQ at hu; omega
     intro i z he;exact hr i ((Line.Fabric.cap_dual hs).1 he).1

end Shift
end
end ExactDerandomization.Gamut

end

section

namespace ExactDerandomization.Gamut
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Night Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats _root_.OAI.ExactDerandomization.Sub
open Line.Fabric Producer
open Rain Spring
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Pond
variable (p:MintV)(v:Fabric u)

abbrev serveR (n:ℕ): Stand:= Stand.TDef n
abbrev serveE (n:ℕ): Stand:= Stand.IDef n
abbrev reapT(w:Wares):Stand:=serveR (clim w.p)
abbrev reapE(w:Wares):Stand:=serveE w.p.J
abbrev rankR(v:Fabric u)(x:ℕ):ℝ:=rank v.S0 (fun a=> v.aimE true a x) (clim u.w0.p)
abbrev rankE(v:Fabric u)(x:ℕ):ℝ:=rank v.S0 (fun a=> v.finalE a x) u.w0.p.J
def TracedR :=
   let a:=v.c 13 0
   ∀ x∈u.D.P,u.D.Voice a x (hole 1 0) (u.D.high a) 0 (rankR v x)
def TracedE :=
   let a:=v.c 16 0
   ∀ x∈u.D.P,u.D.Voice a x (hole 1 0) (u.D.high a) p.coin (rankE v x)
structure Books (p:MintV)(v:Fabric u)(k:ℕ) : Prop where
   iris: Stone.Rector v p
   bod : v.Mantle k
   urn : (reapT u.w0).tollD u ≤ u.v.slope
   ern : (reapE u.w0).tollD u ≤ u.v.slope
   readT:u.s.scripted 13=(reapT u.w0).score0 u.r u.v u.s.pave
   readE:u.s.scripted 16=(reapE u.w0).score0 u.r u.v u.s.pave
namespace Books
variable {p v k}(hB: Books (u:=u) p v k)
include hB
omit hB in
lemma nonn {c:ℝ} (p:Trio)(b:ℕ→Blob)(a:At.Grid)(h:TS a.z c p) (g:Bool)(x y:ℕ):0≤a.pre b p g x y:=by
    unfold At.Grid.pre; split;exact h.nn ..; rfl
lemma echoR {f}(hh:v.Tgood p f) (hp:u.D.Suite (v.c 13 0))(hs:u.D.Heard (v.c 13 0)):
   TracedR v:=by
   let s:=reapT u.w0
   have he : s.Law v (f true) k 0 (v.aimE true):=by
       refine ⟨hB.bod,hB.iris.good,hp,hs,?_,?_ ,hh.secure true,?_⟩
       · change 11<13∧ 9<13∧5<(11:ℕ)∧5< (9:ℕ)∧(13:ℕ) ≤64;omega
       · exact Or.inl ⟨rfl,rfl⟩
       intro x i; unfold Producer.scoreF; split
       · obtain ⟨v0,-⟩:= hB.iris.book.saving.money
         exact Gamut.Pond.Books.nonn _ _ _ (v0.T.support v.t.tag) _ _ _
       rfl
   intro x hx
   exact Stand.Law.ardent he hB.urn (Or.inl rfl) hB.readT hx

omit hB in
lemma sunny(_: Paint u.n)(t: Pool u.n)(Φ:ℝ→ℝ)(e:∀ x,0≤Φ x) (f:ℕ→Paint u.n)(i x:ℕ):
    0≤ Est.Leader Φ i f t x:=e _
lemma echoE {f}(h:v.Efine p f) (hp:u.D.Suite (v.c 16 0))(hs:u.D.Heard (v.c 16 0)):TracedE p v:=by
   let s:=reapE u.w0
   have he : s.Law v f k p.coin v.finalE:=by
       refine ⟨hB.bod,hB.iris.good,hp,hs,?_,?_ ,h.sector,?_⟩
       · change 15<16∧ 14<16∧ 5<(15:ℕ)∧ 5<(14:ℕ)∧(16:ℕ) ≤64;omega
       · exact Or.inr ⟨rfl,rfl⟩
       intro x i; unfold Producer.scoreF; split
       · unfold Fabric.finalE forecast current; dsimp only; split
         · change 0≤ v.grid.pre v.grains (v.t.trio u.plotM) v.t.two x (f.locate x i) *
                                      v.grid.incG v.grains (f.locate x i)*
                     v.t.tower u.plotM v.roll v.m (crossP v.dye) (f.locate x i)
           obtain ⟨v0,-⟩:= hB.iris.book.saving.money
           refine mul_nonneg (mul_nonneg ?_ (v.grid.incG_bounds ..).1) ?_
           · exact Gamut.Pond.Books.nonn _ _ _ (Tonic.fee (s:=u.plotM) v0.T hB.iris.good.2) ..
           unfold Quest.tower;split
           · exact (gamma_mem ..).1
           exact zero_le_one
         exact le_refl _
       rfl
   intro x hx
   exact Stand.Law.ardent he hB.ern (Or.inr rfl) hB.readE hx

end Books
end Pond

end
end ExactDerandomization.Gamut

end

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}
namespace GoodF
open Paper

abbrev hour (_:MintV)(r:Rock q w h):ℕ:= Era.tariff r+4
abbrev treasury (p:MintV)(r:Rock q w h):ℕ:=
   let c:=hour p r
   let L(l:Lyric):=l.tail+(reset l p.prism).cost c+(reset l p.prism).tail
   c+L (base r)+L (genus p)+L (fresh r p noneT)+ L (mixC r p noneT 0)
lemma bloss (r:Rock q w h)(x y:Tags) : same (actorP r x) (actorP r y):=by
    have h(i):same (bootsY (P r x) i) (bootsY (P r y) i):=by
         induction i with
         | zero=> exact oneself Lu.zeroE
         | succ i ih=> exact same.plies ih (Paper.use ..) _
    exact (h _).red
lemma estimated(p:MintV)(r:Rock q w h)(v:Tags):
   let c:= hour p r; let u:=treasury p r
   2  ≤ c ∧powder 100 ≤ c∧ c ≤ u∧∀ j l,
    (l=base r ∨ l=genus p∨l=fresh r p v ∨ l=mixC r p v j) →
          (reset l p.prism).tail ≤ u ∧ (reset l p.prism).cost c  ≤ u:=by
   intro c u
   let H(l:Lyric) := l.tail+(reset l p.prism).cost c+(reset l p.prism).tail
   have hu:u = c+ H (base r) + H (genus p)+H (fresh r p noneT)+H (mixC r p noneT 0):=rfl
   have he {l p2:Fret.Lyric} (h:same l p2) : H l=H p2:=by
       unfold H; rw [h.2.1]; have hh:=h.stow p.prism; rw [hh.2.2,hh.2.1]
   have hv:same (fresh r p noneT) (fresh r p v) :=
        ((oneself _).plies (bloss r _ _) _).plies (oneself _) _
   have hw(j):same (mixC r p noneT 0) (mixC r p v j) :=
        (((oneself _).plies (bloss r _ _) _).plies (oneself _) _).plies (Paper.use ..) _
   have h2:Cambria.Era.tariff r  ≤ c:=Nat.le_add_right ..
   have hp:=Era.billed r
   rw [hu]; refine ⟨by omega,by omega,by omega,fun j l h=>?_⟩
   have hh (k) : (reset k p.prism).tail ≤ H k ∧ (reset k p.prism).cost c ≤ H k:=by
         unfold H;omega
   obtain ⟨ht,hq⟩:=hh l
   rw [he hv,he (hw j)]; grind

end GoodF

namespace Sleigh
open Basket Basket.Sack Sun

section
variable {u:Line (q:=q) (w:=w) (h:=h)}
structure Wax (u:Line (q:=q) (w:=w) (h:=h)) where
   s:Basket.Sack u
   x:ℕ
   i:ℕ
   p:MeterQ
namespace Wax
variable (p:Wax u)
abbrev quote0:= enc ((p.s.a,p.p):Manta)
abbrev s0 (x):=u.D.chord p.s.a x p.quote0
abbrev f:=p.s0 p.x
abbrev g:=p.s.k
abbrev plant := GoodF.hour p.g u.r
abbrev due := p.s.c
abbrev k0(u:Line (q:=q) (w:=w) (h:=h)):=P u.r u.v
abbrev H:=p.s.τ
abbrev T:=p.H + p.due*p.s.d

structure Good (p:Wax u):Prop where
    char:p.s.Ground
    ready:p.x∈u.D.P
    read :p.s.g=PrintV.shell u.r p.s.k u.v
    oath:p.due=GoodF.treasury p.g u.r
    cost0:p.s.wallet + p.s.c ≤ u.v.slope
    makes:PrintV.garment u.r u.x (p.s.home p.x p.i).info=p.quote0
namespace Good
variable {p:Wax u}(he:p.Good)
include he
omit he in
lemma meter (_ _ _:ℕ):True:=trivial
lemma nums :2 ≤ p.plant∧p.plant ≤ p.due∧ Bullet.roomS ≤ p.plant ∧powder 100 ≤ p.plant:=by
   have h:= GoodF.estimated p.g u.r u.v
   have hp:=Era.billed u.r ; refine ⟨h.1,he.oath ▸ h.2.2.1,?_ ,h.2.1⟩
   exact hp.2.1.trans (Nat.le_add_right ..)
omit he in
lemma charged :p.T= p.s.h0 + (p.s.wallet+p.s.c)*p.s.d:=by unfold T H due Basket.Sack.τ; ring
lemma through {a:ℕ}(h:u.D.W a+u.D.D p.s.a  ≤ u.D.W p.s.a):p.T  ≤ u.D.high a:= by
    rw [Vessel.Sleigh.Wax.Good.charged, ←(Vessel.Basket.Sack.Ground.wages (s := p.s))]; exact Studio.soonerC he.char.pro h he.cost0 le_rfl
lemma remains {x}(hx:x∈u.D.P):Standard (p.s0 x) (k0 u) p.T:=by
   have ht:= he.char.pro
   have heA:p.T ≤ u.D.H:= by rw [Vessel.Sleigh.Wax.Good.charged, ←(Vessel.Basket.Sack.Ground.wages (s := p.s))];exact Studio.stayedC ht le_rfl he.cost0
   let k:=knob u.r u.v
   have hf:= Mold.knows u.r u.v u.x u.prog p.s.a x (of_decide_eq_true ht.stage) hx ht.shape.price
   have hv: whoseK0.f u.x p.quote0=p.s.a:=by
                            change (dec (enc _):Manta).1=_;rw [Wire.eq]
   refine ⟨fun i hi=>?_,?_⟩
   · have hm:=hf _ hi
     refine ⟨hm.1,?_,?_⟩
     · change k.height.f u.x (whoseK0.f u.x p.quote0)=_
       rw [hv]; exact hm.2.1
     change k.bank.f u.x (whoseK0.f u.x p.quote0)=_
     rw [hv];exact hm.2.2
   exact Nat.pow_le_pow_right Nat.zero_lt_two heA
omit he in
lemma foster : tea.f u.x p.quote0=p.p:=by change (dec (enc _):Manta).2=_; rw [Wire.eq]
abbrev lampY(p:Wax u):Bool:=light u.n u.w0.p.M p.x p.p
lemma shines :
   p.f.rite p.plant (nearC u.r) (enc (lampY p)):=by
   let h:= he.char.pro
   apply Flash.found u.D h he.ready he.nums.1 _ (Pier.seal_bit u.D h he.nums.1 (q:=p.quote0) _)
   change enc (light _ _ p.x (tea.f u.x p.quote0))=_
   rw [Vessel.Sleigh.Wax.Good.foster];rfl
omit he in
lemma body0(k): (starC k).f p.f.l.x p.f.info=decide (p.p.headQ=k):=
    congrArg (fun a:MeterQ=>decide (a.headQ=k)) Vessel.Sleigh.Wax.Good.foster
attribute [local irreducible] PrintV.model PrintV.garment Fort.radiate
lemma trunk (X:ℝ)(h:p.f.band p.due p.H p.g.prism (Fort.radiate u.r p.g u.v) X):
     (p.s.home p.x p.i).band p.due p.H p.g.prism p.s.g X:=by
    rw [he.read]; exact Seats.transportD (s:=p.s.home p.x p.i) ⟨_,PrintV.garmentK u.r⟩ he.makes h
abbrev void0(p:Wax u):Cog:= snow (k0 u) p.g.prism
lemma snows : p.f.band p.due p.H p.g.prism (void0 p) 0:=by
    obtain ⟨hx,hp,_,hq⟩:=he.nums
    exact flex (steam _ _ (he.remains he.ready) (show powder 100 ≤ p.plant from hq)) (by omega) hp
                                                                                      (by change p.H ≤ p.H+_; exact Nat.le_add_right ..)
lemma dark (hp:lampY p=false):
     (p.s.home p.x p.i).band p.due p.H p.g.prism p.s.g 0:=by
    apply he.trunk
    unfold Fort.radiate
    have h:=he.shines
    obtain ⟨hx,hq,hz⟩:=he.nums
    rw [hp] at h
    exact Seats.avis (higher h (by omega) hq) (fun _=>he.snows) (fun h=> (h rfl).elim)

end Good
end Wax
end
end Sleigh

end
end ExactDerandomization.Vessel

end

section

namespace ExactDerandomization.Vessel.Sleigh.Wax
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Good

abbrev Approved(p:Wax u)(k:Lyric):Prop:=
   ∃ i,k=base u.r ∨ k=genus p.g ∨ k=fresh u.r p.g u.v∨ k=mixC u.r p.g u.v i
abbrev postX (p:Wax u)(x y j:ℕ)(A:ℝ):Prop :=
      ∃ b m,y=hole b m ∧ u.D.W b +u.D.D p.s.a ≤ u.D.W p.s.a∧
            u.D.Voice b x m (u.D.high b) j A
abbrev moneyX(_:Wax u)(x:ℕ):Coin:=Coin.ofZ (if u.r.P.fin u.x x then 1 else 0)

abbrev tunesF(p:Wax u)(x:ℕ):Lyric → ℝ → Prop:= Chor (k0 u) p.plant p.T (p.s0 x)
abbrev amountP(p:Wax u):ℝ:= massB p.g.prism p.s.d
abbrev pullP (p:Wax u) : ℝ:=p.p.value.v
abbrev middleP(p:Wax u):Cog:=
       pleas (starC 1) (roost (k0 u) (base u.r) p.g.prism)
                                (pleas (starC 2) (roost (k0 u) (genus p.g) p.g.prism) (drill u.r p.g u.v))

namespace Good
variable {p:Wax u} (he:p.Good)
include he
omit he in
lemma spend0(x:ℕ) : (p.s0 x).d=p.s.d:=(Vessel.Basket.Sack.Ground.wages (s := p.s))
lemma abi {v:Lyric} (hc:p.Approved v):
    (reset v p.g.prism).cost p.plant≤p.due ∧(reset v p.g.prism).tail≤ p.due:=by
       rw [he.oath]; obtain ⟨i,h⟩:=hc
       obtain ⟨h1,h2⟩:= (GoodF.estimated p.g u.r u.v).2.2.2 i v h
       exact ⟨h2,h1⟩
lemma bornC {x:ℕ}(hx:x∈u.D.P){f:Lyric}(hc:p.Approved f){A:ℝ}
   (hm:p.tunesF x f A)(hy:|A| ≤ p.amountP):
   (p.s0 x).band p.due p.H p.g.prism (roost (k0 u) f p.g.prism) A:=by
    have hp := he.nums
    have hE:= he.abi hc
    have hr : p.H+(reset f p.g.prism).tail*(p.s0 x).d ≤ p.T:=by
          rw [(Vessel.Sleigh.Wax.Good.spend0 (p := p))]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hE.2) _
    exact Amber.onQ _ f _ (he.remains hx) hm (by omega) hr hE.1 (((Vessel.Sleigh.Wax.Good.spend0 (p := p)) x).symm ▸hy)
lemma crust0 {x j y:ℕ}{g:Sight}{A:ℝ}
     (hx:x∈u.D.P)(h:g.f u.x p.quote0=y)(hp:p.postX x y j A):
   (p.s0 x).band p.plant p.T 0 (Bullet.snap g) (A/(2:ℝ)^j):=by
       obtain ⟨b,m,ht,hb,hv⟩:=hp
       exact Amber.normalizeF he.char.pro g he.nums.2.2.1 hx (h.trans ht) hb hv (he.through hb)
omit he in
lemma power0 : range0 p.g ≤ p.amountP:=by
    refine le_trans (b:=massB p.g.coin p.s.d) ?_ (mass_mono (by unfold MintV.prism;omega) _)
    unfold massB; apply pow_le_pow_right₀ (by norm_num)
    have hh:1≤p.s.d:=gap_pos ..; nlinarith
lemma solvent {x j:ℕ}{g:Sight}{A:ℝ}
   (hx:x∈u.D.P)(h:g.f u.x p.quote0=j)(hp:p.postX x j p.g.coin A):
   p.tunesF x (Amber.shade (Bullet.snap g) p.g.coin (Wear.powerF p.g)) A:=by
        apply Amber.cast (he.remains hx) (he.crust0 hx h hp)
        · simp [powerF,syrup,Health]
        unfold massB
        apply pow_le_pow_right₀ (by norm_num)
        have hh:= he.char.pro.well.1;nlinarith
lemma stamp0 {x:ℕ}(hx:x∈u.D.P)(h:|p.pullP|≤p.amountP) :
   p.tunesF x (chip p.g) p.pullP:=by
     have hp := he.remains hx

     obtain heQ:=Vessel.Sleigh.Wax.Good.foster (p := p)

     change Chor _ _ _ _ _ p.p.value.v
     refine Chor.played hp.st hp.he ?_ ?_
     · intro i hi; change (tea.f u.x p.quote0).value=p.p.value
       rw [heQ]
     rw [(Vessel.Sleigh.Wax.Good.spend0 (p := p))];exact h

lemma boil0 {A:ℝ} (h:lampY p=true)
     (hp:p.f.band p.due p.H p.g.prism (middleP p) A):
    (p.s.home p.x p.i).band p.due p.H p.g.prism p.s.g A:=by
       apply he.trunk
       have hx:=he.shines; rw [h] at hx
       have ht:=he.nums
       exact Seats.avis (higher hx (by omega) ht.2.1) (fun h=>False.elim (by exact Nat.one_ne_zero h)) (fun _=>hp)

omit he in
lemma money_ok (x:ℕ) : |(p.moneyX x).v| ≤ 1:=by
     unfold moneyX;split <;> simp

lemma boonBase (h:p.p.headQ=1) :
    p.f.band p.due p.H p.g.prism (middleP p) (p.moneyX p.x).v:=by
       apply Song.pinTrue (starC 1) (((Vessel.Sleigh.Wax.Good.body0 (p := p)) 1).trans (decide_eq_true h))
       have hh:= he.remains he.ready
       have ht:= Vessel.Sleigh.Wax.Good.money_ok (p := p) p.x
       apply he.bornC he.ready (show Approved p _ from Exists.intro 0 (Or.inl rfl)) ?_
                              (ht.trans (mass1 ..))
       exact Amber.occlude hh _ _ rfl (ht.trans (mass1 ..))

omit he in
lemma headC : (atQ hereId 1).f p.f.l.x p.f.info = hole p.p.hereP (hole 1 0):=
    congrArg (fun a:MeterQ=>hole a.hereP (hole 1 0)) Vessel.Sleigh.Wax.Good.foster
lemma boonEye {A:ℝ}(h:p.p.headQ=2)
   (hx:p.postX p.x (hole p.p.hereP (hole 1 0)) p.g.coin A)
   (hm:|p.pullP| ≤ p.amountP)(hh:|p.pullP*A| ≤ p.amountP):
    p.f.band p.due p.H p.g.prism (middleP p) (p.pullP*A):=by
      have hs:p.p.headQ≠1:=by omega
      apply Song.pinFalse (starC 1) (((Vessel.Sleigh.Wax.Good.body0 (p := p)) 1).trans (decide_eq_false hs))
      apply Song.pinTrue (starC 2) (((Vessel.Sleigh.Wax.Good.body0 (p := p)) 2).trans (decide_eq_true h))
      exact he.bornC he.ready (show Approved p (genus p.g) from ⟨0,Or.inr (Or.inl rfl)⟩)
                         ((he.remains he.ready).mult0 (he.stamp0 he.ready hm) (he.solvent he.ready (Vessel.Sleigh.Wax.Good.headC (p := p)) hx)) hh
end Good

end
end ExactDerandomization.Vessel.Sleigh.Wax

end

section

namespace ExactDerandomization.Vessel.Basket.Sack.Ground
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring Sun
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
variable {s:Sack u}(hg:s.Ground)
include hg

omit hg in
lemma smoke (x:ℕ)(j:ℕ):trigger.f u.x (s.home x j).info=decide (s.i=0):=by
   change decide ((dec (Reed.V _ _).1:Crt).2.1.2=0)=_
   rw [Vessel.Basket.Sack.Ground.phase0,Vessel.Basket.Sack.Ground.deco0]
omit hg in
lemma choir0 {i:ℕ}(h:s.i=i+1)(x j:ℕ):
    crystal.f u.x (s.home x j).info=hole (s.v.channel 5 i) (hole 1 0):=by
   change hole (Blade.Crest.pastC (dec (Reed.V _ _).1) 5) _=_
   rw [Vessel.Basket.Sack.Ground.phase0,Vessel.Basket.Sack.Ground.deco0]
   have hm:Blade.Crest.pastC (s.v.c s.i) 5=s.v.channel 5 i:=by
      unfold Blade.Crest.pastC; refine congrArg enc (Prod.ext rfl (Prod.ext ?_ rfl))
      refine Prod.ext rfl ?_; change s.i-1=i;omega
   rw [hm]

lemma waitsage {x:ℕ} (hx:x∈u.D.P)(h:s.priorE x) :
   let t:=s.k; let f:=s.home x 0
   f.band s.c s.τ (prior t) (velvet (I u) t) (s.v.actual t x s.i):=by
   intro t f
   have hp0:= hg.pro; have hR:=hg.hc
   have hp:=hg.guest hx 0
   by_cases he:s.i=0
   · apply Song.pinTrue Sun.trigger ((Vessel.Basket.Sack.Ground.smoke (s := s) x 0).trans (decide_eq_true he))
     rw [show s.v.actual t x s.i=0 from ?_]
     · exact steam _ _ hp hg.pawl.1
     rw [he]
   obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero he
   let q:=s.v.channel 5 j
   have hb:u.D.D q=2*(u.D.D s.a):=by
      change u.D.D (s.v.channel 5 j)=2*u.D.D (s.v.channel 5 s.i)
      rw [Vessel.OrbitV.Counsel.heightZ,Vessel.OrbitV.Counsel.heightZ,hj]
      exact gap_step (by have :=hg.hk; omega)
   have hc:u.D.W q+u.D.D s.a ≤ u.D.W s.a:=by
      change u.D.W _+u.D.D (s.v.channel 5 s.i)≤ u.D.W (s.v.channel 5 s.i)
      unfold q; rw [Vessel.OrbitV.Counsel.heightZ,Vessel.OrbitV.Counsel.costZ,Vessel.OrbitV.Counsel.costZ,hj]
      exact Age.oldpay (by have :=hg.hk; omega) (by decide) (by decide)
   apply Song.pinFalse Sun.trigger ((Vessel.Basket.Sack.Ground.smoke (s := s) x 0).trans (decide_eq_false he))
   have ht : s.τ ≤ u.D.high q:=by
      unfold Sack.τ; rw [←(Vessel.Basket.Sack.Ground.wages (s := s))]
      exact Studio.soonerC hp0 hc hg.pay le_rfl
   apply Bullet.clef u.D hp0 hg.pawl.2.2 hx hc ((Vessel.Basket.Sack.Ground.choir0 (s := s)) hj x 0) ht
   have hS := (h j hj).untilX
   change u.D.Voice q x (hole 1 0) _ _ _ at hS
   have hv:s.v.actual t x s.i=s.v.actual t x (j+1):=by rw [hj]
   have hh:t.sealR * u.D.D q=prior t* u.D.D s.a:=by rw [hb]; unfold prior;ring
   rw [hv,←hh]; exact hS

lemma aware {x:ℕ}(hx:x∈u.D.P)(i j):
    Lu.Standard (film (s.urn x) i j) (campk (I u)) s.τ:=by
   have hk:= Studio.stayedC hg.pro le_rfl hg.pay
   rw [(Vessel.Basket.Sack.Ground.wages (s := s))] at hk
   exact ⟨Studio.positioned hg.pro hx i j,spanFilm (Studio.vital _ hk) i j⟩

lemma surfaces {x:ℕ}(hx:x∈u.D.P):
    let k:=appear (I u) s.k
    k.n.f u.x (s.home x 0).info=s.Pn:=by
   intro k; have he:= stable_home (hg.guest hx 0).st
   let d:=(s.home x 0).d
   change (((campk (I u)).bank.f u.x (s.home x 0).info)^s.k.vol)=_
   rw [show (campk (I u)).bank.f u.x (s.home x 0).info = 2^d from he.2.2,←pow_mul,show d=s.d from (Vessel.Basket.Sack.Ground.wages (s := s)), mul_comm];rfl
lemma housing {x:ℕ}(hx:x∈u.D.P){g:ℕ→ℝ}(hf:harvest s x g) :
   let i:=s.c
   let v:=s.home x 0
   let k:=appear (I u) s.k
   Chor (campk (I u)) i s.τ v (.heap true k (sail s.k s.g)) (s.v.chipV x s.i):=by
   intro i v k
   have hs:v.freq k=range s.Pn:=congrArg range (hg.surfaces hx)
   have hp:= hg.guest hx 0
   rw [←hf.matchesV,←hs]; refine Lyric.Chor.little hp.st ?_ ?_
   · rw [show k.n.f v.l.x v.info=s.Pn from hg.surfaces hx,show v.d=s.d from (Vessel.Basket.Sack.Ground.wages (s := s))]
     apply Nat.pow_lt_pow_right (by omega);change s.k.vol*s.d<(s.k.vol+1)*s.d
     have hc:=gap_pos s.v.m s.i; change 0<s.d at hc; nlinarith
   intro i hi
   have ht : v.bench k i=s.home x i:=by simp [k,v,home,Studio.stk,bench,film, panelx,appear,Branch.port,stairs]
   rw [ht]; rw [hs] at hi; exact .byear (hf.limb i (mem_range.1 hi))

omit hg in
lemma total {x:ℕ}(_:x∈u.D.P){g:ℕ→ℝ}(hf:harvest s x g) :
    |s.v.chipV x s.i|  ≤ massB s.k.tokenH s.d:=by
   rw [←hf.matchesV]
   apply le_trans (abs_sum_le_sum_abs g _)
   apply le_trans (b:=∑ i∈ range s.Pn,massB s.k.prism s.d)
   · apply sum_le_sum
     intro i hi; have hh:= Seats.maxv (hf.limb i (mem_range.1 hi)); change |g i| ≤ massB s.k.prism (u.D.D s.a) at hh
     rwa [(Vessel.Basket.Sack.Ground.wages (s := s))] at hh
   simp only [sum_const,card_range,nsmul_eq_mul]
   rw [mass_mul]
   refine le_of_eq ?_; congr 1; simp [Pn,MintV.rangeN,massB]

lemma console {x:ℕ}(hx:x∈u.D.P)(h:s.priorE x){g:ℕ→ℝ}(hf:harvest s x g):
    let _:=s.a; let v:=s.home x 0; let T:=s.k.sealR
    v.band s.wallet (s.h0) T (pasty s.k (I u) s.g) (s.v.actual s.k x (s.i+1)):=by
   intro a v T
   have hb:= Script.estimate u.r (I u) s.k s.g s.c
   let f:=chest (I u) s.k s.g
   let y:=s.v.actual s.k x (s.i+1)
   let k:=campk (I u)
   have ht:= hg.guest hx 0
   have hl:|y|  ≤  massB T v.d:=by rw [show v.d=s.d from (Vessel.Basket.Sack.Ground.wages (s := s))]; exact s.v.pays ..
   have hm:Chor k s.c s.τ v f y:=by
      unfold f chest; dsimp only; unfold y
      rw [OrbitV.actual,MintV.shore, ← show v.d=gap s.v.m s.i from (Vessel.Basket.Sack.Ground.wages (s := s))]
      apply ht.clips _ (ht.additions (Chor.byear (hg.waitsage hx h)) (hg.housing hx hf))
      let C:= scaleC k T v.l.x v.info
      have hc:C.v = massB T v.d:=scalen (stable_home ht.st) T
      rw [show s.k.roofX v.d = C.v from hc.symm]
      apply Chor.played ht.st ht.he (fun x _=>rfl)
      rw [hc,abs_of_pos (mass0 ..)]
   apply Amber.onQ k f T ht hm (show 1≤ s.c from by have:=hg.pawl;omega) ?_ hb.2.1 hl
   rw [show v.d=s.d from (Vessel.Basket.Sack.Ground.wages (s := s))]; exact Nat.add_le_add_left (Nat.mul_le_mul_right s.d hb.2.2) _

omit hg in
lemma pastlore {x}(h:s.priorE x): s.v.VoteM s.k x s.i :=by
    by_cases hz:s.i=0; intro j hj;omega
    obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero hz
    rw [hj]; exact (h j hj).plan
lemma advances {x:ℕ}(hx:x∈u.D.P)(h:s.priorE x){g:ℕ→ℝ}(hf:harvest s x g):s.v.Earn s.k s.i x:=by
    constructor
    · intro i hi; by_cases ht:s.i=i; rw [←ht]; exact (Vessel.Basket.Sack.Ground.total (s := s)) hx hf
      exact Vessel.Basket.Sack.Ground.pastlore h i (by omega)
    have hs:= hg.console hx h hf
    have he :s.c ≤ s.wallet:= (Script.estimate u.r (I u) s.k s.g s.c).1
    have hx0:u.smallQ s.a 0:=by
       change lb 0 ≤ u.eye.e*u.D.D s.a
       have hc:1 ≤ u.eye.e:=by have hk:=hg.hc.till.cost0; change _ ≤ u.eye.e at hk; unfold Bank.hx Bank.hu Bank.hi at hk; omega
       have hV:=hg.pro.well.1
       rw [lb_zero]; nlinarith
    exact Studio.scoreTicket hg.pro (by omega:(1:ℕ) ≤ 1) (by omega) hx0 (by have:=hg.pawl;omega)
                   hg.pay le_rfl hs hg.cargo

end
end ExactDerandomization.Vessel.Basket.Sack.Ground

end

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack
namespace Ferry
open Sleigh Gamut

variable (s:Sack u)
abbrev core0:=s.v.c s.i
abbrev valid0(j:Seed):Prop:=PlanV.validV u.w0 (core0 s) j
abbrev blanket(j:Seed):=PrintV.model u.r u.x (core0 s) j
abbrev flareP(x:ℕ)(p:Seed):Wax u:=⟨s,x,enc p,blanket s p⟩
abbrev phantom(x j:ℕ):Wax u:=⟨s,x,j,PrintV.black⟩
abbrev AE:= (u.plotM.stage s.v.p.i).S
abbrev W0(C:History) := PrintV.topHull u.r u.x (core0 s) C
abbrev heats (x:ℕ)(c:History)(b:Bool):Bool:=Print.touched b u.n s.v.p.u 0 x c.1 c.2 (Print.issued s.v.dye)
abbrev Wlive (x:ℕ)(p:History):Bool:=Env.live s.v.p.u 0 (↑x) (↑x) (w:=0) (d:=0) le_rfl
                             (Print.queue p.1 p.2).1 (Print.queue p.1 p.2).2 s.v.dye
structure TorchE:Prop where
     may :s.Ground
     oath:s.c=GoodF.treasury s.k u.r
     aid:s.wallet+s.c ≤  u.v.slope
     read:s.g=PrintV.shell u.r s.k u.v

structure Wells :Prop where
     he : TorchE s
     eraR :∀ v:OrbitV u,v.estate → v.m+s.d ≤ s.v.m → v.FEnd
     thenP :∀ v:Fabric u,v.Good→ v.m+s.d ≤ s.v.m → (∃f,v.Efine s.k f)
     shoreP :∀ v:Fabric u,v.Good→ v.m+s.d ≤ s.v.m → v.t.main=true →
                                   (∃ k,v.t.tag=.score k) → Gamut.Pond.TracedE s.k v
namespace TorchE
variable {s}(he:TorchE s)
include he
lemma vfen :u.Chart:=he.may.hc.hp
omit he in
lemma hou0 :W0 s p= ((Aqua.tally u.r u.x s.v.p.i,s.v.p.u,0),p,Print.issued s.v.dye):=by
   unfold W0 PrintV.topHull; congr 1
   change (p,(dec (enc _)))=_; rw [dec_round]
lemma Qyet {p:MeterQ}{c:History} (h:p.h0=W0 s c)(x:ℕ):
  (surf p).frontC u.n x=true ↔ x∈s.v.S∧heats s x c true=true:=by
    let t:=surf p
    have hh:t.1=W0 s c:=h
    change t.frontC u.n x=_↔_
    unfold Surf.frontC Surf.flareQ Surf.heatC Surf.green Surf.chartQ Surf.days Surf.dye Surf.mx
    have hp:=he.may.hc.he.2.1
    rw [hh,Vessel.Ferry.TorchE.hou0]; dsimp only
    simp only [Bool.and_eq_true,decide_eq_true_eq,← mem_range,Aqua.room he.vfen hp]
    simp only [ite_true,Print.issued,Print.shoots]
    change x∈AE s ∧ hit s.v.p.u (x:ZMod u.n) s.v.dye.1 ∧ _ = true ↔ x∈s.v.S∧ _
    rw [OrbitV.S]; unfold src retain; rw [mem_filter]
    exact (and_assoc ..).symm
omit he in
lemma Qend {p:MeterQ}{c:History} (h:p.h0=W0 s c)(x:ℕ):
    (surf p).finalC u.n x=true ↔heats s x c false=true:=by
    let t:=surf p
    have hh:t.1=W0 s c:=h
    have hf:t.windC x=x:=by
         change 1*x+0=_;omega
    change t.finalC u.n x=_ ↔_
    unfold Surf.finalC; rw [hf]
    unfold Surf.flareQ Surf.heatC Surf.green Surf.chartQ Surf.days Surf.dye
    rw [hh,Vessel.Ferry.TorchE.hou0];dsimp only
    simp only [Bool.and_eq_true]
    simp only [Bool.false_eq_true,ite_false, Print.issued,Print.shoots,allhit,true_and]; rfl
lemma lampq {p:MeterQ}{c:History}(h:p.h0=W0 s c)(x:ℕ):
    Fort.light u.n u.w0.p.M x p=true ↔
             0<p.headQ ∧ (p.headQ<3∨ x%u.w0.p.M=p.i) ∧ x∈s.v.S ∧ Wlive s x c=true:=by
    unfold Fort.light; simp only [Bool.and_eq_true,decide_eq_true_eq,he.Qyet h,(Vessel.Ferry.TorchE.Qend (s := s)) h]
    rw [show Wlive s x c=true ↔ heats s x c true=true∧ heats s x c false=true from Print.exactHit ..]
    tauto
omit he in
lemma parked(x:ℕ): Wlive s x (0,0)=true:=by
    have hh(b) :heats s x (0,0) b=true:=by unfold heats; unfold Print.touched; rw [Print.flowed];rfl
    exact (Print.exactHit ..).2 ⟨hh true,hh false⟩
lemma fitted {x:ℕ}(hx:x∈u.D.P)(p:Seed)(hp:valid0 s p):(flareP s x p).Good:=by
    refine ⟨he.may,hx,he.read,he.oath,he.aid,?_⟩
    unfold PrintV.garment
    dsimp only; rw [Vessel.Basket.Sack.Ground.phase0]; dsimp only
    rw [Wire.eq,Vessel.Basket.Sack.Ground.deco0,ite_eq_left (show enc p=enc p ∧ PlanV.validV u.w0 _ p from ⟨rfl,hp⟩)]
lemma else0 {x j:ℕ}(hx:x∈u.D.P)
     (hp:¬(enc (dec j:Seed)=j ∧valid0 s (dec j))):(phantom s x j).Good:=by
    refine ⟨he.may,hx,he.read,he.oath,he.aid,?_⟩
    unfold PrintV.garment
    dsimp only; rw [Vessel.Basket.Sack.Ground.phase0];dsimp only
    rw [Vessel.Basket.Sack.Ground.deco0,ite_eq_right hp]
omit he in
lemma tabs0 (p:Wax u)(hp:p.Good)(hr:p.p=PrintV.black):
     (p.s.home p.x p.i).band p.due p.H p.g.prism p.s.g 0:=by
    apply hp.dark
    unfold Wax.Good.lampY Fort.light; rw [hr]
    change (decide (0<(0:ℕ)∧_)&& _ && _)=false;simp
end TorchE

structure ArcQ (s:Sack u) where
     r:Census.Arc
namespace ArcQ
variable {s:Sack u}
variable (p:ArcQ s)
abbrev k:=s.v.p
abbrev φ:=Census.drops s.v.tire true p.r
abbrev bx:= (p.φ.tick u.w0,p.φ.event)
abbrev cur(i:ℕ):Seed:= Seed.along p.φ i 0
abbrev forward:ℕ:= p.φ.budget s.v.m
abbrev α:=RowD.startF u.r u.x (core0 s) p.φ
def routeP : Pool u.n:=Env.go s.v.ds.u s.v.ds.a (d:=0) (w:=0) le_rfl
                                  (Print.queue p.bx.1 p.bx.2).1 (Print.queue p.bx.1 p.bx.2).2 s.v.dye
abbrev bill0:= Census.h s.v.tire p.r.2.1
abbrev intended(x:ℕ):ℝ:= if x∈s.v.S then Census.wind s.v.tire s.v.s s.v.ds s.v.dye x x p.r else 0
abbrev okQ(x:ℕ):Prop:= x∈s.v.S∧Wlive s x p.bx=true
abbrev hullK:= W0 s p.bx

structure Hand (p:ArcQ s):Prop where
     pools: Wells s
     aligned : p.r∈s.v.areaV s.i
namespace Hand
variable {p:ArcQ s}(h0:Hand p)
include h0
lemma zone : p.φ.habitat u.w0 s.v.p.i s.v.m s.i s.v.s.rays∧ p.φ.ray s.v.p.i=p.r.1∧
      p.φ.slackM s.v.m=p.r.2.1:= Census.grange s.v.tire rfl _ h0.aligned
lemma price0 : p.r.1∈s.v.s.rays∧ p.r.2.1∈s.v.tire.layers p.r.1.1 s.i ∧ p.r.2.2.2< Print.rad^p.bill0:=
    (Census.pat ..).1 h0.aligned
lemma cost0 : s.d ≤ p.φ.sig∧ s.v.tire.cut p.r.1.1 ≤p.φ.sig∧ p.φ.sig < 2*s.d:=by
    have hk:=h0.pools.he.may.hk; have ht:=h0.price0.2.1
    exact ⟨(s.v.tire.full ht hk).1,(s.v.tire.cheap (mem_Ico.1 ht).2).2.1,(s.v.tire.full ht hk).2⟩
lemma swift : p.forward+s.d ≤ s.v.m:=by
    let i:=p.r.2.1
    have hs:i+1<s.v.m:= (s.v.tire.cheap (mem_Ico.1 h0.price0.2.1).2).2.2
    have hf:p.φ.sig=s.v.m-(i+1):=rfl
    have hp:=h0.cost0
    unfold forward Fog.budget; rw [show p.φ.slackM s.v.m=i from h0.zone.2.2]
    split <;>omega
lemma ll0:p.forward<s.v.m:=by have :=h0.swift;have ho: 0<s.d:=gap_pos ..;omega
lemma sigmas:p.φ.tick u.w0 ≤ u.w0.ell*u.limitM:=by
   let y:=p.r.2.1
   have hs : p.φ.sig=s.v.m-(y+1):=rfl
   have hp:=h0.pools.he.may.hc.he.1
   unfold Fog.tick; rw [hs];gcongr;omega
lemma stanza : p.α.v=(if p.r.2.2.1 then 1 else -1)* Env.weight^p.bill0:=by
   have hv:=WindY.rains u.r u.x h0.sigmas
   unfold α RowD.startF
   change (if p.r.2.2.1 then WindY.shower u.r u.x (p.φ.tick u.w0) else _).v=_
   cases he:p.r.2.2.1
   · simp only [Bool.false_eq_true,ite_false,Coin.neg0,hv];rw [neg_one_mul]; rfl
   simp only [ite_true,hv];rw [one_mul];rfl
lemma chaste : |p.α.v| ≤ 1 :=by
   rw [h0.stanza,abs_mul]
   simp only [abs_of_nonneg (WindY.careful p.bill0).1]
   split <;> simpa only [abs_one,abs_neg,one_mul] using (WindY.careful p.bill0).2
lemma voice0(x:ℕ):
   p.intended x= if p.okQ x then p.α.v* (s.v.s.lines p.r.1).seq p.forward p.routeP x x else 0:=by
   have hu: p.forward=(if p.r.2.2.1 then p.r.2.1+1 else p.r.2.1):=by
       unfold forward Fog.budget
       rw [show p.φ.slackM s.v.m=p.r.2.1 from h0.zone.2.2];rfl
   unfold intended Census.wind okQ;rw [h0.stanza];rw [hu]
   dsimp only
   split
   · next hx=> simp only [hx,true_and];rfl
   next hx=> rw [ite_eq_right (fun h=>hx h.1)]
lemma steam0 {x:ℕ}(hx:x∈u.D.P){i:ℕ}(hi:i<u.w0.p.K): (flareP s x (p.cur i)).Good :=
      h0.pools.he.fitted hx _ (Or.inr (s.v.awakeV h0.aligned _ hi))
end Hand
end ArcQ
end Ferry

end
end ExactDerandomization.Vessel

end

section

namespace ExactDerandomization.Vessel.Ferry.ArcQ
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Sleigh Gamut
variable {s:Sack u}

abbrev K(_:Sack u):ℕ:=u.w0.p.K
abbrev M(_:Sack u):ℕ:=u.w0.p.M
abbrev palette(p:ArcQ s)(x i:ℕ):Wax u:=flareP s x (p.cur i)
abbrev amber(_:ArcQ s):Peek:=s.v.p
abbrev pores(p:ArcQ s)(k:ℕ):Fabric u:=⟨Peek.score p.amber.i k,p.forward,crossP p.routeP⟩
abbrev horn(p:ArcQ s)(k:ℕ):MeterQ:=
     PrintV.detectors p.hullK s.v.p.i k p.forward (Print.issued p.routeP) p.α

structure VisitF(p:ArcQ s)(x:ℕ)(f:ℕ → ℝ):Prop where
     union0:∑ i∈range (K s),f i=p.intended x
     has0: ∀ i<K s,let a:=p.palette x i; (a.s.home a.x a.i).band a.due a.H a.g.prism a.s.g (f i)
abbrev prickF(p:ArcQ s)(x:ℕ)(i:ℕ):ℝ:=if i=0 then p.intended x else 0
namespace Hand
variable {p:ArcQ s}(hp:p.Hand)
include hp
omit hp in
lemma united0(x:ℕ):∑ i∈range (K s),p.prickF x i=p.intended x:=by
    unfold prickF
    have hh:0<K s:= Fen.Kpos ..
    simp [hh]

lemma signalF {a:Fabric u}(h:a.m=p.forward)(i j:ℕ): u.D.W (a.c i j)+u.D.D s.a ≤ u.D.W s.a:=by
   apply (Vessel.OrbitV.Counsel.foreign (v := s.v)) a ?_ _ _
   rw [h]; exact hp.swift
lemma deserted {a:OrbitV u}(h:a.m=p.forward)(i j:ℕ): u.D.W (a.channel i j)+u.D.D s.a ≤ u.D.W s.a:=by
   rw [show u.D.W (a.channel i j)=Age.weight a.m i j from u.rolfe ..]
   change _+u.D.D (s.v.channel 5 s.i) ≤ u.D.W (s.v.channel 5 s.i)
   have hk:= hp.pools.he.may.hc
   rw [Vessel.OrbitV.Counsel.costZ,Vessel.OrbitV.Counsel.heightZ,h]; exact Age.renewal hp.swift
lemma aged :p.forward  ≤  u.limitM:= hp.ll0.le.trans hp.pools.he.may.hc.he.1
lemma reading(k:ℕ)(h:s.v.p.ask=some k):
     s.v.p.i=s.v.p.u∧k<u.w0.p.T:=by
    have hx:= hp.pools.he.may.hc.he.2.2.2.2; rw [h] at hx; exact hx
lemma poresReady (k:ℕ)(h:s.v.p.ask=some k):(p.pores k).Good:=by
    obtain ⟨hj,hp1,h2,hR⟩:= hp.pools.he.may.hc.he.2
    obtain ⟨hz,hg⟩:=hp.reading k h
    have he : s.v.p.i+p.forward ≤ u.plotM.roof :=by have H:=hp.ll0; omega
    exact ⟨hp.aged,hj,le_rfl,le_rfl,he,he,rfl,hg⟩

omit hp in
lemma step0 :
    Print.stepout u.n s.v.p.u 0 p.bx.1 p.bx.2 (dec (Age.env (core0 s)))=Print.issued p.routeP:=by
    have hz:(dec (Age.env (core0 s)):Issue)=Print.issued s.v.dye:=dec_round ..
    rw [hz,Print.unpacked];rfl
omit hp in
lemma red0(k:ℕ)(h:s.v.p.ask=some k)(i x:ℕ):
    (p.palette x i).p= if i=0 then p.horn k else PrintV.black:=by
    let r:= core0 s
    change PrintV.model u.r u.x r (p.cur i)=_
    have hf:Garden.origin r=6 ∧ PlanV.j r=k:= by
           simp [PlanV.j,Garden.origin,r,core0,OrbitV.c,Foil.kit,bitV,Garden.fence,h]
    have ha:PlanV.x r=s.v.p.i:=rfl
    unfold PrintV.model; dsimp only
    rw [ite_eq_right (show (p.cur i).1.1≠1 from by change (2:ℕ)≠1; omega),ite_eq_left hf.1,hf.2]
    rw [show Garden.params r |>.2.1=s.v.p.u from rfl, show Garden.m r=s.v.m from rfl]
    have hz:=Vessel.Ferry.ArcQ.Hand.step0 (p := p)
    split
    · next hz0=>
        change i=0 at hz0
        rw [ite_eq_left hz0]
        exact congrArg (fun x=>PrintV.detectors p.hullK s.v.p.i k p.forward x p.α) hz
    next hh=>
    change i≠0 at hh
    rw [ite_eq_right hh]

lemma cuvette (k:ℕ) (h:s.v.p.ask=some k)(x:ℕ):
     p.intended x= if p.okQ x then p.α.v* Pond.rankE (p.pores k) x else 0:=by
    rw [hp.voice0]
    have hh:s.v.r p.forward=forecast u.plotM p.forward:=vault _ _ hp.ll0
    have hE:=hp.reading k h
    let g:= p.pores k; let v:=g.finalE
    split <;> try rfl
    congr 1
    unfold OrbitV.s Peek.weave
    rw [h]
    change ridge (Axis.spout s.v.d ((s.v.r p.forward).outR (Peek.score s.v.p.i k))
                  u.w0.p.J p.routeP) x x=_
    rw [ridge,ite_eq_left rfl]
    unfold Axis.spout
    rw [hh]
    change rank (src s.v.d.S s.v.p.u (crossP p.routeP)) (fun i=>v i x) _=_
    change _=rank (src s.v.d.S s.v.p.i (crossP p.routeP)) (fun i=>v i x) _
    rw [hE.1]

lemma hearC (k:ℕ)(h:s.v.p.ask=some k){x:ℕ}(hx:x∈u.D.P):
   let a:= p.palette x 0
   a.postX x (hole a.p.hereP (hole 1 0)) a.g.coin (Pond.rankE (p.pores k) x):=by
    intro a
    let g:=p.pores k; let b:=g.c 16 0
    have hh:=hp.pools.shoreP g (hp.poresReady k h) hp.swift rfl ⟨k,rfl⟩
    refine ⟨b,hole 1 0,?_,hp.signalF (a:=g) rfl 16 0,hh x hx⟩
    rw [show a.p=p.horn k from ((Vessel.Ferry.ArcQ.Hand.red0 (p := p)) k h ..).trans (ite_eq_left rfl)]; rfl
omit hp in
lemma heightB {p:Wax u} {x y j:ℕ}{A:ℝ}(hx:p.postX x y j A):|A| ≤  (2:ℝ)^j:=by
    obtain ⟨i,k,hh,hz,w,hW,hr⟩:=hx
    have ht:=hW.1; rwa [abs_div,abs_of_pos (show 0<(2:ℝ)^j by positivity),div_le_one (show 0<(2:ℝ)^j by positivity)] at ht

lemma marsD (k:ℕ)(h:s.v.p.ask=some k){x:ℕ}(hx:x∈u.D.P):
   let a:= p.palette x 0
   (a.s.home a.x a.i).band a.due a.H a.g.prism a.s.g (p.intended x):=by
    intro a
    have hc:a.Good:= hp.steam0 hx (Fen.Kpos ..)
    have he:(p.palette x 0).p=p.horn k:=((Vessel.Ferry.ArcQ.Hand.red0 (p := p)) k h ..).trans (ite_eq_left rfl)
    have hQ:a.p.h0=p.hullK:=congrArg MeterQ.h0 he
    have hk:a.p.headQ=2:=congrArg MeterQ.headQ he
    have hv:a.pullP=p.α.v:=congrArg (fun a:MeterQ=>a.value.v) he
    have hl: Wax.Good.lampY a=true ↔ p.okQ x:=by
       have hp0:=hp.pools.he.lampq hQ x
       change Fort.light _ _ x a.p=true↔_; rw [hp0,hk]; unfold okQ;grind
    have hh:= hp.cuvette k h x
    by_cases hb:p.okQ x
    · rw [hh,ite_eq_left hb,←hv]
      have hx1:=hp.hearC k h hx
      apply hc.boil0 (hl.mpr hb)
      have hr:|a.pullP| ≤ 1:= hv ▸ hp.chaste
      exact hc.boonEye hk hx1 (hr.trans (mass1 ..)) ((abs_mul ..).le.trans ((mul_le_mul_of_nonneg_right hr (abs_nonneg _)).trans
                         ((one_mul _).le.trans ((Vessel.Ferry.ArcQ.Hand.heightB hx1).trans Vessel.Sleigh.Wax.Good.power0))))
    rw [hh,ite_eq_right hb]
    exact hc.dark (Bool.eq_false_iff.mpr (fun h=> hb (hl.1 h)))

lemma voyage (k:ℕ)(h:s.v.p.ask=some k){x:ℕ}(hx:x∈u.D.P) :
     VisitF p x (p.prickF x) := by
    refine ⟨Vessel.Ferry.ArcQ.Hand.united0 x,fun i hi=>?_⟩
    unfold prickF
    by_cases ht:i=0
    · subst i; rw [ite_eq_left rfl]; exact hp.marsD k h hx
    rw [ite_eq_right ht]
    exact Vessel.Ferry.TorchE.tabs0 _ (hp.steam0 hx hi) (((Vessel.Ferry.ArcQ.Hand.red0 (p := p)) k h i x).trans (ite_eq_right ht))
end Hand
end
end ExactDerandomization.Vessel.Ferry.ArcQ

end

section

namespace ExactDerandomization.Vessel.Sleigh.Wax
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats Arena.Pier
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Good

abbrev midOld(p:Wax u)(x:ℕ):ℕ:= (Fort.priorF x).f u.x p.quote0
abbrev trace0(p:Wax u)(x _:ℕ)(b:Cog)(z:ℕ):Prop:=
    ∃ q m:ℕ,u.D.W q+u.D.D p.s.a ≤ u.D.W p.s.a∧
       u.D.swears (bell q m 0) x z ∧ ∃ f:Sight, b=Bullet.snap f∧ f.f u.x p.quote0=hole q m
abbrev prismV(_:Wax u)(r:ℕ→ℝ) := boost (Rime.Nest.Good.maxs r u.w0.p.T)
def carrierV(p:Wax u)(x:ℕ)(z:ℕ→ℝ)(k:ℕ):Prop:=
     (∀ i<k,p.p.ago≠0→p.postX x (midOld p i) 0 (z i))∧
                       (p.p.ago=0→∀ i<k,z i=1)
abbrev recordP (p:Wax u) (x:ℕ)(z:ℝ):=p.postX x (hole p.p.hereP (hole 1 0)) 0 z
abbrev scoreP (p:Wax u)(o:ℕ):ℕ:=hole p.p.pt.1 (hole o p.p.pt.2)
abbrev spriteV(p:Wax u)(k:ℕ): Cog :=
         if k=0 then void0 p else roost (k0 u) (mixC u.r p.g u.v k) p.g.prism
structure EscortV (p:Wax u)(x y:ℕ)(f:Kiwi):Prop where
    path : let A:=f.f u.x p.quote0
           Liaison u.D x p.s.a A.1 A.2 ∧ u.D.curve A.1 A.2 true x=some y
structure PayV (p:Wax u)(x k:ℕ) :Prop where
    receipt :trace0 p x k (leave 0) k
    major :k ≤ clim u.w0.p

namespace Good
variable {p:Wax u} (he:p.Good)
include he
omit he in
lemma ancient :
   upQ.f u.x p.quote0=p.p.ago:=congrArg MeterQ.ago Vessel.Sleigh.Wax.Good.foster
omit he in
lemma whatV (b): (stampF b).f u.x p.quote0=p.scoreP b :=by
    exact congrArg (fun a:MeterQ=>hole a.pt.1 (hole b a.pt.2)) Vessel.Sleigh.Wax.Good.foster
lemma springs {x:ℕ}(hx:x∈u.D.P):
    (p.s0 x).band p.plant p.T 0 (choir (k0 u) (.solo 0 (⟨_,Kn.fix (Coin.ofZ 1)⟩))) 1:=by
   have hr:= he.remains hx
   have hh : |(Coin.ofZ 1).v| ≤ massB 0 ((p.s0 x).d):=by simp [massB]
   have hp:Chor (k0 u) 1 p.T (p.s0 x) (.solo 0 ⟨_,Kn.fix (Coin.ofZ 1)⟩) ((Coin.ofZ 1).v):=
             Chor.played hr.st hr.he (fun _ _=>rfl) hh
   rw [show (Coin.ofZ 1).v=1 by simp] at hp
   exact flex (sing hp (by omega) (by simp [tail]))
                (cost_hi (p:=.solo _ ⟨_,Kn.fix (Coin.ofZ 1)⟩) (by omega:1 ≤ 1)) he.nums.2.2.2 le_rfl

lemma beforeC {x:ℕ}(hx:x∈u.D.P) (z:ℕ→ℝ)(k:ℕ)(hp:p.carrierV x z k):
    p.tunesF x (bootsY (k0 u) k) (Rime.Nest.Good.maxs z k) :=by
       have hf:=he.remains hx
       induction k with
       | zero=> exact hf.sil
       | succ k ih=>
           apply hf.up0 (ih ⟨fun i hi=>hp.1 _ (by omega),fun he i hi=>hp.2 he _ (by omega)⟩)
           apply Chor.byear
           by_cases hc:p.p.ago=0
           · apply Song.pinTrue (Wear.falls upQ)
             · change decide (upQ.f u.x p.quote0=0)=true
               rw [(Vessel.Sleigh.Wax.Good.ancient (p := p)),hc]; rfl
             rw [hp.2 hc _ (by omega)]
             exact he.springs hx
           apply Song.pinFalse (Wear.falls upQ)
           · change decide (upQ.f u.x p.quote0=0)=false
             rw [(Vessel.Sleigh.Wax.Good.ancient (p := p))]; exact decide_eq_false hc
           have hm := hp.1 _ (show k<k+1 from by omega) hc
           have hs := he.crust0 (g:=priorF k) hx rfl hm
           simpa only [pow_zero,div_one] using hs

lemma dominion {x:ℕ}(hx:x∈u.D.P)(z:ℕ → ℝ)(h:p.carrierV x z u.w0.p.T):
    p.tunesF x (Fort.actorP u.r u.v) (prismV p z):=
   Arena.Song.Paint.boosted (he.remains hx) (he.beforeC hx z _ h)

lemma influx {x:ℕ}(hx:x∈u.D.P) {A:ℝ}(h:p.recordP x A):
   (p.s0 x).band p.plant p.T 0 Fort.presentQ A:=by
       have hm:=he.crust0 hx (Vessel.Sleigh.Wax.Good.headC (p := p)) h
       simpa only [pow_zero,div_one] using hm

lemma oldera {x:ℕ}(hx:x∈u.D.P)(z:ℕ→ℝ)(h:p.carrierV x z u.w0.p.T)
   (hs:|p.pullP| ≤ p.amountP):
     p.tunesF x (times (chip p.g) (actorP u.r u.v)) (p.pullP*prismV p z) :=
          (he.remains hx).mult0 (he.stamp0 hx hs) (he.dominion hx z h)

lemma freshC {x:ℕ}(hx:x∈u.D.P)(z:ℕ→ℝ)(h:p.carrierV x z u.w0.p.T)
   {A:ℝ}(hf:p.recordP x A)(hs:|p.pullP| ≤ p.amountP)
   (hh:|p.pullP*prismV p z*A|≤p.amountP):
   (p.s0 x).band p.due p.H p.g.prism (roost (k0 u) (fresh u.r p.g u.v) p.g.prism)
             (p.pullP*prismV p z*A):=
   he.bornC hx (show p.Approved _ from ⟨0,Or.inr (Or.inr (Or.inl rfl))⟩)
              ((he.remains hx).mult0 (he.oldera hx z h hs) (Chor.byear (he.influx hx hf))) hh

lemma already {x y:ℕ}{f:Kiwi}(hx:EscortV p x y f):y∈u.D.P:=by
   have hm:=he.nums
   exact (Pier.street hx.path.1 hx.path.2).xem
lemma crafts {x y k:ℕ}(hz:EscortV p x y (Fort.secondC k)) {A:ℝ}(h:p.recordP y A):
    p.tunesF x (.use 0 (Pier.escort u.D.s (Fort.secondC k) presentQ)) A :=
         .byear (Pier.bowls he.char.pro he.nums.1 hz.path.1 he.nums.2.2.1 rfl hz.path.2 _
                                  (he.influx (he.already hz) h))
lemma sperm {x:ℕ}(hx:x∈u.D.P){A:ℝ}(h:p.postX x (p.scoreP 1) p.g.coin A):
   p.tunesF x (Amber.shade (leave 1) p.g.coin (Wear.powerF p.g)) A:= he.solvent hx ((Vessel.Sleigh.Wax.Good.whatV (p := p)) 1) h
lemma mixG {x y k:ℕ} (hx:x∈u.D.P)(ht:0<k) (hz:EscortV p x y (Fort.secondC k))
   (z:ℕ→ℝ)(h:p.carrierV x z u.w0.p.T)
   {B A:ℝ}(hf:p.recordP y A)(ha:p.postX x (p.scoreP 1) p.g.coin B)(hs:|p.pullP| ≤ p.amountP)
   (hh:|p.pullP*prismV p z*B*A| ≤ p.amountP):
   (p.s0 x).band p.due p.H p.g.prism (spriteV p k) (p.pullP*prismV p z*B*A):=by
        have hr:=he.remains hx
        unfold spriteV; rw [ite_eq_right (Nat.ne_of_gt ht)]
        exact he.bornC hx (show p.Approved _ from ⟨k,Or.inr (Or.inr (Or.inr rfl))⟩)
                       (hr.mult0 (hr.mult0 (he.oldera hx z h hs) (he.sperm hx ha)) (he.crafts hz hf)) hh
lemma frostC {x:ℕ}(hx:x∈u.D.P): (p.s0 x).band p.due p.H p.g.prism (spriteV p 0) 0:=by
    obtain ⟨hx',hp,_,hq⟩:=he.nums
    exact flex (steam _ _ (he.remains hx) (show powder 100 ≤ p.plant from hq)) (by omega) hp
                                                                                      (by change p.H ≤ p.H+_; exact Nat.le_add_right ..)
lemma received {x k:ℕ}(hx:x∈u.D.P)(hp:p.PayV x k):
    (p.s0 x).rite p.due (Fort.leave 0) k:=by
       have hf:=he.nums
       obtain ⟨hv,hk⟩:=hp
       have ht:k+4 ≤ p.plant:=by
             unfold plant GoodF.hour Era.tariff Era.budget bootC; change k ≤ clim u.r.w.p at hk;omega
       have hw: Pier.StampX p.quote0 k u.D p.s.a p.due:=by
          have hu:= he.char.pro.well.1
          have hz:=lb_le_inc k
          change lb k+1 ≤ p.due*u.D.D p.s.a
          nlinarith
       obtain ⟨v,m,h1,h2,f,hQ,hr⟩:=hv
       rw [hQ]
       exact Bullet.copy u.D he.char.pro (by omega) hx h1 hr (t:=0) hw h2
lemma stamped {x k:ℕ}(hx:x∈u.D.P)(hp:p.PayV x k){A:ℝ}
   (h:(p.s0 x).band p.due p.H p.g.prism (spriteV p k) A):
    (p.s0 x).band p.due p.H p.g.prism (Fort.syncC u.r p.g u.v) A:=
        Iris.parcel hp.major (he.received hx hp) h
abbrev shunt(p:Wax u):Cog:=
   Song.pleas (starC 3) (roost (k0 u) (fresh u.r p.g u.v) p.g.prism) (Fort.syncC u.r p.g u.v)
lemma sidle {x:ℕ} (hx:EscortV p p.x x (premier u.r)){A:ℝ}(hk:3 ≤ p.p.headQ)
    (hh:(p.s0 x).band p.due p.H p.g.prism (shunt p) A):
   p.f.band p.due p.H p.g.prism (middleP p) A:=by
        have hf:=he.nums
        apply Song.pinFalse (starC 1) (((Vessel.Sleigh.Wax.Good.body0 (p := p)) 1).trans (decide_eq_false (by omega)))
        apply Song.pinFalse (starC 2) (((Vessel.Sleigh.Wax.Good.body0 (p := p)) 2).trans (decide_eq_false (by omega)))
        exact Pier.bowls he.char.pro (by omega) hx.path.1 (by omega) rfl hx.path.2 _ hh

end Good

end
end ExactDerandomization.Vessel.Sleigh.Wax

end

section

namespace ExactDerandomization.Vessel.Ferry
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Sleigh Gamut ArcQ
variable {s:Sack u}

structure Slant (s:Sack u) where
    v:ArcQ s
    l:ℕ
    i:ℕ
    b:Bool
namespace Slant
variable (p:Slant s)
abbrev k(_:Slant s):= s.v.p.u
abbrev xB(_:Slant s)(x:ℕ):=x/M s
abbrev xR(_:Slant s)(x:ℕ):=x%M s
abbrev blade0 : Pool u.n:=pane (M s) p.i 0 p.v.routeP
abbrev born(c:Peek)(a:Pool u.n):OrbitV u:= ⟨p.v.forward,c,a⟩
abbrev g0:=p.v.amber
abbrev impala(i:ℕ):OrbitV u:=p.born (detector p.l i) p.blade0
abbrev startO:OrbitV u:=if p.b then p.born (prizep p.l p.k) p.blade0 else p.born (prizep p.l p.l) (rightP p.blade0)
abbrev temple := Peek.bay u.plotM p.l p.k
abbrev stopE : Fabric u:= ⟨p.temple,p.v.forward,leftP p.blade0⟩
abbrev Hport(j:ℕ): MeterQ:=PrintV.roy p.v.hullK u.n (M s) u.w0 p.i p.k p.l j p.v.forward p.b (Print.issued p.v.routeP) p.v.α
abbrev f0:= if p.i=0 then 0 else (p.impala 0).channel 17 0
abbrev hitC(x:ℕ):Prop:=p.xR x=p.i ∧ p.v.okQ x
abbrev onC(j:ℕ):Prop:=p.b=false ∨ j=0
abbrev dyeV :=if p.b then p.v.α else Coin.mult p.v.α (Aqua.rawcoins u.n p.l)
abbrev ptr:= if p.b then 3 else 4
abbrev pad0(p:Slant s)(x j:ℕ):Wax u:=p.v.palette x j
structure Ride(p:Slant s):Prop where
    he :p.v.Hand
    hh:p.g0.ask=none
    hl:p.g0.i=p.l+1
    hi:p.i<M s
    rateP:p.v.r.1.2=(if p.b then p.i else p.i+M s)
namespace Ride
variable {p:Slant s}
variable (ht:Ride p)
include ht
lemma frost : s.v.p.ready u.plotM s.v.m:=ht.he.pools.he.may.hc.he.2
lemma agedE :p.l  ≤ u.plotM.height∧ p.l  ≤  p.k∧p.k+p.v.forward ≤ u.plotM.roof∧2^p.l ≤ u.n:=by
   have hh:=ht.hl; have hv:=ht.he.ll0
   obtain ⟨h1,h2,h3,_⟩:=ht.frost; change p.g0.i ≤ _ at h1; change p.g0.i ≤ p.k at h2; change p.k+_ ≤ _ at h3
   exact ⟨by omega,by omega,by omega,
         u.plotM.fits ht.he.pools.he.vfen.sc (by omega)⟩
lemma north(j:ℕ)(hj:j<u.w0.p.T): (p.impala j).estate:=by
   have hh:= ht.agedE
   exact ⟨ht.he.aged,hh.1,le_rfl,by change p.l+p.v.forward ≤_; omega,rfl,hj⟩
lemma ap0 {v:Peek}{a: Pool u.n}(h:(p.born v a).estate):
     (p.born v a).FEnd:= ht.he.pools.eraR _ h ht.he.swift
lemma startS : p.startO.estate:=by
    have hh:=ht.agedE
    unfold startO; split
    · exact ⟨ht.he.aged,hh.1,hh.2.1,hh.2.2.1,trivial⟩
    exact ⟨ht.he.aged,hh.1,le_rfl,by change p.l+p.v.forward≤ _; omega,trivial⟩
lemma stopS :p.stopE.Good:=by
    have hh:=ht.agedE
    have hm:0<u.plotM.P.T:=u.w0.p.tOK.1
    exact ⟨ht.he.aged,hh.1,hh.2.1,le_rfl,hh.2.2.1,by change p.l+p.v.forward ≤ _; omega,rfl,by
                                                    change u.plotM.P.T-1 < u.plotM.P.T;omega⟩
lemma clay (j:ℕ) (x:ℕ) :
      (p.pad0 x j).p=if p.onC j then p.Hport j else PrintV.black :=by
    let a:=p.v;let r:= Ferry.core0 s
    have hv := ht.hl
    have hf: Garden.origin r≠6:=by
            have hh:s.v.p.ask=none:= ht.hh
            simp [Garden.origin,r,core0,OrbitV.c,Foil.kit,bitV,Garden.fence,hh]
    have ha:PlanV.x r=s.v.p.i:=rfl
    change PrintV.model u.r u.x r (a.cur j)=_
    unfold PrintV.model; dsimp only
    rw [ite_eq_right (show (a.cur j).1.1≠1 from by change (2:ℕ)≠1; omega),ite_eq_right hf]
    have hs:PlanV.x r-1=p.l:=by change p.g0.i-1=p.l; omega
    rw [hs]

    let q:=Print.stepout u.n p.k 0 a.bx.1 a.bx.2 (dec (Age.env r))
    have hp:q=Print.issued p.v.routeP:=Vessel.Ferry.ArcQ.Hand.step0
    let g(b:Bool)(i):MeterQ:=PrintV.roy p.v.hullK u.n (M s) u.w0 i p.k p.l j a.forward b q a.α
    change (if p.v.r.1.2<M s then if j=0 then g true p.v.r.1.2 else PrintV.black else g false (p.v.r.1.2-M s))=_
    rw [ht.rateP]
    have hr:g p.b p.i=p.Hport j:=congrArg (fun q=>PrintV.roy _ _ _ _ p.i _ _ _ _ _ q _) hp
    by_cases h:p.b=false
    · rw [h] at hr
      have hf:p.onC j:=Or.inl h
      simp only [ite_eq_right (show ¬(p.b=true) by rw [h];decide),ite_eq_left hf,Nat.add_sub_cancel,
                 ite_eq_right (show ¬ p.i+M s<M s by omega)]
      exact hr
    have h:p.b=true:=by cases he:p.b <;> grind
    rw [h] at hr
    have hf : p.onC j↔j=0 :=by unfold onC; rw [h]; simp
    simp only [ite_eq_left h,ite_eq_left ht.hi]
    by_cases hz:j=0
    · rw [ite_eq_left hz,ite_eq_left (hf.2 hz)]
      exact hr
    rw [ite_eq_right hz,ite_eq_right (fun h=>hz (hf.1 h))]

lemma pointI(j):
   let f:=p.Hport j
   f.h0=p.v.hullK∧f.headQ=p.ptr∧ f.i=p.i∧ f.value=p.dyeV∧f.ago=p.f0 ∧f.hereP=p.startO.channel 17 0:=by
   have hg:M s < u.n:= ht.he.pools.he.vfen.sc.radix_small
   have hh:0<M s:=by have :=ht.hi;omega
   have he:Prism.swap u.n (M s) p.i 0 (Print.issued p.v.routeP)=Print.issued p.blade0:=Prism.masked hh hg p.i 0 p.v.routeP
   dsimp only
   unfold Hport PrintV.roy; dsimp only;rw [he]; unfold startO ptr dyeV
   cases h:p.b <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma autocross(j)(h:p.b=false):
    (p.Hport j).pt = (p.stopE.leaveE.dataN,j):=by
   have hg:M s < u.n:= ht.he.pools.he.vfen.sc.radix_small
   have hh:0<M s:=by have :=ht.hi;omega
   unfold Hport PrintV.roy; dsimp only; rw [Prism.masked hh hg,h];rfl

lemma dim {x j:ℕ}(h:p.onC j):
    Wax.Good.lampY (p.pad0 x j)=true ↔ p.hitC x := by
   let f:=p.pad0 x j
   have hc:f.p=p.Hport j:=(ht.clay j x).trans (ite_eq_left h)
   unfold Wax.Good.lampY; change Fort.light u.n (M s) x f.p=true ↔ _
   obtain ⟨h1,h2,h3,-⟩:=ht.pointI j; have he:=ht.he.pools.he.lampq (p:=p.Hport j) (c:=p.v.bx) h1 x
   have hm: 0<p.ptr∧ ¬p.ptr<3:=by unfold ptr; split<;>omega
   rw [hc,he,h2,h3];unfold hitC ArcQ.okQ xR; tauto
lemma pale : |p.dyeV.v| ≤ 1:=by
   unfold dyeV; split;exact ht.he.chaste
   have hp := ht.agedE.2.2.2
   rw [Coin.mul0,Aqua.raw _ hp,abs_mul]
   have hc:=Est.spins hp
   rw [abs_of_nonneg hc.1]
   exact (mul_le_mul ht.he.chaste hc.2 hc.1 zero_le_one).trans (one_mul _).le
end Ride

end Slant
end
end ExactDerandomization.Vessel.Ferry

end

section

namespace ExactDerandomization.Vessel.Ferry.Slant
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Sleigh Gamut ArcQ Arena.Pier
variable {s:Sack u}

abbrev hop(p:Slant s):ℕ:=3+(p.i+M s)
abbrev boot0(p:Slant s) : ℕ:=Was.atom p.hop
def archive(p:Slant s)(x:ℕ)(i:ℕ):ℝ:= if p.i=0 then 1 else (p.impala i).fwd0 x
abbrev Y(p:Slant s)(x:ℕ):ℝ:= Net.carrier u.plotM s.v.r p.v.forward p.l p.i p.blade0 x
abbrev Z(p:Slant s)(x:ℕ):ℝ:=p.startO.fwd0 x

structure Ward (p:Slant s)(x i:ℕ):Prop where
     he:p.Ride
     hx:x∈u.D.P
     ha:i<K s
     hV:p.onC i
namespace Ward
variable {p:Slant s}{x i:ℕ}(hp:p.Ward x i)
include hp
lemma fame0 : (p.pad0 x i).Good:= hp.he.he.steam0 hp.hx hp.ha
lemma clue0 :(p.pad0 x i).p=p.Hport i:=(hp.he.clay i x).trans (ite_eq_left hp.hV)
lemma dawn0 :(p.pad0 x i).p.ago=p.f0:=by rw [hp.clue0]; exact (hp.he.pointI i).2.2.2.2.1
lemma canon0 :(p.pad0 x i).p.headQ=p.ptr:=by rw [hp.clue0]; exact (hp.he.pointI i).2.1
lemma watt0 :(p.pad0 x i).pullP=p.dyeV.v:=by unfold Wax.pullP; rw [hp.clue0]; exact congrArg Coin.v (hp.he.pointI i).2.2.2.1
lemma serves(v:OrbitV u)(h:v.estate) (he:v.m=p.v.forward){y:ℕ}(hy:y∈u.D.P):
    let A:=p.pad0 x i; let w:=v.channel 17 0
    A.postX y (hole w (hole 1 0)) 0 (v.fwd0 y):=by
    intro A w
    have hg:=hp.he.he
    exact ⟨w,hole 1 0,rfl,hg.deserted he 17 0,
                   hg.pools.eraR v h (he.symm ▸hg.swift) y hy⟩
lemma northV {j:ℕ}(hL:p.i≠0):
   Wax.midOld (p.pad0 x i) j=hole ((p.impala j).channel 17 0) (hole 1 0):=by
    let a:=p.pad0 x i; let v:=p.impala 0
    have hf:upQ.f u.x a.quote0=v.channel 17 0:= (Vessel.Sleigh.Wax.Good.ancient (p := a)).trans (hp.dawn0.trans (ite_eq_right hL))
    change Wear.rate0 (dec (upQ.f u.x a.quote0)) j=_
    rw [hf]
    unfold v OrbitV.channel vecL clr; rw [dec_round]; rfl
lemma cycleF {y:ℕ}(hy:y∈u.D.P): Wax.carrierV (p.pad0 x i) y (archive p y) u.w0.p.T:=by
    refine ⟨?_,?_⟩
    · intro j hj ht
      have hL:p.i≠0:= fun e=> ht (hp.dawn0.trans (ite_eq_left e))
      rw [hp.northV hL,archive,ite_eq_right hL]
      exact hp.serves _ (hp.he.north j hj) rfl hy
    intro he j hj; unfold archive
    rw [hp.dawn0] at he; unfold f0 at he; split at he
    · rw [ite_eq_left ‹_›]
    next hu=>exact (Age.cpos _ he).elim
lemma arctic (y:ℕ):
   Wax.prismV (p.pad0 x i) (archive p y)=p.Y y:=by
      let r:=archive p y
      unfold Wax.prismV Y Net.carrier
      split
      · next he=>
        have hh : ∀ j≤u.w0.p.T,Rime.Nest.Good.maxs (archive p y) j=(if j=0 then 0 else 1):=by
           intro j _
           induction j with
           | zero=>simp [Rime.Nest.Good.maxs]
           | succ j ih=>rw [Rime.Nest.Good.maxs,ih (by omega),archive,ite_eq_left he,ite_eq_right (show j+1≠0 by omega)];split <;> norm_num
        rw [hh _ le_rfl,ite_eq_right (Nat.ne_of_gt u.w0.p.tOK.1)]
        apply rising_top <;> norm_num
      next hu=>
        let f(i:ℕ):Paint u.n:=(s.v.r p.v.forward).outV (detector p.l i)
        have hb(i:ℕ):archive p y i=f i p.blade0 y:=by
             unfold archive f;rw [ite_eq_right hu,show s.v.r p.v.forward=_ from vault _ _ hp.he.he.ll0]
        have HH(j:ℕ):Rime.Nest.Good.maxs (archive p y) j = Maxer f j p.blade0 y:=by
              induction j with
              | zero=> rfl
              | succ j ih=>exact congrArg₂ max ih (hb j)
        exact congrArg boost (HH _)
lemma Ybound (y:ℕ):|p.Y y| ≤ 1:=by
     rw [←hp.arctic y]; have hl:in01 (Wax.prismV (p.pad0 x i) (archive p y)):=rising_mem ..
     exact (abs_of_nonneg hl.1).le.trans hl.2

lemma genuine {y:ℕ}(hy:y∈u.D.P):Wax.recordP (p.pad0 x i) y (p.Z y):=by
      unfold Wax.recordP
      have he:(p.pad0 x i).p.hereP=p.startO.channel 17 0:= by rw [hp.clue0]; exact (hp.he.pointI i).2.2.2.2.2
      rw [he]
      exact hp.serves _ hp.he.startS (show p.startO.m=p.v.forward by unfold startO;split<;>rfl) hy
lemma Zbound {y:ℕ}(hy:y∈u.D.P):|p.Z y| ≤ 1:=by simpa only [pow_zero] using Vessel.Ferry.ArcQ.Hand.heightB (hp.genuine hy)
omit hp in
lemma routeC {_:Slant s}:True:=trivial

lemma stroke0 : (premier u.r).f u.x (p.pad0 x i).quote0=(p.boot0,0):=by
   let f:=p.pad0 x i
   change (hole 0 (3+((tea.f u.x f.quote0).i+u.r.w.p.M)),0)=_
   rw [show tea.f u.x f.quote0=f.p from Vessel.Sleigh.Wax.Good.foster,show f.p.i=p.i from hp.clue0.symm ▸ (hp.he.pointI i).2.2.1]
lemma dives (ht:p.hitC x): Wax.EscortV (p.pad0 x i) x (p.xB x) (premier u.r):=by
    have hr:=hp.he.he.pools.he
    have hn:= hr.may.hc.till
    let m:=M s; let y:=p.xB x
    have hX:x∈u.D.P:=hp.hx;have hx:x ≤ u.n:= Nat.le_of_lt_succ (mem_range.1 hX)
    have hc:x%m=p.i:=ht.1;have hB:p.i < m:=hp.he.hi
    have hy:y ≤ u.n:= le_trans (Nat.div_le_self ..) hx
    have hg:p.hop ≤ u.v.bonus:= by
          apply le_trans _ hn.coinbook; change p.i < u.r.w.p.M at hB
          unfold hop ArcQ.M bootC; change 3+(p.i+u.r.w.p.M)≤_; omega
    have hf:Was.Flight u.r u.x p.hop 0 x y:=by
       refine ⟨hx,hy,?_⟩
       change if p.hop=0 then _ else if p.hop=1∨p.hop=2 then _ else
                         0=0 ∧ if p.hop-3< m then _ else p.hop-3-m < m ∧ x=radix m y (p.hop-3-m)
       have ht:p.hop=3+(p.i+m):=rfl
       rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),show p.hop-3-m=p.i from by omega]
       refine ⟨rfl,hB,?_⟩
       unfold radix;rw [←hc]; exact (Nat.mod_add_div ..).symm
    constructor; dsimp only
    rw [hp.stroke0]; refine ⟨?_,hr.vfen.basic0 hf hg (Nat.zero_le _)⟩
    refine ⟨?_,hp.hx,(Line.Chart.voteRoot (u := u)) hg (Nat.zero_le _),(hr.vfen.bootsBasic _).canonicalS⟩
    have he:1+u.D.D s.a ≤ u.D.W s.a:=by
         have hh:=hr.may.hc; let v:=s.v; let x:=s.i
         change 1+u.D.D (v.channel 5 x) ≤ u.D.W (v.channel 5 x)
         rw [show u.D.D (v.channel 5 x)=slackT v.m 5 x from u.rolff .., show u.D.W (v.channel 5 x)=Age.weight v.m 5 x from u.rolfe ..]
         have hm:=weights v.m 5 x; have hs:=pace v.m 5 x;omega
    rw [show cell p.boot0=0 from by simp [Slant.boot0,Was.atom,cell,hole]]
    exact he

end Ward
end
end ExactDerandomization.Vessel.Ferry.Slant

end

section

namespace ExactDerandomization.Vessel.Ferry.Slant
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Sleigh Gamut ArcQ Arena.Pier
variable {s:Sack u}

abbrev flow1(p:Slant s)(x:ℕ):ℝ:= p.dyeV.v*p.Y x*p.Z x
abbrev hueP(p:Slant s)(v:Producer)(x i:ℕ):ℝ:=v.scoreF p.stopE.finalE x i
abbrev flowQ(p:Slant s)(f:Producer)(x i:ℕ):ℝ:= p.dyeV.v*p.Y x*p.hueP f x i*p.Z (f.locate x i)
namespace Ward
variable {p:Slant s}{x i:ℕ}(hp:p.Ward x i)
include hp
lemma score0 (h:p.b=false)(b:ℕ):
   let a:=p.pad0 x i
   a.scoreP b=hole p.stopE.leaveE.dataN (hole b i) := by
       intro a
       have hf:a.p.pt=(p.stopE.leaveE.dataN,i):=hp.clue0.symm ▸hp.he.autocross i h
       unfold Wax.scoreP; rw [hf]
lemma songC (h:p.b=false){f:Producer}(hk:p.stopE.Efine s.k f){z:ℕ}(hz:z∈u.D.P):
   let a:=p.pad0 x i; let _:=p.stopE.leaveE
   a.postX z (a.scoreP 1) a.g.coin (p.hueP f z i):=by
       intro a v
       have he:= hp.he
       have ht:=hk.sector.suit; have hf:=ht.coil
       have hi:u.smallQ v.dataN i:=hf.awake (hf.size0 _ hp.ha)
       have hb: u.D.D v.dataN=1:=p.stopE.ageEnd _ (by decide)
       refine ⟨v.dataN,hole 1 i,hp.score0 h 1,he.he.signalF (a:=p.stopE) rfl _ _,?_⟩
       have hh:= (ht.voices z hz).ready i hi
       rw [show u.D.D p.stopE.leaveE.dataN=1 from hb,mul_one] at hh;exact hh
lemma tagL (h:p.b=false){f:Producer}(hk:p.stopE.Efine s.k f){z:ℕ}(hz:z∈u.D.P):
   (p.pad0 x i).PayV z (f.tag z i):=by
      let a:=p.pad0 x i;let v:=p.stopE.leaveE;let k:=f.tag z i
      have he:=hp.he
      have ht:=hk.sector.suit; have hf:=ht.coil
      have hi:u.smallQ v.dataN i:=hf.awake (hf.size0 _ hp.ha)
      refine ⟨⟨v.dataN,hole 0 i,he.he.signalF (a:=p.stopE) rfl _ _,(ht.trace z hz).next i hi,
                                   stampF 0,rfl,((Vessel.Sleigh.Wax.Good.whatV (p := a)) 0).trans (hp.score0 h ..)⟩,?_⟩
      change k ≤ _
      by_cases ht:k=0; rw [ht]; omega
      exact hk.tin rfl z i ht
lemma mot (h:p.b=false) (k:ℕ):
   let a:=p.pad0 x i; let v:=p.stopE; (secondC k).f u.x a.quote0=(v.slotWord i,k):=by
      intro a v
      let j:=elder.f u.x a.quote0
      have hf:a.p.pt=(p.stopE.leaveE.dataN,i):=hp.clue0.symm ▸ hp.he.autocross i h
      have hs:j=(v.leaveE.dataN,i):= (congrArg MeterQ.pt (Vessel.Sleigh.Wax.Good.foster (p := a))).trans hf
      change (hole (enc ((12,(dec j.1:Crt).2):Crt)) j.2,k)=_
      rw [hs]
      have hh:(dec v.leaveE.dataN:Crt)=Foil.kit 14 (v.m,0) (bitR v.t) (enc (Print.issued v.dye)):=dec_round ..
      dsimp only; rw [hh];rfl
lemma blood (h:p.b=false){f:Producer}(hk:p.stopE.Efine s.k f){z:ℕ}(hz:z∈u.D.P)(ht:0<f.tag z i):
    Wax.EscortV (p.pad0 x i) z (f.locate z i) (secondC (f.tag z i)):=by
     let k:=f.tag z i; let v:=p.stopE
     obtain ⟨h1,h2,h3⟩:= hk.source rfl i hp.ha k ht (hk.tin rfl z i (Nat.ne_of_gt ht))
     constructor;dsimp only
     have hM:=hp.mot h k
     change (secondC _).f _ _=_ at hM
     change Liaison _ z _ ((secondC k).f u.x _).1 _∧u.D.curve ((secondC k).f u.x _).1 _ _ _=_
     rw [hM]; refine ⟨⟨?_,hz,h1,h2⟩,?_⟩
     · rw [show cell (v.slotWord i)=v.c 12 0 from by simp [Fabric.slotWord,cell,hole]]
       exact hp.he.he.signalF (a:=v) rfl _ _
     have HH := h3 z hz; rw [ite_eq_left rfl] at HH; exact HH
lemma used1 {z:ℕ}(h:z∈u.D.P):
   let a:=p.pad0 x i
   (a.s0 z).band a.due a.H a.g.prism (roost (Wax.k0 u) (Fort.fresh u.r a.g u.v) a.g.prism)
                  (p.flow1 z):=by
     intro a
     have he:= hp.fame0
     have hh: |a.pullP| ≤ 1:=hp.watt0 ▸ hp.he.pale
     have hm:1 ≤ a.amountP:=mass1 ..
     have hc: |p.flow1 z|≤a.amountP:=by
        unfold flow1; simp only [abs_mul]; have h1:=hp.Ybound z;have h2:=hp.Zbound h
        have ht:=hp.he.pale
        refine le_trans (mul_le_mul (mul_le_mul ht h1 (abs_nonneg _) (by norm_num)) h2 (abs_nonneg _) (by norm_num)) ?_
        rwa [mul_one,mul_one]
     have hw:a.pullP*a.prismV (archive p z)*p.Z z=p.flow1 z:= by
        rw [show a.pullP=_ from hp.watt0,show a.prismV (archive p z)=_ from hp.arctic z]
     exact hw ▸ he.freshC h (archive p z) (hp.cycleF h) (hp.genuine h) (hh.trans hm) (hw.symm ▸hc)
lemma usedQ (h:p.b=false){f:Producer}(hk:p.stopE.Efine s.k f){z:ℕ}(hz:z∈u.D.P):
   let a:=p.pad0 x i
   (a.s0 z).band a.due a.H a.g.prism (Fort.syncC u.r s.k u.v) (p.flowQ f z i):=by
     intro a
     let k:= f.tag z i; let y:=f.locate z i; let c:= p.hueP f z i
     have ht:a.Good:=hp.fame0
     apply ht.stamped hz (hp.tagL h hk hz)
     by_cases hb : k=0
     · rw [show p.flowQ f z i=0 from ?_,show f.tag z i=0 from hb]; exact ht.frostC hz
       have he:p.hueP f z i=0:=ite_eq_right (fun h=> h hb)
       rw [flowQ,he];ring
     have hx :=hp.blood h hk hz (show 0<k from Nat.pos_of_ne_zero hb)
     have hy:y∈u.D.P:=ht.already hx
     have hQ:=hp.songC h hk hz
     have hw:a.pullP * a.prismV (archive p z)*c*p.Z y=p.flowQ f z i:=by
        rw [show a.pullP=_ from hp.watt0,show a.prismV (archive p z)=_ from hp.arctic z]
     have hh: |a.pullP| ≤ 1:= hp.watt0 ▸ hp.he.pale
     have hc: |p.flowQ f z i| ≤ a.amountP:=by
        unfold flowQ; simp only [abs_mul]
        have hf := Vessel.Ferry.ArcQ.Hand.heightB hQ; change |c| ≤ range0 s.k at hf
        have hz' := hp.Zbound hy
        have hM : range0 s.k ≤ a.amountP:=Vessel.Sleigh.Wax.Good.power0 (p := a)
        apply le_trans (mul_le_mul_of_nonneg_left hz' (by positivity)); rw [mul_one]
        have ht' := mul_le_mul_of_nonneg_left (show |c| ≤ a.amountP from hf.trans hM) (show 0 ≤ |p.dyeV.v| * |p.Y z| from by positivity)
        apply ht'.trans
        have he: |p.dyeV.v| * |p.Y z| ≤ 1:=by
             apply le_trans (mul_le_mul hp.he.pale (hp.Ybound z) (abs_nonneg _) (by norm_num))
             norm_num
        exact (mul_le_mul_of_nonneg_right he (mass0 ..).le).trans (one_mul _).le
     have hd:= ht.mixG hz (show 0<k from Nat.pos_of_ne_zero hb)
                         hx (archive p z) (hp.cycleF hz) (hp.genuine hy) hQ (hh.trans (mass1 ..)) (hw.symm ▸hc)
     rw [show a.pullP*a.prismV (archive p z)*c*p.Z y=p.flowQ f z i from hw] at hd
     exact hd

end Ward
end
end ExactDerandomization.Vessel.Ferry.Slant

end

section

namespace ExactDerandomization.Vessel.Ferry.Slant
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Sleigh Gamut ArcQ
variable {s:Sack u}

abbrev SceneF(p:Slant s): Flame u.n:=p.g0.roy u.plotM s.v.r p.l
abbrev headA(p:Slant s):Est.Line u.n:= Peek.primeQ u.plotM p.g0 s.v.r p.l p.i
abbrev headB(p:Slant s): Est.Line u.n:= Peek.syncQ u.plotM p.g0 s.v.r p.l p.i
abbrev beacon(p:Slant s)(x:ℕ):ℝ :=
    p.Y (p.xB x)*p.dyeV.v*∑ z∈p.stopE.S1,p.stopE.finalE (p.xB x) z*p.Z z
abbrev sense1(p:Slant s)(x:ℕ) := if p.hitC x then p.flow1 (p.xB x) else 0
abbrev senseB(p:Slant s)(f:Producer)(x i:ℕ) := if p.hitC x then p.flowQ f (p.xB x) i else 0
namespace Ride
variable {p:Slant s}(hp:p.Ride)
include hp
lemma glimpse :s.v.s=p.SceneF:=by
    have hx:p.g0.ask=none:=hp.hh
    change p.g0.weave u.plotM s.v.r=_
    unfold Peek.weave;rw [hx];simp only [hp.hl]

lemma prumb (h:p.b=true)(x:ℕ):p.v.intended x=p.sense1 x:=by
   have hm: p.v.r.1.2=p.i:=hp.rateP.trans (ite_eq_left h)
   let r:= s.v.r; let m:=p.v.forward
   have hv:(s.v.s.lines p.v.r.1)=p.headA:=by
     rw [hp.glimpse]
     unfold SceneF Peek.roy;dsimp only;rw [hm,ite_eq_left (show p.i < u.plotM.P.M from hp.hi)]
   have hO:p.startO=p.born (prizep p.l p.k) p.blade0:= ite_eq_left h
   have hc: p.dyeV=p.v.α:=ite_eq_left h
   rw [hp.he.voice0,hv]
   unfold headA Peek.primeQ; dsimp only
   unfold Est.core ridge;rw [ite_eq_left rfl]
   unfold vim mint sense1
   by_cases hQ:p.hitC x
   · rw [ite_eq_left hQ,ite_eq_left (show x%u.plotM.P.M=p.i from hQ.1),ite_eq_left hQ.2]
     let z:=p.xB x
     unfold flow1
     rw [hc,show p.Z z=(r m).outV (prizep p.l p.k) p.blade0 z from
                      (by unfold Z;rw [hO]; exact (congrArg (fun h:Tick u.n=>h.outV _ _ _) (show r m=_ from vault _ _ hp.he.ll0)).symm)]
     change p.v.α.v*(p.Y z* _)=_
     exact (mul_assoc ..).symm
   rw [ite_eq_right hQ]
   split
   · next he=> rw [ite_eq_right (show ¬x%u.plotM.P.M=p.i from fun e=>hQ ⟨e,he⟩),mul_zero]
   rfl
lemma mumb (h:p.b=false)(x:ℕ):p.v.intended x= if p.hitC x then p.beacon x else 0:=by
   have hm:p.v.r.1.2=p.i+M s:=hp.rateP.trans (ite_eq_right (show ¬p.b=true by rw [h]; decide))
   let r:= s.v.r; let m:=p.v.forward
   have hv:(s.v.s.lines p.v.r.1)=p.headB:=by
     rw [hp.glimpse]
     unfold SceneF Peek.roy; dsimp only; rw [hm]
     rw [ite_eq_right (show ¬p.i+M s < u.plotM.P.M by change ¬p.i+M s<M s; omega),show p.i+M s-u.plotM.P.M=p.i from Nat.add_sub_cancel ..]
   have hO:p.startO=p.born (prizep p.l p.l) (rightP p.blade0):= ite_eq_right (show ¬p.b=true by rw [h];decide)
   have ht: r m=forecast u.plotM m:=vault _ _ hp.he.ll0
   have hc: p.dyeV.v=p.v.α.v*peeler u.n p.l:=by
      unfold dyeV;rw [ite_eq_right (show ¬p.b=true by rw [h];decide),Coin.mul0,Aqua.raw _ hp.agedE.2.2.2]
   rw [hp.he.voice0,hv]; unfold headB Peek.syncQ;dsimp only
   unfold Est.core ridge; rw [ite_eq_left rfl]
   unfold vim mint
   by_cases hQ:p.hitC x
   · rw [ite_eq_left hQ,ite_eq_left (show x%u.plotM.P.M=p.i from hQ.1),ite_eq_left hQ.2]
     let z:=p.xB x; let f:=p.stopE
     have hr: p.Z=(r m).outV (prizep p.l p.l) (rightP p.blade0):= by
         ext z; change p.startO.fwd0 z=_; rw [hO,ht]
     unfold beacon; change p.v.α.v*(p.Y z*(peeler u.n p.l*∑ i∈f.S1,
              ((r m).outR f.t f.dye z i)*((r m).outV (prizep p.l p.l) (rightP p.blade0) i)))=
                   p.Y z*p.dyeV.v*∑ i∈f.S1,f.finalE z i*p.Z i
     rw [hr,hc,show f.finalE= (r m).outR f.t f.dye from by rw [ht]]; ring
   rw [ite_eq_right hQ]
   split
   · next he=> rw [ite_eq_right (show ¬x%u.plotM.P.M=p.i from fun e=>hQ ⟨e,he⟩),mul_zero]
   rfl
lemma primes (h:p.b=false){f:Producer}(hh:p.stopE.Efine s.k f) (x:ℕ)(hx:x∈u.D.P):
    ∑ i∈range (K s), p.senseB f x i=p.v.intended x:=by
     rw [hp.mumb h x]; unfold senseB
     by_cases he:p.hitC x
     · simp_rw [ite_eq_left he]
       let S:=range (K s)
       let z:=p.xB x; let v:=p.stopE
       have hz:z∈u.D.P:= mem_range.2 ((show z ≤ x from Nat.div_le_self ..).trans_lt (mem_range.1 hx))
       have ht : ∑ j∈v.S1,v.finalE z j*p.Z j= ∑ i∈range (K s),p.hueP f z i*p.Z (f.locate z i):=by
           have hf :∑ j∈v.S1,v.finalE z j*p.Z j=∑ j∈v.S1,∑ i∈S,
                                    (if f.locate z i=j then p.hueP f z i else 0)*p.Z j:=by
              apply sum_congr rfl;intro j hj
              rw [←sum_mul]
              exact congrArg (fun y=>y*p.Z j) (hh.sector.supply z j hz).symm
           rw [hf,sum_comm]
           apply sum_congr rfl; intro i hi
           let a:=f.locate z i
           rw [sum_eq_single a]
           · rw [ite_eq_left rfl]
           · intro j _ he; rw [ite_eq_right (Ne.symm he),zero_mul]
           intro ha; have hq:¬f.awake z i:= fun e=>ha (hh.sector.light.insured _ _ e).2
           rw [show p.hueP f z i=0 from ite_eq_right hq];split<;>ring
       change _=p.Y z*p.dyeV.v*∑ i∈v.S1,_
       rw [ht,mul_sum]
       apply sum_congr rfl; intro i hi; unfold flowQ; unfold z;ring
     simp only [ite_eq_right he,sum_const_zero]

lemma ship1 {x:ℕ}(hx:x∈u.D.P)(h:p.b=true):
   VisitF p.v x (p.v.prickF x):=by
      refine ⟨Vessel.Ferry.ArcQ.Hand.united0 x,fun j hj=>?_⟩
      let a:=p.pad0 x j; have ht:a.Good:=hp.he.steam0 hx hj
      unfold prickF
      by_cases hv:j=0
      · rw [ite_eq_left hv,hp.prumb h x]
        have hc:p.onC j:= Or.inr hv
        have hf:Ward p x j:=⟨hp,hx,hj,hc⟩
        unfold sense1;split
        · next hh=>
          have hl:= hf.dives hh; let z:=p.xB x; have hw:= hf.used1 (ht.already hl)
          have hb:a.p.headQ=3:=hf.canon0.trans (ite_eq_left h)
          exact ht.boil0 ((hp.dim hc).2 hh)
                     (ht.sidle hl (le_of_eq hb.symm)
                              (Song.pinTrue (starC 3) (((Vessel.Sleigh.Wax.Good.body0 (p := a)) 3).trans (decide_eq_true hb)) hw))
        next he=> exact ht.dark (Bool.eq_false_iff.2 (fun e=>he ((hp.dim hc).1 e)))
      rw [ite_eq_right hv]; apply Vessel.Ferry.TorchE.tabs0 _ ht
      have hc:¬p.onC j:=by unfold onC;rw [h]; simp [hv]
      exact (hp.clay j x).trans (ite_eq_right hc)

lemma shipB {x:ℕ}(hx:x∈u.D.P)(h:p.b=false){f:Producer}(hh:p.stopE.Efine s.k f):
   VisitF p.v x (p.senseB f x):=by
      refine ⟨hp.primes h hh x hx,fun j hj=>?_⟩
      let a:=p.pad0 x j; have ht:a.Good:=hp.he.steam0 hx hj
      have hc:p.onC j:=Or.inl h
      have hf:Ward p x j:=⟨hp,hx,hj,hc⟩
      unfold senseB; split
      · next hu=>
        have hl:=hf.dives hu; have hw:=hf.usedQ h hh (ht.already hl)
        have hb:a.p.headQ=4:= hf.canon0.trans (ite_eq_right (show ¬p.b=true by rw [h];decide))
        exact ht.boil0 ((hp.dim hc).2 hu)
                     (ht.sidle hl (show 3 ≤ a.p.headQ from by omega)
                         (Song.pinFalse (starC 3) (((Vessel.Sleigh.Wax.Good.body0 (p := a)) 3).trans (decide_eq_false (by omega))) hw))
      next he=>exact ht.dark (Bool.eq_false_iff.2 (fun e=>he ((hp.dim hc).1 e)))
lemma transported {x:ℕ}(hx:x∈u.D.P):∃ f,VisitF p.v x f:=by
      cases h:p.b
      · obtain ⟨f,hf⟩:= hp.he.pools.thenP p.stopE hp.stopS hp.he.swift
        exact ⟨_,hp.shipB hx h hf⟩
      exact ⟨_,hp.ship1 hx h⟩
end Ride
end
end ExactDerandomization.Vessel.Ferry.Slant

end

section

namespace ExactDerandomization.Vessel.Ferry
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Sleigh Gamut Slant ArcQ
variable (s:Sack u)
namespace ArcQ.Hand
variable {s:Sack u}
variable {p:ArcQ s}(hp:p.Hand)
include hp
lemma inherit0 {x:ℕ}(hx:x∈u.D.P):∃ f,VisitF p x f:=by
    cases h:s.v.p.ask
    ·
      have ha:=hp.price0.1
      unfold OrbitV.s Peek.weave at ha;rw [h] at ha
      cases he:s.v.p.i with
      | zero=> rw [he] at ha; simp at ha
      | succ i=>
               let j:=p.r.1.2; let m:=M s
               unfold Peek.roy at ha
               rw [he] at ha
               have hl:j<2*m:= mem_range.1 (mem_product.1 ha).2
               by_cases hh:j< m
               · let k:Slant s:=⟨p,i,j,true⟩
                 exact Slant.Ride.transported (p:=k) ⟨hp,h,he,hh,rfl⟩ hx
               let k:Slant s:=⟨p,i,j-m,false⟩
               exact Slant.Ride.transported (p:=k) ⟨hp,h,he,show j-m< m from by omega,
                                  show j=(if false then j-m else j-m +m) from by simp [show j-m+m=j by omega]⟩ hx
    next k=> exact ⟨_,hp.voyage _ h hx⟩
end ArcQ.Hand

namespace Perch
open PlanV Census
abbrev ZeroS(_:Sack u):Seed:=Seed.old false 0
abbrev zero0(s:Sack u):Prop := s.i=0∧s.v.p.i=0∧s.v.p.ask=none
abbrev bandF(s:Sack u)(x i:ℕ)(A:ℝ):Prop:=(s.home x i).band s.c s.τ s.k.prism s.g A
abbrev bandS(s:Sack u)(x:ℕ)(p:Seed)(A:ℝ):Prop:=bandF s x (enc p) A
abbrev zcost(s:Sack u)(x:ℕ):ℝ:=if x∈s.v.S∧ s.i=0 then s.v.s.base x x else 0
abbrev areaS(s:Sack u):Finset Arc:=s.v.areaV s.i
abbrev stars(s:Sack u):Finset (Arc×ℕ):=areaS s ×ˢ range (K s)
def brief(p:Arc×ℕ):Seed:=(ArcQ.mk p.1 :ArcQ s).cur p.2
abbrev jar : Finset Seed := (stars s).image (brief s)
abbrev jug : Finset Seed := if zero0 s then {ZeroS s} else ∅
lemma rayC (s:Sack u):Set.InjOn (brief s) ↑(stars s):=by
   intro i hi j hj h
   obtain ⟨hz,hQ,_⟩:=Seed.along_inj.1 h
   exact Prod.ext ((Census.disjoint0 (w:=u.w0) s.v.tire rfl true _ s.i)
                 (mem_product.1 hi).1 (mem_product.1 hj).1 hz) hQ

lemma urn_id (x:Seed): x∈jar s ↔ PlanV.beats u.w0 (core0 s) x :=by
   constructor
   · intro ht; obtain ⟨j,hj,rfl⟩:=mem_image.1 ht
     exact s.v.awakeV (mem_product.1 hj).1 _ (mem_range.1 (mem_product.1 hj).2)
   rintro ⟨hh,h1,h2,h3⟩
   rw [show PlanV.trees u.w0 (core0 s)=s.v.s.rays from (s.v.agroV s.i).symm] at h3
   let a:=s.v.p.i; let v:=x.fog; let m:=s.v.m
   let z :=s.v.tire
   have hz : v.habitat u.w0 z.key.a z.M s.i s.v.s.rays:=h3
   obtain ⟨hx,hA,hW⟩:= Fog.totally rfl hz
   let r:Arc:=(v.ray a,v.slackM m,v.2)
   have he:r∈areaS s:=by
       refine (pat ..).2 ⟨hx,hA,?_⟩
       change v.event<Print.rad^(u.w0.ell*_); have he:=hz.2.2.2.2
       have ht : s.v.tire.slack r.2.1=v.sig:=hz.2.2.1
       rw [show s.v.tire.slack r.2.1=v.sig from ht]; exact he
   refine mem_image.2 ⟨(r,x.x),mem_product.2 ⟨he,mem_range.2 h1⟩,?_⟩
   have hu:drops s.v.tire true r=v:=by
        change v.first0=true at h2; rw [←h2]; exact hW
   exact (congrArg (fun f=> Seed.along f x.x 0) hu).trans hh.symm
lemma sensed(s:Sack u) : (¬PlanV.sensor (core0 s))↔ s.v.p.ask=none:=by
   unfold PlanV.sensor Garden.origin core0
   cases h:s.v.p.ask <;> simp [h,Garden.fence,OrbitV.c,Foil.kit,Foil.bitV]
lemma begun {p:Seed}:p∈jug s ↔ PlanV.lead (core0 s) p:=by
   have hf: (PlanV.lead (core0 s) p)↔(zero0 s∧p=ZeroS s):=by
       unfold PlanV.lead; rw [sensed]
       change (_∧s.i=_ ∧s.v.p.i=_∧_)↔_
       unfold zero0;tauto

   rw [hf]
   unfold jug; split <;> simp_all ; tauto

lemma aperture:Disjoint (jar s) (jug s):=by
   apply Finset.disjoint_left.2
   intro i hi hx
   have hh := (begun s).1 hx
   have hz:= (urn_id s i).1 hi
   exact Seed.old_not false 0 _ _ _ (hh.2.2.2.symm.trans hz.1)

namespace TorchE
variable {s}(he:TorchE s)

include he
lemma kosmos(z:Seed)(hz:valid0 s z):enc z<s.Pn:=by
   have hf:=he.may.hc.till.saving;have hc:=he.may
   have hd:1 ≤ s.d:=gap_pos ..
   have hp:Pass.sized z (Pass.reserve u.w0) s.d:=by
       rcases hz with hh|hh
       · rw [show z=Seed.old false 0 from hh.2.2.2]
         apply Fen.GardenV.oldcap hd false
         have hh:1 ≤ passport u.w0:=by unfold passport;omega
         rw [show lb (enc (0:ℕ)) =1 from lb_zero]
         nlinarith
       let v:=s.v
       obtain ⟨hz,hw,ha,hT⟩:=hh
       have h1:v.s.rays=PlanV.trees u.w0 (core0 s):=v.agroV s.i
       rw [←h1] at hT
       exact hz.symm ▸ Pass.lengthC u.w0 (s:=s.v.tire) rfl (he.may.hk)
                       (fun x hx=>s.v.fuel x hx) hT hw.le (Nat.zero_le _)
   exact lt_of_lt_of_le (below _) (Nat.pow_le_pow_right (by omega) (hp.trans
                             (Nat.mul_le_mul_right s.d (by change Pass.reserve u.r.w ≤ s.k.vol; have:=hf.power;omega))))

omit he in
lemma value0(h:zero0 s)(x:ℕ):
   s.v.s.base x x= ((flareP s x (ZeroS s)).moneyX x).v:=by
      obtain ⟨h1,h2,h3⟩:= h
      unfold OrbitV.s Peek.weave; rw [h3,h2]
      unfold Peek.pursue; simp only [h3,h2,ridge,ite_true]
      change ((u.r.P.reward u.x x):ℝ)=_
      unfold Wax.moneyX Base.Source.reward; split<;> simp_all

lemma cheap (h:zero0 s){x:ℕ}(hx:x∈u.D.P):bandS s x (ZeroS s) (zcost s x):=by
   let z:= ZeroS s
   have hz:z∈jug s:=by unfold jug; rw [ite_eq_left h];exact mem_singleton_self ..
   let A:=flareP s x z
   have hg:A.Good:= he.fitted hx z (Or.inl ((begun s).1 hz))
   have hc:A.p=PrintV.dawn (W0 s (0,0)):=by change PrintV.model _ _ _ z=_; unfold PrintV.model; apply ite_eq_left (show z.1.1=1 from rfl)
   have hf:A.p.h0=W0 s (0,0):=hc.symm ▸rfl
   have hh:A.p.headQ=1:=hc.symm ▸rfl
   have hl:Wax.Good.lampY A=true↔x∈s.v.S:=by
       change Fort.light _ _ x _=_↔_
       rw [he.lampq hf,Vessel.Ferry.TorchE.parked,hh]; grind
   unfold zcost;split
   · next hX=>
       rw [value0 h]
       exact hg.boil0 (hl.mpr hX.1) (hg.boonBase hh)
   next hu=> exact hg.dark (Bool.eq_false_iff.2 (fun e=>hu ⟨hl.1 e,h.1⟩))
omit he in
lemma quietC (h:¬ zero0 s)(x:ℕ):zcost s x=0:=by
   unfold zcost; split
   · next he=>
     unfold OrbitV.s Peek.weave
     cases hl:s.v.p.ask
     · cases hj:s.v.p.i
       · exact (h ⟨he.2,hj,hl⟩).elim
       rfl
     next j=>rfl
   rfl
end TorchE
end Perch
end
end ExactDerandomization.Vessel.Ferry

end

section

namespace ExactDerandomization.Vessel.Ferry
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring
open Cambria Wear Blade Fort
noncomputable section
open scoped Classical
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
open Basket Basket.Sack Sleigh Gamut Slant ArcQ Rain.Census
variable (s:Sack u)
open Perch
abbrev galaxy: Finset Seed:= jar s∪jug s
abbrev orbitZ:= (galaxy s).image enc
abbrev flowC (r:Arc)(x:ℕ):ℝ:=(⟨r⟩:ArcQ s).intended x

lemma tagroot (j:Seed):j∈ galaxy s ↔ valid0 s j:=by
     rw [galaxy,mem_union,urn_id s,begun s]; unfold valid0 PlanV.validV;tauto
lemma haunt (i): i∈orbitZ s ↔ enc (dec i:Seed)=i ∧ valid0 s (dec i):=by
      unfold orbitZ;rw [mem_image]; constructor
      · rintro ⟨x,h,rfl⟩;rw [Wire.eq]; exact ⟨rfl,(tagroot ..).1 h⟩
      rintro ⟨hp,hV⟩; exact ⟨_,(tagroot ..).2 hV,hp⟩

lemma atmosphere (x:ℕ) :
   s.v.chipV x s.i=(∑ i∈areaS s,flowC s i x)+zcost s x := by
    unfold OrbitV.chipV;rw [Census.humid]
    unfold flowC ArcQ.intended zcost; split
    · next hz=> simp only [hz,true_and]
    next hu=>simp [hu]

namespace Wells
variable {s:Sack u}(he:Wells s)
include he
lemma grouped (x:ℕ)(hx:x∈u.D.P):
    ∃ f:Arc→ℕ → ℝ,∀ i∈areaS s, VisitF (⟨i⟩:ArcQ s) x (f i):=by
    have hp(i:Arc): ∃ f:ℕ→ℝ,i∈areaS s → VisitF (⟨i⟩:ArcQ s) x f:=by
       by_cases ht:i∈areaS s
       · obtain ⟨f,hf⟩:= ArcQ.Hand.inherit0 (show ArcQ.Hand (⟨i⟩:ArcQ s) from ⟨he,ht⟩) hx
         exact ⟨f,fun _=>hf⟩
       exact ⟨fun _=>0,fun h=>(ht h).elim⟩
    choose f hf using hp; exact ⟨f,hf⟩

lemma spentQ (x:ℕ)(hx:x∈u.D.P)(g:Arc→ℕ→ℝ)(hr:∀ i∈areaS s,VisitF (⟨i⟩:ArcQ s) x (g i)):
    ∃ f:Seed → ℝ,(∀ i∈stars s,f (brief s i)=g i.1 i.2)∧
                        (∀ i∈jug s,f i=zcost s x)∧∀ i∈galaxy s,bandS s x i (f i):=by
   have hh (i:Seed):∃ V:ℝ,(∀ j∈stars s,brief s j=i→ V=g j.1 j.2) ∧(i∈jug s→V=zcost s x)∧
                                                  (i∈ galaxy s→bandS s x i V):=by
      by_cases hl:i∈jar s
      · obtain ⟨j,hj,rfl⟩:= mem_image.1 hl
        obtain ⟨ht,hb⟩:=mem_product.1 hj
        refine ⟨g j.1 j.2, fun k hk he=>?_,?_,fun _=>(hr j.1 ht).has0 _ (mem_range.1 hb)⟩
        · rw [rayC s hk hj he]
        intro h; exact (disjoint_left.1 (aperture s) hl h).elim
      have hs(k:ℝ)(j :Arc×ℕ)(he:j∈stars s)(hk:brief s j=i):k=g j.1 j.2:=
                         (hl (mem_image.2 ⟨j,he,hk⟩)).elim
      refine ⟨zcost s x,hs _,fun _=>rfl,?_⟩
      intro hp
      have hh:= (mem_union.1 hp).resolve_left hl
      unfold jug at hh; split at hh
      · next he1=>
                 rw [mem_singleton.1 hh]
                 exact Perch.TorchE.cheap he.he he1 hx
      exact (Finset.notMem_empty i hh).elim
   choose f hf using hh
   exact ⟨f,fun i hi=>(hf (brief s i)).1 _ hi rfl,fun i=>(hf i).2.1,fun i=>(hf i).2.2⟩

lemma harvests(x:ℕ)(hx:x∈u.D.P) : ∃ f, s.harvest x f:=by
   obtain ⟨g,hg⟩:=he.grouped x hx; obtain ⟨f,hf,hl,hp⟩:=he.spentQ x hx g hg
   let p := orbitZ s
   let h(i:ℕ):ℝ:= if i∈p then f (dec i) else 0
   refine ⟨h,?_,fun i hi=>?_⟩
   · have hu:p⊆range s.Pn:=by
        intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.1 hi
        exact mem_range.2 (Perch.TorchE.kosmos he.he j ((tagroot ..).1 hj))
     rw [←sum_subset hu (fun i _ hz=> ite_eq_right hz)]
     have hU : ∑ i∈p,h i=∑ i∈galaxy s,f i:=by
        unfold p orbitZ; rw [sum_image (by
             intro x _ y _ he; exact (Wire.eq _).symm.trans ((congrArg dec he).trans (Wire.eq _)))]
        apply sum_congr rfl; intro i hi; unfold h;rw [ite_eq_left (show enc i∈p from mem_image_of_mem _ hi),Wire.eq]
     rw [hU, galaxy,sum_union (aperture s)]
     have ht : ∑ i∈jar s,f i= ∑ i∈areaS s,flowC s i x:=by
        unfold jar;rw [sum_image (fun x hx y hy he=> rayC s hx hy he)]
        have hl : ∑ i∈stars s,f (brief s i)=∑ i∈stars s,g i.1 i.2:=sum_congr rfl hf
        rw [hl,stars,sum_product]; apply sum_congr rfl; intro i hi; exact (hg i hi).union0
     have hh : ∑ i∈jug s,f i=zcost s x:=by
        by_cases ha:zero0 s
        · have hh:jug s={ZeroS s}:=ite_eq_left ha
          rw [hh,sum_singleton]
          exact hl _ (by simp [hh])
        rw [show jug s=∅ from ite_eq_right ha,sum_empty];exact (Perch.TorchE.quietC ha x).symm
     rw [ht,hh]; exact (atmosphere s x).symm
   unfold h; split
   · next hu=> obtain ⟨j,hj,rfl⟩:=mem_image.1 hu; rw [Wire.eq]; exact hp j hj
   next ht=>
   have hz:¬(enc (dec i:Seed)=i∧ valid0 s (dec i)):=fun h=>ht ((haunt s i).2 h)
   exact Vessel.Ferry.TorchE.tabs0 (phantom s x i) (he.he.else0 hx hz) rfl
lemma cockpit (x:ℕ)(hx:x∈u.D.P)(h:s.priorE x):s.v.Earn s.k s.i x:=by
   obtain ⟨f,hf⟩:= he.harvests x hx; exact he.he.may.advances hx h hf
end Wells

end
end ExactDerandomization.Vessel.Ferry

end

section

namespace ExactDerandomization.Vessel
open Analysis Relay Counter Rill Fret At Hie
open Arena Amber Song Fret.Lyric Reed Lu Est Net
open Grain Terrain Bank Helix Helix.Age Helix.Mold Helix.Foil Helix.Moon Helix.Orbit Chime Dome Scheme Finset Stage
open SiteX Line Fret.Seats
open Rain Spring Sun
noncomputable section
open scoped Classical

variable {q w h:ℕ}
namespace Ma
abbrev essence :Cub ℕ Crt:=⟨_,(Kn.unpack (α:=Crt)).comp VK.left⟩
def brain : Sight:=
    let a:=essence.runs; let m:=a.right.left.left
    let k:= (Kn.fix 5).tuple ((m.tuple m.bl.pred).tuple a.right.right)
    ⟨_,Kn.wash.comp ((Kn.wash.comp k).tuple (Kn.fix (hole 1 0)))⟩
def mature(w:Wares):Cub ℕ Bool:=
   let p:=essence.runs
   ⟨_,GK.decideK (onVK w p.right.right.left p.right.left.left)⟩
def sourceP (k:MintV):Lyric:= Song.sQ (.use k.sealR (Bullet.snap brain))
def shine (k:MintV)(r:Rock q w h)(v:Tags):Cog:=
   let p:=campk (Mold.knob r v)
   Song.pleas (mature r.w) (roost p (sourceP k) 0) (snow p 0)
abbrev promptV(k:MintV)(r:Rock q w h)(v:Tags):Cog:=Studio.arrange (fun _=>shine k r v) 1
abbrev coal:=powder 100+Bullet.roomS+4
def render(k:MintV):ℕ:=let x:=reset (sourceP k) 0; coal+x.tail+x.cost coal
lemma wealthy(k:MintV):
    let x:=reset (sourceP k) 0; x.tail ≤render k∧x.cost coal ≤render k∧coal ≤ render k∧
                          4 ≤ coal∧powder 100 ≤ coal∧ Bullet.roomS ≤ coal:=by
    intro x; have ha:4 ≤ coal∧powder 100 ≤ coal∧Bullet.roomS ≤coal:=
           ⟨Nat.le_add_left ..,by change powder 100 ≤ powder 100+_+4;omega,
              by change Bullet.roomS ≤ powder 100+_+4;omega⟩
    refine ⟨?_,?_,?_,ha⟩ <;> (change _ ≤ coal+x.tail+x.cost coal;omega)
end Ma
namespace OrbitV
variable {u:Line (q:=q) (w:=w) (h:=h)}
abbrev topE (v:OrbitV u):=v.channel 17 0
open Ma

namespace Counsel
variable {p:OrbitV u}{k:MintV} (he:p.Counsel k)
include he
omit he in
lemma due : u.D.D p.topE=1:= Vessel.OrbitV.Counsel.heightZ ..
omit he in
lemma working(x i:ℕ):
     (mature u.r.w).f u.x (Studio.stk u p.topE x i).info=decide p.works :=by
    let v:= (Studio.stk u p.topE x i)
    let q:= essence.f u.x v.info
    have hu:q= Foil.kit 17 (p.m,0) (bitV p.p) (enc (Print.issued p.dye)):=by
       change (dec (dec (enc ((_,_,_):Stool)):Stool).1:Crt)=_
       rw [Wire.eq]; exact Wire.eq _
    have hs:MV q=p.m:=by rw [hu]
    have hm:Age.styx q=bitV p.p:=by rw [hu]
    change decide (operateV u.w0 (MV q) (Age.styx q))=_
    simp only [decide_eq_decide]
    rw [hs,hm]
    unfold OrbitV.works Net.onQ operateV; rw [recovered]; simp only [decide_eq_true_eq];rfl
omit he in
lemma waltz {i:ℕ}(hi:i+1=Age.L p.m)(x:ℕ): brain.f u.x (Studio.stk u p.topE x 0).info=
     hole (p.channel 5 i) (hole 1 0):=by
    let B:= (Studio.stk u p.topE x 0)
    let q0:= essence.f u.x B.info
    have hu:q0= Foil.kit 17 (p.m,0) (bitV p.p) (enc (Print.issued p.dye)):=by
       change (dec (dec (enc ((_,_,_):Stool)):Stool).1:Crt)=_
       rw [Wire.eq]; exact Wire.eq _
    change hole (enc (stint q0 5 (lb (MV q0)-1))) _=_
    rw [hu,show lb (Age.MV _)-1=i from ?_]
    · rfl
    change Age.L p.m-1=i; omega

abbrev Hx (p:OrbitV u) := u.D.high p.topE
abbrev Hpay(p:OrbitV u)(k:MintV):= Hx p+render k
abbrev Home(p:OrbitV u)(x:ℕ):=Studio.stk u p.topE x 0
abbrev visc (u:Line (q:=q) (w:=w) (h:=h)):=campk (knob u.r u.v)

lemma zen(pC:render k ≤ u.v.slope){x:ℕ}(hx:x∈u.D.P):Standard (Home p x) (visc u) (Hpay p k):=by
   have ht:= he.unitV
   have hP:Hpay p k≤ u.D.H:=by
        have hl:= Studio.stayedC ht le_rfl pC; rwa [(Vessel.OrbitV.Counsel.due (p := p)),mul_one] at hl
   exact ⟨Studio.positioned ht hx 0 0,spanFilm (Studio.vital _ hP) ..⟩
lemma piecewise {i:ℕ}(hi:i+1=Age.L p.m)(pC:render k ≤ u.v.slope){x:ℕ}(hx:x∈u.D.P)
   (hh:p.Earn k i x):
   Chor (visc u) coal (Hpay p k) (Home p x) (sourceP k) (smooth (p.actual k x (i+1))):=by
   let b:=p.channel 5 i; have ht:= he.unitV
   have hd:u.D.D b=1∧ u.D.W b+1 ≤ u.D.W p.topE:= by
         change u.D.D (p.channel 5 i) =_∧ u.D.W (p.channel 5 i)+_≤u.D.W (p.channel 17 0)
         rw [Vessel.OrbitV.Counsel.heightZ, Vessel.OrbitV.Counsel.costZ,Vessel.OrbitV.Counsel.costZ];exact Age.endbirth hi (by decide) (by decide) (by decide)
   have hW:u.D.W b+u.D.D p.topE ≤ u.D.W p.topE:=by rw [(Vessel.OrbitV.Counsel.due (p := p))];exact hd.2
   have htB:Hpay p k ≤u.D.high b:=by have hw:= Studio.soonerC ht hW pC le_rfl; rwa [(Vessel.OrbitV.Counsel.due (p := p)),mul_one] at hw
   apply Arena.Song.Paint.between0 (he.zen pC hx)
   apply Chor.byear
   have h6:Bullet.roomS ≤ coal:=(wealthy k).2.2.2.2.2
   apply Bullet.clef u.D ht h6 hx hW (Vessel.OrbitV.Counsel.waltz hi x) htB
   rw [show u.D.D p.topE=u.D.D b from (Vessel.OrbitV.Counsel.due (p := p)).trans hd.1.symm]
   exact hh.untilX

lemma liveF {i:ℕ}(hi:i+1=Age.L p.m)(pC:render k ≤ u.v.slope){x:ℕ}(hx:x∈u.D.P)
   (hs:p.works)(hh:p.Earn k i x):
    (Home p x).band (render k) (Hx p) 0 (shine k u.r u.v) (p.fwd0 x):=by
   have hc:=he.piecewise hi pC hx hh
   let H:= Hx p; let T:= Hpay p k
   let s:= Home p x
   let y:=p.actual k x
   obtain ⟨hp,hu'⟩:= hh
   obtain ⟨h1,h2,h3,h4,h5,h6⟩:= wealthy k
   have hu: 1 ≤ coal:=le_trans (by omega) h4
   apply Song.pinTrue (mature u.w0) ((Vessel.OrbitV.Counsel.working x 0).trans (decide_eq_true hs))
   have he1 :p.fwd0 x=smooth (y (i+1)):= by
             have he2:p.VoteM k x (Age.L p.m):=by rwa [←hi]
             rw [p.settle he2 hs he.till.saving.tested,hi]
   rw [he1]
   have hv:s.d=1:= (Vessel.OrbitV.Counsel.due (p := p))
   have hK:H+(reset (sourceP k) 0).tail*s.d≤T:=by
                rw [hv,mul_one]; exact Nat.add_le_add_left h1 _
   have hL: |smooth (y (i+1))| ≤ massB 0 s.d:=by
                 have hz:= unit_mem (y (i+1)); exact (abs_of_nonneg hz.1).le.trans (le_trans hz.2 (mass1 ..))
   exact Amber.onQ _ (sourceP k) _ (he.zen pC hx) hc hu hK h2 hL
lemma deadL(pC:render k ≤ u.v.slope){x:ℕ}(hx:x∈u.D.P)(hs:¬p.works):
    (Home p x).band (render k) (Hx p) 0 (shine k u.r u.v) (p.fwd0 x):=by
       apply Song.pinFalse (mature u.w0) ((Vessel.OrbitV.Counsel.working x 0).trans (decide_eq_false hs))
       have hh:p.fwd0 x=0:= by
         unfold fwd0 forecast current; dsimp only; rw [ite_eq_right (show ¬Net.onQ u.plotM.gap p.m (p.p.key u.plotM)=true from hs)]
       obtain ⟨h1,h2,h3,h4,h5,h6⟩:= wealthy k
       have hu: 1 ≤ coal:=le_trans (by omega) h4
       rw [hh]
       exact flex (steam _ _ (he.zen pC hx) (show powder 100 ≤ coal from h5)) hu h3 (Nat.le_add_right ..)
lemma smallC :u.smallQ p.topE 0:=by
       change lb 0 ≤ u.eye.e*u.D.D _
       have hc:= he.till.cost0
       rw [lb_zero,(Vessel.OrbitV.Counsel.due (p := p)),mul_one]
       exact le_trans (by unfold Bank.hx Bank.hu Bank.hi; omega) hc
lemma lever (pC:render k ≤ u.v.slope)
   (hs:Studio.Parcel u p.topE (promptV k u.r u.v)){x:ℕ}
   (hQ:(Home p x).band (render k) (Hx p) 0 (shine k u.r u.v) (p.fwd0 x)):
   u.D.Voice p.topE x (hole 1 0) (Hx p) 0 (p.fwd0 x):=by
       have hx:= wealthy k
       have h2:2≤render k:=le_trans (show 2 ≤ coal from le_trans (by omega) hx.2.2.2.1) hx.2.2.1

       have hp:= Studio.scoreTicket (u:=u) (f:=fun _=>shine k u.r u.v) he.unitV
                (o:=1) (m:=1) (by omega) (by omega) he.smallC h2 pC le_rfl hQ hs

       simpa only [Nat.zero_mul] using hp
lemma knownEnd (pC:render k ≤ u.v.slope)
   (hs:Studio.Parcel u p.topE (promptV k u.r u.v))
   (h:p.works → ∀ i:ℕ,i+1=Age.L p.m → ∀ x∈u.D.P,p.Earn k i x):
   p.FEnd:=by
       intro x hx
       apply he.lever pC hs
       by_cases ht0:p.works
       · let i:=Age.L p.m-1
         have he0:i+1=Age.L p.m:=by unfold i Age.L;omega
         exact he.liveF he0 pC hx ht0 (h ht0 _ he0 x hx)
       exact he.deadL pC hx ht0
end Counsel
end OrbitV
end
end ExactDerandomization.Vessel

end

end OAI
