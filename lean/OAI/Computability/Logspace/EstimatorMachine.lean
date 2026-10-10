import OAI.Computability.Logspace.EstimatorInstructions

namespace OAI

/-!
The finite estimator program and its instruction-level resource contracts.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.SiteX
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
noncomputable section

variable {q w h:ℕ}

structure Line where
    r:Rock q w h
    v:Tags
    s:Stash
    x:Word
namespace Line

variable (u:Line (q:=q) (w:=w) (h:=h))
abbrev prog:=woven u.r u.v u.s
abbrev D:=stageC u.r u.v u.x u.prog
abbrev eye:=field u.r u.v u.x u.prog
abbrev torch:= Helix.Torch.harp u.r u.v (coneX u.r u.s.pave)
abbrev wick0:= wick u.r u.v u.x u.prog
abbrev n:= u.r.n u.x
abbrev w0 :=u.r.w
abbrev B := u.r.B u.x
abbrev m:=u.r.matter0 u.x
abbrev plotM:= u.m.s
abbrev limitM:= u.w0.top u.B

lemma poss (s:Pool u.n) : Print.publish u.n (enc (Print.issued s))=true:=
        (mem_filter.1 (Print.entry _)).2
def clr (a:Scout)(m p i:ℕ) (x:Pool u.n): ℕ:=
        enc (kit p (m,i) a (enc (Print.issued x)))
def rowL (a:Quest):= u.clr (bitR a)
def vecL (v:Peek):=u.clr (bitV v)

structure Chart : Prop where
   ok : ∃ p:u.w0.Proof, u.m.ready p
   slopeX : max 6 (10*u.eye.e)  ≤  u.v.slope

namespace Chart
variable {u:Line (q:=q) (w:=w) (h:=h)}(h0:u.Chart)
include h0
lemma sc : u.plotM.SetUp:=by obtain ⟨p,h⟩:=h0.ok; exact u.m.lineup h
lemma above6 :6  ≤  u.v.slope:=(le_max_left ..).trans h0.slopeX
lemma draft {a:ℕ}(hp:licensed u.r u.x a) : u.D.Suite a:= dawn u.r u.v u.x u.prog _ hp
                                        ((by omega:2 ≤ 6).trans h0.above6)
lemma rent {a}(he:u.D.active a) : u.D.Suite a:= h0.draft ((by classical exact of_decide_eq_true he))
lemma e0 : u.D.Suite 0:= h0.draft (Or.inl rfl)
omit h0 in
lemma auth(a): u.D.active a↔ licensed u.r u.x a:= by classical exact decide_eq_true_iff
omit h0 in
lemma cred (c:Scout)(p s a:ℕ)(x:Pool u.n) :
    u.D.active (u.clr c p s a x) ↔
      permit u.w0 u.B u.n (kit s (p,a) c (enc (Print.issued x))):=by
    rw [(auth (u := u))]; simp only [licensed,clr, Age.cpos,dec_round,and_true,false_or]
omit h0 in
lemma courseR {p:Quest}{s a j:ℕ} (x:Pool u.n):u.D.active (u.rowL p s a j x)↔
    s ≤ u.limitM ∧ j<Age.Period s a∧rowUnit u.w0 a s (bitR p)∧p.ready u.plotM s:=by
   unfold rowL; rw [(cred (u := u))]; unfold permit
   have he:¬vecUnit u.w0 a s (bitR p):= fun hv=> solely (rightR p) hv.1
   have hp : testR u.w0 s u.B (roof u.r u.x) (bitR p) ↔ p.ready u.plotM s:=by
        unfold testR; rw [recovery]; rfl
   simp only [Age.g,Age.styx,Age.env,u.poss,hp,he,false_and,true_and,or_false]

omit h0 in
lemma courseV {p:Peek}{s a j:ℕ} (x:Pool u.n):u.D.active (u.vecL p s a j x)↔
    s ≤ u.limitM ∧ j<Age.Period s a∧vecUnit u.w0 a s (bitV p)∧p.ready u.plotM s:=by
   unfold vecL; rw [(cred (u := u))]; unfold permit
   have he:¬rowUnit u.w0 a s (bitV p):= fun hv=> solely hv.1 (rightV p)
   have hp : testV u.w0 s u.B (roof u.r u.x) (bitV p) ↔ p.ready u.plotM s:=by
        unfold testV; rw [recovered]; cases p with | mk i u k => cases k <;> rfl
   simp only [Age.g,Age.styx,Age.env,u.poss,hp,he,false_and,true_and,false_or]

omit h0 in
lemma parse {a}(he:u.D.active a)(ha:a≠0):
       (∃ p s i j x, a=u.rowL p s i j x) ∨ ∃ p s i j x,a=u.vecL p s i j x:=by
   obtain ⟨hk,hA⟩:= (((auth (u := u)) _).1 he).resolve_left ha
   generalize hm : (dec a:Crt)=v at *
   obtain ⟨r,⟨c,e⟩,s,b⟩:=v
   have hv :Print.publish u.n b=true:= hk.1
   change decide _=_ at hv
   obtain ⟨hz,hB⟩:= of_decide_eq_true hv
   obtain ⟨x,hi⟩:= Print.fill _ hz
   have hh:enc (Print.issued x)=b:=by rw [hi,hB]
   rw [←hA]
   rcases hk.2.2.2 with ⟨hj,_⟩|⟨hj,_⟩
   · refine Or.inl ⟨claim s,c,r,e,x,?_⟩
     unfold rowL clr; rw [copyR (show faceR s from hj.1),hh]
   refine Or.inr ⟨gaze s,c,r,e,x,?_⟩
   unfold vecL clr; rw [copyV (show faceV s from hj.1),hh]
omit h0 in
lemma walls {a q}(he:u.D.active a)(hp:unitK q=a): who q ≤ 17:=by
   unfold who; rw [hp]; split
   · omega
   next ht=>
     obtain ⟨hs,hv⟩:= (((auth (u := u)) a).1 he).resolve_left ht
     apply Mold.sizeR _ u.x
     rw [Mold.unitV,show enc (uphold a)=a from hv]
     exact Or.inr ⟨hs,hv⟩
omit h0 in
lemma assigned {a q b c v i j}(he:u.D.active a)(hp:unitK q=a)
     (hx:Lot.Mane u.D.l c v b q (codeRank u.r u.v u.s (who q)) i j):Lot.Mane u.D.l c v b q u.prog i j:=
        seated u.r u.v u.s hx ((walls (u := u)) he hp)

lemma chamber {a}(he:u.D.active a)(hu:u.D.Heard a)(hz:∀ b,u.D.active b→u.D.W b< u.D.W a→
                                                         u.D.won b 0→u.wick0.Veil u.torch b):
      u.wick0.Veil u.torch a:=by
   let p:=u.torch; let r:=u.D; let s:=u.wick0
   have hS : Harp.Wick.Life p s:= Helix.Torch.life _ _ _ _ _ (by have:=h0.above6; omega)
   have hD:= h0.rent he
   apply Harp.Wick.Life.veiled hS hD hu hz
   · exact (le_max_right ..).trans h0.slopeX
   · intro i q hm hA
     exact chask _ u.v u.x u.prog a i q he hA.under0 hm
   intro i q h6 hB x y hy
   have hh:unitK (Harp.quoteQ a i q)=a:=bellU ..
   apply (Line.Chart.assigned (u := u)) he hh
   have hb := hB.tokenpoint
   change decide ((uphold a).1=2∨_) = true at hb
   replace hb:=of_decide_eq_true hb
   have hp0 :a≠0:=by
      intro hp; subst a

      have H : (uphold 0).1=0:=rfl
      grind
   unfold who; rw [hh,ite_eq_right hp0]
   unfold codeRank; rw [ite_eq_right (by omega),ite_eq_left hb]; exact hy

end Chart
end Line
end
end ExactDerandomization.SiteX

end

section

namespace ExactDerandomization.SiteX
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX
noncomputable section
open scoped Classical
variable {q w h:ℕ}
namespace Line
variable (u:Line (q:=q) (w:=w) (h:=h))
def smallQ (a i:ℕ):Prop:= u.eye.wideQ a i
lemma Launch {a}(he:u.D.active a) (i o t:ℕ)(hv:u.smallQ a i)(ho:o ≤ 32)(ht:t ≤ u.D.high a):
      post a o i t ≤  u.D.F.limit:= Night.localC _ _ _ _ _ _ _ _ he hv ho ht
lemma Voices (a o i t:ℕ)(he:u.D.audible (post a o i t)):
   taps (uphold a).1 o t ∧ u.smallQ a i:=by
    have he:= of_decide_eq_true (show decide (entitled u.r u.v u.x (post a o i t))=true from he)
    have hv:=he.2.2.2
    change taps (uphold (unitK (post a o i t))).1 (opt _) (date _)∧ lb _  ≤  _ at hv
    rw [optionX,bellU,targetX,bellT] at hv; exact hv
lemma spokenC {a}(he:u.D.active a)(hz:a≠0)(o i t:ℕ)(hp:u.smallQ a i)
    (hf:taps (uphold a).1 o t):u.D.audible (post a o i t):=by
    refine decide_eq_true ?_
    change entitled _ u.v u.x _
    unfold entitled
    dsimp only
    rw [optionX,targetX,bellU,bellT]
    exact ⟨hz,of_decide_eq_true he,rfl,hf,hp⟩

/- reusable request-origin signature. all indices in the allotted range, incl holes. -/
structure CageQ where
     dataN:ℕ
     visN:ℕ
     tagop:ℕ
     m:ℕ
namespace CageQ
variable (p:CageQ)
structure Front : Prop where
     pos:u.D.active p.dataN
     path:u.D.active p.visN
     baseC: u.eye.e ≥4
     price:u.D.W p.dataN+u.D.D p.visN ≤ u.D.W p.visN
     grain : u.D.D p.dataN=u.D.D p.visN
     size0 : ∀ i<p.m,u.smallQ p.visN i
     tip : (coneX u.r u.s.pave).ispath0.f u.x p.visN=true
     ear0 : ∀ i,(coneX u.r u.s.pave).spur.f u.x (p.visN,i)=post p.dataN p.tagop i 0
     aloud :∀ i,u.smallQ p.visN i→u.D.audible (post p.dataN p.tagop i 0)

namespace Front
variable {u:Line (q:=q) (w:=w) (h:=h)}{p:CageQ}(he:Front u p)
include he
lemma awake {i} (hi:u.smallQ p.visN i):u.smallQ p.dataN i:=by
      unfold smallQ ConeX.wideQ at *; change _ ≤ u.eye.e*u.D.D p.visN at hi
      change _ ≤ u.eye.e*u.D.D p.dataN; rwa [he.grain]
lemma back0 {i} (hi:u.smallQ p.dataN i):u.smallQ p.visN i:=by
      unfold smallQ ConeX.wideQ at *; change _ ≤ u.eye.e*u.D.D p.dataN at hi
      change _ ≤ u.eye.e*u.D.D p.visN; rwa [← he.grain]

lemma point0(h0:u.Chart) (i:ℕ)(hp:u.smallQ p.visN i): u.eye.BaseX u.torch.p p.visN i:=by
    have hx:= h0.rent he.path
    have ht:u.eye.ear u.torch.p p.visN i=post p.dataN p.tagop i 0:=he.ear0 i
    refine ⟨he.baseC,⟨he.path,hx.well.1,hx.well.2,topo_hi _ _ _ _ _ he.path⟩,hp,?_,?_ ,?_ ,?_,he.tip⟩
    · exact highflex u.r u.x p.visN (of_decide_eq_true he.path)
    · rw [ht]; exact he.aloud i hp
    · rw [ht,bellT]
    unfold ConeX.less; rw [ht,bellU]; exact he.price

end Front

structure Trace (x:ℕ)(tag wherep:ℕ→ℕ) :Prop where
    next :∀ i,u.smallQ p.dataN i → u.D.swears (post p.dataN p.tagop i 0) x (tag i)
    fits :∀ i,u.smallQ p.dataN i → u.smallQ p.visN (tag i)
    maxm:∀ i,p.m ≤ i→ tag i=0
    road:∀ i,u.smallQ p.dataN i→u.eye.Flora u.torch.p p.visN i x
                                            (if tag i=0 then none else some (tag i,wherep i))

structure Offer (x:ℕ)(q k:ℕ)(F:ℕ→ℝ):Prop where
     ready :∀ i,u.smallQ p.dataN i→ u.D.Voice p.dataN x (hole q i) (u.D.high p.dataN) (k*u.D.D p.dataN) (F i)
namespace Trace
variable {u:Line (q:=q) (w:=w) (h:=h)}{p:CageQ}
lemma distinct_path {x a f b g} (hA:Trace u p x a f)(hB:Trace u p x b g)(i:ℕ)(hk:u.smallQ p.dataN i):
     a i=b i := (u.D.identity (hA.next _ hk)).symm.trans (u.D.identity (hB.next _ hk))
lemma caseM {x a f} (hA:Trace u p x a f)(i:ℕ)(hi:a i≠0)(hk:u.smallQ p.dataN i):
     u.eye.Pond u.torch.p p.visN i (a i) x (f i):=by
    have ht:=hA.road i hk; rw [ite_eq_right hi] at ht; cases ht
    assumption
lemma places {x a f} (hA:Trace u p x a f)(i:ℕ)(hi:a i≠0)(hk:u.smallQ p.dataN i):
    f i∈ u.D.P := by cases hA.caseM i hi hk with
                      | leaf h0 _=> exact h0.hy
                      | born h0 _ _ _ _=> exact h0.hy
end Trace
end CageQ

/-- Cocoon. Universal micromoves on alpha 0. -/
abbrev atom0 := Was.atom 0
namespace Chart
variable {u:Line (q:=q) (w:=w) (h:=h)}(h0:u.Chart)
include h0
lemma bootsBasic (i:ℕ):u.D.Streams (Was.atom i) (Was.stopped u.r u.x i):=by
   apply Was.motion _ _ _ _ h0.above6
   intro b i j a m hp
   have hl:unitK (Was.packB b i j)=0:=bellU ..
   refine (Line.Chart.assigned (u := u)) h0.e0.stage hl ?_
   unfold who; rw [ite_eq_left hl]
   exact hp

omit h0 in
lemma voteRoot {i j} (hi:i  ≤  u.v.bonus)(hj:j  ≤  u.v.bonus):u.D.dual (Was.atom i) j:=by
     apply decide_eq_true
     unfold paired
     simp only [cell,Scheme.inside,Was.atom,hole,dec_round,ite_true]; exact ⟨True.intro,hi,hj⟩
lemma basic0 {i j x y:ℕ}(hm:Was.Flight u.r u.x i j x y)(hi:i ≤  u.v.bonus)(hj:j ≤ u.v.bonus):
     u.D.curve (Was.atom i) j true x=some y:=by
   have ht: u.n=u.D.peak:=rfl
   rw [(h0.bootsBasic i).lines ((voteRoot (u := u)) hi hj) (show x∈ u.D.P from mem_range.2
                                                            (Nat.lt_succ_of_le hm.1))]
   exact (Was.travel u.r ..).2 hm

omit h0 in
lemma holdX {a i x m _ y:ℕ}
   (_:x∈u.D.P)(hm:u.eye.ear u.torch.p a i=m) (he:u.D.swears m x y):
    u.D.echo (u.eye.ear u.torch.p a i) x=y:= hm ▸ (u.D.identity he)
lemma Rope {p:CageQ}(ht:p.Front u) (i x h j a c m:ℕ)
    (he:u.smallQ p.dataN i) (hr:u.smallQ p.visN h)(hs:h≠0)(hi:x∈u.D.P)
    (hv:offer u.s.pave u.x (stem p.visN i h) =rope a j)
    (hA : u.D.W 0+u.D.D p.visN ≤ u.D.W p.visN)
    (hB:u.D.W a+u.D.D p.visN  ≤  u.D.W p.visN)
    (hD:u.D.D a  ≤ 2*u.D.D p.visN)(hc:c∈u.D.P)
    (hh:u.D.swears (post p.dataN p.tagop i 0) x h)
    (ho:u.eye.Pond u.torch.p a j m x c):
    u.eye.Flora u.torch.p p.visN i x (some (h,c)):=by
   let z:=u.eye; let v:=u.torch.p; let L:=stem p.visN i h
   have hQ : z.h0 v p.visN i h=Was.atom 0 ∧ z.f0 v p.visN i h=Was.atom 0
        ∧z.ip v p.visN i h=0 ∧v.shift.f z.D.x L=(1,0) ∧ z.b1 v p.visN i h=true ∧
         z.s1 v p.visN i h=a ∧ z.i1 v p.visN i h=j:=by
      let w:=offer u.s.pave u.x L
      change w.1.1=_∧ w.2.2.1=_∧w.1.2=_∧ w.2.2.2=_∧w.2.1.1=_∧w.2.1.2.1=_∧w.2.1.2.2=_
      have hr : w=rope a j:=hv; simp [hr,rope]
   obtain ⟨hU,hV,hZ,hf,hj,ha,hW⟩:=hQ
   have hp:=ht.point0 h0 i (ht.back0 he)
   have hS(z:ℕ)(hz:z∈u.D.P):u.D.curve (Was.atom 0) 0 true z=some z:=by
       apply h0.basic0 _ (Nat.zero_le _) (Nat.zero_le _)
       have hc : z ≤ u.n:=by exact Nat.le_of_lt_succ (mem_range.1 hz)
       simp [Was.Flight,hc]
   have hY:z.Allow p.visN (Was.atom 0) 0:=by
      refine ⟨(voteRoot (u := u)) (Nat.zero_le _) (Nat.zero_le _),?_⟩
      unfold Was.atom; rw [show cell (hole 0 0)=0 by simp [cell,hole]]
      exact hA
   apply Flora.wet
   apply Pond.born (m:=x) (m':=c) ?_ hj ?_ ?_ (h':=m) ?_
   · have hg: c ≤ z.D.peak:=Nat.le_of_lt_succ (mem_range.1 hc)
     refine ⟨hp,hs,?_,hr,?_,?_,?_,hi,hi,hc,hc,?_,?_,?_⟩
     · change z.D.echo (u.eye.ear _ _ _) _ = _
       rw [show u.eye.ear u.torch.p p.visN i=post p.dataN p.tagop i 0 from ht.ear0 i]
       exact u.D.identity hh
     · rw [hZ]; unfold wideQ; rw [lb_zero]; have hv:=hp.posX; have hs:=hp.lowp.2.1
       nlinarith
     · rw [hZ,hU]; exact hY
     · rw [hV]; exact hY
     · rw [hZ,hU]; exact hS x hi
     · rw [hV]; exact hS c hc
     change min _ ((v.shift.f z.D.x L).1*c+(v.shift.f z.D.x L).2)=_
     rw [hf]; simp [hg]
   · rw [ha]; exact hB
   · rw [ha]; exact hD
   rw [ha,hW]; exact ho
end Chart
end Line
end
end ExactDerandomization.SiteX

end

section

namespace ExactDerandomization.SiteX
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf
noncomputable section

/- Scalar prices determined before unfolding predecessor calls. -/
structure MintV where
    coin:ℕ
    vol:ℕ
    sealR:ℕ
    low:ℕ
namespace MintV
def prism (p:MintV) := 20+2*p.coin
abbrev tokenH (p:MintV) := p.vol+p.prism
abbrev inputH (p:MintV) := 3*p.sealR
def rangeN (p:MintV)(d:ℕ):ℕ:=2^(p.vol*d)
abbrev roofX (p:MintV)(d:ℕ):ℝ:=massB p.sealR d

def shellQ(p:MintV)(m i:ℕ):ℝ:=p.roofX (if i=0 then 2*gap m 0 else gap m (i-1))
lemma shore (p:MintV)(m i:ℕ): p.shellQ m (i+1)=p.roofX (gap m i):=by simp [shellQ]
lemma shorn (p:MintV)(m i:ℕ) (h:i<Age.L m): p.shellQ m i=p.roofX (2*gap m i):=by
   cases i with
   | zero=>rfl
   | succ i=>simp only [p.shore,gap_step h]
def fine (p:MintV):Prop:=4  ≤  p.sealR ∧ p.tokenH ≤  p.sealR
lemma fluc (p:MintV){d:ℕ}(h:p.fine)(hp:1  ≤  d):16  ≤  p.roofX d:=by
    have he: 4 ≤ p.sealR*d:=by have:=h.1; nlinarith
    calc
      (16:ℝ)  ≤  2^(4:ℕ):=by norm_num
      _  ≤  _ := pow_le_pow_right₀ (by norm_num) he
lemma decor (p:MintV){m i:ℕ}(h:p.fine)(hi:i<Age.L m)(v:At.Pt)
    (he: ht v  ≤  massB p.tokenH (gap m i)):
    ht v+p.shellQ m (i+1)  ≤  p.shellQ m i:=by
   let d:=gap m i
   rw [p.shore,p.shorn m i hi]
   have hp:= p.fluc h (d:=d) (gap_pos ..)
   have hu:ht v ≤  p.roofX d:=he.trans (mass_mono h.2 _)
   change ht v + p.roofX d  ≤  p.roofX (2*d)
   have hx:p.roofX (2*d)=p.roofX d*p.roofX d:=by unfold roofX massB; rw [←pow_add]; congr 1; ring
   rw [hx]; nlinarith
end MintV
open MintV
variable {q w h:ℕ}

namespace Line
variable (u:Line (q:=q) (w:=w) (h:=h))

@[simp] lemma rolff (a:Scout)(m c i:ℕ)(x:Pool u.n):
      Age.D (u.clr a m c i x)=slackT m c i:= by unfold clr; rw [DI]; rfl
@[simp] lemma rolfe(a m c i x): Age.W (u.clr a m c i x)=weight m c i:=by unfold clr; rw [WI]; rfl

structure Fabric where
     t:Quest
     m:ℕ
     dye:Pool u.n
namespace Fabric
variable {u:Line (q:=q) (w:=w) (h:=h)}
variable (v:Fabric u)
abbrev roll:= rolls u.plotM v.m
abbrev frame := v.t.flame u.plotM v.roll v.m
abbrev c(i g:ℕ):= u.rowL v.t v.m i g v.dye
def activeR:=onQ u.w0.A0 v.m (v.t.key u.plotM)=true
abbrev world := v.frame.d
abbrev S0 := v.frame.src0 v.dye
abbrev S1 := v.frame.dst0 v.dye
abbrev S2 := v.frame.dst1 v.dye
abbrev marathon(x:ℕ): Buf.Run := v.frame.go v.dye x
lemma leg(x):(v.marathon x).L=Age.L v.m:=rfl
abbrev tagged(c:ℕ): Bool := decide (c ≤ 4)
abbrev govern := v.t.tag.narrow
def Good:= v.m ≤ u.limitM∧v.t.ready u.plotM v.m

lemma workR : v.activeR↔operateR u.w0 v.m (bitR v.t):=by
   unfold operateR; rw [recovery]; unfold activeR onQ Quest.key; simp only [decide_eq_true_eq]; rfl
namespace Good
variable {v:Fabric u}(e:u.Chart)(hu:v.Good)
include e hu
lemma booked {a b:ℕ}(hi:b < Age.Period v.m a)(he:rowUnit u.w0 a v.m (bitR v.t)):
     u.D.Suite (v.c a b):=e.rent (((Line.Chart.courseR (u := u)) v.dye).2 ⟨hu.1,hi,he,hu.2⟩)
lemma encs {i:ℕ}(hx:i∈ v.world.S):i< u.n:= mem_range.1 (e.sc.ids _ hu.2.1 hx)
lemma n0 {i:ℕ}(hx:i∈ v.S0):i∈u.D.P:= mem_range.2 ((encs e hu (mem_filter.1 hx).1).trans (by change u.n < u.n+1; omega))
lemma n1 {i:ℕ}(hx:i∈ v.S1):i∈u.D.P:= mem_range.2 ((encs e hu (mem_filter.1 hx).1).trans (by change u.n < u.n+1; omega))
end Good

structure HistoryC (v:Fabric u)(p:MintV)(x i:ℕ) where
    kap:ℕ→Bool
namespace HistoryC
variable {p:MintV}{x i:ℕ}
abbrev R (p:MintV)(v:Fabric u)(j:ℕ):ℝ:=p.roofX (gap v.m j)
abbrev actual (a:HistoryC v p x i)(j:ℕ):= (v.marathon x).actual (R p v) a.kap j
structure Compared (a:HistoryC v p x i) : Prop where
   cooling : ∀ j < i,a.kap j=true →1 ≤  ((v.marathon x).pm j).U ((v.marathon x).shifted j (actual v a j))
   shield : ∀ j < i,∀ y∈ (v.marathon x).S, ht ((v.marathon x).inc j y)  ≤  massB p.tokenH (gap v.m j)

lemma Compared.set {a:HistoryC v p x i}(h:Compared v a) (hi:i=Age.L v.m)(he:p.fine)
     {θ C f z} (hp:At.TS θ C f) (hh:θ  ≤ 1)(hc:C ≤  p.roofX 1)(hx:z∈(v.marathon x).S):
     (actual v a i).val (v.marathon x).S (v.marathon x).K f z=
                  ((v.marathon x).mid i).val (v.marathon x).S (v.marathon x).K f z := by
     unfold actual
     rw [← v.leg x] at hi
     subst i
     apply Run.clamped _ hp hh (p.shellQ v.m)
     · intro j hj
       let d:= if j=0 then 2*gap v.m 0 else gap v.m (j-1)
       have hx:1 ≤ d:=by
         unfold d; split; have :=gap_pos v.m 0; omega
         exact gap_pos ..
       refine ⟨le_trans hc ?_,?_⟩
       · change (2:ℝ)^_ ≤  (2:ℝ)^(p.sealR*d); gcongr; norm_num
       change 12 ≤  p.roofX d
       have he1:= p.fluc he hx; linarith
     · exact fun j _=>(p.shore v.m j).le
     · intro j hj y he0
       exact p.decor he hj _ (h.shield j hj y he0)
     · exact h.cooling
     exact hx

end HistoryC
end Fabric
end Line
end
end ExactDerandomization.SiteX

end

section

namespace ExactDerandomization.SiteX.Line
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV CageQ
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}

structure Producer where
    tag : ℕ→ℕ→ℕ
    locate : ℕ→ ℕ→ℕ
namespace Producer
variable (p:Producer)
abbrev awake (x i:ℕ):Prop:=p.tag x i≠0
def coversF(x i:ℕ): Option (ℕ×ℕ):= if p.awake x i then some (p.tag x i,p.locate x i) else none
def scoreF (M:Mat) (x i:ℕ): ℝ:= if p.awake x i then M x (p.locate x i) else 0
structure Light (p:Producer) (M:Mat)(S N:Domain):Prop where
   insured:∀ x i,p.awake x i→x∈S ∧ p.locate x i∈N
   fair:∀ x i j,p.awake x i→p.awake x j→p.locate x i=p.locate x j→i=j
   defend:∀ x y,M x y≠0→∃ i,p.awake x i∧p.locate x i=y
structure Quote (u:Line (q:=q) (w:=w) (h:=h))(v:CageQ)(M:Mat)(which k:ℕ):Prop where
   coil:CageQ.Front u v
   trace:∀ x∈ u.D.P,v.Trace u x (p.tag x) (p.locate x)
   voices:∀ x∈u.D.P,v.Offer u x which k (p.scoreF M x)

structure Certified (u:Line (q:=q) (w:=w) (h:=h))(v:CageQ)(M:Mat)(S N:Domain)(o k:ℕ):Prop where
     light:p.Light M S N
     suit:p.Quote u v M o k

namespace Quote
variable {p:Producer}{c M o k}(h0:Quote p u c M o k)
include h0
lemma orbit {i x:ℕ}(hi:i<c.m)(hr:x∈u.D.P):
     u.eye.Flora u.torch.p c.visN i x (p.coversF x i) := by
    have ht:= (h0.trace x hr).road i (h0.coil.awake (h0.coil.size0 _ hi))
    unfold coversF; by_cases hz:p.awake x i
    · rw [ite_eq_left hz]; rwa [ite_eq_right hz] at ht
    rw [ite_eq_right hz]; rwa [ite_eq_left (show p.tag x i=0 from by simpa only [Producer.awake,ne_eq,not_not] using hz)] at ht
lemma lacks {x i}(he:x∈u.D.P)(hi:p.awake x i):i<c.m:=lt_of_not_ge fun e=>hi ((h0.trace _ he).maxm i e)
end Quote
namespace Certified
variable {p:Producer}{c M S N o k}(h0:p.Certified u c M S N o k)
include h0
lemma supply (x y:ℕ)(he:x∈u.D.P):
   ∑ i∈ range c.m,(if p.locate x i=y then p.scoreF M x i else 0)=M x y:=by
    by_cases hp:M x y=0
    · rw [hp]
      apply sum_eq_zero; intro i hi; unfold scoreF
      unfold Producer.awake; grind
    obtain ⟨i,h,hx⟩:= h0.light.defend x y hp
    rw [sum_eq_single i]
    · unfold scoreF; rw [ite_eq_left hx,ite_eq_left h,hx]
    · intro j hj hz
      by_cases hg:p.locate x j=y
      · rw [ite_eq_left hg]; apply ite_eq_right; intro hh
        exact hz (h0.light.fair x j i hh h (hg.trans hx.symm))
      rw [ite_eq_right hg]
    intro hi; exact False.elim (hi (mem_range.2 (h0.suit.lacks he h)))
lemma pixels {x i}(he:x∈S)(hf:S⊆u.D.P):|p.scoreF M x i|  ≤  massB k (u.D.D c.dataN):=by
    by_cases ht:p.awake x i
    · have hz:= h0.suit.lacks (hf he) ht
      obtain ⟨v,hh,_⟩:= (h0.suit.voices x (hf he)).ready i (h0.suit.coil.awake (h0.suit.coil.size0 i hz))
      have he0:=hh.1
      change |_ / massB k (u.D.D c.dataN)| ≤ 1 at he0
      rwa [abs_div,abs_of_pos (mass0 ..),div_le_one (mass0 ..)] at he0
    unfold scoreF; rw [ite_eq_right ht]; simp only [abs_zero]; positivity
end Certified
end Producer

namespace Fabric
variable (v:Fabric u)
abbrev α (m:MintV)(i:ℕ) : CageQ:= ⟨v.c 1 i,v.c 2 i,0, m.rangeN (gap v.m i)⟩
abbrev Rslots(_:Fabric u) :=u.w0.p.K
abbrev Snum(i):= capacity 2 v.Rslots (Age.L v.m) i
abbrev β (i:ℕ): CageQ:=⟨v.c 3 i,v.c 4 i,0,v.Snum i⟩
abbrev terminal (b:Bool): CageQ:=⟨v.c 9 0, v.c (if b then 11 else 10) 0,if b then 3 else 0,v.Rslots⟩
abbrev leaveE : CageQ:= ⟨v.c 14 0,v.c 15 0,0,v.Rslots⟩
abbrev final0:= v.t.need u.plotM
abbrev finalE := (forecast u.plotM v.m).outR v.t v.dye
abbrev grid := (v.t.builder u.plotM).sess v.dye
abbrev trio(b:Bool):Trio:= if b then suppT v.t.tag.theta false else v.t.trio u.plotM
abbrev grains:= v.t.rowBlock u.plotM v.roll v.m v.dye
abbrev aimE(b:Bool):Mat:=v.grid.pre v.grains (v.trio b) false
abbrev heated (b:Bool):ℕ:= if b then 4 else 1
abbrev Tscale (p:MintV)(b:Bool):ℕ:= if b then 0 else p.coin

def slotWord (v:Fabric u)(i):=hole (v.c 12 0) i

structure Yolk (p:MintV)(i x:ℕ) where
    hist:HistoryC v p x i
    raw : Reed.Poolx
structure YFine (p:MintV)(i x:ℕ)(a:Yolk v p i x):Prop where
    compared:HistoryC.Compared v a.hist
    params:a.raw.p=(v.marathon x).pm i
    posed:a.raw.raw=(v.marathon x).shifted i (HistoryC.actual v a.hist i)
    ns:a.raw.m=(v.α p i).m
    nice:a.raw.Nice

    found:(v.α p i).Trace u x a.raw.tag a.raw.place
    hue:∀ b,(v.α p i).Offer u x (if b then 1 else 2) p.inputH (fun j=> Reed.sideq (a.raw.chip j) b)
    baseX:u.D.Voice (v.c 1 i) x (hole 5 0) (u.D.high (v.c 1 i)) (p.inputH*u.D.D (v.c 1 i)) a.raw.b
    cap : ∀ y∈(v.marathon x).S,ht ((v.marathon x).inc i y)  ≤  massB p.tokenH (gap v.m i)
    night:x∉v.S0→∀ i,a.raw.tag i=0

structure Hinge (p:MintV) (i x:ℕ) where
    hist:HistoryC v p x (i+1)
    depot:Stem.Depot
structure HFine (p:MintV)(i x:ℕ)(a:Hinge v p i x):Prop where
    y0 : HistoryC.Compared v a.hist
    ton : a.depot.y=HistoryC.actual v a.hist (i+1)
    dst : a.depot.S=v.S1
    card0:a.depot.n=v.Snum i
    solid:a.depot.Trust
    found:(v.β i).Trace u x a.depot.tag a.depot.pos
    hue:(∀ b,(v.β i).Offer u x (if b then 1 else 2) p.sealR (fun j=>Reed.sideq (a.depot.qpoint j) b))
    at0:u.D.Voice (v.c 3 i) x (hole 5 0) (u.D.high (v.c 3 i)) (p.sealR*u.D.D (v.c 3 i)) a.depot.y.base
    kill:x∉v.S0→∀ i,¬a.depot.live i

structure Tgood(p:MintV)(f:Bool→Producer):Prop where
   secure:∀ b,(f b).Certified u (v.terminal b) (v.aimE b) v.S0 v.S1 (heated b) (Tscale p b)
   seat :∀ x i,(f false).awake x i→ v.aimE true x ((f false).locate x i)=1

/-- mating on the pre-cap main ports. Captures baseline order by specifying only its needed invariants. -/
structure Profession (f:Producer)(tb:ℕ→ℕ→ℕ) :Prop where
     t1:u.D.active (v.c 12 0)
     bound : ∀ x i,tb x i ≠0 → f.awake x i ∧tb x i  ≤  clim u.w0.p
     quota :∀ x i,f.awake x i →
          (tb x i≠0 ↔ (u.D.P.filter (fun a=>∃ j, f.awake a j ∧ f.locate a j=f.locate x i)).card  ≤ clim u.w0.p)
     guide :∀ x∈ u.D.P,∀ i<v.Rslots,∀ t,0<t→ t ≤ clim u.w0.p→
        u.D.dual (v.slotWord i) t ∧
        u.D.Streams (v.slotWord i) (u.D.curve (v.slotWord i)) ∧
        u.D.curve (v.slotWord i) t true x= if tb x i=t then some (f.locate x i) else none

/-- Final matrix port operations, including paired information for echoes. -/
structure Efine (p:MintV)(f:Producer):Prop where
    sector:f.Certified u v.leaveE v.finalE v.S0 v.S1 1 p.coin
    ticket:u.D.active (v.c 12 0) ∨ v.govern=false
    tin : v.govern=true→∀ x i,f.awake x i→ f.tag x i ≤ clim u.w0.p
    source : v.govern=true→∀ i<v.Rslots,∀ t,0<t→ t ≤ clim u.w0.p→
           u.D.dual (v.slotWord i) t ∧
           u.D.Streams (v.slotWord i) (u.D.curve (v.slotWord i)) ∧
           ∀ x∈ u.D.P,u.D.curve (v.slotWord i) t true x=
                              if f.tag x i=t then some (f.locate x i) else none

end Fabric
end
end ExactDerandomization.SiteX.Line

end

section

namespace ExactDerandomization.SiteX
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV Line Line.Fabric
noncomputable section
namespace Label
abbrev gob (v:ℕ)(_:Word)(u:ℕ):ℕ:= pointer (unitK u) v
lemma gobK(v):Kn (gob v):= by
   have hp:=(Kn.unpack (α:=Crt)).comp unitK0
   exact Kn.wash.comp ((Kn.fix _).tuple hp.right)
abbrev PURE :ℕ:=30
variable {q w h:ℕ}(z: Rock q w h) (v:Tags)

def put (x:Word)(t:ℕ):ℕ:= min (2^T z v x) (2^date t)
lemma putK:Kn (put z v):= by
    have hp:= (stationK z v (α:=ℕ))
    exact Kn.cap hp (Kn.fix _) tokenK.right

def followP (l y :ℕ) (x:Word)(a:Mint.Bean):ℕ:=
    post (gob l x a.1) y a.2.1 (date a.1-a.2.2)
lemma followK(l y):Kn (followP l y):= by
    have h:= Kn.first (β:=Rill.History) (α:=ℕ)
    have hp:=Kn.wash.comp (((gobK l).comp h).tuple (Kn.wash.comp ((Kn.fix y).tuple Kn.next.left)))
    exact Kn.wash.comp (hp.tuple (((tokenK.right).comp h).sub Kn.next.right))
def roadX (cap0:Bool) (i l y:ℕ):Road:=
    ⟨⟨_,gobK i⟩,⟨_,Kn.fix z.w.p.K⟩, if cap0 then ⟨_,Kn.fix 0⟩ else ⟨_,tokenK.right.succ⟩,
        ⟨_,followK l y⟩,if cap0 then ⟨_,Kn.fix 0⟩ else ⟨_,padK ⟨_,putK z v⟩⟩⟩
end Label

namespace Line
namespace Fabric
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
open Label
variable (v:Fabric u)

lemma pointerot (a b:ℕ):pointer (v.c a 0) b=v.c b 0:=by
   unfold c rowL clr pointer; rw [Wire.eq]
@[simp] lemma awayT (a i o t b): gob b u.x (post (v.c a 0) o i t)=v.c b 0:=by
   rw [gob,bellU,v.pointerot]

def diva (p:Fabric u) (f:Producer)(κ unitα l v α :ℕ) (cap0:Bool) : Ember:=
      ⟨u.eye,u.torch.p,roadX u.r u.v cap0 v l α,p.c v 0,p.Rslots,κ,u.v.A,p.c unitα 0,
                     hole Label.PURE 0,f.coversF⟩
lemma weightEnd (a)(ha:¬ Brole a): u.D.W (v.c a 0)=128*(v.m+1)-(64-a)*1:=by
    change Age.W _=_
    unfold c rowL clr; rw [WI]; unfold act weight slackT
    rw [ite_eq_right (show ¬Brole a from ha)]
lemma ageEnd (a)(ha:¬ Brole a):u.D.D (v.c a 0)=1:=by
    unfold c rowL; change Age.D _=_
    rw [Line.rolff,slackT,ite_eq_right ha]
lemma parentL {a b}(hi:¬ Brole a)(he:a<b)(hk:b ≤ 64):
    u.D.W (v.c a 0)+1 ≤ u.D.W (v.c b 0):=by
   have hB:¬Brole b:=by unfold Brole at *; omega
   rw [weightEnd v a hi,v.weightEnd _ hB]
   omega
structure Mantle (κ:ℕ):Prop where
    chart:u.Chart
    k :100  ≤  κ
    space0:lb capD  ≤  κ
    grade: 100*u.eye.e ≤ κ
    grown:1000*κ^2  ≤  u.v.A
    heat:u.v.A  ≤  u.v.slope
    holdp:∀ i<v.Rslots,lb i ≤ κ

namespace Mantle
variable {v:Fabric u}{κ:ℕ}(h0:Mantle v κ)
include h0
lemma ties {unitα a l α:ℕ} (ha:¬Brole a) (he:a<unitα)(hl:unitα  ≤ 64)(b:Bool){f M o x z}
   (hg:Producer.Quote f u
            (CageQ.mk (v.c l 0) (v.c a 0) z v.Rslots) M o x)
   (hp:u.D.Suite (v.c unitα 0))(hh:u.D.Heard (v.c unitα 0)):
   (v.diva f κ unitα l a α b).Trust:=by
   exact ⟨hp,hh,v.ageEnd _ (by unfold Brole at *; omega),v.ageEnd _ ha,
          Nat.le_trans (Nat.le_add_right ..) (v.parentL ha he hl),h0.k,h0.grade,h0.grown,h0.heat,h0.holdp,
                              fun x hx y hy=>hg.orbit hy hx⟩
lemma bridge {unitα a l α t:ℕ}(b:Bool)(f:Producer)(h:u.D.active (v.c unitα 0))
      (he:t  ≤  u.D.high (v.c unitα 0)) :
    (v.diva f κ unitα l a α b).Bridge t := by
   let p:=v.diva f κ unitα l a α b

   refine ⟨he,?_,le_rfl,rfl,?_,?_⟩
   · exact v.awayT ..
   · cases b
     · change date (post (v.c unitα 0) PURE 0 t) + 1 ≤ t + κ
       rw [bellT]; have hz:=h0.k; omega
     change 0 ≤ _; omega
   change 2^(charge _ (Age.W (v.c unitα 0)) t)  ≤ 2^charge u.v.A (planets u.r u.x) (T u.r u.v u.x)
   apply Nat.pow_le_pow_right (by omega)
   have hs:=licensedW u.r ((Line.Chart.auth (u := u) (v.c unitα 0)).1 h)
   have hL := Night.cap_time u.r u.v u.x u.prog (v.c unitα 0) t he
   change charge u.v.A (Age.W (v.c unitα 0)) t  ≤ _
   unfold charge; gcongr
end Mantle

end Fabric
end Line
end
end ExactDerandomization.SiteX

end

section

namespace ExactDerandomization.SiteX
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV Line Line.Fabric Producer
open Fret.Seats Reed
noncomputable section

namespace Studio
/-- allocate main's body by operation tags. -/
def stacc (q:ℕ)(u:ℕ):ℕ:=enc ((q,u,0):Reed.Stool)
def collapse (_:Word)(q:ℕ):ℕ:= postcard (stacc (unitK q) (posn q)) (date q)
lemma lidK:Kn (fun (_:Word) q=>posn q):=tokenK.right.comp (tokenK.right.comp tokenK.left)
lemma oK:Kn (fun (_:Word) q=>opt q):=tokenK.left.comp (tokenK.right.comp tokenK.left)
lemma collapseK:Kn collapse:=
   Kn.wash.comp ((Kn.wash.comp (unitK0.tuple (lidK.tuple (Kn.fix 0)))).tuple tokenK.right)
def erode (p:Cog):Cog:=Cog.ren ⟨_,collapseK⟩ p
def enter(p:ℕ):Relay.Flag:= ⟨_,(oK.comp Kn.first).eq (Kn.fix p)⟩
def arrange (f:ℕ → Cog):ℕ → Cog
   | 0=>erode (f 0)
   | i+1=> .bif (enter (i+1)) (erode (f (i+1))) (arrange f i)

lemma arr {i x y q c d l b M n t} (h:l.Mane c b d (postcard (stacc q i) t) (M n) x y) {j:ℕ}(ht:n ≤ j):
     Lot.Mane l c b d (post q n i t) (arrange M j) x y:=by
    have hf: Lot.Mane l c b d (post q n i t) (erode (M n)) x y:=by
        apply Cog.renameR _ h; simp [collapse,post]
    induction j with
    | zero=>have he:n=0:=by omega
            subst n; exact hf
    | succ j ih=>
      by_cases he:n=j+1
      · subst n
        exact .yes (show decide (opt _=j+1)=true by rw [optionX]; simp) hf
      exact .no (show decide (opt _=j+1)=false by rw [optionX]; simp [he]) (ih (by omega))

variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
abbrev dockA (u:Line (q:=q) (w:=w) (h:=h))(r x:ℕ):Seats:= u.D.chord r x r
abbrev stk(u:Line (q:=q) (w:=w) (h:=h))(v x i:ℕ):Seats:=Reed.film (dockA u v x) i 0
@[simp] lemma stalk(v x i:ℕ):stacc v i=(stk u v x i).info:=rfl
/-- direct untransformed data-station program assigned at one valid card. -/
def Parcel (u:Line (q:=q) (w:=w) (h:=h))(a:ℕ)(p:Cog):Prop:=
    ∀ v b c x y,unitK v=a→ u.D.l.Mane c b (u.D.D a) v p x y→
                                  u.D.l.Mane c b (u.D.D a) v u.D.l.P x y
lemma stationed {p:Cog}{a:ℕ} (_:u.Chart)(he:u.D.active a)(hr:a≠0)
    (hh:∃ _:(uphold a).1≠0, ∀ i,(i=2∨i=4∨i=10∨i=11∨i=15)→(uphold a).1≠i)
    (hx:u.s.scripted (uphold a).1=p):Parcel u a p:=by
   intro v b c0 x y ht hq
   apply (Line.Chart.assigned (u := u)) he ht
   unfold who; rw [ht,ite_eq_right hr]
   obtain ⟨hI,hY⟩:=hh
   unfold codeRank; rw [ite_eq_right hI,ite_eq_right (fun e=>hY _ e rfl),hx]
   exact hq

lemma echoTicket {a x i j c o m:ℕ}{f:ℕ → Cog}(h: u.D.Suite a)
   (hr:o ≤ m)(hs:o ≤ 32)(ht:u.smallQ a i)(hh:2 ≤ c)(he:c ≤ u.v.slope)(hv:rite (stk u a x i) c (f o) j)
   (hz:Parcel u a (arrange f m)):
    u.D.swears (post a o i 0) x j:= by
   intro b hb
   apply h.hired _ 0 (u.Launch h.stage i o 0 ht hs (Nat.zero_le _)) (by omega:1 ≤  c)
             (show c  ≤  u.D.slope from he)
   apply hz _ _ c _ _ (bellU ..)
   exact arr (hv (Dome.glove b x) ⟨_,hb,rfl⟩) hr

lemma scoreTicket {a x i j c o m H:ℕ}{f:ℕ → Cog}(h: u.D.Suite a)(hr:o ≤ m)(hs:o ≤ 32)(ht:u.smallQ a i)
   (hh:2 ≤ c)(he:c ≤ u.v.slope)(hx:H ≤ u.D.high a)
   {V:ℝ}(hp: band (stk u a x i) c H j (f o) V)(hz:Parcel u a (arrange f m)):
    u.D.Voice a x (hole o i) H (j*u.D.D a) V:=by
   obtain ⟨w,hp⟩:=hp
   refine ⟨w,(hp _ (hm (stk u a x i))).1,?_⟩
   intro t hk b he'
   apply h.hired _ t (u.Launch h.stage i o t ht hs (hk.trans hx)) (by omega:1 ≤  c)
             (show c  ≤  u.D.slope from he)
   apply hz _ _ c _ _ (bellU ..)
   exact arr ((hp _ ⟨b,he',rfl⟩).2.digits t hk) hr

lemma positioned {a x}(h:u.D.Suite a)(he:x∈u.D.P)(i j):
   stable (Reed.film (dockA u a x) i j) (Reed.campk (Mold.knob u.r u.v)):=by
   apply spread
   apply Mold.knows u.r u.v u.x u.prog a x (by classical exact of_decide_eq_true h.stage) he
       (show 2  ≤  u.v.slope from h.shape.price)

lemma vital {a x}(H:ℕ)(h:H ≤ u.D.H):
     Fret.Live (dockA u a x).head (Mold.knob u.r u.v) H:=
    Nat.pow_le_pow_right Nat.zero_lt_two h

lemma stayedC {a}(he:u.D.Suite a){t c}(hu:t ≤ u.D.high a)(hh:c ≤ u.v.slope): t+c*u.D.D a ≤ u.D.H:=by
    have he0:= (u.D.till a t).2 ⟨hu,he.paid⟩
    unfold Dome.won Dome.loadC at he0
    change c ≤ u.D.slope at hh
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul hh he.well.2) _) he0
lemma soonerC {a b H c}(he:u.D.Suite b)(hp:u.D.W a+u.D.D b  ≤ u.D.W b)
    (hh:c ≤  u.v.slope)(hz:H ≤ u.D.high b): H+c*u.D.D b  ≤  u.D.high a:=by
    apply le_trans _ (he.descend hp).2
    exact Nat.add_le_add hz (Nat.mul_le_mul_right _ hh)
end Studio

end
end ExactDerandomization.SiteX

end

section

namespace ExactDerandomization.SiteX.Label
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV Line Line.Fabric
noncomputable section
open scoped Classical
/- cap invocation program uses a common graph virtual q. -/
def substitute (_:Word)(q:ℕ):ℕ:=post (unitK q) Label.PURE 0 (date q)
lemma substituteK:Kn substitute:=Kn.wash.comp ((Kn.wash.comp (unitK0.tuple (Kn.fix (hole Label.PURE 0)))).tuple tokenK.right)
def renbody(P:Cog):Cog:=Cog.ren ⟨_,substituteK⟩ P
lemma reprise {u q l c b p k i s}(hp:Lot.Mane l c b k u p i s)(he:substitute l.x q=u):
                   Lot.Mane l c b k q (renbody p) i s:= Cog.renameR _ hp he

abbrev Ticket := Bool × ℕ × ℕ
def match0(i j:ℕ)(_:Word)(q:Plot):Bool:=
    let b:Ticket:=dec (Scheme.which q.1)
    decide (b.2=(i,j))

lemma match0K(i j:ℕ):Kn (match0 i j):=by
    have hl:= tokenK.comp tokenK.left|>.right
    let g:= ((Kn.unpack (α:=Ticket)).comp (hl.comp (Kn.first (β:=Site)))).right
    convert Print.both (g.left.eq (Kn.fix i)) (g.right.eq (Kn.fix j)) using 1
    ext x q
    rw [Bool.eq_iff_iff]
    simp only [match0, decide_eq_true_eq, Bool.and_eq_true, Prod.ext_iff]
    rfl
def outwardP(_:Word)(q:Plot):Bool:=(dec (Scheme.which q.1):Ticket).1
lemma outwardK : Kn outwardP := by
    have hl:= tokenK.comp tokenK.left|>.right
    exact ((Kn.unpack (α:=Ticket)).comp (hl.comp (Kn.first (β:=Site)))).left

abbrev placeholder := Cog.edit ⟨_,Kn.next⟩
variable {q w h:ℕ}
def motionR (z:Rock q w h)(v:Tags)(p:Pose)(i j:ℕ)(otherwise:Cog): Cog:=
    let f(b:Bool):= renbody (Ember.cutWay (coneX z p) (roadX z v true 10 9 0) (schedule z v) v.A
                                            (clim z.w.p) i j b)
    Cog.bif ⟨_,match0K i j⟩ (.bif ⟨_,outwardK⟩ (f true) (f false)) otherwise
def fold0 {r:Rock q w h}(v:Tags)(p:Pose) (l:List (ℕ×ℕ)):Cog:= match l with
    | []=>placeholder
    | f0::l=> motionR r v p f0.1 f0.2 (fold0 (r:=r) v p l)
abbrev neighbors (c:Const) := (range c.K) ×ˢ range (clim c+1)
abbrev fullB (r:Rock q w h)(v:Tags) (p:Pose):Cog:= fold0 (r:=r) v p (neighbors r.w.p).toList
lemma came (t:Ticket)(j:ℕ):
   (dec (Scheme.which (bell j (enc t) 0)):Ticket)=t:=by rw [bellV,dec_round]
lemma pickout(r:Rock q w h) (v:Tags)(p:Pose){n i j:ℕ}(u:List (ℕ×ℕ))
   (he:(i,j)∈ u)(b:Bool){l c B s a k}
   (hp:Lot.Mane l c B k (bell n (idx b i j) 0)
      (renbody (Ember.cutWay (coneX r p) (roadX r v true 10 9 0) (schedule r v) v.A
                                            (clim r.w.p) i j b)) s a):
   Lot.Mane l c B k (bell n (idx b i j) 0) (fold0 (r:=r) v p u) s a:=by
   induction u with
   | nil=> simp at he
   | cons x u ih=>
      obtain ⟨a1,b1⟩:=x
      by_cases hz: i=a1∧j=b1
      · obtain ⟨rfl,rfl⟩:=hz
        apply Lot.Mane.yes
        · unfold match0; simp only [idx,came,decide_true]
        cases b
        · exact Lot.Mane.no (by unfold outwardP; simp only [idx,came]) hp
        exact Lot.Mane.yes (by unfold outwardP; simp only [idx,came]) hp
      apply Lot.Mane.no _ (ih (by simpa [hz] using he))
      unfold match0; simp [idx,hz]
end
end ExactDerandomization.SiteX.Label

end

section

namespace ExactDerandomization.SiteX.Line.Fabric
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV Line Line.Fabric Producer Label
noncomputable section
open scoped Classical

variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
variable (v:Fabric u)(p:Producer)(κ:ℕ)
abbrev alongE :=v.diva p κ 12 9 10 0 true
abbrev core12 := v.c 12 0
variable {v p κ}
lemma cap_dual {i t}(h:u.D.Suite v.core12):
    u.D.dual (v.slotWord i) t↔ i<v.Rslots ∧1  ≤ t∧ t ≤ clim u.w0.p := by
   let x:=v.core12
   change decide (paired u.r u.v u.x (hole x i,t))=true ↔_
   have h0:x≠0:=Age.cpos _
   rw [decide_eq_true_eq]; unfold paired
   have hp: (dec x:Crt).1=12:=by simp [x,core12,c,rowL,clr,kit]
   have hz: licensed u.r u.x x:=of_decide_eq_true h.stage
   simp [cell,Scheme.inside,hole,x,hp,h0,hz]

lemma adding (v:Fabric u)(i z)(b:Bool): u.D.pulseQ (v.slotWord i) z b=bell v.core12 (idx b i z) 0:=by
   change (schedule u.r u.v).before b u.D.x (slotWord v i,z)=_
   simp [Scheme.before,schedule,cell,Scheme.inside,hole,location,slotWord,core12]

structure Bloom12 (v:Fabric u)(p:Producer)(κ:ℕ)(l:ℕ→List Swirl.Gem):Prop where
    quilt:(alongE v p κ).Quilt
    mouth:(alongE v p κ).Mouth l quilt
namespace Bloom12
variable {l:ℕ→List Swirl.Gem}(h0:Bloom12 v p κ l)
include h0

lemma funded (hS:u.v.A*(2*u.v.A+40)  ≤  u.v.slope)
    (_:v.Mantle κ)
    (hf:∀ i z b,i<v.Rslots→ 1 ≤ z→z  ≤ clim u.w0.p→∀ a y,
        Lot.Mane u.D.l u.v.slope ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0) (fullB u.r u.v u.s.pave) a y →
        Lot.Mane u.D.l u.v.slope ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0) u.D.l.P a y)
    (i:ℕ): u.D.Streams (v.slotWord i) ((v.alongE p κ).valueOf l (clim u.w0.p) i) := by
   let e:=v.alongE p κ; have hh:u.D.Suite v.core12:=h0.quilt.h.supply
   let k:=clim u.w0.p
   refine ⟨fun z hz x hx b r hr=>?_,fun z hz x hx b r hg=>?_,fun x hx z hz y hy r m he hp=>?_⟩
   · have he:u.D.pulseQ (v.slotWord i) z b=bell v.core12 (idx b i z) 0:=v.adding ..
     have hp:= (cap_dual hh).1 hz
     have hC := h0.mouth.clearsWay k i hp.1 z b hx hr
     let c:= e.valueOf l k i z b x
     have hi:Lot.Mane u.D.l (Ember.stepC e.A) ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0)
                 (renbody (Ember.cutWay e.p e.R e.D.s e.A k i z b)) (0,glove r x) (Dome.AtM c r x):=
             reprise hC (by simp [substitute]; rfl)
     have hj:i<v.Rslots:=hp.1; have hz1:z ≤  clim u.w0.p:= hp.2.2
     have hk: Lot.Mane u.D.l (Ember.stepC e.A) ⟨u.D.W v.core12,0⟩ 1 (bell v.core12 (idx b i z) 0)
                           (fullB u.r u.v u.s.pave) (0,glove r x) (Dome.AtM c r x):= by
        refine pickout u.r u.v u.s.pave _ ?_ b hi
        simpa only [Finset.mem_toList,neighbors,mem_product,mem_range] using (show i < v.Rslots ∧ z<clim u.w0.p+1 from ⟨hp.1,by omega⟩)
     have hn : 1 ≤  Ember.stepC e.A:=by
          have hs:=h0.quilt.h.skeleton; have hz:=h0.quilt.h.budget
          change _  ≤  e.A at hz; unfold Ember.stepC; change _ ≤ e.k at hs; nlinarith
     have hG := hf i z b hp.1 hp.2.1 hp.2.2 _ _ (hk.mono hS hn)
     have ht:= Night.pairbill u.r u.v u.x u.prog (v.slotWord i) z hz b
     have hg:u.D.pulseQ (v.slotWord i) z b  ≤  u.D.F.limit:=ht
     rw [he] at hg ⊢
     have hp0:u.D.D v.core12=1:=v.ageEnd _ (by decide)
     rw [← hp0] at hG
     exact hh.hired _ 0 hg (by have :=hh.shape.price; change 1 ≤ u.v.slope; change 2 ≤ u.v.slope at this; omega)
                   (by change u.v.slope ≤ u.v.slope; exact le_rfl) hG
   · have he:=h0.mouth.disp.1 hg
     exact ⟨(h0.mouth.pointIn he).1,h0.mouth.disp.2 ((Ember.Mouth.exchange0 b).1 he)⟩
   exact (h0.mouth.unique0 he hp).symm

abbrev flood (_:Fabric u)(p:Producer)(y:ℕ) : Finset ℕ:=
      u.D.P.filter (fun a=>∃ j, p.awake a j ∧ p.locate a j=y)
lemma swell {pay o M}(hs:Certified p u (v.terminal false) M v.S0 v.S1 o pay){y}(he:y∈u.D.P):
    (l y).length=(flood v p y).card:=by
   let b:=v.alongE p κ; let F:=b.pie l clearG
   have ht : Deck.Licence F (h0.quilt.p.lit h0.quilt.h clearG u.D.cleared):=h0.mouth.fitL _ u.D.cleared
   let f(g:Swirl.Gem):= g.1.2
   have hg:(l y).toFinset.image f=flood v p y:=by
      ext a; constructor
      · intro hi; obtain ⟨j,hj,rfl⟩:=mem_image.1 hi
        obtain ⟨x,hx,i,hl,rfl,hk⟩:= (ht.trace0 he).1 (show j∈F.trace y from List.mem_toFinset.mp hj)
        change (p.coversF x i).map _=some y at hk; unfold coversF at hk
        split at hk
        · next he=> simp only [Option.map_some,Option.some.injEq] at hk; exact mem_filter.2 ⟨hx,i,he,hk⟩
        contradiction
      intro hi; obtain ⟨ha,i,hp,hq⟩:=mem_filter.1 hi
      have hw:i<v.Rslots:=hs.suit.lacks ha hp
      refine mem_image.2 ⟨pledge a i,List.mem_toFinset.2 ?_,rfl⟩
      change pledge a i∈F.trace y
      exact (ht.trace0 he).2 ⟨a,ha,i,hw,rfl,show (p.coversF a i).map _ = some y by
                                                        unfold coversF; rw [ite_eq_left hp]; simp [hq]⟩
   have hi : Set.InjOn f (l y).toFinset:= by
      intro c hc g hh hx
      obtain ⟨x,hA,i,hi,hc0,h1⟩:= (ht.trace0 he).1 (show c∈F.trace y from List.mem_toFinset.mp hc)
      obtain ⟨x',hB,j,hj,hh0,h2⟩:= (ht.trace0 he).1 (show g∈F.trace y from List.mem_toFinset.mp hh)
      have hf : x=x':=by rw [hc0,hh0] at hx; exact hx
      have hs1 {x i}(h:F.f x i=some y):p.awake x i ∧ p.locate x i=y:=by
          change (p.coversF x i).map _=some y at h
          unfold coversF at h; split at h
          · next hh=>simp only [Option.map_some,Option.some.injEq] at h; exact ⟨hh,h⟩
          contradiction
      subst x'
      obtain ⟨ha,hx1⟩:=hs1 h1; obtain ⟨hb,hx2⟩:=hs1 h2
      rw [hc0,hh0,hs.light.fair x i j ha hb (hx1.trans hx2.symm)]
   rw [← hg, card_image_iff.2 hi,List.toFinset_card_of_nodup (show (l y).Nodup from (ht.wheels _ he).unique)]
end Bloom12

end
end ExactDerandomization.SiteX.Line.Fabric

end

section

namespace ExactDerandomization.SiteX.Line.Fabric
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV Line Line.Fabric Producer Label
noncomputable section
open scoped Classical

variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
variable (v:Fabric u)(f:Producer)
/- B rank roles station. -/
structure Stand where
     a:ℕ
     i:ℕ
     l:ℕ
     o:ℕ
     t:ℕ
     k:ℕ
namespace Stand
abbrev cage (s: Stand)(v:Fabric u): CageQ:=⟨v.c s.l 0,v.c s.i 0,s.t,v.Rslots⟩
abbrev beacon (s: Stand)(v:Fabric u)(f:Producer)(p:ℕ): Ember:=v.diva f p s.a s.l s.i s.o false
abbrev H (s: Stand)(v:Fabric u):ℕ:=u.D.high (v.c s.a 0)
variable (s:Stand)

abbrev bank(s:Stand)(v:Fabric u)(f:Producer)(M:Mat)(k p:ℕ)(w:ℕ→ℕ→ Tape):Ember.Forest (s.beacon v f p):=
     ⟨⟨_,putK u.r u.v⟩,s.H v,s.k,fun x i=> f.scoreF M x i/(2:ℝ)^k,w⟩

structure Law (p k:ℕ)(M:Mat):Prop where
   reg:v.Mantle p
   plot: v.Good
   auth : u.D.Suite (v.c s.a 0)
   heard : u.D.Heard (v.c s.a 0)
   ready:s.i<s.a∧s.l<s.a ∧ 5<s.i ∧ 5<s.l ∧ s.a  ≤ 64
   mode : Orbit.colorQ s.o s.l
   M0 : f.Certified u (s.cage v) M v.S0 v.S1 s.o k
   pos:∀ x i,0  ≤ f.scoreF M x i

namespace Law
variable {s k v f p M}(hp:s.Law v f p k M)
include hp

lemma promoted :∃ w,Ember.Forest.Archive (s.bank v f M k p w) := by
   obtain ⟨hi,hl,hI,hL,hB⟩:=hp.ready
   have hL0:¬Brole s.l:=by unfold Brole; omega
   have hI0:¬Brole s.i:=by unfold Brole; omega
   have hA0:¬Brole s.a:=by unfold Brole; omega
   let B:=s.cage v
   have hc:=hp.M0.suit.coil
   have heD:u.D.D (v.c s.l 0)=1:=v.ageEnd _ hL0
   have heA:u.D.D (v.c s.a 0)=1:=v.ageEnd _ hA0
   have heW:u.D.W (v.c s.l 0)+1 ≤ u.D.W (v.c s.a 0):=v.parentL hL0 hl hB
   have hq:u.D.high (v.c s.a 0) ≤ u.D.high (v.c s.l 0):=by
        unfold high; have he:=Nat.mul_le_mul_left u.D.slope (show u.D.W (v.c s.l 0)  ≤  _ from
                                           (Nat.le_add_right ..).trans heW); omega
   let e:=s.beacon v f p
   have ht:e.Trust:= hp.reg.ties hI0 hi hB _ hp.M0.suit hp.auth hp.heard
   have hx(a i:ℕ):∃ w,a∈ u.D.P→ i<v.Rslots→u.D.StageW (v.c s.l 0) a (hole s.o i) (u.D.high (v.c s.l 0)) k (f.scoreF M a i) w:=by
        by_cases hX:a∈ u.D.P∧ i<v.Rslots
        · obtain ⟨w,hW⟩:= (hp.M0.suit.voices a hX.1).ready i (hc.awake (hc.size0 _ hX.2))
          have ht : k*u.D.D (s.cage v).dataN=k:=by change k*u.D.D (v.c s.l 0)=k; rw [heD,mul_one]
          rw [ht] at hW; exact ⟨w,fun _ _=>hW⟩
        exact ⟨fun _=>0,fun he ht=> (hX ⟨he,ht⟩).elim⟩
   choose tape hw using hx
   let g:= s.bank v f M k p tape; have he(t:ℕ)(h:t  ≤  g.H) :g.topk.f e.D.x (e.Q t)=2^t :=by
      change Label.put u.r u.v u.x (e.Q t)=_
      unfold Label.put; rw [bellT]
      exact min_eq_right (Nat.pow_le_pow_right Nat.zero_lt_two
              (cap_time u.r u.v u.x u.prog _ t h))
   refine ⟨tape,ht,fun t hs=>hp.reg.bridge _ f hp.auth.stage hs,?_,he,fun t h0=>?_ ,rfl, hp.reg.space0, ?_⟩
   · intro i hi' a ha
     have hW:= hw a i ha hi'
     refine ⟨div_nonneg (hp.pos a i) (by positivity),?_,fun j hj=>?_⟩
     · exact hW.scored.1
     exact hW.scored.2 j (hj.trans hq)
   · change date (e.Q t)+1=_
     rw [bellT]
   dsimp only
   intro t h0 i hi0 j hj
   let y:=g.q t i j
   have hY:y=post (v.c s.l 0) s.o i (t-j):=by
       change followP s.l s.o u.x (e.Q t,i,j)=_
       unfold followP; rw [bellT]; have he:gob s.l u.x (e.Q t)=v.c s.l 0:=v.awayT _ _ _ _ _
       rw [he]
   change e.D.audible y∧date y  ≤  _ ∧ e.D.W (unitK y)<_ ∧ ∀ x∈e.D.P,e.D.echo y x= enc _
   rw [hY,bellU,bellT]
   refine ⟨u.spokenC hc.pos (Age.cpos _) _ _ _ (hc.awake (hc.size0 i hi0)) (Or.inr (by rw [show (uphold (s.cage v).dataN).1=s.l from by simp [uphold, c,rowL,clr,kit]]; exact hp.mode)),
                  le_rfl,heW,fun x hz=>?_⟩
   exact u.D.identity ((hw x i hz hi0).glad (t-j) (le_trans (Nat.sub_le _ _) (h0.trans hq)))

lemma identityN {x:ℕ}(w:ℕ→ℕ→Tape):
    (s.bank v f M k p w).scoreRank x= rank v.S0 (fun i=> M i x) s.k/(2:ℝ)^k:=by
   let e:=s.beacon v f p
   let g:=s.bank v f M k p w
   let S:= Ember.Forest.S e x
   let C:ℝ:=2^k; have hC:0<C:=by unfold C; positivity
   let F:= fun i=> M i x/C
   have hz : rank v.S0 F s.k =rank v.S0 (fun i=>M i x) s.k/C:=by
      have hh:F=fun i=>C⁻¹*M i x:=funext (fun i=>by unfold F; ring)
      rw [hh,scaled_rank (by positivity)]; ring
   let l:= hp.M0.light
   let j(i:ℕ):ℕ:=(token i).1
   have ha(i):i∈S → let a:=(token i).1; let b:=(token i).2
                       a∈v.S0 ∧ f.awake a b ∧ f.locate a b=x ∧ g.V0 i=F a ∧ enc ((a,b):Rill.History)=i:=by
       intro ht; obtain ⟨⟨a,b⟩,he,rfl⟩:=mem_image.1 ht
       have hs:= (mem_filter.1 he).2
       change (coversF f a b).map _=some x at hs
       simp only [token,dec_round]
       unfold coversF at hs; split at hs
       · next hc=>
         have hi : f.locate a b=x:=Option.some.inj hs
         refine ⟨(l.insured a b hc).1,hc,hi,?_,True.intro⟩
         change _=M a x/C; unfold Ember.Forest.V0; simp only [g,dec_round]
         unfold scoreF; rw [ite_eq_left hc,hi]
       contradiction
   have h0(v0:ℝ)(hv:0 ≤ v0) : (S.filter fun i=>v0 < g.V0 i).card =
                               (v.S0.filter fun i=>v0 < F i).card:=by
      let U:=S.filter fun i=>v0< g.V0 i
      have he: U.image j=v.S0.filter fun i=>v0<F i:=by
          ext i; constructor
          · intro hl; obtain ⟨a,h1,rfl⟩:=mem_image.1 hl
            obtain ⟨h1,h2⟩:=mem_filter.1 h1
            have he:=ha a h1; dsimp only at he
            exact mem_filter.2 ⟨he.1,h2.trans_eq he.2.2.2.1⟩
          intro hv'; obtain ⟨hv',hh⟩:=mem_filter.1 hv'
          have hC0:M i x≠0:=by intro hu; unfold F at hh; rw [hu,zero_div] at hh; linarith
          obtain ⟨a,hp0,hb0⟩:= l.defend i x hC0
          let c:=hole i a
          have hg:i∈u.D.P:=hp.plot.n0 hp.reg.chart hv'
          have h0:c∈S:=mem_image.2 ⟨(i,a),mem_filter.2
                  ⟨mem_product.2 ⟨hg,mem_range.2 (hp.M0.suit.lacks hg hp0)⟩,show (f.coversF i a).map _=some x from by
                                                unfold coversF; rw [ite_eq_left hp0]; exact congrArg some hb0⟩,rfl⟩
          have hq0 := ha c h0
          have hp1 : token c=(i,a):= by unfold c hole token; simp
          rw [hp1] at hq0; dsimp only at hq0
          exact mem_image.2 ⟨c,mem_filter.2 ⟨h0,hh.trans_eq hq0.2.2.2.1.symm⟩,by simp [j,hp1]⟩
      rw [← he]; symm
      apply card_image_iff.mpr
      intro i hi j1 hj hl
      have hu1:=ha i (mem_filter.1 hi).1
      have hu2:=ha j1 (mem_filter.1 hj).1
      unfold j at hl
      generalize heI : token i=x at *
      generalize heJ : token j1=y at *
      obtain ⟨i,i'⟩:=x; obtain ⟨j,j'⟩:=y; dsimp only at *
      subst j
      have hj:= l.fair _ _ _ hu1.2.1 hu2.2.1 (hu1.2.2.1.trans hu2.2.2.1.symm)
      subst j'; exact hu1.2.2.2.2.symm.trans hu2.2.2.2.2
   have ht(v0)(he:0 ≤ v0) : (v0<g.scoreRank x) ↔ v0< rank v.S0 F s.k:=by
      rw [Ember.Forest.scoreRank,rank_gt he,rank_gt he,h0 v0 he]
   rw [← hz]
   apply le_antisymm
   · by_contra! hx
     exact lt_irrefl _ ((ht _ (rank_nn ..)).1 hx)
   by_contra! hx
   exact lt_irrefl _ ((ht _ (rank_nn ..)).2 hx)
end Law
end Stand
end
end ExactDerandomization.SiteX.Line.Fabric

end

section

namespace ExactDerandomization.SiteX.Line.Fabric
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV Line Line.Fabric Producer Label
noncomputable section
open scoped Classical

variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
variable {v:Fabric u}{p:Producer}{κ:ℕ}
namespace Bloom12
variable {l:ℕ→List Swirl.Gem}(ht:Bloom12 v p κ l)
include ht
theorem charm {o M pay}(hz:Certified p u (v.terminal false) M v.S0 v.S1 o pay)(ha:v.Mantle κ)(h:v.Good)
    (hh:∀ i,u.D.Streams (v.slotWord i) ((v.alongE p κ).valueOf l (clim u.w0.p) i)):
    ∃ tb:ℕ→ℕ→ℕ,v.Profession p tb:=by
   let C:= v.alongE p κ
   let T:=C.pie l clearG
   have hp : u.D.Suite v.core12:= ht.quilt.h.supply
   let K:=clim u.w0.p
   have hl:= ht.mouth.fitL clearG u.D.cleared
   have he(i)(x):∃ z,(z≠0→ p.awake x i ∧ z  ≤ K)∧
         (p.awake x i→(z≠0↔ (flood v p (p.locate x i)).card  ≤  K)) ∧
         (∀ j,0<j → j ≤ K → C.valueOf l K i j true x= if z=j then some (p.locate x i) else none):=by
      let y:=p.locate x i
      let F(j c:ℕ) := T.takes K i j x c
      have hc (j c): C.valueOf l K i j true x=some c ↔ F j c:= ht.mouth.disp
      have hh(j c)(he:F j c): p.awake x i∧ y=c:=by
          have he:= hl.entry he
          change (p.coversF x i).map Prod.snd=some c at he
          unfold coversF at he; split at he
          · next hw=> exact ⟨hw,Option.some.inj he⟩
          contradiction
      by_cases hg:p.awake x i ∧ (flood v p y).card  ≤  K
      · obtain ⟨h0,h1⟩:=hg
        have he:=(hz.light.insured x i h0)
        have hm:y∈u.D.P:=Good.n1 ha.chart h he.2
        have hf:x∈u.D.P:=Good.n0 ha.chart h he.1
        rw [← ht.swell hz hm] at h1
        have hr:i<v.Rslots:=hz.suit.lacks hf h0
        have hL: pledge x i∈ l y:= by
          change _ ∈ T.trace y
          exact (hl.traceL hm).2 ⟨hf,hr,show (p.coversF x i).map _=some y by
                                                  rw [Producer.coversF,ite_eq_left h0]; rfl⟩
        obtain ⟨a,b,hg⟩:= List.mem_iff_append.mp hL
        let j:=a.length+1
        have hP:F j y:=⟨hm,h1,a,b,hg,rfl⟩
        have hx:j ≤ K:=(Deck.rimmem hP.2.2).2.2.trans h1
        have ht1: j≠0:=by unfold j; omega
        refine ⟨j,fun _=>⟨h0,hx⟩,fun _=>iff_of_true ht1 ?_,
                        fun i0 ho hk=>?_⟩
        · rw [← ht.swell hz hm]; exact h1
        split
        · next hx=> subst i0; exact (hc j y).2 hP
        next he0=>
          cases hf:C.valueOf l K i i0 true x with
          | none=>rfl
          | some u=> have hv:=hl.agree hP ((hc i0 u).1 hf)
                     exact False.elim (he0 hv.2)
      refine ⟨0,by simp,fun hw=>iff_of_false (by simp) (fun hf=>hg ⟨hw,hf⟩),fun j hr hi=>?_⟩
      rw [ite_eq_right (by omega)]
      cases hk:C.valueOf l K i j true x with
      | none=> rfl
      | some t=>
        have hu := (hc j t).1 hk
        obtain ⟨ha,rfl'⟩:=hh j t hu
        refine False.elim (hg ⟨ha,?_⟩)
        rw [rfl',← ht.swell hz hu.1]
        exact hu.2.1
   choose tb hb using he
   refine ⟨fun x i=>tb i x, hp.stage,fun x i=> (hb i x).1,fun x i=>(hb i x).2.1,
                  fun x hx i hA t hB hS=>?_⟩
   have hs:=hh i
   have hz' :u.D.dual (v.slotWord i) t:=(cap_dual hp).2 ⟨hA,hB,hS⟩
   exact ⟨hz',hs.canonicalS, (hs.lines hz' hx _).trans ((hb i x).2.2 t hB hS)⟩
end Bloom12

variable (v0:Tags)
def startsP {q w h:ℕ}(p:Rock q w h)(_:Word)(a:Plot):Bool:=
    let g:=uphold (unitK a.1)
    decide (operateR p.w (MV g) (Age.styx g))
lemma startsK {q w h:ℕ}(p:Rock q w h):Kn (startsP p):=by
    have hp:= ((Kn.unpack (α:=Crt)).comp unitK0).comp (Kn.first (β:=Site))
    exact GK.decideK (onRK p.w hp.right.right.left hp.right.left.left)
def quiet {q w h:ℕ}(p:Rock q w h)(A B:Cog):Cog:=
     .bif ⟨_,startsK p⟩ A B
abbrev capprog {q w h:ℕ} (r:Rock q w h)(v:Tags)(p:Pose):Cog:=quiet r (Label.fullB r v p) Label.placeholder

lemma vocal (o g i t:ℕ)(f:Site):startsP u.r u.x (bell (v.c o g) i t,f)=true ↔ v.activeR:=by
    unfold startsP; rw [bellU]
    simp only [uphold,c,rowL,clr, Wire.eq,decide_eq_true_eq]
    exact v.workR.symm
lemma rankName (i t o g:ℕ):who (bell (v.c o g) i t)=o:=by
    unfold who; rw [bellU,ite_eq_right (show v.c o g ≠ 0 from Age.cpos _)]
    simp [c,uphold,rowL,clr,kit]

theorem tribunal {o M pay}(hz:Certified p u (v.terminal false) M v.S0 v.S1 o pay)(ha:v.Mantle κ)
    (h:v.Good) (hp:u.D.Suite v.core12) (hr:u.D.Heard v.core12) (hx:v.activeR)
    (hA:u.v.A*(2*u.v.A+40)  ≤  u.v.slope)
    (he:u.s.scripted 12 =capprog u.r u.v u.s.pave):∃ tb,v.Profession p tb:=by
   let C:=v.alongE p κ
   have h1:C.Trust:=ha.ties (by decide:¬Brole 10) (by omega) (by omega) true hz.suit hp hr
   have hQ:C.Quilt:=
            ⟨h1, ha.bridge true p hp.stage (Nat.zero_le _), rfl, rfl⟩
   obtain ⟨l,hL⟩:= hQ.quilted
   have hT : Bloom12 v p κ l := ⟨hQ,⟨hL⟩⟩
   refine hT.charm hz ha h (hT.funded hA ha ?_)
   intro i z b hX hz hZ a y hY
   refine (Line.Chart.assigned (u := u)) hp.stage (bellU ..) ?_
   rw [v.rankName (o:=12)]
   change Lot.Mane _ _ _ _ _ (u.s.scripted 12) _ _
   rw [he]; exact .yes ((v.vocal ..).2 hx) hY

abbrev EmptyT :Dome.Tide:=fun _ _ _=>none
lemma desert12 (i:ℕ)(_:v.Good)(hk:¬v.activeR)(he:u.D.Suite v.core12)(ht:u.Chart)
    (hg:u.s.scripted 12=capprog u.r u.v u.s.pave): u.D.Streams (v.slotWord i) EmptyT:=by
    refine ⟨fun z hz x hx b q hq=>?_,fun _ _ _ _ _ _ hl=>by contradiction,fun _ _ _ _ _ _ _ _ hk _=>by contradiction⟩
    have hl:= Night.pairbill u.r u.v u.x u.prog (v.slotWord i) z hz b
    have hD:u.D.D v.core12=1:=v.ageEnd _ (by decide)
    let C:=u.v.slope
    have hM : 6 ≤  C:=ht.above6
    have hm : u.D.pulseQ (v.slotWord i) z b  ≤  u.D.F.limit:=hl
    rw [v.adding] at hm ⊢
    let w:= (u.D.l.book (bell v.core12 (idx b i z) 0))
    let W:=u.D.W v.core12
    have hv:u.D.l.state C ⟨W,0⟩ (0,glove q x):=by
       refine ⟨ht.e0.shape.account _ hx q hq,?_⟩
       change span C W 0 0 (lb 0+1); rw [lb_zero]; unfold span
       have he:1 ≤ W:=hD ▸ he.well.2; nlinarith [Nat.mul_le_mul_left (C*C) he]
    let Q:=bell v.core12 (idx b i z) 0
    have he0 :Lot.Mane u.D.l C ⟨W,0⟩ (u.D.D v.core12) Q (u.s.scripted 12) (0,glove q x) (0,glove q x):=by
       rw [hg]
       apply Lot.Mane.no
       · have hh : ¬ startsP u.r u.x (Q,(0,glove q x))=true:=mt (v.vocal ..).1 hk
         change startsP u.r u.x (Q,0,glove q x)=false; simpa using hh
       exact .edit rfl hv hv
    have hm1: Lot.Mane u.D.l C ⟨W,0⟩ (u.D.D v.core12) Q u.D.l.P (0,glove q x) (0,glove q x):=by
       apply (Line.Chart.assigned (u := u)) he.stage (bellU ..)
       rw [v.rankName]
       exact he0
    exact he.hired _ 0 hm (by change 1 ≤ C;omega) le_rfl hm1

end
end ExactDerandomization.SiteX.Line.Fabric

end

section

namespace ExactDerandomization.SiteX.Line.Fabric
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Plaza _root_.OAI.ExactDerandomization.Sub
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At MintV Line Line.Fabric Producer Label Ember.Forest
noncomputable section
open scoped Classical

variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
namespace Stand
variable (s:Stand)
def score0 (p:Rock q w h)(k:Tags)(g:Pose):Cog:=
   let b:=roadX p k false s.i s.l s.o
   let v:= coneX p g
   let w:PowerTop:= ⟨_, Label.putK p k⟩
   renbody (liftarm (Ember.Forest.trackG v b (schedule p k) k.A w s.k))
abbrev tollD (u : Line (q:=q) (w:=w) (h:=h)) :=powder (u.v.A*(2*u.v.A+40)+6*(s.k+50))
namespace Law
variable {s k v f p M}(hp:s.Law (u:=u) v f p k M)
include hp

set_option maxHeartbeats 1000000 in
theorem ardent (hc:s.tollD u  ≤  u.v.slope)(hq:s.a=13∨s.a=16)
    (hl:u.s.scripted s.a=s.score0 u.r u.v u.s.pave){x}(hx:x∈u.D.P):
    u.D.Voice (v.c s.a 0) x (hole 1 0) (s.H v) k (rank v.S0 (fun i=> M i x) s.k):=by
    obtain ⟨f0,hA⟩:=hp.promoted
    let q:=s.bank v f M k p f0
    have ht := hA.fullplan hx; let e:=s.beacon v f p; let j:=v.c s.a 0
    let F:= q.scoreTape x
    have hs: Checked F (q.scoreRank x) q.H:=hA.estimated x
    refine ⟨F,⟨?_,?_⟩⟩
    ·  rw [← hp.identityN f0]; exact hs
    intro t he b hb
    let y:=(e.D.orch e.u x e.slotv)
    have hp0 :Dome.glove b x  ≤  u.D.F.limit:=hp.auth.shape.account _ hx b hb
    have hn:(s.cage v).visN=v.c s.i 0:=rfl
    obtain ⟨hg,hB⟩:= ht (Dome.glove b x) ⟨_,hb,rfl⟩
    let c:=enc (dsign F t)
    have hC := hB.digits t he
    let r:=post j 1 0 t
    have hlQ: u.smallQ j 0:=by
       have hh:1 ≤ u.eye.e:= le_trans (by omega) hp.M0.suit.coil.baseC
       unfold Line.smallQ ConeX.wideQ; rw [lb_zero]
       have he1:= hp.auth.well.1
       change 1 ≤  u.eye.e*u.D.D j; change 0< u.D.D j at he1; nlinarith
    have hw : Lot.Mane u.D.l (s.tollD u) ⟨u.D.W j,t⟩ (u.D.D j) r (u.s.scripted s.a)
                               (0,glove b x) (c,glove b x):=by
       rw [hl]; unfold score0
       change Lot.Mane u.D.l (s.tollD u) ⟨u.D.W j,t⟩ (u.D.D j) (post j 1 0 t) (renbody q.engine) (0,glove b x) (c,glove b x)
       have he0: Label.substitute u.x (post j 1 0 t) = post j Label.PURE 0 t:=by simp only [substitute,bellT,bellU,post]
       apply reprise (u:=post j Label.PURE 0 t) ?_ (show Label.substitute u.D.l.x _=_ from he0)
       exact hC
    have hR: who r=s.a:= rankName (v:=v) _ _ s.a 0
    have hy: Lot.Mane u.D.l (s.tollD u) ⟨u.D.W j,t⟩ (u.D.D j) r u.D.l.P
                               (0,glove b x) (c,glove b x):=by
       apply (Line.Chart.assigned (u := u)) hp.auth.stage (bellU ..)
       rw [hR]
       unfold codeRank
       rw [ite_eq_right (by omega),ite_eq_right (by omega)]
       exact hw
    exact hp.auth.hired _ t (u.Launch hp.auth.stage 0 1 t hlQ (by omega) he)
                                        (by unfold tollD powder; omega) hc hy
end Law

abbrev TDef (k:ℕ) :Stand:=⟨13,11,9,4,3,k⟩
abbrev IDef (k:ℕ) :Stand:=⟨16,15,14,1,0,k⟩

end Stand
end
end ExactDerandomization.SiteX.Line.Fabric

end

end OAI
