import OAI.Computability.Logspace.EstimatorMachine
import OAI.Computability.Logspace.IterationSchedule

namespace OAI

/-!
Choice of simultaneous resource and error parameters for the estimator.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Terrain
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon
open SiteX SiteX.Line
open Rain

noncomputable section
open scoped Classical
variable {q w h:ℕ} {r:Rock q w h}

namespace Bank
/- Monetary knobs separated from the syntactic program.
Overspending c for canonical tapes scheduled LAST. Width e is
small label sizing, independent of c. -/

def bootC (r:Rock q w h):ℕ:= 50+ Was.Kpre r +clim r.w.p+2*r.w.p.M

abbrev hi (_:MintV)(r:Rock q w h):ℕ:=bootC r+10
abbrev hu (p:MintV)(r:Rock q w h):ℕ:=10*(hi p r+p.vol)
abbrev hx (p:MintV)(r:Rock q w h):ℕ:= 10*(hu p r+p.vol)
structure Green (r:Rock q w h)(p:MintV) :Prop where
    money : ∃ t:r.w.Proof, t.T.size^4 ≤  massB p.coin 1∧ t.T.R ≤ massB p.sealR 1
    minutes: (massB p.low 1)⁻¹  ≤  delta / 1000
    power : 4+Pass.reserve r.w ≤ p.vol
    honest: 16+p.tokenH ≤ p.sealR

lemma greenUp {r:Rock q w h} (e:r.w.Proof):∃ p:MintV,Green r p:=by
    have he (c:ℝ):∃ p:ℕ,c ≤ massB p 1 := by
      obtain ⟨p,h⟩:= exists_nat_gt c
      exact ⟨p,h.le.trans (swellB (by omega)).le⟩
    obtain ⟨k,hk⟩:=he (e.T.size^4)
    obtain ⟨c,hc⟩:=he e.T.R
    obtain ⟨w,hw⟩:=he (1000/delta)
    let v:=4+Pass.reserve r.w
    let p:MintV:=⟨k,v,c+16+v+20+2*k,w⟩
    refine ⟨p,⟨e,hk,le_trans hc (mass_mono (by dsimp only [p]; omega) _)⟩,?_,le_rfl,?_⟩
    · apply le_trans (inv_anti₀ (div_pos (by norm_num) dp) hw)
      exact le_of_eq (by simp)
    change 16+(v+(20+2*k)) ≤ _
    dsimp only [p]; omega

structure Turf (p:MintV) (r:Rock q w h) (v:Tags) :Prop where
    saving : Green r p
    cost0 : hx p r ≤ v.e
    coinbook : bootC r  ≤  v.bonus

namespace Green
variable {p:MintV} (h0:Green r p)
include h0
lemma tested : p.fine:=by
   unfold MintV.fine; have hh:=h0.honest; omega
lemma rooms:50+CarryE r.w+r.w.p.K ≤  p.vol:=by
   have hh:=h0.power; unfold Pass.reserve passport at hh; omega
lemma boxesK {d i:ℕ}(hp:1 ≤  d)(he:i<r.w.p.K):
   lb i  ≤  p.vol*d:=by
   have hm:=h0.rooms; have hh:=lb_le_inc i; nlinarith
omit h0 in
lemma capacityE (p':Wares)(m i): capacity 2 p'.p.K (Age.L m) i=2^(CarryE p' * gap m i):=by
   unfold capacity CarryE; change 2^(_*gap m i *4)=2^_
   congr 1; ring
lemma trunks {d i q0:ℕ}(_:d<Age.L i)(hp:q0< capacity 2 r.w.p.K (Age.L i) d):
   lb q0 ≤ p.vol*gap i d:=by
    rw [capacityE] at hp
    have hk:= gap_pos i d
    have ht:0 < CarryE r.w:=by unfold CarryE cexpo fexpo; omega
    exact le_trans (modest hp (Nat.mul_pos ht hk)) (Nat.mul_le_mul_right _ (by have:=h0.rooms; omega))
lemma ray_size{d i:ℕ}(he:1 ≤ d)(hp:i<p.rangeN d):lb i ≤ p.vol*d:=
   modest hp (Nat.mul_pos (by have :=h0.rooms;omega) he)
lemma bill0 {d i j:ℕ}(hd:1 ≤ d) (hp:i<p.rangeN d)(hj:j ≤ bootC r+1):
    lb (Seek.bin i j) ≤ hu p r*d:=by
     have h1:lb (enc (i,j)) ≤ 2*lb i+lb j+2:=measure_pair i j
     have h2:= h0.ray_size hd hp
     have h3:= lb_le_inc j
     unfold hu hi Seek.bin
     nlinarith
lemma office {i m j s:ℕ}(hd:i+1=Age.L m)
     (hj:j < capacity 2 r.w.p.K (Age.L m) i)(hs:lb s ≤ hu p r):
    lb (Seek.bin j s) ≤ hx p r:= by
     have h1:lb (enc (j,s)) ≤ 2*lb j+lb s+2:=measure_pair j s
     have h2:= h0.trunks (by omega) hj
     have h3 : gap m i=1:=by simp [gap,← hd]
     rw [h3] at h2; unfold hx Seek.bin; have hx:= h0.rooms; omega
end Green

end Bank
open Bank
namespace Stone
variable {q w h:ℕ}{u:Line (q:=q) (w:=w) (h:=h)}
variable (v:Fabric u)

@[simp] lemma W (a i:ℕ): u.D.W (v.c a i)= Age.weight v.m a i:=u.rolfe ..
@[simp] lemma D (a i:ℕ): u.D.D (v.c a i)= slackT v.m a i:=u.rolff ..
@[simp] lemma roleR(a i): (uphold (v.c a i)).1=a:=by simp [Fabric.c,rowL,clr,kit]
lemma zeroR(a i): 1+u.D.D (v.c a i)  ≤  u.D.W (v.c a i):= by
    have he:=(W v a i); have hp:=(D v a i); have hh:=weights v.m a i; have hq:=pace v.m a i
    omega

lemma pointing(a b i): pointer (v.c a i) b=v.c b i:=by
    unfold Fabric.c rowL clr pointer; rw [Wire.eq]
lemma alive {a b i o:ℕ}(hi:b=2∨b=4∨b=10∨b=11∨b=15)
    (he: b=11 ∧ a=9 ∧ o=3 ∨ (a+1=b ∧b≠11∧o=0))(j:ℕ):
    (coneX u.r u.s.pave).ispath0.f u.x (v.c b i)=true ∧
     (coneX u.r u.s.pave).spur.f u.x (v.c b i,j)=post (v.c a i) o j 0:=by
    change visitX u.x _ = true ∧ send u.x _ = _
    unfold visitX send; dsimp only; rw [roleR]
    refine ⟨decide_eq_true hi,?_⟩
    unfold assignT selop; rw [roleR]; simp_rw [Stone.pointing]; congr 1 <;> grind

structure Rector (v:Fabric u)(p:MintV):Prop where
    book:Bank.Turf p u.r u.v
    chart:u.Chart
    good:v.Good
namespace Rector
variable {v:Fabric u}{p:MintV}(h0:Rector v p)
include h0
lemma tickets(_ v':ℕ)(hp: v'.succ ≤ Bank.hx p u.r):(lb v') ≤ u.eye.e :=
    (lb_le_inc v').trans (hp.trans h0.book.cost0)
lemma wide0 (a i:ℕ):u.smallQ (v.c a i) 0:=by
   change lb 0  ≤  u.eye.e * u.D.D (v.c a i)
   rw [lb_zero]; have hx : 1 ≤ u.D.D (v.c a i):=by rw [D]; exact (pace ..).1
   have hf : 1 ≤ u.eye.e:=by have h:=h0.book.cost0; change _ ≤ u.eye.e at h; unfold Bank.hx hu hi at h; omega
   nlinarith
lemma aft {a i j:ℕ}(hx:lb j ≤ p.vol*u.D.D (v.c a i)):u.smallQ (v.c a i) j:=by
   exact le_trans hx (Nat.mul_le_mul_right _ (le_trans (show p.vol ≤ Bank.hx p u.r by unfold Bank.hx;omega) h0.book.cost0))
lemma endUnits (a:ℕ) (hj:a=14∨a=15∨(a=12 ∧ delta0 (bitR v.t))∨(a=16∧redV (bitR v.t))):
        u.D.Suite (v.c a 0):=by
   apply Fabric.Good.booked h0.chart h0.good
   · rw [Age.Period,ite_eq_right (by unfold Brole; omega)]; omega
   exact ⟨rightR _,Or.inr (by grind)⟩

variable (hc:v.activeR)
lemma midUnits (hc:v.activeR) (a i:ℕ)(hj:(1 ≤ a∧a ≤ 4∧i< Age.L v.m)∨i=0∧((9 ≤ a∧a ≤ 11)∨(a=13∧delta0 (bitR v.t)))):
        u.D.Suite (v.c a i):=by
   apply Fabric.Good.booked h0.chart h0.good ?_ ⟨rightR _,Or.inl ⟨by grind,(v.workR).1 hc⟩⟩
   unfold Age.Period Brole; rcases hj with h|h <;> grind
lemma provision {a b i o m:ℕ}(hi:b=2∨b=4∨b=10∨b=11∨b=15)
    (he: b=11 ∧ a=9 ∧ o=3 ∨ (a+1=b ∧b≠11∧o=0))
    (hs:u.D.Suite (v.c a i))(ht:u.D.Suite (v.c b i))
    (hh:∀ j:ℕ,j < m → lb j  ≤  p.vol*u.D.D (v.c b i)):
     (CageQ.mk (v.c a i) (v.c b i) o m).Front u:=by
   have ha: (1 ≤ a∧ a ≤ 17)∧(Age.Brole a↔Age.Brole b):=by unfold Age.Brole;omega
   have hx:u.D.D (v.c a i)=u.D.D (v.c b i):=by rw [D,D]; simp [slackT,ha.2]
   refine ⟨hs.stage,ht.stage,?_,?_,hx,fun i hi=> h0.aft (hh i hi),
                   (alive v (i:=i) hi he 0).1,fun j=>(alive v (i:=i) hi he j).2,?_⟩
   · have h:= h0.book.cost0; change _ ≤ u.eye.e at h; unfold Bank.hx hu Bank.hi at h; omega
   · rw [W,W,D]; apply Age.sooner _ (by omega) (by omega)
     rwa [D,D] at hx
   intro j hk
   apply spokenC u hs.stage (Age.cpos _) o j 0
   · change lb j ≤ u.eye.e *u.D.D (v.c a i)
     rw [hx]; exact hk
   rw [roleR]
   unfold taps omegaQ colorQ; omega
lemma frontI (hc:v.activeR) (i)(he:i < Age.L v.m): (v.α p i).Front u := by
   apply h0.provision (by decide) (by decide) (h0.midUnits hc 1 i (Or.inl ⟨by decide,by decide,he⟩))
                                      (h0.midUnits hc 2 i (Or.inl ⟨by decide,by decide,he⟩))
   intro j hj; rw [D]; exact h0.book.saving.ray_size (gap_pos _ i) hj
lemma frontP (hc:v.activeR) (i)(he:i < Age.L v.m): (v.β i).Front u := by
   apply h0.provision (by decide) (by decide) (h0.midUnits hc 3 i (Or.inl ⟨by decide,by decide,he⟩))
                                      (h0.midUnits hc 4 i (Or.inl ⟨by decide,by decide,he⟩))
   intro j hj; rw [D]; exact h0.book.saving.trunks he hj
lemma frontT (hc:v.activeR) (b): (v.terminal b).Front u:=by
   cases b
   · apply h0.provision (by decide) (by decide) (h0.midUnits hc 9 0 (Or.inr ⟨rfl,Or.inl (by decide)⟩))
                                     (h0.midUnits hc 10 0 (Or.inr ⟨rfl,Or.inl (by decide)⟩))
     intro j hj; rw [D]; exact h0.book.saving.boxesK ((pace ..).1) hj
   apply h0.provision (by decide) (by decide) (h0.midUnits hc 9 0 (Or.inr ⟨rfl,Or.inl (by decide)⟩))
                                     (h0.midUnits hc 11 0 (Or.inr ⟨rfl,Or.inl (by decide)⟩))
   intro j hj; rw [D]; exact h0.book.saving.boxesK ((pace ..).1) hj
lemma frontE : v.leaveE.Front u:=by
   apply h0.provision (by decide) (by decide) (h0.endUnits _ (Or.inl rfl))
                                     (h0.endUnits _ (Or.inr (Or.inl rfl)))
   intro j hj; rw [D]; exact h0.book.saving.boxesK ((pace ..).1) hj
end Rector
end Stone
end
end ExactDerandomization.Terrain

end

end OAI
