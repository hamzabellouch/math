import OAI.Computability.Logspace.EstimatorMachine

namespace OAI

/-!
Finite iteration schedules and the decomposition of estimator increments.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Rain
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At SiteX SiteX.MintV
noncomputable section

/- Enumerate the increments by a pool in which each piece of a telescope,
variant of the walk, and multiplicand port have one reserved index. -/
abbrev Crack:= Bool×ℕ
abbrev CellQ:= Crack × (ℕ×ℕ)
abbrev Fog := (Bool×CellQ) × (Bool×ℕ)
abbrev Seed := (ℕ× ℕ×ℕ) × Fog
abbrev store0 (_:Word)(x:ℕ):Seed:=dec x
namespace Fog
abbrev first0 (q:Fog):Bool:=q.1.1
abbrev cell0 (q:Fog):= q.1.2
abbrev sig (q:Fog) := q.cell0.2.2
abbrev event (q:Fog):= q.2.2
abbrev k (q:Fog)(a:ℕ):= if q.cell0.1.1 then a+q.cell0.1.2 else a-q.cell0.1.2
abbrev ray (q:Fog)(a:ℕ):ℕ×ℕ:= (q.k a,q.cell0.2.1)
abbrev slackM (q:Fog)(M:ℕ):= M-q.sig-1
abbrev budget (q:Fog)(M:ℕ) := if q.2.1 then q.slackM M+1 else q.slackM M
abbrev tick (q:Fog)(v:Wares):=v.ell*q.sig

def habitat (q:Fog)(w:Wares)(a m i:ℕ)(forest:Finset Ray):Prop:=
   let p:=q.ray a
   let s:Est.Stair:=⟨m,0,⟨a,0,0⟩,w.ell⟩
   p∈forest ∧ q.slackM m ∈ s.layers p.1 i ∧ s.slack (q.slackM m)=q.sig ∧
   q.cell0.1=(if a ≤ p.1 then (true,p.1-a) else (false,a-p.1)) ∧
   q.event<Print.rad^(q.tick w)
def number0 (s: Stair)(b:Bool) (k:Ray) (m:ℕ)(a:Bool)(i:ℕ):Fog:=
   let v:=s.key.a
   (((b,(if v ≤ k.1 then (true,k.1-v) else (false,v-k.1)),k.2,s.slack m)),a,i)
lemma from0 (s:Stair)b r m v i:
    (number0 s b r m v i).ray s.key.a=r := by
     refine Prod.ext ?_ rfl
     unfold ray k number0 cell0; dsimp only; split <;> simp_all ; omega

lemma just (s:Stair)(p:Ray)(m:ℕ):s.layers p.1 m =
     Est.Stair.layers ⟨s.M,0,⟨s.key.a,0,0⟩,s.lam⟩ p.1 m := by
     cases m <;> rfl
lemma hews {s:Stair} {w:Wares}(hp:s.lam=w.ell) (b:Bool) {p:Ray}{forest:Finset Ray}(he:p∈forest)
      {i m:ℕ}(hm:m∈s.layers p.1 i)(a:Bool) {j:ℕ}(hj:j<Print.rad^(s.lam*s.slack m)):
   (number0 s b p m a j).habitat w s.key.a s.M i forest ∧ (number0 s b p m a j).slackM s.M=m:=by
   let q:= number0 s b p m a j
   have h:s.gap i ≤ s.slack m ∧ s.cut p.1 ≤ s.slack m ∧m+1<s.M := s.cheap (mem_Ico.1 hm).2
   have hd:q.slackM s.M=m:=by unfold q number0 slackM Stair.slack; have hh:= h.2.2; dsimp [sig,cell0]; omega
   refine ⟨?_,hd⟩
   let a0:=s.key.a
   let n:Stair:=⟨s.M,0,⟨a0,0,0⟩,w.ell⟩
   have hZ := just s p i
   rw [hp] at hZ hj
   have hh:q.ray a0=p:=from0 ..
   have hf:q.k a0=p.1:=congrArg Prod.fst hh
   change q.ray a0∈forest ∧ q.slackM s.M∈n.layers (q.k a0) i∧ n.slack (q.slackM s.M)=q.sig∧
         q.cell0.1=(if a0≤ q.k a0 then _ else _)∧ q.event<_
   refine ⟨hh.symm ▸ he,?_,?_,?_,hj⟩
   · rw [hf,hd]; exact hZ ▸ hm
   · rw [hd]; rfl
   change q.cell0.1=(if a0 ≤ q.k a0 then (true,q.k a0-a0) else (false,a0-q.k a0)); rw [hf]; rfl

lemma totally {s:Stair}{w:Wares}(_:s.lam=w.ell){i:ℕ}{forest:Finset Ray}
   {q:Fog}(h:q.habitat w s.key.a s.M i forest):
   let p:=q.ray s.key.a
   p∈forest ∧ q.slackM s.M∈s.layers p.1 i ∧
          number0 s q.first0 p (q.slackM s.M) q.2.1 q.event=q :=by
    dsimp only; refine ⟨h.1,?_,?_⟩
    · rw [just s (q.ray s.key.a) i]; exact h.2.1
    obtain ⟨hj,hk,hC⟩:=h.2.2
    dsimp only [number0]; change q.cell0.1=(if s.key.a ≤ q.k s.key.a then (true,q.k s.key.a-s.key.a) else (false,s.key.a-q.k s.key.a)) at hk; rw [← hk,show s.slack _=q.sig from hj]

lemma far0 {s:Stair} {w:Wares}(hp:s.lam=w.ell){i:ℕ}(hi:i<s.L){forest:Finset Ray}{q:Fog}
      (h:q.habitat w s.key.a s.M i forest):
    q.cell0.1.2 ≤  2*s.gap i ∧ s.gap i ≤ q.sig∧ q.sig< 2*s.gap i:=by
   let r:=q.ray s.key.a; let m:=q.slackM s.M
   have hm:m∈s.layers r.1 i:= (totally hp h).2.1
   have hr :s.slack m=q.sig:=h.2.2.1
   have h0:=s.full hm hi
   have he :distn s.key.a r.1+1 ≤ s.slack m:= (s.cheap (mem_Ico.1 hm).2).2.1
   have hu:q.cell0.1.2  ≤  distn s.key.a r.1:= by
      rw [show q.cell0.1=(if s.key.a ≤ r.1 then (true,r.1-s.key.a)else(false,s.key.a-r.1)) from h.2.2.2.1]
      unfold distn; split <;> dsimp only <;> omega
   omega
end Fog
namespace Seed
abbrev fog:(Seed)→ Fog:=Prod.snd
abbrev x (v:Seed):ℕ:= v.1.2.1
abbrev y (v:Seed):ℕ:=v.1.2.2
def old (b:Bool)(i:ℕ):Seed:=((if b then 0 else 1,i,0),(false,(true,0),0,0),false,0)
def along (v:Fog)(i j:ℕ):Seed:= ((2,i,j),v)
lemma old_inj {b c i j}: Seed.old b i=Seed.old c j ↔ b=c∧i=j:=by
    cases b <;> cases c <;> simp [Seed.old]
lemma along_inj {q f i j a b}: along q i j=along f a b ↔ q=f∧i=a∧j=b:=by simp [along]; tauto
lemma old_not (p i j q v):old p i ≠ along q j v:=by cases p <;> simp [old,along]
end Seed

abbrev CarryE(p:Wares) :ℕ:= cexpo 2 p.p.K *4
def passport (v:Wares):ℕ:= 50+v.p.M^2+v.p.K+2*v.p.M+4*CarryE v+2*v.ell*lb Print.rad

namespace Pass
variable (v:Wares)
lemma small {p d i j:ℕ}(h:p ≤ i*d)(he:i ≤ j):p ≤ j*d:=le_trans h (Nat.mul_le_mul_right d he)
abbrev sized {α} [Wire α] (u:α)(k d:ℕ):= lb (enc u) ≤ k*d
lemma pair {α β} [Wire α] [Wire β] {p:α}{q:β}{c d:ℕ}(h:1 ≤ d)(hc:2 ≤ c)
    (hp:sized p c d)(hq:sized q c d):sized (p,q) (4*c) d:=by
   have he:lb (enc (p,q)) ≤ 2*lb (enc p)+lb (enc q)+2:=measure_pair ..
   unfold sized at *; nlinarith
lemma little (p d:ℕ)(h:1 ≤ d):sized p (p+1) d:=by
    change lb p ≤ _; have := lb_le_inc p; nlinarith
lemma left {α} [Wire α] (p:α)(k d:ℕ)(h:sized p k d) (c:ℕ)(hp:k ≤ c):sized p c d:=small h hp
lemma boo (p:Bool)(k d:ℕ)(he:1 ≤  k)(hp:1 ≤ d):sized p k d:=by
    unfold sized
    have h: lb (enc p)=1:=by cases p<;> rfl
    rw [h]; nlinarith
abbrev reserve (v:Wares):=4^7 *passport v
lemma lengthC {s:Stair} {i:ℕ}(hp:s.lam=v.ell)(hi:i<s.L){forest:Finset Ray}
   (h:∀ q∈forest,q.2 ≤ v.p.M^2+2*v.p.M+2){q:Fog}(hq:q.habitat v s.key.a s.M i forest) {p r:ℕ}
   (he:p ≤ v.p.K)(ht:r ≤ v.p.K):sized (Seed.along q p r) (reserve v) (s.gap i):=by
   let c:=passport v; let d:=s.gap i
   have hc:c≥50:=by unfold c passport; omega
   have hd:d ≥ 1:=gapD_pos ..
   have hz:q.cell0.2.1 ≤ v.p.M^2+2*v.p.M+2:=h (q.ray s.key.a) hq.1
   obtain ⟨hm,hL,hs⟩:= Fog.far0 hp hi hq
   have hK : lb (enc q.event)  ≤  c*d:=by
       have hr:q.event< Print.rad^ (v.ell*q.sig):=hq.2.2.2.2
       have hh:Print.rad ≤ 2^lb Print.rad:= (below _).le
       have hv:q.event<2^(c*d):= hr.trans_le (le_trans (Nat.pow_le_pow_left hh _) (by
           rw [←pow_mul]; apply Nat.pow_le_pow_right (by omega)
           let L:= lb Print.rad
           have he: 2*v.ell*L ≤  c:=by unfold L; unfold c passport; omega
           change q.sig < 2*d at hs
           change L*(v.ell*_) ≤ _
           nlinarith [Nat.mul_le_mul_left (L*v.ell) hs.le,Nat.mul_le_mul_right d he]))
       exact modest hv (by nlinarith)
   have hC(x:ℕ)(hi:x+1 ≤ c):sized x c d:= left x _ d (little x d hd) c hi
   have hl(x:ℕ)(hi:x ≤ 2*d):sized x c d:=by change lb x  ≤  _; have := lb_le_inc x; nlinarith
   have hA:sized q.cell0.1 (4*c) d:=pair hd (by omega) (boo _ _ _ (by omega) hd) (hl _ hm)
   have hB:sized q.cell0.2 (4*c) d:=pair hd (by omega)
                 (hC q.cell0.2.1 (by unfold c passport; omega)) (hl q.sig hs.le)
   have hv:sized q.cell0 (4*(4*c)) d:= pair hd (by omega) hA hB
   have hw:sized q.1 (4*(4*(4*c))) d:=pair hd (by omega) (boo _ _ _ (by omega) hd) hv
   have hq1:sized q (4*(4*(4*(4*c)))) d:=pair hd (by omega) hw (pair hd (by omega)
          (boo _ _ _ (by omega) hd) (left _ c d hK _ (by omega)))
   have hi:sized (2,p,r) (4*(4*c)) d:= by
       refine pair hd (by omega) (left (2:ℕ) c d (hC 2 (by omega)) (4*c) (by omega)) (pair hd (by omega) (hC _ ?_) (hC _ ?_))
       all_goals unfold c passport; omega
   exact left (Seed.along q p r) _ d (pair hd (by omega) (left _ _ d hi _ (by omega)) hq1)
                       _ (by unfold reserve; change _  ≤  _ * c; omega)
end Pass
end
end ExactDerandomization.Rain

end

section

namespace ExactDerandomization.Rain
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Helix Helix.Foil Helix.Age Helix.Moon Helix.Night Helix.Mold Helix.Orbit Scheme
open Dome Cone ConeX Buf At SiteX SiteX.MintV Fog Env
noncomputable section
open scoped Classical

variable {n:ℕ} [Fact n.Prime]
/- Iteration radii by slack chart. -/
namespace Census
variable (s:Stair)
abbrev h(i) := s.lam*s.slack i
def calendar (m:ℕ) := ((Finset.univ:Finset Bool)×ˢ (range (Print.rad^h s m)))
def tracks (p:Finset Ray)(i:ℕ) := p.biUnion (fun q=>{q}×ˢ ((s.layers q.1 i).biUnion
                                                               fun m=>{m}×ˢ calendar s m))
abbrev Arc:= Ray × ℕ × Bool×ℕ
lemma pat (p:Finset Ray)(i:ℕ)(x:Arc): x∈tracks s p i ↔
    x.1∈p∧ x.2.1∈s.layers x.1.1 i∧ x.2.2.2< Print.rad^h s x.2.1:=by
   unfold tracks calendar
   rcases x with ⟨a,b,c,d⟩; cases c <;> simp [and_assoc,and_left_comm,and_comm]
def drops (b:Bool)(q:Arc):Fog:= number0 s b q.1 q.2.1 q.2.2.1 q.2.2.2
lemma grange {w:Wares}(ht:s.lam=w.ell)(b:Bool){x:Arc}{p i}(h:x∈tracks s p i):
   (drops s b x).habitat w s.key.a s.M i p∧ (drops s b x).ray s.key.a=x.1 ∧
                                    (drops s b x).slackM s.M=x.2.1:=by
    obtain ⟨hl,hA,hQ⟩:= (pat s p i x).mp h
    obtain ⟨hz,hf⟩:=hews ht b hl hA x.2.2.1 hQ
    exact ⟨hz,from0 ..,hf⟩

lemma disjoint0 {w:Wares}(ht:s.lam=w.ell) (b p i):Set.InjOn (drops s b) ↑(tracks s p i):= by
    intro x hx y hy he
    have h1:=grange s ht b hx; have h2:=grange s ht b hy
    have ha:x.1=y.1:= h1.2.1.symm.trans ((congrArg (fun x=> ray x s.key.a) he).trans h2.2.1)
    have hb:x.2.1=y.2.1:= h1.2.2.symm.trans ((congrArg (fun x=> slackM x s.M) he).trans h2.2.2)
    have hc:x.2.2=y.2.2:=congrArg (fun q:Fog=>q.2) he
    exact Prod.ext ha (Prod.ext hb hc)
lemma total (p:Finset Ray) (i:ℕ) (f:Arc→ℝ):
    ∑ x∈tracks s p i,f x=
      ∑ x∈p,∑ m∈s.layers x.1 i,∑ j∈range (Print.rad^(h s m)),∑ b:Bool,f (x,m,b,j):=by
   unfold tracks
   rw [sum_biUnion]
   · apply sum_congr rfl; intro x hx
     rw [sum_product]; simp only [sum_singleton]
     rw [sum_biUnion]
     · apply sum_congr rfl; intro m hm; rw [sum_product]
       simp only [sum_singleton]; unfold calendar; rw [sum_product,sum_comm]
     intro i hi j hj ht; apply Finset.disjoint_left.2
     intro a ha hc; simp only [mem_product,mem_singleton] at ha hc; grind
   intro i hi j hj ht; apply Finset.disjoint_left.2
   intro a ha hc; simp only [mem_product,mem_singleton] at ha hc; grind

def wind (f:Est.Flame n)(d:Axis)(u:Pool n)(x y:ℕ)(r:Arc):ℝ:=
    let t:= Print.queue (h s r.2.1) r.2.2.2
    if Env.live d.u d.a (↑x:ZMod n) (↑y:ZMod n) (w:=0) (d:=0) le_rfl t.1 t.2 u then
          (if r.2.2.1 then 1 else -1)*Env.weight^(h s r.2.1)*
                 (f.lines r.1).seq (if r.2.2.1 then r.2.1+1 else r.2.1)
                        (go d.u d.a (w:=0) (d:=0) le_rfl t.1 t.2 u) x y
    else 0

theorem humid (f:Flame n)(d:Axis)(i:ℕ)(u:Pool n)(x y:ℕ) :
    f.portion s d i u x y=(∑ j∈tracks s f.rays i,wind s f d u x y j)+
                                           if i=0 then f.base x y else 0 :=by
   rw [total]
   unfold Flame.portion
   apply congrArg (fun (p:ℝ)=>p+_)
   apply sum_congr rfl; intro j hj; unfold Est.Line.waveR
   apply sum_congr rfl; intro m hm
   unfold Est.Line.pick Axis.fw Env.sampling
   rw [← Print.touring]
   apply sum_congr rfl; intro p hp
   simp only [Fintype.sum_bool]
   unfold wind
   let v:= Print.queue (h s m) p
   dsimp only
   unfold Est.Line.shake h
   split
   · next hx=> simp only [ite_true,Bool.false_eq_true,ite_false]; ring
   next hc=>ring
end Census

end
end ExactDerandomization.Rain

end

end OAI
