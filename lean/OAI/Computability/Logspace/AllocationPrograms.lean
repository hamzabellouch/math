import OAI.Computability.Logspace.ContourTraversal

namespace OAI

/-!
Guarded allocation and finite instruction interfaces for recursive queries.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Generate allocation guards in LF. -/
namespace ExactDerandomization.Mint
open Relay Swirl Counter Finset
abbrev Node := Lore ℕ
abbrev Bean := Lore Seat

structure Rune where
   mode : Cub Node ℕ
   slip : Cub Node ℕ
   next : Cub Bean ℕ
   token : Cub Bean ℕ
   initMark : Cub Bean Bool

structure Valve where
   W : Cub ℕ ℕ
   T : Cub ℕ ℕ
   D : Cub ℕ ℕ
   depth : Cub ℕ ℕ
   clock : Cub ℕ ℕ
   tap : Cub ℕ Bool
   voted : Cub Node Bool
   reach : Bool → Cub Node ℕ
   storeU : Cub ℕ ℕ

structure Mill where
    A : ℕ
    r : Rune
    v : Valve
namespace Mill
variable (p:Mill)
def O (x:Word) (q:ℕ):Level:= ⟨p.v.W.f x q,p.v.T.f x q⟩
def E0 (x:Word) (q:ℕ):Level:=⟨p.v.depth.f x q,p.v.clock.f x q⟩
def shoot (_:Mill)(A:ℕ)(_:Word)(a:Node) := (caplen a.2)^A
lemma shootK : Kn (p.shoot p.A) := Kn.power _ (Kn.caplenK.comp Kn.next)
def total (x:Word)(q:ℕ):ℕ := min (p.v.storeU.f x q) (2^charge p.A (p.v.W.f x q) (p.v.T.f x q))
lemma totalK : Kn p.total :=
   Kn.cap p.v.storeU.runs (Kn.fix 2) (((Kn.fix p.A).times p.v.T.runs).add
                                                  ((Kn.fix (p.A*p.A)).times p.v.W.runs))

def loanP (x:Word) (a:Bean):Prop :=
    let q:=a.1
    let v:=a.2.1
    let z:=a.2.2
    let u:=p.O x q
    let L:=p.E0 x z
    L.w + p.v.D.f x q≤u.w ∧ span p.A (u.w-L.w) u.t L.t (lb v+1)
instance loanD (x:Word) (a:Bean):Decidable (p.loanP x a):=by unfold loanP span; infer_instance
def loan (x:Word)(a:Bean):Bool:= decide (p.loanP x a)

lemma conj {α} [Wire α] (h j : PT α Bool) (he:Kn h) (hs:Kn j):
   Kn (fun x a=> h x a&&j x a):=by
   convert he.cond hs (Kn.fix false) using 1
   ext x a; cases e:h x a <;> simp []
lemma loanK : Kn p.loan:= by
   have ht: Kn (fun (_:Word)(a:Bean)=>a.1):=Kn.first
   have hv: Kn (fun (_:Word)(a:Bean)=>a.2):=Kn.next
   have hf:=p.v.W.runs.comp ht; have he:=p.v.D.runs.comp ht
   have hz:=p.v.depth.runs.comp hv.right; have ha := p.v.clock.runs.comp hv.right
   have hc: Kn (fun (_:Word)(_a:Bean)=>p.A):=Kn.fix _
   have hl:= ((hv.left.bl.succ).add (hc.times ha)).le
             ((hc.times (p.v.T.runs.comp ht)).add (((hc.times hc).times (hf.sub hz))))
   convert conj _ _ ((hz.add he).le hf) hl using 1
   ext x a
   simp only [loan, loanP, span, O, E0]
   exact Bool.decide_and ..

def axis (_:Word)(a:Bean):Node :=(a.1,a.2.1)
lemma axisK : Kn axis:=Kn.first.tuple Kn.next.left

def road (b:Bool) (x:Word) (a:Bean) :=
    let n:=axis x a
    let s:=p.r.slip.f x n
    if p.r.mode.f x n ≤ 1 then s else p.v.reach b |>.f x (s,p.r.token.f x a)
lemma roadK (b) : Kn (p.road b):=
    (p.r.mode.runs.comp axisK).cond_le (Kn.fix 1) (p.r.slip.runs.comp axisK)
       ((p.v.reach b).runs.comp ((p.r.slip.runs.comp axisK).tuple p.r.token.runs))

def limits (x:Word) (a:Bean):Bool :=
   decide (a.2.2< p.total x a.1) && decide (a.2.2 < p.shoot p.A x (axis x a))
lemma limitsK: Kn p.limits := conj _ _ (Kn.next.right.lt (p.totalK.comp Kn.first))
                                                   (Kn.next.right.lt (p.shootK.comp axisK))
def good0 (x:Word)(a:Bean):Bool:=
  let m:=p.r.mode.f x (axis x a)
  let t:=p.r.slip.f x (axis x a)
  let b:=p.r.token.f x a
  let z:= fun u=>p.loan x (a.1,a.2.1,p.road u x a)
  if m=0 then true else
   (z true && z false) && (if m=1 then p.v.tap.f x t else
          p.v.voted.f x (t,b) && decide (p.r.next.f x (a.1,a.2.1,b)=a.2.2+1))
lemma good0K : Kn p.good0:= by
   have ha : Kn (fun (_:Word)(a:Bean)=>a.1):=Kn.first
   have hb : Kn (fun (_:Word)(a:Bean)=>a.2):=Kn.next
   have h:=p.r.mode.runs.comp axisK; have he:=p.r.slip.runs.comp axisK
   have hv(b:Bool) := p.loanK.comp (ha.tuple (hb.left.tuple (p.roadK b)))
   exact h.cond_eq (Kn.fix 0) (Kn.fix _) (conj _ _ (conj _ _ (hv true) (hv false))
        (h.cond_eq (Kn.fix 1) (p.v.tap.runs.comp he)
           (conj _ _ (p.v.voted.runs.comp (he.tuple p.r.token.runs))
            ((p.r.next.runs.comp (ha.tuple (hb.left.tuple p.r.token.runs))).eq (hb.right.succ)))))
def permit (x:Word)(a:Bean):Bool:= (p.limits x a && p.limits x (a.1,a.2.2,a.2.1)) && p.good0 x a
lemma permitK : Kn p.permit:=conj _ _ (conj _ _ p.limitsK
          (p.limitsK.comp (Kn.first.tuple (Kn.next.right.tuple Kn.next.left)))) p.good0K

def bud :Bud :=⟨⟨_,p.shootK⟩, p.r.initMark,⟨_,p.permitK⟩,p.r.mode,p.r.next,p.r.token,fun b=>⟨_, p.roadK b⟩⟩

/-- semantic call responses -/
structure Fuel where
    l:Lot
    q:ℕ
    domain: Finset ℕ
    hand:ℕ→ℕ
    echo:ℕ→ℕ→ℕ
    stream:ℕ→ℕ→Bool→ℕ→Option ℕ
abbrev price := p.A*(2*p.A+40)
abbrev slipk (s:Fuel)(x) := p.r.slip.f s.l.x (s.q,x)
def clay (s:Fuel):Clay:=
   ⟨s.l,p.O s.l.x s.q,p.v.D.f s.l.x s.q,s.q,p.price,
       range (p.total s.l.x s.q),s.domain,s.hand,
       fun v x=>s.echo (p.slipk s v) x, fun v=>s.stream (p.slipk s v)⟩
abbrev entitled (s:Fuel)(q:ℕ) := ∃ v,p.loanP s.l.x (s.q,v,q)

def motor (s:Fuel) (q z:ℕ) (b:Bool) (c:ℕ): Site :=
    match s.stream q z b c with
    | none=> (0,s.hand c)
    | some w=> (1,s.hand w)
structure Fires (s:Fuel):Prop where
   ax: 1≤ p.A
   wp : 1 ≤ (p.O s.l.x s.q).w
   openL : ∀ q,s.l.book q=p.E0 s.l.x q
   hands : ∀ i∈s.domain,s.hand i ≤ s.l.F.limit
   ring : ∀ t,p.v.tap.f s.l.x t=true → entitled p s t → ∀ i∈s.domain,
       Boots s.l.x s.l.F s.l.P t s.l.P (0,s.hand i) (s.echo t i,s.hand i)
   rout : ∀ t z,p.v.voted.f s.l.x (t,z)=true →
      (∀ b,entitled p s ((p.v.reach b).f s.l.x (t,z))) →
      ∀ i∈s.domain,∀ b, Boots s.l.x s.l.F s.l.P ((p.v.reach b).f s.l.x (t,z)) s.l.P (0,s.hand i)
                          (motor s t z b i) ∧
                        ∀ j,s.stream t z b i=some j → j∈s.domain ∧ s.stream t z (!b) j=some i
   uniq : ∀ {t i z y a b}, s.stream t z true i=some a → s.stream t y true i=some b →
          z=y

lemma plusbase {a b:ℕ} (x:Bool) :
   lb (enc ((x,a,b):Panel))+1≤lb a*2+lb b+7:=by
   have hx:=measure_pair x (a,b)
   have hv:= measure_pair a b
   have he : Relay.measure x=1 := by cases x<;> rfl
   change Relay.measure (x,a,b)+1 ≤ Relay.measure a*2+Relay.measure b+7
   omega
lemma lumax {v i}(_:1≤p.A)
    (h:i≤ (caplen v)^p.A) :
    lb i≤ lb v*p.A+1 := by
   have he:=lb_mono h
   rw [caplen,← pow_mul,lb_shift] at he
   exact he
lemma cheaply {i v}(hA:1≤p.A) (h:i≤ (caplen v)^p.A) (b y:Bool) :
   lb (enc ((y,Bud.invert b (v,i)):Panel))+1 ≤ (2*p.A+40)*lb v:= by
   have hs:=p.lumax hA h
   cases b
   · change lb (enc (y,i,v))+1≤_

     have he:= plusbase (a:=i) (b:=v) y
     nlinarith [lb_pos v]
   change lb (enc (y,v,i))+1≤_
   have he:=plusbase (a:=v) (b:=i) y
   nlinarith [lb_pos v]

end Mill
end ExactDerandomization.Mint

end

section

namespace ExactDerandomization.Mint
open Relay Swirl Counter Finset
namespace Mill
variable (p:Mill) (s:Fuel)

abbrev view (v i:ℕ):Bean :=(s.q,v,i)
abbrev compo (v) := p.r.mode.f s.l.x (s.q,v)
abbrev label (v _ z:ℕ) := p.r.next.f s.l.x (view s v z)
abbrev wherep (v i) := p.r.token.f s.l.x (view s v i)

abbrev faith (v t) := p.loanP s.l.x (view s v t)
abbrev afoot (v) :=
    p.v.tap.f s.l.x (p.slipk s v)=true ∧ p.faith s v (p.slipk s v)
abbrev swept (v i:ℕ)(b:Bool) :=
   (p.v.reach b).f s.l.x (p.slipk s v,i)
abbrev swift (v z:ℕ) :=
      p.v.voted.f s.l.x (p.slipk s v,z)=true ∧ ∀ b,p.faith s v (p.swept s v z b)

lemma purity {v i} (h:p.compo s v=0) :
    p.good0 s.l.x (view s v i)=true :=by unfold compo at h; simp [good0,axis,h]
lemma bright {v i} (h:p.compo s v=1) :
    p.good0 s.l.x (view s v i)=true ↔ p.afoot s v:= by
   unfold compo at h
   simp [view,afoot,good0,axis,h,road,slipk,loan,faith,and_comm]
lemma abroad {v i} (h:2≤ p.compo s v) :
    p.good0 s.l.x (view s v i)=true ↔
       p.swift s v (p.wherep s v i) ∧ p.label s v i (p.wherep s v i)=i+1 := by
   unfold compo at h; let x:=p.r.mode.f s.l.x (s.q,v)
   change 2 ≤ x at h
   have he:p.r.mode.f s.l.x (s.q,v)≠0:=by change x≠0; omega
   have hk:p.r.mode.f s.l.x (s.q,v)≠1:=by change x≠1; omega
   have hm:¬ p.r.mode.f s.l.x (s.q,v)≤1:=by change ¬ x≤1; omega
   simp [view,wherep,label,good0,road,axis,loan,swift,hm,he,hk,swept,faith,slipk]
   tauto

lemma stamp (b:Bool) {v i} (h:p.compo s v=1) :
    p.road b s.l.x (view s v i)=p.slipk s v:=by simp_all [road,compo,axis,slipk]
lemma stampm (b:Bool) {v i} (h:2≤p.compo s v) :
    p.road b s.l.x (view s v i)=p.swept s v (p.wherep s v i) b := by
   unfold road; exact ite_eq_right (by change ¬ p.compo s v ≤ 1; omega)

lemma approved {v i} :
    p.bud.ready (p.clay s) v i=true ↔
     (v∈(p.clay s).raw ∧ i∈(p.clay s).raw ∧ i < caplen v ^ p.A ∧ v < caplen i ^ p.A) ∧
      p.good0 s.l.x (view s v i)=true:= by
   change (((decide (i < p.total s.l.x s.q) && decide (i < caplen v ^ p.A)) &&
     (decide (v < p.total s.l.x s.q) && decide (v < caplen i ^ p.A))) &&
     p.good0 s.l.x (s.q, v, i)) = true ↔ _
   simp only [Bool.and_eq_true, decide_eq_true_eq, clay, mem_range]
   tauto

namespace Fires
variable {p s}
lemma tilt (h:Fires p s): p.bud.Wall (p.clay s):= by
   let w:=p.O s.l.x s.q
   let v:=p.clay s
   change p.bud.Wall v
   have hc := h.ax; have hw: 1≤ w.w:=h.wp
   refine ⟨fun {a b} hz=>(p.approved s).1 hz|>.1,fun {a c} ha hs i hi b=>?_,fun {a b} hs he dir=>?_,
           fun {a b} hs he x hx dir=>?_, fun {a b} hs he=>?_, ?_⟩
   · change i ≤ caplen a ^p.A at hi
     refine ⟨h.hands _ hs,?_⟩
     replace ha: a<2^(charge p.A w.w w.t) :=
       lt_of_lt_of_le (mem_range.1 ha) (min_le_right ..)
     have hh : lb a≤ charge p.A w.w w.t:=modest ha (by unfold charge; nlinarith)
     have he:lb (enc ((b,a,i):Panel))+1≤(2*p.A+40)*lb a:=p.cheaply hc hi true b
     have hl:=span_mono (show span p.A w.w w.t 0 (lb a) by unfold span charge at *; omega)
                   (D:=p.price) (by unfold price; nlinarith) hc
     have hz:=lax (show span p.A w.w w.t 0 (lb a) by unfold span charge at *; omega) (m:=2*p.A+40)
               (D:=p.price) (by unfold price; nlinarith) hc
     change span p.price w.w w.t 0 (lb (enc ((b,a,i):Panel))+1)
     have hv : p.price*p.A ≤ p.price*p.price:=by unfold price; nlinarith
     unfold span; nlinarith [Nat.mul_le_mul_right w.w hv]
   · let f:=p.road dir s.l.x (view s a b)
     let u:=p.E0 s.l.x f
     obtain ⟨hh,ht⟩:= (p.approved s).1 hs
     change p.compo s a≠0 at he
     have hl: p.faith s a f:=by
        by_cases hx:p.compo s a=1
        · rw [show f=p.slipk s a from p.stamp s dir hx]
          exact ((p.bright s hx).1 ht).2
        have hg:2≤ p.compo s a:=by omega
        rw [show f=p.swept s a (p.wherep s a b) dir from p.stampm s dir hg]
        exact ((p.abroad s hg).1 ht).1.2 dir
     change u.w+v.d≤w.w ∧ span p.A (w.w-u.w) w.t u.t (lb a+1) at hl
     change s.l.jump p.price w v.d (enc ((false,(if dir then (a,b) else (b,a))):Panel)) f
     unfold Lot.jump; rw [h.openL]; change u.w+v.d≤w.w ∧ _
     have hz:= lax hl.2 (m:=2*p.A+40) (D:=p.price) (by unfold price; nlinarith) hc
     have hv : p.price*p.A ≤ p.price*p.price:=by unfold price; nlinarith
     have hh1:= p.cheaply hc hh.2.2.1.le dir false
     refine ⟨hl.1,?_⟩

     change span p.price (w.w-u.w) w.t u.t (lb (enc ((false,Bud.invert dir (a,b)):Panel))+1)
     unfold span; nlinarith [Nat.mul_le_mul_right (w.w-u.w) hv]
   · change p.compo s a=1 at he
     have hl:= (p.bright s he).1 ((p.approved s).1 hs).2
     have hs := h.ring (p.slipk s a) hl.1 ⟨_,hl.2⟩ x hx
     change Boots s.l.x s.l.F s.l.P (p.road dir s.l.x (view s a b)) _ _ _
     rw [p.stamp s dir he]
     exact hs
   · change 2 ≤ p.compo s a at he
     have hp:= (p.abroad s he).1 ((p.approved s).1 hs).2
     refine ⟨hp.2,fun x hx dir=>?_⟩
     have hy:=h.rout _ _ hp.1.1 (fun b=> ⟨_,hp.1.2 b⟩) x hx dir
     refine ⟨?_,hy.2⟩
     change Boots s.l.x _ _ (p.road dir s.l.x (view s a b)) _ _ _
     rw [p.stampm s dir he]; exact hy.1
   · intro v i j _ _ _ x _ y z g e
     exact h.uniq g e
end Fires

end Mill
end ExactDerandomization.Mint

end

section

namespace ExactDerandomization.Mint
open Relay Swirl Finset
namespace Mill
variable (p:Mill) (s:Fuel)
abbrev prize := charge p.A (p.O s.l.x s.q).w (p.O s.l.x s.q).t
def Reserve := 2^prize p s ≤ p.v.storeU.f s.l.x s.q
def fitting (x y:ℕ) := lb x≤ prize p s ∧ lb y≤prize p s ∧
                           lb x ≤ lb y*p.A ∧ lb y ≤ lb x*p.A
abbrev minted:=p.bud.Hill (p.clay s)
lemma mem_of {x} (h:p.Reserve s) (he:lb x≤prize p s) : x∈(p.clay s).raw :=
   mem_range.2 ((below x).trans_le (by
      change (2:ℕ)^(lb x)≤ min _ (2^prize p s)
      rw [min_eq_right h]; exact Nat.pow_le_pow_right Nat.zero_lt_two he))

lemma bid {x y} (h:p.Reserve s) (he:fitting p s x y) (hh:p.good0 s.l.x (view s x y)=true):
   p.bud.ready (p.clay s) x y=true := by
    apply (approved _ _).2
    have hc {x y} (h:lb x≤lb y*p.A): x < caplen y^p.A :=
       (below x).trans_le (by unfold caplen; rw [← pow_mul]; exact Nat.pow_le_pow_right Nat.zero_lt_two h)
    exact ⟨⟨p.mem_of s h he.1,p.mem_of s h he.2.1,hc he.2.2.2,hc he.2.2.1⟩,hh⟩

lemma meets0 {v i x} (h:p.Reserve s) (he:fitting p s v i) (hh:p.compo s v=0)
    (hk:p.label s v i 0=i+1) (hx:x∈s.domain) : minted p s (v,x) (i,x):=
   ⟨(Bud.walled _).2 ⟨p.mem_of s h he.1,hx⟩,(Bud.walled _).2 ⟨p.mem_of s h he.2.1,hx⟩,
        p.bid s h he (p.purity s hh),by
          change (match p.compo s v with | 0=>_ | 1=>_ | _=>_)
          rw [hh]; exact ⟨hk,rfl⟩⟩
lemma meets1 {v i x} (h:p.Reserve s) (he:fitting p s v i) (hh:p.compo s v=1)
    (hk:p.label s v i (s.echo (p.slipk s v) x)=i+1) (hz:p.afoot s v)
    (hx:x∈s.domain) : minted p s (v,x) (i,x):=
   ⟨(Bud.walled _).2 ⟨p.mem_of s h he.1,hx⟩,(Bud.walled _).2 ⟨p.mem_of s h he.2.1,hx⟩,
        p.bid s h he ((bright p s hh).2 hz),by
          change (match p.compo s v with | 0=>_ | 1=>_ | _=>_)
          rw [hh]; exact ⟨hk,rfl⟩⟩
lemma meets2 {v i x y b} (h:p.Reserve s) (he:fitting p s v i) (hh:p.compo s v=2)
    (hz:b=p.wherep s v i) (hk:p.label s v i b=i+1) (hf:p.swift s v b)
    (hx:x∈s.domain) (hy:y∈s.domain) (hr:s.stream (p.slipk s v) b true x=some y) :
    minted p s (v,x) (i,y):=by
   subst b
   exact ⟨(Bud.walled _).2 ⟨p.mem_of s h he.1,hx⟩,(Bud.walled _).2 ⟨p.mem_of s h he.2.1,hy⟩,
        p.bid s h he ((abroad p s (by change 2 ≤ p.compo s v; omega)).2 ⟨hf,hk⟩),by
          change (match p.compo s v with | 0=>_ | 1=>_ | _=>_)
          rw [hh]; exact hr⟩

abbrev mate (v:Dot) := ∀ y,¬ p.minted s v y
lemma cinder0 {v c} (h:p.compo s v=0) (hh:∀ i,p.label s v i 0=0) : p.mate s (v,c) := by
   rintro ⟨i,y⟩ ⟨-,hz,_,e⟩
   change (match p.compo s v with| 0=> _| 1=>_|_=>_) at e
   rw [h] at e; have hp:p.label s v i 0=i+1:= e.1; rw [hh] at hp; omega
lemma cinder1 {v c} (h:p.compo s v=1) (hh:∀ i,p.label s v i (s.echo (p.slipk s v) c)=0) :
   p.mate s (v,c) := by
   rintro ⟨i,y⟩ ⟨-,hz,_,e⟩
   change (match p.compo s v with| 0=> _| 1=>_|_=>_) at e
   rw [h] at e; have hp:p.label s v i (s.echo (p.slipk s v) c)=i+1:= e.1; rw [hh] at hp; omega
end Mill
end ExactDerandomization.Mint

end

end OAI
