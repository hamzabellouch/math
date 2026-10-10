import OAI.Computability.Logspace.ContourPrograms
import OAI.Computability.Logspace.DyadicArithmetic

namespace OAI

/-!
Bounded tours, paired path operations, and finite traversal programs.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Plaza
open Relay Mint Swirl Counter Relation Finset _root_.OAI.ExactDerandomization.Sub

def pledge (a p:ℕ):= gem0 (Sub.prime p) a
lemma pledge_eq {a b c d}: pledge a b=pledge c d ↔ a=c ∧ b=d:=by
    refine ⟨fun e=> ?_,by rintro ⟨rfl,rfl⟩; rfl⟩
    have hp : Sub.prime b=Sub.prime d := congrArg (fun x=>x.1.1) e
    have he:=congrArg (fun n=> (dec n:Sub.Card).2.1) hp
    simp [Sub.prime] at he
    exact ⟨congrArg (fun x=>x.1.2) e,he⟩

def sealG (u:Quill) := u.b.scent.f u.x0 (u.q,1)
structure Deck where
    u:Quill
    f:ℕ→ℕ→Option ℕ
    trace : ℕ→List Gem
namespace Deck
variable (p:Deck)
abbrev dom:=p.u.s.domain
abbrev slots:=p.u.b.ports.f p.u.x0 p.u.q

structure Licence (h:p.u.Tidy):Prop where
    began:p.u.H=0
    well : p.u.Stringent (sealG p.u)
    suit0:p.u.Suite p.f
    wheels : ∀ c∈p.dom,p.u.Wheel h p.f (sealG p.u) c (p.trace c)

def rim (xs:List Gem)(x:Gem)(r:ℕ) := ∃ a b,xs=a++x::b ∧ r=a.length+1
def takes (k i r a b:ℕ) := b∈p.dom ∧ (p.trace b).length≤k ∧ rim (p.trace b) (pledge a i) r
lemma rimmem {xs x r}(h:rim xs x r):x∈xs∧ 0<r∧ r≤xs.length:=by
    obtain ⟨a,b,rfl,rfl⟩:=h; simp
lemma splitup {xs:List Gem} {r:ℕ} (h:0<r)(hv:r≤xs.length):
    ∃ x,rim xs x r:=by
    induction xs generalizing r with
    | nil=> simp_all
    | cons y l ih=>
      by_cases hz:r=1
      · exact ⟨y,[],l,rfl,hz⟩
      obtain ⟨z,a,b,ha,hb⟩:= ih (r:=r-1) (by omega) (by simp at hv; omega)
      exact ⟨z,y::a,b,by simp [ha],by simp; omega⟩
lemma uniq1 {l x y r} (h:rim l x r)(e:rim l y r) : x=y:=by
    obtain ⟨a,b,rfl,h1⟩:=h; obtain ⟨c,d,h,h2⟩:=e
    have he:c.length=a.length:=by omega
    have hf:= congrArg (fun l=>l[a.length]?) h
    simp [he] at hf
    exact hf
lemma uniq2 {l x r t}(h:rim l x r)(e:rim l x t) (hp:l.Nodup): r=t := by
    obtain ⟨a,b,rfl,rfl⟩:=h; obtain ⟨c,d,h2,rfl⟩:=e
    have he1 : x∉a:=fun h=> List.disjoint_left.1 ((List.nodup_append'.1 hp).2.2) h (by simp)
    rw [h2] at hp
    have he2 : x∉c:=fun h=> List.disjoint_left.1 ((List.nodup_append'.1 hp).2.2) h (by simp)
    have hq:=congrArg (fun l=>l.idxOf x) h2
    simp [List.idxOf_append,he1,he2] at hq
    rw [hq]

namespace Licence
variable {p : Deck} {h:p.u.Tidy} (s:p.Licence h)
include s
lemma scented (z w:ℕ): p.u.scent z w=sealG p.u:=by
    unfold Quill.scent; rw [s.began]; rfl

lemma trace0 {y c}(hc:c∈p.dom):y∈p.trace c ↔ ∃ a∈p.dom,∃ i < p.slots,y=pledge a i ∧ p.f a i=some c:=by
    rw [(s.wheels _ hc).members]; constructor
    · rintro ⟨a,b,c,d,e,f,h⟩; exact ⟨a,b,c,d,e,f⟩
    rintro ⟨a,ha,i,hv,hk,hh⟩; exact ⟨a,ha,i,hv,hk,hh,(s.scented ..).symm⟩

lemma traceL {i a b}(he:b∈p.dom):pledge a i∈p.trace b ↔ a∈p.dom ∧ i < p.slots ∧ p.f a i=some b:=by
    rw [s.trace0 he]
    simp [pledge_eq]

lemma entry {k i r a b}(hz:p.takes k i r a b):p.f a i=some b:=
    ((s.traceL hz.1).1 (rimmem hz.2.2).1).2.2
lemma agree {k i r t a b c}(h1:p.takes k i r a b)(h2:p.takes k i t a c):
    b=c∧r=t:=by
    obtain rfl:= Option.some.inj ((s.entry h1).symm.trans (s.entry h2))
    exact ⟨rfl,uniq2 h1.2.2 h2.2.2 (s.wheels _ h2.1).unique⟩

end Licence

lemma back0 {k i r j a b c}(h1:p.takes k i r a b)(h2:p.takes k j r c b) : a=c∧ i=j:=
       pledge_eq.1 (uniq1 h1.2.2 h2.2.2)

end Deck
end ExactDerandomization.Plaza

end

section

namespace ExactDerandomization.Plaza
open Relay Swirl Mint _root_.OAI.ExactDerandomization.Sub Counter

abbrev pan (v:ℕ):Panel:= (false,v,0)
def pr (v:ℕ):Cog:= etch (α:=ℕ) (fun _ _=> pan (Sub.prime v)) (Kn.fix _)
abbrev tags (p:Sub.Bow)(x:Word)(a:Lore ℕ):=p.scent.f x (a.1,1)
def opn (p:Sub.Bow):Cog :=
   let ht:= p.scent.runs.comp (Kn.first.tuple (Kn.fix (α:=Lore ℕ) 1))
   etch (α:=ℕ) (fun x a=>pan (Sub.done (tags p x a))) ((Kn.fix false).tuple
       ((Sub.cnameK _ _ _ _ (Kn.fix 3) ht (Kn.fix 0) (Kn.fix 0)).tuple (Kn.fix 0)))
def clearp (i:ℕ):Cog:= etch (α:=Panel) (fun _ _=>i) (Kn.fix _)

def launch (m: Mill) (p r k:ℕ) : Cog :=
   .seq (pr p) ((snag m).surf k
      (fun i=> if i=r then clearp 1 else Rake.ply (snag m).forth i (clearp 0))
         (clearp 0))
def screen (p:Sub.Bow) (v:ℕ) : Cog :=
    .toss ⟨fun x u=>p.ask.f x (p.alpha.f x u.1,v), p.ask.runs.comp
                ((p.alpha.runs.comp Kn.first).tuple (Kn.fix v))⟩
          ⟨fun _ u=>(if u.2.1=0 then 0 else 1,u.2.2),
             (Kn.next.left.cond_eq (Kn.fix 0) (Kn.fix 0) (Kn.fix 1)).tuple Kn.next.right⟩
def forwardp (p:Sub.Bow)(m:Mill)(k i r:ℕ):Cog :=
    .seq (screen p i)
       (.bif (gear (α:=ℕ) (fun _ a=> decide (a.2=0)) (Kn.next.eq (Kn.fix 0)))
          (.edit ⟨_,Kn.next⟩) (launch m i r k))

abbrev rowFlag (p:ℕ) : Flag :=
    gear (α:=Panel) (fun _ a=> decide (a.2.2.1=Sub.prime p))
        (Kn.next.right.left.eq (Kn.fix (Sub.prime p)))
def reversep (p:Sub.Bow)(m:Mill)(k i r:ℕ):Cog :=
    .seq (opn p) ((snag m).dune k r
        (.bif (rowFlag i) (clearp 1) (Rake.ply (snag m).back r (clearp 0)))
                (clearp 0))

namespace Deck
variable (p:Deck)
noncomputable section
abbrev at0 (i a : ℕ): Site:= (i,p.u.s.hand a)
abbrev hq (h:p.u.Tidy):=p.u.hall h
abbrev angi (h:p.u.Tidy)(x b:ℕ):= (p.hq h).tag (gem0 x b) false
abbrev ctg:=gem0 (Sub.done (sealG p.u))
abbrev net (h:p.u.Tidy):= (p.hq h).acts
abbrev now (h:p.u.Tidy):= p.u.s.l.state (p.hq h).cost (p.hq h).b
abbrev atpred (P: ℕ→Prop) (v:Option ℕ) := ∀ y,P y↔ v=some y
def berth (b: ℕ):Option ℕ→Site
    | none=>p.at0 0 b
    | some c=>p.at0 1 c

lemma bitAdm {a} (h:p.u.Tidy) (ha:a∈p.dom) {k:ℕ} (hk:k≤1):
    p.now h (p.at0 k a):= by
    let b:=p.u.B
    have hv:1≤b.w:=h.run.wp
    let c:=p.u.p.price
    have he:1≤p.u.A:=h.run.ax
    have hc:4≤c:=by change 4≤ p.u.A*(2*p.u.A+40); nlinarith
    refine ⟨h.run.hands _ ha,?_⟩
    change span c b.w b.t 0 (lb k+1)
    have hu:= lb_mono hk; rw [lb_one] at hu
    unfold span; nlinarith [Nat.mul_le_mul_left (c*c) hv]

lemma trackAll {a i}(h:p.u.Tidy) (s:p.Licence h) (ha:a∈p.dom) (hi:i<p.slots):
    p.u.Rating p.u.child i ∧
    p.now h (p.angi h (Sub.prime i) a) ∧
    (p.u.s.echo (p.u.hear p.u.child i) a=0 ↔ p.f a i=none) ∧
          ∀ b,p.f a i=some b → b∈p.dom:= by
    obtain ⟨hp,hz⟩:= s.suit0.row a ha i hi
    have he:p.now h (p.angi h (Sub.prime i) a):=by
       apply ((p.u.forge h).yields).adm (v:=pledge a i)
       refine ⟨?_,Nat.zero_le _⟩
       apply (Bud.walled _).2
       exact ⟨p.u.p.mem_of p.u.s h.reserve (p.u.prepaid h (p.u.capPrime h hz.lengthp) (by omega)),ha⟩
    cases hf: p.f a i with
    | none=>
      rw [hf] at hp
      cases hp with | dry hr _ hl=> exact ⟨hr,he,by simp [hl],by simp⟩
    | some y=>
      rw [hf] at hp
      cases hp with | born hh=>
       cases hh with
       | solo h0 hz=>
         refine ⟨h0.hr,he,by rw [h0.chosen]; simp [h0.extant],?_⟩
         intro b he; obtain rfl:=Option.some.inj he; exact h0.hw
       | pair h0 ht g y hw=>
         refine ⟨h0.hr,he,by rw [h0.chosen]; simp [h0.extant],?_⟩
         intro b he; obtain rfl:=Option.some.inj he; exact h0.hw

lemma march {k c i}(h:p.u.Tidy)(hl:c∈p.dom)(hv:p.u.Rating p.u.child i)
    (hk:k=(if p.u.s.echo (p.u.hear p.u.child i) c=0 then 0 else 1)):
    p.net h (screen p.u.b i) (p.at0 0 c) (p.at0 k c):= by
    let u:=p.u; let f:=u.hear u.child i; let a:=u.A
    have hr:=hv.heat.1; have hw: u.v.depth.f u.x0 f+1 ≤ u.B.w:=by
       have hp:=hv.heat.2; rw [h.steady] at hp
       exact hp.trans h.openR
    have he : Mill.faith u.p u.s 0 f:=by
       have ha: 1 ≤ a:=h.run.ax
       have hA : 4 ≤ a:=by
         have hs:=h.gain; have hv:=h.reach
         change 4≤p.u.A; nlinarith
       change _+_ ≤ u.B.w ∧ span a (u.B.w-u.v.depth.f u.x0 f) _ (u.v.clock.f u.x0 f) _
       have hp : 1 ≤ u.B.w-u.v.depth.f u.x0 f :=by omega
       constructor
       · convert hw using 1
         change _+p.u.v.D.f p.u.x0 p.u.q=(_+1)
         rw [h.gap0]
         rfl
       · rw [show u.v.clock.f u.x0 f=0 from hr,lb_zero]; unfold span
         nlinarith [Nat.mul_le_mul_left (a*a) hp]
    have hu:= h.run.ring f hv.get ⟨_,he⟩ c hl
    refine .toss (q':=f) ?_ ?_ (p.bitAdm h hl (by omega)) (p.bitAdm h hl (by split at hk <;> omega))
                     ?_ hu
    · rfl
    · subst k; rfl
    change p.u.s.l.jump u.p.price u.B (p.u.p.v.D.f u.x0 u.q) 0 f
    unfold Lot.jump
    rw [h.run.openL f]
    have he1:= h.run.ax
    exact ⟨he.1, span_mono he.2 (by change p.u.A≤ p.u.A*(2*p.u.A+40); nlinarith) he1⟩

end
end Deck
end ExactDerandomization.Plaza

end

section

namespace ExactDerandomization.Plaza
open Relay Swirl Mint _root_.OAI.ExactDerandomization.Sub Counter
namespace Deck
variable (p:Deck)
noncomputable section

lemma era {k r i a}(h:p.u.Tidy)(s:p.Licence h)(ha:a∈p.dom)(hi:i<p.slots):
   ∃ v, atpred (p.takes k i r a) v ∧
        p.net h (forwardp p.u.b p.u.p k i r) (p.at0 0 a) (p.berth a v):= by
   obtain ⟨hw,hv,h1,h2⟩:=p.trackAll h s ha hi
   let flag:=if p.u.s.echo (p.u.hear p.u.child i) a=0 then 0 else 1
   have hc0:= p.march (k:=flag) h ha hw rfl
   cases he:p.f a i with
   | none=>
     rw [show flag=0 from ite_eq_left (h1.2 he)] at hc0
     refine ⟨none,fun b=> ⟨fun hz=>by have := s.entry hz; grind,by simp⟩,.seq hc0
            (.yes ?_ (.edit ?_ hc0.spots.2 hc0.spots.2))⟩
     · rfl
     · rfl
   | some b=>
    have hb:= h2 _ he
    rw [show flag=1 from ite_eq_right (fun hz=>by have hp:= h1.1 hz; grind)] at hc0
    have hk:=p.u.drum (s.wheels b hb)
    have hv0: pledge a i∈p.trace b:=(s.traceL hb).2 ⟨ha,hi,he⟩
    obtain ⟨x,y,hxy⟩:=List.mem_iff_append.mp hv0
    have hzxp: p.net h (pr i) (p.at0 1 a) (p.angi h (Sub.prime i) a) :=
          etches _ _ (i:=1) rfl hc0.spots.2 hv

    let H:=p.angi h (Sub.done (sealG p.u)) b
    have hr:H=(p.hq h).tag (ctg p b) false:= rfl
    have hs : p.now h H := by
       apply (p.u.forge h).yields.adm (ctg p b)
       exact ⟨p.u.root_ok (h:=h) s.well hb,Nat.zero_le _⟩
    let bad:=clearp 0
    have hhbad : p.net h bad (p.angi h (Sub.prime i) a) (p.at0 0 a):=
       etches _ _ rfl hv (p.bitAdm (k:=0) h ha (by omega))
    let Z:= (snag p.u.p).surf k (fun j=>if j=r then clearp 1 else Rake.ply (snag p.u.p).forth j bad) bad
    have hpf {v} (hm:p.net h Z (p.angi h (Sub.prime i) a) v):
        p.net h (forwardp p.u.b p.u.p k i r) (p.at0 0 a) v := by
       refine .seq hc0 (.no ?_ (.seq hzxp hm)); rfl
    by_cases good:r=x.length+1∧(p.trace b).length≤ k
    · have h0:p.takes k i r a b:= ⟨hb,good.2,x,y,hxy,good.1⟩
      refine ⟨some b,fun c=> ⟨fun he=>congrArg some (s.agree h0 he).1,?_⟩,hpf ?_⟩
      · rintro hp; obtain rfl:=Option.some.inj hp; exact h0
      apply (snag p.u.p).climbed hk _ _ bad hxy
      · intro
        rw [ite_eq_left good.1.symm]
        exact etches _ _ rfl hs (p.bitAdm (k:=1) h hb (by omega))
      · intro e; have hz:=good.2; omega
    · refine ⟨none,fun c=> ⟨fun h0=>?_,by simp⟩,hpf ?_⟩
      · obtain rfl:=Option.some.inj (he.symm.trans (s.entry h0))
        exact False.elim (good ⟨uniq2 h0.2.2 ⟨x,y,hxy,rfl⟩ (s.wheels _ hb).unique,h0.2.1⟩)
      · apply (snag p.u.p).climbed hk _ _ bad hxy
        · intro hm
          rw [ite_eq_right (show ¬ x.length+1=r by grind)]
          have hz:= hk.round; rw [hxy] at hz
          have hh:= hz.sever.1.every
                     (fun a b (h:(snag p.u.p).pass (p.hq h) a b)=>h.1)
          exact Rake.follow hh hhbad
        · intro; exact hhbad

lemma beam {k r i b}(h:p.u.Tidy)(s:p.Licence h)(hb:b∈p.dom):
   ∃ v, atpred (fun a=>p.takes k i r a b) v ∧
       p.net h (reversep p.u.b p.u.p k i r) (p.at0 0 b) (p.berth b v):=by
   have hh:=p.u.drum (s.wheels b hb)
   let H:= p.angi h (Sub.done (sealG p.u)) b
   have hs:p.now h H := by
       apply (p.u.forge h).yields.adm (ctg p b)
       exact ⟨p.u.root_ok (h:=h) s.well hb,Nat.zero_le _⟩
   have hp0:p.now h (p.at0 0 b):=p.bitAdm h hb (by omega)
   have hp:p.net h (opn p.u.b) (p.at0 0 b) H:=etches _ _ (i:=0) rfl hp0 hs
   by_cases he:(p.trace b).length≤ k∧0 < r∧r≤(p.trace b).length
   · obtain ⟨w,m,n,hv,hL⟩:= splitup he.2.1 he.2.2
     have hmem:w∈p.trace b:=by simp [hv]
     obtain ⟨a,ha,j,hj,rfl,hf⟩:= (s.trace0 hb).1 hmem
     have h1:p.takes k j r a b:=⟨hb,he.1,m,n,hv,hL⟩
     have ht:=(p.trackAll h s ha hj).2.1
     by_cases hg:j=i
     · subst j
       refine ⟨some a,fun c=> ⟨fun hy=>congrArg some (p.back0 h1 hy).1,?_⟩,.seq hp ?_⟩
       · intro h; obtain rfl:=Option.some.inj h; exact h1
       apply (snag p.u.p).chose hh
       · intro _
         refine ⟨_,_,_,hv,hL,.yes ?_ (etches _ _ rfl ht (p.bitAdm (k:=1) h ha ?_))⟩
         · rw [gear_at]; simp [pledge,gem0]
         · omega
       intro; contradiction
     · refine ⟨none,fun c=>⟨fun hy=>False.elim (hg (p.back0 h1 hy).2),by simp⟩,.seq hp ?_⟩
       apply (snag p.u.p).chose hh
       · intro _
         refine ⟨_,_,_,hv,hL,.no ?_ ?_⟩
         · rw [gear_at]
           have hz:Sub.prime j≠Sub.prime i:=fun e=> hg ((pledge_eq (a:=a) (c:=a) (b:=j) (d:=i)).1
                               (congrArg (fun v=>gem0 v a) e)).2
           simp [pledge,hz,gem0]
         · rw [hL]
           have hy : p.net h (clearp 0) H (p.at0 0 b):=etches _ _ rfl hs hp0
           have hm:=hh.round; rw [hv] at hm
           have hq:= hm.sever.1.both (w:=fun a b=> (p.hq h).acts (snag p.u.p).back
                                          ((p.hq h).tag a false) ((p.hq h).tag b false)) (fun y z h=>h.2)
           have hc:=Rake.follow hq hy
           rw [List.length_reverse] at hc; exact hc
       intro; contradiction
   · refine ⟨none,fun a=> ⟨fun hh=>False.elim (he ⟨hh.2.1,(rimmem hh.2.2).2⟩),by simp⟩,.seq hp ?_⟩
     apply (snag p.u.p).chose hh
     · intro; contradiction
     intro
     exact etches _ _ rfl hs hp0

end
end Deck
end ExactDerandomization.Plaza

end

section

namespace ExactDerandomization.Plaza
open Rill Swirl _root_.OAI.ExactDerandomization.Sub Mint Relay Counter Finset

abbrev PowerTop := Cub ℕ ℕ

structure WheelTop where
   p:Mill
   pin:PowerTop
   k:ℕ
namespace WheelTop
variable (p:WheelTop)

abbrev Eqpt:= ℕ×ℕ
abbrev minPt (Q o:ℕ):Eqpt := (Q,enc (pan (Sub.done o)))
def headQ (x:Word)(a:Lore ℕ):Eqpt:= minPt 0 (p.pin.f x a.1*2)
def point (z:ℕ) := (dec ((dec z:Panel).2.1):Sub.Card).2.1
lemma minK {α} [Wire α] (f g:PT α ℕ) (h:Kn f)(e:Kn g) :
   Kn (fun x a=>minPt (f x a) (g x a)) :=
    h.tuple (Kn.wash.comp ((Kn.fix false).tuple
        ((cnameK _ _ _ _ (Kn.fix 3) e (Kn.fix 0) (Kn.fix 0)).tuple (Kn.fix 0))))
lemma pointK {α} [Wire α] {f:PT α ℕ}(h:Kn f):
   Kn (fun x a=>point (f x a)):= by
   have he:=(Kn.unpack (α:=Panel)).comp h
   exact ((Kn.unpack (α:=Sub.Card)).comp he.right.left).right.left

lemma headK:Kn p.headQ:=minK _ _ (Kn.fix 0) ((p.pin.runs.comp Kn.first).times (Kn.fix 2))
def busy (x:Word)(a:Lore Eqpt):Bool :=
    if a.2.1 ≤ p.k then decide (p.pin.f x a.1< point a.2.2) else false
lemma busyK:Kn p.busy :=
    Kn.next.left.cond_le (Kn.fix _) ((p.pin.runs.comp Kn.first).lt (pointK Kn.next.right))
                 (Kn.fix _)

def full (i:ℕ):Cog := etch (α:=Panel)
     (fun _ a=>((i,enc a.2):Eqpt)) ((Kn.fix i).tuple (Kn.wash.comp Kn.next))
def undoTop (_:Slip) := 0
def ang :Cub Slip ℕ:=⟨fun _ a=>a.1,Kn.first⟩
def update (p:WheelTop)(_ :Word)(a:Lore Eqpt) :Eqpt :=
   let w:Eqpt:=dec a.2.2
   let z:=a.2.1+w.1
   if z≤p.k then minPt z (point w.2-1) else (p.k+1,w.2)
lemma updateK:Kn p.update:=by
   have hz:Kn (fun (_:Word)(a:Lore Eqpt)=> (dec a.2.2:Eqpt)) := Kn.unpack.comp Kn.next.right
   have h:=Kn.next.left.add hz.left
   exact h.cond_le (Kn.fix _) (minK _ _ h (pointK hz.right).pred) ((Kn.fix _).tuple hz.right)

def chart (x:Word)(a:Lore Eqpt):ℕ:= codeQ ((point a.2.2-p.pin.f x a.1:ℕ):ℤ)
lemma chartK:Kn p.chart:=codeK (((pointK Kn.next.right).sub (p.pin.runs.comp Kn.first)).ZofN)
def per :Cog:= .seq (Cog.focus ang ((snag p.p).gather (p.k+1) full)) (etch _ p.updateK)
def hunt :Cog:=.loop (gear _ p.busyK) p.per
def track: Cog:=.seq (etch _ p.headK) (.seq p.hunt (etch _ p.chartK))

end WheelTop

def tinc (S:Finset ℕ)(f:ℕ→ℕ)(o:ℕ) := (S.filter fun i=> f i=o).card
lemma width (S : Finset ℕ)(f:ℕ→ℕ)(o): countgt S f o+tinc S f o=countge S f o:=by
   let v:=S.filter fun i=> o<f i; let w:= S.filter fun i=>f i=o
   have hp : Disjoint v w:=by simp [v,w,Finset.disjoint_left]; omega
   have hz : v∪ w= S.filter (fun i=> o≤ f i):= by ext i; simp [v,w]; grind
   change _+_= #_
   rw [← hz,card_union_of_disjoint hp]; rfl

lemma segment {l n o} : countge l n (o+1)=countgt l n o:=rfl

structure Isle where
   u:Quill
   f:ℕ→ℕ→Option ℕ
   wheel:ℕ→List Gem
   pos:ℕ
   S:Finset ℕ
   tag:ℕ→ℕ
   stem:PowerTop
   k:ℕ
namespace Isle
variable (s:Isle)
abbrev p : WheelTop:=⟨s.u.p,s.stem,s.k⟩
abbrev P:=s.stem.f s.u.x0 s.u.q
noncomputable abbrev Hq(h:s.u.Tidy):Arena := s.u.hall h
abbrev slot (i:ℕ):=gem0 (Sub.done (s.P+i)) s.pos
structure Wrap (h:s.u.Tidy):Prop where
    fixedc:s.pos∈s.u.s.domain
    orbit:∀ i ≤ s.P,s.u.Wheel h s.f (s.P+i) s.pos (s.wheel i)
    ok:∀ i ≤ s.P,s.u.Stringent (s.P+i)
    sites:∀ i ≤ s.P,0 < i → tinc s.S s.tag i=(s.wheel i).length
    boundt:∀ i∈s.S,s.tag i ≤ s.P

abbrev speed (s:Isle):= s.k+50
abbrev pay1(s:Isle):= s.u.p.price+3*s.speed
abbrev pay(s:Isle):=s.pay1+3*s.speed
abbrev way (s:Isle)(c:ℕ):= Lot.Mane s.u.s.l c s.u.B 1 s.u.q
abbrev line (s:Isle)(c:ℕ):Site:= (c,s.u.s.hand s.pos)
abbrev term (s:Isle)(o k:ℕ):Site :=
           s.line (enc (WheelTop.minPt k (s.P+o)))
end Isle
end ExactDerandomization.Plaza

end

section

namespace ExactDerandomization.Plaza
open Rill Swirl _root_.OAI.ExactDerandomization.Sub Mint Relay Counter Finset
namespace Isle
noncomputable section
abbrev ball (s:Isle)(h:s.u.Tidy)(o:ℕ) :=(s.u.hall h).tag (s.slot o) false
abbrev hall2 (s:Isle) (h:s.u.Tidy) :Arena := {s.u.hall h with cost:=s.pay1}

abbrev cur (s:Isle)(v:ℕ):=countgt s.S s.tag v
namespace Wrap
variable {s:Isle} {h:s.u.Tidy} (p:s.Wrap h)
include p
omit p in
include h in
lemma hc0 : 1 ≤ s.u.p.price:=by
   have he : 1 ≤ s.u.A:=h.run.ax
   change 1 ≤ s.u.A*(2*s.u.A+40)
   nlinarith
omit p in
lemma dollar {i}(hi:i ≤ s.k+1):
   span s.speed 1 s.u.B.t s.u.B.t (lb i+1):=by
   have he:=lb_le_inc i
   unfold span speed; nlinarith
lemma person {i}(he:i ≤ s.P) : s.u.s.l.state s.u.p.price s.u.B (s.ball h i):=by
   apply ((s.u.forge h).yields).adm (s.slot i)
   exact ⟨s.u.root_ok (h:=h) (p.ok i he) p.fixedc,Nat.zero_le _⟩

lemma shortterm {i j}(hi:i ≤ s.P)(hj:j≤ s.k+1):
   s.u.s.l.state s.pay1 s.u.B (s.term i j):=by
   have hz:=p.person hi; have hhC:=(hc0 (s := s) (h := h))
   have hw:1 ≤ s.u.B.w:=h.run.wp
   have hu: span s.pay1 s.u.B.w s.u.B.t 0 (lb (enc (j,(s.ball h i).1))+1):=
       holdcap hz.2 (movespan ((dollar (s := s)) hj) hw) (by unfold pay1; omega)
                      (by unfold speed; omega) hhC
   exact ⟨hz.1,hu⟩
lemma wider {i j}(hi:i ≤ s.P)(hj:j≤ s.k+1):
   s.u.s.l.state s.pay s.u.B (s.term i j):=by
   have hz:=p.shortterm hi hj
   have ht:=(hc0 (s := s) (h := h))
   have hc1:1 ≤ s.pay1:=by unfold pay1; omega
   exact ⟨hz.1,span_mono hz.2 (by unfold pay; omega) hc1⟩

lemma circul {i} (he:i ≤ s.P):
   (snag s.u.p).Circuit (s.hall2 h) (s.slot i) (s.wheel i):= by
   have hz:= s.u.drum (p.orbit i he)
   refine ⟨hz.round.every ?_,hz.init,hz.others⟩
   intro a b hh
   have h1:s.u.p.price≤ s.pay1:=by unfold pay1; omega
   exact ⟨hh.1.mono h1 (hc0 (s := s) (h := h)),hh.2.mono h1 (hc0 (s := s) (h := h))⟩

lemma harvest {i t}(hi:i ≤ s.P)(ht:t=min (s.wheel i).length (s.k+1)):
   (s.hall2 h).acts ((snag s.u.p).gather (s.k+1) WheelTop.full) (s.ball h i) (s.term i t):=by
   have ht0:t ≤ s.k+1:=by omega
   subst t
   apply (snag s.u.p).attained (p.circul hi)
   have hz:=p.person hi
   have hA:s.u.s.l.state s.pay1 s.u.B (s.ball h i):=
     ⟨hz.1,span_mono hz.2 (by unfold pay1; omega) (hc0 (s := s) (h := h))⟩
   exact etches _ _ rfl hA (p.shortterm hi ht0)

omit p in
lemma sound {i t}(_:i ≤ s.P)(ht:t ≤ s.k)(hp:0 < i) :
    (gear _ s.p.busyK).f s.u.x0 (s.u.q,s.term i t)=true:=by
    change (gear _ s.p.busyK).f s.u.x0 (s.u.q,Pause (WheelTop.minPt t (s.P+i)) _)=true
    rw [gear_at]
    simp [WheelTop.busy,ht,WheelTop.point,pan,Sub.done,P,hp]
omit p in
lemma off0 {i t}(he:s.k<t ∨ i=0) :
    (gear _ s.p.busyK).f s.u.x0 (s.u.q,s.term i t)=false:=by
    change (gear _ s.p.busyK).f s.u.x0 (s.u.q,Pause (WheelTop.minPt t (s.P+i)) _)=false
    rw [gear_at]; simp [WheelTop.busy,WheelTop.point,pan,P,Sub.done]
    omega

lemma plusstep {i j m n u}(hi:i ≤ s.P)(ht:j ≤ s.k)(hp:0 < i)
    (hm:m=min (s.wheel i).length (s.k+1))
    (hn:n=min (m+j) (s.k+1))(hu:u=(if n ≤ s.k then i-1 else i)):
    s.way s.pay s.p.per (s.term i j) (s.term u n):= by
    have hA:=(hc0 (s := s) (h := h))
    have hl:1 ≤ s.pay1:=by unfold pay1; omega
    have he: s.way s.pay (Cog.focus WheelTop.ang _) (hold j (s.ball h i)) (hold j (s.term i m)):=
        Cog.focus_word WheelTop.ang (d:=1)
            (show s.way s.pay1 _ _ _ from by
              have ht:= p.harvest hi hm
              change Lot.Mane s.u.s.l s.pay1 s.u.B (s.u.v.D.f s.u.x0 s.u.q) _ _ _ _ at ht
              rw [h.gap0] at ht; exact ht)
            rfl ((dollar (s := s)) (show j ≤ s.k+1 by omega))
            (show 1 ≤ s.u.B.w from h.run.wp) (by unfold pay; omega) hl
                     (by unfold speed; omega)
    apply Lot.Mane.seq he
    apply etches _ _ (i:= (j,(s.term i m).1)) ?_ he.spots.2 (p.wider (by split at hu<;>omega) (by omega))
    change s.p.update s.u.x0 (s.u.q,j,enc (WheelTop.minPt m (s.P+i)))=WheelTop.minPt n (s.P+u)
    by_cases hx:j+m ≤ s.k
    · have hv : n=m+j:=by omega
      have hs:n ≤ s.k:=by omega
      rw [hu,ite_eq_left hs,hv]
      simp [WheelTop.update,WheelTop.minPt,WheelTop.point,pan,Sub.done,show s.P+i-1=s.P+(i-1) by omega,Nat.add_comm j m,show m+j ≤ s.k by omega]
    · have hn:n=s.k+1:=by omega
      have hs:¬ n≤ s.k:=by omega
      rw [hu,ite_eq_right hs,hn]; simp [WheelTop.update,WheelTop.minPt,hx]

lemma runout {i}(hi:i ≤ s.P)(ht:s.cur i ≤ s.k):
     ∃ n,n ≤ s.k+1 ∧
      s.way s.pay s.p.hunt (s.term i (s.cur i)) (s.term (rankN s.S s.tag s.k) n):=by
    induction i with
    | zero=>
      have hp: rankN s.S s.tag s.k=0:= by
        by_contra hz
        exact not_lt.mpr ht (aboveN.1 (show 0<rankN s.S s.tag s.k by omega))
      rw [hp]
      exact ⟨_,ht.trans (by omega),.stop ((off0 (s := s)) (Or.inr rfl)) (p.wider hi (by omega))⟩
    | succ i ih=>
      let m:=min (s.wheel (i+1)).length (s.k+1)
      let n:=min (m+s.cur (i+1)) (s.k+1)
      have hf : n= min (s.cur i) (s.k+1):=by
         unfold n m; rw [← p.sites _ hi (by omega)]; have he:=width s.S s.tag (i+1)
         rw [segment] at he; unfold cur; omega
      have he:= (sound (s := s)) hi ht (by omega)
      by_cases hm:n ≤ s.k
      · have h0:n=s.cur i:=by omega
        obtain ⟨j,hj,hx⟩:= ih (by omega) (by omega)
        refine ⟨j,hj,.more he ?_ hx⟩
        have hs:i = (if n ≤ s.k then (i+1)-1 else (i+1)):=by simp [hm]
        rw [← h0]
        exact p.plusstep hi ht (by omega) (m:=m) rfl rfl hs
      have ht0:n ≤ s.k+1:=by omega
      refine ⟨n,ht0,.more (y:=s.term (i+1) n) he ?_ ?_⟩
      · exact p.plusstep hi ht (by omega) (m:=m) rfl rfl (Eq.symm (ite_eq_right hm))
      have hz : i+1=rankN s.S s.tag s.k:= by
        have h1 := Nat.le_of_lt (aboveN (S:=s.S) (p:=s.tag) (k:=s.k) (i:=i)|>.2
                                                  (show s.k < s.cur i by omega))
        have h3:i+1≤rankN s.S s.tag s.k:= aboveN (S:=s.S) (p:=s.tag) (k:=s.k) (i:=i)|>.2
                                                     (show s.k < s.cur i by omega)
        have h2: ¬ i+1<rankN s.S s.tag s.k := mt aboveN.1 (not_lt_of_ge ht)
        omega
      rw [← hz]
      exact .stop ((off0 (s := s)) (Or.inl (by omega))) (p.wider hi ht0)

lemma support0 {i}(he:i≤32): s.u.s.l.state s.pay s.u.B (s.line i):=by
   have hp:=(hc0 (s := s) (h := h)); have h2:20 ≤ s.pay:=by unfold pay pay1 speed; omega
   have h3: lb i≤6:=lb_mono (y:=32) he
   have hh:1 ≤ s.u.B.w:=h.run.wp
   refine ⟨h.run.hands _ p.fixedc,?_⟩
   change span s.pay s.u.B.w s.u.B.t 0 (lb i+1)
   unfold span; nlinarith [Nat.mul_le_mul_left (s.pay*s.pay) hh]
theorem cash: s.way s.pay s.p.track (s.line 0) (s.line (codeQ (rankN s.S s.tag s.k))):=by
   have hz : s.cur s.P=0:=by
      unfold cur countgt; rw [card_eq_zero,filter_eq_empty_iff]; intro x hx
      exact not_lt.mpr (p.boundt _ hx)
   obtain ⟨n,hn,hh⟩:= p.runout (i:=s.P) le_rfl (by rw [hz]; omega)
   rw [hz] at hh
   refine .seq (etches _ _ (i:=0) ?_ (p.support0 (i:=0) (by omega)) hh.spots.1)
                      (.seq hh (etches _ _ ?_ hh.spots.2 (p.support0 (i:=codeQ (rankN s.S s.tag s.k)) ((rangeQ _).trans (by omega)))))
   · change WheelTop.minPt 0 (s.P*2)=WheelTop.minPt 0 (s.P+s.P); rw [show s.P*2=s.P+s.P by omega]
   · change s.p.chart s.u.x0 (s.u.q,WheelTop.minPt n (s.P + rankN s.S s.tag s.k))=codeQ (rankN s.S s.tag s.k)
     simp [WheelTop.chart,WheelTop.point,Sub.done,pan,P]
end Wrap
end
end Isle
end ExactDerandomization.Plaza

end

section

namespace ExactDerandomization.Plaza
open Relay Mint _root_.OAI.ExactDerandomization.Sub Swirl Counter Rill Finset

def rakeword (w:Tape):ℕ→List ℕ
   | 0=>[enc (dsign w 0)]
   | n+1=> rakeword w n ++ [enc (dsign w (n+1))]
lemma width0 (w t) : (rakeword w t).length=t+1:=by induction t <;> simp_all [rakeword,Nat.add_assoc]

def neigh (t d:ℕ):ℕ:= enc ((2*(dec d:ℤ)+ (dec t:ℤ)):ℤ)
lemma neighK {α} [Wire α] {t d:PT α ℕ} (ht:Kn t)(hd:Kn d):
    Kn (fun x a=>neigh (t x a) (d x a)) :=
   Kn.wash.comp (((Kn.fix (2:ℤ)).prodZ (Kn.unpack.comp hd)).plusZ (Kn.unpack.comp ht))

abbrev pot (k:ℕ):ℕ := caplen k ^ 40
def cutter : PT ℕ ℕ := sweep
     (fun (_:Word)(a:ℕ×ℕ×ℕ)=>neigh a.2.1 a.2.2) (fun _ x=>x) (fun _ _=>enc (0:ℤ))
            (fun _ x=> pot x)
lemma cutterK:Kn cutter:= Kn.sweepK _ _ _ _ (neighK Kn.next.left Kn.next.right) Kn.identity
                    (Kn.fix _) (Kn.power _ Kn.caplenK)

lemma checked_max {w T V} (h:Checked w V T){t}(ht:t≤T):
    lb (enc (w t)) ≤ 3*(t+4)+2 := by
   apply Zbound _ _ (by omega)
   have hh:=abs_le.1 (h.2 t ht); obtain ⟨hp,he⟩:=abs_le.1 h.1
   have hz: |(w t:ℝ)|≤ 2^t+2:= by
      apply abs_le.2
      have ht : (0:ℝ)<2^t:=by positivity
      constructor <;> nlinarith
   have hi : -( (2:ℤ)^t+2)≤w t ∧ w t≤ (2:ℤ)^t+2:=by exact_mod_cast abs_le.1 hz
   have h1 : (w t).natAbs ≤ (2:ℕ)^t+2:=by
      generalize hw:w t=r at *
      have hf: ((2:ℕ)^t:ℤ)=2^t:=by push_cast; rfl
      omega
   rw [pow_add]
   have hh:(1:ℕ)≤ 2^t:=Nat.one_le_pow _ _ (by omega)
   omega

lemma land (w:Tape)(T:ℕ)(L:ℕ)(h:enc (0:ℤ)≤L)(hz:∀ i≤T,enc (w i)≤L):
    Scan L neigh (enc (0:ℤ)) (rakeword w T) (enc (w T)):=by
   induction T with
   | zero=>
     refine .cons h ?_
     rw [neigh,dec_round,dec_round, dsign,ite_eq_left rfl, mul_zero,zero_add]; exact .nil (hz _ le_rfl)
   | succ T ih=>
     rw [rakeword]
     have hp:= Grid.Scan.snatch (ih (fun i hi=>hz i (by omega))) (p:=enc (w (T+1)))
                    (a:=enc (dsign w (T+1))) ?_ (hz _ le_rfl)
     · exact hp
     rw [neigh,dec_round,dec_round]
     congr 1; simp [dsign]

lemma high_mesh (l:List ℕ): l.length+1≤lb (mesh l):=by
   induction l with
   | nil=> exact le_rfl
   | cons v l ih=> rw [List.length_cons,measure_mesh]; omega
lemma cutcorrect {w T V} (x) (h:Checked w V T) :
      cutter x (mesh (rakeword w T))=enc (w T):= by
    let u:=mesh (rakeword w T)
    have ho (q:ℕ)(hv:lb q≤3*(T+4)+2) : q ≤ pot u:= by
       apply (below q).le.trans
       rw [pot,caplen,← pow_mul]
       have ht:= high_mesh (rakeword w T)
       rw [width0] at ht
       apply Nat.pow_le_pow_right (by omega); unfold u; omega
    refine exact_sweep (l:=rakeword w T) (land w T (pot u) ?_ ?_) rfl
    · apply ho; rw [show lb (enc (0:ℤ))=4 by decide]; omega
    intro t ht; apply ho
    have he:= checked_max h ht; omega

lemma chaints {u:Quill}{p c t:ℕ}{w:Tape}
   (hz:∀ i ≤ t,u.s.echo (u.garnish p i) c=enc (dsign w (t-i))) :
    u.chainR p c (t+1)=mesh (rakeword w t):= by

   suffices h:∀ n ≤ t+1,
       let l:= rakeword w t
       u.chainR p c n = mesh (l.drop (t+1-n)) by simpa using h (t+1) le_rfl
   have hs (l:List ℕ)(k:ℕ)(e:k<l.length):
       l.drop k = l[k] :: l.drop (k+1) :=by
       exact List.drop_eq_getElem_cons e
   have hm (j:ℕ)(i:ℕ)(he:i<(rakeword w j).length):
         (rakeword w j)[i]=enc (dsign w i):=by
      induction j with
      | zero=>simp only [rakeword,List.length_cons,List.length_nil] at he; have : i=0:=by omega
              subst i; simp [rakeword]
      | succ j ih=>
         unfold rakeword
         rw [List.getElem_append]
         split
         · apply ih
         next hp=>
           rw [width0] at he hp
           have he : i=j+1:=by omega
           subst i; simp [width0]
   intro n he; dsimp only
   induction n with
   | zero=>simp [width0,Quill.chainR,forNat,List.drop_of_length_le,mesh]
   | succ n ih=>
     rw [u.chain_next, ih (by omega),hz n (by omega),hs (rakeword w t) (t+1-(n+1)) (by rw [width0]; omega),mesh,hm]
     rw [show t+1-(n+1)=t-n by omega,show t+1-n=t-n+1 by omega]

def padValue (p:PowerTop)(x:Word)(a:Node):ℕ := p.f x a.1+
    min (p.f x a.1) ((dec (cutter x a.2):ℤ).toNat)
lemma padK(p): Kn (padValue p):= (p.runs.comp Kn.first).add
           ((p.runs.comp Kn.first).small ((Kn.unpack.comp (cutterK.comp Kn.next)).topNat))

def tagsA (n:ℕ)(w:Tape)(t:ℕ):ℕ:=min n (w t).toNat
lemma tag_est {w:Tape}{x:ℝ}{t} (hx:0≤x) (h:Checked w x t) :
    |(tagsA (2^t) w t:ℝ)-2^t*x|≤ 2 := by
    have hz:=h.2 t le_rfl; obtain ⟨ha,hb⟩:=abs_le.1 h.1
    have he:0≤ (2:ℝ)^t:=by positivity
    unfold tagsA
    by_cases hk:w t<0
    · rw [show (w t).toNat=0 by omega]; simp
      obtain ⟨hz,hg⟩:=abs_le.mp hz
      have ht: (w t:ℝ)<0:=by exact_mod_cast hk
      rw [abs_of_nonneg hx]; nlinarith
    have ht: ((w t).toNat:ℝ)=(w t:ℝ):= by
       exact_mod_cast (show ((w t).toNat:ℤ)=w t by omega)
    push_cast; rw [ht]
    rcases le_total (w t:ℝ) (2^t) with hp|hp
    · rw [min_eq_right hp]; exact hz
    rw [min_eq_left hp,abs_le]
    obtain ⟨h1,h2⟩:= abs_le.mp hz
    constructor <;> nlinarith

lemma stringentQ {u:Quill}{t i} (h: u.Tidy) (he:u.H=t+1) (hi:i ≤ 2^t):
    u.Stringent (2^t+i) := by
   unfold Quill.Stringent; rw [he]
   have ht:lb (2^t)≤lb (2^t+i):=lb_mono (by omega)
   have hp:lb (2^t+i)≤lb (2^(t+1)):=lb_mono (by rw [pow_succ];omega)
   rw [lb_shift] at hp ht; have hb:=h.gain
   refine ⟨ht,?_⟩; nlinarith

end ExactDerandomization.Plaza

end

end OAI
