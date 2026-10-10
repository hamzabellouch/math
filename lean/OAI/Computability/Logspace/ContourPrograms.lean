import OAI.Computability.Logspace.AllocationPrograms

namespace OAI

/-!
Canonical contour queries and bounded path selection.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Sub
open Relay Swirl Mint Counter

/-- Common path-table scripts. The prefix of the digit stream attached
to an endpoint will be assembled with repeated stationary queries from
the initiation. use steps=0 for the plain cap kernel. -/
structure Bow where
    alpha : Cub ℕ ℕ
    clipA : Cub ℕ ℕ
    ports : Cub ℕ ℕ
    steps : Cub ℕ ℕ
    dress : Cub Bean ℕ
    scent : Cub Node ℕ
    padding : Cub ℕ ℕ
    ask : Cub Node ℕ
    before : Cub Bean ℕ
    knot : Cub Bean ℕ
    other : Cub Bean ℕ
    passp : Cub Bean ℕ
    haskid : Cub Bean Bool

abbrev Jet := ℕ×ℕ×ℕ×ℕ×ℕ
namespace Jet
abbrev band (v:Jet):= v.1
abbrev port (v:Jet):= v.2.1
abbrev rune (v:Jet):=v.2.2.1
abbrev invp (v:Jet):=v.2.2.2.1
abbrev sizeJ (v:Jet):=v.2.2.2.2
def jik (v:Jet) (b h e:ℕ) :Jet:=(b,port v,h,e,sizeJ v)
def turn (v:Jet) (b:ℕ):Jet:=jik v b (rune v) (invp v)

def cap (s:ℕ):Jet:= dec (fore s)
lemma capK {α} [Wire α] (v:PT α ℕ) (h:Kn v):Kn (fun x a=>cap (v x a)):=
                 Kn.unpack.comp h.top
lemma jikK {α} [Wire α] (v:PT α Jet) (b h e:PT α ℕ) (hv:Kn v) (hb:Kn b) (hh:Kn h) (he:Kn e):
     Kn (fun x a=> jik (v x a) (b x a) (h x a) (e x a)) :=
      hb.tuple (hv.right.left.tuple (hh.tuple (he.tuple hv.right.right.right.right)))
lemma turnK {α} [Wire α] (v:PT α Jet) (b:PT α ℕ) (hv:Kn v) (hb:Kn b):
     Kn (fun x a=>turn (v x a) (b x a)) :=
       jikK _ _ _ _ hv hb hv.right.right.left hv.right.right.right.left
def tug (s:ℕ)(v:Jet):ℕ:= cord (enc v) s
lemma tugK {α} [Wire α] (s:PT α ℕ) (v:PT α Jet) (hs:Kn s)(hv:Kn v):
   Kn (fun x a=>tug (s x a) (v x a)) := (Kn.wash.comp hv).push hs
@[simp] lemma cap_tug (v:Jet ) (s): cap (tug s v)=v:= by simp [cap,tug]
@[simp] lemma aft_tug (v:Jet ) (s): aft (tug s v)=s:= by simp [tug]
end Jet
abbrev Card := ℕ×ℕ×ℕ×ℕ

def cname (b p i s:ℕ): ℕ := enc ((b,p,i,s):Card)
abbrev prime (p) :=cname 0 p 0 0
abbrev tell (p i s):=cname 1 p i s
abbrev going (p s):=cname 2 p 0 s
abbrev done (p) :=cname 3 p 0 0
lemma cnameK {α} [Wire α] (b p i s:PT α ℕ) (h:Kn b) (hp:Kn p) (hi:Kn i) (hs:Kn s):
    Kn (fun x a=>cname (b x a ) (p x a ) (i x a ) (s x a)) :=
       Kn.wash.comp (h.tuple (hp.tuple (hi.tuple hs)))
@[simp] lemma decname (b p i s):dec (cname b p i s)=((b,p,i,s):Card) := Wire.eq _

namespace Bow
variable (p:Bow)

def readyJ (x:Word) (a:Node):Jet:=(0,a.2,0,0,p.padding.f x a.1)
lemma readyK : Kn p.readyJ :=
    (Kn.fix _).tuple (Kn.next.tuple ((Kn.fix _).tuple ((Kn.fix _).tuple (p.padding.runs.comp Kn.first))))

def hint (α:ℕ)(f:Jet):Bean:=(α,Jet.port f,Jet.rune f)

abbrev Xtra := Node×ℕ×ℕ
def along (x:Word) (a:Xtra) :=
   p.other.f x (hint a.2.2 (dec a.2.1))
def journey : PT Node ℕ :=
    sweep p.along (fun x a=> windback x a.2) (fun x a=>p.alpha.f x a.1)
               (fun x a=>p.clipA.f x a.1)
lemma hintK {α} [Wire α] (f:PT α ℕ)(v:PT α Jet)(h:Kn f)(e:Kn v):
    Kn (fun x a=> hint (f x a) (v x a)):=h.tuple (e.right.left.tuple e.right.right.left)
lemma journeyK : Kn p.journey:= Kn.sweepK _ _ _ _
        (p.other.runs.comp (hintK _ _ Kn.next.right (Kn.unpack.comp Kn.next.left)))
        (Kn.windbackK.comp Kn.next) (p.alpha.runs.comp Kn.first)
              (p.clipA.runs.comp Kn.first)

abbrev Cap := ℕ×ℕ×ℕ
abbrev Lift := ℕ×ℕ×ℕ×ℕ
abbrev purec (i:ℕ):Cap :=(0,0,i)
def inprog (x:Word) (a:Lift) : Cap :=
   let (q,o,s,i):=a
   let v:=Jet.cap s
   let t:=aft s
   let α:=p.journey x (q,t)
   let H:= hint α v
   let work := fun z=> going o (Jet.tug t z) + 1
   if Jet.band v=0 then (1,p.ask.f x (α,Jet.port v), if i=0 then 0 else work (Jet.jik v 1 i 0))
   else if Jet.band v=1 then (2,p.before.f x H,work (Jet.jik v 2 (Jet.rune v) i))
   else if Jet.band v=2 then
      if p.haskid.f x H then
         purec (going o (Jet.tug (Jet.tug t (Jet.turn v 3)) (p.readyJ x (p.other.f x H,p.passp.f x H)))+1)
      else purec (work (Jet.turn v 4))
   else if Jet.band v=4 then (2,p.knot.f x H,work (Jet.turn v 5))
   else if Jet.band v=5 then
         if t≤1 then purec (done o+1)
         else purec (going o (Jet.tug (aft t) (Jet.turn (Jet.cap t) 4))+1)
   else purec 0

lemma pureK {α} [Wire α] (x:PT α ℕ) (h:Kn x) : Kn (fun w a=>purec (x w a)) :=
   (Kn.fix _).tuple ((Kn.fix _).tuple h)
lemma goingK {α} [Wire α] (x y:PT α ℕ)(h:Kn x)(g:Kn y) :
    Kn (fun w a=> going (x w a ) (y w a)+1) :=
            (cnameK _ _ _ _ (Kn.fix 2) h (Kn.fix 0) g).succ

set_option maxRecDepth 2048 in
lemma progK: Kn p.inprog:=by
    have h:Kn (fun (_:Word) (a:Lift)=>a.1):=Kn.first
    have e:Kn (fun (_:Word)(a:Lift)=>a.2):=Kn.next
    let o:PT Lift ℕ:=fun _ a=>a.2.1
    let T:PT Lift ℕ:=fun _ a=> aft a.2.2.1
    let F:PT Lift Jet:=fun _ a=> Jet.cap a.2.2.1
    let A:PT Lift ℕ:=fun x a=> p.journey x (a.1,T x a)
    have hs:Kn o:=e.left
    have hw:Kn T:=e.right.left.tail
    have hf:Kn F:=Jet.capK _ e.right.left
    have ha:Kn A:=p.journeyK.comp (h.tuple hw)
    have hp:=hintK A F ha hf
    let work (z:PT Lift Jet):PT Lift ℕ:=fun x a=>going (o x a) (Jet.tug (T x a) (z x a))+1
    have hk (v : PT Lift Jet) (h:Kn v):Kn (work v):=goingK _ _ hs (Jet.tugK _ _ hw h)
    have hi:=e.right.right
    have hc:=hf.left
    let xik (k b:ℕ) (u:PT Lift ℕ) := fun x a=>Jet.jik (F x a) k (u x a) b
    let w2 : PT Lift Jet:=fun x a=>Jet.jik (F x a) 2 (Jet.rune (F x a)) (a.2.2.2)
    have hy : Kn w2:=Jet.jikK _ _ _ _ hf (Kn.fix _) hf.right.right.left hi
    let turn (i:ℕ):PT Lift Jet:= fun x a=>Jet.turn (F x a) i
    have hx(i):Kn (turn i):=Jet.turnK _ _ hf (Kn.fix _)
    exact hc.cond_eq (Kn.fix 0)
       ((Kn.fix _).tuple ((p.ask.runs.comp (ha.tuple hf.right.left)).tuple
                (hi.cond_eq (Kn.fix 0) (Kn.fix _) (hk (xik 1 0 _) (Jet.jikK _ _ _ _ hf (Kn.fix _) hi (Kn.fix _))))))
       (hc.cond_eq (Kn.fix 1)
          ((Kn.fix _).tuple ((p.before.runs.comp hp).tuple (hk _ hy)))
       (hc.cond_eq (Kn.fix 2)
         ((p.haskid.runs.comp hp).cond
            (pureK _ (goingK _ _ hs (Jet.tugK _ _ (Jet.tugK _ _ hw (hx 3))
                    (p.readyK.comp ((p.other.runs.comp hp).tuple (p.passp.runs.comp hp))))))
            (pureK _ (hk _ (hx 4))))
       (hc.cond_eq (Kn.fix 4)
          ((Kn.fix _).tuple ((p.knot.runs.comp hp).tuple (hk _ (hx 5))))
       (hc.cond_eq (Kn.fix 5)
          (hw.cond_le (Kn.fix 1)
             (pureK _ ((cnameK _ _ _ _ (Kn.fix 3) hs (Kn.fix 0) (Kn.fix 0)).succ))
             (pureK _ (goingK _ _ hs (Jet.tugK _ _ hw.tail
                (Jet.turnK _ _ (Jet.capK _ hw) (Kn.fix 4))))))
          (Kn.fix _)))))

end Bow
end ExactDerandomization.Sub

end

section

namespace ExactDerandomization.Sub
open Relay Mint Swirl Counter
namespace Bow
variable (p:Bow)

abbrev Cover:= ℕ×Card×ℕ
def air (x:Word)(a:Cover):Cap :=
   let (q,v,h):=a
   let (b,o,i,w):=v
   if b=0 then purec (if o<p.ports.f x q then tell o 0 1+1 else 0)
   else if b=1 then
     if i<p.steps.f x q then (1,p.dress.f x (q,o,i),tell o (i+1) (cord h w)+1)
     else
       let z:=p.scent.f x (q,w)
       purec (going z (Jet.tug 1 (p.readyJ x (p.alpha.f x q,o)))+1)
   else if b=2 then p.inprog x (q,o,w,h)
   else purec 0

def loom (x:Word)(a:Bean) := p.air x (a.1,dec a.2.1,a.2.2)
lemma airK : Kn p.air:= by
   have hp:Kn (fun (_:Word)(a:Cover)=>a.2) :=Kn.next
   have h:Kn (fun (_:Word)(a:Cover)=>a.1) :=Kn.first
   have hv:=hp.left
   have hb:=hv.left
   have ho:=hv.right.left
   have hi:=hv.right.right.left
   have hw:=hv.right.right.right
   exact hb.cond_eq (Kn.fix 0)
       (pureK _ (ho.cond_lt (p.ports.runs.comp h)
            ((cnameK _ _ _ _ (Kn.fix 1) ho (Kn.fix 0) (Kn.fix 1)).succ) (Kn.fix 0)))
       (hb.cond_eq (Kn.fix 1)
          (hi.cond_lt (p.steps.runs.comp h)
             ((Kn.fix 1).tuple ((p.dress.runs.comp (h.tuple (ho.tuple hi))).tuple
                  ((cnameK _ _ _ _ (Kn.fix 1) ho hi.succ (hp.right.push hw)).succ)))
             (pureK _ (goingK _ _ (p.scent.runs.comp (h.tuple hw)) (Jet.tugK _ _ (Kn.fix 1)
                                     (p.readyK.comp ((p.alpha.runs.comp h).tuple ho))))))
       (hb.cond_eq (Kn.fix 2)
            (p.progK.comp (h.tuple (ho.tuple (hw.tuple hp.right))))
            (Kn.fix _)))
lemma loomK : Kn p.loom:=p.airK.comp (Kn.first.tuple ((Kn.unpack.comp Kn.next.left).tuple Kn.next.right))

/-- token extraction (destination) -/
def peel (v:Card):ℕ :=
   let f:=Jet.cap v.2.2.2
   if Jet.band f=2 then Jet.invp f else 0
def peel0 (_:Word)(a:Bean):ℕ:=
    let v:= (dec a.2.2:Card)
    if v.1=2 then peel v else 0
lemma peelK : Kn peel0:=by
    let d (_:Word) (a:Bean):= (dec a.2.2:Card)
    have he:Kn d:=Kn.unpack.comp Kn.next.right
    have hf:= Jet.capK _ he.right.right.right
    exact he.left.cond_eq (Kn.fix 2)
       (hf.left.cond_eq (Kn.fix 2) hf.right.right.right.left (Kn.fix 0)) (Kn.fix 0)

def stripe0 (x:Word)(a:Bean):Bool :=
    let (q,v,i):=a
    let t:= (dec v:Card).2.1
    if i=0 then if v=done t then true else if v=Sub.prime t then decide (t < p.ports.f x q) else false
    else false
lemma stripeK : Kn p.stripe0:= by
    let d (_:Word) (a:Bean):= (dec a.2.1:Card)
    have he:Kn d:=Kn.unpack.comp Kn.next.left
    have hi:Kn (fun (_:Word) (a:Bean)=>a.2):=Kn.next
    have ht:=he.right.left
    exact hi.right.cond_eq (Kn.fix 0)
       (hi.left.cond_eq (cnameK _ _ _ _ (Kn.fix 3) ht (Kn.fix 0) (Kn.fix 0))
              (Kn.fix _) (hi.left.cond_eq (cnameK _ _ _ _ (Kn.fix 0) ht (Kn.fix 0) (Kn.fix 0))
                      (ht.lt (p.ports.runs.comp Kn.first)) (Kn.fix _)))
       (Kn.fix _)

def reader (x:Word)(a:Node) := p.loom x (a.1,a.2,0)
lemma readerK : Kn p.reader := p.loomK.comp (Kn.first.tuple (Kn.next.tuple (Kn.fix _)))

def Rune0 (p:Bow): Rune :=
    ⟨⟨fun x a=> (p.reader x a).1, p.readerK.left⟩,⟨fun x a=> (p.reader x a).2.1, p.readerK.right.left⟩,
       ⟨fun x a=> (p.loom x a).2.2,p.loomK.right.right⟩,
       ⟨_,peelK⟩,⟨_,p.stripeK⟩⟩

end Bow
end ExactDerandomization.Sub

end

section

namespace ExactDerandomization.Sub
open Relay Mint Swirl Counter

/-- Settings for local correctness at a contour invocation. -/
structure Quill where
    b : Bow
    v : Valve
    s : Mill.Fuel
    k : ℕ
    A : ℕ
    grit : ℕ→ℕ
    bulk : ℕ→ℕ

namespace Quill
variable (u:Quill)
def p : Mill:=⟨u.A,u.b.Rune0,u.v⟩
abbrev x0 :=u.s.l.x
abbrev q:=u.s.q
abbrev B:=u.p.O u.x0 u.q
abbrev H:=u.b.steps.f u.x0 u.q
abbrev child:=u.b.alpha.f u.x0 u.q
abbrev ceiling:=u.b.clipA.f u.x0 u.q

structure Tidy : Prop where
    run : u.p.Fires u.s
    gain : 100 ≤ u.k
    reach : 1000*u.k^2 ≤ u.A
    reserve : Mill.Reserve u.p u.s
    gap0 : u.v.D.f u.x0 u.q=1
    early : u.H ≤ u.B.t+u.k
    steady : u.grit u.child =1
    openR : u.bulk u.child≤u.B.w

def Cush (v i : ℕ) := lb v≤20*u.k*i ∧ i≤4*lb v
lemma leftP (a b:ℕ): lb a ≤ lb (enc (a,b)) :=lb_mono (cord_fine a _).2.1.le
lemma rightP (a b:ℕ): lb b ≤ lb (enc (a,b)) :=lb_mono (le_trans (by omega: b≤b+1) (cord_fine a _).1.le)

lemma cname_l (b p i s) :
    lb (cname b p i s) ≤2*(lb b+lb p+lb i)+lb s+6 ∧
       lb p ≤ lb (cname b p i s) ∧ lb s ≤ lb (cname b p i s):= by
   let v : ℕ:=enc ((i,s):ℕ×ℕ)
   let w : ℕ:=enc ((p,v):ℕ×ℕ)
   have hp: w=enc (p,i,s):=rfl
   have hz: cname b p i s=enc (b,w):=rfl
   rw [hz]
   have he : lb w≤2*lb p+lb v+2:=measure_pair _ _
   have hs : lb v≤2*lb i+lb s+2:=measure_pair _ _
   have ht : lb (enc (b,w)) ≤ 2*lb b+lb w+2:=measure_pair _ _
   have hy : lb p≤lb w:=leftP p v
   have hy2:=rightP b w; have hy3 : lb v≤lb w:=rightP p v; have hy4 : lb s≤lb v:=rightP i s
   omega

lemma inProgG {k : ℕ} {label S} (h:u.Tidy)
    (hv: u.H≤ lb label) (he: lb label ≤ u.k*(u.H+1)) (ht:k≤ lb S) (hs:lb S ≤ 1+4*u.k*k) :
   u.Cush (going label S) (u.H+k+1) :=by
   have hp:=h.gain
   obtain ⟨h1,h2,h3⟩:=cname_l 2 label 0 S
   have hc : lb 2=2:=rfl
   rw [hc,lb_zero] at h1
   change _ ≤ _ at ht
   unfold Cush going; constructor
   · nlinarith
   have hz:=lb_pos (cname 2 label 0 S)
   omega

lemma capDone {z} (h:u.Tidy) (hv:u.H≤lb z) (he:lb z≤u.k*(u.H+1)):
    u.Cush (done z) (u.H+1):= by
   obtain ⟨h1,h2,h3⟩:=cname_l 3 z 0 0
   have hu : lb 3=2:=rfl
   rw [lb_zero,hu] at h1; have hp:=h.gain
   unfold Cush done; constructor
   · nlinarith
   have hz:=lb_pos (cname 3 z 0 0); omega
lemma capPrime {p} (h:u.Tidy) (he:lb p≤u.k):u.Cush (prime p) 1:= by
   obtain ⟨h1,h2,h3⟩:=cname_l 0 p 0 0
   rw [lb_zero] at h1
   have hp:=h.gain; unfold Cush prime
   have hz:=lb_pos (cname 0 p 0 0); omega
lemma capTell {p i s} (h:u.Tidy) (he:lb p≤u.k)
    (hy:i+1≤lb s)(hz:lb s ≤1+3*u.k*i):u.Cush (tell p i s) (i+1):= by
   obtain ⟨h1,h2,h3⟩:=cname_l 1 p i s
   rw [lb_one] at h1
   have hp:=h.gain
   have hh:=lb_le_inc i
   unfold Cush tell; constructor
   · nlinarith
   omega

lemma prepaid {v i} (h:u.Tidy) (e:u.Cush v i) (he:i≤u.H+u.B.w+1):
    lb v≤Mill.prize u.p u.s := by
   have hw : 1≤u.B.w:=h.run.wp
   have hh:= h.early; have hz:=h.gain; have ht:=h.reach
   obtain ⟨he1,he2⟩:=e
   have h1 : i≤u.B.t+ (u.k+2)*u.B.w :=by nlinarith
   change lb v ≤ charge u.A u.B.w u.B.t
   have h2 : 20*u.k*(u.k+2) ≤ u.A*u.A:=by
      have hz : 10*u.k ≤ u.A:=by nlinarith
      nlinarith [Nat.mul_le_mul hz hz]
   have h3 : 20*u.k≤ u.A:=by nlinarith
   unfold charge
   nlinarith [Nat.mul_le_mul_right u.B.w h2,Nat.mul_le_mul_right u.B.t h3,Nat.mul_le_mul_left (20*u.k) h1]

lemma team0 {v i w j} (h:u.Tidy) (hv:u.Cush v i) (hw:u.Cush w j) (he:i≤4*j) :
   lb v≤lb w*u.A:= by
   have ha:=h.gain; have he1:=h.reach
   have h2:i≤16*lb w:=by have hp:=hw.2; omega
   have h3:20*u.k*16 ≤ u.A:=by nlinarith
   have hz:=hv.1
   nlinarith [Nat.mul_le_mul_right (lb w) h3,Nat.mul_le_mul_left (20*u.k) h2]
lemma team {v i w j} (h:u.Tidy) (hv:u.Cush v i) (hw:u.Cush w j) (hi:i≤u.H+u.B.w+1)
    (hj:j≤u.H+u.B.w+1)(he:i≤4*j) (hf:j≤4*i):
    Mill.fitting u.p u.s v w := ⟨u.prepaid h hv hi,u.prepaid h hw hj,u.team0 h hv hw he,u.team0 h hw hv hf⟩

lemma structure_pay {v i f} (h:u.Tidy) (hv:u.Cush v i)
    (he:i≤u.H+(u.B.w-u.v.depth.f u.x0 f)+1)
    (ht:u.v.depth.f u.x0 f+1 ≤ u.B.w) (hh:u.v.clock.f u.x0 f=0) :
   Mill.faith u.p u.s v f := by
   let x:=u.B.w-u.v.depth.f u.x0 f; have hx:1≤x:=by dsimp only [x]; omega
   have hz:=h.gain; have hg:=h.reach
   change _+_≤_ ∧ span u.A x u.B.t (u.v.clock.f u.x0 f) (lb v+1)
   refine ⟨by change u.v.depth.f u.x0 f+u.v.D.f u.x0 u.q≤_; rw [h.gap0]; exact ht,?_⟩
   rw [hh]
   have hp:=hv.1
   have h1:i≤u.B.t+(u.k+2)*x:=by have hh1:=h.early; change i≤u.H+x+1 at he; nlinarith
   have h2:20*u.k≤u.A:=by nlinarith
   have h3:20*u.k*(u.k+2)+1≤u.A*u.A:=by nlinarith
   unfold span; nlinarith [Nat.mul_le_mul_right u.B.t h2,Nat.mul_le_mul_right x h3,Nat.mul_le_mul_left (20*u.k) h1]

lemma score_pay {v i f}(h:u.Tidy)(hv:u.Cush v (i+1))
   (he:i+u.v.clock.f u.x0 f≤ u.B.t+u.k) (hs:u.v.depth.f u.x0 f+1≤u.B.w):
    Mill.faith u.p u.s v f := by
   let x:=u.B.w-u.v.depth.f u.x0 f; have hx:1≤x:=by dsimp only [x]; omega
   have hp:=h.reach; have hg:=h.gain
   change _+_≤_ ∧ span u.A x u.B.t (u.v.clock.f u.x0 f) (lb v+1)
   refine ⟨by change u.v.depth.f u.x0 f+u.v.D.f u.x0 u.q≤_; rw [h.gap0]; exact hs,?_⟩
   have hz:=hv.1; have h1:20*u.k≤u.A:=by nlinarith
   have h2:u.k+2≤u.A:=by nlinarith
   have ht : u.A*(u.k+2) ≤ u.A*u.A*x := by
      have hm:u.A*(u.k+2) ≤ u.A*u.A:= Nat.mul_le_mul_left u.A h2
      nlinarith [Nat.mul_le_mul_left (u.A*u.A) hx]
   unfold span; nlinarith [Nat.mul_le_mul_left u.A he,Nat.mul_le_mul_right (i+1) h1]

end Quill
end ExactDerandomization.Sub

end

section

namespace ExactDerandomization.Sub
open Relay Mint Swirl Counter
namespace Quill
variable (u:Quill)

abbrev Cr (x y : Swirl.Dot) := u.p.minted u.s x y
abbrev Track := Relation.ReflTransGen u.Cr

abbrev Aq (b p i s : ℕ) (j) := u.b.air u.x0 (u.q,(b,p,i,s),j)
lemma Ax (b p i s j) : u.b.loom u.x0 (u.q,cname b p i s,j) = u.Aq b p i s j := by simp [Aq,Bow.loom]
lemma deco (b p i s):
    u.p.compo u.s (cname b p i s)= (u.Aq b p i s 0).1 :=
        congrArg (fun x=>x.1) (u.Ax b p i s 0)
lemma tripk (b p i s) : u.p.slipk u.s (cname b p i s)=(u.Aq b p i s 0).2.1 :=
    congrArg (fun x=>x.2.1) (u.Ax b p i s 0)
lemma stable (b p i s t v) : u.p.label u.s (cname b p i s) v t=(u.Aq b p i s t).2.2 :=
    congrArg (fun x=>x.2.2) (u.Ax b p i s t)

abbrev garnish (p i) := u.b.dress.f u.x0 (u.q,p,i)
def chainR (p c:ℕ) (i:ℕ):ℕ := forNat (fun k v=> cord (u.s.echo (u.garnish p k) c) v) 1 i
lemma chain_next (p c i) : u.chainR p c (i+1)=cord (u.s.echo (u.garnish p i) c) (u.chainR p c i):=rfl
abbrev scent (p c) := u.b.scent.f u.x0 (u.q,u.chainR p c u.H)

def Stringent (z:ℕ):=u.H ≤ lb z ∧ lb z ≤ u.k*(u.H+1)

structure Gown (p c:ℕ):Prop where
    lengthp : lb p≤ u.k
    known : p < u.b.ports.f u.x0 u.q
    lens : ∀ i < u.H,lb (u.s.echo (u.garnish p i) c) ≤ u.k
    law0 : ∀ i < u.H, i+u.v.clock.f u.x0 (u.garnish p i) ≤ u.B.t+u.k ∧
                 u.v.depth.f u.x0 (u.garnish p i)+1 ≤ u.B.w ∧
                 u.v.tap.f u.x0 (u.garnish p i)=true
    hair : u.Stringent (u.scent p c)

lemma chain_size {p c} (h:u.Tidy)(e:u.Gown p c){i}(hi:i≤u.H) :
   i+1 ≤ lb (u.chainR p c i) ∧ lb (u.chainR p c i) ≤1+3*u.k*i ∧ 1≤u.chainR p c i:= by
    induction i with
    | zero=>change 0+1≤lb 1 ∧ lb 1≤_ ∧ 1≤1; rw [lb_one]; omega
    | succ i ih=>
      rw [u.chain_next]; obtain ⟨ha,hb,hc⟩:=ih (by omega)
      have hz:=lb_cord (u.s.echo (u.garnish p i) c) _ hc
      rw [hz]
      have hw:= lb_pos (u.s.echo (u.garnish p i) c)
      have hk:= e.lens i hi
      have hf:= h.gain
      refine ⟨by omega,by nlinarith,(cord_fine ..).2.2.le⟩

lemma pointing {p c i} (h:u.Tidy)(e:u.Gown p c) (hi:i≤u.H):
   u.Cush (tell p i (u.chainR p c i)) (i+1) :=
    let hk:= u.chain_size h e hi
    u.capTell h e.lengthp hk.1 hk.2.1

lemma prepared {p c}(h:u.Tidy) (g:u.Gown p c)(he:c∈u.s.domain):
    u.Track (prime p,c) (tell p u.H (u.chainR p c u.H),c):=by
   have e0: u.Cr (prime p,c) (tell p 0 1,c):=by
      have hk0 := u.pointing h g (Nat.zero_le _)
      change u.Cush (tell p 0 1) (0+1) at hk0
      apply u.p.meets0 u.s h.reserve
          (u.team h (u.capPrime h g.lengthp) hk0 (by omega) (by omega) (by omega) (by omega)) _ _ he
      · rw [u.deco]; rfl
      rw [u.stable]; simp [Aq,Bow.air,g.known,Bow.purec]
   suffices h:∀ i≤ u.H,u.Track (prime p,c) (tell p i (u.chainR p c i),c) by exact h _ le_rfl
   intro i hi
   induction i with
   | zero=> exact Relation.ReflTransGen.single e0
   | succ i ih=>
     apply Relation.ReflTransGen.tail (ih (by omega))
     have hz:=u.pointing h g (show i≤u.H by omega); let w:=tell p i (u.chainR p c i)
     have hi': i < u.b.steps.f u.x0 u.q:=hi
     have hp0:u.p.slipk u.s w=u.garnish p i:=by unfold w; rw [u.tripk]; simp [Aq,Bow.air,hi',garnish]
     apply u.p.meets1 u.s h.reserve (u.team h hz (u.pointing h g hi) (by omega) (by omega) (by omega) (by omega)) _ _ _ he
     · rw [u.deco]; simp [Aq,Bow.air,hi']
     · have hx:=hp0; unfold w at hx
       rw [hx,u.stable]
       simp [Aq,Bow.air,hi',u.chain_next]
     · obtain ⟨ha,hb,hc⟩:= g.law0 i hi
       change u.p.afoot u.s w
       unfold Mill.afoot; rw [hp0]
       exact ⟨hc,u.score_pay h hz ha hb⟩

lemma shut {p c} : u.p.mate u.s (done p,c) := by
   apply u.p.cinder0
   · rw [u.deco]; rfl
   intro i; rw [u.stable]; rfl
lemma different {a b c} : going a b≠done c:= by
   intro he
   have hc:= congrArg (fun x=> (dec x:Card).1) he
   simp [going,done] at hc

end Quill
end ExactDerandomization.Sub

end

section

namespace ExactDerandomization.Sub
open Relay Mint Swirl Counter
namespace Quill
variable (u:Quill)

abbrev fill (a p) := u.b.readyJ u.x0 (a,p)
abbrev hear (a p) := u.b.ask.f u.x0 (a,p)
abbrev tagH (a p h:ℕ):Bean:=(a,p,h)
abbrev callB (a p h) := u.b.before.f u.x0 (tagH a p h)
abbrev callP (a p h) := u.b.knot.f u.x0 (tagH a p h)
abbrev lower (a p h) := u.b.other.f u.x0 (tagH a p h)
abbrev portD (a p h) := u.b.passp.f u.x0 (tagH a p h)
abbrev dives (a p h) := u.b.haskid.f u.x0 (tagH a p h)
def kidJ (a p h e b:ℕ) : Jet:= (u.fill a p).jik b h e
lemma turnkid (a p h e b g):Jet.turn (u.kidJ a p h e b) g=u.kidJ a p h e g := rfl

def calm (a t:ℕ):= u.v.clock.f u.x0 t=0 ∧ u.v.depth.f u.x0 t+u.grit a ≤ u.bulk a

def Orders (a q v:ℕ):Prop :=
    u.v.voted.f u.x0 (q,v)=true ∧ ∀ b,u.calm a ((u.v.reach b).f u.x0 (q,v))

def little (a:ℕ) (f:Jet) :=
   u.grit a≤lb (enc f) ∧ lb (enc f) ≤u.k*u.grit a

structure Rating (a p:ℕ) : Prop where
   insured : a≤u.ceiling
   positive : 1≤u.grit a
   reach : u.grit a ≤ u.bulk a
   littleR : u.little a (u.fill a p)
   get : u.v.tap.f u.x0 (u.hear a p)=true
   heat : u.calm a (u.hear a p)

structure Bolts (a p h e :ℕ) : Prop where
    before0 : u.little a (u.kidJ a p h 0 1)
    passed : ∀ i ≤ 5, u.little a (u.kidJ a p h e i)
    forward0 : u.Orders a (u.callB a p h) e
    post : u.Orders a (u.callP a p h) 0

/-- canonical path selection supplies a coherent and costed path, not just a
validity bit. -/
structure Chess (a p h e c z y w:ℕ) : Prop where
    hr : u.Rating a p
    kin : u.Bolts a p h e
    hx : c∈u.s.domain
    hz : z∈u.s.domain
    hy : y∈u.s.domain
    hw : w∈u.s.domain
    chosen : u.s.echo (u.hear a p) c=h
    extant : h≠0
    peak : u.s.stream (u.callB a p h) e true c=some z
    erode : u.s.stream (u.callP a p h) 0 true y=some w

/-- Valid terminal program coherence/cost trace -/
inductive Herd : ℕ→ℕ→ℕ→ℕ→ℕ→ℕ→Prop

   | solo {a p h e c z w} (h0:u.Chess a p h e c z z w) (hd:u.dives a p h=false):
                         Herd a p c h e w
   | pair {a p h e c z y w f g} (hr:u.Chess a p h e c z y w) (hv:u.dives a p h=true)
            (hd:u.bulk (u.lower a p h)+u.grit a ≤ u.bulk a)
            (hy:u.grit (u.lower a p h) ≤ 2*u.grit a)
            (he:Herd (u.lower a p h) (u.portD a p h) z f g y):
                          Herd a p c h e w

lemma Herd.on {u:Quill} {a p c h e w} (hh:u.Herd a p c h e w) :
    u.Rating a p ∧ u.Bolts a p h e:=by cases hh with | solo h0 _=> exact ⟨h0.hr,h0.kin⟩ | pair hr _ _ _ _=>exact ⟨hr.hr,hr.kin⟩

inductive Lane (a p c:ℕ) : Option ℕ→Prop
   | dry (hr:u.Rating a p) (hc:c∈u.s.domain) (hh:u.s.echo (u.hear a p) c=0) :
               Lane a p c none
   | born {h e w} (hs:u.Herd a p c h e w) : Lane a p c (some w)

abbrev wagon (l:List ℕ)(f:Jet) := mesh (enc f::l)
lemma wagon_eq (l f) : wagon l f=Jet.tug (mesh l) f:= rfl
def cart (o:ℕ)(l:List ℕ)(f:Jet) := going o (wagon l f)

structure Course (l:List ℕ) (a m:ℕ):Prop where
    dimensional : m+u.bulk a ≤ u.B.w
    room0 : m ≤ lb (mesh l)
    room1 : lb (mesh l) ≤ 1+4*u.k*m
    link : Scan u.ceiling (fun j k=> u.b.along u.x0 ((u.q,0),j,k)) u.child l.reverse a

lemma coal {l a m p o f} (h:u.Tidy)(hx:u.Rating a p)(hh:u.Course l a m)
    (hv:u.little a f)(hz:u.Stringent o):
    u.Cush (cart o l f) (u.H+(m+u.grit a)+1) := by
   apply inProgG u h hz.1 hz.2
   · rw [wagon, measure_mesh]; have := hv.1; have := hh.room0; omega
   · rw [wagon, measure_mesh]; have := hv.2; have := hh.room1
     have he:=hx.positive; have hp:=h.gain
     nlinarith

lemma rag {l a m p} (hx:u.Rating a p)(hh:u.Course l a m) :
    u.H+(m+u.grit a)+1 ≤ u.H+u.B.w+1:=by
   have he:=hx.reach; have hz:=hh.dimensional; omega

lemma aloft {l a m} (hh:u.Course l a m):
    u.b.journey u.x0 (u.q,mesh l)=a:= by
   unfold Bow.journey
   exact exact_sweep (l:=l.reverse) hh.link (windback_mesh ..)

lemma goto {l a m p h t} {f:Jet} (ht:u.Tidy)(hp:u.Rating a p)
    (hz:u.Course l a m) (hy:u.Rating (u.lower a p h) t)
    (he:u.bulk (u.lower a p h)+u.grit a ≤ u.bulk a)
    (hi:u.little a f) (hh:Jet.rune f=h)(hk:Jet.port f=p):
    u.Course (enc f::l) (u.lower a p h) (m+u.grit a) := by
   obtain ⟨h1,h2,h3,h4⟩:=hz
   refine ⟨by omega,?_,?_,?_⟩
   · rw [measure_mesh]; have hz:=hi.1; omega
   · rw [measure_mesh]; have hz:=hi.2; have hg:=ht.gain; have hh:=hp.positive
     nlinarith
   rw [List.reverse_cons]
   exact Grid.Scan.snatch h4 (by
      simp [Bow.along,Bow.hint,hk,hh,lower,tagH]) hy.insured

lemma price1 {l a m p t} (hx:u.Rating a p)(hh:u.Course l a m) (hz:u.calm a t) :
   u.v.depth.f u.x0 t+1≤u.B.w ∧
       u.H+(m+u.grit a)+1 ≤ u.H+(u.B.w-u.v.depth.f u.x0 t)+1:= by
   have he:=hx.positive; have hv:=hh.dimensional; have ha:=hz.2; omega

lemma timeok {t l a m p f o} (h:u.Tidy)(hx:u.Rating a p)(he:u.Course l a m)
   (hy:u.little a f) (ho:u.Stringent o)
   (hh:u.calm a t): Mill.faith u.p u.s (cart o l f) t :=
     let hz:=u.price1 hx he hh
     u.structure_pay h (u.coal h hx he hy ho) hz.2 hz.1 hh.1

lemma ae {l o i f} :
    u.b.loom u.x0 (u.q,cart o l f,i) = u.b.inprog u.x0 (u.q,o,wagon l f,i):=
       u.Ax 2 o 0 (wagon l f) i

lemma resultv {l o i f m a} (he:u.Course l a m):
    u.b.loom u.x0 (u.q,cart o l f,i) =
   let t:=mesh l
   let v:=f
   let α:=a
   let _:=u.q
   let x:=u.x0
   let H:= Bow.hint α v
   let p:=u.b
   let work := fun z=> going o (Jet.tug t z)+1
   if Jet.band v=0 then (1,p.ask.f x (α,Jet.port v), if i=0 then 0 else work (Jet.jik v 1 i 0))
   else if Jet.band v=1 then (2,p.before.f x H,work (Jet.jik v 2 (Jet.rune v) i))
   else if Jet.band v=2 then
      if p.haskid.f x H then
         Bow.purec (going o (Jet.tug (Jet.tug t (Jet.turn v 3)) (p.readyJ x (p.other.f x H,p.passp.f x H)))+1)
      else Bow.purec (work (Jet.turn v 4))
   else if Jet.band v=4 then (2,p.knot.f x H,work (Jet.turn v 5))
   else if Jet.band v=5 then
         if t≤1 then Bow.purec (done o+1)
         else Bow.purec (going o (Jet.tug (aft t) (Jet.turn (Jet.cap t) 4))+1)
   else Bow.purec 0:=by
      rw [u.ae]; simp only [Bow.inprog,wagon_eq,Jet.cap_tug,Jet.aft_tug,u.aloft he]

end Quill
end ExactDerandomization.Sub

end

section

namespace ExactDerandomization.Sub
open Relay Mint Swirl Counter Relation
namespace Quill
variable (u:Quill)

lemma taking {l a m p o v w}(ht:u.Tidy)(hp:u.Rating a p)
    (hx:u.Course l a m)(hy:u.Stringent o) (hz:u.little a v)(hh:u.little a w):
    Mill.fitting u.p u.s (cart o l v) (cart o l w):=
   u.team ht (u.coal ht hp hx hz hy) (u.coal ht hp hx hh hy) (u.rag hp hx) (u.rag hp hx) (by omega) (by omega)

abbrev future1 (o:ℕ)(l:List ℕ)(f:Jet) :ℕ:= cart o l f+1
lemma future_eq (o l f): future1 o l f=going o (Jet.tug (mesh l) f)+1:=rfl

lemma ore0 {l a m} (hp:u.Course l a m) (o p i:ℕ):
    u.b.loom u.x0 (u.q,cart o l (u.fill a p),i)=
      (1,u.hear a p,if i=0 then 0 else future1 o l (u.kidJ a p i 0 1)):=by
   rw [u.resultv hp]; simp only [Jet.band,fill,Bow.readyJ,ite_true]; rfl
lemma ore1 {l a m} (hp:u.Course l a m) (o p h i:ℕ):
    u.b.loom u.x0 (u.q,cart o l (u.kidJ a p h 0 1),i)=
             (2,u.callB a p h, future1 o l (u.kidJ a p h i 2)):= by
   rw [u.resultv hp]; simp only [kidJ,Jet.band,Jet.jik,OfNat.one_ne_ofNat,one_ne_zero,ite_false,ite_true]; rfl
lemma ore4 {l a m} (hp:u.Course l a m) (o p h e i:ℕ):
    u.b.loom u.x0 (u.q,cart o l (u.kidJ a p h e 4),i)=
             (2,u.callP a p h, future1 o l (u.kidJ a p h e 5)):=by
   rw [u.resultv hp]; rfl

lemma pairTok2 (a p h e o:ℕ) (l:List ℕ) (v) :
   u.p.wherep u.s v (cart o l (u.kidJ a p h e 2)) = e:=by
   change Bow.peel0 u.x0 (_, _, cart ..) = _
   simp [Bow.peel0,Bow.peel, cart,going,wagon_eq,kidJ,Jet.jik,Jet.band,Jet.invp]
lemma pairTok5 (a p h e o:ℕ)(l:List ℕ) (v):
   u.p.wherep u.s v (cart o l (u.kidJ a p h e 5))=0:=by
   change Bow.peel0 u.x0 (_, _, cart ..) = _
   simp [Bow.peel0,Bow.peel,cart,going,wagon_eq,kidJ,Jet.jik,Jet.band]

lemma first0 {l a m p o c} (_:u.Tidy)(_:u.Rating a p)(hc:u.Course l a m)(_:u.Stringent o)
    (he:u.s.echo (u.hear a p) c=0):
    u.p.mate u.s (cart o l (u.fill a p),c):= by
   apply u.p.cinder1
   · exact congrArg Prod.fst (u.ore0 hc o p 0)
   intro i
   have hS: u.p.slipk u.s (cart o l (u.fill a p))=u.hear a p:=
      congrArg (fun x=> x.2.1) (u.ore0 hc o p 0)
   rw [hS,he]
   exact congrArg (fun x=>x.2.2) (u.ore0 hc o p 0)

lemma helm {l a m p o h e c z y w} (ht:u.Tidy)(hp:u.Chess a p h e c z y w)
    (hx:u.Course l a m)(ho:u.Stringent o):
    u.Cr (cart o l (u.fill a p),c) (cart o l (u.kidJ a p h 0 1),c):= by
   let v:=cart o l (u.fill a p)
   have h1:=u.ore0 hx o p
   have hs:u.p.slipk u.s v=u.hear a p:=congrArg (fun x=>x.2.1) (h1 0)
   change u.Cr (v,c) _
   apply u.p.meets1 u.s ht.reserve (u.taking ht hp.hr hx ho hp.hr.littleR hp.kin.before0) ?_ ?_ ?_ hp.hx
   · exact congrArg Prod.fst (h1 0)
   · rw [hs,hp.chosen]
     exact (congrArg (fun x=>x.2.2) (h1 h)).trans (ite_eq_right hp.extant)
   unfold Mill.afoot; rw [hs]
   exact ⟨hp.hr.get, u.timeok ht hp.hr hx hp.hr.littleR ho hp.hr.heat⟩

lemma swift0 {l a m p f o t r} (ht:u.Tidy)(hr:u.Rating a p)
    (hx:u.Course l a m) (hv:u.little a f) (ho:u.Stringent o)
    (he:u.p.slipk u.s (cart o l f)=t)(h:u.Orders a t r):
    u.p.swift u.s (cart o l f) r:=by
   unfold Mill.swift Mill.swept; rw [he]
   exact ⟨h.1,fun b=>u.timeok ht hr hx hv ho (h.2 b)⟩

lemma prowl {l a m p o h e c z y w} (ht:u.Tidy)(hp:u.Chess a p h e c z y w)
    (hx:u.Course l a m)(ho:u.Stringent o):
    u.Cr (cart o l (u.kidJ a p h 0 1),c) (cart o l (u.kidJ a p h e 2),z):=by
   let f:=u.kidJ a p h 0 1
   let v:=cart o l f; have hq:=u.ore1 hx o p h
   have hs:u.p.slipk u.s v=u.callB a p h:=congrArg (fun x=>x.2.1) (hq 0)
   change u.Cr (v,c) _
   apply u.p.meets2 u.s ht.reserve (u.taking ht hp.hr hx ho hp.kin.before0 (hp.kin.passed 2 (by omega)))
        (congrArg Prod.fst (hq 0)) (u.pairTok2 ..).symm (congrArg (fun x=>x.2.2) (hq e))
        (u.swift0 ht hp.hr hx hp.kin.before0 ho hs hp.kin.forward0) hp.hx hp.hz
   rw [hs]
   exact hp.peak

lemma shiver {l a m p o h e c z y w} (ht:u.Tidy)(hp:u.Chess a p h e c z y w)
    (hx:u.Course l a m)(ho:u.Stringent o):
    u.Cr (cart o l (u.kidJ a p h e 4),y) (cart o l (u.kidJ a p h e 5),w):=by
   let f:=u.kidJ a p h e 4; let v:=cart o l f; have hq:=u.ore4 hx o p h e
   have hs:u.p.slipk u.s v=u.callP a p h:=congrArg (fun x=>x.2.1) (hq 0)
   change u.Cr (v,y) _
   apply u.p.meets2 u.s ht.reserve
           (u.taking ht hp.hr hx ho (hp.kin.passed 4 (by omega)) (hp.kin.passed 5 (by omega)))
           (congrArg Prod.fst (hq 0)) (u.pairTok5 ..).symm (congrArg (fun x=>x.2.2) (hq 0))
           (u.swift0 ht hp.hr hx (hp.kin.passed 4 (by omega)) ho hs hp.kin.post) hp.hy hp.hw
   rw [hs]; exact hp.erode

end Quill
end ExactDerandomization.Sub

end

section

namespace ExactDerandomization.Sub
open Relay Mint Swirl Counter Relation
namespace Quill
variable (u:Quill)
private abbrev nextJ (u:Quill) (a p h e) := enc (u.kidJ a p h e 3)
lemma ore2 {l a m} (hp:u.Course l a m) (o p h e i:ℕ):
   u.b.loom u.x0 (u.q,cart o l (u.kidJ a p h e 2),i)=
      if u.dives a p h then
         Bow.purec (future1 o (nextJ u a p h e::l) (u.fill (u.lower a p h) (u.portD a p h)))
      else Bow.purec (future1 o l (u.kidJ a p h e 4)):= by
   rw [u.resultv hp]
   unfold kidJ Jet.band Jet.jik; rfl

lemma blink0 {v i z}(ht:u.Tidy)(h:u.b.loom u.x0 (u.q,v,0)=Bow.purec (i+1))
    (he:u.p.fitting u.s v i) (hh:z∈u.s.domain): u.Cr (v,z) (i,z) :=
   u.p.meets0 u.s ht.reserve he (congrArg Prod.fst h) (congrArg (fun x=>x.2.2) h) hh

lemma downfit {l S a m alpha p p' o v w}(ht:u.Tidy)(hp:u.Rating a p)
    (hx:u.Course l a m)(hy:u.Stringent o) (hz:u.little a v)
    (hr:u.Rating alpha p')(hk:u.Course S alpha (m+u.grit a))
    (hm:u.little alpha w) (hh:u.grit alpha ≤2*u.grit a):
    Mill.fitting u.p u.s (cart o l v) (cart o S w) :=
   u.team ht (u.coal ht hp hx hz hy) (u.coal ht hr hk hm hy) (u.rag hp hx) (u.rag hr hk)
           (by omega) (by omega)

lemma pop5 {l f a m} (hp:u.Course (enc f::l) a m)
   (o p h g i:ℕ): u.b.loom u.x0 (u.q,cart o (enc f::l) (u.kidJ a p h g 5),i)=
        Bow.purec (future1 o l (Jet.turn f 4)) := by
   rw [u.resultv hp]
   suffices he :
       (if mesh (enc f::l)≤1 then Bow.purec (done o+1)
         else Bow.purec (going o
               (Jet.tug (aft (mesh (enc f::l))) (Jet.turn (Jet.cap (mesh (enc f::l))) 4)) +1))
            = Bow.purec (future1 o l (Jet.turn f 4)) by
      convert he using 1
      rfl
   change (if Jet.tug (mesh l) f≤1 then _ else _)=_
   have he1 : ¬Jet.tug (mesh l) f≤1:=not_le_of_gt (cord_fine ..).2.2
   rw [ite_eq_right he1]
   change Bow.purec (going o (Jet.tug (aft (Jet.tug (mesh l) f)) (Jet.turn (Jet.cap (Jet.tug (mesh l) f)) 4))+1)=_
   rw [Jet.aft_tug,Jet.cap_tug]; rfl

lemma popped_only {a} (hp:u.Course [] a 0) (o p h g):
    u.b.loom u.x0 (u.q,cart o [] (u.kidJ a p h g 5),0)=Bow.purec (done o+1):=by rw [u.resultv hp]; rfl

lemma reverse_fit (p:Mill)(s:Mill.Fuel){v w}(h:p.fitting s v w):p.fitting s w v:=
   ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

lemma flagdown {l a m p h e o c z y w}(ht:u.Tidy)(hp:u.Chess a p h e c z y w)
    (hx:u.Course l a m) (ho:u.Stringent o) (hy:u.dives a p h=false):
   u.Cr (cart o l (u.kidJ a p h e 2),z) (cart o l (u.kidJ a p h e 4),z):=
    u.blink0 ht ((u.ore2 hx o p h e 0).trans (ite_eq_right (by simp [hy])))
           (u.taking ht hp.hr hx ho (hp.kin.passed 2 (by omega)) (hp.kin.passed 4 (by omega))) hp.hz

lemma ladder {a m p l o h e c w} (ht:u.Tidy) (hp:u.Herd a p c h e w)
   (hx:u.Course l a m) (ho:u.Stringent o):
   u.Track (cart o l (u.fill a p),c) (cart o l (u.kidJ a p h e 5),w) := by
   induction hp generalizing l m with
   | solo hr h1=>
      exact ReflTransGen.tail (.tail (.tail (.single (u.helm ht hr hx ho)) (u.prowl ht hr hx ho))
             (u.flagdown ht hr hx ho h1)) (u.shiver ht hr hx ho)
   | @pair a p h e c z y w f g hr hv hd hy he ih=>
      let S:= nextJ u a p h e :: l
      obtain ⟨hf,hh⟩:=he.on
      have hy' : u.Course S (u.lower a p h) (m+u.grit a) :=
        u.goto ht hr.hr hx hf hd (hr.kin.passed 3 (by omega)) rfl rfl
      have ht1:= ih hy'
      have hu0:= u.ore2 hx o p h e 0
      have hs:= u.downfit ht hr.hr hx ho (hr.kin.passed 2 (by omega)) hf hy' hf.littleR hy
      have hs2:= u.downfit ht hr.hr hx ho (hr.kin.passed 4 (by omega)) hf hy' (hh.passed 5 (by omega)) hy
      have hp1: u.Cr (cart o l (u.kidJ a p h e 2),z) (cart o S (u.fill (u.lower a p h) (u.portD a p h)),z):=
         u.blink0 ht (hu0.trans (ite_eq_left hv)) hs hr.hz
      have hp5:u.b.loom u.x0 (u.q,cart o S (u.kidJ (u.lower a p h) (u.portD a p h) f g 5),0)=
                        Bow.purec (future1 o l (u.kidJ a p h e 4)):=
         u.pop5 hy' o (u.portD a p h) f g 0
      have hpf := u.blink0 ht hp5 (reverse_fit _ _ hs2) hr.hy
      exact .tail (.tail ((ReflTransGen.tail (.tail (.single (u.helm ht hr hx ho))
                       (u.prowl ht hr hx ho)) hp1).trans ht1) hpf) (u.shiver ht hr hx ho)

lemma dawn {p}(ht:u.Tidy)(he:u.Rating u.child p):
     u.Course [] u.child 0:=⟨by simpa using ht.openR,Nat.zero_le _,by change lb 1≤_; rw [lb_one]; omega,
                             .nil he.insured⟩

lemma cool {p c}(ht:u.Tidy)(he:u.Gown p c)(hk:u.Rating u.child p)(hx:c∈u.s.domain):
    u.Track (prime p,c) (cart (u.scent p c) [] (u.fill u.child p),c) := by
   let hz:=u.prepared ht he hx
   apply ReflTransGen.tail hz
   have hv:=u.pointing ht he (i:=u.H) le_rfl
   have hs:=u.coal ht hk (u.dawn ht hk) hk.littleR he.hair
   have heF:u.b.loom u.x0 (u.q,tell p u.H (u.chainR p c u.H),0)= Bow.purec (cart (u.scent p c) [] (u.fill u.child p)+1):=by
      rw [u.Ax]; simp [Aq,Bow.air,H]
      rfl
   have hg := ht.steady; have hu:=ht.run.wp
   change 1 ≤ u.B.w at hu
   apply u.blink0 ht heF (u.team ht hv hs (by omega) (by omega) (by omega) (by omega)) hx

lemma onion {p c h e w} (ht:u.Tidy)(he:u.Gown p c)
    (hc:c∈u.s.domain) (hw:w∈u.s.domain)
    (hk:u.Herd u.child p c h e w):
    u.Track (prime p,c) (done (u.scent p c),w):= by
   obtain ⟨ha,hb⟩:=hk.on
   have hs:=u.dawn ht ha
   have hh:=u.ladder ht hk hs he.hair
   apply ReflTransGen.tail ((u.cool ht he ha hc).trans hh)
   let v:=u.coal ht ha hs (hb.passed 5 (by omega)) he.hair
   have he:=u.capDone ht he.hair.1 he.hair.2
   have hp:=ht.steady; have hr:=ht.run.wp
   change 1 ≤ u.B.w at hr
   exact u.blink0 ht (u.popped_only hs ..)
             (u.team ht v he (by omega) (by omega) (by omega) (by omega)) hw
end Quill
end ExactDerandomization.Sub

end

section

namespace ExactDerandomization.Sub
open Relay Mint Swirl Counter Relation Finset

def helmet (_:Word)(x:Lore Panel) :Bool := decide ((dec x.2.2.1:Card).1=3)
lemma helmetK : Kn helmet := ((Kn.unpack (α:=Card)).comp Kn.next.right.left).left.eq (Kn.fix 3)
def snag (p: Mill): Rake := ⟨p.bud.showall,gear _ helmetK⟩

abbrev gem0 (v c:ℕ):Gem := ((v,c),0)
lemma priority (p q): prime p≠done q:=by
   intro h; have e:=congrArg (fun x=>(dec x:Card).1) h; simp [prime,done] at e

namespace Quill
noncomputable section
variable (u:Quill)
abbrev forge (h:u.Tidy) := h.run.tilt
def hall (h:u.Tidy) := Bud.arena (u.forge h)
lemma marked {h:u.Tidy} {p c} (he:p<u.b.ports.f u.x0 u.q):
   (snag u.p).p.check (u.hall h) (gem0 (prime p) c)=true ∧
    (snag u.p).root (u.hall h) (gem0 (prime p) c)=false := by
    constructor
    · change u.b.stripe0 u.x0 (u.q,prime p,0)=true
      simp [Bow.stripe0,priority,prime,he]
    rw [Rake.root,snag,gear_at]
    simp [helmet,prime]
lemma capped (h:u.Tidy) (o c:ℕ):
   (snag u.p).p.check (u.hall h) (gem0 (done o) c)=true ∧
   (snag u.p).root (u.hall h) (gem0 (done o) c)=true:=by
    constructor
    · change u.b.stripe0 u.x0 (u.q,done o,0)=true; simp [Bow.stripe0,done]
    rw [Rake.root,snag,gear_at]; simp [helmet,done]
lemma casing (h:u.Tidy){v: Gem}(he:(snag u.p).p.check (u.hall h) v=true):
    (∃ o c,v=gem0 (done o) c) ∨ ∃ p c,v=gem0 (prime p) c ∧ p<u.b.ports.f u.x0 u.q:=by
    rcases v with ⟨⟨v,c⟩,j⟩
    let o:=(dec v:Card).2.1
    change (if j=0 then if v=done o then true else if v=prime o then decide (o < u.b.ports.f u.x0 u.q)
          else false else false)=true at he
    split at he
    · next hw=>
       split at he
       · next hh=> exact Or.inl ⟨o,c,by unfold gem0; rw [hh,hw]⟩
       split at he
       · next hh=> exact Or.inr ⟨o,c,by unfold gem0; rw [hh,hw],of_decide_eq_true he⟩
       contradiction
    contradiction

abbrev upG (u:Quill)(h:u.Tidy):= (u.hall h).trees
lemma up_act (h:u.Tidy) {a b} : (u.upG h).up a=some b ↔ u.Cr a b :=
    (u.forge h).twig.atU
lemma blocked {h:u.Tidy} {a} (he:u.p.mate u.s a) : (u.upG h).up a=none := by
   cases hz:(u.upG h).up a with
   | none=> rfl
   | some b=> exact False.elim (he b ((u.up_act h).1 hz))

lemma domain_ok {h:u.Tidy} {x:Dot} (hh:x∈(u.upG h).V):x.2∈u.s.domain :=
   ((Bud.walled _).1 hh).2
lemma root_ok {h:u.Tidy}{o c} (ho:u.Stringent o)(hc:c∈u.s.domain):
   (done o,c)∈(u.upG h).V:= by
    apply (Bud.walled _).2
    exact ⟨u.p.mem_of u.s h.reserve (u.prepaid h (u.capDone h ho.1 ho.2) (by omega)),hc⟩

def Budded (h:u.Tidy) (r v:Dot): Prop:= ∃ n,(u.upG h).Flight r n v
lemma together (h:u.Tidy){r a b} (hr:(u.upG h).up r=none) (ha:u.Track a b):
   u.Budded h r a ↔ u.Budded h r b:= by
   induction ha with
   | refl=>rfl
   | @tail a b hx e ih=>
     rw [ih]
     have he:= (u.up_act h).2 e
     constructor
     · rintro ⟨n,hn⟩
       cases hn with
       | node=> grind
       | above h hz hh=> rw [he] at hz; obtain rfl := Option.some.inj hz; exact ⟨_,hh⟩
     rintro ⟨n,hb⟩
     exact ⟨_,.above ((u.forge h).twig.pairs e).1 he hb⟩
lemma unite {h:u.Tidy}{r v:Dot}(he:u.Budded h r v)(hp:(u.upG h).up v=none):v=r:=by
    obtain ⟨n,hn⟩:=he
    cases hn <;> grind

lemma to_entry {h:u.Tidy}{o c a p s} (ho:u.Stringent o)(hc:c∈u.s.domain)(ha:a∈u.s.domain)
    (he:u.Lane u.child p a s)(hr:u.Gown p a):
    u.Budded h (done o,c) (prime p,a) ↔ s=some c ∧ o=u.scent p a:= by
    have hu:(u.upG h).up (done o,c)=none:=u.blocked (u.shut)
    cases he with
    | dry hx hk hw=>
       rw [u.together h hu (u.cool h hr hx ha)]
       refine ⟨fun h0=>?_,by simp⟩
       have hv:=u.first0 h hx (u.dawn h hx) hr.hair hw
       have h1:=u.unite h0 (u.blocked hv)
       have h2:=congrArg Prod.fst h1
       exact False.elim (different h2)
    | born hw=>
       rename_i i j b
       have he:b∈u.s.domain:=by
          cases hw with
          | solo hr _=> exact hr.hw
          | pair hr _ _ _ _=> exact hr.hw
       rw [u.together h hu (u.onion h hr ha he hw)]
       constructor
       · intro hv
         have h1:=u.unite hv (u.blocked u.shut)
         have hg : done (u.scent p a)=done o:=congrArg Prod.fst h1
         have hg2:=congrArg (fun x=>(dec x:Card).2.1) hg
         simp only [done,decname] at hg2
         exact ⟨congrArg some (congrArg Prod.snd h1),hg2.symm⟩
       rintro ⟨e,h1⟩; obtain rfl:=Option.some.inj e; rw [← h1]
       exact ⟨0,.node (u.root_ok ho hc)⟩

def ent (f:ℕ→ℕ→Option ℕ)(o c:ℕ)(y:Gem) :=
    ∃ a∈u.s.domain,∃ i < u.b.ports.f u.x0 u.q,
             y=gem0 (prime i) a ∧ f a i=some c ∧ o=u.scent i a
structure Suite (f:ℕ→ℕ→Option ℕ) : Prop where
    row : ∀ a∈u.s.domain,∀ i < u.b.ports.f u.x0 u.q,
            u.Lane u.child i a (f a i) ∧ u.Gown i a

lemma arrival {h:u.Tidy} {o c f y} (hs:u.Suite f)(ho:u.Stringent o)(hc:c∈u.s.domain):
    u.ent f o c y ↔
     (u.upG h).nest (done o,c) y ∧
       (snag u.p).p.check (u.hall h) y=true ∧ y ≠ gem0 (done o) c:= by
    constructor
    · rintro ⟨a,ha,i,hi,rfl,e,hx⟩
      obtain ⟨hl,hw⟩:= hs.row a ha i hi
      obtain ⟨n,hk⟩:= (u.to_entry ho hc ha hl hw).2 ⟨e,hx⟩
      exact ⟨⟨⟨hk.on,Nat.zero_le _⟩,_,hk⟩,(u.marked hi).1,fun e=>priority i o
                                                           (congrArg (fun x=>x.1.1) e)⟩
    rintro ⟨hv,hx,hz⟩
    rcases u.casing h hx with ⟨v,w,rfl⟩ | ⟨p,a,rfl,hp⟩
    · exact False.elim (hz (congrArg (fun x:Dot=>(x,0)) (u.unite hv.2 (u.blocked u.shut))))
    have he:a∈u.s.domain:=u.domain_ok hv.1.1
    obtain ⟨hr,ht⟩:=hs.row a he p hp
    exact ⟨a,he,p,hp,rfl,(u.to_entry ho hc he hr ht).1 hv.2⟩

structure Wheel (h:u.Tidy)(f:ℕ→ℕ→Option ℕ)(o c:ℕ)(l:List Gem): Prop where
   front : Stripe (Flare ((u.upG h).march true) ((snag u.p).p.check (u.hall h)))
                       (gem0 (done o) c) l (gem0 (done o) c)
   aft : Stripe (Flare ((u.upG h).march false) ((snag u.p).p.check (u.hall h)))
                       (gem0 (done o) c) l.reverse (gem0 (done o) c)
   unique : l.Nodup
   members : ∀ y,y∈l↔u.ent f o c y

lemma beat (h:u.Tidy){f o c}(hp:u.Suite f)(ho:u.Stringent o)(hc:c∈u.s.domain) :
   ∃ l,u.Wheel h f o c l:= by
    obtain ⟨l,hl,hz,h1,h2⟩:= (u.upG h).streak (u.root_ok ho hc) (u.blocked u.shut)
                                           ((snag u.p).p.check (u.hall h)) (u.capped h o c).1
    refine ⟨l,h1,h2,(List.nodup_cons.1 hl).2,fun y=>?_⟩
    rw [u.arrival (h:=h) hp ho hc]
    have hg:= (List.nodup_cons.1 hl).1
    have hh:=hz y
    unfold gem0
    rw [List.mem_cons] at hh
    grind

lemma drum {h:u.Tidy}{f o c l}(hv:u.Wheel h f o c l):
    (snag u.p).Circuit (u.hall h) (gem0 (done o) c) l:= by
    have hg : (snag u.p).p.Covers (u.hall h):=(u.forge h).yields
    refine ⟨(hv.front.twain hv.aft).every (fun a b ⟨e,g⟩=>⟨hg.flash _ e,hg.flash _ g⟩),
                        (u.capped h o c).2,?_⟩
    intro v hx
    obtain ⟨a,_,p,ht,rfl,_,_⟩:= (hv.members v).1 hx
    exact (u.marked ht).2

/-- The contour order is an invariant of the effective graph. -/
def gloved (w:ℕ→ℕ) : Quill:={u with s:={u.s with hand:=w}}

lemma past {h:u.Tidy} {f o c l} (hs:u.Wheel h f o c l)
    {w} (h1:(u.gloved w).Tidy):
    (u.gloved w).Wheel h1 f o c l:=by
    rcases hs with ⟨ha,hb,hc,hd⟩

    exact ⟨ha,hb,hc,hd⟩

end
end Quill
end ExactDerandomization.Sub

end

end OAI
