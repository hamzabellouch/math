import OAI.Computability.Logspace.RecursivePrograms

namespace OAI

/-!
Contour traversal of finite functional graphs with explicit predecessor enumeration.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-!
Contour on a functional graph with raw-name-labelled cursor nodes.
Include slots for absent incidences. This enables scanning arbitrary raw
program records of comparable size for predecessors; incidence
alphabets at this graph layer need not be bounded by constants. -/
namespace ExactDerandomization.Swirl
open Relay Finset

abbrev Dot := ℕ×ℕ
abbrev Gem := Dot×ℕ

structure Fir where
   V : Finset Dot
   rad : ℕ → ℕ
   up : Dot → Option Dot
   kid : Dot → ℕ → Option Dot
   pairU : ∀ x∈V,∀ {y},up x=some y  →
       y∈V ∧ y.1 < rad x.1 ∧ x.1 < rad y.1 ∧ kid y x.1=some x
   pairK : ∀ y∈V,∀ i {x},kid y i=some x  →  x∈V ∧ up x=some y ∧ x.1=i

namespace Fir
variable (g:Fir)

def broad (x:Dot):=g.rad x.1
def finalx (x:Dot):Gem := (x,g.broad x)
def roll (x:Gem): Gem :=
   let p:=x.1; let i:=x.2
   if i < g.broad p then
      match g.kid p i with
      | none=>(p,i+1)
      | some y=>(y,0)
   else
      match g.up p with
      | none=>(p,0)
      | some y=>(y,p.1+1)
def fold (x:Gem): Gem :=
   let p:=x.1; let i:=x.2
   if i=0 then
       match g.up p with
       | none=> (p,g.broad p)
       | some y=> (y,p.1)
   else
       match g.kid p (i-1) with
       | none=>(p,i-1)
       | some y=>(y,g.broad y)

def live (x:Gem):= x.1∈g.V ∧ x.2 ≤ g.broad x.1

lemma forward {x} (h:g.live x) : g.live (g.roll x) ∧ g.fold (g.roll x)=x := by
   rcases x with ⟨p,i⟩; obtain ⟨hz,ht⟩:=h
   change i≤g.broad p at ht
   change p∈g.V at hz
   by_cases hi:i<g.broad p
   · cases he:g.kid p i with
     | none=> simp [live,roll,fold,hi,he,hz]
     | some y=>
       obtain ⟨ha,hb,hc⟩:=g.pairK p hz i he
       simp [live,roll,fold,hi,he,hb,hc,ha]
   cases he:g.up p with
   | none=> simp [live,roll,fold,hz,hi,he]; omega
   | some y=>
      obtain ⟨ha,hb,hc,hd⟩:=g.pairU p hz he
      change p.1<g.broad y at hc
      simp [live,roll,fold,hi,he,ha,hd]; omega

inductive Flight (S:Dot) : ℕ → Dot → Prop
  | node (h:S∈g.V): Flight S 0 S
  | above {n y x} (h:x∈g.V) (e:g.up x=some y) (p:Flight S n y):
                  Flight S (n+1) x

lemma Flight.on {g:Fir} {S n x} (h:g.Flight S n x):x∈g.V:=by cases h <;> assumption
lemma Flight.unique {g:Fir} {S n m x} (h:g.Flight S n x) (e:g.Flight S m x) (ha:g.up S=none) : m=n := by
   induction h generalizing m with
   | node hx =>
     cases e <;> simp_all
   | above hx hh hk ih=> cases e <;> simp_all

lemma quota {S} (hs:g.up S=none) : ∃ d, ∀ {x n},g.Flight S n x → n≤d := by
  classical
  have he (p : Finset Dot) : ∃ d, ∀ {x n},x∈p → g.Flight S n x → n≤d := by
     induction p using Finset.induction_on with
     | empty=> exact ⟨0, by simp⟩
     | @insert a p ha ih=>
       obtain ⟨d,h⟩:=ih
       by_cases hh:∃ n,g.Flight S n a
       · obtain ⟨n,hk⟩:=hh
         refine ⟨n+d,fun {x i} hu hm=>?_⟩
         obtain rfl|hz:=mem_insert.1 hu
         · rw [Flight.unique hk hm hs]; omega
         have he:= h hz hm; omega
       refine ⟨d,fun {x i} hu hm=>h ?_ hm⟩
       obtain rfl|hz:=mem_insert.1 hu
       · exact (hh ⟨i,hm⟩).elim
       exact hz
  obtain ⟨d,hk⟩:=he g.V; exact ⟨d,fun {_ _} h=>hk h.on h⟩

def nest (S:Dot) (p:Gem) := g.live p ∧ ∃ n,g.Flight S n p.1
lemma rise {S p} (hS:g.up S=none) (h:g.nest S p):g.nest S (g.roll p):= by
   have he:=g.forward h.1; refine ⟨he.1,?_⟩
   rcases p with ⟨v,i⟩
   obtain ⟨hz,n,h⟩:=h
   change g.Flight S n v at h
   by_cases hk:i<g.broad v
   · cases hu:g.kid v i with
     | none=> simp [roll,hk,hu]; exact ⟨n,h⟩
     | some x=>
       obtain ⟨ha,hb,-⟩:=g.pairK v hz.1 i hu
       simp [roll,hk,hu]; exact ⟨_,.above ha hb h⟩
   cases e:g.up v with
   | none=> simp [roll,hk,e]; exact ⟨n,h⟩
   | some w=>
      simp [roll,hk,e]
      cases h with
      | node=> simp_all
      | @above i v hx hv hw=> simp_all; aesop

end Fir

def lap {α} (f:α → α) (v:α) : ℕ → α
   | 0=> v
   | n+1=> f (lap f v n)

section
variable {α:Type} (f:α → α)
lemma laps (v i j): lap f v (i+j)=lap f (lap f v i) j := by
   induction j with | zero=> simp [lap] | succ j ih=> rw [← add_assoc,lap,ih,lap]

def Link (x y : α):= ∃ i, lap f x i=y
lemma Link.seq {f x y z} (h:Link (α:=α) f x y) (e:Link f y z):Link f x z:=by
   obtain ⟨i,rfl⟩:=h; obtain ⟨j,rfl⟩:=e; exact ⟨_,laps ..⟩
lemma same (x:α) : Link f x x:=⟨0,rfl⟩
lemma ride {x y} (h:f x=y): Link f x y:=⟨1,h⟩
end

namespace Fir
variable (g:Fir)

lemma between {S} (hs:g.up S=none) :
    ∀ {n x},g.Flight S n x  →  ∀ i, i≤g.broad x  →
                   Link g.roll (x,0) (x,i) := by
   obtain ⟨d,h⟩:=g.quota hs
   suffices ht:∀ j {n x}, d ≤ n+j → g.Flight S n x  →
       ∀ i,i≤g.broad x → Link g.roll (x,0) (x,i) by
     exact fun {_ _} e => ht d (by omega) e
   intro j
   induction j with
   | zero=>
      intro n x hh he i ha
      induction i with
      | zero=> exact same ..
      | succ i ih=>
        apply Link.seq (ih (by omega))
        have hi:i<g.broad x:=by omega
        cases hz:g.kid x i with
        | none=> apply ride; simp [roll,hz,hi]
        | some y=>
          obtain ⟨h1,h2,h3⟩:=g.pairK x he.on i hz
          have hk:=h (Flight.above h1 h2 he); omega
   | succ j ih=>
      intro n x hh he i ha
      induction i with
      | zero=> exact same ..
      | succ i hi=>
         apply Link.seq (hi (by omega))
         have hi:i<g.broad x:=by omega
         cases hz:g.kid x i with
         | none=> apply ride; simp [roll,hz,hi]
         | some y=>
           obtain ⟨h1,h2,h3⟩:=g.pairK x he.on i hz
           have hy:= ih (show d ≤ n+1+j by omega) (Flight.above h1 h2 he) (g.broad y) le_rfl
           exact .seq (ride _ (by simp [roll,hz,hi])) (.seq hy (ride _ (by simp [roll,h2,h3])))

lemma orbit {S p} (hs:g.up S=none) (h:g.nest S p) :
    Link g.roll (S,0) p := by
   rcases p with ⟨x,i⟩; obtain ⟨hx,n,h⟩:=h
   change g.Flight S n x at h
   apply Link.seq _ (g.between hs h _ hx.2)
   clear hx
   induction h with
   | node=> exact same ..
   | @above n y x hx he hy ih=>
     obtain ⟨ha,hb,hc,hd⟩:=g.pairU x hx he
     exact .seq ih (.seq (g.between hs hy _ hc.le) (ride _ (by
           simp [roll,hc,broad,hd])))
lemma whirl {S} (hs:S∈g.V) (hh:g.up S=none) :
    ∃ n, lap g.roll (S,0) (n+1)=(S,0) := by
   obtain ⟨i,hi⟩:=g.between hh (Flight.node hs) (g.broad S) le_rfl
   exact ⟨i,by rw [lap,hi]; simp [roll,hh]⟩

end Fir
end ExactDerandomization.Swirl

end

section

namespace ExactDerandomization.Swirl
open Relay

variable {α:Type}

/-- Linear link with internal points explicit; endpoints can coincide. -/
inductive Stripe (r:α→α→Prop) : α→List α→α→Prop
  | run {x y} (h:r x y) : Stripe r x [] y
  | hook {x y z l} : r x y → Stripe r y l z → Stripe r x (y::l) z

namespace Stripe
variable {r w : α→α→Prop}

lemma joins {x y z l m} (h:Stripe r x l y) (e:Stripe r y m z):Stripe r x (l++y::m) z:=by
   induction h with
   | run hp=>exact .hook hp e
   | hook hz _ ih=> exact .hook hz (ih (by assumption))

lemma both {x u l} (h:Stripe r x u l)
    (hr:∀ a b,r a b → w b a) : Stripe w l u.reverse x := by
   induction h with
   | run h=> exact .run (hr _ _ h)
   | hook h e ih=>
     rw [List.reverse_cons]
     exact joins ih (.run (hr _ _ h))

lemma every {x l y} (h:Stripe r x l y) (hz:∀ x y,r x y → w x y):
    Stripe w x l y := by induction h with
    | run h=> exact .run (hz _ _ h)
    | hook h _ ih=> exact .hook (hz _ _ h) ih

lemma sever {x y z a b} (h:Stripe r x (a++z::b) y):
    Stripe r x a z ∧ Stripe r z b y := by
   induction a generalizing x with
   | nil=> cases h with | hook u v=> exact ⟨.run u,v⟩
   | cons j a ih=>
     cases h with
     | hook u v=>
       obtain ⟨hv,hw⟩:=ih v; exact ⟨.hook u hv,hw⟩

end Stripe

inductive Flare (r:α→α→Prop) (f:α→Bool) : α→α→Prop
   | arrive {x y} : r x y → f y=true → Flare r f x y
   | climb {x y z} : r x y → f y=false → Flare r f y z → Flare r f x z

lemma stripes {r:α→α→Prop} {x y l} (h:Stripe r x l y) (v:α→Bool) (e:v y=true):
    Stripe (Flare r v) x (l.filter v) y:= by
   induction h with
   | run hz=> exact .run (.arrive hz e)
   | @hook x a y l h t ih=>
     specialize ih e
     by_cases ht:v a=true
     · simp [ht]; exact .hook (.arrive h ht) ih
     replace ht:v a=false:=by simp_all
     rw [List.filter_cons_of_neg]; swap; simp [ht]
     generalize he:l.filter v=m at *
     cases ih with
     | run ha=> exact .run (.climb h ht ha)
     | hook ha hb=> exact .hook (.climb h ht ha) hb

namespace Rope
variable (f:α→α)
def rope (x:α) : ℕ→ List α
   | 0=>[]
   | n+1=> f x :: rope (f x) n

lemma before (x i) : lap f x (i+1) = lap f (f x) i:= by
   rw [show i+1=1+i by omega,laps]; rfl

lemma paid (S : α→Prop) (h:∀ i,S i→ S (f i))
   (x:α) (e:S x) (n) :
   Stripe (fun i j=> S i ∧ f i=j) x (rope f x n) (lap f x (n+1)):= by
   induction n generalizing x with
   | zero=> exact .run ⟨e,rfl⟩
   | succ n ih=>
      rw [rope,before]
      exact .hook ⟨e,rfl⟩ (ih _ (h _ e))

lemma sat {x y:α} {n} : y∈rope f x n ↔ ∃ i<n,lap f x (i+1)=y:= by
   induction n generalizing x with
   | zero=> simp [rope]
   | succ n ih=>
     simp only [rope,List.mem_cons,ih]
     constructor
     · rintro (rfl|⟨i,hi,e⟩)
       · exact ⟨0,by omega,rfl⟩
       exact ⟨i+1,by omega,(before f x (i+1)).trans e⟩
     rintro ⟨i,h,e⟩; cases i with
     | zero=>left; exact e.symm
     | succ i=> exact Or.inr ⟨i,by omega,(before f x (i+1)).symm.trans e⟩

lemma repeatZ {x:α} {n} (h:lap f x (n+1)=x) (i:ℕ) :
    ∃ j, j≤n∧ lap f x j=lap f x i:= by
   induction i using Nat.strong_induction_on with | h i ih =>
    by_cases he:i≤n
    · exact ⟨i,he,rfl⟩
    have hu : n+1+(i-(n+1))=i := by omega
    obtain ⟨j,hj,hk⟩:= ih (i-(n+1)) (by omega)
    refine ⟨j,hj,hk.trans ?_⟩
    exact (calc
        lap f x i= _ := congrArg _ hu.symm
        _= lap f (lap f x (n+1)) (i-(n+1)):=laps ..
        _= _:=by rw [h]).symm

lemma clean {x:α} {n} (h: ∀ j, j≤n → ∀ i<j, lap f x i≠lap f x j) :
    (x::rope f x n).Nodup:=by
   induction n generalizing x with
   | zero=> simp [rope]
   | succ n ih=>
     refine List.nodup_cons.2 ⟨?_,?_⟩
     · intro hz; obtain ⟨i,hi,e⟩:= (sat _).1 hz
       exact h _ hi 0 (by omega) e.symm
     rw [rope]; apply ih
     intro j hj i hi
     rw [← before,← before]
     exact h (j+1) (by omega) (i+1) (by omega)

lemma cutpoint {S:α→Prop} {x} (hh:S x) (hz:∀ a,S a → S (f a))
   (hr : ∀ a,S a → Link f x a) (he:∃ n,lap f x (n+1)=x) :
   ∃ l, (x::l).Nodup ∧ (∀ a,a∈x::l ↔ S a) ∧ Stripe (fun i j=> S i ∧ f i=j) x l x:= by
  classical
  let n:=Nat.find he
  have hp:lap f x (n+1)=x:= Nat.find_spec he
  refine ⟨rope f x n,clean _ ?_,fun a=>?_,by
    have hh:=paid f S hz x hh n; rw [hp] at hh; exact hh⟩
  · intro j hj i hi h
    have e1 : lap f x (i+(n+1-j))=x := by
       rw [laps,h,← laps,show j+(n+1-j)=n+1 by omega,hp]
    have ht := Nat.find_min' he (show lap f x (i+(n-j)+1)=x by
                      rw [show i+(n-j)+1=i+(n+1-j) by omega,e1])
    change n≤_ at ht
    omega
  · rw [List.mem_cons,sat]
    have ht(i): S (lap f x i):=by induction i with | zero=>exact hh | succ i ih=> exact hz _ ih
    constructor
    · rintro (rfl|⟨i,hj,rfl⟩)
      · exact hh
      exact ht _
    intro hy
    obtain ⟨i,rfl⟩:=hr a hy
    obtain ⟨j,hj,he⟩:=repeatZ f hp i
    cases j with
    | zero=> left; exact he.symm
    | succ j=> exact Or.inr ⟨_,hj,he⟩

end Rope

namespace Fir
variable (g:Fir)
def march (b:Bool) (i j:Gem) := g.live i ∧ (if b then g.roll i else g.fold i)=j ∧ g.live j
lemma streak {S} (hs:S∈g.V) (hh:g.up S=none) (m:Gem→Bool) (hm:m (S,0)=true) :
    ∃ l: List Gem, ((S,0)::l).Nodup ∧
       (∀ a,a∈(S,0)::l ↔ g.nest S a ∧ m a=true) ∧
       Stripe (Flare (march g true) m) (S,0) l (S,0) ∧
       Stripe (Flare (march g false) m) (S,0) l.reverse (S,0):= by
   have hr : g.nest S (S,0):=⟨⟨hs,Nat.zero_le _⟩,⟨0, Flight.node hs⟩⟩
   let v : Gem := (S,0)
   let p i j:=g.nest S i ∧ g.roll i=j
   obtain ⟨l,hl,he,h⟩:= Rope.cutpoint g.roll hr (fun a e=>g.rise hh e)
                     (fun a e=>g.orbit hh e) (g.whirl hs hh)
   have h1 : ∀ a b,p a b → march g true a b := by
      rintro a b ⟨e,rfl⟩; exact ⟨e.1,rfl,(g.forward e.1).1⟩
   have h2 : ∀ a b,march g true a b → march g false b a := by
      rintro a b ⟨e,rfl,h⟩; exact ⟨h,(g.forward e).2,e⟩
   have hh : Stripe (march g false) v l.reverse v :=
         h.both (fun a b q=>h2 a b (h1 a b q))
   have hg : Stripe (march g true) v l v:= h.every h1
   refine ⟨l.filter m,?_,fun i=>?_,stripes hg m hm,?_⟩
   · simpa [hm] using hl.filter m
   · have hz:= he i
     simp only [List.mem_cons,List.mem_filter]
     grind
   simpa using stripes hh m hm

end Fir
end ExactDerandomization.Swirl

end

section

namespace ExactDerandomization.Swirl
open Relay

def Fir.riseQ (g:Fir) (v:Dot) (i:ℕ):Option Dot :=
   match g.up v with
   | some y=> if y.1=i then some y else none
   | none=>none
def Fir.probe (g:Fir) (parent:Bool) (v:Dot) (i:ℕ) :=
   if parent then g.riseQ v i else g.kid v i

abbrev Seat := ℕ×ℕ
abbrev Panel := Bool×Seat

structure Arena where
    l : Lot
    b : Level
    d : ℕ
    q : ℕ
    cost : ℕ
    trees : Fir
    hand : ℕ→ℕ

namespace Arena
variable (s:Arena)
abbrev acts := Lot.Mane s.l s.cost s.b s.d s.q
abbrev wait {α} [Wire α] (v:α) (c:ℕ):Site := Pause v (s.hand c)
abbrev tag (p:Gem) (f:Bool :=false) : Site := s.wait ((f,p.1.1,p.2):Panel) p.1.2

def touch (b:Bool) (v:Dot) (i:ℕ):Site :=
    match s.trees.probe b v i with
    | none=> s.tag (v,i) false
    | some w=> s.wait ((true,v.1,i):Panel) w.2

end Arena

structure Shows where
    rad : Cub (Lore ℕ) ℕ
    marked : Cub (Lore Seat) Bool
    probes : Bool→ Cog
namespace Shows
variable (p:Shows)

abbrev Chart := Lore Panel

def ray (x:Word) (a:Chart) := p.rad.f x (a.1,a.2.2.1)
lemma rayK : Kn p.ray:=p.rad.runs.comp (Kn.first.tuple Kn.next.right.left)

def keep (x:Word) (a:Chart) : Bool :=
   if a.2.1 then false else decide (a.2.2.2< p.ray x a)
lemma keepK : Kn p.keep:= Kn.next.left.cond (Kn.fix _) (Kn.next.right.right.lt p.rayK)

def upmov (dir:Bool) (_:Word) (a:Chart) : Panel :=
    let (b,v,i):=a.2
    if b then (true,i,if dir then v+1 else v)
    else (false,v,i+1)
lemma upK (b): Kn (upmov b):=by
    have ht : Kn (fun (_:Word) (a:Chart)=>a.2):=Kn.next
    let v:=upmov b
    change Kn v
    cases b
    · exact ht.left.cond ((Kn.fix _).tuple (ht.right.right.tuple ht.right.left))
                  ((Kn.fix _).tuple (ht.right.left.tuple ht.right.right.succ))
    · exact ht.left.cond ((Kn.fix _).tuple (ht.right.right.tuple ht.right.left.succ))
                  ((Kn.fix _).tuple (ht.right.left.tuple ht.right.right.succ))

def summit (p:Shows) (dir:Bool) (x:Word) (a:Chart) : Panel :=
    let (b,v,i):=a.2
    (false,v, if b then i else if dir then 0 else p.rad.f x (a.1,v))
lemma summitK (b):Kn (p.summit b):=by
    have ht : Kn (fun (_:Word) (a:Chart)=>a.2):=Kn.next
    cases b
    · exact (Kn.fix _).tuple (ht.right.left.tuple (ht.left.cond ht.right.right p.rayK))
    · exact (Kn.fix _).tuple (ht.right.left.tuple (ht.left.cond ht.right.right (Kn.fix _)))

def topseat (_:Word) (a:Chart) : Panel := (false,a.2.2.1,0)
lemma topK : Kn topseat := (Kn.fix _).tuple (Kn.next.right.left.tuple (Kn.fix _))

def tryU (dir:Bool) : Cog := .seq (p.probes true) (etch (upmov dir) (upK dir))
def chase (dir:Bool) : Cog := .loop (gear p.keep p.keepK) (p.tryU dir)
def rise (dir:Bool) : Cog := .seq (etch _ topK) (.seq (p.chase dir) (etch _ (p.summitK dir)))

def downgrade (_:Word) (a:Chart):Panel := (false,a.2.2.1,a.2.2.2-1)
lemma downgrades : Kn downgrade := (Kn.fix _).tuple
         (Kn.next.right.left.tuple Kn.next.right.right.pred)
def dock (p:Shows) (dir:Bool) (x:Word) (a:Chart) : Panel :=
   let (b,v,i):=a.2
   if b then (false,i,if dir then 0 else p.rad.f x (a.1,i))
   else (false,v, if dir then i+1 else i)
lemma dockK (d): Kn (p.dock d) := by
    have ht : Kn (fun (_:Word) (a:Chart)=> a.2):=Kn.next
    cases d
    · exact ht.left.cond ((Kn.fix _).tuple (ht.right.right.tuple
                         (p.rad.runs.comp (Kn.first.tuple ht.right.right))))
                    ((Kn.fix _).tuple ht.right)
    · exact ht.left.cond ((Kn.fix _).tuple (ht.right.right.tuple (Kn.fix _)))
                   ((Kn.fix _).tuple (ht.right.left.tuple ht.right.right.succ))

def highp (_:Word) (a:Chart) : Bool := decide (0<a.2.2.2)
lemma highK : Kn highp := (Kn.fix _).lt Kn.next.right.right
def seeD (dir:Bool) : Cog :=
   .seq (p.probes false) (etch _ (p.dockK dir))
def step : Bool→ Cog
   | true=> .bif (gear _ p.keepK) (p.seeD true) (p.rise true)
   | false=> .bif (gear _ highK) (.seq (etch _ downgrades) (p.seeD false)) (p.rise false)

def repeatQ (x:Word) (a:Chart) := !(p.marked.f x (a.1,a.2.2))
lemma repeatK : Kn p.repeatQ := Kn.bneg _ (p.marked.runs.comp (Kn.first.tuple Kn.next.right))
def spool (b:Bool) : Cog := .loop (gear _ p.repeatK) (p.step b)
def away (b:Bool) : Cog := .seq (p.step b) (p.spool b)
def check (s:Arena) (v:Gem):Bool:= p.marked.f s.l.x (s.q,v.1.1,v.2)

structure Covers (s:Arena) : Prop where
    rate : ∀ v∈s.trees.V,p.rad.f s.l.x (s.q,v.1)=s.trees.broad v
    adm : ∀ v,s.trees.live v → ∀ b,s.l.state s.cost s.b (s.tag v b)
    know : ∀ b v, v∈s.trees.V → ∀ i, i < s.trees.broad v →
           s.acts (p.probes b) (s.tag (v,i) false) (s.touch b v i)

end Shows
end ExactDerandomization.Swirl

end

section

namespace ExactDerandomization.Swirl
open Relay
namespace Shows
variable {p:Shows} {s:Arena} (u:p.Covers s)

def promote (_:Fir) (b:Bool) (v:Dot)(w:Dot) :Gem := (w,if b then v.1+1 else v.1)

def counted (s:Arena) (b:Bool) (v:Dot):Site :=
   match s.trees.up v with
   | none => s.tag (v,s.trees.broad v) false
   | some w=> s.tag (promote s.trees b v w) true

def rer (s:Arena) (b:Bool) (v:Dot):Gem :=
   match s.trees.up v with
   | none=> (v, if b then 0 else s.trees.broad v)
   | some w=>promote s.trees b v w

namespace Covers
include u

lemma stayst {v:Dot} {i} (h:v∈s.trees.V) (hi:i ≤ s.trees.broad v) (b:Bool) :
    s.l.state s.cost s.b (s.tag (v,i) b):=u.adm _ ⟨h,hi⟩ b

lemma truekeep {x} (hi : x.2 < s.trees.broad x.1) (h:x.1∈s.trees.V) :
    (gear p.keep p.keepK).f s.l.x (s.q,s.tag x false)=true := by
    rw [gear_at]; simp [keep,ray,u.rate x.1 h,hi]
lemma falsekeep {x : Gem} (hi : x.2=s.trees.broad x.1) (h:x.1∈s.trees.V) :
    (gear p.keep p.keepK).f s.l.x (s.q,s.tag x false)=false := by
    rw [gear_at]; simp [keep,ray,u.rate x.1 h,hi]
omit u in
lemma stopkeep (x:Gem) :
    (gear p.keep p.keepK).f s.l.x (s.q,s.tag x true)=false := by
    rw [gear_at]; simp [keep]
lemma powered {b v w} (hv:v∈s.trees.V) (h:s.trees.up v=some w) (e) :
   s.l.state s.cost s.b (s.tag (promote s.trees b v w) e):= by
    obtain ⟨ha,hb,hc,hd⟩:=s.trees.pairU v hv h
    apply u.stayst ha
    change v.1 < s.trees.broad w at hc
    split <;> omega

set_option maxHeartbeats 2000000 in
lemma sought {v i} (h:v∈s.trees.V) (hi:i ≤ s.trees.broad v)
    (he:∀ w,s.trees.up v=some w → i ≤ w.1) (b:Bool) :
    s.acts (p.chase b) (s.tag (v,i) false) (counted s b v):= by
   induction hi using Nat.decreasingInduction with
   | self=>
     have hp : s.trees.up v=none:=by
        cases hw:s.trees.up v with
        | none=>rfl
        | some w=>
          exfalso
          exact not_lt.mpr (he _ hw) (s.trees.pairU _ h hw).2.1
     rw [counted,hp]; exact .stop (u.falsekeep rfl h) (u.stayst h le_rfl _)
   | of_succ i hi ih=>
     by_cases hv : ∃ w,s.trees.up v=some w ∧ w.1=i
     · obtain ⟨w,hw,rfl⟩:=hv
       rw [counted,hw]
       have hz:= u.know true v h w.1 hi
       have hk : s.touch true v w.1 = s.wait ((true,v.1,w.1):Panel) w.2 := by
          simp [Arena.touch,Fir.probe,Fir.riseQ,hw]
       rw [hk] at hz
       have hn:=u.powered (b:=b) h hw true
       have hy: s.acts (etch _ (upK b))
             (s.wait ((true,v.1,w.1):Panel) w.2)
             (s.tag (promote s.trees b v w) true) :=
          etches _ (upK b) (l:=s.l) (c:=s.cost) (b:=s.b) (d:=s.d) (q:=s.q)
             (i:=((true,v.1,w.1):Panel)) (w:=s.hand w.2) rfl hz.spots.2 hn
       have hp: s.acts (p.chase b) (s.tag (promote s.trees b v w) true)
                           (s.tag (promote s.trees b v w) true):=.stop
                            ((stopkeep (p := p) (s := s)) (promote s.trees b v w)) hn
       exact .more (u.truekeep hi h) (.seq hz hy) hp
     have hg:= u.know true v h i hi
     have hw:s.touch true v i=s.tag (v,i) false:= by
        cases e:s.trees.up v with
        | none=> simp [Arena.touch,Fir.probe,Fir.riseQ,e]
        | some w=>
          have hz : w.1≠i:=fun hf=>hv ⟨_,e,hf⟩
          simp [Arena.touch,Fir.probe,Fir.riseQ,e,hz]
     rw [hw] at hg
     have hk : ∀ w,s.trees.up v=some w → i+1 ≤ w.1:=by
        intro w hw
        have hs:= he _ hw
        have hz : w.1≠i:=fun hf=>hv ⟨_,hw,hf⟩
        omega
     have hz:= ih hk
     refine .more (u.truekeep hi h) (.seq hg ?_) hz
     exact etches _ (upK b) rfl hg.spots.2 hz.spots.1

lemma wished {v i} (h:v∈s.trees.V) (hi:i ≤ s.trees.broad v) (b:Bool):
    s.acts (p.rise b) (s.tag (v,i) false) (s.tag (rer s b v) false):= by
   have he0:= u.sought h (Nat.zero_le _) (i:=0) (fun _ _=>Nat.zero_le _) b
   apply Lot.Mane.seq (etches _ topK rfl (u.stayst h hi false) he0.spots.1)
   refine .seq he0 ?_
   have hu:=he0.spots.2
   cases he:s.trees.up v with
   | none=>
     simp only [counted,he] at hu ⊢
     simp only [rer,he]
     exact etches _ (p.summitK b) (by simp [summit,u.rate v h]) hu (u.stayst h (i:=if b then 0 else s.trees.broad v) (by split <;> omega) false)
   | some w=>
     simp only [counted,he] at hu ⊢
     simp only [rer,he]
     exact etches _ (p.summitK b) rfl hu (u.powered h he false)

def chosen (s:Arena) (b:Bool) (v:Dot) (i:ℕ): Gem:=
   match s.trees.kid v i with
   | none=>(v,if b then i+1 else i)
   | some w=>(w, if b then 0 else s.trees.broad w)
lemma child {v i} (h:v∈s.trees.V) (hi:i < s.trees.broad v) (b:Bool):
    s.acts (p.seeD b) (s.tag (v,i) false) (s.tag (chosen s b v i) false):= by
   have hz:= u.know false v h i hi
   cases he:s.trees.kid v i with
   | none=>
     have hs:s.touch false v i=s.tag (v,i) false:=by simp [Arena.touch,Fir.probe,he]
     rw [hs] at hz
     refine .seq hz ?_
     rw [chosen,he]
     exact etches _ (p.dockK b) rfl hz.spots.2 (u.stayst h (by split <;> omega) _)
   | some w=>
     have hs:s.touch false v i=s.wait ((true,v.1,i):Panel) w.2:=by simp [Arena.touch,Fir.probe,he]
     rw [hs] at hz
     obtain ⟨ha,hb,hc⟩:=s.trees.pairK v h i he
     refine .seq hz ?_
     rw [chosen,he]
     exact etches _ (p.dockK b) (by simp only [dock,← hc,u.rate w ha,ite_true]) hz.spots.2
                            (u.stayst ha (by split <;> omega) _)

lemma forwardx {v} (h:s.trees.live v) :
   s.acts (p.step true) (s.tag v false) (s.tag (s.trees.roll v) false) := by
   rcases v with ⟨v,i⟩
   by_cases hi:i < s.trees.broad v
   · refine .yes (u.truekeep hi h.1) ?_
     rw [show s.trees.roll (v,i)=chosen s true v i from by
       cases hw:s.trees.kid v i <;> simp [Fir.roll,chosen,hi,hw]]
     exact u.child h.1 hi true
   have he : i=s.trees.broad v:=le_antisymm h.2 (by omega)
   refine .no (u.falsekeep he h.1) ?_
   rw [show s.trees.roll (v,i)=rer s true v from by
        cases hw:s.trees.up v <;> simp [Fir.roll,hi,rer,promote,hw]]
   exact u.wished h.1 h.2 true
lemma previousx {v} (h:s.trees.live v) :
   s.acts (p.step false) (s.tag v false) (s.tag (s.trees.fold v) false) := by
   rcases v with ⟨v,i⟩; cases i with
   | zero=>
     refine .no (by rw [gear_at]; simp [highp]) ?_
     rw [show s.trees.fold (v,0)=rer s false v from by
       cases hw:s.trees.up v <;> simp [Fir.fold,rer,promote,hw]]
     exact u.wished h.1 h.2 false
   | succ i=>
     have hs := u.child (i:=i) h.1 h.2 false
     refine .yes (by rw [gear_at]; simp [highp])
       (.seq (etches _ downgrades rfl (u.stayst h.1 h.2 false) hs.spots.1) ?_)
     rw [show s.trees.fold (v,i+1)=chosen s false v i from by
        cases hw:s.trees.kid v i <;> simp [Fir.fold,chosen,hw]]
     exact hs

lemma turnx (b:Bool) {x y} (h:s.trees.march b x y):
   s.acts (p.step b) (s.tag x false) (s.tag y false):=by
   obtain ⟨h,rfl,-⟩:=h; cases b
   · exact u.previousx h
   exact u.forwardx h

omit u in
lemma restNeon (x:Gem) : (gear p.repeatQ p.repeatK).f s.l.x (s.q,s.tag x false) =
                          !(p.check s x):=gear_at _ _ _ _ _ _
lemma flash (b:Bool) {x y} (h:Flare (s.trees.march b) (p.check s) x y):
    s.acts (p.away b) (s.tag x false) (s.tag y false):= by
   induction h with
   | @arrive x y h e=>
     have hy:=u.turnx b h
     exact .seq hy (.stop (by rw [(restNeon (p := p) (s := s)),e]; rfl) hy.spots.2)
   | @climb x v z h e hz ih=>
     unfold away at ih
     cases ih with
     | seq hp hq=>
       exact .seq (u.turnx b h) (.more (by rw [(restNeon (p := p) (s := s)),e]; rfl) hp hq)

end Covers
end Shows
end ExactDerandomization.Swirl

end

section

/-! Cap from bounded tours; constants are continuation tags, not
additional allocations. -/
namespace ExactDerandomization.Swirl
open Relay

lemma Stripe.twain {α} {r s:α→α→Prop} {x l y} (h:Stripe r x l y) (e:Stripe s y l.reverse x):
    Stripe (fun a b=> r a b ∧ s b a) x l y := by
   have he : Stripe (fun a b=>s b a) x l y := by simpa using e.both (w:=fun a b=>s b a) (fun _ _ h=>h)
   clear e
   induction h with
   | run h=> cases he with | run e=> exact .run ⟨h,e⟩
   | hook h _ ih=> cases he with | hook v e=> exact .hook ⟨h,v⟩ (ih e)

structure Rake where
    p : Shows
    flag : Flag
namespace Rake
variable (r:Rake)
abbrev forth := r.p.away true
abbrev back := r.p.away false
abbrev root (s:Arena) (v:Gem) := r.flag.f s.l.x (s.q,s.tag v false)
abbrev pass (s:Arena) (a b: Gem) :=
   s.acts r.forth (s.tag a false) (s.tag b false) ∧
       s.acts r.back (s.tag b false) (s.tag a false)

structure Circuit (s:Arena) (x:Gem) (l:List Gem) : Prop where
   round : Stripe (r.pass s) x l x
   init : r.root s x=true
   others : ∀ y∈l,r.root s y=false

lemma cable {s:Arena} (h:r.p.Covers s) {v:Dot} (hs:v∈s.trees.V) (he:s.trees.up v=none)
   (hm:r.p.check s (v,0)=true) (hz:r.root s (v,0)=true)
   (hk:∀ y:Gem,s.trees.nest v y → r.p.check s y=true → y≠(v,0) → r.root s y=false) :
   ∃ l:List Gem,r.Circuit s (v,0) l ∧ l.Nodup ∧ ∀ y,y∈l ↔
      s.trees.nest v y ∧ r.p.check s y=true ∧ y≠(v,0) := by
   obtain ⟨l,hl,h1,h2,h3⟩:=s.trees.streak hs he _ hm
   have ht (y:Gem) : y∈l ↔ s.trees.nest v y ∧ r.p.check s y=true ∧ y≠(v,0):=by
       rw [List.nodup_cons] at hl
       have h:=h1 y
       grind
   exact ⟨l, ⟨(h2.twain h3).every fun a b ⟨e,g⟩=>⟨h.flash _ e,h.flash _ g⟩,
                   hz,fun a e=>hk a ((ht a).1 e).1 ((ht a).1 e).2.1 ((ht a).1 e).2.2⟩,
                (List.nodup_cons.1 hl).2,ht⟩

def seek (r:Rake) : ℕ→(ℕ → Cog) → Cog → Cog
  | 0,y,n=> .bif r.flag (y 0) n
  | k+1,y,n=> .bif r.flag (y 0) (.seq r.forth (r.seek k (fun i=>y (i+1)) (.seq r.back n)))
inductive Alley (r:Rake) (s:Arena) (rootv:Gem) : Gem→ℕ→Prop
  | home (h:r.root s rootv=true) : Alley r s rootv rootv 0
  | walk {n a b} (h:r.pass s a b) (e:r.root s a=false) (g:Alley r s rootv b n) :
       Alley r s rootv a (n+1)

lemma Alley.ofStripe {r s a x l} (h:Stripe (r.pass s) x l a)
    (hs:r.root s a=true) (ht:r.root s x=false) (he:∀ i∈l,r.root s i=false):
    Alley r s a x (l.length+1):= by
    induction h with
    | run h=> exact .walk h ht (.home hs)
    | hook h e ih=> exact .walk h ht (ih hs (he _ (by simp)) fun i hi=>he i (by simp [hi]))
lemma sounded {s a b j} (h:Alley r s b a j) (n:ℕ) (y:ℕ → Cog) (w:Cog) {u}
    (hy:j≤n→ s.acts (y j) (s.tag b false) u)
    (hw:n<j→ s.acts w (s.tag a false) u) :
    s.acts (seek r n y w) (s.tag a false) u:= by
    induction h generalizing n y w with
    | home h=>
      cases n <;> exact .yes h (hy (Nat.zero_le _))
    | @walk j a b h e g ih=>
      cases n with
      | zero=> exact .no e (hw (by omega))
      | succ n=>
        exact .no e (.seq h.1 (ih n _ _ (fun ht=> hy (by omega)) (fun hz=> .seq h.2 (hw (by omega)))))

def gather (r:Rake) (k:ℕ) (f:ℕ → Cog) : Cog :=
   .seq r.forth (seek r k f (.seq r.back (f k)))

lemma attained {s x l} (h:r.Circuit s x l) (k:ℕ) (f:ℕ → Cog) {u}
   (he:s.acts (f (min l.length k)) (s.tag x false) u):
    s.acts (gather r k f) (s.tag x false) u:= by
   obtain ⟨hr,hi,h1⟩:=h
   cases l with
   | nil=>
      cases hr with
      | run hr=>
        apply Lot.Mane.seq hr.1
        apply r.sounded (.home hi)
        · intro; simpa using he
        intro h; omega
   | cons a l=>
      cases hr with
      | hook hp h=>
        have hv:=Alley.ofStripe h hi (h1 a (by simp)) (fun a e=>h1 a (by simp [e]))
        apply Lot.Mane.seq hp.1
        apply r.sounded hv
        · intro h; simpa [h] using he
        intro h
        exact .seq hp.2 (by simpa [show k≤l.length+1 by omega] using he)

def ply (f: Cog) : ℕ→ Cog→ Cog
   | 0,w=>w
   | n+1,w=>.seq f (ply f n w)
lemma follow {s:Arena} {f a b l} (p:Stripe
               (fun a b=>s.acts f (s.tag a false) (s.tag b false)) a l b) {w u}
   (h:s.acts w (s.tag b false) u) :
    s.acts (ply f (l.length+1) w) (s.tag a false) u:=by
   induction p with
   | run hz=>exact .seq hz h
   | hook hz e ih=>exact .seq hz (ih (by assumption))

def surf (r:Rake) (k:ℕ) (y:ℕ → Cog) (bad:Cog) : Cog :=
   seek r k (fun i=> gather r (k+1) fun m=>
        if m≤k then y (m+1-i) else ply r.back i bad) bad

lemma climbed {s x l} (h:r.Circuit s x l) (k:ℕ) (y:ℕ → Cog) (bad:Cog)
   {u a b i} (hs:l=a++i::b)
   (hy:l.length≤k → s.acts (y (a.length+1)) (s.tag x false) u)
   (hw:k< l.length → s.acts bad (s.tag i false) u) :
   s.acts (r.surf k y bad) (s.tag i false) u:= by
   subst l
   have hh:= h.round.sever
   have ht:= Alley.ofStripe hh.2 h.init (h.others i (by simp)) (fun x h1=>h.others x (by simp [h1]))
   apply r.sounded ht
   · intro hb
     apply r.attained h
     simp only [List.length_append,List.length_cons]
     split
     · next hl=>
       have h1: (a++i::b).length ≤ k:=by simp; omega
       have hp:=hy h1
       convert hp using 1
       have hz : min (a.length+(b.length+1)) (k+1)+1-(b.length+1)=a.length+1:= by omega
       rw [hz]
     · next hl=>
       have he:k < (a++i::b).length:=by simp; omega
       have hu:=follow (hh.2.both (w:=fun a b=>s.acts r.back (s.tag a false) (s.tag b false))
                                      (fun y z h=>h.2)) (hw he)
       simpa using hu
   intro hb; apply hw; simp; omega

def dune (r:Rake) (k i:ℕ) (yes bad:Cog) : Cog :=
   gather r (k+1) fun n=> if n≤ k ∧ 0 < i ∧ i≤n then ply r.forth i yes else bad

lemma chose {s x l} (h:r.Circuit s x l) (k i:ℕ) (yes bad:Cog)
   {u} (hy: (l.length≤ k ∧ 0 < i ∧ i≤l.length) →
             ∃ a b v,l=a++v::b ∧ i=a.length+1 ∧
                               s.acts yes (s.tag v false) u)
   (hw: ¬ (l.length≤ k ∧ 0 < i ∧ i≤l.length) → s.acts bad (s.tag x false) u):
    s.acts (r.dune k i yes bad) (s.tag x false) u:= by
   apply r.attained h
   split
   · next ht=>
     obtain ⟨a,b,v,e,ht1,hp⟩:=hy (by omega)
     subst l; subst i
     exact follow (h.round.sever.1.every (fun y z h=>h.1)) hp
   · next ht=> exact hw (by omega)

end Rake
end ExactDerandomization.Swirl

end

section

namespace ExactDerandomization.Swirl
open Relay Finset

structure Twig where
    V : Finset Dot
    rad : ℕ → ℕ
    goes : Dot →  Dot →  Prop
    pairs : ∀ {x y},goes x y  →  x∈V∧ y∈V∧ y.1 < rad x.1 ∧ x.1 < rad y.1
    aim : ∀ {x y z},goes x y  →  goes x z  →  z=y
    projected : ∀ {x y z},goes x y  →  goes z y  →  z.1=x.1  →  z=x

namespace Twig
noncomputable section
variable (p:Twig)

def sole (f:Dot → Prop) : Option Dot := by
   classical
   exact if h:∃ i,f i then some (Classical.choose h) else none
lemma solely (f:Dot → Prop) (h:∀ i,f i → ∀ j,f j  →  j=i) (i) :
    sole f=some i ↔ f i:=by
   classical
   unfold sole; split
   · next he=> have hh:=Classical.choose_spec he; grind
   next he=> grind

def upward (x:Dot):= sole (p.goes x)
def fromp (y:Dot)(i:ℕ):= sole (fun x=> p.goes x y ∧ x.1=i)

lemma atU {x y}:p.upward x=some y ↔ p.goes x y:= solely _ (fun _ h _ e=>p.aim h e) y
lemma atD {x y i}:p.fromp y i=some x ↔ p.goes x y ∧ x.1=i :=
   solely _ (fun _ ⟨h,e⟩ _ ⟨u,v⟩=>p.projected h u (v.trans e.symm)) _

def tree : Fir where
   V:=p.V
   rad:=p.rad
   up:=p.upward
   kid:=p.fromp
   pairU := fun _ _ _ h=> let u:=p.atU.1 h;
                           ⟨(p.pairs u).2.1,(p.pairs u).2.2.1,(p.pairs u).2.2.2,p.atD.2 ⟨u,rfl⟩⟩
   pairK := fun _ _ _ _ h=>let u:=p.atD.1 h; ⟨(p.pairs u.1).1,p.atU.2 u.1,u.2⟩

lemma probeU {x i y} : p.tree.probe true x i=some y ↔ p.goes x y ∧ y.1=i:= by
   unfold Fir.probe Fir.riseQ
   rw [ite_eq_left rfl]
   cases h:p.tree.up x with
   | none=>
      refine ⟨by simp,fun he=>?_⟩
      have hz : p.tree.up x=some y:=p.atU.2 he.1
      rw [h] at hz; contradiction
   | some w=>
      have hm:=p.atU.1 h
      constructor
      · rintro hp; split at hp
        · next he=> grind
        contradiction
      intro h
      obtain rfl:= p.aim hm h.1
      grind
lemma probeD {x i y} : p.tree.probe false y i=some x ↔ p.goes x y∧ x.1=i:=p.atD

end
end Twig

/-- The finite path-kernel: `after q name val = next_raw_name + 1`, zero for no
edge. Modes 0 = static, 1 = opaque stationary, any other = mobile. Every
operation-dependent guard is generated in LF before calling a lower query. -/
structure Bud where
    rad : Cub (Lore ℕ) ℕ
    mark : Cub (Lore Seat) Bool
    allow : Cub (Lore Seat) Bool
    mode : Cub (Lore ℕ) ℕ
    after : Cub (Lore Seat) ℕ
    beta : Cub (Lore Seat) ℕ
    stem : Bool →  Cub (Lore Seat) ℕ

/-- Root kernel proof data. hand maps addresses to the shared register carrying
that address and a catalyst, not to local pc states. Different hand embeddings
of the same addresses during different invocations are allowed. -/
structure Clay where
   l:Lot
   b:Level
   d:ℕ
   q:ℕ
   cost:ℕ
   raw: Finset ℕ
   cursor: Finset ℕ
   hand: ℕ → ℕ
   echo : ℕ → ℕ → ℕ
   stream : ℕ → ℕ → Bool → ℕ → Option ℕ

namespace Bud
variable (p:Bud) (s:Clay)

abbrev pk (s:Clay)(v i:ℕ) : Lore Seat := (s.q,v,i)
abbrev ready (v i) := p.allow.f s.l.x (pk s v i)

abbrev entry v:= p.mode.f s.l.x (s.q,v)
abbrev nextx (v i) := p.after.f s.l.x (pk s v i)
abbrev code (v i):=p.beta.f s.l.x (pk s v i)
abbrev range0 v:=p.rad.f s.l.x (s.q,v)

def earth:= s.raw ×ˢ s.cursor
lemma walled {x:Dot} : x∈ earth s ↔ x.1∈s.raw ∧ x.2∈s.cursor:=mem_product

def Hill (x y:Dot) :Prop :=
   x∈earth s ∧ y∈earth s ∧ p.ready s x.1 y.1=true ∧
    match p.entry s x.1 with
    | 0=> p.nextx s x.1 0=y.1+1 ∧ x.2=y.2
    | 1=> p.nextx s x.1 (s.echo x.1 x.2)=y.1+1 ∧ x.2=y.2
    | _=> s.stream x.1 (p.code s x.1 y.1) true x.2=some y.2

/-- Canonical toss calls for stationary/moving candidates -/
abbrev poke (b:Bool) (i j:ℕ) := p.stem b |>.f s.l.x (pk s i j)
def motorout (v z:ℕ)(b:Bool)(c:ℕ): Site :=
    match s.stream v z b c with
    | none=> (0,s.hand c)
    | some w=> (1,s.hand w)

def bed (a:Bool) (v i c:ℕ):Site:= Pause ((a,v,i):Panel) (s.hand c)

structure Wall : Prop where
    scaled : ∀ {v i},p.ready s v i=true  →
                    v∈s.raw ∧ i∈s.raw ∧ i<p.range0 s v ∧ v<p.range0 s i
    size : ∀ {v c},v∈s.raw  →  c∈s.cursor  →  ∀ i≤ p.range0 s v,∀ b,s.l.state s.cost s.b (bed s b v i c)
    call : ∀ {v i}, p.ready s v i=true  →  p.entry s v≠0  →  ∀ b,
          let a : Seat:= if b then (v,i) else (i,v)
          s.l.jump s.cost s.b s.d (enc ((false,a):Panel)) (p.poke s b v i)
    upright : ∀ {v i}, p.ready s v i=true  →  p.entry s v=1  →  ∀ x∈s.cursor,∀ b,
         Boots s.l.x s.l.F s.l.P (p.poke s b v i) s.l.P (0,s.hand x) (s.echo v x,s.hand x)
    kite : ∀ {v i}, p.ready s v i=true  →  2 ≤ p.entry s v  →
         p.nextx s v (p.code s v i)=i+1 ∧ ∀ x∈s.cursor,∀ b,
           Boots s.l.x s.l.F s.l.P (p.poke s b v i) s.l.P (0,s.hand x)
                (motorout s v (p.code s v i) b x) ∧
               ∀ y,s.stream v (p.code s v i) b x=some y  →
                   y∈s.cursor ∧ s.stream v (p.code s v i) (!b) y=some x
    unique : ∀ {v i j}, p.ready s v i=true  →  p.ready s v j=true  →  2≤ p.entry s v  →
       ∀ x∈s.cursor,∀ y z, s.stream v (p.code s v i) true x=some y  →
                             s.stream v (p.code s v j) true x=some z  →
                             p.code s v i=p.code s v j

def Wall.twig {s:Clay} {p:Bud} (h:Wall p s) : Twig where
    V:=earth s
    rad:=p.range0 s
    goes:=p.Hill s
    pairs:= fun {_ _} ⟨ha,hb,hc,_⟩=> ⟨ha,hb,(h.scaled hc).2.2⟩
    aim:=by
       rintro x y z ⟨ha,hb,hc,hp⟩ ⟨_,hd,he,hq⟩
       let i:=x.1
       cases ht:p.entry s x.1 with
       | zero=> rw [ht] at hp hq; grind
       | succ n=>
         cases n with
         | zero=> rw [ht] at hp hq; grind
         | succ n=>
           rw [ht] at hp hq
           have hs : 2 ≤ p.entry s x.1:=by omega
           have hu:= h.unique hc he hs x.2 ((walled _).1 ha).2 _ _ hp hq
           have hx: z.1=y.1:=by have h1:= (h.kite hc hs).1; have h2:=(h.kite he hs).1; grind
           apply Prod.ext hx
           grind
    projected:=by
       rintro x y z ⟨ha,hb,hc,hp⟩ ⟨hz,_,he,hq⟩ e
       apply Prod.ext e; rw [e] at hq
       cases ht:p.entry s x.1 with
       | zero=> rw [ht] at hp hq; grind
       | succ n=>
         cases n with
         | zero=> rw [ht] at hp hq; grind
         | succ n=>
           rw [ht] at hp hq
           have hs : 2 ≤ p.entry s x.1:=by omega
           have h1:=((h.kite hc hs).2 x.2 ((walled _).1 ha).2 true).2 _ hp
           have h2:=((h.kite hc hs).2 z.2 ((walled _).1 hz).2 true).2 _ hq
           grind

noncomputable def arena {p:Bud} {s:Clay}(h:p.Wall s):Arena :=
    ⟨s.l,s.b,s.d,s.q,s.cost,h.twig.tree,s.hand⟩

end Bud
end ExactDerandomization.Swirl

end

section

namespace ExactDerandomization.Swirl
open Relay Finset
namespace Bud
variable (p:Bud) (s:Clay)

def invert (b:Bool) (a:Seat) : Seat := if b then a else (a.2,a.1)
lemma invert2 (b:Bool) (x:Seat): invert b (invert b x)=x:=by cases b <;>simp [invert]

def lit (s:Clay) (b:Bool) (a:Seat) (c:ℕ) : Option ℕ :=
    let (v,i):=invert b a
    if p.ready s v i then
      match p.entry s v with
      | 0=> if p.nextx s v 0=i+1 then some c else none
      | 1=> if p.nextx s v (s.echo v c)=i+1 then some c else none
      | _=> s.stream v (p.code s v i) b c
    else none

namespace Wall
variable {p s} (h:Wall p s)
include h

lemma alive {v i c e:ℕ} (hc:c∈s.cursor) :
    p.Hill s (v,c) (i,e) ↔ p.lit s true (v,i) c=some e:=by
   unfold Hill lit; simp only [invert,ite_true]
   by_cases hv:p.ready s v i=true
   · obtain ⟨ha,hb,h1,h2⟩:=h.scaled hv
     rw [ite_eq_left hv]
     cases hk:p.entry s v with
     | zero=>
       by_cases ht:p.nextx s v 0=i+1 <;> simp [hv,walled,ha,hb,hc,ht] ; grind
     | succ k=>
       cases k with
       | zero=> by_cases ht:p.nextx s v (s.echo v c)=i+1 <;>
                      simp [hv,walled,ha,hb,hc,ht] ; grind
       | succ k=>
         simp only [hv,walled,ha,hb,hc,true_and,and_self ]
         constructor
         · intro e; exact e.2
         intro e; exact ⟨(((h.kite hv (by omega)).2 c hc true).2 _ e).1,e⟩
   simp [hv]

lemma hover {v i c e:ℕ} (hc:c∈s.cursor) :
    p.Hill s (v,e) (i,c) ↔ p.lit s false (i,v) c=some e:=by
   unfold Hill lit; simp only [invert,Bool.false_eq_true,ite_false]
   by_cases hv:p.ready s v i=true
   · obtain ⟨ha,hb,h1,h2⟩:=h.scaled hv
     rw [ite_eq_left hv]
     cases hk:p.entry s v with
     | zero=>
       by_cases ht:p.nextx s v 0=i+1 <;> simp [hv,walled,ha,hb,hc,ht] ; grind
     | succ k=>
       cases k with
       | zero=> by_cases ht:p.nextx s v (s.echo v c)=i+1 <;>
                      simp [hv,walled,ha,hb,hc,ht] <;> grind
       | succ k=>
         simp only [hv,walled,ha,hb,hc,true_and,and_self ]
         constructor
         · intro e; exact (((h.kite hv (by omega)).2 _ e.1 true).2 _ e.2).2
         intro e; exact ((h.kite hv (by omega)).2 c hc false).2 _ e
   simp [hv]

lemma auth (b:Bool) {v c:ℕ} (hc:c∈s.cursor) (i:ℕ) :
   h.twig.tree.probe b (v,c) i = (p.lit s b (v,i) c).map (fun j=>(i,j)):=by
   have he(w:Dot): h.twig.tree.probe b (v,c) i=some w ↔
                (p.lit s b (v,i) c).map (fun j=>(i,j))=some w:=by
      rcases w with ⟨w,e⟩
      cases b
      · rw [h.twig.probeD]
        by_cases hk:w=i
        · subst w; change p.Hill s (i,e) (v,c) ∧ _ ↔ _; rw [h.hover hc]; simp
        simp [hk,Ne.symm hk]
      · rw [h.twig.probeU]
        by_cases hk:w=i
        · subst w; change p.Hill s (v,c) (i,e) ∧ _ ↔ _; rw [h.alive hc]; simp
        simp [hk,Ne.symm hk]
   generalize h1:h.twig.tree.probe b (v,c) i=w at *
   generalize h2:(p.lit s b (v,i) c).map (fun j=>(i,j))=z at *
   cases w with
   | none=> cases z with
            | none=>rfl
            | some a=> have := he a; simp_all
   | some a=>
     exact ((he a).1 rfl).symm

lemma again (b:Bool) {v i c w} (hc:c∈s.cursor) (hw:p.lit s b (v,i) c=some w) :
   w∈s.cursor := by
   cases b
   · exact ((walled s).1 ((h.hover hc).2 hw).1).2
   · exact ((walled s).1 ((h.alive hc).2 hw).2.1).2

lemma dusk (b:Bool) {v c:ℕ} (hc:c∈s.cursor) (i:ℕ) :
    (arena h).touch b (v,c) i =
      match p.lit s b (v,i) c with
      | none=> bed s false v i c
      | some e=>bed s true v i e:=by
   unfold Arena.touch
   have he : (arena h).trees.probe b (v,c) i=(p.lit s b (v,i) c).map (fun j=>(i,j)) :=
       h.auth b hc i
   rw [he]
   cases p.lit s b (v,i) c <;> rfl

end Wall
end Bud
end ExactDerandomization.Swirl

end

section

namespace ExactDerandomization.Swirl
open Relay Finset
namespace Bud
variable (p:Bud)

def putter (b:Bool) (_:Word) (a:Lore Panel) : Lore Seat :=
    (a.1,invert b a.2.2)
lemma putK(b):Kn (putter b):= by
   cases b
   · exact Kn.first.tuple (Kn.next.right.right.tuple Kn.next.right.left)
   · exact Kn.first.tuple Kn.next.right
def gate (b:Bool) (x:Word) (a:Lore Panel) : Bool:= p.allow.f x (putter b x a)
def chk (b:Bool) (x:Word) (a:Lore Panel):ℕ :=
     let u:=putter b x a
     p.mode.f x (u.1,u.2.1)
lemma chkK (b):Kn (p.chk b) := p.mode.runs.comp ((putK b).left.tuple (putK b).right.left)

def printx (b:Bool) (x:Word) (a : Lore Panel × ℕ) : Panel :=
    let u:= putter b x a.1
    let i:= p.after.f x (u.1,u.2.1,a.2)
    (if p.chk b x a.1 ≤ 1 then decide (i=u.2.2+1) else decide (a.2=1),
     a.1.2.2)

lemma printK (b): Kn (p.printx b) := by
   have hp := (putK b).comp (Kn.first (β:=ℕ))
   have hg := p.after.runs.comp (hp.left.tuple (hp.right.left.tuple Kn.next))
   exact (((p.chkK b).comp Kn.first).cond_le (Kn.fix _) (hg.eq hp.right.right.succ) (Kn.next.eq (Kn.fix _))).tuple Kn.first.right.right

def pureq (b:Bool) (x:Word) (a:Lore Panel) := p.printx b x (a,0)
lemma pureK (b) : Kn (p.pureq b) := (p.printK b).comp (Kn.identity.tuple (Kn.fix _))

def script (b:Bool) (x:Word) (a:Slip) := (p.stem b).f x (putter b x (a.1,dec a.2))
lemma scriptK (b) : Kn (p.script b) :=
   (p.stem b).runs.comp ((putK b).comp (Kn.first.tuple (Kn.unpack.comp Kn.next)))

def heedx (b:Bool) (x:Word) (a:Drain) : Site :=
   Pause (p.printx b x ((a.1.1,dec a.1.2),a.2.1)) a.2.2
lemma heedK (b): Kn (p.heedx b) := (Kn.wash.comp ((p.printK b).comp
    ((Kn.first.left.tuple (Kn.unpack.comp Kn.first.right)).tuple Kn.next.left))).tuple Kn.next.right

def tackle (b:Bool):Cog :=
   .bif (gear (p.gate b) (p.allow.runs.comp (putK b)))
         (.bif (gear (fun x a=> decide (p.chk b x a=0)) ((p.chkK b).eq (Kn.fix _)))
           (etch (p.pureq b) (p.pureK b))
           (.toss ⟨_,p.scriptK b⟩ ⟨_,p.heedK b⟩))
         (.edit ⟨_,Kn.next⟩)

def showall : Shows:= ⟨p.rad,p.mark,p.tackle⟩

namespace Wall
variable {s p} (h:Wall p s)

set_option maxHeartbeats 800000 in
lemma handle {v c} (hv:v∈s.raw) (hc:c∈s.cursor) {i} (hi:i<p.range0 s v)
   (b:Bool):
   (arena h).acts (p.tackle b) (bed s false v i c) ((arena h).touch b (v,c) i):= by
   let a:Panel:=(false,v,i)
   let z:= invert b a.2
   have ha:=h.size hv hc i hi.le false
   rw [h.dusk b hc]
   have hz : z.1=(invert b (v,i)).1∧ z.2=(invert b (v,i)).2:=⟨rfl,rfl⟩
   have hg : (gear (p.gate b) (p.allow.runs.comp (putK b))).f s.l.x (s.q,bed s false v i c)=
                               p.ready s z.1 z.2 := gear_at ..
   have hy : p.chk b s.l.x (s.q,a)=p.entry s z.1:=rfl
   have hm : (gear (fun x a=> decide (p.chk b x a=0)) ((p.chkK b).eq (Kn.fix 0))).f
             s.l.x (s.q, bed s false v i c)=decide (p.entry s z.1=0):=gear_at ..
   by_cases ht:p.ready s z.1 z.2=true
   · apply Lot.Mane.yes (hg.trans ht)
     have ht' := ht
     dsimp only [z,a] at ht'
     cases he:p.entry s z.1 with
     | zero=>
       apply Lot.Mane.yes (by rw [hm,he]; rfl)
       by_cases he0:p.nextx s z.1 0=z.2+1
       · have hu : p.lit s b (v,i) c=some c:=by
             unfold lit; simp only [ht',ite_true]
             change (match p.entry s z.1 with | 0=> _ | 1=>_ | _=>_)=_
             rw [he]; exact ite_eq_left he0
         rw [hu]
         refine etches _ _ ?_ ha (h.size hv hc i hi.le true)
         change p.printx b s.l.x ((s.q,a),0)=(true,v,i)
         dsimp only [printx]; rw [hy,he,ite_eq_left (by omega)]
         change (decide (p.nextx s z.1 0=z.2+1),v,i)=(true,v,i)
         simp [he0]
       · have hu : p.lit s b (v,i) c=none:=by
             unfold lit; simp only [ht',ite_true]
             change (match p.entry s z.1 with | 0=> _ | 1=>_ | _=>_)=_
             rw [he]; exact ite_eq_right he0
         rw [hu]
         refine etches _ _ ?_ ha ha
         change p.printx b s.l.x ((s.q,a),0)=(false,v,i)
         dsimp only [printx]; rw [hy,he,ite_eq_left (by omega)]
         change (decide (p.nextx s z.1 0=z.2+1),v,i)=(false,v,i); simp [he0]
     | succ n=>
       apply Lot.Mane.no (by rw [hm,he]; simp)
       have hd:=h.call ht (show p.entry s z.1≠0 by omega) b
       have hc1 : s.l.jump s.cost s.b s.d (bed s false v i c).1 (p.poke s b z.1 z.2):=by
          cases b <;> exact hd
       have hc2:p.script b s.l.x (s.q, (bed s false v i c).1)=p.poke s b z.1 z.2:=by
          unfold script; simp [bed,Pause]; rfl
       have hc3 (t w:ℕ) : p.heedx b s.l.x ((s.q,(bed s false v i c).1),(t,w)) =
                                  Pause (p.printx b s.l.x ((s.q,a),t)) w:=by simp [heedx,a,bed,Pause]
       cases n with
       | zero=>
         let t:=s.echo z.1 c
         have hh:= h.upright ht he c hc b
         by_cases hb:p.nextx s z.1 t=z.2+1
         · have hu:p.lit s b (v,i) c=some c:=by
             unfold lit; simp only [ht',ite_true]
             change (match p.entry s z.1 with | 0=>_ | 1=>_ | _=>_)=_
             rw [he]; exact ite_eq_left hb
           have hs:p.printx b s.l.x ((s.q,a),t)=(true,v,i):=by
              dsimp only [printx]; rw [hy,he,ite_eq_left (by omega)]
              change (decide (p.nextx s z.1 t=z.2+1),v,i)=(true,v,i); simp [hb]
           rw [hu]; exact .toss hc2 ((hc3 t (s.hand c)).trans (congrArg (fun n=>Pause n (s.hand c)) hs)) ha (h.size hv hc i hi.le true) hc1 hh
         have hu:p.lit s b (v,i) c=none:=by
             unfold lit; simp only [ht',ite_true]
             change (match p.entry s z.1 with | 0=>_ | 1=>_ | _=>_)=_
             rw [he]; exact ite_eq_right hb
         have hs:p.printx b s.l.x ((s.q,a),t)=(false,v,i):=by
              dsimp only [printx]; rw [hy,he,ite_eq_left (by omega)]
              change (decide (p.nextx s z.1 t=z.2+1),v,i)=(false,v,i); simp [hb]
         rw [hu]; exact .toss hc2 ((hc3 t (s.hand c)).trans (congrArg (fun n=>Pause n (s.hand c)) hs)) ha ha hc1 hh
       | succ n=>
         have hh2 : 2 ≤ p.entry s z.1:=by omega
         have hh:= (h.kite ht hh2).2 c hc b
         have hQ:p.lit s b (v,i) c=s.stream z.1 (p.code s z.1 z.2) b c:=by
             unfold lit; simp only [ht',ite_true]
             change (match p.entry s z.1 with | 0=>_ | 1=>_ | _=>_)=_
             rw [he]
             rfl
         have hh1:=hh.1; unfold motorout at hh1
         rw [hQ]
         cases he0:s.stream z.1 (p.code s z.1 z.2) b c with
         | none=>
           have hs:p.printx b s.l.x ((s.q,a),0)=(false,v,i):=by
              dsimp only [printx]; rw [hy,he,ite_eq_right (show ¬ n+1+1 ≤ 1 by omega)]
              rfl
           rw [he0] at hh1; exact .toss hc2 ((hc3 0 (s.hand c)).trans (congrArg (fun n=>Pause n (s.hand c)) hs)) ha ha hc1 hh1
         | some w=>
           have hs:p.printx b s.l.x ((s.q,a),1)=(true,v,i):=by
              dsimp only [printx]; rw [hy,he,ite_eq_right (show ¬ n+1+1 ≤ 1 by omega)]
              rfl
           rw [he0] at hh1
           exact .toss hc2 ((hc3 1 (s.hand w)).trans (congrArg (fun n=>Pause n (s.hand w)) hs)) ha (h.size hv (hh.2 _ he0).1 i hi.le true) hc1 hh1
   have hx : p.ready s z.1 z.2=false := by simp_all
   apply Lot.Mane.no (hg.trans hx)
   have hu:p.lit s b (v,i) c=none:=by unfold lit; apply ite_eq_right ht
   rw [hu]; exact .edit rfl ha ha

theorem yields : p.showall.Covers (arena h) := by
   refine ⟨fun _ _=>rfl,?_,?_⟩
   · rintro ⟨⟨v,c⟩,i⟩ ⟨hv,ht⟩ b
     obtain ⟨hv,hc⟩:= (walled _).1 hv
     exact h.size hv hc i ht b
   rintro b ⟨v,c⟩ h0 i hi
   obtain ⟨hv,hc⟩:= (walled _).1 h0
   exact h.handle hv hc hi b

end Wall
end Bud
end ExactDerandomization.Swirl

end

end OAI
