import OAI.Computability.Logspace.IterationSchedule
import OAI.Computability.Logspace.RowEvaluation

namespace OAI

/-!
Uniform configuration, copy-arc, and reward evaluation.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Spring
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Aqua

variable (r:Rock q w h)

def tally (x:Word)(i:ℕ):ℕ:=
    r.P.size x * min (r.n x) (r.w.p.M^i)
lemma tallyK {α}[Wire α]{i:PT α ℕ}(he:Kn i):Kn (fun x a=>tally r x (i x a)):=
   (show Kn (fun x (_:α)=>r.P.size x) from fun _ _=>r.P.eSize).times (Kn.cap r.nKn (Kn.fix _) he)

section
variable {u:Line (q:=q) (w:=w) (h:=h)}
lemma wideT {_ i:ℕ}:0 ≤ i:=Nat.zero_le _
lemma tank (_:u.Chart) (i:ℕ):
   (u.plotM.stage i).S=range (u.r.P.size u.x*u.w0.p.M^i):=by
    let M:=u.w0.p.M
    have hM:0<M:=by have hp:=u.w0.p.mOK; dsimp only [M]; omega
    induction i with
    | zero=> rw [pow_zero,mul_one]; rfl
    | succ i ih=>
      rw [Scene.mature,Stg.next]
      change copyZone (u.plotM.stage i).p.M (u.plotM.stage i).S=_
      rw [u.plotM.aligned,ih]
      ext j; change j∈copyZone M _↔j∈range (_*M^(i+1))
      rw [member_copy hM,mem_range,mem_range]
      rw [Nat.div_lt_iff_lt_mul hM,pow_succ,mul_assoc]
lemma maxv (e:u.Chart) {i:ℕ}(hi:i ≤ u.B):
    tally u.r u.x i = u.r.P.size u.x *u.r.w.p.M ^ i:=by
   have hs:=e.sc
   have hk : u.w0.p.M ≤ 2^u.w0.p.M:=le_trans (by omega) (exp_big _)
   let m:=u.w0.p.M
   have hh : m^i ≤ (2:ℕ)^(u.w0.ceiling u.B):=le_trans (Nat.pow_le_pow_left hk i) (by
      rw [←pow_mul]
      apply Nat.pow_le_pow_right (by omega)
      unfold Wares.ceiling Wares.density
      have ht:=Nat.mul_le_mul_left m hi
      unfold m at ht;nlinarith)
   unfold tally
   rw [min_eq_right (show m^i ≤ u.n from le_trans hh hs.fuel)]
lemma room (e:u.Chart) {i:ℕ}(hi:i ≤ u.B):
    range (tally u.r u.x i)=(u.plotM.stage i).S:=by rw [tank e,maxv e hi]
end

def dbox (n k:ℕ):Coin:=Coin.ofZ ((min n (2^k))^4:ℕ)
abbrev qua (n k:ℕ):Coin:=Coin.inv (dbox n k)
def qq (n k:ℕ): Coin:=Coin.mult (Coin.ofZ ((side n k)^4:ℕ)) (Coin.inv (Coin.ofZ (n^4:ℕ)))
def quo (n a k:ℕ):Coin:=
      Coin.mult (Coin.mult (qua n k) (dbox n a))
                 (Coin.mult (qq n a) (Coin.inv (qq n (max a k))))
def rawcoins(n k:ℕ):Coin:= Coin.mult (qua n k) (Coin.inv (qq n k))
def sbase(n k:ℕ):Coin:=Coin.mult (Coin.inv (Coin.ofZ 2)) (dbox n k)

def zet :Coin:=Coin.place 1 (4096*400*1000000*1000)
lemma coinZ : zet.v=zeta:=by norm_num [zet,zeta,At.small,delta,Hie.A,Coin.place,Coin.v]

section
variable {α}[Wire α]{n a k:PT α ℕ}
lemma dboxK (h:Kn n)(he:Kn k):Kn (fun x p=>dbox (n x p) (k x p)):=
    Coin.ofK (((Kn.cap h (Kn.fix 2) he).power 4).ZofN)
lemma qqK (h:Kn n)(he:Kn k):Kn (fun x p=>qq (n x p) (k x p)):=
   Coin.multK (Coin.ofK (((Print.asideK h he).power 4).ZofN)) (Coin.invK (Coin.ofK ((h.power 4).ZofN)))
lemma largeK {α}[Wire α]{t s:PT α ℕ}(h:Kn t)(e:Kn s):Kn (fun x a=>max (t x a) (s x a)):=by
    simpa only [max_def] using h.cond_le e e h
lemma quoK(h:Kn n)(ht:Kn a)(he:Kn k):Kn (fun x p=>quo (n x p) (a x p) (k x p)):=by
   exact Coin.multK (Coin.multK (Coin.invK (dboxK h he)) (dboxK h ht)) (Coin.multK (qqK h ht)
                                                     (Coin.invK (qqK h (largeK ht he))))
lemma rawK (h:Kn n)(he:Kn k):Kn (fun x p=>rawcoins (n x p) (k x p)):=
   Coin.multK (Coin.invK (dboxK h he)) (Coin.invK (qqK h he))
end
variable {n:ℕ} [Fact n.Prime]
omit [Fact (Nat.Prime n)] in
lemma priceT {k:ℕ}(h:2^k ≤ n):(dbox n k).v=(rate k)⁻¹:=by simp [dbox,rate,h]
omit [Fact (Nat.Prime n)] in
lemma priceV {k:ℕ}(h:2^k ≤ n):(qua n k).v=rate k:=by rw [Coin.inv0,priceT h, inv_inv]
omit [Fact (Nat.Prime n)] in
lemma pc (k:ℕ):(qq n k).v=pct n k:=by simp [qq,pct]; ring_nf
omit [Fact (Nat.Prime n)] in
lemma pureG {a k:ℕ}(h:2^(nar a k) ≤ n): (quo n a k).v=loaded n a k:=by
   have ha:2^a ≤ n:= le_trans (Nat.pow_le_pow_right Nat.zero_lt_two (le_max_left ..)) h
   have hk: 2^k ≤ n:= le_trans (Nat.pow_le_pow_right Nat.zero_lt_two (le_max_right ..)) h
   simp only [quo,Coin.mul0,priceT ha,priceV hk,Coin.inv0,pc]
   unfold loaded nar; ring_nf
omit [Fact (Nat.Prime n)] in
lemma raw (k:ℕ)(h:2^k ≤ n):(rawcoins n k).v=peeler n k:=by
    rw [rawcoins,Coin.mul0,priceV h,Coin.inv0,pc,peeler,div_eq_mul_inv]
omit [Fact (Nat.Prime n)] in
lemma seed (k:ℕ)(h:2^k ≤ n): (sbase n k).v=(2:ℝ)⁻¹*(rate k)⁻¹:=by
    simp [sbase,priceT h]
end Aqua

namespace WindY
abbrev tx:ℕ:=Fintype.card Env.Atom
lemma nowM : 0<tx:=Fintype.card_pos
variable (r:Rock q w h)
def shower (x:Word) (j:ℕ):Coin:=
    let s:= 2^(planets r x*(r.w.ell * lb tx))
    Coin.inv (Coin.ofZ ((min s (tx^j)):ℕ))
lemma showerK {α}[Wire α]{g :PT α ℕ}(h:Kn g):Kn (fun x a=>shower r x (g x a)):=
     Coin.invK (Coin.ofK ((Kn.cap (upclock r _) (Kn.fix _) h).ZofN))
lemma rains (x: Word){l:ℕ}(h:l ≤ r.w.ell*Moon.M r x):
     (shower r x l).v=Env.weight^l:=by
   unfold shower; dsimp only
   have he:=below tx
   have hh: tx^l ≤  2^(planets r x * (r.w.ell*lb tx)):=by
       refine le_trans (Nat.pow_le_pow_left he.le l) ?_
       rw [← pow_mul]
       apply Nat.pow_le_pow_right (by omega)
       refine le_trans (Nat.mul_le_mul_left _ h) ?_
       have ht:Moon.M r x ≤ planets r x:=by unfold planets; omega
       nlinarith [Nat.mul_le_mul_right (r.w.ell*lb tx) ht]
   rw [min_eq_right hh,Coin.inv0,Coin.ofv]
   simp [Env.weight,tx,inv_pow]
lemma careful (l:ℕ):0 ≤ Env.weight^l ∧ Env.weight^l ≤1:=by
    have h:0≤Env.weight:=by unfold Env.weight; positivity
    have hs : 1 ≤ (tx:ℝ) := by exact_mod_cast nowM
    have hv:Env.weight ≤1:=by apply inv_le_one_of_one_le₀ hs
    exact ⟨by positivity,pow_le_one₀ h hv⟩
end WindY

/- environment remap for copy arcs -/
namespace Prism
def swap (n M i j:ℕ) (s:Issue):Issue:= (Print.stretch n M i s.1,Print.stretch n M j s.2.1,s.2.2)
lemma swapK {α}[Wire α]{n i j:PT α ℕ}{s:PT α Issue}(hn:Kn n)(hi:Kn i)(hj:Kn j)(hs:Kn s)(M):
   Kn (fun x a=> swap (n x a) M (i x a) (j x a) (s x a)):=
   (Print.stretchK hn (Kn.fix M) hi hs.left).tuple ((Print.stretchK hn (Kn.fix M) hj hs.right.left).tuple hs.right.right)
lemma masked {n M:ℕ} [Fact n.Prime](h:0<M)(he:M<n)(i j:ℕ)(s:Pool n) :
    swap n M i j (Print.issued s)=Print.issued (Est.pane M i j s):=by
   have hs:(M:ZMod n)≠0:=by
     intro hm; have hh:=congrArg ZMod.val hm
     rw [ZMod.val_natCast,Nat.mod_eq_of_lt he,ZMod.val_zero] at hh; omega
   unfold swap Print.issued
   erw [Print.stretchy _ _ _ hs,Print.stretchy _ _ _ hs]
   simp only [pane,replica,dite_eq_right hs]; rfl
def leftE (s:Issue):Issue:=(s.1,s.2.2,s.2.1)
def rightE (s:Issue):Issue:=(s.2.2,s.2.1,s.1)
def crossE (s:Issue):Issue:=(s.2.1,s.1,s.2.2)

end Prism
end
end ExactDerandomization.Spring

end

section

namespace ExactDerandomization.Spring
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain
noncomputable section
open scoped Classical

namespace Garden

variable (w:Wares)
abbrev fence(a:Crt):Scout:= Age.styx a
abbrev m(a:Crt):=Age.MV a
abbrev origin(a:Crt):= (fence a).2.1
abbrev stageQ(a:Crt):=(fence a).1.1
abbrev params(a:Crt):ID:= (fence a).1
abbrev greenY(a:Crt):=(fence a).1.2.2.1
abbrev matchZ(a:Crt):=(fence a).2.2.2
abbrev countO(a:Crt):= if origin a=1 then w.p.T else (fence a).2.2.1

def asker (a:Crt) := (range (greenY a+m a+1)).filter fun k=> (if origin a=0 then stageQ a-1 else stageQ a) ≤ k+pad w.p
def foreground (a:Crt)(b:Bool):Finset Ray:=
   if b then
     if origin a=0 then (if stageQ a=0 then ∅ else asker w a ×ˢ range (w.p.M*w.p.M))
     else (asker w a ×ˢ range (if countO w a=0 then 1 else 2) ∪
            if origin a=1 then {(stageQ a,2)} else ∅)
   else if matchZ a=true ∧ origin a≠4 then {(greenY a,0)} else ∅

def atmos (c:Crt)(q:Seed):Prop :=
    q=Seed.along q.2 q.x q.y ∧ q.x<w.p.K∧q.y<w.p.K ∧
         q.fog.habitat w (greenY c) (m c) (Age.g c) (foreground w c q.fog.first0)
def retired(c:Crt) (q:Seed):Prop:=
     q=Seed.old true q.x ∧ Age.g c ≠ 0 ∧ q.x < capacity 2 w.p.K (Age.L (m c)) (Age.g c-1)
def began(c:Crt) (q:Seed):Prop:=
     q=Seed.old false q.x ∧ Age.g c=0∧ origin c=0 ∧ stageQ c=0∧ q.x<2
def ace (c:Crt)(q:Seed):Prop:=atmos w c q ∨ retired w c q ∨ began c q

abbrev Lead:=Crt × Seed
abbrev Pan:=ℕ×ℕ
def clean (w:Wares)(p:Pan):Bool:=decide (enc (dec p.2:Seed)=p.2 ∧ ace w (dec p.1) (dec p.2))
namespace Plot
open Helix.GK
variable {α β}[Wire α][Wire β]{b:PT α Bool}{n k :PT α ℕ}
lemma wall {f h:PT α β}(hp:Kn f)(he:Kn h):GK (fun x a=> f x a=h x a):=by
    convert eqG (Kn.wash.comp hp) (Kn.wash.comp he) using 1
    ext x a; exact ⟨fun e=>congrArg enc e,fun v=>(Wire.eq _).symm.trans ((congrArg dec v).trans (Wire.eq _))⟩
lemma matt {f g:PT α Prop}(h:Kn b)(he:GK f)(hg:GK g):GK (fun x a=> if b x a then f x a else g x a):=by
    let h1:=GK.forth h
    convert orG (h1.andG he) (h1.notG.andG hg) using 1
    ext x a; split <;> simp_all
lemma countEat (h:Kn n)(he:Kn k)(j:ℕ):GK (fun x a=> n x a<j^ (k x a)):=by
   convert GK.ltG h (Kn.cap h.succ (Kn.fix j) he) using 1
   ext x a; omega
variable {a:PT α Crt}{r:PT α Ray}{f:PT α Fog}{s:PT α Seed}
lemma askG (h:Kn a)(g:Kn k):GK (fun x p=> k x p ∈ asker w (a x p)):=by
   have p:=h.right.right.left
   have hp:=p.left.left
   let hx:=p.left.right.right.left.add h.right.left.left
   convert (ltG g hx.succ).andG (leG (p.right.left.cond_eq (Kn.fix 0) hp.pred hp)
                                                   (g.add (Kn.fix (pad w.p)))) using 1
   ext x q; simp only [asker,mem_filter,mem_range]
lemma fgG (h:Kn a)(hp:Kn r)(hg:Kn b):
    GK (fun x u=>r x u∈ foreground w (a x u) (b x u)) :=by
    have he:=h.right.right.left
    let i:=he.left.left
    let t:=he.right.left
    let N:= t.cond_eq (Kn.fix 1) (Kn.fix w.p.T) he.right.right.left
    let k(e:ℕ):=GK.eqG t (Kn.fix e)
    let so:= (forth he.right.right.right).andG ((k 4).notG)
    let z:= wall hp (he.left.right.right.left.tuple (Kn.fix 0))
    let v:= asker w
    let q:= askG w h hp.left
    let u:= (GK.notG (eqG i (Kn.fix 0))).andG (q.andG (ltG hp.right (Kn.fix (w.p.M*w.p.M))))
    let Q:=q.andG (ltG hp.right (N.cond_eq (Kn.fix 0) (Kn.fix 1) (Kn.fix 2)))
    let Z:= Q.orG ((k 1).andG (wall hp (i.tuple (Kn.fix 2))))
    convert matt hg (ifG u Z t (Kn.fix 0)) (so.andG z) using 1
    ext x a; unfold foreground; split <;> grind

lemma fogK (h:Kn a)(e:Kn f):Kn (fun x u=> (f x u).ray (greenY (a x u))):=
     let p:=h.right.right.left.left.right.right.left
     let q:=e.left.right
     (q.left.left.cond (p.add q.left.right) (p.sub q.left.right)).tuple q.right.left

lemma reachK {m g a k:PT α ℕ}(h:Kn m)(e:Kn g)(hp:Kn a)(he:Kn k):
  Kn (fun x v=> Stair.reach ⟨m x v,0,⟨a x v,0,0⟩,w.ell⟩ (k x v) (g x v)) :=
    h.sub (Aqua.largeK (Age.gapK h e) (((hp.sub he).add (he.sub hp)).succ))
lemma yokeK {m g a k:PT α ℕ}(h:Kn m)(e:Kn g)(hp:Kn a)(he:Kn k):
  Kn (fun x v=> Stair.yoke ⟨m x v,0,⟨a x v,0,0⟩,w.ell⟩ (k x v) (g x v)):=by
    convert e.cond_eq (Kn.fix 0) (Kn.fix 0) (reachK w h e.pred hp he) using 1
    ext x v; cases g x v <;> simp only [ite_true,Nat.succ_ne_zero,ite_false] <;> rfl
lemma habG (h:Kn a)(e:Kn f):GK (fun x p=> (f x p).habitat w (greenY (a x p)) (m (a x p)) (Age.g (a x p))
                                             (foreground w (a x p) (f x p).first0)):=by
   have q:= fogK h e
   let t:= e.left.right
   let s:= h.right.left
   let A:= h.right.right.left.left.right.right.left
   let I:= (s.left.sub t.right.right).pred
   let u:=(leG (yokeK w s.left s.right A q.left) I).andG
                        (ltG I (reachK w s.left s.right A q.left))
   let v:=eqG (s.left.sub I.succ) t.right.right
   let V:= wall t.left (A.cond_le q.left ((Kn.fix true).tuple (q.left.sub A))
                                              ((Kn.fix false).tuple (A.sub q.left)))
   let w':= countEat e.right.right ((Kn.fix w.ell).times t.right.right) Print.rad
   convert (fgG w h q e.left.left).andG (u.andG (v.andG (V.andG w'))) using 1
   ext x a; unfold Fog.habitat Stair.layers; simp only [mem_Ico]; rfl
lemma atmosK(h:Kn a)(e:Kn s):GK (fun x p=>atmos w (a x p) (s x p)):=
    let q:= e.left.right
    (wall e (((Kn.fix (2:ℕ)).tuple q).tuple e.right)).andG
       ((ltG q.left (Kn.fix _)).andG ((ltG q.right (Kn.fix _)).andG (habG w h e.right)))
lemma oldKn {q:PT α ℕ}(h:Kn q)(b:Bool):Kn (fun x p=>Seed.old b (q x p)):=
    ((Kn.fix _).tuple (h.tuple (Kn.fix _))).tuple (Kn.fix _)
lemma retireK(h:Kn a)(e:Kn s):GK (fun x p=>retired w (a x p) (s x p)):=
    let q:= e.left.right.left
    let p:= h.right.left
    let m:= (((Kn.fix (cexpo 2 w.p.K)).times (Age.gapK p.left p.right.pred)).times (Kn.fix 4))
    (wall e (oldKn q true)).andG ((notG (eqG p.right (Kn.fix 0))).andG (countEat q m 2))
lemma beganK(h:Kn a)(e:Kn s):GK (fun x p=>began (a x p) (s x p)):=
   let q:=e.left.right.left
   let p:=h.right.right.left
   (wall e (oldKn q false)).andG ((eqG h.right.left.right (Kn.fix 0)).andG
                      ((eqG p.right.left (Kn.fix 0)).andG ((eqG p.left.left (Kn.fix 0)).andG
                                                    (ltG q (Kn.fix 2)))))
lemma cleanK (h:Kn a)(e:Kn s): GK (fun x p=> ace w (a x p) (s x p)):=
   (atmosK w h e).orG ((retireK w h e).orG (beganK h e))
lemma basin : Kn (fun (_:Word)(p:Pan)=> Garden.clean w p) :=
   let h:= (Kn.unpack (α:=Seed)).comp (Kn.next (α:=ℕ))
   decideK ((eqG (Kn.wash.comp h) Kn.next).andG (cleanK w (Kn.unpack.comp Kn.first) h))
end Plot
end Garden
end
end ExactDerandomization.Spring

end

section

namespace ExactDerandomization.Spring
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain
open Cambria Cambria.Wear Garden
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Blade
abbrev Embellish:= Surf× Rus
def bald : Embellish:= default

namespace HullT
variable (r:Rock q w h)

abbrev determine(k:Crt)(b:Bool):ℕ:=if b then greenY k else (params k).2.2.2
def tides (x:Word)(k:Crt)(b:Bool)(p:Rill.History) : Cambria.Hull:=
     ((Aqua.tally r x (stageQ k),(params k).2.1,determine k b),p,dec (Age.env k))
lemma tideK {α}[Wire α]{a:PT α Crt}{v:PT α Bool}{p:PT α Rill.History}
    (h:Kn a)(e:Kn v)(ht:Kn p):Kn (fun x w=>tides r x (a x w) (v x w) (p x w)):=
   let s:=h.right.right.left.left
   let p:=s.right.right
   ((Aqua.tallyK r s.left).tuple (s.right.left.tuple (e.cond p.left p.right))).tuple
                                            (ht.tuple (Kn.unpack.comp h.right.right.right))
end HullT

namespace Crest
abbrev portN (a i:ℕ):Rill.History:=(Was.atom i,a)
abbrev postN:= (Was.atom 0,((1,0):Arch))
def pastC (c:Crt)(i:ℕ):ℕ:= enc (stint c i (Age.g c-1))
def bronze (c:Crt)(h:Hull)(i:ℕ): Embellish:=
     ((h,portN 0 0,(pastC c 4,i),postN),(0,false),Coin.ofZ 0,0,(pastC c 3,i),0)
def newelf(n k:ℕ)(h:Hull)(i:ℕ):Embellish:=
     ((h,portN 0 (i+1),(0,0),postN),(1,true),Aqua.sbase n k,0,(0,0),0)

abbrev launch(k r:ℕ)(s:Scout)(q:Issue):ℕ:= enc (kit k (r,0) s (enc q))
abbrev op (t f x:ℕ):ℕ:= hole t (hole f x)
def ordinary(h:Hull)(b:Bool)(r j:ℕ)(q:Scout)(p:Issue)(c:Coin): Embellish:=
    ((h,portN 0 0,(launch 15 r q p,j),postN),(2,b),c,0,(launch 14 r q p,j),0)
def company(h:Hull)(r _ i j:ℕ)(q Q:Scout)(p:Issue)(c:Coin):Embellish:=
    let x:= Prism.leftE p
    let y:= Prism.rightE p
    let u:= launch 14 r q x
    ((h,(hole (launch 12 r q x) i,op u 0 i),(launch 15 r Q y,j),postN),(2,true),
                                                         c,op u 1 i,(launch 14 r Q y,j),0)
def twins(h: Hull)(r s:ℕ)(q:Scout)(i j M l n:ℕ)(p:Issue)(c:Coin):Embellish:=
    let x:= Prism.swap n M i j p
    ((h,portN 0 (3+(i+M)),(launch 15 r q x,s),(Was.atom (3+j),M,j)),
             (2,true),c,0,(launch 14 r q x,s),if i=0 then 0 else launch 17 r (bitV (detector l 0)) x)

section
variable {α}[Wire α]{a:PT α Crt}{H:PT α Hull}{j n r i l k :PT α ℕ}{p q:PT α Scout}{s:PT α Issue}{c:PT α Coin}
lemma pastK (h:Kn a)(i):Kn (fun x b=>pastC (a x b) i):=
   Kn.wash.comp ((Kn.fix _).tuple ((h.right.left.left.tuple h.right.left.right.pred).tuple h.right.right))
lemma bronzeK (h:Kn a)(he:Kn H)(hk:Kn i):Kn (fun x b=>bronze (a x b) (H x b) (i x b)):=
   (he.tuple ((Kn.fix _).tuple (((pastK h 4).tuple hk).tuple (Kn.fix _)))).tuple
           ((Kn.fix _).tuple ((Kn.fix _).tuple ((Kn.fix _).tuple (((pastK h 3).tuple hk).tuple (Kn.fix _)) )))
lemma opK (h:Kn n)(f:ℕ)(e:Kn i):Kn (fun x b=>op (n x b) f (i x b)):=
   Kn.wash.comp (h.tuple (Kn.wash.comp ((Kn.fix f).tuple e)))
lemma portK (h:Kn i): Kn (fun x b=>portN 0 (i x b)):=
    (Kn.wash.comp ((Kn.fix 0).tuple h)).tuple (Kn.fix 0)
lemma neoK (h:Kn n)(e:Kn k)(hu:Kn H)(hf:Kn i):Kn (fun x b=>newelf (n x b) (k x b) (H x b) (i x b)):=
   (hu.tuple ((portK hf.succ).tuple (Kn.fix _))).tuple ((Kn.fix _).tuple ((Coin.multK (Kn.fix _)
                                     (Aqua.dboxK h e)).tuple (Kn.fix _)))
lemma orbitK (n:ℕ)(h:Kn r)(e:Kn p)(hf:Kn s):Kn (fun x b=>launch n (r x b) (p x b) (s x b)):=
     Kn.wash.comp ((Kn.fix n).tuple ((h.tuple (Kn.fix 0)).tuple (e.tuple (Kn.wash.comp hf))))
lemma ordinaryK (h:Kn r)(e:Kn p)(hf:Kn s)(hg:Kn j)(hs:Kn H)(hx:Kn c)(b:Bool):
   Kn (fun x a=>ordinary (H x a) b (r x a) (j x a) (p x a) (s x a) (c x a)):=
    (hs.tuple ((Kn.fix _).tuple (((orbitK 15 h e hf).tuple hg).tuple (Kn.fix _)))).tuple
                 ((Kn.fix _).tuple (hx.tuple ((Kn.fix _).tuple (((orbitK 14 h e hf).tuple hg).tuple (Kn.fix _)))))
lemma companyK (h:Kn r)(e:Kn p)(hw:Kn q)(hf:Kn s)(hg:Kn j)(ht:Kn i)(hs:Kn H)(hx:Kn c)(_:Kn k):
   Kn (fun x a=>company (H x a) (r x a) (k x a) (i x a) (j x a) (p x a) (q x a) (s x a) (c x a)):=
    let L:=hf.left.tuple (hf.right.right.tuple hf.right.left)
    let R:= hf.right.right.tuple (hf.right.left.tuple hf.left)
    let t:= orbitK 14 h e L
    let u:= orbitK 14 h hw R
    (hs.tuple (((Kn.wash.comp ((orbitK 12 h e L).tuple ht)).tuple (opK t 0 ht)).tuple
                    (((orbitK 15 h hw R).tuple hg).tuple (Kn.fix _)))).tuple
            ((Kn.fix _).tuple (hx.tuple ((opK t 1 ht).tuple ((u.tuple hg).tuple (Kn.fix _)))))
lemma twinK(h:Kn H)(he:Kn r)(hw:Kn k)(hx:Kn p)(hf:Kn i)(ht:Kn j)(M:ℕ)(hu:Kn l)
       (hm:Kn n)(hD:Kn s)(hc:Kn c):
   Kn (fun x a=>twins (H x a) (r x a) (k x a) (p x a) (i x a) (j x a) M (l x a) (n x a) (s x a) (c x a)):=by
   have hg:=Prism.swapK hm hf ht hD M
   have hi:=portK ((Kn.fix 3).add (hf.add (Kn.fix M)))
   have hy:=orbitK 15 he hx hg; have hW:=orbitK 14 he hx hg
   have hq:= (Kn.wash.comp ((Kn.fix (0:ℕ)).tuple ((Kn.fix 3).add ht))).tuple ((Kn.fix M).tuple ht)
   have hC:Kn (fun x a=> bitV (detector (l x a) 0)):= (hu.tuple (hu.tuple (Kn.fix _))).tuple  (Kn.fix ((6,0,false):ChoiceX))
   exact (h.tuple (hi.tuple ((hy.tuple hw).tuple hq))).tuple
            ((Kn.fix _).tuple (hc.tuple ((Kn.fix _).tuple ((hW.tuple hw).tuple
                                   (hf.cond_eq (Kn.fix 0) (Kn.fix 0) (orbitK 17 he hC hg))))))
end
end Crest

namespace RowD
open Crest
variable (w:Wares)

def foreC (p:Crt): Scout:=
    let q:=fence p
    (q.1,q.2.1,q.2.2.1,false)
def school(p:Crt)(k:ℕ)(b:Bool):Scout:= ((stageQ p,(if b then stageQ p else (params p).2.1),k,max (greenY p) k),0,0,true)
def hinge (p:Crt)(u:ℕ):Scout:=
    let k:=stageQ p
    ((k,(params p).2.1,k,u),if origin p=2∨origin p=4 then 2 else 3,(countO w p)-1,true)
def coral (p:Crt)(k j:ℕ):Scout:=((stageQ p-1,(params p).2.1,k,max (greenY p) k),1,j,true)

variable {q w0 h:ℕ}(r:Rock q w0 h)
abbrev n:=r.n
def dock(x:Word)(c:Crt)(s:Fog):Hull:= HullT.tides r x c s.first0 (s.tick r.w,s.event)
abbrev skies(x:Word)(c:Crt)(s:Fog):Issue:=
    Print.stepout (r.n x) (params c).2.1 (HullT.determine c s.first0) (s.tick r.w) s.event (dec (Age.env c))
def startF(x:Word)(_:Crt)(s:Fog):Coin:=
    let t:=WindY.shower r x (s.tick r.w)
    if s.2.1 then t else Coin.neg t
def scaleB (x:Word)(c:Crt)(s:Fog):Coin:= Coin.mult (startF r x c s)
                         (Aqua.quo (r.n x) (greenY c) ((s.ray (greenY c)).1))

def pickA(x:Word)(c:Crt)(s:Seed):Embellish:=
    let f:=s.fog
    let u:= dock r x c f
    let k:=f.ray (greenY c)
    let p:=f.budget (m c)
    let y:= skies r x c f
    let h:= scaleB r x c f
    if f.first0 then
      if origin c=0 then
         let M:=r.w.p.M
         if s.x=0 then twins u p s.y (coral c k.1 (k.2%M)) (k.2/M) (k.2%M) M (stageQ c-1) (r.n x) y h else bald
      else if k.2=0 then
         if s.x=0 then ordinary u true p s.y (school c k.1 false) y h else bald
      else if k.2=1 then
         Crest.company u p k.1 s.x s.y (hinge r.w c (stageQ c)) (school c k.1 true)
                                      y (Coin.mult h (Aqua.rawcoins (r.n x) (stageQ c)))
      else if s.x=0 then
              ordinary u true p s.y (hinge r.w c (max (greenY c) (stageQ c))) y (Coin.neg h)
           else bald
    else if s.x=0 then ordinary u false p s.y (foreC c) y (Coin.mult (startF r x c f) Aqua.zet) else bald

section
variable {α}[Wire α]{b:PT α Crt}{f:PT α Fog}{p:PT α Seed}{j i n:PT α ℕ}
lemma chartK(h:Kn b)(e:Kn f):(Kn (fun x a=>dock r x (b x a) (f x a))) :=
    HullT.tideK r h e.left.left ((((Kn.fix r.w.ell).times e.left.right.right.right)).tuple e.right.right)
lemma skiesK(h:Kn b)(e:Kn f):Kn (fun x a=>skies r x (b x a) (f x a)) :=
   let k:=h.right.right.left.left.right
   Print.stepK r.nKn k.left (e.left.left.cond k.right.left k.right.right)
       ((Kn.fix _).times e.left.right.right.right) e.right.right (Kn.unpack.comp h.right.right.right)
lemma startK(_:Kn b)(e:Kn f):Kn (fun x a=> startF r x (b x a) (f x a)) :=
   let k:=WindY.showerK r ((Kn.fix _).times e.left.right.right.right)
   e.right.left.cond k (Coin.negK k)
lemma scaleBK (h:Kn b)(e:Kn f):Kn (fun x a=> scaleB r x (b x a) (f x a)) :=
   Coin.multK (startK r h e) (Aqua.quoK r.nKn h.right.right.left.left.right.right.left
                                                           (Garden.Plot.fogK h e).left)
lemma cal (h:Kn b):Kn (fun x a=> foreC (b x a)):=
   let e:= h.right.right.left
   e.left.tuple (e.right.left.tuple (e.right.right.left.tuple (Kn.fix false)))
lemma skol (h:Kn b)(hp:Kn i)(g:Bool):Kn (fun x a=>school (b x a) (i x a) g):=by
   have he:=h.right.right.left.left
   have hf:=hp.tuple (Aqua.largeK he.right.right.left hp)
   cases g
   · exact (he.left.tuple (he.right.left.tuple hf)).tuple (Kn.fix _)
   exact (he.left.tuple (he.left.tuple hf)).tuple (Kn.fix _)
lemma canK (h:Kn b)(hp:Kn i): Kn (fun x a=> hinge w (b x a) (i x a)):=by
   have he:=h.right.right.left
   have hg:= he.left.left
   have hf:= he.right.left
   have hz:= (hf.cond_eq (Kn.fix 1) (Kn.fix w.p.T) he.right.right.left).pred
   have hk:Kn (fun x a=> (hinge w (b x a) (i x a)).2.1):=by
       convert hf.cond_eq (Kn.fix 2) (Kn.fix (α:=α) (2:ℕ))
                              (hf.cond_eq (Kn.fix 4) (Kn.fix (2:ℕ)) (Kn.fix (3:ℕ))) using 1
       ext x a; unfold hinge; grind
   exact (hg.tuple (he.left.right.left.tuple (hg.tuple hp))).tuple (hk.tuple (hz.tuple (Kn.fix true)))
lemma coalK (h:Kn b)(he:Kn i)(hp:Kn j): Kn (fun x a=> coral (b x a) (i x a) (j x a)) :=
   let u:=h.right.right.left.left
   (u.left.pred.tuple (u.right.left.tuple (he.tuple (Aqua.largeK u.right.right.left he)))).tuple
                              ((Kn.fix 1).tuple (hp.tuple (Kn.fix _)))
lemma pollen (h:Kn b)(e:Kn p):Kn (fun x a=> pickA r x (b x a) (p x a)):= by
   have hf:= e.right
   have hp:=h.right.right.left.left
   have ht:=hp.left; have hz:=hf.left.left
   have hh:=e.left.right
   have hJ:=chartK r h hf
   have hv:= h.right.left.left.sub hf.left.right.right.right
   have hW:=hf.right.left.cond hv.pred.succ hv.pred
   have he:= Garden.Plot.fogK h hf
   have hs:= skiesK r h hf
   have hN:= scaleBK r h hf
   let n:=r.nKn (α:=α)
   let M:= Kn.fix (α:=α) r.w.p.M
   let z(f:PT α Embellish)(hp:Kn f):= hh.left.cond_eq (Kn.fix 0) hp (Kn.fix bald)
   exact hz.cond
       (h.right.right.left.right.left.cond_eq (Kn.fix 0)
            (z _ (Crest.twinK hJ hW hh.right (coalK h he.left (he.right.mod M))
                             (he.right.div M) (he.right.mod M) r.w.p.M ht.pred n hs hN))
            (he.right.cond_eq (Kn.fix 0)
               (z _ (Crest.ordinaryK hW (skol h he.left false) hs hh.right hJ hN true))
            (he.right.cond_eq (Kn.fix 1) (Crest.companyK hW (canK r.w h ht) (skol h he.left true) hs
               hh.right hh.left hJ (Coin.multK hN (Aqua.rawK n ht)) he.left)
               (z _ (Crest.ordinaryK hW (canK r.w h (Aqua.largeK hp.right.right.left ht)) hs hh.right hJ (Coin.negK hN) true)))))
       (z _ (Crest.ordinaryK hW (cal h) hs hh.right hJ (Coin.multK (startK r h hf) (Kn.fix _)) false))
end

end RowD
end Blade
end
end ExactDerandomization.Spring

end

section

namespace ExactDerandomization.Spring
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain
open Cambria Cambria.Wear Garden Blade Cambria.BadgeX Terrain
noncomputable section
open scoped Classical
variable {q w h:ℕ}

namespace Lily
variable (r:Rock q w h)
abbrev defaultH (x:Word)(c:Crt):Hull:= HullT.tides r x c true (0,0)
def recruit (x:Word)(s: Garden.Lead):Embellish:=
   let w:= s.1
   let p:=s.2
   let h:=defaultH r x w
   if p.1.1=0 then Crest.bronze w h p.x
   else if p.1.1=1 then Crest.newelf (r.n x) (greenY w) h p.x
   else RowD.pickA r x w p

def arms (x:Word)(p:Pan):Embellish:=
   if Garden.clean r.w p then recruit r x (dec p.1,dec p.2) else bald
def wraps (x:Word)(p:Pan):GridY:=(p.1,arms r x p)
def pose0 (x:Word)(a:Mold.Croft):Aide:=
    (arms r x (pointer a.1 1,a.2.1)).1.priceC a.2.2
lemma armsK:Kn (arms r) := by
   have h:= Kn.first (α:=ℕ) (β:=ℕ); have e:= Kn.next (α:=ℕ) (β:=ℕ)
   have hs:=(Kn.unpack (α:=Crt)).comp h
   have he:=(Kn.unpack (α:=Seed)).comp e
   have hf:=HullT.tideK r hs (Kn.fix true) (Kn.fix ((0,0):Rill.History))
   have hp:=he.left.left; have hz:=he.left.right.left
   exact (Garden.Plot.basin _).cond
             (hp.cond_eq (Kn.fix 0) (Crest.bronzeK hs hf hz)
                         (hp.cond_eq (Kn.fix 1) (Crest.neoK r.nKn hs.right.right.left.left.right.right.left hf hz)
                               (RowD.pollen r hs he))) (Kn.fix _)
attribute [local irreducible] arms RowD.pickA
def poseX:Pose:= by
   have he:= (Kn.first (α:=ℕ) (β:=Rill.History))
   let k:= Kn.wash.comp ((Kn.fix (1:ℕ)).tuple (((Kn.unpack (α:=Crt)).comp he).right))
   have h:= armsK r
   exact ⟨_,Surf.Prep.aideK (h.comp (k.tuple Kn.next.left)).left Kn.next.right⟩
set_option maxHeartbeats 200000 in
lemma goalF (x a): (poseX r).f x a=pose0 r x a:=rfl

def bay (x:Word)(a:ℕ):ℕ:=
   let p:= Reed.V x a
   enc (wraps r x (p.1,p.2.1))
lemma bayK:Kn (bay r):=
   Kn.wash.comp ((Kn.first.tuple (armsK r)).comp (Reed.VK.left.tuple Reed.VK.right.left))
abbrev liftq (r:Rock q w h) := Fret.Seats.transformed (Cub.mk (bay r) (bayK r))
def foreP (v: Tags)(p:MintV)(base:Cog) : ℕ → Cog
  | 1=> liftq r (grainq p (Wear.shelf (knob r v)) r (schedule r v) true)
  | 2=> liftq r (grainq p (Wear.shelf (knob r v)) r (schedule r v) false)
  | 5=>base
  | _=> liftq r ((hub r).garden (schedule r v))
private lemma foreP_choice (v:Tags) (p:MintV) (base:Cog) (b:Bool):
    foreP r v p base (if b then 1 else 2) =
      liftq r (grainq p (Wear.shelf (knob r v)) r (schedule r v) b) := by
    cases b <;> rfl

abbrev prog (v:Tags)(p:MintV)(base:Cog) := Studio.arrange (foreP r v p base) 5
attribute [local irreducible] bay Lily.poseX
attribute [local irreducible] Lily.recruit Arena.Gate.garden Wear.coast

namespace Service
open Cambria.Rime Rime.Nest Rime.Nest.Good
open Fret.Seats
variable {u:Line (q:=q) (w:=w) (h:=h)} {p:MintV}
structure Fits (s:Nest u) (v:Fabric u) (i j:ℕ) :Prop where
    good:s.Good
    cageX:s.ray.cage=(v.α s.t i)
    book : wraps u.r u.x (s.ray.src,j)=(s.a,s.ray.t,s.diploma)
    yarn : u.s.pave=poseX u.r
namespace Fits
set_option maxHeartbeats 200000
variable {s:Nest u}{v:Fabric u}{i j}(h0:Fits s v i j)
include h0
lemma stow : bay u.r u.x ((Studio.stk u s.a s.ray.x j).info)=s.v:= by
   unfold bay Studio.stk Reed.film info panelx Reed.V
   dsimp only; rw [dec_round]
   rw [h0.good.scores]
   exact congrArg enc h0.book
lemma traced0 : (arms u.r u.x (s.a,j)).1=s.ray.t:=by
    have he:= congrArg (fun a:GridY=>a.2.1) h0.book
    exact he

abbrev prS (s:Nest u)(j:ℕ):Seats:=Studio.stk u s.a s.ray.x j
lemma cupF {qB t c a b}(h:s.home.hear t c qB a b):(prS s j).hear t c (liftq u.r qB) a b:=by
   have hu:(panelx (prS s j) s.v).hear t c qB a b:=h
   apply importD (s:=prS s j) ⟨_,bayK u.r⟩ _ hu
   exact h0.stow
lemma cupG {qB t c a b}(h:s.home.band c t a qB b):(prS s j).band c t a (liftq u.r qB) b:=by
    have hu:(panelx (prS s j) s.v).band c t a qB b:=h
    apply transportD (s:=prS s j) ⟨_,bayK u.r⟩ _ hu
    exact h0.stow
lemma engrave(k): offer u.s.pave u.x (stem s.ray.cage.visN j k)=s.ray.t.priceC k:=by
    have hs:s.ray.cage.visN=v.c 2 i:= congrArg CageQ.visN h0.cageX
    have he:(uphold s.ray.cage.visN).1=2:=by rw [hs,Stone.roleR]
    unfold offer; rw [ite_eq_left (show (uphold s.ray.cage.visN).1=2 from he),h0.yarn,goalF]; unfold pose0
    have hf:pointer s.ray.cage.visN 1=s.a:=by
      rw [hs,Stone.pointing]
      exact congrArg CageQ.dataN h0.cageX |>.symm
    simp only []

    rw [hf]
    rw [h0.traced0]

lemma supplies (base) (hr:Studio.Parcel u s.a (Lily.prog u.r u.v s.t base))(hv:u.smallQ s.a j):
   u.D.swears (post s.a 0 j 0) s.ray.x (title s):=by
    let S:= Studio.stk u s.a s.ray.x j
    have hx:S.rite (C0 s) (foreP u.r u.v s.t base 0) (title s):= by
       have he:=h0.cupF (qB:=(hub u.r).garden u.D.s) h0.good.home0
       rw [foreP] <;> first| exact he | decide
    have hs:=Era.billed u.r
    have ht := (Wear.Paper.eras s.t u.r u.D.s (krod u) true (title s)).1
    exact Studio.echoTicket h0.good.primary (by omega: (0:ℕ) ≤ 5) (by omega) hv
                 (le_trans (le_trans (by omega) hs.1) ht) h0.good.large0 hx hr
lemma portraits(base) (hr:Studio.Parcel u s.a (Lily.prog u.r u.v s.t base))(hv:u.smallQ s.a j):
    u.eye.Flora u.torch.p s.ray.cage.visN j s.ray.x s.ray.outR:= by
    apply h0.good.grip.paths hv _ (h0.engrave _)
    rw [show s.ray.cage.tagop=0 from congrArg CageQ.tagop h0.cageX]
    exact h0.supplies base hr hv
private lemma beams_band (base) (b:Bool) (X:ℝ) (hx:gross s b X):
    (Studio.stk u s.a s.ray.x j).band (C0 s) s.H s.t.inputH
      (foreP u.r u.v s.t base (if b then 1 else 2)) X:=by
    have hs : u.D.s = schedule u.r u.v := rfl
    rw [foreP_choice, ← hs]
    exact h0.cupG (qB:=grainq s.t (krod u) u.r u.D.s b) hx

lemma beams (base) (hr:Studio.Parcel u s.a (Lily.prog u.r u.v s.t base))(hv:u.smallQ s.a j)
     (b:Bool)(X:ℝ)(hx:gross s b X):
   u.D.Voice s.a s.ray.x (hole (if b then 1 else 2) j) (u.D.high s.a) (s.t.inputH*u.D.D s.a) X:=by
    let S:= Studio.stk u s.a s.ray.x j
    let k:= if b then 1 else 2
    have hx': S.band (C0 s) s.H s.t.inputH (foreP u.r u.v s.t base k) X:=
      h0.beams_band base b X hx
    have hs:=Era.billed u.r
    have ht := (Wear.Paper.eras s.t u.r u.D.s (krod u) b (title s)).1
    have he:k ≤ 5:=by unfold k; split<;>omega
    exact Studio.scoreTicket (u := u) (a := s.a) (x := s.ray.x) (i := j) (j := s.t.inputH)
      (c := C0 s) (o := k) (m := 5) (H := s.H) (f := foreP u.r u.v s.t base)
      h0.good.primary he (by omega) hv
      (le_trans (le_trans (by omega) hs.1) ht) h0.good.large0 le_rfl hx' hr
end Fits
end Service
end Lily
end
end ExactDerandomization.Spring

end

section

namespace ExactDerandomization.Spring
open Analysis Hie Counter Relay Rill Fret Grain Net Est At Buf Stage Finset
open Chime Scheme Dome Cone.ConeX _root_.OAI.ExactDerandomization.Sub Swirl
open Helix Helix.Age Helix.Mold Helix.Orbit Helix.Foil Helix.Moon Helix.Torch
open SiteX SiteX.Line Glass Glass.Rod Rain
open Cambria Cambria.Wear Garden Blade Terrain Terrain.Bank BadgeX
noncomputable section
open scoped Classical
variable {q w h:ℕ} {u:Line (q:=q) (w:=w) (h:=h)}
namespace Fen
variable (w:Wares)
lemma Kpos:0<w.p.K:=by
   have hs:=w.p.KOK
   have hx:0 < (w.p.T+1:ℝ)/eta delta:=by unfold eta delta Hie.A; positivity
   by_contra! hn; rw [Nat.eq_zero_of_le_zero hn] at hs; push_cast at hs; nlinarith

variable (v:Fabric u)
abbrev owner(a:Fabric u)(i:ℕ):Crt:=kit 1 (a.m,i) (bitR a.t) (enc (Print.issued a.dye))
lemma heir (i):enc (owner v i)=v.c 1 i:=rfl
lemma therein (i): (dec (v.c 1 i) : Crt)=owner v i:=by rw [← heir,Wire.eq]
abbrev year(a:Fabric u): Est.Stair:=a.t.stair u.plotM a.m
abbrev ashes (a:Fabric u)(b:Bool):Est.Flame u.n:=
                      if b then a.t.start u.plotM a.roll a.m else a.t.companion u.plotM a.roll
abbrev gridR (a:Fabric u)(b:Bool): Axis:=
    if b then a.t.plan u.plotM else (a.t.plan u.plotM).narrowed a.t.t
lemma force (b:Bool)(j:ℕ):foreground u.w0 (owner v j) b=(ashes v b).rays :=by
    let a:=v.t
    cases b
    · change (if a.main=true∧(shaped a.tag).1≠4 then {(a.a,0)} else ∅)= (if a.two then {(a.a,0)} else ∅)
      unfold Quest.two
      cases he:a.tag <;> simp [Kind.paired, shaped]
      next b i=> cases b <;> simp
    change _= (a.start u.plotM v.roll v.m).rays
    unfold Quest.start
    let r:=owner v j
    have hp: origin r=(shaped a.tag).1:=rfl
    have hh: greenY r=a.a:=rfl
    have ht: Garden.stageQ r=a.i:=rfl
    have hn:m r=v.m:=rfl
    have hW:(fence r).2.2.1=(shaped a.tag).2:=rfl
    change foreground u.w0 r true=_
    unfold foreground countO asker
    rw [hp,hh,ht,hn,hW]
    cases hq:a.tag
    · cases he:a.i with
      | zero=> simp [shaped]
      | succ i=> simp only [Quest.agency,Quest.fleet,Quest.tray,shaped, Nat.add_sub_cancel,
                         ite_true, ite_eq_right (by omega:i+1≠0)]
                 rfl
    · simp [shaped,Quest.pipe,Quest.company,Quest.tray]; rfl
    · next b k=> cases b <;> simp [shaped,Quest.pipe,Quest.company,Quest.tray] <;> rfl
    simp [shaped,Quest.pipe,Quest.company,Quest.tray]; rfl
lemma fuel (_:ℕ)(z:Cambria.Hull):z.1=z.1:=rfl
lemma quietox {i _ j _ _:ℕ}{_:Fog}(h:retired u.w0 (owner v i) (Seed.old true j)):
   Age.g (owner v i) ≠0∧ j < capacity 2 u.w0.p.K (Age.L v.m) (i-1):=
           ⟨h.2.1,h.2.2⟩

namespace GardenV
lemma oldcap {w:Wares} {d i:ℕ}(hd:0<d)(b:Bool)(hp:lb (enc i)  ≤  passport w*d):
   Pass.sized (Seed.old b i) (Pass.reserve w) d:= by
   let c:=passport w; have hc:50 ≤ c:=by unfold c passport; omega
   have ht (b:Bool) : Pass.sized b c d:=Pass.boo b _ _ (by omega) hd
   have he(a:ℕ)(h:a ≤ 1):Pass.sized a c d:=by
       apply Pass.left _ _ _ (Pass.little _ d hd)
       omega
   let p:Fog:= ((false,(true,0),0,0),false,0)
   have hP: Pass.sized p (4*(4*(4*(4*c)))) d:=by
     have h1:Pass.sized ((true,(0:ℕ)): Rain.Crack) (4*c) d:=Pass.pair hd (by omega) (ht _) (he 0 (by omega))
     have h2:Pass.sized (((0:ℕ),0):Rill.History) (4*c) d:=Pass.pair hd (by omega) (he 0 (by omega)) (he 0 (by omega))
     have h3:= Pass.pair hd (by omega) h1 h2
     have h5:= Pass.pair hd (by omega) (ht false) (he 0 (by omega))
     exact Pass.pair hd (by omega) (Pass.pair hd (by omega) (Pass.left Bool.false _ _ (ht Bool.false) _ (by omega)) h3)
                             (Pass.left _ _ _ h5 _ (by omega))
   have h1 := Pass.pair hd (by omega:2 ≤ c) (show Pass.sized i c d from hp) (he 0 (by omega))
   let k:ℕ:=if b then 0 else 1
   have h3:k  ≤  1:=by unfold k; split<;>omega
   have h2:=Pass.pair hd (by omega)
                        (Pass.left k _ _ (he k h3) (4*c) (by omega)) h1
   exact Pass.left _ _ _ (Pass.pair hd (by omega) (Pass.left _ _ _ h2 _ (by omega)) hP) _
                           (by unfold Pass.reserve; change _ ≤ _*c; omega)
lemma forestLen {w:Wares}{a:Crt}{b:Bool}{r:Ray}(h:r∈foreground w a b):
    r.2  ≤  w.p.M^2+2*w.p.M+2:=by
    unfold foreground at h
    split at h
    · split at h
      · split at h
        · simp only [notMem_empty] at h
        have ht:= mem_range.1 (mem_product.mp h).2; nlinarith
      simp only [mem_union,mem_product,mem_range] at h; grind
    split at h
    · simp only [mem_singleton] at h; rw [h]; dsimp only; omega
    simp only [notMem_empty] at h

set_option maxRecDepth 6000 in
lemma windowN {i:ℕ}(hi:i<Age.L v.m){p:MintV}(he:Green u.r p){s:Seed}(hg:ace u.w0 (owner v i) s):
   enc s < p.rangeN (gap v.m i):=by
   let d:=gap v.m i; let c:=owner v i
   have hd:1  ≤  d:=gap_pos ..
   apply lt_of_lt_of_le (below _) (Nat.pow_le_pow_right (by omega) ?_)
   change lb _ ≤ p.vol*d
   apply le_trans _ (Nat.mul_le_mul_right d ((le_trans (show Pass.reserve u.r.w ≤ 4+Pass.reserve u.r.w by omega) he.power)))
   change Pass.sized s _ d
   rcases hg with h|h|h
   · have hc:s=Seed.along s.2 s.x s.y:=h.1
     exact Eq.mp (congrArg (fun q=>Pass.sized q (Pass.reserve u.w0) d) hc.symm)
          (Pass.lengthC u.w0 (s:=year v) rfl hi (fun q _=>forestLen ‹_›)
                       h.2.2.2 h.2.1.le h.2.2.1.le)
   · obtain ⟨hc,hj,hq⟩:=h
     apply Eq.mp (congrArg (fun q=>Pass.sized q (Pass.reserve u.w0) d) hc.symm) (oldcap (w:=u.w0) (i:=s.x) hd true ?_)
     have hk : (i-1)+1=i:=by change i≠0 at hj; omega
     change s.x < capacity 2 u.w0.p.K (Age.L v.m) _ at hq
     rw [Green.capacityE] at hq
     have hu:gap v.m (Age.g (owner v i)-1)=2*d:=by
        apply Eq.trans (gap_step (i:=i-1) (by omega)) _
        rw [hk]
     rw [hu] at hq
     apply le_trans (modest hq (by unfold CarryE cexpo fexpo; nlinarith))
     have ht:2*CarryE u.w0 ≤ passport u.w0:=by unfold passport; omega
     nlinarith
   obtain ⟨hc,-,-,-,hj⟩:=h
   apply Eq.mp (congrArg (fun q=>Pass.sized q (Pass.reserve u.w0) d) hc.symm) (oldcap (w:=u.w0) (i:=s.x) hd false ?_)
   have hn:= lb_le_inc s.x
   change lb s.x ≤ _
   have hp:10 ≤ passport u.w0:=by unfold passport;omega
   nlinarith
end GardenV

open Census
abbrev R:=Census.Arc
abbrev area(v:Fabric u)(b:Bool)(i:ℕ):Finset Arc:= tracks (year v) (ashes v b).rays i
def chenille (b:Bool)(z:Arc×ℕ×ℕ):Seed:= Seed.along (drops (year v) b z.1) z.2.1 z.2.2
def fanD (i:ℕ)(b:Bool):Finset (Arc×ℕ×ℕ):= area v b i ×ˢ ((range v.Rslots)×ˢ(range v.Rslots))

lemma sauna {b:Bool}{i:ℕ}{z:Arc×ℕ×ℕ}(hz:z∈fanD v i b):
    atmos u.w0 (owner v i) (chenille v b z):=by
    obtain ⟨hx,hb,hc⟩:= show z.1∈area v b i∧ z.2.1< u.w0.p.K ∧ z.2.2<u.w0.p.K from by simpa [fanD] using hz
    have hp : (chenille v b z).fog.first0=b:=rfl
    refine ⟨rfl,hb,hc,?_⟩
    rw [hp,Fen.force]
    exact (grange (year v) rfl b hx).1
lemma skyfell {s:Seed}{i:ℕ}(b:Bool) :
   s∈ (fanD v i b).image (chenille v b) ↔ atmos u.w0 (owner v i) s∧ s.fog.first0=b:=by
    constructor
    · intro h; obtain ⟨v,h1,rfl⟩:=mem_image.1 h
      exact ⟨sauna _ h1,rfl⟩
    rintro ⟨h,rfl⟩
    let a:=greenY (owner v i)
    let M:=m (owner v i)
    let t:=s.fog
    let r:Arc:=(t.ray a,t.slackM M,t.2)
    let w:Arc×ℕ×ℕ:=(r,s.x,s.y)
    obtain ⟨he,hh,hc,hp⟩:=h
    rw [Fen.force] at hp
    have hg : t.habitat u.w0 (year v).key.a (year v).M i (ashes v t.first0).rays:=hp
    obtain ⟨hx,hA,hW⟩:= Fog.totally rfl hg
    have hf:r∈area v t.first0 i:=by
         refine (pat ..).2 ⟨hx,hA,?_⟩
         have he:t.event<Print.rad^(u.w0.ell*t.sig):= hg.2.2.2.2
         change t.event<Print.rad^(u.w0.ell*_); change _^ (u.w0.ell * t.sig)>t.event at he
         have hk : (year v).slack r.2.1=t.sig:=hp.2.2.1
         rwa [hk]
    refine mem_image.2 ⟨w,mem_product.2 ⟨hf,mem_product.2 ⟨mem_range.2 hh,mem_range.2 hc⟩⟩,?_⟩
    change Seed.along _ _ _=s
    rw [show drops (year v) s.fog.first0 w.1=t from hW]; exact he.symm
lemma meadow (b:Bool)(i:ℕ):Set.InjOn (chenille v b) ↑(fanD v i b):=by
    intro x hx y hy he
    obtain ⟨hf,hv,hq⟩:=Seed.along_inj.1 he
    exact Prod.ext ((disjoint0 (w:=u.w0) (year v) rfl b _ i) (mem_product.1 hx).1 (mem_product.1 hy).1 hf) (Prod.ext hv hq)
end Fen

end
end ExactDerandomization.Spring

end

end OAI
