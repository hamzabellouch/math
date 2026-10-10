import OAI.Computability.Logspace.DyadicArithmetic

namespace OAI

/-!
Bounded query programs with explicit scratch space and finite-margin guarantees.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! cost calculus for prefix recipes. -/
namespace ExactDerandomization.Fret
open Relay Counter Rill Analysis Finset
abbrev unitB (d:ℕ):ℝ:=(2:ℝ)^d
abbrev massB (r d:ℕ):ℝ:= (2:ℝ)^(r*d)
lemma unit1 (d):1 ≤ unitB d:=one_le_pow₀ (by norm_num)
lemma mass1(r d):1 ≤ massB r d:= unit1 _
lemma mass0(r d):0< massB r d:= by unfold massB; positivity
lemma swellB {c d:ℕ}(h:1 ≤ d) : (c:ℝ)< massB c d:= by
    have h1: c<2^c:=by have he:=growing c; omega
    have hh:= lt_of_lt_of_le h1
            (Nat.pow_le_pow_right Nat.zero_lt_two (show c  ≤  c*d by nlinarith))
    unfold massB; exact_mod_cast hh
lemma mass_mul (r k d):massB (r+k) d=massB r d*massB k d:=by unfold massB; rw [add_mul,pow_add]
lemma mass_mono {r k:ℕ}(h:r ≤ k)(d:ℕ):massB r d ≤ massB k d:=by
    unfold massB; gcongr ;norm_num

structure Knob where
    height:Cub ℕ ℕ
    bank:Cub ℕ ℕ
    store:Cub ℕ ℕ

def Align (p:Port)(k:Knob) := p.OK ∧ k.height.f p.l.x p.info=p.d ∧ k.bank.f p.l.x p.info=2^p.d
def Live (p:Port)(k:Knob)(T:ℕ) := 2^T  ≤  k.store.f p.l.x p.info

def Ears (p:Port)(c T i:ℕ)(f:Cog)(v:ℝ) :=
   p.Tells f c T (v / massB i p.d)
lemma amplitude {p:Port} {c T i f v}(h:Ears p c T i f v): |v| ≤  massB i p.d:= by
    obtain ⟨w,h,-⟩:=h
    obtain ⟨hb,-⟩:=h
    rw [abs_div,abs_of_pos (mass0 ..),div_le_one (mass0 ..)] at hb
    exact hb
lemma fewer {p:Port}{f c H w F}(h:p.Feeds f c H w F){D T}(he:1 ≤ c)(hk:c  ≤ D)(hv:T ≤  H):
    p.Feeds f D T w F :=
   ⟨⟨h.1.1,fun t hi=>h.1.2 t (hi.trans hv)⟩,
       ⟨fun t hi=>(h.2.digits t (hi.trans hv)).mono hk he⟩⟩
lemma supply {p:Port}{f c T i v}(h:Ears p c T i f v){D H}(he:1 ≤ c)(hk:c ≤ D)(hp:H  ≤  T):
    Ears p D H i f v:=by
    obtain ⟨w,h⟩:=h
    exact ⟨w,fewer h he hk hp⟩

def amount (p:Knob)(i:ℕ) (x:Word)(v:ℕ):ℕ:=(p.bank.f x v)^i
lemma amountK (p:Knob)(i): Kn (amount p i):= Kn.power _ p.bank.runs
lemma counted {p:Port}{k}(h:Align p k)(i):
    (amount k i p.l.x p.info:ℝ)=massB i p.d:=by
    rw [amount,h.2.2,massB,Nat.mul_comm,pow_mul]; push_cast; rfl
def scaleC (k:Knob)(i:ℕ) (x:Word)(v:ℕ):Coin:=Coin.ofZ (amount k i x v)
lemma scaleK(k i): Kn (scaleC k i):=Coin.ofK (amountK k i).ZofN
lemma scalen {p:Port}{k}(h:Align p k)(i):(scaleC k i p.l.x p.info).v=massB i p.d:=by
    rw [scaleC,Coin.ofv]; push_cast; exact counted h i

structure Bid where
    gate:Coin×Coin → Coin
    gn:Kn (fun (_:Word) a=>gate a)
    truef:ℝ → ℝ → ℝ

namespace Bid

variable (p:Bid)
abbrev arm := ℕ×Coin×Coin
def remote (s:Knob)(i j o:ℕ)(x:Word)(a:arm):Coin :=
   let A:=Coin.mult a.2.1 (scaleC s i x a.1)
   let B:=Coin.mult a.2.2 (scaleC s j x a.1)
   Coin.mult (p.gate (A,B)) (Coin.inv (scaleC s o x a.1))
lemma remoteK (s i j o) : Kn (p.remote s i j o):= by
    have hp:Kn (fun (_:Word)(a:arm)=>a.1):=Kn.first
    have ha:=Coin.multK Kn.next.left ((scaleK s i).comp hp)
    have hb:=Coin.multK Kn.next.right ((scaleK s j).comp hp)
    exact Coin.multK (p.gn.comp (ha.tuple hb)) (Coin.invK ((scaleK s o).comp hp))

structure Fit (e i j:ℕ) : Prop where
   goodC:∀ a b,(p.gate (a,b)).v=p.truef a.v b.v
   sturdy:∀ {d:ℕ},1 ≤ d  →  ∀ {x y z w:ℝ},
        |x| ≤ 2*massB i d  →  |y| ≤  2*massB j d  →  |z| ≤ 2*massB i d  →  |w| ≤ 2*massB j d  →
             |p.truef x y-p.truef z w|  ≤  massB e d*(|x-z|+|y-w|)

def uPair (p:Bid)(k:Knob)(i j o e:ℕ)(f g:Cog):Meld :=
   let M:=e+i+j+6
   { P:={ n:=fun _=>⟨_,Kn.fix 1⟩, route:=fun _=>⟨_,Kn.first⟩,
          margin:=⟨fun x a=>M*k.height.f x a, (Kn.fix _).times k.height.runs⟩,
          scans:=fun b=> if b then f else g }
     f:=⟨_,p.remoteK k i j o⟩ }

lemma behold {x y:ℝ}{d :ℕ}(s:0< d) (e i j o:ℕ) (u:p.Fit e i j)
    (he:|x| ≤ massB i d)(ht:|y| ≤ massB j d)
    {a b:ℝ}(hi:|a-x/massB i d| ≤ 1)(hk:|b-y/massB j d| ≤ 1):
       |p.truef (a*massB i d) (b*massB j d)/massB o d - p.truef x y/massB o d|  ≤
          massB (e+i+j) d*(|a-x/massB i d|+|b-y/massB j d|):=by
    let I:=massB i d; let J:=massB j d
    have hh1:=mass0 i d; have hh2:=mass0 j d
    let v:= |a-x/I|; let w:=|b-y/J|
    have h1: |a*I-x|=I*v:=by
       unfold I v; rw [show a*I-x=I*(a-x/I) from by unfold I; field_simp]
       rw [abs_mul,abs_of_pos hh1]
    have h2: |b*J-y|=J*w:= by
       have he':b*J-y=J*(b-y/J):=by unfold J; field_simp
       rw [he',abs_mul]; exact congrArg (fun t=> t*w) (abs_of_pos hh2)
    have ha: |a*I|  ≤ 2*I := by
       change v ≤ 1 at hi; change 0<I at hh1; change |x| ≤ I at he
       have hh:= abs_add_le (a*I-x) x
       rw [sub_add_cancel] at hh; nlinarith
    have hb:|b*J| ≤ 2*J:=by
       change w ≤ 1 at hk; change 0<J at hh2; change |y| ≤ J at ht
       have hh:= abs_add_le (b*J-y) y; rw [sub_add_cancel] at hh; nlinarith
    have hz:=u.sturdy s ha hb (le_trans he (by linarith)) (le_trans ht (by linarith))
    rw [←sub_div,abs_div,abs_of_pos (mass0 o d)]
    apply le_trans (div_le_self (abs_nonneg _) (mass1 o d))
    apply le_trans hz
    rw [h1,h2, mass_mul,mass_mul]
    have ht : 1 ≤ I:= mass1 ..; have hp:1 ≤ J:=mass1 ..
    change massB e d*(I*v+J*w)  ≤  massB e d*I*J*(v+w)
    rw [show massB e d*I*J*(v+w)=massB e d*(I*J*(v+w)) by ring]
    apply mul_le_mul_of_nonneg_left _ (mass0 e d).le
    have hv:0 ≤ I*v:=mul_nonneg (by unfold I; positivity) (abs_nonneg _)
    have hx0:0 ≤ J*w:=mul_nonneg (by unfold J; positivity) (abs_nonneg _)
    nlinarith

abbrev joinCost (e i j c:ℕ):= e+i+j+6+100+c
lemma joint {s:Port}{k i j o e c H f g V X} (h: Align s k) (he:p.Fit e i j) (hc:1 ≤  c)
   (h1:Ears s c (H+(e+i+j+6)*s.d) i f V)(h2:Ears s c (H+(e+i+j+6)*s.d) j g X)
   (hv:|p.truef V X| ≤ massB o s.d) :
   Ears s (powder (Oven.price (joinCost e i j c))) H o (p.uPair k i j o e f g).cooked (p.truef V X):= by
   have ha:=amplitude h1; have hb:=amplitude h2
   obtain ⟨w,h1⟩:=h1; obtain ⟨b,h2⟩:=h2
   let d:=s.d; have hd:1 ≤ s.d:=h.1.1
   let q:=p.uPair k i j o e f g
   let f0:Rill.EV:=fun t _=> if t then V/massB i d else X/massB j d
   let g0:Rill.DW:=fun t _=> if t then w else b
   let C:=joinCost e i j c
   have hC:C≥100∧ c ≤ C:=by unfold C joinCost; omega
   have hM : q.P.margin.f s.l.x s.info=(e+i+j+6)*s.d:=by simp [q,uPair,h.2.1]
   have he0:q.P.Thaw s C H g0 f0:=by
      refine ⟨hC.1,h.1,?_,?_,?_⟩
      · rw [hM]; unfold C joinCost; exact Nat.mul_le_mul_right s.d (by omega)
      · intro b; change 1<2^(C*s.d); have hz:=growing (C*s.d); nlinarith
      intro b i hi; cases b
      · have hu: q.P.scans false=g:=by simp [q,uPair]
        rw [hu, Oven.ext,hM]; exact fewer h2 hc hC.2 le_rfl
      · have hu:q.P.scans true=f:=by simp [q,uPair]
        rw [hu,Oven.ext,hM]; exact fewer h1 hc hC.2 le_rfl
   have hl : q.Lip s (massB (e+i+j) s.d) (p.truef V X/massB o s.d) f0:=by
      refine ⟨by rw [abs_div,abs_of_pos (mass0 ..)]; exact (div_le_one (mass0 ..)).2 hv,
           mass1 ..,?_,fun x y hs hz=>?_⟩
      · rw [hM]; let n:=e+i+j
        change massB n s.d*4*3 ≤ massB (n+6) s.d
        rw [mass_mul n 6]; have hh : 12  ≤ massB 6 s.d:=by
           unfold massB
           calc
              (12:ℝ)  ≤  2^(6:ℕ):=by norm_num
              _ ≤ _:=pow_le_pow_right₀ (by norm_num) (by omega)
        have hp:=mass0 n s.d; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) hp.le
      · have hx:q.tally s f0 true=V/massB i s.d:=by simp [q,Meld.tally,Oven.labels,uPair,f0,d]
        have ht:q.tally s f0 false=X/massB j s.d:=by simp [q,Meld.tally,Oven.labels,uPair,f0,d]
        rw [hx] at hs; rw [ht] at hz; rw [hx,ht]
        simp only [q,uPair,remote,Coin.mul0,Coin.inv0,he.goodC,scalen h,← div_eq_mul_inv]
        exact behold _ hd _ _ _ _ he ha hb hs hz
   exact ⟨_,q.stream s he0 hl⟩
end Bid

end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill

inductive Doop where
  | plus| minus| prod| lesser| greater| flip
deriving DecidableEq

namespace Doop

def gate : Doop  →  Coin×Coin  →  Coin
   | .plus=>fun p=> Coin.join p.1 p.2
   | .minus=>fun p=> Coin.join p.1 (Coin.neg p.2)
   | .prod=>fun p=> Coin.mult p.1 p.2
   | .lesser=>fun p=> Coin.minimum p.1 p.2
   | .greater=>fun p=> Coin.maximum p.1 p.2
   | .flip => fun p=> Coin.inv (Coin.maximum p.1 (Coin.ofZ 1))

lemma gateK (p:Doop):Kn (fun (_:Word) a=> p.gate a):= by
   cases p
   · exact Coin.addaK Kn.first Kn.next
   · exact Coin.addaK Kn.first (Coin.negK Kn.next)
   · exact Coin.multK Kn.first Kn.next
   · exact Coin.minK Kn.first Kn.next
   · exact Coin.maxK Kn.first Kn.next
   exact Coin.invK (Coin.maxK Kn.first (Kn.fix (Coin.ofZ 1)))

noncomputable def val : Doop  →  ℝ → ℝ → ℝ
   | .plus=>fun x y=>x+y
   | .minus=>fun x y=>x-y
   | .prod=>fun x y=>x*y
   | .lesser=> fun x y=> min x y
   | .greater=> fun x y=>max x y
   | .flip=> fun x _=>(max x 1)⁻¹
noncomputable def ration(p:Doop):Bid:=⟨p.gate,p.gateK,p.val⟩
def fast (i j:ℕ) := i+j+2
lemma down_clip (x y:ℝ) : |(max x 1)⁻¹-(max y 1)⁻¹| ≤ |x-y| := by
   let a:= max x 1; let b:=max y 1
   have ha:1  ≤  a:=le_max_right ..
   have hb:1 ≤  b:=le_max_right ..
   have he:a⁻¹-b⁻¹=(b-a)/(a*b):=by field_simp
   have hv : |b-a| ≤ |x-y|:=by
      unfold b a; grind
   change |a⁻¹-b⁻¹| ≤ _
   rw [he,abs_div,abs_of_nonneg (show 0≤a*b by nlinarith)]
   exact le_trans (div_le_self (abs_nonneg _) (by nlinarith)) hv
lemma legit (p:Doop)(i j):p.ration.Fit (fast i j) i j:=by
   refine ⟨fun a b=>?_,fun {d} he {x y z t} hx hy hz ht=>?_⟩
   · cases p <;> simp [ration,gate,val,sub_eq_add_neg]
   let I:=massB i d; let J:=massB j d; let K:=massB (fast i j) d
   have h1:1 ≤ I:=mass1 ..; have h2:1 ≤ J:=mass1 ..
   have hu:2 ≤ massB 2 d:=le_of_lt (by simpa using swellB (c:=2) he)
   have hi : 2*I  ≤  K :=by unfold K fast; rw [mass_mul,mass_mul]; change 2*I ≤ I*J*_; nlinarith [mul_le_mul_of_nonneg_left hu (show 0≤I*J by nlinarith)]
   have hj : 2*J  ≤  K :=by unfold K fast; rw [mass_mul,mass_mul]; change 2*J ≤ I*J*_; nlinarith [mul_le_mul_of_nonneg_left hu (show 0≤I*J by nlinarith)]
   let a:=|x-z|; let b:=|y-t|
   have ha:0 ≤ a:=abs_nonneg _; have hb:0 ≤ b:=abs_nonneg _
   have hg:a+b ≤ K*(a+b):=by nlinarith
   cases p
   · change |x+y-(z+t)| ≤ K*(a+b); rw [show _-_=x-z+(y-t) by ring]; exact (abs_add_le ..).trans hg
   · change |x-y-(z-t)| ≤ K*(a+b); rw [show _-_=x-z-(y-t) by ring]; exact (abs_sub _ _).trans hg
   · change |x*y-z*t| ≤ K*(a+b)
     have he1:|x-z| *|y| ≤ a*K:=mul_le_mul_of_nonneg_left (hy.trans hj) ha
     have he2:|y-t| *|z| ≤ b*K:=mul_le_mul_of_nonneg_left (hz.trans hi) hb
     rw [show x*y-z*t=(x-z)*y+(y-t)*z by ring]
     apply le_trans (abs_add_le ..)
     rw [abs_mul,abs_mul]; nlinarith
   · apply le_trans _ hg; simp only [val,ration]; dsimp only [a,b]; grind
   · apply le_trans _ hg; simp only [val,ration]; dsimp only [a,b]; grind
   · exact (down_clip x z).trans ((le_add_of_nonneg_right hb).trans hg)

lemma geom (p:Doop) (i j d:ℕ) (h:0<d) {x y:ℝ}
   (hx: |x| ≤ massB i d)(hy:|y| ≤ massB j d):
   |p.val x y| ≤ massB (fast i j) d:=by
   let I:=massB i d; let J:=massB j d
   let K:=massB 2 d
   have hs:2 ≤ K:=le_of_lt (by simpa [K] using swellB (c:=2) h)
   have hi:1 ≤ I:=mass1 ..; have hj:1 ≤ J:=mass1 ..
   unfold fast; rw [mass_mul, mass_mul]
   change |p.val x y| ≤ I*J*K
   change |x| ≤ I at hx; change |y| ≤ J at hy
   have hu := mul_le_mul_of_nonneg_left hs (show 0≤I*J by nlinarith)
   have hh: |x|+|y| ≤ I*J*K:=by nlinarith
   cases p
   · exact (abs_add_le ..).trans hh
   · exact (abs_sub ..).trans hh
   · change |x*y| ≤ _; rw [abs_mul]
     nlinarith [mul_le_mul hx hy (abs_nonneg _) (show 0 ≤ I by linarith)]
   · refine le_trans ?_ hh; simp [val,min_def]; split <;> have :=abs_nonneg y <;> have := abs_nonneg x <;> linarith
   · refine le_trans ?_ hh; simp [val,max_def]; split <;> have :=abs_nonneg y <;> have := abs_nonneg x <;> linarith
   · change |(max x 1)⁻¹| ≤ _
     have hc:1  ≤  max x 1:=le_max_right ..
     rw [abs_inv,abs_of_nonneg (by linarith)]
     exact le_trans (inv_le_one_of_one_le₀ hc) (by nlinarith)

end Doop

abbrev CoinQuery := ℕ×ℕ

namespace Brick
def center (p:Knob) (f:Cub CoinQuery Coin) (i:ℕ)(x:Word)(a:Plot):Coin :=
   let q:History:=dec a.1
   let u:=p.store.f x q.1
   let s:=Coin.ofZ ((min u (2^q.2):ℕ):ℤ)
   Coin.mult s (Coin.mult (f.f x (q.1,a.2.2)) (Coin.inv (scaleC p i x q.1)))

set_option maxHeartbeats 1000000 in
lemma centerK (p f i):Kn (center p f i):=by
   have h:Kn (fun (_:Word)(a:Plot)=> (dec a.1:History)):=Kn.unpack.comp Kn.first
   have hz:=Coin.ofK ((Kn.cap (p.store.runs.comp h.left) (Kn.fix 2) h.right).ZofN)
   exact Coin.multK hz (Coin.multK (f.runs.comp (h.left.tuple Kn.next.right))
                                  (Coin.invK ((scaleK p i).comp h.left)))

def solop (p:Knob) (f:Cub CoinQuery Coin)(i:ℕ):Cog:=
   .edit ⟨fun x a=>(codeQ (Coin.floor0 (center p f i x a)),a.2.2),
      (codeK (Coin.floorK (centerK p f i))).tuple Kn.next.right⟩
def solo (p:Knob)(f:Cub CoinQuery Coin)(i:ℕ):Cog:=liftarm (solop p f i)
def tapeR (p:Knob)(f:Cub CoinQuery Coin)(i:ℕ)(s:Port)(t:ℕ):ℤ:=
   Coin.floor0 (center p f i s.l.x (postcard s.info t,0,s.src))

lemma each0 (p:Knob)(f:Cub CoinQuery Coin)(i:ℕ)(s:Port)(H)(ha:Align s p)
   (hl:Live s p H){v}(hv:(f.f s.l.x (s.info,s.src)).v=v)
   (he:|v| ≤ massB i s.d):
   s.Feeds (solo p f i) (powder 100) H (tapeR p f i s) (v/massB i s.d):=by
   apply lifting ha.1 (by omega)
   · intro t ht
     refine .edit rfl (s.stale ha.1 t _ (by omega)) (s.alone ha.1 t 100 ?_ ?_)
     · omega
     have h1:=lb_mono (rangeQ (tapeR p f i s t))
     rw [show lb 31=5 by rfl] at h1; omega
   refine ⟨by rw [abs_div,abs_of_pos (mass0 ..)]; exact (div_le_one (mass0 ..)).2 he,
              fun t ht=>?_⟩
   let u:=tapeR p f i s t
   have hg:=Coin.floorok (center p f i s.l.x (postcard s.info t,0,s.src))
   have hz : 2^t  ≤  p.store.f s.l.x s.info:= le_trans (Nat.pow_le_pow_right Nat.zero_lt_two ht) hl
   let g:= center p f i s.l.x (postcard s.info t,0,s.src)
   change (u:ℝ) ≤ g.v ∧ g.v ≤ (u:ℝ)+1 at hg
   have hp:g.v=(2:ℝ)^t*(v/massB i s.d):=by
       unfold g center; simp only [postcard,Wire.eq,Coin.mul0,Coin.ofv,Coin.inv0,hv,scalen ha,
                div_eq_mul_inv]; push_cast
       rw [min_eq_right (by exact_mod_cast hz)]
   rw [hp] at hg
   rw [abs_le]; unfold u at hg; constructor <;>linarith

end Brick
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill Analysis Finset

structure Branch where
    n : Cub ℕ ℕ
    route : Cub (ℕ×ℕ) ℕ
    k : Cub ℕ ℕ
    e : ℕ

namespace Branch
variable (p:Branch)
def port (s:Port)(i:ℕ):Port := {s with info:=p.route.f s.l.x (s.info,i)}
abbrev S (s:Port) := range (p.n.f s.l.x s.info)
abbrev key (s: Port):=p.k.f s.l.x s.info

def bowl (f:Cog): Survey := ⟨p.n,p.k,p.route,f⟩

structure Trust (s:Port)(i:ℕ)(V:ℕ→ℝ)(c H:ℕ)(f:Cog):Prop where
    cheaply : p.n.f s.l.x s.info < (2:ℕ)^(p.e*s.d)
    tick :∀ j∈p.S s,Ears (p.port s j) c H i f (V j)

lemma lease {s:Port}{V H c i f}(h:p.Trust s i V c H f)(hc:1 ≤ c)(ho:s.OK):
    Ears s (powder (Survey.priceB (c+p.e+100))) H i (p.bowl f).poll (rank (p.S s) V (p.key s)):=by
   classical
   have hh(j): ∃ w,j∈p.S s → (p.port s j).Feeds f c H w (V j/massB i s.d):=by
       by_cases ht:j∈p.S s
       · obtain ⟨w,hx⟩:=h.tick j ht; exact ⟨w,fun _=>hx⟩
       exact ⟨fun _=>0,fun hz=> (ht hz).elim⟩
   choose w hw using hh
   let u:=p.bowl f
   let W:= fun (j:ℕ)=> V j/massB i s.d
   have hz : u.Clue s (c+p.e+100) H W w:= by
      refine ⟨by omega,ho,?_ ,fun j hj=>fewer (hw j (mem_range.2 hj)) hc (by omega) le_rfl⟩
      apply h.cheaply.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two ?_)
      gcongr; omega
   let v:=massB i s.d
   have hs:rank (p.S s) W (p.key s)=rank (p.S s) V (p.key s)/v:=by
      have hm:W=(fun j=>v⁻¹*V j):=funext fun _=> by unfold v W; ring
      rw [hm,scaled_rank (by unfold v; positivity)]; ring
   have ht: Ears s (powder (Survey.priceB (c+p.e+100))) H i u.poll (rank (p.S s) V (p.key s)) := by
      unfold Ears; rw [← hs]; exact ⟨_, hz.tasked⟩
   exact ht

def collect (f:Cog)(k:Knob) (r:ℕ): Meld :=
    let o:=r+p.e
    let M:=p.e+6
    let even1 (x:Word)(a:Bid.arm):Coin:= Coin.mult (Coin.mult a.2.1 (scaleC k r x a.1))
                                                            (Coin.inv (scaleC k o x a.1))
    have he:Kn even1 := Coin.multK
       (Coin.multK Kn.next.left ((scaleK k r).comp Kn.first))
       (Coin.invK ((scaleK k o).comp Kn.first))
    { P:={ n:= fun b=> if b then p.n else ⟨_,Kn.fix 0⟩, route:=fun _=>p.route,
           margin:=⟨fun x a=>M*k.height.f x a,(Kn.fix _).times k.height.runs⟩,scans:=fun _=>f }
      f:=⟨_,he⟩ }
abbrev reserve : ℕ := p.e+6
abbrev foldC(p:Branch)(c:ℕ):= c+p.e+106
lemma poem {s:Port}{V H c i f k}
   (h:p.Trust s i V c (H+p.reserve*s.d) f)(hc:1 ≤ c)(ho:Align s k) :
   Ears s (powder (Oven.price (p.foldC c))) H (i+p.e) ((p.collect f k i).cooked) (∑ j∈p.S s, V j):=by
   classical
   let u:=p.collect f k i
   let C:=p.foldC c
   let o:=i+p.e
   let D:=massB i s.d
   let B:=massB o s.d
   have hA:0<D:=mass0 i s.d
   have hB:0<B:=mass0 o s.d
   let W:Rill.EV:= fun b j=> V j/D
   have hk:C≥p.reserve∧C≥100∧ c ≤  C:=by unfold C reserve foldC; omega
   have hN(q:Bool) : u.P.labels s q  ≤  p.n.f s.l.x s.info := by cases q <;> simp [Oven.labels,u,collect]
   have hs(b:Bool)(j):∃ w,(j<u.P.labels s b) → (u.P.rel s b j).Feeds (u.P.scans b) c (H+p.reserve*s.d) w (W b j):=by
      by_cases ht:j<u.P.labels s b
      · obtain ⟨w,h0⟩:=h.tick j (mem_range.2 (ht.trans_le (hN b)))
        exact ⟨w,fun _=>h0⟩
      exact ⟨fun _=>0,fun hz=> (ht hz).elim⟩
   choose w hw using hs
   have he0:u.P.margin.f s.l.x s.info=p.reserve*s.d:= by
         simp [u,collect,reserve,ho.2.1]
   have he:u.P.Thaw s C H w W:=by
      refine ⟨hk.2.1,ho.1,by rw [he0]; exact Nat.mul_le_mul_right _ hk.1,?_,?_⟩
      · intro b; apply lt_of_le_of_lt (hN b)
        apply h.cheaply.trans_le
        exact Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right _ (by unfold C foldC; omega))
      intro b i h; unfold Oven.ext; rw [he0]; exact fewer (hw b i h) hc hk.2.2 le_rfl
   let m:=p.n.f s.l.x s.info
   let v:=∑ j∈p.S s, V j
   have hi(Den):0 < massB Den s.d:= mass0 ..
   have hb:B=D*massB p.e s.d:= mass_mul ..
   have hr:m < massB p.e s.d:= by unfold massB; exact_mod_cast h.cheaply
   have hl : u.Lip s 1 (v/B) W:=by
     refine ⟨?_,le_rfl,?_,fun x y hx hy=>?_⟩
     · rw [abs_div,abs_of_pos hB,div_le_one hB]
       apply le_trans (abs_sum_le_sum_abs .. )
       have hz:∑ j∈p.S s, |V j| ≤  ∑ _∈p.S s,D:=by
            exact sum_le_sum fun j hz=>amplitude (p:=p.port s j) (h.tick j hz)
       apply hz.trans; simp [S,m] at *
       rw [hb]; nlinarith
     · rw [he0]; simp [u,collect,Oven.labels,m] at *
       unfold reserve; rw [add_mul,pow_add]; unfold massB at hr
       have hv: (16:ℝ)  ≤  (2:ℝ)^(6*s.d):=calc
          _  ≤  (2:ℝ)^(6:ℕ):=by norm_num
          _  ≤  _:=pow_le_pow_right₀ (by norm_num) (by have := ho.1.1; omega)
       have hp := mass1 p.e s.d; unfold massB at hp
       nlinarith
     have hx0:u.tally s W true=v/D:=by
       simp only [v,D,W,u,collect,Meld.tally,S,Oven.labels,ite_true,sum_div]
     rw [hx0]
     simp only [u,collect,Coin.mul0,Coin.inv0,scalen ho,← div_eq_mul_inv,one_mul]
     change |x.v*D/B - v/B|  ≤  |x.v-v/D| +_
     apply le_trans _ (le_add_of_nonneg_right (abs_nonneg _))
     have hx1:x.v*D/B-v/B=(x.v-v/D)* (D/B):= by field_simp
     rw [hx1,abs_mul,abs_of_nonneg (by positivity : 0 ≤  D/B)]
     apply mul_le_of_le_one_right (abs_nonneg _)
     apply (div_le_one hB).2
     have hz0:=mass1 p.e s.d; nlinarith
   exact ⟨_,u.stream s he hl⟩
end Branch
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill Analysis Finset

inductive Lyric where
   | solo (i:ℕ) (f:Cub CoinQuery Coin)
   | use (i:ℕ) (p:Cog)
   | duet (p:Doop)(x y:Lyric)(o:ℕ)
   | heap (sum0:Bool)(p:Branch)(f: Lyric)

namespace Lyric
def weight: Lyric  → ℕ
   | .solo i _| .use i _=>i
   | .duet _ _ _ o=> o
   | .heap b p f=> if b then weight f+p.e else weight f

def pulse (i j:ℕ):= Doop.fast i j+i+j+6
def tail : Lyric → ℕ
   | .solo ..| .use ..=>0
   | .duet _ x y _=> pulse (weight x) (weight y)+max (tail x) (tail y)
   | .heap b p f=> (if b then p.reserve else 0)+tail f

def operate (e i j c:ℕ):= powder (Oven.price (Bid.joinCost e i j c))
def cost (p: Lyric)(c:ℕ): ℕ := match p with
   | .solo ..=> powder 100
   | .use ..=>c
   | .duet _ x y _=> operate (Doop.fast (weight x) (weight y)) (weight x) (weight y)
                                      (max (cost x c) (cost y c))
   | .heap b p f=> if b then powder (Oven.price (p.foldC (cost f c))) else
                                      powder (Survey.priceB (cost f c+p.e+100))

lemma cost_hi {p:Lyric}{c:ℕ}(hc:1 ≤ c):1 ≤ p.cost c:= by
   have hp (i:ℕ): 1 ≤ powder i:=by unfold powder; omega
   cases p with
   | solo=> exact hp _
   | use=> exact hc
   | duet=> exact hp _
   | heap b=> cases b <;> exact hp _

noncomputable def choir (s:Knob) (p:Lyric):Cog:= match p with
   | .solo i f=> Brick.solo s f i
   | .use _ f=>f
   | .duet p x y o=>
      let i:=weight x
      let j:=weight y
      (p.ration.uPair s i j o (Doop.fast i j) (choir s x) (choir s y)).cooked
   | .heap b p f=>
        let q:=choir s f
        if b then (p.collect q s (weight f)).cooked else (p.bowl q).poll

inductive Lethe (p:Knob)(c T:ℕ) : Port →  Lyric  → ℝ → Prop where
   | byear {s r f V} :
       Ears s c T r f V  →  Lethe p c T s (.use r f) V
   | played {s i f}(h:Align s p)(e:Live s p T)
       (hb: |(f.f s.l.x (s.info,s.src)).v|  ≤  massB i s.d):
          Lethe p c T s (.solo i f) (f.f s.l.x (s.info,s.src)).v
   | doo {s i j A B u o} (h:Align s p)
       (ha:Lethe p c T s i A) (hb:Lethe p c T s j B) (hr:|u.val A B| ≤ massB o s.d):
              Lethe p c T s (.duet u i j o) (u.val A B)
   | little {s q f V b} (h:Align s p)
       (he:q.n.f s.l.x s.info<(2:ℕ)^(q.e*s.d)) (hg:∀ i∈q.S s,Lethe p c T (q.port s i) f (V i)):
               Lethe p c T s (.heap b q f) (if b then ∑ i∈q.S s,V i else rank (q.S s) V (q.key s))

theorem song {p c T s f V} (hc:1 ≤ c) (h:Lethe p c T s f V){H:ℕ}(he:H+f.tail*s.d ≤ T):
     Ears s (f.cost c) H f.weight (choir p f) V:= by
    induction h generalizing H with
    | @byear s i q v h=> apply supply h hc le_rfl; exact (Nat.le_add_right ..).trans he
    | @played s i f h hl hb=>
      have hp:H ≤ T :=(Nat.le_add_right ..).trans he
      exact ⟨_, Brick.each0 p f i s H h ((Nat.pow_le_pow_right Nat.zero_lt_two hp).trans hl) rfl hb⟩
    | @doo s i j A B u o h h1 h2 h3 ia ib=>
      let z:=pulse i.weight j.weight
      let v:= H+z*s.d
      let k:=max (i.cost c) (j.cost c)
      have hp:v+max (tail i) (tail j)*s.d ≤ T:=by
          change H+(z+max i.tail j.tail)*s.d ≤ T at he
          unfold v; rwa [add_mul,← add_assoc] at he
      have hi : v+(tail i)*s.d ≤ T := by
         apply le_trans _ hp
         gcongr; exact le_max_left ..
      have hj : v+(tail j)*s.d ≤ T:=by
         apply le_trans _ hp
         gcongr; exact le_max_right ..
      apply Bid.joint u.ration h (u.legit ..) ((cost_hi (p:=i) hc).trans (le_max_left ..)) _ _ h3
      · exact supply (ia hi) (cost_hi hc) (le_max_left ..) le_rfl
      exact supply (ib hj) (cost_hi hc) (le_max_right ..) le_rfl
    | @little s q f V b h hz hf ih=>
      let i:= f.weight
      let w:=choir p f
      have hp:q.Trust s i V (f.cost c) (H+(if b then q.reserve else 0)*s.d) w:= by
         refine ⟨hz,fun j hj=>ih j hj ?_⟩
         unfold tail at he; dsimp only [Branch.port]; rwa [add_mul,← add_assoc] at he
      cases b
      · simp only [choir,cost,weight,Bool.false_eq_true,ite_false]
        simp only [Bool.false_eq_true,ite_false,zero_mul,add_zero] at hp
        exact q.lease hp (cost_hi hc) h.1
      simp only [choir,cost,weight,ite_true]
      exact q.poem hp (cost_hi hc) h

lemma Lethe.bnd {p c T s f V}(h:Lethe p c T s f V):
    |V|  ≤  massB f.weight s.d:= by
   induction h with
   | byear he=> exact amplitude he
   | played _ _ hb=> exact hb
   | doo _ _ _ he _ _=> exact he
   | @little s q f V b h he hg ih=>
     let X:=massB f.weight s.d
     have hp:0 ≤ X:= (mass0 ..).le
     have hi (i:ℕ)(e:i∈q.S s):|V i| ≤ X:=ih i e
     cases b
     · rw [ite_eq_right (by simp),abs_of_nonneg (rank_nn ..)]; exact rank_le hp
                              (fun i e=>le_trans (le_abs_self _) (hi _ e))
     · simp only [weight,ite_true]
       refine le_trans (abs_sum_le_sum_abs ..) ?_
       apply le_trans (b:=∑ i ∈ q.S s,X) (sum_le_sum hi)
       simp only [Branch.S, sum_const,card_range,nsmul_eq_mul]
       have hr:(q.n.f s.l.x s.info:ℝ)< massB q.e s.d:=by unfold massB; exact_mod_cast he
       rw [mass_mul]
       unfold X at *; nlinarith

abbrev bi (p:Doop)(x y:Lyric):Lyric:= .duet p x y (Doop.fast x.weight y.weight)
lemma Lethe.bundle {p c T s i j A B} (h:Lethe p c T s i A) (e:Lethe p c T s j B)
    (hs:Align s p)(op:Doop):
    Lethe p c T s (bi op i j) (op.val A B):=
   .doo hs h e (op.geom _ _ s.d hs.1.1 h.bnd e.bnd)

end Lyric
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill Analysis Finset
namespace Bid
variable(p:Bid)
lemma fixedjoint {s:Port}{k i j o e c H f g V X w b} (h: Align s k) (he:p.Fit e i j) (hc:1 ≤  c)
   (h1:s.Feeds f c (H+(e+i+j+6)*s.d) w (V/massB i s.d))(h2:s.Feeds g c (H+(e+i+j+6)*s.d) b (X/massB j s.d))
   (hv:|p.truef V X| ≤ massB o s.d) :
   let q:=p.uPair k i j o e f g
   s.Feeds q.cooked (powder (Oven.price (joinCost e i j c))) H (q.out s (fun t _=> if t then w else b)) (p.truef V X /massB o s.d):= by
   have ha:=amplitude (p:=s) (v:=V) (f:=f) (i:=i) (T:=H+(e+i+j+6)*s.d) (c:=c) ⟨w,h1⟩; have hb:=amplitude (p:=s) (v:=X) (f:=g) (i:=j) (T:=H+(e+i+j+6)*s.d) (c:=c) ⟨b,h2⟩
   let d:=s.d; have hd:1 ≤ s.d:=h.1.1
   let q:=p.uPair k i j o e f g
   let f0:Rill.EV:=fun t _=> if t then V/massB i d else X/massB j d
   let g0:Rill.DW:=fun t _=> if t then w else b
   let C:=joinCost e i j c
   have hC:C≥100∧ c ≤ C:=by unfold C joinCost; omega
   have hM : q.P.margin.f s.l.x s.info=(e+i+j+6)*s.d:=by simp [q,uPair,h.2.1]
   have he0:q.P.Thaw s C H g0 f0:=by
      refine ⟨hC.1,h.1,?_,?_,?_⟩
      · rw [hM]; unfold C joinCost; exact Nat.mul_le_mul_right s.d (by omega)
      · intro b; change 1<2^(C*s.d); have hz:=growing (C*s.d); nlinarith
      intro b i hi; cases b
      · have hu: q.P.scans false=g:=by simp [q,uPair]
        rw [hu, Oven.ext,hM]; exact fewer h2 hc hC.2 le_rfl
      · have hu:q.P.scans true=f:=by simp [q,uPair]
        rw [hu,Oven.ext,hM]; exact fewer h1 hc hC.2 le_rfl
   have hl : q.Lip s (massB (e+i+j) s.d) (p.truef V X/massB o s.d) f0:=by
      refine ⟨by rw [abs_div,abs_of_pos (mass0 ..)]; exact (div_le_one (mass0 ..)).2 hv,
           mass1 ..,?_,fun x y hs hz=>?_⟩
      · rw [hM]; let n:=e+i+j
        change massB n s.d*4*3 ≤ massB (n+6) s.d
        rw [mass_mul n 6]; have hh : 12  ≤ massB 6 s.d:=by
           unfold massB
           calc
              (12:ℝ)  ≤  2^(6:ℕ):=by norm_num
              _ ≤ _:=pow_le_pow_right₀ (by norm_num) (by omega)
        have hp:=mass0 n s.d; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) hp.le
      · have hx:q.tally s f0 true=V/massB i s.d:=by simp [q,Meld.tally,Oven.labels,uPair,f0,d]
        have ht:q.tally s f0 false=X/massB j s.d:=by simp [q,Meld.tally,Oven.labels,uPair,f0,d]
        rw [hx] at hs; rw [ht] at hz; rw [hx,ht]
        simp only [q,uPair,remote,Coin.mul0,Coin.inv0,he.goodC,scalen h,← div_eq_mul_inv]
        exact behold _ hd _ _ _ _ he ha hb hs hz
   exact q.stream s he0 hl
end Bid
namespace Branch
variable (p:Branch)
structure Faith (s:Port)(i:ℕ)(V:ℕ→ℝ)(c H:ℕ)(f:Cog)(w:ℕ→Tape):Prop where
    cheaply : p.n.f s.l.x s.info < (2:ℕ)^(p.e*s.d)
    tick :∀ j∈p.S s,(p.port s j).Feeds f c H (w j) (V j/massB i s.d)

lemma leased {s:Port}{V H c i f w}(h:p.Faith s i V c H f w)(hc:1 ≤ c)(ho:s.OK):
    s.Feeds (p.bowl f).poll (powder (Survey.priceB (c+p.e+100))) H
       (fun t=> (rankN (p.S s) (fun j=>(w j t).toNat) (p.key s):ℤ)) ((rank (p.S s) V (p.key s))/massB i s.d):=by
   classical
   let u:=p.bowl f
   let W:= fun (j:ℕ)=> V j/massB i s.d
   have hz : u.Clue s (c+p.e+100) H W w:= by
      refine ⟨by omega,ho,?_ ,fun j hj=>fewer (h.tick j (mem_range.2 hj)) hc (by omega) le_rfl⟩
      apply h.cheaply.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two ?_)
      gcongr; omega
   let v:=massB i s.d
   have hs:rank (p.S s) W (p.key s)=rank (p.S s) V (p.key s)/v:=by
      have hm:W=(fun j=>v⁻¹*V j):=funext fun _=> by unfold v W; ring
      rw [hm,scaled_rank (by unfold v; positivity)]; ring
   rw [← hs]; exact hz.tasked
lemma poems {s:Port}{V H c i f k tapes}
   (h:p.Faith s i V c (H+p.reserve*s.d) f tapes)(hc:1 ≤ c)(ho:Align s k) :
   let u:=p.collect f k i
   s.Feeds u.cooked (powder (Oven.price (p.foldC c))) H (u.out s (fun _ j=>tapes j)) ((∑ j∈p.S s, V j)/massB (i+p.e) s.d):=by
   classical
   let u:=p.collect f k i
   let C:=p.foldC c
   let o:=i+p.e
   let D:=massB i s.d
   let B:=massB o s.d
   have hA:0<D:=mass0 i s.d
   have hB:0<B:=mass0 o s.d
   let W:Rill.EV:= fun b j=> V j/D
   have hk:C≥p.reserve∧C≥100∧ c ≤  C:=by unfold C reserve foldC; omega
   have hN(q:Bool) : u.P.labels s q  ≤  p.n.f s.l.x s.info := by cases q <;> simp [Oven.labels,u,collect]
   let w:DW:=fun _ j=>tapes j
   have hw(b:Bool)(j) (ht:j<u.P.labels s b): (u.P.rel s b j).Feeds (u.P.scans b) c (H+p.reserve*s.d) (w b j) (W b j):=
            h.tick j (mem_range.2 (ht.trans_le (hN b)))
   have he0:u.P.margin.f s.l.x s.info=p.reserve*s.d:= by
         simp [u,collect,reserve,ho.2.1]
   have he:u.P.Thaw s C H w W:=by
      refine ⟨hk.2.1,ho.1,by rw [he0]; exact Nat.mul_le_mul_right _ hk.1,?_,?_⟩
      · intro b; apply lt_of_le_of_lt (hN b)
        apply h.cheaply.trans_le
        exact Nat.pow_le_pow_right Nat.zero_lt_two (Nat.mul_le_mul_right _ (by unfold C foldC; omega))
      intro b i h; unfold Oven.ext; rw [he0]; exact fewer (hw b i h) hc hk.2.2 le_rfl
   let m:=p.n.f s.l.x s.info
   let v:=∑ j∈p.S s, V j
   have hi(Den):0 < massB Den s.d:= mass0 ..
   have hb:B=D*massB p.e s.d:= mass_mul ..
   have hr:m < massB p.e s.d:= by unfold massB; exact_mod_cast h.cheaply
   have hl : u.Lip s 1 (v/B) W:=by
     refine ⟨?_,le_rfl,?_,fun x y hx hy=>?_⟩
     · rw [abs_div,abs_of_pos hB,div_le_one hB]
       apply le_trans (abs_sum_le_sum_abs .. )
       have hz:∑ j∈p.S s, |V j| ≤  ∑ _∈p.S s,D:=by
            exact sum_le_sum fun j hz=>amplitude (p:=p.port s j) (i:=i) (f:=f) (c:=c)
                         (T:=H+p.reserve*s.d) ⟨tapes j,h.tick j hz⟩
       apply hz.trans; simp [S,m] at *
       rw [hb]; nlinarith
     · rw [he0]; simp [u,collect,Oven.labels,m] at *
       unfold reserve; rw [add_mul,pow_add]; unfold massB at hr
       have hv: (16:ℝ)  ≤  (2:ℝ)^(6*s.d):=calc
          _  ≤  (2:ℝ)^(6:ℕ):=by norm_num
          _  ≤  _:=pow_le_pow_right₀ (by norm_num) (by have := ho.1.1; omega)
       have hp := mass1 p.e s.d; unfold massB at hp
       nlinarith
     have hx0:u.tally s W true=v/D:=by
       simp only [v,D,W,u,collect,Meld.tally,S,Oven.labels,ite_true,sum_div]
     rw [hx0]
     simp only [u,collect,Coin.mul0,Coin.inv0,scalen ho,← div_eq_mul_inv,one_mul]
     change |x.v*D/B - v/B|  ≤  |x.v-v/D| +_
     apply le_trans _ (le_add_of_nonneg_right (abs_nonneg _))
     have hx1:x.v*D/B-v/B=(x.v-v/D)* (D/B):= by field_simp
     rw [hx1,abs_mul,abs_of_nonneg (by positivity : 0 ≤  D/B)]
     apply mul_le_of_le_one_right (abs_nonneg _)
     apply (div_le_one hB).2
     have hz0:=mass1 p.e s.d; nlinarith
   exact u.stream s he hl
end Branch
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Relay
open Counter
namespace Cog
variable (q:Cub ℕ ℕ)

abbrev repx {α} (q:Cub ℕ ℕ)(x:Word)(a:ℕ×α) := (q.f x a.1,a.2)
lemma repK {α} [Wire α] : Kn (repx (α:=α) q):= (q.runs.comp Kn.first).tuple Kn.next

def stampT (q:Cub ℕ ℕ) {α β:Type}[Wire α][Wire β](v:Cub (ℕ×α) β) :Cub (ℕ×α) β:=
   ⟨fun x a=>v.f x (repx q x a),v.runs.comp (repK ..)⟩
def outerQ (q:Cub ℕ ℕ)(v:Cub Drain Site): Cub Drain Site:=
   ⟨fun x a=>v.f x ((q.f x a.1.1,a.1.2),a.2),
           v.runs.comp (((q.runs.comp Kn.first.left).tuple Kn.first.right).tuple Kn.next)⟩
def ren : Cog→ Cog
    | edit f=> edit (stampT q f)
    | toss p e=> toss (stampT q p) (outerQ q e)
    | seq a b=> seq (ren a) (ren b)
    | Cog.bif p a b=> Cog.bif (stampT q p) (ren a) (ren b)
    | loop p a=> loop (stampT q p) (ren a)
lemma renameR {l c b d n p a u} (h:Lot.Mane l c b d n p a u){x:ℕ} (e:q.f l.x x=n):
   Lot.Mane l c b d x (ren q p) a u:= by
    induction h
    · rename_i he hf hg
      apply Lot.Mane.edit _ hf hg
      simp only [stampT,repx,e]; exact he
    · rename_i eh ek hl hi hm hp
      refine .toss ?_ ?_ hl hi hm hp
      · simp only [stampT,repx,e]; exact eh
      simp only [outerQ,e]; exact ek
    · exact .seq (by assumption) (by assumption)
    · apply Lot.Mane.yes _ (by assumption)
      simp only [stampT,repx,e]; assumption
    · apply Lot.Mane.no _ (by assumption)
      simp only [stampT,repx,e]; assumption
    · apply Lot.Mane.more _ (by assumption) (by assumption)
      simp only [stampT,repx,e]; assumption
    · apply Lot.Mane.stop _ (by assumption)
      simp only [stampT,repx,e]; assumption

end Cog
namespace Lot
lemma Mane.rise {l c q w t p d a b}(h:Mane l c ⟨w,t⟩ d q p a b){H}(he:t≤H):
    Mane l c ⟨w,H⟩ d q p a b:=by
   have h1(i j k:ℕ):span c k t i j → span c k H i j:= fun e=>
      le_trans e (Nat.add_le_add_right (Nat.mul_le_mul_left c he) _)
   have hh(a)(e:l.state c ⟨w,t⟩ a):l.state c ⟨w,H⟩ a:=⟨e.1,h1 _ _ _ e.2⟩
   have hg(a q:ℕ)(e:l.jump c ⟨w,t⟩ d a q):l.jump c ⟨w,H⟩ d a q:=⟨e.1,h1 _ _ _ e.2⟩
   induction h
   · exact .edit (by assumption) (hh _ ‹_›) (hh _ ‹_›)
   · rename_i he hf hk hl he0 ho
     exact .toss he hf (hh _ hk) (hh _ hl) (hg _ _ he0) ho
   · exact .seq (by assumption) (by assumption)
   · exact .yes (by assumption) (by assumption)
   · exact .no (by assumption) (by assumption)
   · exact .more (by assumption) (by assumption) (by assumption)
   · exact .stop (by assumption) (hh _ ‹_›)

lemma absorb {c t d W :ℕ} (h:1≤c)(hp:t≤c*d)(_:1≤W)(hz:d≤W)
     {j k}(h1:span c W t j k):
    span (4*c) W 0 j k:= by
   have hs : t ≤ c*W:= le_trans hp (Nat.mul_le_mul_left c hz)
   have hl:=lax h1 (m:=1) (D:=4*c) (by omega) h; unfold span
   nlinarith [Nat.mul_le_mul_left c hs]
lemma Mane.pause {l c q w t p d a b}(h:Mane l c ⟨w,t⟩ d q p a b)
   (he:1≤ c)(ho:1≤d)(hr:d≤w)(hp:t≤c*d):
   Mane l (4*c) ⟨w,0⟩ d q p a b:=by
   have hh(v)(h:l.state c ⟨w,t⟩ v):l.state (4*c) ⟨w,0⟩ v:=
      ⟨h.1,absorb he hp (ho.trans hr) hr h.2⟩
   have hg(v t1)(h:l.jump c ⟨w,t⟩ d v t1):l.jump (4*c) ⟨w,0⟩ d v t1:= by
       have he0 : d≤w-(l.book t1).w:=by have hu:(l.book t1).w+d≤w:=h.1; omega
       exact ⟨h.1,absorb he hp (ho.trans he0) he0 h.2⟩
   induction h
   · exact .edit (by assumption) (hh _ ‹_›) (hh _ ‹_›)
   · rename_i he hf hk hl he0 ho
     exact .toss he hf (hh _ hk) (hh _ hl) (hg _ _ he0) ho
   · exact .seq (by assumption) (by assumption)
   · exact .yes (by assumption) (by assumption)
   · exact .no (by assumption) (by assumption)
   · exact .more (by assumption) (by assumption) (by assumption)
   · exact .stop (by assumption) (hh _ ‹_›)
end Lot
end ExactDerandomization.Relay

end

section

/-! Scratch-control algebra. -/
namespace ExactDerandomization.Fret
open Relay Counter Rill

abbrev Punct (p:Port)(c v:ℕ) := lb v +1 ≤ c*p.d
lemma holdroom {p:Port}{c u v:ℕ}(_:p.OK)(h:Punct p c u)(e:Punct p c v):
    Punct p (4*c) (enc (u,v)):=by
   have hc:0<c:=by by_contra! hx; unfold Punct at *; simp_all
   unfold Punct at *
   have he : lb (enc (u,v))≤ 2*lb u+lb v+2:=measure_pair _ _
   nlinarith
lemma punctspan {p:Port}{c v t}(hc:Punct p c v) (ht:1≤c) :
   span c p.d t t (lb v+1):=by
   unfold Punct span at *
   nlinarith [Nat.mul_le_mul_right p.d (show c≤c*c by nlinarith)]
lemma plight {p:Port}{c v t}(hc:Punct p c v) (hp:p.OK)(ht:1≤c):
    p.l.state c ⟨p.w,t⟩ (p.s v):= by
   refine ⟨hp.2.2,movespan ?_ hp.2.1⟩
   have h:=punctspan hc ht (t:=t); unfold span at *; dsimp; omega
lemma punct0 {p:Port}(h:p.OK) {c}(ht:2≤c): Punct p c 0:= by
   unfold Punct; rw [lb_zero]; have he:=h.1; nlinarith
lemma punct_up {p:Port} {c v j}(h:Punct p c v)(ht:c≤j):Punct p j v:=
   h.trans (Nat.mul_le_mul_right p.d ht)

/- holding structural query control and visiting neighboring digit routine.
For same absolute numerical place (special case = zero). -/
namespace Cargo
def mint (P:Cub History ℕ)
    (x:Word)(q:Slip):ℕ:=
   let a:History:= dec q.1
   postcard (P.f x (a.1,q.2)) a.2
lemma mintK(P):Kn (mint P):= by
   have h:= (Kn.unpack (α:=History)).comp (Kn.first (β:=ℕ))
   exact Kn.wash.comp ((P.runs.comp (h.left.tuple Kn.next)).tuple h.right)
def openx (_:Word)(a:Lore ℕ):History:=(a.2,0)
lemma openK:Kn openx:=Kn.next.tuple (Kn.fix _)
def encase (P:Cub History ℕ) (q:Cog):Cog:=
   .seq (etch _ openK) (Cog.focus ⟨_,mintK P⟩ q)

def transit (f:Cub History ℕ)(p:Port)(i:ℕ) : Port:={p with info:=f.f p.l.x (p.info,i)}
lemma aboard {p:Port} {c v t q} {f:Cub History ℕ}
   (hp:p.OK)(ht:1≤c)(hz:Punct p c v)
   {u:Site}(he:(transit f p v).comp t c q (p.s 0) u):
   p.comp t (4*c) (encase f q) (p.s v) (hold v u):= by
    have h1:=punctspan hz ht (t:=t)
    have hc : p.comp t (4*c) (Cog.focus ⟨_,mintK f⟩ q)
       (hold v (p.s 0)) (hold v u) := by
      refine Cog.focus_word _ he ?_ h1 hp.2.1 (by omega) ht ht
      simp [mint,transit,postcard]
    exact .seq (etches _ _ (i:=v) rfl (plight (punct_up hz (by omega)) hp (by omega)) hc.spots.1) hc

def switch (k:Cub ℕ ℕ)(x:Word)(v:ℕ):ℕ:=
   let a:History:=dec v
   postcard (k.f x a.1) a.2
lemma switchK(k):Kn (switch k):=by
   have h:= (Kn.unpack (α:=History))
   exact Kn.wash.comp ((k.runs.comp h.left).tuple h.right)

def strip (_:Word)(n:ℕ):ℕ:= postcard (dec n:History).1 0
lemma stripK : Kn strip :=Kn.wash.comp ((Kn.unpack (α:=History)).left.tuple (Kn.fix _))

abbrev only0 (p:Port)(c:ℕ):=p.comp 0 c
def flag0:Flag := ⟨fun _ a=>decide (a.2.1=0),Kn.next.left.eq (Kn.fix 0)⟩
def knock : Cog:= etch (α:=ℕ) (fun _ _=>(0:ℕ)) (Kn.fix _)

def choose (hint A B:Cog) := Cog.seq (Cog.ren ⟨_,stripK⟩ hint) (.bif flag0
                                (.seq knock A) (.seq knock B))

lemma expands {p:Port}{c q t x y}(h: p.comp 0 c q x y):
   p.comp t c (Cog.ren ⟨_,stripK⟩ q) x y :=
    (Cog.renameR ⟨_,stripK⟩ h (by simp [strip,postcard])).rise (Nat.zero_le _)

lemma flavor {p:Port}{c b q g f i t v} (_:p.OK) (h:only0 p c q (p.s 0) (p.s b))
    (ha:b=0 → Ears p c t i g v)(hb:b≠0 → Ears p c t i f v):
        Ears p c t i (choose q g f) v:=by
    by_cases hh:b=0
    · obtain ⟨w,hr,hw⟩:=ha hh
      refine ⟨w,hr,⟨fun k hk=>?_⟩⟩
      have ht:=hw.digits _ hk; have hg:=expands h (t:=k)
      refine .seq hg (.yes (show decide (b=0)=true by simp [hh]) (.seq ?_ ht))
      exact etches _ _ (i:=b) rfl hg.spots.2 ht.spots.1
    obtain ⟨w,hr,hw⟩:=hb hh
    refine ⟨w,hr,⟨fun k hk=>?_⟩⟩
    have ht:=hw.digits _ hk; have hg:=expands h (t:=k)
    refine .seq hg (.no (show decide (b=0)=false by simp [hh]) (.seq ?_ ht))
    exact etches _ _ (i:=b) rfl hg.spots.2 ht.spots.1

def combine (hint B:Cog)(C:Cub History ℕ):Cog:=
   .seq (Cog.ren ⟨_,stripK⟩ hint)
        (.seq (encase C B)
           (etch (α:=History) (fun _ h=>h.2.2) Kn.next.right))

lemma restores {p:Port}{c b q g C i t v}
    (hp:p.OK) (hb:Punct p c b)(hc:1≤ c)(h:only0 p c q (p.s 0) (p.s b))
    (ha:Ears (transit C p b) c t i g v) :
        Ears p (4*c) t i (combine q g C) v:=by
   obtain ⟨w,ht,h0⟩:=ha
   refine ⟨w,ht,⟨fun k hk=>?_⟩⟩
   have hz:=h0.digits k hk
   have he:=aboard hp hc hb hz
   have hu := (expands (t:=k) h).mono (D:=4*c) (by omega) hc
   refine .seq hu (.seq he ?_)
   exact etches _ _ (i:=((b,enc (dsign w k)):History)) rfl he.spots.2
                         (hz.mono (c:=c) (D:=4*c) (by omega) hc).spots.2
end Cargo
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill

/-- transparent query/list iteration -/
structure Camp where
   n : Cub ℕ ℕ
   recipe : Cub History ℕ
   prog : Cog
   post : Cub (Lore (ℕ×ℕ)) ℕ

namespace Camp
variable (r:Camp)
abbrev Info:=Lore (ℕ×ℕ)
def cond0 (x:Word)(a:Info): Bool:= decide (a.2.1 < r.n.f x (dec a.1:History).1)
lemma condK:Kn r.cond0:=Kn.next.left.lt (r.n.runs.comp ((Kn.unpack (α:=History)).comp Kn.first).left)

def work0 (x:Word)(a:Info):ℕ×ℕ:= ((dec a.2.1:ℕ×ℕ).1+1,r.post.f x ((dec a.1:History).1,a.2))
lemma workK:Kn r.work0:= ((Kn.unpack (α:=History)).comp Kn.next.left).left.succ.tuple
                 (r.post.runs.comp (((Kn.unpack (α:=History)).comp Kn.first).left.tuple Kn.next))

def solve :Cog:= .loop (gear _ r.condK) (.seq (Cargo.encase r.recipe r.prog) (etch _ r.workK))
def walk0 :Cog:= .seq (etch (α:=ℕ) (fun _ a=> ((0,a.2):ℕ×ℕ)) ((Kn.fix _).tuple Kn.next))
                         (.seq r.solve (etch (α:=ℕ×ℕ) (fun _ a=>a.2.2) Kn.next.right))

variable (p:Port)(t:ℕ)
def n0 := r.n.f p.l.x p.info
def poster (a b c:ℕ) := r.post.f p.l.x (p.info,enc ((a,b):ℕ×ℕ),c)

lemma round {p:Port}{t c u:ℕ} (h:p.OK)(ht:2≤ c)(v x:ℕ→ℕ)(he:v 0=u) (hn:Punct p c (r.n0 p))
   (hs:∀ i≤r.n0 p,Punct p c (v i))
   (hh:∀ i<r.n0 p,r.poster p i (v i) (x i)=v (i+1) ∧
              (Cargo.transit r.recipe p (enc (i,v i))).comp t c r.prog (p.s 0) (p.s (x i))):
    p.comp t (16*c) r.walk0 (p.s u) (p.s (v (r.n0 p))) := by
   let pay:=16*c
   have hc:1≤c:=by omega
   have hu :c≤pay:=by unfold pay; omega
   let z:=r.n0 p
   have hz(i:ℕ)(hi:i≤z):Punct p (4*c) (enc (i,v i)):=holdroom h
                       (by unfold Punct; exact le_trans (Nat.add_le_add_right (lb_mono hi) _) hn) (hs i hi)
   have hx(i:ℕ)(hi:i≤z):p.l.state pay ⟨p.w,t⟩ (p.s (enc (i,v i))):=
                            plight (punct_up (hz i hi) (by unfold pay; omega)) h (by omega)
   have hk (i:ℕ)(hi:i≤z):p.comp t pay r.solve (p.s (enc (i,v i))) (p.s (enc (z,v z))) := by
     have hd(i:ℕ) : (gear _ r.condK).f p.l.x (postcard p.info t,
                                           Pause (i,v i) p.src)=decide (i<z):=by
        rw [gear_at]; simp [postcard,z,cond0,n0]
     induction hi using Nat.decreasingInduction with
     | self=> exact .stop (by exact (hd _).trans (by simp)) (hx z le_rfl)
     | of_succ i hi ih=>
       obtain ⟨hj,hp⟩:=hh i hi
       have hA:=Cargo.aboard h (by omega:1 ≤4*c) (hz i hi.le)
                                               (hp.mono (D:=4*c) (by omega) hc)
       rw [show 4*(4*c)=pay by unfold pay; omega] at hA
       apply Lot.Mane.more ((hd _).trans (by simp [hi]))
                 (Lot.Mane.seq hA ?_) ih
       exact etches _ _ (i:=((enc (i,v i),x i):ℕ×ℕ)) (by simp [work0,postcard]; exact hj)
                       hA.spots.2 (hx _ hi)
   have h0: v 0=u:=he
   have hf:=hk 0 (Nat.zero_le _)
   subst u
   refine .seq (etches _ _ (i:=v 0) rfl ?_ hf.spots.1)
                 (.seq hf (etches _ _ (i:=(z,v z)) rfl hf.spots.2 ?_))
   · exact plight (punct_up (hs 0 (Nat.zero_le _)) hu) h (by omega)
   exact plight (punct_up (hs z le_rfl) hu) h (by omega)
end Camp
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill Finset
/-- Probe an actual finite-margin numerical question. -/
structure Badge where
   p : Cog
   k:Knob
   i:ℕ
   m:ℕ
   test:Cub (ℕ×Coin) ℕ

namespace Badge
variable (p:Badge)
def one : Oven:=
   ⟨fun b=>if b then ⟨_,Kn.fix 1⟩ else ⟨_,Kn.fix 0⟩,fun _=>⟨_,Kn.first⟩,⟨_,Kn.fix 0⟩,fun _=>p.p⟩

def dispatch (x:Word)(q:ℕ):ℕ:=
   let v:History:=dec q
   postcard v.1 (p.m*p.k.height.f x v.1)
lemma dispatchK: Kn p.dispatch:=by
    have hp:= (Kn.unpack (α:=History)).left
    exact Kn.wash.comp (hp.tuple ((Kn.fix _).times (p.k.height.runs.comp hp)))

abbrev cell (p:Badge)(x:Word)(q:ℕ)(v:Comb):Coin :=
    Coin.mult (scaleC p.k p.i x q) (Coin.place v.2.2.2.1 (v.2.1/2))
def valuep (x:Word)(a:Ream):ℕ:=
    let v:=(dec a.1:History).1
    p.test.f x (v,p.cell x v a.2)
lemma valueK : Kn p.valuep:= by
    have hp:= ((Kn.unpack (α:=History)).comp (Kn.first (β:=Comb))).left
    have ht:= Kn.next (α:=ℕ) (β:=Comb)
    exact p.test.runs.comp (hp.tuple (Coin.multK ((scaleK p.k p.i).comp hp)
            (Coin.placeK ht.right.right.right.left (ht.right.left.div (Kn.fix 2)))))

def check : Cog := .seq (Cog.ren ⟨_,p.dispatchK⟩ p.one.astir)
                                         (etch _ p.valueK)

def plan (s:Port)(_:ℕ):ℕ:= p.m*s.d
def tariffStart(c:ℕ):= c+p.m+100
def tariff(c:ℕ):= 4*Oven.price (p.tariffStart c)
lemma query {s c t V w} (h:Align s p.k)(hc:1 ≤ c)(ht:t=p.m*s.d)
   (hp:s.Feeds p.p c t w (V/massB p.i s.d))
   {j:ℕ}(hk:Punct s c j)
   (he:j=p.test.f s.l.x (s.info, Coin.mult (scaleC p.k p.i s.l.x s.info) (Coin.place (w t) (2^t)))) :
   Cargo.only0 s (p.tariff c) p.check (s.s 0) (s.s j):= by
   let u:=p.one
   let c1:=p.tariffStart c
   have h1:100 ≤ c1∧c ≤ c1:=by unfold c1 tariffStart; omega
   have hw:s.OK:=h.1
   have he1 : (p.one).Thaw s c1 t (fun b i=>w) (fun b i=> (V/massB p.i s.d)):=by
       refine ⟨h1.1,h.1,by change 0  ≤  _; omega,fun b=>?_,fun b i hi=>?_⟩
       · have hh : (p.one).labels s b ≤ 1:=by cases b <;>exact (by simp [one,Oven.labels])
         have hz:=growing (c1*s.d)
         apply lt_of_le_of_lt hh; have :=hw.1; nlinarith
       exact fewer hp hc h1.2 le_rfl
   have hs := he1.finds le_rfl rfl
   let v:Comb:=(t+1,2^(t+1),0,w t,0)
   have hf : s.comp t (Oven.price c1) p.one.astir (s.s 0) (Pause v s.src):= by
      convert hs using 1
      rw [p.one.finished]
      simp [v,one,Oven.labels,Oven.ext]
   have hz: 1 ≤  Oven.price c1∧ c ≤  Oven.price c1 ∧ p.m ≤  Oven.price c1:=by
      unfold c1 Oven.price Oven.bill tariffStart; omega
   have he0: Cargo.only0 s (p.tariff c) (Cog.ren ⟨_,p.dispatchK⟩ p.one.astir)
                                     (s.s 0) (Pause v s.src):= by
      apply Lot.Mane.pause (t:=t) _ hz.1 h.1.1 h.1.2.1 (ht ▸ Nat.mul_le_mul_right _ hz.2.2)
      exact Cog.renameR _ hf (by simp [dispatch,postcard,h.2.1,ht])
   apply Lot.Mane.seq he0
   refine etches _ _ (i:=v) ?_ he0.spots.2
         (plight (v:=j) (punct_up hk ?_) h.1 ?_)
   · have hu:2^(t+1)/2=(2:ℕ)^t:=by rw [pow_succ]; omega
     simp [v,valuep,postcard,he,hu,cell]
   · unfold tariff; change c ≤ 4*Oven.price c1; omega
   · unfold tariff; change 1 ≤ 4*Oven.price c1; omega

lemma accuracy {s V w t} (h:Align s p.k)(he:Checked w (V/massB p.i s.d) t):
   let x:= Coin.mult (scaleC p.k p.i s.l.x s.info) (Coin.place (w t) (2^t))
   |x.v - V|  ≤  massB p.i s.d * 2/(2:ℝ)^t:=by
   have hp:=abs_le.1 (he.2 t le_rfl)
   let Q:= (2:ℝ)^t; let R:=massB p.i s.d
   have hq:0<Q:=by unfold Q; positivity
   have hr:0<R:=mass0 ..
   dsimp only
   rw [Coin.mul0,Coin.place0 _ _ (Nat.one_le_pow _ _ (by omega)),scalen h]; push_cast
   change |R*((w t:ℝ)/Q)-V| ≤ R*2/Q
   have hf:(0:ℝ) ≤ R/Q:=by positivity
   have hg : R*((w t:ℝ)/Q)-V=(R/Q)*((w t:ℝ)-Q*(V/R)):= by field_simp
   rw [hg,abs_mul,abs_of_nonneg hf]
   rw [show R*2/Q=R/Q*2 by ring]; exact mul_le_mul_of_nonneg_left (he.2 t le_rfl) hf
end Badge
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill Analysis Finset

/-! Uniform simultaneous assurance across all permitted catalytic windings. -/
structure Seats where
    head : Port
    pass0 : ℕ → Prop
    hm : pass0 head.src

namespace Seats
variable (s:Seats)
abbrev d := s.head.d
abbrev l := s.head.l
abbrev info := s.head.info
abbrev seat (x:ℕ):Port:={s.head with src:=x}
def hasOK :=∀ x,s.pass0 x→(s.seat x).OK
def stable (k:Knob) :=∀ x,s.pass0 x → Align (s.seat x) k
abbrev panelx (v:ℕ):Seats:={s with head:={s.head with info:=v}}
abbrev bench (p:Branch)(i:ℕ):Seats:={s with head:=p.port s.head i}

@[simp] lemma home : s.seat s.head.src=s.head := rfl
lemma stable_home {s k} (h:stable s k):Align s.head k:=h _ s.hm
lemma has_home {s} (h:hasOK s):s.head.OK:=h _ s.hm
lemma rocks {s k} (h:stable s k):s.hasOK := fun x hx=>(h x hx).1

def loud (c T i:ℕ)(f:Cog)(V:ℝ)(w:Tape):= ∀ x,s.pass0 x→(s.seat x).Feeds f c T w (V/massB i s.d)
def band (c T i:ℕ)(f:Cog)(V:ℝ) :=∃ w,s.loud c T i f V w
lemma maxv {s c T i f V}(h: band s c T i f V): |V| ≤ massB i s.d:= by
    obtain ⟨w,h⟩:=h; exact amplitude (p:=s.head) (c:=c) (T:=T) (i:=i) (f:=f) ⟨w,h _ s.hm⟩
lemma flex {s c T i f V}(h:band s c T i f V) {D H}(he:1≤c)(hk:c≤D)(hh:H≤T):band s D H i f V:=by
    obtain ⟨w,h⟩:=h; exact ⟨w,fun x hx=> fewer (h x hx) he hk hh⟩
abbrev freq (s:Seats) (p:Branch):=p.S s.head
def full (s:Seats)(p:Branch)(V:ℕ→ℝ)(i c H:ℕ)(f:Cog):=
      p.n.f s.l.x s.info < (2:ℕ)^(p.e*s.d) ∧ ∀ j∈ s.freq p,(s.bench p j).band c H i f (V j)
lemma located {s p i c H f V} (h: full s p V i c H f):∃ w,∀ x,s.pass0 x→ p.Faith (s.seat x) i V c H f w:=by
    classical
    have he(j):∃ w,∀ x,s.pass0 x → ∀ e:j∈s.freq p,
          ((s.bench p j).seat x).Feeds f c H w (V j/massB i s.d):=by
       by_cases hi:j∈s.freq p
       · obtain ⟨w,h1⟩:=h.2 j hi; exact ⟨w,fun x hx _=> h1 x hx⟩
       exact ⟨fun _=>0,fun _ _ hz=> (hi hz).elim⟩
    choose w hw using he
    exact ⟨w,fun x hx=>⟨h.1,fun j e=>hw j x hx e⟩⟩
lemma leasedD {s p i c H f V} (h:full s p V i c H f) (hc:1≤c)(he:hasOK s):
     s.band (powder (Survey.priceB (c+p.e+100))) H i (p.bowl f).poll (rank (s.freq p) V (p.key s.head)):= by
    obtain ⟨w,h⟩:=located h
    exact ⟨fun t=> rankN (s.freq p) (fun j=>(w j t).toNat) (p.key s.head), fun x hx=>
             p.leased (h x hx) hc (he x hx)⟩
lemma rhymeD {s:Seats}{p i c H f V k} (h:s.full p V i c (H+p.reserve*s.d) f) (hc:1≤c)(he:stable s k):
     s.band (powder (Oven.price (p.foldC c))) H (i+p.e) ((p.collect f k i).cooked) (∑ j∈s.freq p,V j):=by
    obtain ⟨w,h⟩:=located h
    exact ⟨(p.collect f k i).out s.head (fun _ j=>w j),fun x hx=> p.poems (h x hx) hc (he x hx)⟩
lemma duetD (p:Bid){s:Seats}{k i j o e c H f g V X} (h:stable s k)(he:p.Fit e i j)(hc:1≤ c)
    (h1:s.band c (H+(e+i+j+6)*s.d) i f V)(h2:s.band c (H+(e+i+j+6)*s.d) j g X)
    (hv:|p.truef V X| ≤ massB o s.d):
    s.band (powder (Oven.price (Bid.joinCost e i j c))) H o (p.uPair k i j o e f g).cooked (p.truef V X):=by
    obtain ⟨w,h1⟩:=h1; obtain ⟨b,h2⟩:=h2
    exact ⟨(p.uPair k i j o e f g).out s.head (fun t _=> if t then w else b),
            fun x hx=> p.fixedjoint (h x hx) he hc (h1 x hx) (h2 x hx) hv⟩

def hear (t c:ℕ)(q:Cog)(v y:ℕ):=∀ x,s.pass0 x→(s.seat x).comp t c q (v,x) (y,x)
abbrev rite (s:Seats)(c:ℕ)(q:Cog)(u:ℕ):=s.hear 0 c q 0 u

lemma avis {s:Seats}{c b q t v i f g} (h: rite s c q b)
    (ha:b=0→s.band c t i g v)(hb:b≠0→s.band c t i f v):
    s.band c t i (Cargo.choose q g f) v:=by
    by_cases hz:b=0
    · obtain ⟨w,hA⟩:=ha hz
      refine ⟨w,fun x hx=>?_⟩
      obtain ⟨ha,ht⟩:=hA x hx
      refine ⟨ha,⟨fun k hk=>?_⟩⟩
      have hc:=Cargo.expands (p:=s.seat x) (h x hx) (t:=k)
      have he:=ht.digits k hk
      refine .seq hc (.yes (show decide (b=0)=true by simp [hz]) (.seq ?_ he))
      exact etches _ _ (i:=b) rfl hc.spots.2 he.spots.1
    obtain ⟨w,hA⟩:= hb hz
    refine ⟨w,fun x hx=>?_⟩
    obtain ⟨ha,ht⟩:=hA x hx
    refine ⟨ha,⟨fun k hk=>?_⟩⟩
    have hc:=Cargo.expands (p:=s.seat x) (h x hx) (t:=k)
    have he:=ht.digits k hk
    refine .seq hc (.no (show decide (b=0)=false by simp [hz]) (.seq ?_ he))
    exact etches _ _ (i:=b) rfl hc.spots.2 he.spots.1

abbrev berth (C:Cub History ℕ)(s:Seats)(b:ℕ):Seats:=s.panelx (C.f s.l.x (s.info,b))

lemma advises {s:Seats}{c b q g C i t v}
   (hp:s.hasOK) (hb:Punct s.head c b)(hc:1≤c)(h:s.rite c q b)
   (ha:(berth C s b).band c t i g v):
    s.band (4*c) t i (Cargo.combine q g C) v:=by
   obtain ⟨w,ha⟩:=ha
   refine ⟨w,fun x hx=>?_⟩
   obtain ⟨hv,he⟩:=ha x hx
   refine ⟨hv,⟨fun k hk=>?_⟩⟩
   have hz:=he.digits k hk
   have ht:=Cargo.aboard (f:=C) (t:=k) (v:=b) (hp x hx) hc hb hz
   have hu := (Cargo.expands (p:=s.seat x) (t:=k) (h x hx)).mono (D:=4*c) (by omega) hc
   refine .seq hu (.seq ht ?_)
   exact etches _ _ (i:=((b,enc (dsign w k)):History)) rfl ht.spots.2
                         (hz.mono (c:=c) (D:=4*c) (by omega) hc).spots.2
end Seats

namespace Lyric
open Seats
inductive Chor (p:Knob)(c T:ℕ) : Seats → Lyric → ℝ → Prop where
   | byear {s r f V} :
       s.band c T r f V → Chor p c T s (.use r f) V
   | played {s i f v}(h:stable s p)(e:Live s.head p T)
       (hz:∀ x,s.pass0 x→ f.f s.l.x (s.info,x)=v)
       (hb: |v.v| ≤ massB i s.d):
          Chor p c T s (.solo i f) v.v
   | doo {s i j A B u o} (h:stable s p)
       (ha:Chor p c T s i A) (hb:Chor p c T s j B) (hr:|u.val A B| ≤ massB o s.d):
              Chor p c T s (.duet u i j o) (u.val A B)
   | little {s q f V b} (h:stable s p)
       (he:q.n.f s.l.x s.info<(2:ℕ)^(q.e*s.d)) (hg:∀ i∈s.freq q,Chor p c T (s.bench q i) f (V i)):
               Chor p c T s (.heap b q f) (if b then ∑ i∈ s.freq q,V i else rank (s.freq q) V (q.key s.head))

lemma sing {p c T s f V}(h:Chor p c T s f V)(hc:1≤c) {H:ℕ} (he:H+f.tail*s.d≤T):
     s.band (f.cost c) H f.weight (choir p f) V := by
   induction h generalizing H with
   | @byear s i q v h=> apply flex h hc le_rfl; exact (Nat.le_add_right ..).trans he
   | @played s i f v h hl hz hb=>
     refine ⟨Brick.tapeR p f i s.head,fun x hx=>?_⟩
     have ht:Brick.tapeR p f i (s.seat x)=Brick.tapeR p f i s.head:=by
         funext j; unfold Brick.tapeR Brick.center
         simp only [postcard,dec_round]
         change Coin.floor0 (Coin.mult _ (Coin.mult (f.f s.l.x (s.info,x)) _)) =
                      Coin.floor0 (Coin.mult _ (Coin.mult (f.f s.l.x (s.info,s.head.src)) _))
         rw [hz x hx,hz _ s.hm]
     rw [← ht]
     have hp:H≤T :=(Nat.le_add_right ..).trans he
     exact Brick.each0 p f i (s.seat x) H (h x hx) ((Nat.pow_le_pow_right Nat.zero_lt_two hp).trans hl)
                      (congrArg Coin.v (hz x hx)) hb
   | @doo s i j A B u o h h1 h2 h3 ia ib=>
     let z:=pulse i.weight j.weight
     let v:= H+z*s.d
     have hp:v+max (tail i) (tail j)*s.d ≤ T:=by
          change H+(z+max i.tail j.tail)*s.d ≤ T at he
          unfold v; rwa [add_mul,← add_assoc] at he
     have hi : v+(tail i)*s.d ≤ T := by
         apply le_trans _ hp
         gcongr; exact le_max_left ..
     have hj : v+(tail j)*s.d ≤ T:=by
         apply le_trans _ hp
         gcongr; exact le_max_right ..
     apply duetD u.ration h (u.legit ..) ((cost_hi (p:=i) hc).trans (le_max_left ..)) _ _ h3
     · exact flex (ia hi) (cost_hi hc) (le_max_left ..) le_rfl
     exact flex (ib hj) (cost_hi hc) (le_max_right ..) le_rfl
   | @little s q f V b h hz hf ih=>
     have hp:s.full q V f.weight (f.cost c) (H+(if b then q.reserve else 0)*s.d) (choir p f):= by
         refine ⟨hz,fun j hj=>ih j hj ?_⟩
         unfold tail at he; rwa [add_mul,← add_assoc] at he
     cases b
     · simp only [choir,cost,weight,Bool.false_eq_true,ite_false]
       simp only [Bool.false_eq_true,ite_false,zero_mul,add_zero] at hp
       exact leasedD hp (cost_hi hc) (rocks h)
     simp only [choir,cost,weight,ite_true]
     exact rhymeD hp (cost_hi hc) h

lemma Chor.nominal {p c T s f V}(h:Chor p c T s f V):Lethe p c T s.head f V:=by
    induction h with
    | @byear s r f V h=>
      obtain ⟨w,h⟩:=h; exact .byear ⟨w,h _ s.hm⟩
    | @played s i f v h e hz hb=>
      have hu:f.f s.l.x (s.info,s.head.src)=v:=hz _ s.hm
      subst v; exact .played (stable_home h) e hb
    | doo h _ _ hi ih ik=> exact .doo (stable_home h) ih ik hi
    | little h he _ hi=> exact .little (stable_home h) he hi
lemma Chor.minuet {p c T s i j A B}(h:Chor p c T s i A)(e:Chor p c T s j B) (hs:stable s p)(op:Doop):
    Chor p c T s (bi op i j) (op.val A B):=
   .doo hs h e (op.geom _ _ s.d (stable_home hs).1.1 h.nominal.bnd e.nominal.bnd)

end Lyric
end ExactDerandomization.Fret

end

section

namespace ExactDerandomization.Fret
open Relay Counter Rill Analysis Finset

namespace Seats
lemma higher {s c t q x y i} (h:hear s t c q x y)(hp:1 ≤ c)(he:c ≤ i):hear s t i q x y:=
   fun x hx=>(h x hx).mono he hp
lemma pointed0 {s c v k} (hp:hasOK s) (he:2 ≤ c)(ht:Punct s.head c v)(hz:Punct s.head c k):
   s.hear 0 c (etch (α:=ℕ) (fun _ _=>k) (Kn.fix _)) v k:=fun x hx=>
   etches _ _ (i:=v) rfl (plight ht (hp x hx) (by omega)) (plight hz (hp x hx) (by omega))
abbrev nothingX := Cargo.knock
lemma blankD {s c}(h:hasOK s)(he:2 ≤ c):s.rite c nothingX 0:=
   pointed0 h he (punct0 (has_home h) he) (punct0 (has_home h) he)

lemma steer {s c z q f g b} (h:rite s c q z)
    (ha:z=0→s.rite c f b)(hb:z≠0→s.rite c g b):
    s.rite c (Cargo.choose q f g) b:=by
   intro x hx
   have hu:=Cargo.expands (p:=s.seat x) (h x hx) (t:=0)
   by_cases he:z=0
   · have hz:=ha he x hx
     exact .seq hu (.yes (show decide (z=0)=true by simp [he])
             (.seq (etches _ _ (i:=z) rfl hu.spots.2 hz.spots.1) hz))
   have hz:=hb he x hx
   exact .seq hu (.no (show decide (z=0)=false by simp [he])
            (.seq (etches _ _ (i:=z) rfl hu.spots.2 hz.spots.1) hz))
abbrev transformed (P:Cub ℕ ℕ)(f:Cog) := Cog.ren ⟨_,Cargo.switchK P⟩ f
lemma importD (P:Cub ℕ ℕ){s:Seats}{t c q x y v}(e:P.f s.l.x s.info=v)
    (h:hear (panelx s v) t c q x y):s.hear t c (transformed P q) x y:=by
   intro z hz
   refine Cog.renameR _ (h z hz) ?_
   change Cargo.switch P s.l.x _=postcard v t
   simp [Cargo.switch,postcard,e]
lemma transportD (P:Cub ℕ ℕ){s:Seats}{T i f c x v}(e:P.f s.l.x s.info=v)
   (h:band (panelx s v) c T i f x):s.band c T i (transformed P f) x:=by
   obtain ⟨w,h⟩:=h
   have hh(t:ℕ)(ht:t ≤ T):hear (panelx s v) t c f 0 (enc (dsign w t)):=
       fun z hz=>(h z hz).2.digits t ht
   exact ⟨w,fun z hz=> ⟨(h z hz).1,⟨fun t ht=>importD P e (hh t ht) z hz⟩⟩⟩

end Seats

open Seats

/-- Pick the zero-based kth nonzero answer; the pair of index and answer is positive, or 0 if none. -/
structure Seek where
    b:Branch
    mask:Cog

namespace Seek
variable (s:Seek)
abbrev bin (i z:ℕ):ℕ := enc (i,z)
lemma binpos (i z) : 0<bin i z:=lt_trans Nat.zero_lt_one (cord_fine _ _).2.2
abbrev SeqN := ℕ×ℕ
def transfer (k i x:ℕ) (v:SeqN):SeqN:=
   if x=0 then v else (v.1+1,if v.1=k then bin i x else v.2)

def relief (v:ℕ→ ℕ)(k:ℕ):ℕ→SeqN
    | 0=>(0,0)
    | i+1=>transfer k i (v i) (relief v k i)
def part (v:ℕ→ℕ)(i:ℕ): Finset ℕ:= (range i).filter fun j=>v j≠0

lemma heightp (v k i):(relief v k i).1 = (part v i).card:=by
   induction i with
   | zero=>simp [relief,part]
   | succ i ih=>
     have hh : part v (i+1) = if v i ≠ 0 then insert i (part v i) else part v i:=by
                   unfold part; rw [range_add_one,filter_insert]
     by_cases he:v i=0
     · simp [relief,transfer,he,ih,hh]
     have hm:i ∉ part v i:=by simp [part]
     simp [relief,transfer,he,ih,hh,hm]
lemma countle (v i):(part v i).card  ≤  i:=by simpa [part] using card_filter_le (range i) (fun j=>v j≠0)
lemma catalogs {v:ℕ→ℕ}{i j:ℕ}(h:i ≤ j):part v i ⊆ part v j:=by unfold part; gcongr
lemma ticket {v:ℕ→ℕ}{k i:ℕ} (hi:i<k)(he:v i≠0): (part v i).card < (part v k).card:=by
    apply card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨catalogs hi.le,fun h=>?_⟩
    have hm:i∈part v k:=by simp [part,hi,he]
    rw [← h] at hm; simp [part] at hm
lemma order {v:ℕ→ℕ}{k i j:ℕ}(hi:i<j) (he:v i≠0)(ht:(part v i).card=k):
     (relief v k j).2=bin i (v i):=by
    induction hi with
    | refl=> simp only [relief,transfer,ite_eq_right he,heightp,ht,ite_true]
    | @step j hi ih=>
      have hh : (relief v k j).1≠ k:=by rw [heightp,← ht]; exact ne_of_gt (ticket hi he)
      simp only [relief,transfer,hh,ite_false]
      split <;> exact ih
lemma found_min {v:ℕ→ℕ}{k j:ℕ} (ht:k < (part v j).card):
    ∃ i∈part v j, (part v i).card=k:=by
   induction j with
   | zero=>simp [part] at ht
   | succ j ih=>
     by_cases he:k < (part v j).card
     · obtain ⟨i,h,e⟩:=ih he; exact ⟨i,catalogs (by omega) h,e⟩
     rw [←heightp v k] at he ht
     rw [relief,transfer] at ht
     split at ht
     · contradiction
     next h=>
       refine ⟨j,by simp [part,h],?_⟩
       dsimp only at ht; simp_rw [heightp] at ht he; omega
lemma missed {v:ℕ→ℕ}{k j:ℕ}: (relief v k j).2=0 ↔ (part v j).card  ≤  k:=by
   constructor
   · intro h; by_contra! hc
     obtain ⟨i,hx,hv⟩:=found_min hc
     obtain ⟨hx,hz⟩:=mem_filter.1 hx
     rw [order (mem_range.1 hx) hz hv] at h; have := binpos i (v i); omega
   intro h
   induction j with
   | zero=>rfl
   | succ j ih=>
      have he:(relief v k j).2=0:=ih (le_trans (card_le_card (catalogs (by omega))) h)
      by_cases hs:v j=0
      · simpa [relief,transfer,hs]
      have hv : (part v j).card<k:=lt_of_lt_of_le (ticket (k:=j+1) (by omega) hs) h
      simp [relief,transfer,hs,heightp,ne_of_lt hv,he]

lemma casebook (v k i):(relief v k i).2=0 ∨ ∃ j∈part v i,
                (part v j).card=k ∧ (relief v k i).2=bin j (v j):=by
   rcases le_or_gt (part v i).card k with hh|hh
   · exact Or.inl (missed.2 hh)
   obtain ⟨j,h1,h2⟩:=found_min hh; obtain ⟨hx,he⟩:=mem_filter.1 h1
   exact Or.inr ⟨_,h1,h2,order (mem_range.1 hx) he h2⟩

abbrev grainK {α} [Wire α] {p g f:PT α ℕ} {q:PT α SeqN}
   (hp:Kn p)(hg:Kn g)(hf:Kn f)(hq:Kn q): Kn (fun x a=> transfer (p x a) (g x a) (f x a) (q x a)):= by
    have hi:=Kn.wash (α:=SeqN)
    have hh:Kn (fun x a=> if (q x a).1=p x a then bin (g x a) (f x a) else (q x a).2):=
       by simpa only [decide_eq_true_eq] using ((hq.left.eq hp).cond (hi.comp (hg.tuple hf)) hq.right)
    simpa only [transfer,decide_eq_true_eq] using ((hf.eq (Kn.fix 0)).cond hq (hq.left.succ.tuple hh))

def fill (x:Word)(a:Camp.Info):ℕ:=
   let (i,r):History:=dec a.2.1
   binBoth (transfer (s.b.k.f x a.1) i a.2.2 (dec r))
 where binBoth (v:SeqN) := enc v
lemma fillK:Kn s.fill:= by
   have h:= (Kn.unpack (α:=History)).comp (Kn.next (β:=History) (α:=ℕ)).left
   exact Kn.wash.comp (grainK (s.b.k.runs.comp Kn.first) h.left Kn.next.right (Kn.unpack.comp h.right))

def road (x:Word)(a:History):ℕ:= s.b.route.f x (a.1,(dec a.2:History).1)
lemma roadK:Kn s.road:=
   s.b.route.runs.comp (Kn.first.tuple ((Kn.unpack (α:=History)).comp Kn.next).left)

def tent :Camp:=⟨s.b.n,⟨_,s.roadK⟩,s.mask,⟨_,s.fillK⟩⟩
def latch := Cog.seq (etch (α:=ℕ) (fun _ _=>((0,0):SeqN)) (Kn.fix _)) (.seq s.tent.walk0
                (etch (α:=SeqN) (fun _ a=>a.2.2) Kn.next.right))
variable (p:Seats)
abbrev N:=s.b.n.f p.l.x p.info

lemma earns {c}{p:Seats} (h:p.hasOK)(hc:2 ≤ c)(v:ℕ→ ℕ)
     (he:Punct p.head c (s.N p))
     (hp:∀ i<s.N p,Punct p.head c (v i) ∧ (p.bench s.b i).rite c s.mask (v i)):
    let z:=(relief v (s.b.key p.head) (s.N p)).2
    Punct p.head (4*c) z ∧ p.rite (16*(16*c)) s.latch z:=by
   let k:=s.b.key p.head; let m:=s.N p; let w:= relief v k
   have ha:= has_home h
   have hk(i)(hi:i ≤ m) : Punct p.head c i:=by
            unfold Punct; exact le_trans (Nat.add_le_add_right (lb_mono hi) _) he
   have hw(i)(hi:i ≤ m) : Punct p.head (4*c) (w i).2:=by
      rcases casebook v k i with hh|⟨j,h1,-,hg⟩
      · change (w i).2=0 at hh; rw [hh]; exact punct0 ha (by omega)
      change (w i).2=bin j _ at hg; rw [hg]; have he:=lt_of_lt_of_le (mem_range.1 (mem_filter.1 h1).1) hi
      exact holdroom ha (hk j he.le) (hp j he).1
   have hh (i)(hi:i ≤ m): Punct p.head (16*c) (enc (w i)):=by
        have ht : (w i).1 ≤ m:=by change (relief v k i).1 ≤ m; rw [heightp]; exact (countle ..).trans hi
        have he:= holdroom ha (punct_up (hk _ ht) (show c ≤ 4*c by omega)) (hw i hi)
        convert he using 1 ; grind
   dsimp only; refine ⟨hw m le_rfl,fun x hx=>?_⟩
   have hz:=h x hx
   have hr:=s.tent.round (t:=0) (p:=p.seat x) hz (by omega:2 ≤ 16*c) (fun i=>enc (w i)) v rfl
        (vscale he) (fun i hi=>hh i hi) (show ∀ i < s.tent.n0 (p.seat x),
        _ from fun i hi=> by
          have hn:i < m:=hi
          have hs:= ((hp i hn).2 x hx).mono (D:=16*c) (by omega) (by omega)
          constructor
          · unfold Camp.poster tent fill; simp only [dec_round]; rfl
          convert hs using 1 <;> simp [Cargo.transit,tent,road,seat,Branch.port])
   unfold Port.comp at *
   refine .seq (etches _ _ (i:=0) rfl ?_ hr.spots.1) (.seq hr
              (etches _ _ (i:=w m) rfl hr.spots.2 ?_))
   · exact plight (punct0 hz (by omega)) hz (by omega)
   exact plight (punct_up (hw m le_rfl) (by omega)) hz (by omega)
 where
    vscale {c n p}(e:Punct p c n): Punct p (16*c) n:=punct_up e (by omega)
end Seek
end ExactDerandomization.Fret

end

end OAI
