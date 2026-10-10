import OAI.Computability.Logspace.EstimatorBounds

namespace OAI

/-!
Error bounds for products, rank queries, and transported estimator values.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Bounded row atoms in the common environment. -/
set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie Buf At Finset

variable {n : ℕ} [Fact n.Prime]
def crossP : Equiv.Perm (Pool n) :=
    let t : Pool n→ Pool n := fun ⟨x,y,w⟩=> (y,x,w)
    ⟨t,t,fun _=>rfl,fun _=>rfl⟩
def leftP : Equiv.Perm (Pool n) :=
    let t : Pool n→ Pool n := fun ⟨x,y,z,w⟩=> (x,z,y,w)
    ⟨t,t,fun _=>rfl,fun _=>rfl⟩
def rightP : Equiv.Perm (Pool n) :=
    let t : Pool n→ Pool n := fun ⟨x,y,z,w⟩=> (z,y,x,w)
    ⟨t,t,fun _=>rfl,fun _=>rfl⟩

def ratioN (k l) := box (k-l)
lemma upper_flip {k l : ℕ} (h:l≤k) (N) :
   scaleM N k = ratioN k l^4*scaleM N l := by
   unfold ratioN
   rw [← swell h]
   unfold scaleM
   obtain hn|hn:=Nat.eq_zero_or_pos N
   · simp [hn]
   have hK := (rate_pos k).ne'; have hL := (rate_pos l).ne'
   field_simp

structure Tile (d : Axis) (K : ℝ) (D : ℕ) (f : Pics n) : Prop where
   cap : RCap K f
   falls : ∀ s x y,f s x y≠0 → x∈src d.S d.u s ∧ y∈dst d.S d.a s
   rows : ∀ s x (S : Domain), (S.filter fun y=> f s x y≠0).card≤D

def Shelf (D : ℕ) (f : Pics n) := ∀ s y (S:Domain),(S.filter fun x=> f s x y≠0).card≤D

lemma tile_zero (d : Axis) {K : ℝ} (h:0≤K) (D) : Tile d K D (n:=n) (fun _ _ _=>0) :=
   ⟨fun _ _ _ =>by simp [fourth,h], fun s x y =>by simp,fun s x S=>by simp⟩
omit [Fact (Nat.Prime n)] in
lemma shelf_zero (D) : Shelf D (n:=n) (fun _ _ _=>0):=by unfold Shelf; simp
lemma Tile.extend {d : Axis} {K L : ℝ} {u p} {f:Pics n} (h:Tile d K u f) (he:K≤L)
    (hp:u≤p) : Tile d L p f :=
       ⟨fun x i j=> ⟨(h.cap x i j).1,(h.cap x i j).2.trans he⟩,h.falls,
         fun s x S=> (h.rows s x S).trans hp⟩

abbrev flaw (f g : Pics n) : Pics n :=
    fun s i j=> fourth (f s i j)-fourth (g s i j)
abbrev flawV (f g : Paint n) : Paint n := fun s i=>fourth (f s i)-fourth (g s i)

namespace Axis
variable (d : Axis)

abbrev startd (a : ℕ) : Axis := {d with u:=a}
lemma vsmall (u : ℕ) (h:u≤d.u) (f : Paint n) :
    d.von f ≤ ratioN d.u u * (d.startd u).von f := by
   let c:=ratioN d.u u
   have ht : 0≤c:= (box0 _).le
   change _≤c*_
   apply (d.vm_le (mul_nonneg ht ((d.startd u).vn0 _))).2
   rw [mul_pow,Axis.von_four,d.vi_apply,vi_apply,upper_flip h _]
   rw [mul_assoc]
   refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (av_mono ?_) (scaleM_nn ..)) (by positivity)
   intro i; apply sum_le_sum_of_subset_of_nonneg (fun j hj=>?_) (fun j _ _=>by positivity)
   obtain ⟨he,hj⟩ := mem_filter.1 hj; exact mem_filter.2 ⟨he,contained _ u h hj⟩
lemma tsmall (u : ℕ) (h : d.a ≤ u) (f : Pics n) :
    (d.narrowed u).ton f≤d.ton f := by
   apply ((d.narrowed u).tm_le (d.tn0 _)).2
   rw [d.ton_four]
   apply d.vi_mono
   intro i j hi
   apply sum_le_sum_of_subset_of_nonneg (fun j hj=> ?_) (fun j _ _=>by positivity)
   obtain ⟨he,hj⟩:=mem_filter.1 hj; exact mem_filter.2 ⟨he,contained _ _ h hj⟩

lemma tperm (e:Equiv.Perm (Pool n)) (f : Pics n) :
   d.ti f=scaleM d.N d.u * av (fun s=>∑ i∈src d.S d.u (e s),
                              ∑ j∈dst d.S d.a (e s), f (e s) i j) := by
   rw [ti_apply]
   congr 1; exact (av_perm e (fun s=>∑ i∈src d.S d.u s,∑ j∈dst d.S d.a s,f s i j)).symm

lemma vperm (e:Equiv.Perm (Pool n)) (f : Paint n) :
   d.vi f=scaleM d.N d.u * av (fun s=>∑ i∈src d.S d.u (e s),f (e s) i) := by
   rw [vi_apply]; congr 1; exact (av_perm e _).symm

lemma ti_add (f g : Pics n) : d.ti (fun s i j=>f s i j+g s i j)=d.ti f+d.ti g :=
    Meter.add ..
lemma vi_add (f g : Paint n) : d.vi (fun s i=> f s i+g s i)=d.vi f+d.vi g := Meter.add ..

lemma tvh {p : Paint n} (h:2^d.u ≤ n) (he:d.S.card≤d.N)
    (hv:∀ u x,in01 (p u x)) : d.von p≤ 2 := by
   apply (d.vm_le (by norm_num)).2
   refine le_trans ?_ (by norm_num : (16:ℝ) ≤ (2:ℝ)^4)
   apply le_trans _ (vi_one (n:=n) (w:=0) d h he)
   apply d.vi_mono; intro s i hi
   exact le_trans (pow_le_pow_left₀ (hv s i).1 (hv s i).2 4) (by norm_num)

/-- trivial root error against zero -/
lemma zero_root {K : ℝ} {D : ℕ} (h:2^d.u≤n) (he:d.S.card≤d.N)
    {f : Pics n} (hv:Tile d K D f) (hp:1≤K) :
     d.terr f (fun _ _ _=>0) ≤ 2*K*(D+1:ℝ) := by
   unfold terr
   apply (d.tm_le (by positivity)).2
   let g u i j := f u i j
   have hz (u) (i) :
      ∑ j∈dst d.S d.a u,(fourth (g u i j)-fourth 0)^4 ≤ (D:ℝ)*K^4 := by
     let T:=dst d.S d.a u
     let S:= T.filter (fun j=>f u i j≠0)
     rw [← sum_subset (s₁:= S) (s₂:=T) (filter_subset ..)]
     · have hi:S.card≤ D:=hv.rows ..
       calc
        _ ≤ ∑ j∈S,K^4 := sum_le_sum fun j _=>by
                  rw [show fourth 0=0 by simp [fourth],sub_zero]
                  exact pow_le_pow_left₀ (fourth_nn _) ((hv.cap u i j).2) _
        _ ≤ _ := by simp only [sum_const,nsmul_eq_mul]
                    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hi) (by positivity)
     · intro j hj hh
       have he : g u i j=0:=by unfold S g at *; by_contra he; exact hh (mem_filter.2 ⟨hj,he⟩)
       rw [he]; norm_num
   let u:= (D:ℝ)*K^4
   apply le_trans (d.vi_mono (fun s i _=> hz s i))
   change d.vi (fun _ _=>u)≤_
   have he1 : d.vi (n:=n) (w:=0) (fun _ _=>u)=u*(d.vi (n:=n) (w:=0) fun _ _=>1):= by
      simpa only [mul_one] using d.vmul (n:=n) (w:=0) (fun _ _=> 1) u
   rw [he1]; apply le_trans (mul_le_mul_of_nonneg_left (d.vi_one h he) (by dsimp only [u]; positivity))
   have hh1 : 0≤ (D:ℝ) := by positivity
   have hh2 : (D:ℝ)≤ (D+1:ℝ)^4 := by nlinarith [sq_nonneg ((D:ℝ)^2)]
   unfold u; linarith [mul_le_mul_of_nonneg_right hh2 (show 0≤K^4 by positivity)]

end Axis

structure Builder (d : Axis) where
   p : Const
   t : ℕ
   tau : ℝ
   c : Bool

namespace Builder
variable {d : Axis} (f : Builder d)
abbrev Block (n:ℕ) := Pool n→ℕ→Blob
def sess (u:Pool n) : Grid := ⟨f.p,f.tau,src d.S d.u u,dst d.S d.a u,dst d.S f.t u,f.c⟩
def coins (g:Block n) (v:Trio) (b:Bool) : Pics n := fun u=> (f.sess u).pre (g u) v b
def wrapped (g:Block n) (v:Trio) (b:Bool) (w:Paint n) : Pics n :=
    fun u=> (f.sess u).result (g u) v b (w (crossP u))

lemma tiling {C v} (g:Block n) (hb: TS f.tau C v) (ht:0<f.tau) (b : Bool) :
    Tile d (C^3) f.p.K (f.coins g v b) := by
    refine ⟨fun s i j=>?_,fun s i j e=>(Grid.pre_support _ _ hb ht _ _ e),
                       fun s x S=>(f.sess s).pre_count (g s) hb ht x S⟩
    unfold coins Grid.pre; split
    · exact ⟨hb.nn ..,hb.rootub ..⟩
    have he:0≤C^3:=pow_nonneg (by linarith [hb.start.one]) _
    norm_num [fourth,he]
lemma tiling_out {C v} (g:Block n) (hb:TS f.tau C v) (ht:0<f.tau)
    (b : Bool) (w : Paint n) (h : ∀ s i,in01 (w s i)) :
    Tile d (C^3) f.p.K (f.wrapped g v b w) := by
   have he:= f.tiling g hb ht b
   have hh (s i j) : f.wrapped g v b w s i j≠0 → f.coins g v b s i j≠0 :=
      fun e hi=> e (show f.coins g v b s i j*_ *_=0 from by rw [hi]; ring)
   refine ⟨fun s i j=>?_,fun s i j e=>he.falls s i j (hh s i j e),fun s i S=>le_trans
      (card_le_card ?_) (he.rows s i S)⟩
   · obtain ⟨h1,h2⟩:=he.cap s i j
     let a:=f.coins g v b s i j
     let c:=(f.sess s).incG (g s) j
     let r:=w (crossP s) j
     change 0≤a*c*r ∧ fourth (a*c*r)≤_
     have hh:in01 c:= Grid.incG_bounds ..
     have hv:in01 r:=h _ _
     obtain ⟨hs1,hs2⟩:=hh; obtain ⟨hx1,hx2⟩:=hv
     have hA:0≤a:=h1
     refine ⟨by positivity,(fourth_mono (b:=a) ?_).trans h2⟩
     have he : a*c≤a:=by nlinarith
     nlinarith [show 0≤a*c by positivity]
   intro x hi
   exact mem_filter.mpr ⟨(mem_filter.1 hi).1,hh s i x (mem_filter.1 hi).2⟩

lemma fromshelf (g:Block n) {v} (ht:0<f.tau) (h:f.c=true)
    (b B : Bool) (w: Paint n)
    (hw : ∀ x≤f.tau/2,v x=0) :
    Shelf (clim f.p) (f.wrapped g (mainT f.tau v B) b w) := by
   intro s j S
   let p:=f.sess s
   let G : ℕ→Blob.Guess:=fun x=>⟨fun y=> ((g s x).ts y).1,(g s x).rk p.dst p.p.K⟩
   have he : p.Agree (g s) G := by
      intro x _
      change Blob.acc _ _ _ _ f.tau
      simp [G,Blob.acc,show 0≤f.tau/10000 by positivity]
   apply le_trans (card_le_card ?_) (p.degree_in G j h S)
   intro x hx; obtain ⟨h1,h2⟩:=mem_filter.1 hx
   exact mem_filter.2 ⟨h1,p.nonzero_present (g s) ht he hw h2⟩

lemma bolts {g:Block n} {v} {w : Paint n} :
    d.pinned f.t (f.wrapped g v true w) := by
   apply d.realize_pin; intro s i j
   unfold wrapped Grid.result Grid.pre
   split
   · next he=>
     intro _
     obtain ⟨ha,hb,hc⟩:=he
     exact hc.resolve_left (by simp)
   · intro h; exact False.elim (h (by ring))

end Builder

end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

variable {n : ℕ} [Fact n.Prime]

def peeler (n k : ℕ) := rate k / pct n k
lemma spins {k : ℕ} (h : 2^k≤n) : in01 (peeler n k) :=
   ⟨(div_pos (rate_pos _) (pct_pos (NeZero.pos _) _)).le,
     (div_le_one (pct_pos (NeZero.pos _) _)).mpr (pct_bounds h).1⟩

lemma spliff (x y : ℝ) : (x+y)^4≤8*(x^4+y^4) := by
   have e := Analysis.even4 x y
   linarith [show 0≤(x-y)^4 by positivity]

/-- Product split using final support of F and initial support of G.
For a product-stochastic pair use mixture contraction individually per path. -/
lemma split_product {K x y p q : ℝ} (hx:0≤x) (_:0≤y)
    (hp:0≤ p) (_:0≤ q) (hb:fourth p ≤ K) (he:fourth y≤K) :
    (fourth (x*y)- fourth (p*q))^4 ≤
      8*K^4*((if y≠0 then (fourth x-fourth p)^4 else 0)
                     +(if p≠0 then (fourth y-fourth q)^4 else 0)) := by
   let a:=fourth x; let b:=fourth y; let c:=fourth p; let d:=fourth q
   rw [fourth_mul hx,fourth_mul hp]
   change (a*b-c*d)^4≤ _
   have hu {v : ℝ} (h:fourth v≤K) (x : ℝ) :
         (fourth v*x)^4 ≤ K^4*(if v≠0 then x^4 else 0) := by
      by_cases he:v=0
      · simp [he,fourth]
      · rw [ite_eq_left he, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (fourth_nn _) h _) (by positivity)
   rw [show a*b-c*d=b*(a-c)+c*(b-d) by ring]
   apply le_trans (spliff ..)
   have e1:= hu he (a-c); have e2:=hu hb (b-d)
   dsimp only [a,b,c,d] at e1 e2 ⊢
   linarith

lemma combine4 {a b : ℝ} (h:0≤a) (e:0≤b) : a^4+b^4≤ (a+b)^4 := by
   nlinarith [show 0≤a^2*b^2 by positivity,show 0≤a*b^3 by positivity,show 0≤a^3*b by positivity]

lemma slots (b : ℝ) (h:0≤b) {K : ℕ} (S : Domain) (f : ℕ→ℝ)
    (hr:(S.filter fun i=> f i≠0).card≤ K) :
    ∑ j∈S,(if f j≠0 then b else 0)≤K*b := by
   rw [←sum_filter]
   simp only [sum_const,nsmul_eq_mul]
   exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 hr) h

namespace Axis
variable (d : Axis)
abbrev deckX (k : ℕ) := d.narrowed k
abbrev deckY (k l : ℕ) := ((d.startd k).narrowed l)
abbrev midpoint (k : ℕ) (s : Pool n) := dst d.S k (leftP s)
def pass (k : ℕ) (f g : Pics n) : Pics n :=
    fun s x y=> peeler n k * ∑ i∈d.midpoint k s,f (leftP s) x i*g (rightP s) i y
def spotL (k : ℕ) (f g : Pics n) : Pics n :=
    fun s x y=> ∑ i∈d.midpoint k s, if g (rightP s) i y≠0 then f (leftP s) x i ^ 4 else 0
def spotR (k : ℕ) (f g : Pics n) : Pics n :=
    fun s x y=> ∑ i∈d.midpoint k s, if f (leftP s) x i≠0 then g (rightP s) i y ^ 4 else 0

/-- terminal sum eliminated by right row support -/
lemma spotL_on (k : ℕ) (f g : Pics n) (D : ℕ) (h:∀ s x (S:Domain),
    (S.filter fun i=> g s x i≠0).card ≤ D) :
    d.ti (d.spotL k f g) ≤ D * (d.deckX k).ton f ^4 := by
   rw [ton_four,d.ti_apply, (deckX d k).tperm leftP]
   rw [mul_left_comm (D:ℝ), ← av_cmul (↑D:ℝ)]
   apply mul_le_mul_of_nonneg_left (av_mono _) (scaleM_nn ..)
   intro s
   unfold spotL
   dsimp only [deckX,narrowed]
   rw [mul_sum]
   apply sum_le_sum; intro i hi
   rw [sum_comm,mul_sum]
   apply sum_le_sum; intro j hj
   exact slots _ (by positivity) _ _ (h _ _ _)

/-- release old source to charge right discrepancies -/
lemma spotR_on (k l : ℕ) (f g : Pics n) (D : ℕ) (h:Shelf D f) (hl:l ≤ d.a) (hk:k≤d.u) :
    d.ti (d.spotR k f g) ≤ ratioN d.u k ^4 * (D * (d.deckY k l).ton g^4) := by
   rw [ton_four,d.ti_apply, (deckY d k l).tperm rightP]
   rw [mul_left_comm (D:ℝ),← av_cmul (↑D:ℝ), upper_flip hk _,mul_assoc]
   have hp:0≤ratioN d.u k ^4:=by positivity
   apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (av_mono _) (scaleM_nn ..)) hp
   intro s
   dsimp only [deckY,narrowed,startd]
   unfold spotR
   let X0:=src d.S d.u s; let Y:=dst d.S d.a s; let Z:=d.midpoint k s
   let W:=dst d.S l (rightP s)
   change ∑ i∈ X0,∑ j∈Y,∑ x∈Z,_ ≤ (D:ℝ)*∑ x∈Z,∑ j∈ W, _
   have hz : Y ⊆ W := by
      intro i hi; obtain ⟨hh,he⟩:= mem_filter.1 hi
      exact mem_filter.2 ⟨hh,contained _ _ hl he⟩
   rw [sum_comm]
   calc _ ≤ ∑ j∈Y,∑ x∈Z,(D:ℝ)*g (rightP s) x j ^4 := by
             apply sum_le_sum; intro j hj; rw [sum_comm]
             apply sum_le_sum; intro x hx
             exact slots _ (by positivity) _ _ (h _ _ _)
        _ ≤ _ := by
            rw [sum_comm (s:=Y),mul_sum]
            apply sum_le_sum; intro x hx
            rw [mul_sum]; exact sum_le_sum_of_subset_of_nonneg hz (fun _ _ _=>by positivity)

lemma swaying {k} (h:2^k≤n) {K : ℝ} {f g p q : Pics n}
    (hf:RCap K f) (hg:RCap K g) (hp:RCap K p) (hq:RCap K q) (s x y) :
    (flaw (d.pass k f g) (d.pass k p q) s x y)^4 ≤
       8*K^4*(d.spotL k (flaw f p) g s x y+d.spotR k p (flaw g q) s x y) := by
   let a:= peeler n k
   have hm : in01 a:=spins h
   let F:=fun i=>f (leftP s) x i; let G:=fun i=>g (rightP s) i y
   let P:=fun i=>p (leftP s) x i; let Q:=fun i=>q (rightP s) i y
   let T:=d.midpoint k s; let m:=Meter.Sum T
   unfold flaw pass
   rw [fourth_mul hm.1, fourth_mul hm.1,←mul_sub,mul_pow,fourth_four hm.1]
   have hh := mixtures m (fun i=> F i * G i) (fun i=> P i * Q i)
                  (fun i=>mul_nonneg (hf ..).1 (hg ..).1) (fun i=>mul_nonneg (hp ..).1 (hq ..).1)
   change a* (fourth (m.I _) - fourth (m.I _))^4 ≤ _
   apply le_trans (b:= (fourth (m.I fun i=> F i* G i)-fourth (m.I fun i=>P i*Q i))^4)
   · exact le_trans (mul_le_mul_of_nonneg_right hm.2 (by positivity)) (le_of_eq (one_mul _))
   apply hh.trans
   unfold spotL spotR
   rw [← sum_add_distrib,mul_sum]
   apply sum_le_sum; intro i hi
   exact split_product (hf ..).1 (hg ..).1 (hp ..).1 (hq ..).1 (hp ..).2 (hg ..).2

abbrev fare (K : ℝ) (D : ℕ) := 2*K*(1+D:ℝ)
set_option maxHeartbeats 600000 in
lemma cost_pass {k l} (hz:2^k≤n) (hl:l ≤ d.a) (hk:k≤d.u) {f g p q : Pics n} {K : ℝ} {D : ℕ}
    (hf:RCap K f) (hg:Tile (d.deckY k l) K D g) (hp:RCap K p) (ht:Shelf D p)
    (hq:RCap K q) (hK:1≤K) :
    d.terr (d.pass k f g) (d.pass k p q)
      ≤ fare K D * ((d.deckX k).terr f p+ratioN d.u k*(d.deckY k l).terr g q) := by
   let A:=(d.deckX k).terr f p
   let B:=(d.deckY k l).terr g q
   let c:=ratioN d.u k
   have hK : 0<K := by linarith
   have ha : 0≤ A:= Axis.tn0 ..
   have hb : 0≤ B:= Axis.tn0 ..
   have hc : 0≤ c:= (box0 _).le
   change _≤fare K D*(A+c*B)
   apply (d.tm_le (by unfold fare; positivity)).2
   have he:= d.ti_mono (fun s i j _ _=> d.swaying hz hf hg.cap hp hq s i j)
   apply he.trans
   rw [d.tmul, d.ti_add (d.spotL k (flaw f p) g) (d.spotR k p (flaw g q))]
   have h1:=d.spotL_on k (flaw f p) g D hg.rows
   have h2:=d.spotR_on k l p (flaw g q) D ht hl hk
   apply le_trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (show 0≤8*K^4 by positivity))
   change 8*K^4*(D*A^4+c^4*(D*B^4)) ≤ _
   have h3 := combine4 ha (mul_nonneg hc hb)
   have hd : (0:ℝ)≤D:=by positivity
   have he1 : (D:ℝ)≤(1+D:ℝ)^4 := by nlinarith [sq_nonneg ((D:ℝ)^2)]
   calc _ = 8*K^4*D*(A^4+(c*B)^4) := by ring
        _ ≤ (fare K D)^4 * (A+c*B)^4 := by
          have h4 : 8*(D:ℝ) ≤ 16*(1+D:ℝ)^4:=by linarith
          refine mul_le_mul ?_ h3 (by positivity) (by positivity)
          have h5 := mul_le_mul_of_nonneg_right h4 (show 0≤ K^4 by positivity)
          unfold fare; linarith
        _ = _ := by ring

lemma pass_range {l k K D} {f g:Pics n} (h:2^k≤n) (hK:1≤K)
    (hf : Tile (d.deckX k) K D f) (hg : Tile (d.deckY k l) K D g) :
    RCap ((D+1:ℝ)*K^2) (d.pass k f g) := by
   intro s x y
   let a:=peeler n k
   let T:=d.midpoint k s
   let p:=fun i=>f (leftP s) x i; let q:=fun i=>g (rightP s) i y
   let S:= ∑ i∈T,p i*q i
   have ha:in01 a:=spins h
   have hs : 0≤S:=sum_nonneg fun i hi=>mul_nonneg (hf.cap ..).1 (hg.cap ..).1
   change 0≤a*S ∧ fourth (a*S)≤_
   refine ⟨mul_nonneg ha.1 hs,?_⟩
   have hv : S≤ K^4*K^4*D := by
      apply le_trans (b:=∑ i∈T, if p i≠0 then K^4*K^4 else 0)
      · apply sum_le_sum; intro i hi; split
        · exact mul_le_mul ((from_cap hf.cap _ _ _).2)
                 ((from_cap hg.cap _ _ _).2) (hg.cap ..).1 (by positivity)
        · next h=> rw [not_not] at h; rw [h,zero_mul]
      conv_rhs=>rw [mul_comm]
      exact slots _ (show 0≤K^4*K^4 by positivity) T p (hf.rows ..)
   let z:ℝ:=D+1
   have h0 : 0≤z*K^2:= by unfold z; positivity
   apply le_trans _ (le_of_eq (four_fourth h0))
   apply fourth_mono
   have hz : (D:ℝ) ≤ z^4 := by
      have he : 0≤ (D:ℝ):=by positivity
      unfold z; nlinarith [sq_nonneg ((D:ℝ)^2)]
   have hA:=mul_le_mul_of_nonneg_right ha.2 hs
   linarith [mul_le_mul_of_nonneg_left hz (show 0≤K^4*K^4 by positivity)]

lemma pass_pin {l k} {f g : Pics n} (h: (d.deckY k l).pinned d.a g) :
    d.pinned d.a (d.pass k f g) := by
   apply d.realize_pin
   intro s x y he
   by_contra! hv
   apply he
   have hz (i : ℕ) : g (rightP s) i y=0 := by
       conv_lhs=>rw [← show (d.deckY k l).wmask d.a g=g from h]
       exact ite_eq_right hv
   unfold pass; simp_rw [hz]; simp

end Axis
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

variable {n : ℕ} [Fact n.Prime]

namespace Axis
variable (d:Axis)

def Surf (i j:ℕ) (s:Pool n) := Env.mask d.u d.a (↑i:ZMod n) (↑j:ZMod n) s
def BothPin (f : Pics n) := ∀ i∈d.S,∀ j∈d.S, ∃ p:Channel n→Channel n→ℝ,
                    ∀ s,d.Surf i j s → f s i j=p s.1 s.2.1
def SinglePin (f : Pics n) := ∀ i∈d.S,∀ j∈d.S,∃ p:Channel n→ℝ,
                    ∀ s,d.Surf i j s → f s i j=p s.2.1

lemma marginalization (k : ℕ) (p : Channel n→Channel n→ℝ) (v : Channel n→ℝ)
    (x y z : ZMod n) :
      @Env.cond n 0 _ d.u d.a x y
        (fun s=> if hit k z s.2.2.1 then p s.1 s.2.2.1*v s.2.1 else 0) =
          pct n k * atP d.u x (fun s=> atP k z (p s)) * atP d.a y v := by
   let H (a : pc n d.u) := openP d.u x a
   let V (b : pc n d.a) := openP d.a y b
   have he (s t : Channel n) :
     av (fun c: Channel n=> if hit k z c then p s c*v t else 0) =
          pct n k * (atP k z (p s)*v t) := by
       rw [conditionP]
       unfold atP; rw [av_mulc]
   let w : ℝ:= av (fun a=>av (fun b=>av (fun c:Channel n=> if hit k z c then p (H a) c*v (V b) else 0)))
   refine Eq.trans (b:=w) ?_ ?_
   · unfold Env.cond w
     simp only [Env.outward]
     rw [av_prod]
     congr 1
     funext a
     rw [av_prod]
     congr 1
     funext b
     rw [av_prod]
     congr 1
     funext c
     exact av_const (α := Salt 0) _
   unfold w
   simp_rw [he,av_cmul]
   unfold atP
   rw [av_mulc]; dsimp only [H,V]; ring

def through (k i:ℕ) (f g : Pics n) : Pics n :=
    fun s x y=> if hit k (i:ZMod n) s.2.2.1 then f (leftP s) x i*g (rightP s) i y else 0

set_option maxHeartbeats 500000 in
lemma through_mean (k) (f g : Pics n) {i x y}
    (hx:x∈d.S) (hy:y∈d.S) (hi:i∈d.S)
    (hp:(d.deckX k).BothPin f) (hv:(d.startd k).SinglePin g) :
   d.fm (through k i f g) x y =
     pct n k * (d.deckX k).fm f x i * (d.startd k).fm g i y := by
   obtain ⟨p,hp⟩:=hp x hx i hi
   obtain ⟨v,hv⟩:=hv i hi y hy
   let F :Pics n:=fun s _ _=> p s.1 s.2.1
   let G :Pics n:=fun s _ _=> v s.2.1
   have he : d.fm (through k i f g) x y=d.fm (through k i F G) x y := by
       apply d.eqfm; intro s hs ht
       unfold through; split
       · next eh=>
         exact congrArg₂ (·*·) (hp (leftP s) ⟨hs,eh⟩) (hv (rightP s) ⟨eh,ht⟩)
       rfl
   have heL : (deckX d k).fm f x i = (deckX d k).fm F x i :=
      (deckX d k).eqfm fun s hx hj=>hp s ⟨hx,hj⟩
   have heG : (startd d k).fm g i y = (startd d k).fm G i y :=
      (startd d k).eqfm fun s hx hj=>hv s ⟨hx,hj⟩
   rw [he,heL,heG]
   change Env.cond d.u d.a (x:ZMod n) (y:ZMod n) (w:=0) _=_
   have hh := d.marginalization k p v (x:ZMod n) (y:ZMod n) (i:ZMod n)
   have hl : (d.deckX k).fm F x i =
       atP d.u (x:ZMod n) (fun s=>atP k (i:ZMod n) (p s)):=panel_const _ _ _ _ _
   have hr : (d.startd k).fm G i y=atP d.a (y:ZMod n) v:= by
       unfold fm Env.cond G atP; simp only [av_prod,av_const,Env.outward,startd]
   rw [hl,hr]
   exact hh

lemma pass_id (k) (f g :Pics n) (hp:(deckX d k).BothPin f) (hg:(startd d k).SinglePin g)
    {x y} (hx:x∈d.S) (hy:y∈d.S) :
    d.fm (d.pass k f g) x y=rate k * mm d.S ((deckX d k).fm f) ((d.startd k).fm g) x y := by
   let P :Pics n:=fun s x y=>∑ i∈d.S,through k i f g s x y
   have he : d.pass k f g=fun s x y=> peeler n k * P s x y := by
      ext s x y
      unfold pass midpoint dst retain P; rw [sum_filter]
      rfl
   have hp0 : d.fm P x y= ∑ i∈d.S,d.fm (through k i f g) x y := by
      unfold fm Env.cond P; rw [av_sum]
   rw [he,d.fscalar, hp0]
   have he := sum_congr (s₁:=d.S) rfl (fun i hi=> d.through_mean k f g hx hy hi hp hg)
   rw [he]; unfold mm
   rw [mul_sum,mul_sum]
   apply sum_congr rfl; intro i hi
   unfold peeler
   field_simp [(pct_pos (NeZero.pos n) k).ne']

end Axis

/- exact atoms directly inserted by Ask into canonical Panel. -/
namespace bed
def pat (q : Ask) (f : ℝ→ℝ) (col : Vec) : Pics n :=
    fun s=>q.atomTrue f col s.1 s.2.1
def bath (q : Ask) : Pics n := fun s=>q.bath s.1 s.2.1
def dfix (q : Ask) (N:ℕ):Axis:=⟨q.S,N,q.u,q.a⟩

lemma truth {q} {f : ℝ→ℝ} {col} (N) (h:Ask.Valid q col n)
    (hf:∀ x≤q.z,f x=0) (x y) (hx:x∈q.S) (hy:y∈q.S) :
    ((dfix q N).narrowed q.t).fm (pat (n:=n) q f col) x y =f (q.d x y)*col y := by
   apply Eq.trans (b:=q.two (n:=n) x y (fun s t=>q.atomTrue f col s t x y))
                 (panel_const _ _ _ _ _) (q.normalized_mean h hx hy hf)
lemma tooth {q : Ask} (N x y) :
    ((dfix q N).narrowed q.t).fm (bath (n:=n) q) x y=q.tooth n x y := @panel_const n 0 _ q.u q.t x y (fun s t=> q.bath s t x y)
lemma twopin (q) (f : ℝ→ℝ) (col N a) :
    ((dfix q N).narrowed a).BothPin (pat (n:=n) q f col) :=
     fun i _ j _=> ⟨fun x y=> q.atomTrue f col x y i j,fun _ _=>rfl⟩

lemma onepin (q : Ask) (f : ℝ→ℝ) (col N) (h:q.sp=false) (he:q.a≤q.t) :
    ((dfix q N).narrowed q.t).SinglePin (pat (n:=n) q f col) := by
   intro i hi j hj
   refine ⟨fun t=> f (q.d i j)*throttle q.S q.G q.a q.p.K i t q.z*
       divisor (zeta*q.tooth n i j)*1*col j,?_⟩
   intro s hs
   obtain ⟨hp,hx,hy⟩:= q.valid_broad s.1 s.2.1 i j he hi hj hs.1 hs.2
   rw [pat,q.premask _ _ _ _ _ _ hp hx hy]
   simp only [Grid.incG,Ask.hand,h,Bool.false_eq_true,ite_false]

end bed
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

variable {n : ℕ} [Fact n.Prime]

/-- A part is shared over one copy-symbol pair. -/
def replica (M i : ℕ) : Equiv.Perm (Channel n) :=
    if h:(↑M : ZMod n)=0 then Equiv.refl _
    else affineChannel (M:ZMod n) (i:ZMod n) h
def pane (M i j : ℕ) : Equiv.Perm (Pool n) :=
    Equiv.prodCongr (replica M i) (Equiv.prodCongr (replica M j) (Equiv.refl _))

lemma raid_id {M} (h:0<M) (hh:M<n) (i x : ℕ) (k) (s:Channel n) :
    hit k (x:ZMod n) (replica M i s) ↔ hit k (↑(radix M x i):ZMod n) s := by
   have hs : (M:ZMod n)≠0:=by
      intro he
      have hh:=congrArg ZMod.val he
      rw [ZMod.val_natCast] at hh
      simp only [ZMod.val_zero,Nat.mod_eq_of_lt ‹M<n›] at hh; omega
   unfold replica hit
   rw [dite_eq_right hs, affine_eval]
   have hq: (↑(radix M x i):ZMod n)= (i:ZMod n)+(x:ZMod n)*(M:ZMod n) := by unfold radix; push_cast; ring
   rw [hq]

def mint (M i : ℕ) (p:Vec) : Vec := fun x=> if x%M=i then p (x/M) else 0
def markM (M i j : ℕ) (p:Mat) : Mat :=
    fun x y=> if x%M=i ∧ y%M=j then p (x/M) (y/M) else 0

def pep (M i j : ℕ) (p: Pics n) : Pics n :=
   fun s=>markM M i j (p (pane M i j s))
def vim (M i : ℕ) (p: Paint n) : Paint n :=
   fun s=> mint M i (p (pane M i 0 s))

namespace Axis
variable (d:Axis)

abbrev nextd (M : ℕ) : Axis := {d with S:=copyZone M d.S}

lemma transport {x y i j M : ℕ} (hM:0<M) (hm:M<n) (hx:x%M=i) (hy:y%M=j)
    (f : Pool n→ℝ) :
    Env.cond d.u d.a (x:ZMod n) (y:ZMod n) (fun s=> f (pane M i j s)) =
         Env.cond d.u d.a (↑(x/M):ZMod n) (↑(y/M):ZMod n) f := by
   have he (s:Pool n) : Env.mask d.u d.a (x:ZMod n) (y:ZMod n) s ↔
                        Env.mask d.u d.a (↑(x/M):ZMod n) (↑(y/M):ZMod n) (pane M i j s) := by
      unfold Env.mask
      change _↔ hit d.u (↑(x/M):ZMod n) (replica M i s.1) ∧ hit d.a _ (replica M j s.2.1)
      rw [raid_id hM hm,raid_id hM hm,show radix M (x/M) i=x from by rw [← hx]; exact Nat.mod_add_div ..,
            show radix M (y/M) j=y from by rw [←hy]; exact Nat.mod_add_div ..]
   apply mul_left_cancel₀ (mul_pos (pct_pos (NeZero.pos n) d.u) (pct_pos (NeZero.pos n) d.a)).ne'
   rw [← Env.two_cond,←Env.two_cond]
   let v (s:Pool n):= if Env.mask d.u d.a (↑(x/M):ZMod n) (↑(y/M):ZMod n) s then f s else 0
   refine Eq.trans (b:=av (fun s=>v (pane M i j s))) ?_ (av_perm (pane M i j) v)
   apply congrArg av; ext s; unfold v
   simp_rw [he]

lemma transportV {x i M:ℕ} (hM:0<M) (hm:M<n) (hx:x%M=i) (p : Paint n) :
   d.vm (vim M i p) x=d.vm p (x/M) := by
   unfold vm vim mint
   simp_rw [ite_eq_left hx]
   have hs:= @transport n _ (d.narrowed 0) x 0 i 0 M hM hm hx (Nat.zero_mod _) (fun s=> p s (x/M))
   simpa only [narrowed, Nat.zero_div,Nat.cast_zero] using hs

lemma pep_mean {M i j : ℕ} {p : Pics n} (hM:0<M) (hm:M<n) (x y) :
    (d.nextd M).fm (pep M i j p) x y=markM M i j (d.fm p) x y := by
   unfold pep markM fm
   split
   · next he=> simp_rw [ite_eq_left he]
               exact d.transport hM hm he.1 he.2 (fun s=>p s (x/M) (y/M))
   · next he=> simp [he,Env.cond,av_zero]

lemma vim_mean {M i : ℕ} {p: Paint n} (hM:0<M) (hm:M<n) (x) :
    (d.nextd M).vm (vim M i p) x=mint M i (d.vm p) x := by
   by_cases he:x%M=i
   · exact (d.transportV hM hm he p).trans (Eq.symm (show mint M i _ x=_ from ite_eq_left he))
   unfold vm vim mint; simp [he,Env.cond,av_zero]

lemma pane_ti {M i j : ℕ} {p : Pics n} (hi:i<M) (hj:j<M) (hm:M<n) :
    (d.nextd M).ti (pep M i j p)=d.ti p := by
   rw [fpivot,fpivot]
   have hM:0<M:=by omega
   let f (x y):=pct n d.u*pct n d.a*d.fm p x y
   have he (x y) :
     pct n d.u*pct n d.a*(d.nextd M).fm (pep M i j p) x y=markM M i j f x y := by
       rw [pep_mean d hM hm]; unfold markM; split; rfl; ring
   change scaleM _ _ * (∑ x∈copyZone M d.S,∑ y∈copyZone M d.S,pct n d.u*pct n d.a* _)= _
   simp_rw [he]
   have H (x y) (a b) (ha:a<M) (hb:b<M) :
      markM M i j f (radix M x a) (radix M y b)=
           if a=i then (if b=j then f x y else 0) else 0 := by
      obtain ⟨hp,hq⟩:=fromrad M x a ha
      obtain ⟨hu,hv⟩:=fromrad M y b hb
      unfold markM; grind
   have hh (x a) (ha:a<M) :
     ∑ y∈copyZone M d.S,markM M i j f (radix M x a) y = if a=i then ∑ y∈d.S,f x y else 0 := by
     rw [eval_copies]
     have he (y) : ∑ b∈range M, markM M i j f (radix M x a) (radix M y b) =
                      if a=i then f x y else 0 := by
        rw [Finset.sum_eq_single j,H x y a j ha hj]; simp
        · intro b hb hz; rw [H x y a b ha (mem_range.mp hb)]; split <;> simp_all
        · intro h; exact False.elim (h (mem_range.mpr hj))
     simp_rw [he]
     split <;> simp_all
   rw [eval_copies]
   congr 1
   apply sum_congr rfl; intro x hx
   rw [sum_eq_single i,hh x i hi, ite_eq_left rfl]
   · intro a ha h; rw [hh x a (mem_range.mp ha),ite_eq_right h]
   · intro h; exact False.elim (h (mem_range.mpr hi))

lemma pane_vi {M i : ℕ} {p : Paint n} (hi:i<M) (hm:M<n) :
    (d.nextd M).vi (vim M i p)=d.vi p := by
   rw [vpivot,vpivot]
   dsimp only [nextd]
   rw [eval_copies]
   congr 1; apply sum_congr rfl; intro x hx
   have he (y) :
     ((d.nextd M).vm (vim M i p)) y=mint M i (d.vm p) y := vim_mean d (by omega) hm y
   simp_rw [show ({ d with S:=copyZone M d.S }:Axis)=d.nextd M from rfl]
   have hp a (h:a<M) : (d.nextd M).vm (vim M i p) (radix M x a) =
                             if a=i then d.vm p x else 0 := by rw [he,mint,(fromrad M x a h).1,(fromrad M x a h).2]
   rw [sum_eq_single i,hp i hi,ite_eq_left rfl]
   · intro j hj hz; rw [hp j (mem_range.mp hj),ite_eq_right hz]; ring
   · intro h; exact False.elim (h (mem_range.mpr hi))

lemma pep_terr {M i j : ℕ} {p q : Pics n} (hi:i<M) (hj:j<M) (hm:M<n) :
    (d.nextd M).terr (pep M i j p) (pep M i j q)=d.terr p q := by
   unfold terr
   let f:Pics n:= fun s x y=> (fourth (p s x y)-fourth (q s x y))^4
   have hs : (fun s x y=> (fourth (pep M i j p s x y)-fourth (pep M i j q s x y))^4)=pep M i j f := by
      ext s x y
      unfold pep markM; split; rfl; ring
   unfold ton Meter.L
   congr 1; change Axis.ti _ _=d.ti f; rw [hs,d.pane_ti hi hj hm]

lemma vim_cost {M i : ℕ} {p q : Paint n} (hi:i<M) (hm:M<n) :
   (d.nextd M).von (fun s x=>vim M i p s x-vim M i q s x) =
         d.von (fun s x=>p s x-q s x) := by
   let f:Paint n:=fun s x=> (p s x-q s x)^4
   have hs : (fun s x=> (vim M i p s x-vim M i q s x)^4) = vim M i f := by
      ext s x
      unfold vim mint; split; rfl; ring
   unfold von Meter.L; congr 1; change Axis.vi (d.nextd M) _=d.vi f
   rw [hs,d.pane_vi hi hm]

lemma pep_pin {M i j : ℕ} {p : Pics n} {k} (hi:i<M) (hm:M<n) (hp: d.pinned k p) :
    (d.nextd M).pinned k (pep M i j p) := by
   have hM:0<M:=by omega
   apply realize_pin
   intro s x y he
   unfold pep markM at he; split at he
   · next hh =>
     have hz : y/M ∈ dst d.S k (pane M i j s) := by
         by_contra! hc
         apply he
         conv_lhs=>rw [← show d.wmask k p=p from hp]
         exact ite_eq_right hc
     obtain ⟨hu,hz⟩:=mem_filter.mp hz
     apply mem_filter.mpr ⟨(member_copy hM).2 hu,?_⟩
     have h1:= (raid_id hM hm j (y/M) k s.2.1).1 hz
     have he1:radix M (y/M) j=y := by conv_lhs=>rw [← hh.2]
                                      exact Nat.mod_add_div ..
     rwa [he1] at h1
   exact (he rfl).elim

lemma pep_cap {M i j : ℕ} {p : Pics n} {K : ℝ} (hp:RCap K p) (h:0≤K) :
    RCap K (pep M i j p) := by
   intro s x y; unfold pep markM; split; apply hp
   simp [fourth,h]

end Axis
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset
open scoped Classical

variable {n : ℕ} [Fact n.Prime]
abbrev Fwd (n:ℕ) := Pool n→ℕ→ℕ→Prop

namespace Axis
variable (d:Axis)

def spout (p:Pics n) (K : ℕ) : Paint n :=
   fun s y=> rank (src d.S d.u (crossP s)) (fun i=> p (crossP s) i y) K

lemma spout_at (p q:Pics n) (K : ℕ) (u : Pool n) (y) :
    (d.spout p K (crossP u) y-d.spout q K (crossP u) y)^4 ≤
        ∑ x∈src d.S d.u u,(p u x y-q u x y)^4 := by
   let S:=src d.S d.u u
   let a:ℝ:=(Meter.Sum S).L fun x=>p u x y-q u x y
   have he (i) (hi:i∈S) : |p u i y-q u i y| ≤ a := by
      conv_lhs=>rw [← four_fourth (abs_nonneg _)]
      rw [Meter.abs4]; apply fourth_mono
      exact single_le_sum (f:=fun i=>(p u i y-q u i y)^4) (fun i _=>by positivity) hi
   have hs := rank_lip (show 0≤a from Meter.Lnn ..) (f:=fun i=>p u i y) (g:=fun i=>q u i y)
                  (K:=K) he
   conv_lhs=>rw [← Meter.abs4]
   exact le_trans (pow_le_pow_left₀ (abs_nonneg _) hs 4) (le_of_eq (Meter.L4 ..))

lemma rank_fee (p q : Pics n) (K : ℕ) (hz : d.a≤d.u) :
    ratioN d.u d.a * (d.startd d.a).von (fun s i=>d.spout p K s i - d.spout q K s i)
       ≤ d.ton (fun s i j=>p s i j-q s i j) := by
   let u:=fun s i=>d.spout p K s i - d.spout q K s i
   let t:=fun s i j=>p s i j-q s i j
   let e:=ratioN d.u d.a
   let c:=d.startd d.a
   change e*c.von u≤d.ton t
   have hc:0≤e := (box0 _).le
   conv_lhs=>rw [← four_fourth (mul_nonneg hc (c.vn0 u))]
   conv_rhs=>rw [← four_fourth (d.tn0 t)]
   apply fourth_mono
   rw [d.ton_four,mul_pow,c.von_four,vperm _ crossP,ti_apply,upper_flip hz d.N, mul_assoc]
   refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (av_mono ?_) (scaleM_nn ..))
                (pow_nonneg hc _)
   intro s
   dsimp only
   rw [sum_comm]
   change ∑ y∈dst d.S d.a s,_ ≤ _
   apply sum_le_sum; intro y hy
   exact d.spout_at p q ..

lemma vm_two (p : Channel n→Channel n→ℝ) (i:ℕ) :
   d.vm (n:=n) (fun s (_:ℕ)=>p s.1 s.2.1) i=
            atP d.u (↑i:ZMod n) (fun s=>av (fun t=>p s t)) := by
   have hz (s : Channel n) : atP 0 (0:ZMod n) (p s)=av (p s) := by
     have he:=conditionP 0 (0:ZMod n) (p s)
     simpa only [allhit,ite_true,pct_c0,one_mul] using he.symm
   unfold vm
   have he:=panel_const d.u 0 i 0 p (w:=0)
   rw [Nat.cast_zero] at he; rw [he]
   simp only [hz]

lemma expect_spout {p:Pics n} (G:Mat) (K J) (_:d.a=d.u)
    (h:∀ s,∀ x∈src d.S d.u s,∀ y∈dst d.S d.u s,p s x y=
                       mark d.S G d.u K x y s.2.1) {y:ℕ} (hy:y∈d.S) :
    d.vm (d.spout p J) y=U n d.S G d.u K J y := by
   let f (s t : Channel n):=score d.S G d.u K J y t s
   rw [d.eqvm (g:=fun s _=> f s.1 s.2.1) ?_,d.vm_two]
   · rfl
   intro s he
   change rank _ _ _ = rank _ _ _
   apply sub_eq_zero.mp
   apply abs_eq_zero.mp
   apply le_antisymm _ (abs_nonneg _)
   let q:=crossP s
   apply rank_lip (le_refl _)
   intro i hi; have hv:y∈dst d.S d.u q:=mem_filter.2 ⟨hy,he⟩
   have hh:= h q i hi y hv
   change |p q i y - mark _ _ _ _ _ _ q.2.1| ≤ _
   rw [hh]; norm_num

abbrev focus (u : Fwd n) (v : Paint n) : Pics n :=
   fun s i j=> if u s i j then v (crossP s) j else 0
set_option maxHeartbeats 700000 in
lemma focal (u:Fwd n) (v:Paint n) (D : ℕ) (hk:d.a≤d.u)
    (hs:∀ s y,( (src d.S d.u s).filter fun x=>u s x y).card≤2*D) :
    d.ton (focus u v) ≤ (1+2*D:ℝ)*ratioN d.u d.a * (d.startd d.a).von v := by
   let p:=ratioN d.u d.a
   let k : ℝ:=1+2*D
   let e:=d.startd d.a
   have ht : 0≤ p:= (box0 _).le
   have hK : 1≤k:=by unfold k; simp
   change _ ≤ k*p*e.von _
   apply (d.tm_le (mul_nonneg (by positivity) (e.vn0 _))).2
   rw [mul_pow,mul_pow,Axis.von_four,d.ti_apply, vperm _ crossP,upper_flip hk d.N,mul_assoc]
   have hn : k^4*p^4*(scaleM e.N e.u * av (fun s=>∑ i∈src e.S e.u (crossP s),v (crossP s) i ^4)) =
           ratioN d.u d.a ^4*(scaleM d.N d.a*
             av (fun s=>k^4*∑ y∈dst d.S d.a s,v (crossP s) y ^4)) := by
      rw [av_cmul]; change k^4*p^4*(scaleM d.N d.a*_)=p^4*(scaleM d.N d.a*(k^4*_)); ring_nf; rfl
   rw [hn]
   apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (av_mono _) (scaleM_nn ..))
                                          (by positivity)
   intro s
   dsimp only [focus]; rw [sum_comm,mul_sum]; apply sum_le_sum; intro y hy
   let f x:=u s x y
   let b:=(v (crossP s) y)^4
   have he : (2:ℝ)*D ≤ k^4 := by
       have hi : k≤k^4:=by simpa using pow_le_pow_right₀ hK (show 1≤(4:ℕ) by omega)
       unfold k at *; linarith
   have hz x : (if f x then v (crossP s) y else 0)^4 = if f x then b else 0 := by
       by_cases h:f x
       · rw [ite_eq_left h,ite_eq_left h]
       · rw [ite_eq_right h,ite_eq_right h]; ring
   change ∑ x∈src d.S d.u s,(if f x then v (crossP s) y else 0)^4 ≤ _
   simp_rw [hz]
   rw [← sum_filter]
   simp only [sum_const,nsmul_eq_mul]
   apply mul_le_mul_of_nonneg_right _ (show 0≤b by unfold b; positivity)
   apply le_trans _ he; exact_mod_cast hs s y

end Axis
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset
open scoped Classical

variable {n : ℕ} [Fact n.Prime]
lemma fourth0 : fourth (0:ℝ)=0:=by simp [fourth]
lemma fourth1 : fourth (1:ℝ)=1:=by simp [fourth]
lemma fourth_interval {x:ℝ} (h:in01 x) : in01 (fourth x) :=
    ⟨fourth_nn _, le_trans (fourth_mono h.2) (le_of_eq fourth1)⟩

lemma multrip {C a b x y p q : ℝ} (ha:0≤a) (hb:0≤b) (ht: fourth b ≤ C)
    (hx:in01 x) (hy:in01 y) (hp:in01 p) (hq:in01 q) :
    |fourth (a*x*p)-fourth (b*y*q)| ≤
       |fourth a-fourth b| + C*(|fourth x-fourth y| + |fourth p-fourth q|) := by
   have h1 (v) (h:in01 v) : |fourth v| ≤1:= by rw [abs_of_nonneg (fourth_nn _)]; exact (fourth_interval h).2
   have hz:= Frag.lipprod (h1 _ hx) (h1 _ hq) (p:= fourth p) (g:= fourth y)
   rw [fourth_mul (mul_nonneg ha hx.1),fourth_mul (mul_nonneg hb hy.1), fourth_mul ha,fourth_mul hb]
   have h3 : |fourth b| ≤ C:=by rw [abs_of_nonneg (fourth_nn _)]; exact ht
   have h4 : |fourth x*fourth p|≤1:= by
     rw [abs_mul]; exact le_trans (mul_le_mul (h1 _ hx) (h1 _ hp) (abs_nonneg _) zero_le_one)
                             (le_of_eq (one_mul _))
   have he := Frag.lipprod h3 h4 (g:=fourth a) (p:=fourth y*fourth q)
   rw [abs_sub_comm (fourth b),abs_sub_comm (fourth y*_), abs_sub_comm (fourth b*_)] at he
   rw [mul_assoc,mul_assoc]
   have h0 : 0≤ C:=le_trans (fourth_nn _) ht
   linarith [mul_le_mul_of_nonneg_left hz h0]

namespace Builder
def confl (u v:Pics n) : Fwd n := fun s i j=> u s i j≠0∨v s i j≠0
variable {d : Axis} (f : Builder d)

set_option maxHeartbeats 900000 in
/-- sparse final wrapper estimate from compressed pre-score and pre-main. -/
lemma sealed (u v : Block n) {C r J : ℝ} (_:0≤r) (w w' : Paint n) (o : Trio) (b:Bool)
    (ho : TS f.tau C o) (hs:TS f.tau C (suppT f.tau false))
    (ht:0<f.tau) (hh:f.c=true) (hm:d.a≤d.u)
    (hw:∀ s x,in01 (w s x)) (hw':∀ s x,in01 (w' s x))
    (hz:Lip J (fun x=>fourth (shutoff x))) (he:0≤J)
    (hoP:Shelf (clim f.p) (f.wrapped u o b w)) (hvP:Shelf (clim f.p) (f.wrapped v o b w'))
    (hy:d.terr (f.coins u o b) (f.coins v o b)≤r)
    (hp:d.terr (f.coins u (suppT f.tau false) false) (f.coins v (suppT f.tau false) false)≤r) :
    d.terr (f.wrapped u o b w) (f.wrapped v o b w') ≤
       r + C^3*(1+2*clim f.p:ℝ)*(J*(4*(C^3)^3)*r+
                         ratioN d.u d.a * (d.startd d.a).von (flawV w w')) := by
   let oP:=f.wrapped u o b w; let vP:=f.wrapped v o b w'
   let X (v:Block n):=f.coins v o b
   let R (v:Block n):=f.coins v (suppT f.tau false) false
   let M:= clim f.p; let K:ℝ:=1+2*M
   let P:Fwd n:=confl oP vP
   have h0:=ho.start.one
   have hc : 0≤ C^3 := by positivity
   have hK:0≤K:=by unfold K; positivity
   have hi (s y) : ((src d.S d.u s).filter fun x=>P s x y).card≤ 2*M:= by
      let S:= src d.S d.u s
      let A:= S.filter (fun x=>oP s x y≠0)
      let B:= S.filter (fun x=>vP s x y≠0)
      have he : S.filter (fun x=>P s x y) ⊆ A ∪ B := by
         intro i hi; obtain ⟨hi,hk⟩:=mem_filter.1 hi
         rcases hk with hk|hk
         · exact mem_union_left _ (mem_filter.mpr ⟨hi,hk⟩)
         exact mem_union_right _ (mem_filter.mpr ⟨hi,hk⟩)
      have hx:A.card≤M:= hoP s y S
      have hy:B.card≤M:= hvP s y S
      exact (card_le_card he).trans ((card_union_le ..).trans (by linarith))
   let a:Pics n :=fun s x y=>|flaw (X u) (X v) s x y|
   let sp:Paint n:=fun s y=> d.spout (R u) M s y-d.spout (R v) M s y
   let g:Paint n :=fun s y=>J * |sp s y|
   let c:Paint n :=fun s y=>|flawV w w' s y|
   let pp:Pics n := Axis.focus P g
   let qq:Pics n:= Axis.focus P c
   have H (s x y) : |flaw oP vP s x y| ≤ a s x y+C^3*(pp s x y+qq s x y) := by
      by_cases hk:P s x y
      · let m (v:Block n):=(f.sess s).incG (v s) y
        let t:=crossP s
        have heX : |fourth (m u)-fourth (m v)|≤g t y := by
           have H (v:Block n) : m v=shutoff (d.spout (R v) M t y):= by
               change (f.sess _).incG _ _=_
               unfold Grid.incG; rw [ite_eq_left (show (f.sess s).sp=true from hh)]; rfl
           unfold g sp; rw [H,H]; exact hz ..
        obtain h1 := (f.tiling u ho ht b).cap s x y
        obtain h2 := (f.tiling v ho ht b).cap s x y
        change |fourth (X u s x y*m u*w t y)-fourth (X v s x y*m v*w' t y)| ≤ _
        apply le_trans (multrip h1.1 h2.1 h2.2 ((f.sess s).incG_bounds (u s) y)
                              ((f.sess s).incG_bounds (v s) y) (hw ..) (hw' ..))
        change _ ≤ _+C^3*((if _ then _ else _)+(if _ then _ else _))
        rw [ite_eq_left hk,ite_eq_left hk]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add heX le_rfl) hc)
      have ht1 : oP s x y=0:= by_contra (fun e=>hk (Or.inl e))
      have ht2 : vP s x y=0:= by_contra (fun e=>hk (Or.inr e))
      change |fourth (oP s x y)-fourth (vP s x y)| ≤ _+C^3*((if _ then _ else _)+(if _ then _ else _))
      rw [ht1,ht2,ite_eq_right hk,ite_eq_right hk,sub_self,abs_zero, add_zero,mul_zero,add_zero]
      exact abs_nonneg _
   have hb1 : d.ton a≤r:=by unfold a; rw [d.ton_subnorm]; exact hy
   let L:=d.startd d.a; let m:=ratioN d.u d.a
   have hm1:0≤ m:= (box0 _).le
   have hq : d.ton qq ≤ K*m*L.von (flawV w w') := by
       have he:=d.focal P c M hm hi
       have hc:L.von c=L.von (flawV w w'):=Meter.Labs ..
       change d.ton qq≤K*m*L.von c at he
       rwa [hc] at he
   have hP : d.ton pp ≤ K*(J*(4*(C^3)^3)*r) := by
      have h0 := d.focal P g M hm hi
      have hZ:L.von g=J*L.von sp := by
          unfold g; rw [L.vscale,abs_of_nonneg he]
          exact congrArg (J*·) (show L.von (fun s y=> |sp s y|)=L.von sp from Meter.Labs ..)
      have hrank := d.rank_fee (R u) (R v) M hm
      have hpr:=d.root_fee (f.tiling u hs ht false).cap (f.tiling v hs ht false).cap (by
                     exact one_le_pow₀ ho.start.one)
      have hv : m*L.von sp ≤4*(C^3)^3*r :=
         hrank.trans (hpr.trans (mul_le_mul_of_nonneg_left hp (by positivity)))
      change d.ton pp≤K*m*L.von g at h0; rw [hZ] at h0; apply h0.trans
      have he1:=mul_le_mul_of_nonneg_left hv (mul_nonneg hK he)
      linarith
   apply (d.torder fun s x y _ _=> H s x y).trans
   let v:Pics n:= fun s i j=>C^3*(pp s i j+qq s i j)
   apply (d.tplus a v).trans
   unfold v; rw [d.tscale,abs_of_nonneg hc]
   have H:= d.tplus pp qq
   apply le_trans (add_le_add hb1 (mul_le_mul_of_nonneg_left
              (le_trans H (add_le_add hP hq)) hc))
   exact le_of_eq (by dsimp [m,K,L,M]; ring)

/-- Full-array comparison with exact-ID compression, with membership mask. -/
lemma rated (v : Spray n 0) {s M : ℝ} (he : v.d=d) (hz : v.K=f.p.K)
    {C : ℝ} {o : Trio} (ho : TS f.tau C o) (ht : v.Works s M)
    (h:delta≤f.tau) (hh:f.tau≤1)
    (b : Bool) :
   d.terr (f.coins (fun u x=> (v.go u x).mid v.L) o b)
            (f.coins (fun u x=> (v.go u x).origin) o b) ≤
                 Spray.localP v.K v.b C M*s := by
    subst d
    have hc:= v.compress ht ho h hh
    rw [← v.d.ton_subnorm] at hc; apply le_trans ?_ hc

    apply v.d.torder
    intro u x y hx hy
    unfold Builder.coins Grid.pre
    by_cases he:b=false∨ y∈(f.sess u).narrow
    · have hp : x∈(f.sess u).src ∧ y∈(f.sess u).dst ∧ (b=false∨_) := ⟨hx,hy,he⟩
      rw [ite_eq_left hp,ite_eq_left hp]
      unfold Spray.diff
      simp only [Spray.go,sess,hz]
      exact le_rfl
    · have hp : ¬ (x∈(f.sess u).src ∧ y∈(f.sess u).dst ∧ (b=false∨_)) := fun h=>he h.2.2
      rw [ite_eq_right hp,ite_eq_right hp,sub_self,abs_zero]; exact abs_nonneg _

end Builder

end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

variable {n : ℕ} [Fact n.Prime]
def Maxer {n} (u : ℕ→Paint n) : ℕ→Paint n
  | 0 => fun _ _=>0
  | i+1=>fun s x=> max (Maxer u i s x) (u i s x)

def Leader (g : ℝ→ℝ) (i:ℕ) (u:ℕ→Paint n) : Paint n :=
   fun s x=>g (Maxer u i s x)

omit [Fact (Nat.Prime n)] in
lemma maxima (u v : ℕ→Paint n) (k s x) :
    |Maxer u k s x-Maxer v k s x| ≤ ∑ i∈range k,|u i s x-v i s x| := by
   induction k with
   | zero=>simp [Maxer]
   | succ k ih=>
     rw [show Maxer u (k+1) s x=_ from rfl, sum_range_succ]
     have he : 0≤ ∑ i∈range k, |u i s x-v i s x|:=sum_nonneg fun _ _ => abs_nonneg _
     refine maxnear (ih.trans (le_add_of_nonneg_right (abs_nonneg _))) ?_
     linarith

lemma leaders_mean (P:Stg) (g : ℝ→ℝ) (i s x) :
    Leader g i (fun j (_:Pool n)=>P.testU n j) s x=g (P.probed n i x) := by
   have hh (i) : Maxer (fun j (_:Pool n)=>P.testU n j) i s x=P.probed n i x := by
      induction i with
      | zero=>rfl
      | succ k ih=> exact congrArg (fun i=>max i (P.testU n k x)) ih
   unfold Leader; rw [hh]

namespace Axis
variable (d:Axis)
lemma v_abs (f:Paint n) : d.von (fun s i=> |f s i|)= d.von f := Meter.Labs ..
lemma leader_cost (u v : ℕ→Paint n) {C g} (he : Lip C (fun t=>fourth (g t))) (h0:0≤C)
    {r k} (h:∀ i<k,d.von (fun s x=> u i s x-v i s x) ≤r) :
    d.von (flawV (Leader g k u) (Leader g k v)) ≤ C*k*r := by
   let f:Paint n:=fun s x=> ∑ i∈range k, |u i s x-v i s x|
   have hs (s x) : |flawV (Leader g k u) (Leader g k v) s x|≤C*f s x :=
     le_trans (he _ _) (mul_le_mul_of_nonneg_left (maxima u v k s x) h0)
   apply le_trans (d.vorder (fun s x _=>hs s x))
   rw [d.vscale,abs_of_nonneg h0]
   unfold f
   apply le_trans (mul_le_mul_of_nonneg_left
       (d.vseries (fun i s x=>|u i s x-v i s x|) _) h0)
   have ht (i) (hi:i∈range k) : d.von (fun s x=> |u i s x-v i s x|) ≤ r := by
      rw [d.v_abs (fun s x=>u i s x-v i s x)]; exact h i (mem_range.1 hi)
   have hh:=mul_le_mul_of_nonneg_left (sum_le_sum ht) h0
   apply hh.trans; simp only [sum_const,nsmul_eq_mul,card_range]
   exact le_of_eq (by ring)

lemma multiplier_fee {p : Pics n} (u : Paint n) {D : ℕ} (hr: ∀ s i (S : Domain),
   (S.filter fun x=> p s i x≠0).card ≤ D) :
   d.ton (fun s i j=> if p s i j≠0 then u s i else 0) ≤ (D+1:ℝ)*d.von u := by
   have hv:=d.vn0 u
   apply (d.tm_le (by positivity)).2
   rw [mul_pow,d.von_four,← d.vmul]
   apply d.vi_mono; intro s i hi
   let T:=dst d.S d.a s
   let f x:=p s i x
   have he (x) : (if f x≠0 then u s i else 0)^4= if f x≠0 then u s i^4 else 0 := by
      by_cases h:f x≠0
      · rw [ite_eq_left h,ite_eq_left h]
      rw [ite_eq_right h,ite_eq_right h]; ring
   change ∑ j∈T,(if f j≠0 then u s i else 0)^4≤_
   simp_rw [he]
   have hh : (D:ℝ)≤ (D+1:ℝ)^4:=by
      have he : 0≤(D:ℝ):=by positivity
      nlinarith [sq_nonneg ((D:ℝ)^2)]
   apply le_trans (slots _ (show 0≤u s i^4 by positivity) T f (hr ..))
   exact mul_le_mul_of_nonneg_right hh (by positivity)

end Axis

def honor (u : Paint n) (f : Pics n) : Pics n := fun s i j=>f s i j*u s i
def fame (u v : Paint n) : Paint n:=fun s i=> u s i*v s i

namespace Axis

variable (d:Axis)
lemma honors_fee {k} (hk:k≤d.u) {p q : Pics n} {u v : Paint n} {C : ℝ} {D : ℕ}
    {a} (hl:a≤d.a)
    (he:RCap C p) (hc0:1≤C) (hq: Tile (d.narrowed a) C D q)
    (hx :∀ s i,in01 (u s i)) (_:∀ s i,in01 (v s i)) :
    d.terr (honor u p) (honor v q) ≤
       (d.narrowed a).terr p q + C*(D+1:ℝ)*ratioN d.u k *(d.startd k).von (flawV u v) := by
   let f:=flaw (honor u p) (honor v q)
   let z:Pics n:=fun s i j=> if q s i j ≠0 then flawV u v s i else 0
   let h:= flaw p q
   have H (s i j) : |f s i j| ≤ |h s i j|+C* |z s i j| := by
      have hv : |fourth (u s i)| ≤1:= by
        rw [abs_of_nonneg (fourth_nn _)]; exact (fourth_interval (hx s i)).2
      obtain ⟨ht,hw⟩:= hq.cap s i j
      have hb:|fourth (q s i j)|≤ C:=by rw [abs_of_nonneg (fourth_nn _)]; exact hw
      unfold f flaw honor
      rw [fourth_mul (he s i j).1,fourth_mul ht]
      unfold h flaw z; split
      · next hNz=>

        rw [mul_comm (fourth (p _ _ _)),mul_comm (fourth (q _ _ _))]
        apply le_trans (Frag.lipprod hv hb)
        unfold flawV; linarith
      · next eco=>
        have hg:q s i j=0:=not_not.mp eco
        rw [hg,fourth0,zero_mul,sub_zero,sub_zero,abs_zero,mul_zero,add_zero,abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_left hv (abs_nonneg _)) (le_of_eq (mul_one _))
   have hA:0≤C:=by linarith
   have hf:= d.torder fun s i j _ _=>H s i j
   apply hf.trans
   apply (d.tplus (fun s i j=>|h s i j|) (fun s i j=>C* |z s i j|)).trans
   rw [d.ton_subnorm,d.tscale,abs_of_nonneg hA, d.ton_subnorm]
   have hz : d.ton z≤(D+1:ℝ)*d.von (flawV u v):=d.multiplier_fee _ hq.rows
   have ht:= (d.narrowed a).tsmall d.a hl h
   have hx:=d.vsmall k hk (flawV u v)
   refine add_le_add (show d.ton h ≤ _ from ht) ?_
   apply le_trans (mul_le_mul_of_nonneg_left
        (hz.trans (mul_le_mul_of_nonneg_left hx (by positivity))) hA)
   exact le_of_eq (by ring)

omit [Fact (Nat.Prime n)] in
lemma root_cap_hon {C : ℝ} {p : Pics n} {u:Paint n} (h:RCap C p) (hw:∀ s i,in01 (u s i)) :
    RCap C (honor u p) := by
   intro s i j
   have hk := h s i j; have he := hw s i
   exact ⟨mul_nonneg hk.1 he.1,le_trans (fourth_mono
          (le_trans (mul_le_mul_of_nonneg_left he.2 hk.1) (le_of_eq (mul_one _)))) hk.2⟩

lemma pinned_hon {t} {p : Pics n} {u : Paint n} (h:d.pinned t p) : d.pinned t (honor u p) := by
   apply d.realize_pin; intro s i j hv
   by_contra! he
   have hh : p s i j=0 := by
      conv_lhs=>rw [← show d.wmask t p=p from h]
      exact ite_eq_right he
   exact hv (by unfold honor; rw [hh,zero_mul])

lemma fame_fee {u v p q : Paint n} {C : ℝ} (hC:0≤C) (h:∀ s i,in01 (u s i))
    (e:∀ s i,in01 (v s i)) (hp:∀ s i, |q s i| ≤ C) {k} (hk:k≤d.u) :
    d.von (fun s i=>fame u p s i-fame v q s i) ≤
       d.von (fun s i=> p s i-q s i) + C*4*ratioN d.u k*(d.startd k).von (flawV u v) := by
   let f:Paint n:=fun s i=> p s i-q s i
   let g:= flawV u v
   have H (s i) : |fame u p s i-fame v q s i| ≤ |f s i|+(C*4)* |g s i| := by
      have hu:=h s i; have hv:=e s i
      unfold fame
      have ht:= Frag.lipprod (show |u s i|≤1 from (abs_of_nonneg hu.1).le.trans hu.2)
                    (hp s i) (p:= p s i) (g:=v s i)
      have hc:= ordinary hu.1 hv.1 (fourth_interval hu).2 (fourth_interval hv).2
      unfold f g flawV
      nlinarith
   apply le_trans (d.vorder (fun s i _=>H s i))
   apply le_trans (d.vplus (fun s i=>|f s i|) (fun s i=>C*4* |g s i|))
   rw [d.v_abs,d.vscale,abs_of_nonneg (by positivity),d.v_abs]
   have hi:= d.vsmall k hk g
   change d.von f+C*4*d.von g≤d.von f+ _* (d.startd k).von g
   linarith [mul_le_mul_of_nonneg_left hi (show 0≤C*4 by positivity)]

end Axis
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

variable {n : ℕ} [Fact n.Prime]

lemma crowd (S : Domain) {p : Vec} {D : ℕ} (h:(S.filter (fun i=> p i≠0)).card≤D) :
    (∑ i∈S,p i)^4 ≤ (D:ℝ)^4*∑ i∈S,(p i)^4 := by
   let z:=(Meter.Sum S).L p
   have hz : 0≤ z:=Meter.Lnn ..
   have he : ∀ i∈S,|p i|≤z:=by
     intro i hi
     conv_lhs=>rw [← four_fourth (abs_nonneg _)]
     rw [Meter.abs4]
     apply fourth_mono
     exact single_le_sum (f:=fun i=>p i^4) (fun i _=>by positivity) hi
   calc
    _ ≤ (D*z)^4 := by
       rw [← Meter.abs4]
       apply pow_le_pow_left₀ (abs_nonneg _) _
       apply (abs_sum_le_sum_abs ..).trans
       calc ∑ i∈S, |p i| ≤ ∑ i∈S, if p i≠0 then z else 0 :=
              sum_le_sum fun i hi=>by split; exact he i hi; next h=> simp [not_not.mp h]
            _ ≤ _:= slots z hz S p h
    _ = _ := by rw [mul_pow]; rw [show z^4=∑ i∈S,p i^4 from Meter.L4 ..]

namespace Axis
variable (d:Axis)
def passV (k : ℕ) (p:Pics n) (v:Paint n) : Paint n :=
   fun s x=>peeler n k*∑ y∈d.midpoint k s,p (leftP s) x y*v (rightP s) y

lemma passV_id (k : ℕ) (p:Pics n) (v:Vec) (hp:(deckX d k).BothPin p)
    {x:ℕ} (hx:x∈d.S) :
   d.vm (d.passV k p (fun _=>v)) x =
        rate k * mv d.S ((deckX d k).fm p) v x := by
  let g : Pics n := fun s i _=> v i
  let a:= d.narrowed 0
  have H1: d.vm (d.passV k p (fun _=>v)) x =
              a.fm (a.pass k p g) x x := by
     rw [← show ridge (d.vm (d.passV k p (fun _=>v))) x x=d.vm (d.passV k p (fun _=>v)) x from by simp [ridge],← diagh]
     apply a.eqfm
     intro s hi hz
     unfold core ridge; rw [ite_eq_left rfl]; rfl
  have hs : a.deckX k=d.deckX k:=rfl
  have he : (a.startd k).fm g=fun i j=> v i := (a.startd k).fdet _
  rw [H1,a.pass_id k _ g _ _ hx hx, he,hs]
  · rfl
  · exact hp
  · exact fun i _ j _=> ⟨fun _=>v i,fun s _=>rfl⟩

lemma left_cost {k : ℕ} (f:Pics n) (u:Paint n) (hk:2^k ≤ n) {D}
  (h:∀ s i (S:Domain),(S.filter (fun j=> f s i j≠0)).card≤D)
  (he:∀ s i,in01 (u s i)) :
    d.von (d.passV k f u) ≤ D*(d.deckX k).ton f := by
   have hc : 0≤ (d.deckX k).ton f:=Axis.tn0 ..
   apply (d.vm_le (by positivity)).mpr
   rw [mul_pow,ton_four,← tmul]
   rw [d.vi_apply,(deckX d k).tperm leftP]
   refine mul_le_mul_of_nonneg_left (av_mono ?_) (scaleM_nn ..)
   intro s; dsimp only
   apply sum_le_sum; intro i hi
   let z:=d.midpoint k s
   let g:Vec:= fun j=>f (leftP s) i j*u (rightP s) j
   have hh : (peeler n k)^4≤1 := calc _ ≤ (1:ℝ)^4:= pow_le_pow_left₀ (spins hk).1 (spins hk).2 _
                                      _ = _:= by ring
   have hv:=crowd z (p:=g) (show (z.filter fun j=>g j≠0).card ≤ D from by
      apply le_trans (card_le_card ?_) (h (leftP s) i z)
      intro x hx; obtain ⟨h1,h2⟩:=mem_filter.1 hx
      apply mem_filter.2 ⟨h1,?_⟩
      intro h; exact h2 (by unfold g; rw [h,zero_mul]))
   change (peeler n k * ∑ j∈z,g j)^4≤ _
   rw [mul_pow,← mul_sum]
   have H (t) (h : in01 t) : t^4≤1:= by
      exact le_trans (pow_le_pow_left₀ h.1 h.2 _) (by norm_num)
   refine le_trans (le_trans (mul_le_mul_of_nonneg_right hh (by positivity)) (le_of_eq (one_mul _))) ?_
   refine hv.trans (mul_le_mul_of_nonneg_left (sum_le_sum ?_) (by positivity))
   intro x hx
   unfold g; rw [mul_pow]
   exact le_trans (mul_le_mul_of_nonneg_left (H _ (he (rightP s) x)) (by positivity)) (le_of_eq (mul_one _))

lemma right_cost {k : ℕ} (f:Pics n) (v:Paint n) (hk:2^k ≤ n) (hl:k≤d.u) {D C}
   (h0:1≤C) (h: Tile (d.deckX k) C D f) (hp : Shelf D f) :
    d.von (d.passV k f v) ≤ (D+1:ℝ)^2*C^4*ratioN d.u k*(d.startd k).von v := by
   have ht (s i):
       (d.passV k f v s i)^4≤
             (D:ℝ)^4*(C^4)^4*∑ j∈d.midpoint k s,
                 if f (leftP s) i j≠0 then v (rightP s) j ^4 else 0 := by
       let S:=d.midpoint k s
       let g:Vec:= fun j=>f (leftP s) i j*v (rightP s) j
       have he (j) : (g j)^4 ≤ (C^4)^4*(if f (leftP s) i j≠0 then v (rightP s) j^4 else 0) := by
          by_cases hn:f (leftP s) i j≠0
          · unfold g; rw [ite_eq_left hn,mul_pow]
            obtain ⟨ha,hb⟩:=from_cap h.cap (leftP s) i j
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hb 4) (by positivity)
          simp only [g,hn,↓reduceIte]; rw [not_not.mp hn]; norm_num
       have hh:(S.filter fun j=>g j≠0).card≤D:= by
          refine le_trans (card_le_card ?_) (h.rows (leftP s) i S)
          intro j hj; obtain ⟨h1,h2⟩:=mem_filter.1 hj
          exact mem_filter.2 ⟨h1,fun h=>h2 (by unfold g; rw [h,zero_mul])⟩
       unfold passV; rw [mul_pow]
       change _ * (∑ j∈S,g j)^4≤ _
       apply le_trans (b:=(∑ j∈S,g j)^4)
       · have hz : (peeler n k)^4≤1:= calc
               _ ≤ (1:ℝ)^4 := pow_le_pow_left₀ (spins hk).1 (spins hk).2 _
               _ = _:=by ring
         exact le_trans (mul_le_mul_of_nonneg_right hz (by positivity)) (le_of_eq (one_mul _))
       rw [mul_assoc, mul_sum]
       exact (crowd S hh).trans (mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> he i) (by positivity))
   let e:=(D+1:ℝ)
   let z:=ratioN d.u k
   let V:=d.startd k
   have hC: 0≤ z:= (box0 _).le
   have hu:= V.vn0 v
   change _≤ e^2*C^4*z*V.von v
   apply (d.vm_le (by positivity)).2
   simp only [mul_pow, von_four]
   rw [d.vi_apply, V.vperm rightP,upper_flip hl]
   let t:=(C^4)^4
   have hiC : 0≤(e^2)^4*t:=by unfold t; positivity
   have hi: (∑ i∈range 0, i)=0:=by simp
   let g (s:Pool n) := ∑ i∈d.midpoint k s,v (rightP s) i^4
   let B:=(e^2)^4*t
   let X (s:Pool n) := ∑ i∈src d.S d.u s,d.passV k f v s i ^4
   change z^4 * scaleM d.N k * av X ≤ B*z^4 * (scaleM d.N k * av g)
   have he (s:Pool n) : X s≤ B*g s := by
      let S:=src d.S d.u s
      apply le_trans (sum_le_sum (fun i (_:i∈S)=> ht s i))
      rw [← mul_sum,sum_comm]
      have hh : ∀ j∈d.midpoint k s, ∑ i∈ S,
              (if f (leftP s) i j≠0 then v (rightP s) j ^4 else 0) ≤ D*v (rightP s) j^4 :=
           fun j _=> slots _ (by positivity) S _ (hp ..)
      have hx : 0≤ g s:= sum_nonneg fun i _=>by positivity
      apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum hh) (by positivity))
      rw [← mul_sum]
      have hl : (D:ℝ)≤e:=by unfold e; linarith
      have hz : 1≤e:=by unfold e; simp
      have hP : (D:ℝ)^4*D≤ (e^2)^4 := calc
         _ ≤ e^4*e:=by have he : 0≤(D:ℝ):=by positivity
                       gcongr
         _ = e^5:= by ring
         _ ≤ (e^2)^4 := by rw [← pow_mul]; exact pow_le_pow_right₀ hz (by omega)
      unfold B; change (D:ℝ)^4*t*((D:ℝ)*g s)≤_
      have ha := mul_le_mul_of_nonneg_right hP (show 0≤ t*g s by unfold t; positivity)
      linarith
   have hv:=av_mono he
   rw [av_cmul] at hv
   apply le_trans (mul_le_mul_of_nonneg_left hv (show 0≤ z^4 * scaleM d.N k from
                        mul_nonneg (by positivity) (scaleM_nn ..)))
   exact le_of_eq (by ring)

lemma pastime {k:ℕ} {p q :Pics n} {x y: Paint n} (hk:2^k≤n) (hl:k≤d.u) {C : ℝ} {D : ℕ}
    (h0:1≤C) (hp:Tile (d.deckX k) C D p) (hq:Tile (d.deckX k) C D q)
    (ht:Shelf D q) (hx:∀ s i,in01 (x s i)) :
    d.von (fun s i=>d.passV k p x s i-d.passV k q y s i) ≤
       2*D*(4*C^3) * (d.deckX k).terr p q +
                   (D+1:ℝ)^2*C^4*ratioN d.u k*(d.startd k).von (fun s i=> x s i-y s i) := by
   let f:Pics n:=fun s i j=>p s i j-q s i j
   let g:Paint n:=fun s i=>x s i-y s i
   have he : (fun s i=> d.passV k p x s i-d.passV k q y s i) =
               fun s i=>d.passV k f x s i+d.passV k q g s i:=by
      ext s i; unfold passV f g
      simp_rw [sub_mul,mul_sub,sum_sub_distrib,mul_sub]; ring
   rw [he]; apply (d.vplus (d.passV k f x) (d.passV k q g)).trans
   have hh : d.von (d.passV k f x) ≤ ((2*D:ℕ):ℝ)*(d.deckX k).ton f := by
      apply d.left_cost f x hk _ hx; intro s i S
      let A:=S.filter (fun j=>p s i j≠0)
      let B:= S.filter (fun j=>q s i j≠0)
      refine le_trans (card_le_card (t:= A∪B) ?_) ((card_union_le ..).trans ?_)
      · intro j hj; obtain ⟨h1,h2⟩:=mem_filter.1 hj
        by_cases hx:p s i j≠0
        · exact mem_union_left _ (mem_filter.2 ⟨h1,hx⟩)
        · apply mem_union_right _; apply mem_filter.2 ⟨h1,?_⟩; intro h; apply h2; unfold f; rw [h,not_not.mp hx]; ring
      · exact le_trans (add_le_add (hp.rows ..) (hq.rows ..)) (by linarith)
   refine add_le_add (hh.trans ?_) (d.right_cost q g hk hl h0 hq ht)
   have hi:= mul_le_mul_of_nonneg_left ((deckX d k).root_fee hp.cap hq.cap h0)
                            (show 0≤ (2*D:ℝ) by positivity)
   change 2*D*(d.deckX k).ton f≤ _ at hi
   push_cast; linarith

lemma pastbound {k D} {p:Pics n} {u:Paint n} {C} (hk:2^k≤n) (h:Tile (deckX d k) C D p)
    (hr:∀ s i,in01 (u s i)) (s i) : 0≤d.passV k p u s i∧d.passV k p u s i ≤ D*C^4 := by
   let S:=midpoint d k s
   let f:Vec:=fun j=>p (leftP s) i j
   let T:=∑ j∈S,f j *u (rightP s) j
   obtain ⟨h1,h2⟩:= spins hk
   have hz : 0≤T:=sum_nonneg fun i _=>mul_nonneg (h.cap ..).1 (hr ..).1
   have he : T≤ D*C^4 := by
      unfold T
      apply le_trans (b:=∑ j∈S, if f j≠0 then C^4 else 0)
      · apply sum_le_sum
        intro j hj
        by_cases hi : f j≠0
        · rw [ite_eq_left hi]
          obtain ⟨hx,hy⟩:=from_cap h.cap (leftP s) i j
          change 0≤f j at hx; change f j≤_ at hy
          nlinarith [(hr (rightP s) j).2]
        rw [ite_eq_right hi,not_not.mp hi,zero_mul]
      exact slots _ (by positivity) S _ (h.rows ..)
   change 0≤peeler n k*T∧ peeler n k*T≤_
   exact ⟨mul_nonneg h1 hz,le_trans (by nlinarith) he⟩

end Axis
end
end ExactDerandomization.Est

end

end OAI
