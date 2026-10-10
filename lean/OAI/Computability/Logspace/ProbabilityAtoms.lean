import OAI.Computability.Logspace.AffineSampling
import OAI.Computability.Logspace.ProbabilityHierarchy

namespace OAI

/-!
Rank cutoffs, bounded row atoms, and their Lipschitz estimates.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Analysis
noncomputable section

def clip (a b x : ℝ) := min b (max a x)
def sat (u : ℝ) := clip (-u) u

lemma clip_ic (a b) : Ic 1 (clip a b) := by intro x y e; unfold clip; grind
lemma clip_lip (a b) : Lip 1 (clip a b) := (clip_ic a b).lip
lemma clip_bounds {a b} (h:a≤b) (x) : a≤ clip a b x ∧ clip a b x≤b := by unfold clip; grind
lemma sandwich {u a b:ℝ} (h:-u≤a) (e:b≤u) (x) :
    clip a b (sat u x)=clip a b x := by unfold sat clip; grind

lemma Lip.raise {a b f} (h : Lip a f) (e:a≤b) : Lip b f :=
   fun x y=> le_trans (h x y) (mul_le_mul_of_nonneg_right e (abs_nonneg _))

lemma Lip.chain {a b f g} (h : Lip a f) (e : Lip b g) (ha:0≤a) :
    Lip (a*b) (fun x=>f (g x)) := by
  intro x y
  refine le_trans (h (g x) (g y)) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (e x y) ha

/-- Building block with bounded fourth-root Lipschitz norm and bounded
sensitivity range. The constants here need not be the algorithmic
clamp coefficients. -/
structure Frag (c : ℝ) (f : ℝ → ℝ) : Prop where
  one : 1≤ c
  nn : ∀ x,0 ≤ f x
  ub : ∀ x,fourth (f x) ≤ c
  lip : Lip c (fun x=>fourth (f x))
  flat : ∀ x,f (sat c x)=f x

lemma Frag.raise {c f} (h : Frag c f) {b} (hb:c≤b) : Frag b f := by
  refine ⟨h.one.trans hb,h.nn,fun x=>(h.ub x).trans hb,h.lip.raise hb,fun x=>?_⟩
  calc f (sat b x) = _:= (h.flat _).symm
       _ = f (sat c x) := by
            unfold sat
            rw [show clip (-c) c (clip (-b) b x)=clip (-c) c x from sandwich (by linarith) hb x]
       _ = _:=h.flat x

lemma Frag.lipprod {c d : ℝ} {f g p q : ℝ}
    (he:|f| ≤ c) (hg:|q|≤d) :
    |f*p-g*q| ≤ c * |p-q| + d  * |f-g| := by
  have hv : f*p-g*q=f*(p-q)+q*(f-g) := by ring
  rw [hv]
  refine (abs_add_le ..).trans ?_
  rw [abs_mul,abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right he (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hg (abs_nonneg _))

lemma Frag.mul {c d f g} (h:Frag c f) (e:Frag d g) :
    Frag (2*c*d) (fun x=> f x*g x) := by
  have hc:=h.one; have hd:=e.one
  have hk x : fourth (f x*g x)=fourth (f x)*fourth (g x) :=
     fourth_mul (h.nn x)
  have hs (b : ℝ) (ht:1≤b): 0≤b := by linarith
  refine ⟨by nlinarith,fun x=>mul_nonneg (h.nn _) (e.nn _),fun x=>?_,fun x y=>?_,fun x=>?_⟩
  · rw [hk]
    have ht := mul_le_mul (h.ub x) (e.ub x) (fourth_nn _) (hs c hc)
    nlinarith
  · simp only [hk]
    have he (x : ℝ) : |fourth x|=fourth x := abs_of_nonneg (fourth_nn _)
    refine (Frag.lipprod (c:=c) (d:=d) (by rw [he];apply h.ub)
         (by rw [he]; apply e.ub)).trans ?_
    have ht := mul_le_mul_of_nonneg_left (h.lip x y) (hs d hd)
    have hy := mul_le_mul_of_nonneg_left (e.lip x y) (hs c hc)
    dsimp only at ht hy
    linarith
  · have hx := (h.raise (b:=2*c*d) (by nlinarith)).flat x
    have he := (e.raise (b:=2*c*d) (by nlinarith)).flat x
    simp only [hx,he]

lemma Frag.scale_clip {c f} (h:Frag c f) {u d a b:ℝ} (hu:|u|≤d) :
    Frag (c*d + |a| + |b| + c) (fun x=> f (u*clip a b x)) := by
  let z:=c*d+|a|+|b|+c
  have hc := h.one; have hd:=abs_nonneg u; have he:=abs_nonneg a; have ht:=abs_nonneg b
  have hv : c≤z := by dsimp only [z]; nlinarith
  refine ⟨h.one.trans hv,fun _=>h.nn _,fun x=> le_trans (h.ub _) hv,fun x y=>?_,fun x=>?_⟩
  · have hh : |u * clip a b y-u*clip a b x|≤d * |y-x| := by
      rw [← mul_sub,abs_mul]
      have h := clip_lip a b x y
      rw [one_mul] at h
      exact mul_le_mul hu h (abs_nonneg _) (le_trans hd hu)
    have hz := mul_le_mul_of_nonneg_left hh (show 0≤c by linarith)
    dsimp only [z]
    calc _ ≤ _ := h.lip (u*clip a b x) (u*clip a b y)
         _ ≤ _ := by nlinarith [abs_nonneg (y-x)]
  · rw [sandwich]
    · nlinarith [neg_le_abs a]
    · nlinarith [le_abs_self b]

lemma Frag.cnst (x : ℝ) (h:0≤x) : Frag (1+fourth x) (fun _=>x) :=
   ⟨by linarith [fourth_nn x],fun _=>h,fun _=>by linarith,by
     intro a b; simp; have := fourth_nn x; positivity,fun _=>rfl⟩

/-- convenient sufficient condition for bounded-away-from-zero leaves -/
lemma rootSlope {z x y : ℝ} (h:0<z) (hx:z≤x) (hy:z≤y) :
    |fourth y-fourth x| ≤ |y-x|/(fourth z)^3 := by
  have hu (a b : ℝ) (ha:z≤a) (hab:a≤b) :
       |fourth b-fourth a| ≤ |b-a|/(fourth z)^3 := by
    let r:= fourth z; let s:=fourth a; let t:=fourth b
    have hr : 0<r:=fourth_pos h
    have hs : r ≤ s:= fourth_mono ha
    have ht : s≤t:= fourth_mono hab
    change |t-s| ≤ |b-a|/r^3
    rw [abs_of_nonneg (sub_nonneg.mpr ht), abs_of_nonneg (sub_nonneg.mpr hab),
       le_div_iff₀ (pow_pos hr _)]
    have hj : r^3≤t^3+t^2*s+t*s^2+s^3 := by
      have hv : r^3 ≤ s^3 := pow_le_pow_left₀ (le_of_lt hr) hs 3
      have h1:0<s := lt_of_lt_of_le hr hs; have h2:0<t:=lt_of_lt_of_le h1 ht
      exact le_trans hv (le_add_of_nonneg_left (by positivity))
    have he : s^4=a:=fourth_four (by linarith)
    have hg : t^4=b:=fourth_four (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr ht)]
  rcases le_total x y with h|h
  · exact hu x y hx h
  · rw [abs_sub_comm,abs_sub_comm y x]
    exact hu y x hy h

lemma frag_positive {low high u c : ℝ} {f : ℝ→ℝ} (h:0<low)
   (_:0≤u) (e : ∀ x, low ≤ f x ∧ f x≤high)
   (he : Lip c f) (hh : ∀ x,f (sat u x)=f x) :
    ∃ c', Frag c' f := by
  let C := max (max u 1) (max (fourth high) (c/(fourth low)^3))
  have hs : 1≤C ∧ u≤C ∧ fourth high≤C ∧ c/(fourth low)^3≤C := by unfold C; grind
  refine ⟨C,hs.1,fun x=> le_trans (le_of_lt h) (e x).1,fun x=>
          le_trans (fourth_mono (e x).2) hs.2.2.1, ?_,fun x=>?_⟩
  · refine Lip.raise (a:=c/(fourth low)^3) ?_ hs.2.2.2
    intro x y
    have hy := rootSlope h (e x).1 (e y).1
    exact hy.trans (by rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right (he x y) (pow_nonneg (fourth_nn _) _ ))
  · have hee : sat u (sat C x)=sat u x := sandwich (by linarith [hs.2.1]) hs.2.1 x
    calc _ = f (sat u (sat C x)) := (hh _).symm
         _ = _ := by rw [hee,hh]

lemma frag_switch {a b : ℝ} (h:a<b) :
    ∃ c, Frag c (rising a b) ∧ Frag c (fun x=>1-rising a b x) := by
  obtain ⟨v,hv,hr,hn⟩ := rising_root h
  let c:=max (max (-a) b) (max 1 v)
  have hh : -a≤c ∧ b≤c ∧ 1≤c ∧ v≤c := by unfold c; grind
  have h0 {x:ℝ} (hx:x≤1) : fourth x ≤ c := by
    exact (fourth_mono hx).trans (by simpa [fourth] using hh.2.2.1)
  have hf (x) : rising a b (sat c x)=rising a b x := by
    unfold sat clip
    rcases le_total x (-c) with hl|hl
    · rw [rising_bot h (by grind),rising_bot h (by linarith [hh.1])]
    rcases le_total c x with he|he
    · rw [rising_top h (by grind),rising_top h (by grind)]
    rw [max_eq_right hl,min_eq_right he]
  refine ⟨c,⟨hh.2.2.1,fun _=>(rising_mem ..).1,fun _=> h0 (rising_mem ..).2,
        hr.raise hh.2.2.2,hf⟩,hh.2.2.1,fun x=>?_,fun x=>?_,hn.raise hh.2.2.2,fun x=>?_⟩
  · exact sub_nonneg.mpr (rising_mem ..).2
  · exact h0 (sub_le_self _ (rising_mem ..).1)
  · simp only [hf]

end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.At
noncomputable section
open Analysis Hie Finset

abbrev cut := rising (1/2) 1
lemma cut_low {x : ℝ} (h:x≤1/2) : cut x=0 := rising_bot (by norm_num) h
lemma cut_high {x : ℝ} (h:1≤x) : cut x=1 := rising_top (by norm_num) h

def highcut (k : ℕ) (d : ℝ) := if k=0 then 1 else 1-cut (d/16)
def sw (k : ℕ) (d : ℝ) := cut d * highcut k d
def bin (k : ℕ) (x : ℝ) := x*sw k (x/rate k)
lemma high_mem (k) (x) : in01 (highcut k x) := by
  unfold highcut
  split
  · unfold in01; norm_num
  obtain ⟨h,h'⟩:= rising_mem (1/2:ℝ) 1 (x/16)
  unfold in01 cut; constructor <;> linarith
lemma sw_mem (k) (x) : in01 (sw k x) := by
  unfold sw
  have hh : in01 (cut x):=rising_mem ..; have hs:=high_mem k x
  exact ⟨mul_nonneg hh.1 hs.1,(mul_le_mul hh.2 hs.2 hs.1 zero_le_one).trans_eq (by norm_num)⟩
lemma bin_mem {x k} (h:0≤x) : 0 ≤ bin k x ∧ bin k x ≤ x := by
  obtain ⟨h1,h2⟩:=sw_mem k (x/rate k)
  exact ⟨mul_nonneg h h1,(mul_le_mul_of_nonneg_left h2 h).trans_eq (by ring)⟩

lemma sw_bot {x k} (h:x≤1/2) : sw k x=0 := by rw [sw,cut_low h]; ring
lemma sw_top {x k} (h:16≤x) (e:k≠0) : sw k x=0 := by
  rw [sw,highcut,ite_eq_right e,cut_high (show 1≤x/16 by linarith)]; ring

lemma sw_succ (k x) : sw (k+1) x=cut x-cut (x/16) := by
   rw [sw,highcut,ite_eq_right (by omega)]
   rcases le_total 1 x with h|h
   · rw [cut_high h]; ring
   · rw [cut_low (by linarith : x/16≤1/2)]; ring

lemma rate_step (k) : rate (k+1)=rate k/16 := by
  unfold rate; rw [pow_succ]; ring
lemma rate0 : rate 0=1 := by norm_num [rate]
lemma rate_small (k) : rate k≤1 := by
  induction k with
  | zero=>exact le_of_eq rate0
  | succ k ih=>rw [rate_step]; linarith

lemma telescope (x k) : ∑ j∈range (k+1), bin j x=x*cut (x/rate k) := by
  induction k with
  | zero=>simp [bin,sw,highcut]
  | succ k ih=>
    rw [sum_range_succ,ih,bin,sw_succ]
    rw [show x/rate (k+1)/16=x/rate k from by rw [rate_step]; ring]
    ring

lemma discarded {x k} (h:0≤x) :
    let r := x-∑ j∈range (k+1),bin j x
    0 ≤ r ∧ r ≤ rate k ∧ r ≤ x := by
  rw [telescope]
  have he : in01 (cut (x/rate k)) := rising_mem ..
  rcases le_total (rate k) x with hx|hx
  · rw [cut_high (by rw [le_div_iff₀ (rate_pos _)]; linarith)]
    simp [h,le_of_lt (rate_pos _)]
  · obtain ⟨h1,h2⟩:=he
    dsimp; exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

def cap (P : Const) : ℝ := P.T+32
lemma cap_hi (P) : 16≤cap P := by unfold cap; linarith
def tone (P : Const) := clip (1/2) (cap P)
def dirShare (P : Const) (i : Option ℕ) (x : ℝ) :=
   match i with
   | none=>1
   | some i=> share P.M i x
def bfrag (P) (k l) (i : Option ℕ) (d : ℝ) :=
   tone P d * sw k (tone P d)*dirShare P i (rate k/rate l*tone P d)

lemma tone_mem (P d) : 1/2 ≤ tone P d ∧ tone P d≤cap P :=
    clip_bounds (by linarith [cap_hi P]) d
lemma bfrag_low (P k l i) {d} (h:d≤1/2) :
    bfrag P k l i d=0 := by
  have e: tone P d=1/2:=by unfold tone clip; rw [max_eq_left h,min_eq_right (by linarith [cap_hi P])]
  rw [bfrag,e,sw_bot (le_refl _)]; ring
lemma bexact (P k l i) (x : ℝ) (h : x ≤ (P.T+1:ℝ)*rate l) :
    rate k*bfrag P k l i (x/rate k)=bin k x * dirShare P i (x/rate l) := by
  let d:=x/rate k
  rcases le_total d (1/2) with hd|hd
  · rw [bfrag_low _ _ _ _ hd,bin,sw_bot hd]; ring
  rcases le_total d (cap P) with he|he
  · have ee : tone P d=d := by unfold tone clip; rw [max_eq_right hd,min_eq_right he]
    change rate k*(tone P d*sw k (tone P d)* _)=_
    rw [ee]
    unfold bin; dsimp only [d]; field_simp [ne_of_gt (rate_pos k)]

  · have ht:P.T+1<cap P := by unfold cap; linarith
    have hh : k≠0 := by
      intro h'
      have hu := rate_small l
      have hv : d=x := by unfold d; rw [h',rate0,div_one]
      nlinarith
    rw [bfrag,bin, sw_top (le_trans (cap_hi _) he) hh]
    have ee : tone P d=cap P := by unfold tone clip; rw [max_eq_right hd,min_eq_left he]
    change rate k*(tone P d * sw k (tone P d) * _) = _
    rw [ee,sw_top (cap_hi P) hh]; ring

lemma hiRatio (P : Const) (k) {x} (h:0≤x) (hs : x ≤ (P.T+1 : ℝ)) :
   bin k x ≤ cap P*rate k := by
  by_cases e:k=0
  · refine le_trans (bin_mem h).2 ?_
    rw [e,rate0]
    unfold cap; linarith
  rcases le_total 16 (x/rate k) with ht|ht
  · rw [bin,sw_top ht e]
    have h0:= rate_pos k; have he:=cap_hi P; nlinarith
  · have h0:= (div_le_iff₀ (rate_pos _)).mp ht
    have he:=cap_hi P; exact le_trans (bin_mem h).2
                    (le_trans h0 (by gcongr; exact le_of_lt (rate_pos _)))

lemma dir_regular (P : Const) :
   ∃ c:ℝ, ∀ i, Frag c (dirShare P i) := by
  have hA : bound0<bound1 := by norm_num
  obtain ⟨c1,hc1,-⟩:= frag_switch hA
  have h0 : 0<P.M := by have := P.mOK; omega
  have hp : 0<(P.M:ℝ) := by exact_mod_cast h0
  let q:ℝ := (P.M:ℝ)⁻¹
  have he : 0<q := inv_pos.mpr hp
  have hm : 1≤ (P.M:ℝ):= by exact_mod_cast h0
  have hl : ∀ x, q ≤ share P.M 0 x ∧ share P.M 0 x ≤ 1 := by
    intro x
    refine ⟨?_,share_le h0 _⟩
    unfold share Hie.slice
    rw [ite_eq_left rfl, div_eq_mul_inv]
    obtain ⟨hv,hu⟩ := rising_mem bound0 bound1 x
    change q ≤ 1-_+_*q
    have hh:q ≤ 1 := by unfold q; rw [inv_le_one₀ hp]; exact hm
    nlinarith
  have hR := (rising_ic hA).lip
  let Z := 8/(bound1-bound0)
  obtain ⟨cr,hr⟩ := frag_positive (f:=share P.M 0) (c:=Z*(1+q)) (u:=c1) he
    (by linarith [hc1.one]) hl (by
      intro x y
      let g z := Hie.slice z
      change |(share ..)-(share ..)|≤_
      have hl : share P.M 0 y-share P.M 0 x = -(g y-g x)+(g y-g x)*q := by
        unfold share g q; simp only [ite_true,div_eq_mul_inv]; ring
      have h1 : |g y-g x|≤ Z * |y-x|:=hR x y
      rw [hl]
      refine (abs_add_le ..).trans ?_
      rw [abs_neg,abs_mul,abs_of_pos he]
      nlinarith [mul_le_mul_of_nonneg_right h1 he.le]) (by intro x; unfold share Hie.slice; rw [hc1.flat])
  let v := 2*c1*(1+fourth q)
  have hv (i : ℕ) (h:i≠0) : Frag v (share P.M i) := by
    unfold share
    simpa only [share,h,↓reduceIte,zero_add,div_eq_mul_inv,Hie.slice] using
               hc1.mul (Frag.cnst q (le_of_lt he))
  let b:=max cr (max v (1+fourth 1))
  refine ⟨b,fun i=>?_⟩
  cases i with
  | none=> exact (Frag.cnst 1 (by norm_num)).raise (by unfold b; grind)
  | some i=>
    rcases eq_or_ne i 0 with h|h
    · subst i; exact hr.raise (le_max_left ..)
    · exact (hv i h).raise (by unfold b; grind)

lemma bin_reg (P : Const) (R : ℝ) :
    ∃ c:ℝ, ∀ k l i, rate k/rate l≤R → Frag c (bfrag P k l i) := by
  let a:ℝ:=1/2
  let u:=cap P
  obtain ⟨cl,hl⟩ := frag_positive (f:=tone P) (c:=1) (u:=u)
          (show 0<a by norm_num [a]) (show 0≤u by linarith [cap_hi P]) (tone_mem P)
           (clip_lip a u) (fun x=>sandwich (show -u ≤ a by have:=cap_hi P; dsimp only [u,a]; linarith) le_rfl x)
  obtain ⟨cs,hchi,hbar⟩:=frag_switch (show a<1 by norm_num [a])
  obtain ⟨cr,hr⟩:=dir_regular P
  let K (c d:ℝ) := c*d+|a|+|u|+c
  have hu : Frag (K cs 1) (fun x=>cut (tone P x)) := by
    simpa only [K,one_mul,tone] using hchi.scale_clip
                      (a:=a) (b:=u) (d:=1) (show |(1:ℝ)|≤ 1 by norm_num)
  let v := max (K cs (1/16)) (1+fourth 1)
  have he k : Frag v (fun x=> highcut k (tone P x)) := by
    by_cases h:k=0
    · simp only [highcut,h, ↓reduceIte]
      exact (Frag.cnst 1 (by norm_num)).raise (le_max_right ..)
    · simp only [highcut,h, ↓reduceIte,cut]
      have H:=hbar.scale_clip (a:=a) (b:=u) (show |(1/16:ℝ)| ≤ 1/16 by norm_num)
      refine Frag.raise ?_ (le_max_left ..)
      convert H using 1
      ext x
      congr 2; change tone P x/16=1/16*tone P x; ring
  refine ⟨2*(2*cl*(2*K cs 1*v))*K cr R,fun k l i h=>?_⟩
  have hh := (hr i).scale_clip (a:=a) (b:=u) (d:=R) (show |rate k/rate l|≤R by
     rw [abs_of_pos (div_pos (rate_pos _) (rate_pos _))]
     exact h)
  exact (hl.mul (hu.mul (he k))).mul hh

def Qc (P : Const) (x : ℝ) := Q (clip 0 (cap P) x)
lemma shoulder_reg (P : Const) : ∃ c:ℝ, Frag c (Qc P) := by
  obtain ⟨c,hc,h⟩ := shoulder_root A A (by norm_num [A])
  let b:=cap P
  let C:=max b (max c (fourth (Q b)))
  have H : 16≤b := cap_hi P
  have H' : b≤C ∧ c≤C ∧ fourth (Q b) ≤ C := by unfold C; grind
  refine ⟨C,by linarith [H'.1],fun x=> Qnn _,fun x=>?_,?_,?_⟩
  · refine le_trans (fourth_mono ?_) H'.2.2
    exact (Qic _ _ (clip_bounds (by linarith) _).2).1
  · exact (h.lip.chain (clip_lip 0 b) hc.le).raise (by rw [mul_one]; exact H'.2.1)
  · intro x; unfold Qc; rw [sandwich (by linarith [H'.1]) H'.1]

lemma Qc_low {P x} (h:x≤A) : Qc P x=0 := by
  exact shoulder_bot (by norm_num [A]) (show clip 0 (cap P) x ≤ A by
    unfold clip; have : (0:ℝ)≤A:=by norm_num [A]
    exact (min_le_right ..).trans (max_le this h))

end
end ExactDerandomization.At

end

section

namespace ExactDerandomization.At
noncomputable section
open Analysis Hie Finset

abbrev small : ℝ := delta/1000000
abbrev zeta : ℝ := small/1000

lemma zp : 0 < zeta := by norm_num [zeta,small,delta,A]
lemma dp : 0 < delta := by norm_num [delta,A]

/-- use identically clipped denominators on any input -/
def den (x : ℝ) := clip (zeta/2) zeta x/zeta
def divisor (x : ℝ) := (den x)⁻¹
lemma within_den (x) : 1/2 ≤ den x ∧ den x ≤ 1 := by
  have hp:=zp
  have h:=clip_bounds (a:=zeta/2) (b:=zeta) (by linarith) x
  unfold den; constructor
  · rw [le_div_iff₀ hp]; linarith [h.1]
  · rw [div_le_iff₀ hp]; linarith [h.2]
lemma inv_den (x) : 1 ≤ divisor x ∧ divisor x ≤ 2 := by
  have h:=within_den x
  have hp : 0 < den x := by linarith [h.1]
  unfold divisor
  rw [inv_eq_one_div,le_div_iff₀ hp,div_le_iff₀ hp]
  constructor <;> linarith [h.1,h.2]
lemma den_reg : ∃ c,Frag c divisor := by
  have hz:=zp
  refine frag_positive zero_lt_one hz.le inv_den (c:=4/zeta) ?_ ?_
  · intro x y
    let p:=den x
    let q:=den y
    have h : 1/2 ≤ p ∧ p ≤ 1 := within_den x
    have e : 1/2 ≤ q ∧ q ≤ 1 := within_den y
    have hp : 0<p := by linarith [h.1]
    have hq : 0<q := by linarith [e.1]
    change |q⁻¹-p⁻¹|≤ _
    rw [show q⁻¹-p⁻¹=(p-q)/(p*q) from by field_simp, abs_div,abs_of_pos (mul_pos hp hq)]
    have hg : |p-q| ≤ |y-x|/zeta := by
      unfold p q den; rw [← sub_div,abs_div,abs_of_pos hz]
      have h:=clip_lip (zeta/2) zeta x y
      rw [abs_sub_comm _ (clip _ _ y)]
      rw [one_mul] at h
      gcongr
    have ht : 1/4≤p*q := by nlinarith [e.1,h.1]
    rw [div_le_iff₀ (mul_pos hp hq)]
    refine le_trans hg ?_
    have hx:=abs_nonneg (y-x)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hz]; nlinarith
  · intro x
    unfold divisor den
    rw [sandwich (by linarith) le_rfl]

/-- Uniform finite list of pre-incoming figures; product of independent
scalar pieces. -/
structure Trio where
  start : ℝ→ℝ
  row : ℝ→ℝ
  quo : ℝ→ℝ

def Trio.eval (f : Trio) (x r q : ℝ) := f.start x*f.row r*f.quo q

structure TS (z C : ℝ) (f : Trio) : Prop where
  start : Frag C f.start
  row : Frag C f.row
  quo : Frag C f.quo
  shut : ∀ x≤z/8,f.start x=0
  off : ∀ x≥z/40,f.row x=0
  full : ∀ x≤eta z,f.row x=1

lemma TS.nn {z C f} (h : TS z C f) x r q : 0≤ f.eval x r q :=
  mul_nonneg (mul_nonneg (h.start.nn x) (h.row.nn r)) (h.quo.nn q)
lemma TS.base {z C f} (h : TS z C f) x r q :
    fourth (f.eval x r q)=fourth (f.start x)*fourth (f.row r)*fourth (f.quo q) := by
  unfold Trio.eval; rw [fourth_mul (mul_nonneg (h.start.nn x) (h.row.nn r)),
    fourth_mul (h.start.nn x)]
lemma TS.flat {z C f} (h : TS z C f) x r q :
    f.eval (sat C x) (sat C r) (sat C q)=f.eval x r q := by
  simp only [Trio.eval,h.start.flat,h.row.flat,h.quo.flat]
lemma TS.rootub {z C f} (h : TS z C f) x r q : fourth (f.eval x r q) ≤ C^3 := by
  rw [h.base]
  have hh:=h.row.one
  have he:=mul_le_mul (h.start.ub x) (h.row.ub r) (fourth_nn _) (by linarith)
  exact (mul_le_mul he (h.quo.ub q) (fourth_nn _) (by positivity)).trans_eq (by ring)

lemma TS.comparison {z C f} (h : TS z C f) {x x' r r' q q' a : ℝ}
    (e1:|x-x'|≤a) (e2:|r-r'|≤a) (e3:|q-q'|≤a) :
    |fourth (f.eval x r q)-fourth (f.eval x' r' q')|≤ 3*C^3*a := by
  have hh:=h.start.one
  have e0 : 0≤ C := by linarith
  let root (g : ℝ→ℝ) (x : ℝ):=fourth (g x)
  have he (g : ℝ→ℝ) (h : Frag C g) (x): |root g x| ≤ C := by
    rw [abs_of_nonneg (fourth_nn _)]; exact h.ub x
  have he' (g : ℝ→ℝ) (h : Frag C g) (x y) (hi : |x-y|≤a):
      |root g x-root g y|≤ C*a := le_trans (h.lip y x) (mul_le_mul_of_nonneg_left hi e0)
  rw [h.base,h.base]
  have hu := Frag.lipprod (c:=C) (d:=C) (he _ h.start x) (he _ h.row r')
             (g:=root f.start x') (p:=root f.row r)
  have hv : |root f.start x * root f.row r-root f.start x'*root f.row r'| ≤ 2*C^2*a := by
    have h1:=mul_le_mul_of_nonneg_left (he' _ h.start x x' e1) e0
    have h2:=mul_le_mul_of_nonneg_left (he' _ h.row r r' e2) e0
    linarith
  have ht := Frag.lipprod (c:=C*C) (d:=C)
      (show |root f.start x*root f.row r| ≤ C*C from by
        rw [abs_mul]; exact mul_le_mul (he _ h.start _) (he _ h.row _) (abs_nonneg _) e0)
      (he _ h.quo q') (g:=root f.start x'*root f.row r') (p:=root f.quo q)
  unfold root at ht he' hv
  have hq := mul_le_mul_of_nonneg_left (he' _ h.quo q q' e3) (show 0≤C*C by positivity)
  have hp := mul_le_mul_of_nonneg_left hv e0
  linarith

lemma TS.extend {f t c d} (h:TS t c f) (e:c≤d) : TS t d f :=
  ⟨h.start.raise e,h.row.raise e,h.quo.raise e,h.shut,h.off,h.full⟩

def mainT (t : ℝ) (phi : ℝ→ℝ) (q : Bool) : Trio :=
  { start:=phi,row:=gate t,quo:= if q then divisor else fun _=>1 }
def prep (t : ℝ) := rising (t/2) (3*t/4)
def prepT (t) := mainT t (prep t) false

/-- auxiliary and all-purpose witness. -/
def suppT (t : ℝ) (b : Bool) : Trio :=
  if b then ⟨rising (t/8) (t/6),fun x=>1-rising (t/50) (t/40) x,fun _=>1⟩
  else ⟨rising (t/4) (t/3),fun x=>1-rising (t/200) (t/100) x,fun _=>1⟩

lemma main_ts {t C} (h : 0<t) :
    ∃ c, ∀ f, Frag C f → (∀ x ≤ t/2, f x=0) →
                      ∀ b, TS t c (mainT t f b) := by
  have hg : 0<eta t := div_pos h (by norm_num)
  obtain ⟨d,-,he⟩ := frag_switch (show eta t<2*eta t by linarith)
  obtain ⟨r,hr⟩:=den_reg
  have ht := Frag.cnst 1 zero_le_one
  let c:=max C (max d (max r (1+fourth 1)))
  refine ⟨c,fun f hh hp b=>⟨hh.raise (by unfold c; grind),he.raise (by unfold c; grind),
    ?_, fun x hx=>hp x (by linarith),fun x hx=> gate_shut h x ?_,gate_full h⟩⟩
  · cases b
    · exact ht.raise (by unfold c; grind)
    · exact hr.raise (by unfold c; grind)
  · unfold eta; linarith

lemma supp_ts0 {a b c d t : ℝ} (_ : 0<t) (ha:a<b) (hc:c<d)
    (hl : t/8 ≤ a) (hh:d ≤ t/40) (he:eta t ≤ c) :
    ∃ C, TS t C ⟨rising a b,fun x=>1-rising c d x,fun _=>1⟩ := by
  obtain ⟨s,h,-⟩:=frag_switch ha
  obtain ⟨r,-,e⟩:=frag_switch hc
  let C:=max s (max r (1+fourth 1))
  refine ⟨C,h.raise (by unfold C; grind),e.raise (by unfold C; grind),
    (Frag.cnst 1 zero_le_one).raise (by unfold C; grind),
    fun x h => rising_bot ha (le_trans h hl),
    fun x h=> ?_,fun x h=>?_⟩ <;> dsimp only
  · rw [rising_top hc (le_trans hh h)]; ring
  · rw [rising_bot hc (le_trans h he)]; ring

lemma supp_ts {t : ℝ} (h:0<t) :
    ∃ c,∀ b,TS t c (suppT t b) := by
  have hh : eta t≤ t/200 := by unfold eta; linarith
  obtain ⟨s,hs⟩:=supp_ts0 h (show t/8<t/6 by linarith)
             (show t/50<t/40 by linarith) le_rfl le_rfl (by linarith)
  obtain ⟨r,hr⟩:=supp_ts0 h (show t/4<t/3 by linarith)
             (show t/200<t/100 by linarith) (by linarith) (by linarith) hh
  exact ⟨max r s, fun b=>by cases b
                            · exact hr.extend (le_max_left ..)
                            · exact hs.extend (le_max_right ..)⟩

end
end ExactDerandomization.At

end

section

namespace ExactDerandomization.At
noncomputable section
open Analysis Hie Finset

abbrev Pt := ℝ × ℝ
structure Blob where
   base : ℝ
   ts : ℕ → Pt

namespace Blob

def rk (S : Domain) (K : ℕ) (u : Blob) :=
    max (rank S (fun i=>(u.ts i).1) K) u.base
def val (S : Domain) (K : ℕ) (u : Blob) (f : Trio) (i) :=
    f.eval (u.ts i).1 (rk S K u) (u.ts i).2

lemma thin {S S' : Domain} {u : Blob} {K} {b c : ℝ} (h : S' ⊆ S) (hc : 0≤c) (hb:c < b)
    (hi : ∀ i∈S', b ≤ (u.ts i).1 ∧ u.rk S K ≤ c) :
    S'.card ≤ K := by
  by_contra! he
  obtain ⟨i,hh⟩ := card_pos.mp (lt_of_le_of_lt K.zero_le he)
  let v:=fun i=>(u.ts i).1
  have ht : S' ⊆ S.filter (fun i=> b ≤ v i) :=
     fun j hk=>mem_filter.2 ⟨h hk,(hi j hk).1⟩
  have hs := (@rank_ge _ S v K b (lt_of_le_of_lt hc hb)).mpr
                        (lt_of_lt_of_le he (card_le_card ht))
  exact (not_le_of_gt hb) (le_trans hs (le_trans (le_max_left ..) (hi i hh).2))

lemma support_size {f : Trio} {t C} (h : TS t C f) (e:0<t)
     (u : Blob) (S : Domain) (K : ℕ) :
    (S.filter (fun i=>u.val S K f i≠0)).card ≤ K := by
  apply thin (u:=u) (b:=t/8) (c:=t/40) (filter_subset ..) (by linarith) (by linarith)
  intro i hk; have he: f.eval _ (u.rk S K) (u.ts i).2≠0:= (mem_filter.mp hk).2
  constructor
  · by_contra! hs; apply he
    unfold Trio.eval; rw [h.shut _ (le_of_lt hs)]; ring
  · by_contra! hs; apply he
    unfold Trio.eval; rw [h.off _ (le_of_lt hs)]; ring

/-- Consistency with deterministic finite approximations for access. -/
structure Guess where
  first : ℕ → ℝ
  kth : ℝ

def acc (g : Guess) (u : Blob) (S : Domain) (K) (t : ℝ) :=
     (∀ i∈S, |(u.ts i).1-g.first i|≤t/10000) ∧
           |u.rk S K-g.kth|≤t/10000

/-- b=false exposes main, true exposes the first (precursor) witness
(for purposes of rank). -/
def expose (t : ℝ) (g : Guess) (b : Bool) (S : Domain) :=
   if b then S.filter (fun i=> t/5 < g.first i ∧ g.kth < t*(15/1000))
        else S.filter (fun i=> 5*t/12 < g.first i ∧ g.kth < t*(35/10000))

lemma expose_subset (S) (t) (g) (b) : expose t g b S ⊆ S := by
  unfold expose; split <;> apply filter_subset

lemma has_room {t} {g u S K} (hg : acc g u S K t) (he:0<t) {b} {i} (h : i∈expose t g b S) :
    (u.ts i).1 > (if b then t/6 else t/3) ∧
       u.rk S K < (if b then t/50 else t/200) := by
    obtain ⟨p,q⟩:=hg
    obtain ⟨h1,h2⟩:=abs_le.1 (p i (expose_subset _ _ _ _ h))
    obtain ⟨h3,h4⟩:=abs_le.1 q
    cases b <;>
      (simp only [expose,Bool.false_eq_true,ite_false,ite_true,mem_filter] at h ⊢
       obtain ⟨-,a,b'⟩:=h
       constructor <;> linarith)

lemma protects {t} {g u S K} (hg : acc g u S K t) (he:0<t) {b} {i} (h : i∈expose t g b S) :
    u.val S K (suppT t b) i = 1 := by
  obtain ⟨ha,hb⟩:= has_room hg he h
  cases b <;> (
    simp only [ite_false,ite_true,Bool.false_eq_true,val,suppT,Trio.eval] at *
    rw [rising_top (by linarith) (le_of_lt ha), rising_bot (by linarith) (le_of_lt hb)]
    ring)

lemma exposure_count {t} {g u S K} (hg : acc g u S K t) (he:0<t) (b) :
    (expose t g b S).card ≤ K := by
  refine thin (u:=u) (b:=t/6) (c:=t/50) (expose_subset ..) (by linarith)
                    (by linarith) (fun i h=>?_)
  obtain ⟨p,q⟩:=has_room hg he h
  cases b <;> (simp only [ite_false,ite_true,Bool.false_eq_true] at *; constructor <;> linarith)

lemma exposed_main {t} {g u S K} (hg : acc g u S K t) (he:0<t) {i} (hi:i∈S)
    (v) {f} (hp : ∀ x≤t/2,f x=0)
    (hh : u.val S K (mainT t f v) i≠0) : i∈expose t g false S := by
  have e1 : t/2 < (u.ts i).1 := by
     by_contra! h
     apply hh
     simp [mainT,val,Trio.eval,hp _ h]
  have e2 : rk S K u<2*eta t := by
     by_contra! h
     apply hh
     simp [mainT,val,Trio.eval, gate_shut he _ h]
  obtain ⟨h1,h2⟩:=abs_le.1 (hg.1 i hi)
  obtain ⟨h3,h4⟩:=abs_le.1 hg.2
  unfold eta at e2
  exact mem_filter.mpr ⟨hi,by linarith,by linarith⟩

lemma exposed_supp {t} {g u S K} (hg : acc g u S K t) (he:0<t) {i} (hi:i∈S)
    (hh : u.val S K (suppT t false) i≠0) : i∈expose t g true S := by
  have e1 : t/4 < (u.ts i).1 := by
    by_contra! h; apply hh; unfold val
    simp only [suppT,Bool.false_eq_true,ite_false,Trio.eval]
    rw [rising_bot (by linarith) h]; ring
  have e2 : u.rk S K < t/100 := by
    by_contra! h; apply hh; unfold val
    simp only [suppT,Bool.false_eq_true,ite_false,Trio.eval]
    rw [rising_top (by linarith) h]; ring
  obtain ⟨h1,h2⟩:=abs_le.1 (hg.1 i hi)
  obtain ⟨h3,h4⟩:=abs_le.1 hg.2
  exact mem_filter.mpr ⟨hi,by linarith,by linarith⟩

lemma missing_baseline {t} {g u S K} (hg : acc g u S K t) (he:0<t) (b) {i}
     (hh : (u.ts i).1=u.base) : i∉expose t g b S := by
  intro h
  obtain ⟨p,q⟩:=has_room hg he h
  have hA : u.base≤u.rk S K:=le_max_right ..
  cases b <;> simp at p q <;> linarith

end Blob
end
end ExactDerandomization.At

end

section

namespace ExactDerandomization.At
noncomputable section
open Analysis Hie Finset

/-- choose incoming cap after pilot column thresholds. Use ranking with same
convention (zero-based; cap at c, c+1st score gate). -/
def clim (p : Const) := (1+32*(128 + 4*(p.J+1)))*128
lemma clim_bound (p : Const) : (1+32*limitJ p.J)*128 ≤ (clim p+1:ℝ) := by
  unfold limitJ clim; push_cast; linarith

structure Grid where
  p : Const
  z : ℝ
  src : Domain
  dst : Domain
  narrow : Domain
  sp : Bool

def shutoff (x : ℝ) := 1-rising (1/4) (1/2) x
lemma shutoff_mem (x) : in01 (shutoff x) := by
  obtain ⟨h,e⟩:=rising_mem (1/4) (1/2) x
  unfold shutoff in01; constructor <;> linarith
lemma shutoff_full {x} (h:x≤1/4) : shutoff x=1 := by
  unfold shutoff; rw [rising_bot (by norm_num) h]; norm_num
lemma shutoff_zero {x} (h:1/2≤x) : shutoff x=0 := by
  unfold shutoff; rw [rising_top (by norm_num) h]; norm_num

namespace Grid

variable (t : Grid) (g : ℕ → Blob)

def pre (h : Trio) (mask : Bool) (x y : ℕ) :=
   if x∈ t.src ∧ y∈ t.dst ∧ (mask=false ∨ y∈ t.narrow) then
      (g x).val t.dst t.p.K h y
   else 0
def witness (b) := t.pre g (suppT t.z b) false
def rankin (y) := rank t.src (fun x=> t.witness g false x y) (clim t.p)
def incG (y) := if t.sp then shutoff (t.rankin g y) else 1
def result (f : Trio) (b) (col : ℕ → ℝ) (x y) :=
    t.pre g f b x y*t.incG g y*col y

def present (f : ℕ→Blob.Guess) (b : Bool) (x) :=
    if x∈t.src then Blob.expose t.z (f x) b t.dst else ∅
def inc (f : ℕ→Blob.Guess) (y) :=
    t.src.filter fun x=>y∈t.present f false x
def paired (f : ℕ→Blob.Guess) (x) :=
    if t.sp then (t.present f false x).filter fun y=> (t.inc f y).card ≤ clim t.p
     else t.present f false x
def Agree (f : ℕ→Blob.Guess) : Prop :=
    ∀ x∈t.src, Blob.acc (f x) (g x) t.dst t.p.K t.z

lemma incG_bounds (y) : in01 (t.incG g y) := by
  unfold incG; split
  · apply shutoff_mem
  · unfold in01; norm_num

lemma pres_range {h x y b} (e : y∈t.present h b x) : x∈t.src ∧ y∈t.dst := by
  unfold present at e; split at e
  · refine ⟨by assumption, (Blob.expose_subset _ _ _ _) e⟩
  · simp at e

lemma pres_card {f} (he:0<t.z) (h:t.Agree g f) (x b) : (t.present f b x).card ≤ t.p.K := by
   unfold present; split
   · next e=>exact Blob.exposure_count (h x e) he b
   · simp

lemma protect {f} {x y b} (he:0<t.z) (h:t.Agree g f) (hg : y∈t.present f b x) :
   t.witness g b x y=1 := by
  obtain ⟨hs,hk⟩:= t.pres_range hg
  simp only [present,hs,ite_true] at hg
  simp only [witness,pre,hk,hs,true_or,true_and,ite_true]
  exact Blob.protects (h x hs) he hg

lemma has_main {f} (he : 0<t.z) (h:t.Agree g f)
    {mask v : Bool} {w : ℝ → ℝ} (hw:∀ x ≤ t.z/2,w x=0)
    {x y} (hi : t.pre g (mainT t.z w v) mask x y ≠ 0) :
    y ∈ t.present f false x := by
  unfold pre at hi; split at hi
  · next e=>
    obtain ⟨e,s,-⟩:=e; unfold present; rw [ite_eq_left e]
    exact Blob.exposed_main (h x e) he s v hw hi
  · exact (hi rfl).elim

lemma has_witness {f x y} (he : 0<t.z) (h:t.Agree g f) (hi:t.witness g false x y≠0) :
    y∈ t.present f true x := by
  unfold witness pre at hi; split at hi
  · next e=>
    obtain ⟨e,s,-⟩:=e; unfold present; rw [ite_eq_left e]
    exact Blob.exposed_supp (h x e) he s hi
  · exact (hi rfl).elim

lemma paired_sub (f x) : t.paired f x ⊆ t.present f false x := by
  unfold paired; split
  · apply filter_subset
  · rfl

lemma degree {f x} (he:0<t.z) (h:t.Agree g f) : (t.paired f x).card ≤ t.p.K :=
   le_trans (card_le_card (t.paired_sub f x)) (pres_card t g he h ..)

lemma degree_in (f) (w) (h : t.sp=true) (S : Domain) :
   (S.filter fun x=> w∈t.paired f x).card≤clim t.p := by
  by_cases he:(t.inc f w).card ≤ clim t.p
  · apply le_trans (card_le_card ?_) he
    intro i hi
    have e := t.paired_sub f i (mem_filter.1 hi).2
    exact mem_filter.2 ⟨(t.pres_range e).1,e⟩
  have hh : S.filter (fun x=> w∈t.paired f x)= ∅ := by
    ext i; simp [paired,h,he]
  simp [hh]

lemma nonzero_present {f w x y v b col} (he:0<t.z) (h:t.Agree g f)
    (hw:∀ x ≤ t.z/2,w x=0)
    (hz:t.result g (mainT t.z w v) b col x y ≠ 0) :
    y∈ t.paired f x := by
  unfold result at hz
  have hi : y ∈ t.present f false x:= has_main t g he h hw (by intro e; apply hz; rw [e]; ring)
  unfold paired; split
  · next s=>
    apply mem_filter.mpr ⟨hi,?_⟩
    by_contra! hn
    have hh : 1 ≤ t.rankin g y := by
      apply (rank_ge (by norm_num)).mpr (lt_of_lt_of_le hn (card_le_card ?_))
      intro i hh
      obtain ⟨e,w⟩:=mem_filter.1 hh
      exact mem_filter.2 ⟨e,le_of_eq (Eq.symm (t.protect g he h w))⟩
    apply hz
    rw [incG,ite_eq_left s,shutoff_zero (by linarith : 1/2≤ t.rankin g y)]
    ring
  · exact hi

lemma pre_support {C f b} (_:TS t.z C f) (_ : 0<t.z) (x y)
    (hh:t.pre g f b x y≠0) : x∈t.src ∧ y∈t.dst := by
  unfold pre at hh; split at hh
  · next e=> exact ⟨e.1,e.2.1⟩
  exact (hh rfl).elim
lemma pre_count {C f b} (h:TS t.z C f) (he : 0<t.z) (x) (A : Domain) :
    (A.filter fun i=> t.pre g f b x i≠0).card≤t.p.K := by
  refine le_trans (card_le_card ?_) (Blob.support_size h he (g x) t.dst t.p.K)
  intro i hi; have hk:= (mem_filter.1 hi).2
  unfold pre at hk; split at hk
  · next e=> exact mem_filter.2 ⟨e.2.1,hk⟩
  exact (hk rfl).elim

end Grid
end
end ExactDerandomization.At

end

section

namespace ExactDerandomization.At
noncomputable section
open Analysis Hie Finset

structure Ask where
    p : Const
    S : Domain
    G : Mat
    u : ℕ
    a : ℕ
    t : ℕ
    z : ℝ
    sp : Bool

namespace Ask
variable (q : Ask)
variable {n : ℕ} [Fact n.Prime]

def hand (s t : Channel n) : Grid :=
   ⟨q.p,q.z,retain q.u q.S s,retain q.a q.S t,retain q.t q.S t,q.sp⟩
def d (x y) := q.G x y / rate q.a
def raw (x : ℕ) (s : Vec) : Blob :=
   ⟨0,fun y=>(q.d x y,s y)⟩
def botRow (x) := q.raw x fun _=>0
def bath (s t : Channel n) (x y) :=
    (q.hand s t).result q.botRow (prepT q.z) false (fun _=>1) x y

/-- two independent retentions at rates u and t -/
def two (x y : ℕ) (f : Channel n → Channel n → ℝ) :=
   atP q.u (x:ZMod n) (fun s=> atP q.t (y:ZMod n) (f s))

def tooth (q) (n : ℕ) [Fact n.Prime] (x y) :=
   two (n:=n) q x y (fun s t=> bath q s t x y)

def rawplus (s : Channel n) (x) :=
   q.raw x fun y=> if y∈ retain q.t q.S s then zeta* q.tooth n x y else 0

def atomTrue (f : ℝ → ℝ) (col : Vec) (s t : Channel n) (x y) :=
    (q.hand s t).result (q.rawplus t) (mainT q.z f true) true col x y

lemma hth (x) (s) (t : Channel n) :
    gate q.z ((q.raw x s).rk (retain q.a q.S t) q.p.K)= throttle q.S q.G q.a q.p.K x t q.z := by
    rw [Blob.rk,max_eq_left]; rfl; exact rank_nn _ _ _

lemma gate1 (s t : Channel n) (y) :
    (q.hand s t).incG (q.rawplus t) y=(q.hand s t).incG q.botRow y := by
  have hs x : (q.hand s t).witness (q.rawplus t) false x y=
          (q.hand s t).witness q.botRow false x y := by
     unfold Grid.witness Grid.pre; split
     · simp [Trio.eval, Blob.val,suppT,rawplus,raw,botRow,Blob.rk]
     · rfl
  unfold Grid.incG Grid.rankin; simp_rw [hs]

lemma base_bath (s t : Channel n) (x y) (h:x∈(q.hand s t).src) (e:y∈(q.hand s t).dst) :
    q.bath s t x y=prep q.z (q.d x y)*throttle q.S q.G q.a q.p.K x t q.z *
                       (q.hand s t).incG q.botRow y := by
    simp only [bath,Grid.result,Grid.pre,h,e,true_or,true_and,ite_true,mul_one,
      Blob.val,Trio.eval,prepT, mainT,Bool.false_eq_true,ite_false]
    dsimp only [hand,botRow]
    rw [q.hth]; rfl

lemma bath_mem (s t : Channel n) (x y : ℕ) :
    in01 (q.bath s t x y) := by
  by_cases h : x∈(q.hand s t).src ∧ y∈(q.hand s t).dst
  · rw [q.base_bath s t x y h.1 h.2]
    have H (x y) (h:in01 x) (e:in01 y) : in01 (x*y) :=
       ⟨mul_nonneg h.1 e.1,(mul_le_mul h.2 e.2 e.1 zero_le_one).trans_eq (one_mul _)⟩
    exact H _ _ (H _ _ (rising_mem ..) (gate_mem ..)) ((q.hand s t).incG_bounds ..)
  · have e : q.bath s t x y=0 := by unfold bath Grid.result Grid.pre; split <;> grind
    rw [e]; unfold in01; norm_num

lemma tooth_mem (x y) : in01 (q.tooth n x y) :=
    expect_mem fun _=>expect_mem fun _=>q.bath_mem ..

lemma two_mono {x y : ℕ} {f g : Channel n → Channel n→ℝ}
    (h:∀ s t, hit q.u (x:ZMod n) s → hit q.t (y:ZMod n) t → f s t ≤ g s t) :
    q.two x y f≤q.two x y g :=
     av_mono fun _=>av_mono fun _=>h _ _ (hit_open ..) (hit_open ..)

lemma two_rw {x y : ℕ} {f g : Channel n→Channel n→ℝ}
    (h:∀ s t, hit q.u (x:ZMod n) s → hit q.t (y:ZMod n) t → f s t = g s t) :
    q.two x y f=q.two x y g :=
  le_antisymm (q.two_mono fun s t he hi=>le_of_eq (h s t he hi))
              (q.two_mono fun s t he hi=>le_of_eq (Eq.symm (h s t he hi)))

lemma valid_broad (s t : Channel n) (x y) (ht : q.a≤q.t)
    (hx:x∈q.S) (hy:y∈q.S)
    (h : hit q.u (x:ZMod n) s) (e : hit q.t (y:ZMod n) t) :
    x∈(q.hand s t).src ∧ y∈(q.hand s t).dst ∧ y∈(q.hand s t).narrow :=
    ⟨mem_filter.2 ⟨hx,h⟩,mem_filter.2 ⟨hy,contained q.t q.a ht e⟩,
      mem_filter.2 ⟨hy,e⟩⟩

lemma premask (s t : Channel n) (x y) (f : ℝ→ℝ) (col : Vec)
    (h : x∈(q.hand s t).src) (e : y∈(q.hand s t).dst) (ht : y∈(q.hand s t).narrow) :
    q.atomTrue f col s t x y = f (q.d x y)*throttle q.S q.G q.a q.p.K x t q.z *
       divisor (zeta*q.tooth n x y)*(q.hand s t).incG q.botRow y*col y := by
    simp only [atomTrue,Grid.result,q.gate1,Grid.pre,h,e,ht,or_true,true_and,ite_true,
        Blob.val, Trio.eval,mainT]
    rw [show (q.rawplus t x).ts y=(q.d x y,zeta*q.tooth n x y) from (by
       simp [rawplus,raw,show y∈retain q.t q.S t from ht])]
    have he := q.hth x (fun y=>if y∈retain q.t q.S t then zeta*q.tooth n x y else 0) t
    change gate _ ((q.rawplus t x).rk _ _) = _ at he
    dsimp only [hand]; rw [he]

lemma tooth0 {x y} (hz:0<q.z) (h : q.d x y ≤ q.z/2) : q.tooth n x y=0 := by
  have e s t : q.bath (n:=n) s t x y=0 := by
    have e' : prep q.z (q.d x y)=0:=rising_bot (by linarith) h
    unfold bath Grid.result Grid.pre; split
    · simp only [prepT,mainT,Blob.val,Trio.eval,botRow,raw,e']; ring
    · ring
  simp [tooth,two,atP,e,av_zero]

structure Valid (q : Ask) (col : Vec) (n : ℕ) [Fact n.Prime] : Prop where
   adm : legal n q.S
   lo : delta≤ q.z
   src : 2^q.u≤n
   tok : q.a≤q.t
   entry : 2^q.a≤n
   nonneg : ∀ i j,0≤ q.G i j
   row : ∀ x, wt q.S q.G x ≤ q.p.T+1
   sparse : q.sp=true → q.z=A ∧ q.a≤q.u ∧ ∀ y∈q.S,col y≠0 →
      (rowhi q.S q.G q.a y).card*(rate q.a) ≤ limitJ q.p.J

lemma row_fail {col} (h : Valid q col n) {x y : ℕ} (hy:y∈q.S) :
    atP q.t (↑y:ZMod n) (cost q.S q.G q.a q.p.K x q.z) ≤ 1/128 := by
  have ht := q.p.KOK
  have he:=h.lo
  apply gate_bound (lt_of_lt_of_le dp h.lo) h.entry h.nonneg h.row h.adm (mem_range.1 (h.adm hy))
  refine le_trans ?_ ht
  have h1 : 0< eta q.z := by have := dp; unfold eta; linarith
  have h2 : 0<eta delta:=by norm_num [eta,A,delta]
  gcongr; unfold eta; apply div_le_div_of_nonneg_right he; norm_num

def lbad (s t : Channel n) (y : ℕ) : ℝ :=
    if (q.hand s t).incG q.botRow y=1 then 0 else 1

lemma col_fail {col} (h : Valid q col n) {x y : ℕ} (hx:x∈q.S) (hy:y∈q.S)
    (e : col y ≠ 0) (t : Channel n) :
    atP q.u (↑x:ZMod n) (fun s=>q.lbad s t y) ≤ 1/128 := by
   by_cases he:q.sp=true
   · obtain ⟨h1,h2,H⟩:=h.sparse he
     let W:=rowhi q.S q.G q.a y
     have hm : (W.card:ℝ)*rate q.a ≤ limitJ q.p.J := H y hy e
     have hs (s) :
        (clim q.p+1:ℝ)*q.lbad s t y ≤ tally q.u W s := by
        unfold lbad; split
        · rw [mul_zero]; unfold tally; positivity
        · next hbad=>
           rw [mul_one]
           let g:=q.hand s t
           let f i:=g.witness q.botRow false i y
           have hn : 1/4 < rank g.src f (clim q.p) := by
              by_contra! hc
              apply hbad
              simp only [Grid.incG,hand,he,ite_true]
              exact shutoff_full hc
           have hk := (rank_gt (by norm_num)).1 hn
           have hw : (g.src.filter fun i=> 1/4 < f i) ⊆ retain q.u W s := by
              intro i hi; obtain ⟨hi,hv⟩:=mem_filter.1 hi
              obtain ⟨hi',hi''⟩:=mem_filter.1 (show i ∈ retain q.u q.S s from hi)
              refine mem_filter.2 ⟨mem_filter.2 ⟨hi',?_⟩,hi''⟩
              by_contra! hle
              have hz : q.d i y < 2*delta := (div_lt_iff₀ (rate_pos q.a)).2 hle
              refine ne_of_gt (lt_trans (show 0<(1/4:ℝ) by norm_num) hv) ?_
              unfold f Grid.witness Grid.pre; split
              · simp only [Blob.val,botRow,raw,Trio.eval,suppT,g,hand,h1,Bool.false_eq_true,
                   ite_false]
                rw [rising_bot (by norm_num [A]) (show q.d i y≤A/4 from by
                    unfold delta A at *; linarith)]
                ring
              · rfl
           have hu : clim q.p<(retain q.u W s).card := lt_of_lt_of_le hk (card_le_card hw)
           unfold tally
           exact_mod_cast hu
     have hp := tally_cond (S:=W) (fun i hi=>h.adm (mem_filter.1 hi).1) h.src
                     (j:=q.u) x (mem_range.1 (h.adm hx))
     have hu :
        (clim q.p+1:ℝ)*atP q.u (↑x:ZMod n) (fun s=>q.lbad s t y) ≤
          atP q.u (↑x:ZMod n) (tally q.u W) := by
        unfold atP; rw [← av_cmul]; exact av_mono (fun _=> hs _)
     have ha : rate q.u ≤ rate q.a := by unfold rate; gcongr; norm_num
     have H := clim_bound q.p
     have hq : 1+W.card*(32:ℝ)*rate q.u≤1+32*limitJ q.p.J := by
        nlinarith [mul_le_mul_of_nonneg_left ha (show 0≤(W.card:ℝ) by positivity)]
     apply le_of_mul_le_mul_left _ (show 0 < (clim q.p+1:ℝ) by positivity)
     linarith
   · simp [atP,lbad,hand,Grid.incG,he,av_zero]

set_option maxHeartbeats 1000000 in
lemma normalized_mean {col} (h : Valid q col n) {x y : ℕ} (hx:x∈q.S) (hy:y∈q.S)
    {f : ℝ→ℝ} (hf : ∀ x ≤ q.z,f x=0) :
    q.two x y (n:=n) (fun s t=> q.atomTrue f col s t x y) = f (q.d x y)*col y := by
   let b (s t : Channel n) := throttle q.S q.G q.a q.p.K x t q.z*(q.hand s t).incG q.botRow y
   let w := q.tooth n x y
   let p:=q.two x y b
   have ht : q.two x y (n:=n) (fun s t=> q.atomTrue f col s t x y)
        = p*(f (q.d x y)*col y*divisor (zeta*w)) := by
     unfold p two atP; rw [← av_mulc]
     simp_rw [← av_mulc]
     apply congrArg av; ext s; apply congrArg av; ext t
     let i := openP q.u (↑x:ZMod n) s
     let j := openP q.t (↑y:ZMod n) t
     obtain ⟨a,a',a''⟩:= q.valid_broad i j x y h.tok hx hy (hit_open ..) (hit_open ..)
     change q.atomTrue f col i j x y=b i j*_
     rw [q.premask i j x y f col a a' a'']
     unfold b w; ring
   rw [ht]
   by_cases hg:f (q.d x y)=0
   · rw [hg]; ring
   by_cases he:col y=0
   · rw [he]; ring
   have hh:w=p := by
     have he' : prep q.z (q.d x y)=1 := by
       have H := lt_of_not_ge (show ¬ q.d x y ≤ q.z from fun h=>hg (hf _ h))
       have e:=lt_of_lt_of_le dp h.lo
       exact rising_top (by linarith) (by linarith)
     apply two_rw
     intro s t hk ht
     obtain ⟨a,a',-⟩:= q.valid_broad s t x y h.tok hx hy hk ht
     rw [q.base_bath s t x y a a',he',one_mul]
   have hu : 1/2 ≤ p := by
     let v (t : Channel n) := cost q.S q.G q.a q.p.K x q.z t
     have hm s t : 1-v t-q.lbad s t y ≤ b s t := by
       obtain ⟨a1,a2⟩:= (q.hand s t).incG_bounds q.botRow y
       let w:=throttle q.S q.G q.a q.p.K x t q.z
       obtain ⟨a3,a4⟩:= (show in01 w from gate_mem ..)
       have hw : 0≤b s t:=mul_nonneg a3 a1
       unfold lbad v cost
       split <;> split <;> simp_all [b] ; linarith
     let u:=q.two x y (fun s t=>1-v t-q.lbad s t y)
     have hz:u≤p:=q.two_mono fun s t _ _=>hm s t
     have hrv:= q.row_fail h (x:=x) hy
     have hcv (t) := q.col_fail h hx hy he t
     have hh : 1/2≤u := by
        unfold u two atP
        rw [av_swap]
        simp only [av_sub,av_const]
        have hl :
            av (fun t:pc n q.t=> atP q.u (↑x:ZMod n)
                 (fun s=>q.lbad s (openP q.t (↑y:ZMod n) t) y)) ≤ 1/128 := by
           refine le_trans (b:=av (fun _ :pc n q.t=>1/128)) (av_mono fun i=>hcv _) ?_
           rw [av_const]
        dsimp only [atP] at hl hrv; unfold v
        linarith
     linarith
   have hz:= q.tooth_mem (n:=n) x y |>.2
   change w≤1 at hz
   have hw : den (zeta*w)=p := by
      have h1:= mul_le_mul_of_nonneg_left hu (le_of_lt zp)
      have h2:= mul_le_mul_of_nonneg_left hz (le_of_lt zp)
      unfold den clip
      rw [max_eq_right (by rw [hh]; linarith),min_eq_right (by linarith),hh]
      field_simp [ne_of_gt zp]
   rw [divisor,hw]
   field_simp [ne_of_gt (show 0<p by linarith)]

end Ask
end
end ExactDerandomization.At

end

end OAI
