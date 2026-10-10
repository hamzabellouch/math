import Mathlib

namespace OAI

/-!
Finite averages, affine spectral gaps, and fourth-moment sampling estimates.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-!
Scalar cutoffs. Piecewise using only arithmetic and min/max. We
use fourth moments (instead of eighth), hence fourth-root flatness.
-/
namespace ExactDerandomization.Analysis
noncomputable section

def fourth (x : ℝ) := Real.sqrt (Real.sqrt x)
def Ic (c : ℝ) (f : ℝ→ℝ) :=
    ∀ x y : ℝ, x ≤ y → f x≤f y ∧ f y - f x≤c*(y-x)
def Lip (c : ℝ) (f : ℝ→ℝ) := ∀ x y, |f y-f x|≤c*|y-x|
def smooth (x : ℝ) := min 1 (max 0 x)
def in01 (x : ℝ) := 0≤x ∧ x≤1

lemma fourth_nn (x) : 0≤ fourth x := Real.sqrt_nonneg _
lemma fourth_four {x : ℝ} (h : 0≤x) : fourth x^4=x := by
  rw [fourth,show 4=2*2 from rfl,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt h]
lemma four_fourth {x : ℝ} (h : 0≤x) : fourth (x^4)=x := by
  unfold fourth; rw [show 4=2*2 from rfl,pow_mul,Real.sqrt_sq (sq_nonneg _),Real.sqrt_sq h]

lemma Ic.lip {c f} (h : Ic c f) : Lip c f := by
 intro x y; rcases le_total x y with h1|h1
 · obtain ⟨e,g⟩ := h x y h1
   rwa [abs_of_nonneg (sub_nonneg.mpr e),abs_of_nonneg (sub_nonneg.mpr h1)]
 obtain ⟨e,g⟩ := h y x h1
 rw [abs_of_nonpos (sub_nonpos.mpr e),abs_of_nonpos (sub_nonpos.mpr h1)]
 linarith

lemma unit_mem (x) : in01 (smooth x) := by unfold in01 smooth; grind

lemma unit_ic : Ic 1 smooth := by intro x y h; unfold smooth; grind

lemma exp4inc {x y : ℝ} (hx : in01 x) (hy : in01 y) (h : x≤y) :
    x^4 ≤ y^4 ∧ y^4-x^4≤4*(y-x) := by
  have hv : y-x≥0 := by linarith
  refine ⟨pow_le_pow_left₀ hx.1 h _,?_⟩
  have H : y^3+y^2*x+y*x^2+x^3≤4 := calc
    _ ≤ (1:ℝ)^3+1^2*1+1*1^2+1^3 := by obtain ⟨_,_⟩:=hx; obtain ⟨_,_⟩:=hy; gcongr
    _ = _ := by norm_num
  nlinarith [mul_le_mul_of_nonneg_right H hv]

lemma icUnitFour : Ic 4 (fun x=>smooth x^4) := by
  intro x y h
  obtain ⟨e,t⟩ := unit_ic x y h
  obtain ⟨s,r⟩ := exp4inc (unit_mem x) (unit_mem y) e
  exact ⟨s,by dsimp; linarith⟩

def fade (x : ℝ) := (smooth (2*x)^4 + (1-smooth (2*(1-x))^4))/2
lemma fade_low {x : ℝ} (h : x≤1/2) : fade x=(smooth (2*x)^4)/2 := by
  have hg : 1≤2*(1-x) := by linarith
  have ht : smooth (2*(1-x))=1 := by unfold smooth; grind
  unfold fade; rw [ht]; ring
lemma fade_symm (x : ℝ) : fade (1-x) = 1-fade x := by
  simp only [fade,sub_sub_cancel]
  ring

lemma fade_ic : Ic 8 fade := by
  intro x y e
  obtain ⟨h1,h2⟩ := icUnitFour (2*x) (2*y) (by linarith)
  obtain ⟨h3,h4⟩ := icUnitFour (2*(1-y)) (2*(1-x)) (by linarith)
  dsimp at *; unfold fade; constructor <;> linarith
lemma fade_bot {x : ℝ} (h : x≤0) : fade x=0 := by
  rw [fade_low (by linarith)]
  have e : 2*x≤0 := by linarith
  simp [smooth,e]
lemma fade_top {x : ℝ} (h : 1≤x) : fade x=1 := by
  have := fade_symm x
  rw [fade_bot (by linarith)] at this; linarith
lemma fade_mem (x) : in01 (fade x) := by
  rcases le_total x 0 with h|h
  · simp [fade_bot h,in01]
  rcases le_total 1 x with e|e
  · simp [fade_top e,in01]
  constructor
  · simpa only [fade_bot (le_refl _)] using (fade_ic 0 x h).1
  · simpa only [fade_top (le_refl _)] using (fade_ic x 1 e).1

def rising (a b x : ℝ) := fade ((x-a)/(b-a))
lemma rising_ic {a b : ℝ} (h:a<b) : Ic (8/(b-a)) (rising a b) := by
  have ht : 0<b-a := sub_pos.mpr h
  intro x y he
  obtain ⟨eh,eg⟩ := fade_ic ((x-a)/(b-a)) ((y-a)/(b-a)) (by gcongr)
  refine ⟨eh,?_⟩
  unfold rising
  convert eg using 1; ring
lemma rising_bot {a b x : ℝ} (h:a<b) (e:x≤a) : rising a b x=0 :=
  fade_bot (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 e) (sub_nonneg.2 (le_of_lt h)))
lemma rising_top {a b x : ℝ} (h:a<b) (e:b≤x) : rising a b x=1 :=
  fade_top (by apply (le_div_iff₀ (sub_pos.2 h)).mpr; linarith)
lemma rising_mem (a b x) : in01 (rising a b x) := fade_mem _

/-- simpler shoulder for the hierarchy threshold; gap W. -/
def shoulder (A W x : ℝ) :=
    W*smooth ((x-A)/W)^4+max 0 (x-A-W)
lemma shoulder_ic (A W : ℝ) (e : 0<W) : Ic 5 (shoulder A W) := by
  intro x y he
  obtain ⟨h,h'⟩ := icUnitFour ((x-A)/W) ((y-A)/W) (by gcongr)
  dsimp at h h'
  have hu := mul_le_mul_of_nonneg_left h (le_of_lt e)
  have hv : W * (smooth ((y-A)/W)^4-smooth ((x-A)/W)^4) ≤ 4*(y-x) := by
    calc _ ≤ W*(4*((y-A)/W - (x-A)/W)) := mul_le_mul_of_nonneg_left h' (le_of_lt e)
         _ = _ := by field_simp; ring
  unfold shoulder
  constructor
  · exact add_le_add hu (max_le_max_left _ (by linarith))
  · rcases le_total 0 (x-A-W) with hg|hg <;> rcases le_total 0 (y-A-W) with hs|hs <;>
      simp [hg,hs] <;> linarith

lemma shoulder_bot {A W x} (h:0<W) (he:x≤A) : shoulder A W x=0 := by
  have ht : (x-A)/W≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [shoulder,smooth,ht,show x-A-W≤0 from by linarith]

lemma shoulder_spec (A W x) (h:0<W) :
    max 0 (x-A-W) ≤ shoulder A W x ∧ shoulder A W x ≤ max 0 (x-A) := by
  constructor
  · unfold shoulder; exact le_add_of_nonneg_left (by positivity)
  rcases le_total x A with ht|ht
  · rw [shoulder_bot h ht]
    exact le_max_left _ _
  unfold shoulder
  rw [max_eq_right (show 0≤ x-A from by linarith)]
  rcases le_total W (x-A) with he|he
  · rw [max_eq_right (show 0≤x-A-W from by linarith)]
    have hs : 1≤ (x-A)/W := by rw [le_div_iff₀ h]; linarith
    unfold smooth; rw [max_eq_right (by linarith), min_eq_left hs]; linarith
  · have hs : in01 ((x-A)/W) := ⟨by apply div_nonneg <;> linarith, by rw [div_le_iff₀ h]; linarith⟩
    rw [smooth,max_eq_right hs.1,min_eq_right hs.2,max_eq_left (show x-A-W≤0 from by linarith),add_zero]
    have H := pow_le_pow_of_le_one hs.1 hs.2 (show 1≤ (4:ℕ) by omega)
    calc _ ≤ W*((x-A)/W)^1 := mul_le_mul_of_nonneg_left H (le_of_lt h)
         _ = _ := by field_simp

lemma fourth_mono : Monotone fourth := fun _ _ h=>Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h)
lemma fourth_pos {x : ℝ} (h : 0<x) : 0<fourth x := Real.sqrt_pos.2 (Real.sqrt_pos.2 h)

lemma fourth_mul {x y : ℝ} (h : 0≤x) : fourth (x*y)=fourth x*fourth y := by
  simp only [fourth, Real.sqrt_mul h,Real.sqrt_mul (Real.sqrt_nonneg x)]

/-- For increasing cutoffs it suffices to explicitly bound the root in
the part close to the zero threshold. -/
lemma join_inc {t a b : ℝ} {f : ℝ → ℝ} (ha : 0≤a) (hb : 0≤b)
    (l : ∀ x y, x≤y → y≤t → f x ≤ f y ∧ f y-f x≤a*(y-x))
    (r : ∀ x y, x≤y → t≤x → f x ≤ f y ∧ f y-f x≤b*(y-x)) :
    Ic (a+b) f := by
  intro x y he
  rcases le_total y t with h|h
  · obtain ⟨hs,ht⟩ := l x y he h
    exact ⟨hs,by nlinarith⟩
  rcases le_total t x with e|e
  · obtain ⟨hs,ht⟩ := r x y he e
    exact ⟨hs,by nlinarith⟩
  obtain ⟨h1,h2⟩ := l x t e le_rfl
  obtain ⟨h3,h4⟩ := r t y h le_rfl
  exact ⟨le_trans h1 h3,by nlinarith⟩

lemma rise_root {c t a : ℝ} {f : ℝ→ℝ} (h : Ic c f) (hp : 0<f t)
    (ha : 0≤a) (hc : 0<c)
    (hl : ∀ x y, x≤y → y≤t → fourth (f x)≤fourth (f y) ∧
                        fourth (f y)-fourth (f x)≤a*(y-x)) :
    ∃ c' : ℝ, 0<c' ∧ Ic c' (fun x=>fourth (f x)) := by
  let v:=fourth (f t)
  have hv : 0<v := fourth_pos hp
  let b:=c/v^3
  have h0 : 0<b := by unfold b; positivity
  refine ⟨a+b,by linarith,join_inc ha (le_of_lt h0) hl (fun x y he hg=>?_)⟩
  obtain ⟨h1,h2⟩ := h x y he
  have hx: f t≤f x := (h t x hg).1
  let u:= fourth (f x)
  let z:= fourth (f y)
  have hu : v ≤ u := fourth_mono hx
  have hz : u ≤ z := fourth_mono h1
  have hs : v^3 ≤ z^3+z^2*u+z*u^2+u^3 := by
    have e := pow_le_pow_left₀ (le_of_lt hv) hu 3
    have hh : 0<u := lt_of_lt_of_le hv hu
    have he : 0<z := lt_of_lt_of_le hh hz
    exact le_trans e (le_add_of_nonneg_left (by positivity))
  have e1 : u^4=f x := fourth_four (by linarith)
  have e2 : z^4=f y := fourth_four (by linarith)
  refine ⟨hz,?_⟩
  change z-u ≤ c/v^3*(y-x)
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hs (show 0≤z-u by linarith)]

lemma fade_root : ∃ c : ℝ, 0<c ∧ Ic c (fun x=>fourth (fade x)) := by
  let u := fourth (1/2)
  have hu : 0<u := fourth_pos (by norm_num)
  have ht : 0< fade (1/2) := by unfold fade smooth; norm_num
  refine rise_root fade_ic ht (a:=u*2) (by positivity) (by norm_num) ?_
  intro x y he ht
  have hl (x) (h : x≤1/2) : fourth (fade x)=u*smooth (2*x) := by
    rw [fade_low h,show smooth (2*x)^4/2=1/2*smooth (2*x)^4 by ring,
        fourth_mul (by norm_num),four_fourth (unit_mem _).1]
  rw [hl x (le_trans he ht),hl y ht]; obtain ⟨h1,h2⟩ := unit_ic (2*x) (2*y) (by linarith)
  constructor <;> nlinarith

lemma rising_root {a b : ℝ} (h : a<b) :
    ∃ c:ℝ, 0<c ∧ Lip c (fun x=>fourth (rising a b x)) ∧
                         Lip c (fun x=>fourth (1-rising a b x)) := by
  obtain ⟨c,hc,e⟩ := fade_root
  have ek := e.lip
  let u (x : ℝ) := (x-a)/(b-a)
  have he (x y) : c*|u y-u x|=c/(b-a)*|y-x| := by
    rw [show u y-u x=(y-x)/(b-a) by unfold u; ring, abs_div, abs_of_pos (sub_pos.2 h)]
    ring
  refine ⟨c/(b-a),div_pos hc (sub_pos.2 h),fun x y=>?_,fun x y=>?_⟩
  · rw [← he]; exact ek (u x) (u y)
  · change |fourth (1-fade (u y))-fourth (1-fade (u x))|≤_
    rw [← fade_symm,←fade_symm,← he]
    have ht := ek (1-u x) (1-u y)
    rwa [show 1-u y-(1-u x)=-(u y-u x) by ring,abs_neg] at ht

lemma shoulder_root (A W) (e : 0<W) :
    ∃ c:ℝ,0<c ∧ Ic c (fun x=>fourth (shoulder A W x)) := by
  have H : 0< shoulder A W (A+W) := by
    have he : A+W-A=W := by ring
    unfold shoulder smooth; rw [he,div_self (ne_of_gt e)]
    simpa using e
  have hp := fourth_pos e
  refine rise_root (shoulder_ic A W e) H (a:=fourth W/W) (by positivity) (by norm_num) ?_
  intro x y hx hy
  have hl (x) (h : x≤A+W) :
       fourth (shoulder A W x)=fourth W*smooth ((x-A)/W) := by
    unfold shoulder
    rw [max_eq_left (show x-A-W≤0 by linarith),add_zero,
       fourth_mul (le_of_lt e),four_fourth (unit_mem _).1]
  rw [hl x (le_trans hx hy),hl y hy]
  obtain ⟨h1,h2⟩ := unit_ic ((x-A)/W) ((y-A)/W) (by gcongr)
  refine ⟨by nlinarith,?_⟩
  have ht := mul_le_mul_of_nonneg_left h2 (le_of_lt hp)
  calc _ ≤ _ := show fourth W*smooth ((y-A)/W)-fourth W*smooth ((x-A)/W) ≤
             fourth W*(1*((y-A)/W-(x-A)/W)) by rw [← mul_sub]; exact ht
       _ = _ := by ring

end
end ExactDerandomization.Analysis

end

section

/-! Basic finite averages in the statistical analysis. -/
namespace ExactDerandomization
namespace Analysis
noncomputable section
open Finset

variable {α β : Type}

def avs (s : Finset α) (f : α → ℝ) : ℝ := (∑ i ∈ s, f i) / s.card
def av [Fintype α] (f : α → ℝ) : ℝ := avs univ f
variable [Fintype α] [Fintype β]

lemma av_cmul (x : ℝ) (f : α → ℝ) : av (fun i=> x*f i) = x*av f := by
  rw [av,av,avs,avs,← mul_sum]; ring
lemma av_mulc (x : ℝ) (f : α → ℝ) : av (fun i=> f i*x) = av f *x := by
  simpa only [mul_comm x] using av_cmul x f
lemma av_add (f g : α → ℝ) : av (fun i=>f i+g i)=av f+av g := by
  simp only [av,avs,sum_add_distrib,add_div]
lemma av_sub (f g : α → ℝ) : av (fun i=>f i-g i)=av f-av g := by
  simp only [av,avs,sum_sub_distrib,sub_div]
lemma av_div (f : α → ℝ) (x : ℝ) : av (fun i=> f i/x) = av f/x := by
  simp only [div_eq_mul_inv,av_mulc]

lemma av_mono {f g : α → ℝ} (h : f ≤ g) : av f ≤ av g :=
  div_le_div_of_nonneg_right (sum_le_sum fun i _=>h i) (Nat.cast_nonneg _)
lemma av_nonneg (f : α → ℝ) (h : ∀ i, 0≤f i) : 0 ≤ av f :=
  div_nonneg (sum_nonneg fun i _=>h i) (Nat.cast_nonneg _)

lemma av_swap (f : α → β → ℝ) : av (fun i=> av (f i))=av (fun j=> av (fun i=> f i j)) := by
  simp only [av,avs,← sum_div]
  rw [sum_comm]
  ring

lemma av_sum {γ : Type} (s : Finset γ) (f : γ → α → ℝ) :
    av (fun i=>∑ j∈s, f j i) = ∑ j∈s,av (f j) := by
  simp only [av,avs,← sum_div]
  rw [sum_comm]

lemma av_equiv (e : α ≃ β) (f : β → ℝ) : av (fun i=> f (e i)) = av f := by
  simp only [av,avs,card_univ,Fintype.card_congr e]
  rw [Fintype.sum_equiv e _ f fun i=>rfl]
lemma av_perm (e : Equiv.Perm α) (f : α → ℝ) : av (fun i=> f (e i))=av f :=
  av_equiv e f
lemma av_prod (f : α × β → ℝ) : av f = av (fun a=> av (fun b=> f (a,b))) := by
  simp only [av,avs,card_univ,Fintype.card_prod,Nat.cast_mul,← sum_div]
  rw [Fintype.sum_prod_type]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma av_const [Nonempty α] (c : ℝ) : av (fun _ : α=> c) = c := by
  simp [av,avs,Fintype.card_pos.ne']
lemma av_zero : av (fun _ : α=> (0:ℝ)) = 0 := by simp [av,avs]

lemma av_card [Nonempty α] (f : α → ℝ) :
    (Fintype.card α : ℝ)*av f = ∑ i,f i := by rw [mul_comm]; simp [av,avs,Fintype.card_pos.ne']

variable [Nonempty α]

lemma av_sq_le (f : α → ℝ) : av f ^2 ≤ av (fun i=>f i^2) := by
  let c := av f
  have h := av_nonneg (fun i=> f i^2 - (2*c*f i)+c^2) (fun i=>by nlinarith [sq_nonneg (f i-c)])
  rw [av_add, av_sub, av_const,av_cmul] at h
  dsimp [c] at h; nlinarith

lemma av_four_le (f : α → ℝ) : av f ^4 ≤ av (fun i=>f i^4) := by
  calc av f ^4 = (av f^2)^2 := by ring
       _ ≤ (av (fun i=>f i^2))^2 := pow_le_pow_left₀ (sq_nonneg _) (av_sq_le f) _
       _ ≤ av (fun i=>(f i^2)^2) := av_sq_le _
       _ = _ := by simp only [pow_succ, pow_zero]; ring_nf

/-- Variance around the finite average. -/
def var2 (f : α → ℝ) := av (fun i=>(f i-av f)^2)

lemma var2_sum (f : α → ℝ) : var2 f = av (fun i=> f i^2) - av f^2 := by
  unfold var2
  have he (i : α) : (f i-av f)^2=f i^2-(2*av f)*f i+(av f)^2 := by ring
  simp only [he,av_add,av_sub,av_const,av_cmul]
  ring

lemma var2_best (f : α → ℝ) (z : ℝ) : var2 f ≤ av (fun i=>(f i-z)^2) := by
  rw [var2_sum]
  have he (i : α) : (f i-z)^2=f i^2-2*z*f i+z^2 := by ring
  simp only [he,av_add,av_sub,av_cmul,av_const]
  nlinarith [sq_nonneg (av f-z)]

lemma var2_pair (f : α → ℝ) :
   av (fun i=> av (fun j=> (f i-f j)^2)) = 2*var2 f := by
  have h (i j : α) : (f i-f j)^2=f i^2-(2*f i)*f j+f j^2 := by ring
  simp only [h,av_add,av_sub,av_cmul,av_const,av_mulc,var2_sum]
  ring

lemma pair_four (f : α → ℝ) (h : av f=0) :
    av (fun i=> f i^4) ≤ av (fun i=> av (fun j=> (f i-f j)^4)) := by
  apply av_mono; intro i
  have he := av_four_le (fun j=>f i-f j)
  simpa only [av_sub,av_const,h,sub_zero] using he

end
end Analysis
end ExactDerandomization

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Finset Complex
open scoped ComplexConjugate

namespace Square

abbrev T (n : ℕ) := ZMod n × ZMod n
abbrev order (n : ℕ) [NeZero n] := Fintype.card (T n)
variable {n : ℕ} [NeZero n]

abbrev c (x : ZMod n) := ZMod.stdAddChar x

lemma cab (i : ZMod n) : ‖c i‖ = 1 := Circle.norm_coe _
lemma csq (i : ZMod n) : normSq (c i)=1 := by rw [← Complex.sq_norm,cab]; norm_num
lemma cconj (i : ZMod n) : conj (c i)=c (-i) := by
  have hi : c i * c (-i) = 1 := by rw [c,c,← AddChar.map_add_eq_mul]; simp
  have ht := mul_conj (c i)
  rw [csq, Complex.ofReal_one] at ht
  exact mul_left_cancel₀ (by intro h; simp [h] at hi) (ht.trans hi.symm)

def dot (x y : T n) : ZMod n := x.1*y.1+x.2*y.2
abbrev e (x y : T n) := c (dot x y)

lemma ortho (x : T n) : ∑ k : T n, e k x = if x=0 then (order n:ℂ) else 0 := by
  have h (a : ZMod n) : ∑ k, c (k*a) = if a=0 then (n:ℂ) else 0 := by
    simp only [c,AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar _)]
    split <;> simp_all
  have hi (a b : ZMod n) : e (a,b) x=c (a*x.1)*c (b*x.2) := AddChar.map_add_eq_mul _ _ _
  rw [Fintype.sum_prod_type]
  simp only [hi,← mul_sum,← sum_mul,h]
  rcases x with ⟨a,b⟩
  by_cases ha : a=0 <;> by_cases hb : b=0 <;> simp [ha,hb,T,order,Prod.ext_iff]

lemma cross (x y : T n) : ∑ k : T n, e k x * conj (e k y) =
    if x=y then (order n:ℂ) else 0 := by
  have hi (k : T n) : e k x * conj (e k y) = e k (x-y) := by
    simp only [e,cconj,c,← AddChar.map_add_eq_mul]
    congr 1
    unfold dot; simp only [Prod.fst_sub, Prod.snd_sub]; ring
  simp only [hi,ortho,sub_eq_zero]

def hat (f : T n → ℂ) (k : T n) := ∑ x, e k x*f x

lemma parse (f : T n → ℂ) :
    ∑ k, normSq (hat f k) = order n * ∑ x, normSq (f x) := by
  apply Complex.ofReal_injective
  simp only [ofReal_sum,ofReal_mul,ofReal_natCast,← mul_conj]
  have he (k) : hat f k*conj (hat f k) =
       ∑ x, ∑ y, (e k x * conj (e k y)) * (f x*conj (f y)) := by
    simp only [hat, map_sum,map_mul]; rw [sum_mul]; simp only [mul_sum]; congr! 2; ring
  simp only [he]
  rw [sum_comm]
  rw [mul_sum]
  apply sum_congr rfl; intro i _
  rw [sum_comm]; simp_rw [← sum_mul,cross]; simp

lemma hat_sub (f g : T n → ℂ) (k) :
    hat (fun i=> f i-g i) k = hat f k-hat g k := by simp [hat,mul_sub,sum_sub_distrib]

lemma hat_shift (f : T n → ℂ) (y k : T n) :
    hat (fun x=> f (x+y)) k = e k (-y) * hat f k := by
  have he (x : T n) : e k x = e k (-y)*e k (x+y) := by
    simp only [e,c,← AddChar.map_add_eq_mul]
    congr 1
    simp only [dot,Prod.fst_neg,Prod.snd_neg,Prod.fst_add,Prod.snd_add]; ring
  calc hat (fun x=> f (x+y)) k = ∑ x, e k (-y)*(e k (x+y)*f (x+y)) := by
         unfold hat; apply sum_congr rfl; intro x _
         rw [← mul_assoc,← he]
       _ = _ := by
         rw [← mul_sum]
         congr 1
         exact Fintype.sum_equiv (Equiv.addRight y) _ _ fun i=> rfl

def shear (b : Bool) (d : ZMod n) : T n → T n :=
  match b with
  | true => fun x => (x.1+d*x.2, x.2)
  | false => fun x=> (x.1,x.2+d*x.1)

omit [NeZero n] in
lemma shear_shear (b) (d : ZMod n) (x : T n) : shear b (-d) (shear b d x)=x := by
  cases b <;> simp [shear]

def shPerm (b : Bool) (d : ZMod n) : Equiv.Perm (T n) :=
  ⟨shear b d,shear b (-d),shear_shear b d, fun x=>by simpa using shear_shear b (-d) x⟩

lemma e_shear (b) (d : ZMod n) (x y : T n) :
    e (shear (!b) (-d) x) (shear b d y)=e x y := by
  unfold e; congr 1; cases b <;> simp [dot,shear] <;> ring

lemma hat_sh (f : T n → ℂ) (b : Bool) (d : ZMod n) (k) :
    hat (fun i=> f (shear b d i)) k = hat f (shear (!b) (-d) k) := by
  exact Fintype.sum_equiv (shPerm b d) _ _ fun x => by simp only [shPerm,Equiv.coe_fn_mk,e_shear]

def mass (f : T n → ℝ) (k : T n) := normSq (hat (fun i=> (f i:ℂ)) k)

lemma allmass (f : T n→ℝ) :
    ∑ k, mass f k = (order n:ℝ)^2*av (fun i=> (f i)^2) := by
  unfold mass
  rw [parse,pow_two,mul_assoc,av_card]
  simp [sq]

lemma at0 (f : T n→ℝ) :
    mass f 0 = (order n:ℝ)^2*(av f)^2 := by
  unfold mass
  have he : hat (fun i=> (f i:ℂ)) 0 = ↑(∑ i, f i) := by simp [hat,e,c,dot]
  rw [he, ← av_card]
  simp [sq]

lemma vnonzero (f : T n→ℝ) :
    ∑ k, (if k=0 then 0 else mass f k) = (order n:ℝ)^2*var2 f := by
  have he (k) : (if k=0 then 0 else mass f k) = mass f k-(if k=0 then mass f k else 0) := by
    split <;> simp_all
  simp only [he,sum_sub_distrib,allmass,var2_sum]
  simp [at0]; ring

/-- Character displacement away from low frequencies. -/
abbrev lift (i : ZMod n) := i.valMinAbs
def near (i : ZMod n) : Prop := 16*|lift i|<(n:ℤ)

instance (i : ZMod n) : Decidable (near i) := by unfold near; infer_instance

def threshold : ℝ := 2*(1-Real.cos (Real.pi/8))

lemma pos_threshold : 0<threshold := by
  have hp:=Real.pi_pos
  have h := Real.strictAntiOn_cos (show (0:ℝ)∈ Set.Icc 0 Real.pi by constructor <;> linarith)
      (show Real.pi/8∈ Set.Icc 0 Real.pi by constructor <;> linarith) (show 0<Real.pi/8 by linarith)
  rw [Real.cos_zero] at h
  unfold threshold; linarith

lemma far_threshold (i : ZMod n) (h : ¬ near i) :
    threshold ≤ normSq (c (-i)-1) := by
  rw [normSq_sub,csq]
  simp only [map_one,mul_one]
  let t := 2*Real.pi* (lift i:ℝ)/n
  have he : c (-i) = Complex.exp (-(t:ℂ)*I) := by
    have H := ZMod.stdAddChar_coe (N:=n) (-lift i)
    simp [lift] at H
    simp [t,c,lift,H]; congr 1; ring
  have hr : (Complex.exp (-(t:ℂ)*I)).re = Real.cos t := by
    rw [Complex.exp_mul_I]; simp [← Complex.ofReal_cos]
  have hn : 0<(n:ℝ) := by exact_mod_cast (NeZero.pos n)
  have hp := Real.pi_pos
  obtain ⟨h1,h2⟩ := ZMod.valMinAbs_mem_Ioc i
  unfold near at h; push Not at h
  have h3 : (n:ℝ) ≤ 16 * |(lift i:ℝ)| := by exact_mod_cast h
  have h1' : -(n:ℝ)< (lift i:ℝ)*2 := by exact_mod_cast h1
  have h2' : (lift i:ℝ)*2 ≤ (n:ℝ) := by exact_mod_cast h2
  have hh : |t| = 2*Real.pi* |(lift i:ℝ)| /n := by
    simp [t,abs_mul,abs_div,abs_of_nonneg (le_of_lt hp),abs_of_nonneg (le_of_lt hn)]
  have hu : |t| ≤ Real.pi := by
    rw [hh,div_le_iff₀ hn]; cases le_total 0 (lift i:ℝ) with
    | inl w=>rw [abs_of_nonneg w]; nlinarith
    | inr w=>rw [abs_of_nonpos w]; nlinarith
  have hl : Real.pi/8≤|t| := by rw [hh,le_div_iff₀ hn]; nlinarith
  have hz := Real.cos_le_cos_of_nonneg_of_le_pi (show 0≤Real.pi/8 by linarith) hu hl
  have hnz : Real.cos |t| = Real.cos t := by
    rcases le_total 0 t with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.cos_neg]
  rw [hnz] at hz
  rw [he,hr]
  unfold threshold; linarith

end Square
end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Finset
variable {α β γ : Type}

def energy [Fintype α] (k : ℕ) (f : α → ℝ) (p : α → α) :=
  av fun i=> (f (p i)-f i)^k
def mass4 [Fintype α] (f : α → ℝ) := av fun i=> f i^4
abbrev Family (γ α : Type) := γ → Equiv.Perm α
def energies [Fintype α] [Fintype γ] (G : Family γ α) (f : α → ℝ) :=
  ∑ j : γ, energy 2 f (G j)

def expands [Fintype α] [Fintype γ] (G : Family γ α) (C : ℝ) :=
  ∀ f : α → ℝ, var2 f ≤ C * energies G f

lemma samesq (a b : ℝ) (h : 0≤a*b) :
    (a-b)^4 ≤ 4*(a^2-b^2)^2 ∧
      (a^2-b^2)^2 ≤ 2*(a-b)^2*(a^2+b^2) := by
  have : 0 ≤ (a-b)^2*(a*b) := by positivity
  constructor <;> nlinarith [(show 0≤ (a-b)^4 by positivity)]

lemma oppsq (a b : ℝ) (h : a*b≤0) :
    (a-b)^4 ≤ 4*(a^2+b^2)^2 ∧
      (a^2+b^2)^2 ≤ 2*(a-b)^2*(a^2+b^2) := by
  have : (a-b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a+b)]
  have hc : a*b*(a^2+b^2)≤0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
  constructor <;> nlinarith [sq_nonneg (a^2+b^2),sq_nonneg (a-b)]

lemma signedsq (a b : ℝ) :
    (a-b)^4 ≤ 4*(a*|a|-b*|b|)^2 ∧
      (a*|a|-b*|b|)^2 ≤ 2*(a-b)^2*(a^2+b^2) := by
  rcases le_total 0 a with ha|ha <;> rcases le_total 0 b with hb|hb
  · rw [abs_of_nonneg ha,abs_of_nonneg hb]
    simpa only [sq] using samesq a b (mul_nonneg ha hb)
  · rw [abs_of_nonneg ha,abs_of_nonpos hb]
    simpa [sq] using oppsq a b (mul_nonpos_of_nonneg_of_nonpos ha hb)
  · rw [abs_of_nonpos ha,abs_of_nonneg hb]
    have e := oppsq a b (mul_nonpos_of_nonpos_of_nonneg ha hb)
    constructor <;> linarith [e.1,e.2]
  · rw [abs_of_nonpos ha,abs_of_nonpos hb]
    have e := samesq a b (mul_nonneg_of_nonpos_of_nonpos ha hb)
    constructor <;> linarith [e.1,e.2]

lemma signedsq_eps (A a b : ℝ) (h : 0≤A) :
    32*A*(a*|a|-b*|b|)^2 ≤ a^4+b^4+2048*A^2*(a-b)^4 := by
  have he := mul_le_mul_of_nonneg_left (signedsq a b).2 (show 0≤32*A by positivity)
  nlinarith [sq_nonneg (a^2-32*A*(a-b)^2),sq_nonneg (b^2-32*A*(a-b)^2)]

lemma even4 (a b : ℝ) :
    ((a+b)/2)^4 + (a-b)^4/16 ≤ (a^4+b^4)/2 := by nlinarith [sq_nonneg (a^2-b^2)]

variable [Fintype α] [Nonempty α] [Fintype γ] [Nonempty γ]

/-- L4 Poincare via L2 on signed-squares. -/
lemma e4 {G : Family γ α} {C : ℝ} (hC : 1≤C) (h : expands G C)
    (f : α → ℝ) (ef : av f=0) :
    let A := C*Fintype.card γ
    mass4 f ≤ 1024*A^2 * av (fun j : γ=>energy 4 f (G j)) := by
  let A := C*(Fintype.card γ)
  have hA : 0 ≤ A := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  let g i := f i*|f i|
  have h1 : mass4 f ≤ 8*var2 g := by
    have he (i j : α) : (f i-f j)^4 ≤ 4*(g i-g j)^2 := (signedsq (f i) (f j)).1
    have hu : av (fun i=> av (fun j=> (f i-f j)^4)) ≤
         av (fun i=> av (fun j=>4*(g i-g j)^2)) := av_mono (fun i=> av_mono (he i))
    simp only [av_cmul,var2_pair] at hu
    have hh := pair_four f ef
    unfold mass4; linarith
  have h2 : mass4 f ≤ 8*A*av (fun j=>energy 2 g (G j)) := by
    have H := h g
    unfold energies at H
    rw [← av_card] at H
    dsimp only [A]; linarith
  have h3 (j : γ) :
      32*A* energy 2 g (G j) ≤ mass4 f+mass4 f+2048*A^2*energy 4 f (G j) := by
    have he : av (fun i=>32*A*(g (G j i)-g i)^2) ≤
         av (fun i=> f (G j i)^4 + f i^4 +2048*A^2*(f (G j i)-f i)^4) :=
      av_mono fun i=> signedsq_eps A _ _ hA
    rw [av_cmul,av_add,av_add,av_cmul,
      show av (fun i=>f (G j i)^4) = _ from
        av_perm (G j) (fun i=>f i^4)] at he
    exact he
  have hu := av_mono (f:=fun j=>32*A* energy 2 g (G j)) (g:=fun j =>
                 mass4 f+mass4 f+2048*A^2*energy 4 f (G j)) h3
  simp only [av_add, av_cmul, av_const] at hu
  dsimp; dsimp only [A] at h2 hu
  linarith

def lazyK (G : Family γ α) (f : α → ℝ) : α → ℝ :=
    fun i => av fun j=> (f (G j i)+f i)/2

omit [Nonempty α] in
lemma K_av (G : Family γ α) (f : α → ℝ) : av (lazyK G f)=av f := by
  unfold lazyK
  rw [av_swap]
  simp only [av_div,av_add]
  have e (j : γ) := av_perm (G j) f
  simp only [e,av_const]
  ring

omit [Nonempty α] in
lemma K_dec (G : Family γ α) (f : α → ℝ) :
    mass4 (lazyK G f) + (av fun j=>energy 4 f (G j))/16 ≤ mass4 f := by
  have H : av (fun i=> (lazyK G f i)^4) ≤ av (fun i=> av (fun j=> ((f (G j i)+f i)/2)^4)) :=
    av_mono fun i=> av_four_le (fun j=> (f (G j i)+f i)/2)
  have e (j : γ) :
     av (fun i=>((f (G j i)+f i)/2)^4) + energy 4 f (G j)/16 ≤ mass4 f := by
    have hi := av_mono (f:=fun i=> ((f (G j i)+f i)/2)^4 + (f (G j i)-f i)^4 /16)
        (g:=fun i=> (f (G j i)^4+f i^4)/2) (fun i=> even4 _ _)
    rw [av_add,av_div,av_div,av_add,show av (fun i=>f (G j i)^4) = _ from
           av_perm (G j) (fun i=>f i^4)] at hi
    unfold energy mass4
    linarith
  unfold mass4
  rw [av_swap (fun i j=> ((f (G j i)+f i)/2)^4)] at H
  have he := av_mono (f:=fun j : γ=> av (fun i=>((f (G j i)+f i)/2)^4) +
                   energy 4 f (G j)/16) (g:=fun _=> mass4 f) e
  rw [av_add,av_div,av_const] at he
  dsimp only [mass4] at *
  linarith

def loss (γ : Type) [Fintype γ] (C : ℝ) := (16384*(C*Fintype.card γ)^2)⁻¹

lemma loss_bounds (hC : 1≤ C) :
    0 < loss γ C ∧ loss γ C < 1 := by
  have h : (1:ℝ) ≤ Fintype.card γ := by exact_mod_cast Fintype.card_pos
  have h' : 1 ≤ C * Fintype.card γ := by nlinarith
  unfold loss
  have h0 : 1 < 16384 * (C * ↑(Fintype.card γ)) ^ 2 := by nlinarith
  constructor
  · exact inv_pos.mpr (by linarith)
  · exact inv_lt_one_of_one_lt₀ h0

lemma K_shrink {G : Family γ α} (hC : 1≤ C) (h : expands G C)
    (f : α → ℝ) (ef : av f=0) : mass4 (lazyK G f) ≤ (1-loss γ C)*mass4 f := by
  have h1 := K_dec G f
  have h2 := e4 hC h f ef
  set V := av (fun j : γ=>energy 4 f (G j))
  set A := C*↑(Fintype.card γ)
  change mass4 f ≤ 1024*A^2*V at h2
  change _ ≤ (1-(16384*A^2)⁻¹) * mass4 f
  have hA : 0 < A := mul_pos (by linarith)
    (Nat.cast_pos.mpr Fintype.card_pos)
  have he : (16384*A^2)⁻¹ * mass4 f ≤ V/16 := by
    field_simp
    linarith
  linarith

def walk (G : Family γ α) (f : α → ℝ) : ℕ → α → ℝ
 | 0 => f
 | d+1 => lazyK G (walk G f d)

lemma walk_mix {G : Family γ α} (hC : 1 ≤ C) (h : expands G C) (f : α → ℝ)
    (d : ℕ) :
    mass4 (fun i=> walk G f d i-av f) ≤ (1-loss γ C)^d * (16*mass4 f) := by
  let g := fun i=> f i-av f
  have eg : av g=0 := by simp [g,av_sub,av_const]
  have eg1 : mass4 g ≤16*mass4 f := by
    have hz (i : α) : (f i-av f)^4 ≤ 8*(f i^4 + av f^4) := by
      have hs := even4 (f i) (av f)
      linarith [(show 0≤ ((f i+av f)/2)^4 by positivity)]
    have H := @av_mono α _ _ _ (show (fun i=>(f i-av f)^4) ≤
                    (fun i=>8*(f i^4+av f^4)) from hz)
    simp only [av_cmul,av_add,av_const] at H
    dsimp only [g,mass4]
    linarith [av_four_le f]
  have he (d : ℕ) :
      mass4 (walk G g d) ≤ (1-loss γ C)^d * (16*mass4 f) ∧
          av (walk G g d)=0 ∧ walk G g d = fun i=>walk G f d i-av f := by
    induction d with
    | zero => simpa only [pow_zero,one_mul,walk] using And.intro eg1 ⟨eg,rfl⟩
    | succ d ih =>
      obtain ⟨e1,e2,e3⟩ := ih
      refine ⟨?_,?_,?_⟩
      · rw [walk,pow_succ']
        exact le_trans (K_shrink hC h _ e2)
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left e1 (show 0 ≤ 1-loss γ C from sub_nonneg.2 (le_of_lt (loss_bounds hC).2)))
      · rw [walk,K_av,e2]
      · funext i
        simp only [walk,lazyK,e3,av_div,av_add,av_sub,av_const]
        ring
  obtain ⟨h1,h2,h3⟩ := he d
  rwa [← h3]

end
end ExactDerandomization.Analysis

end

section

/-!
Uniform affine mixing input for the paper, part 1: an elementary Fourier
proof of a square torus gap. Additional permutations of an external
coordinate are permitted during shear moves. This provides the needed
finite statement without assuming a property-(T) result.
-/
namespace ExactDerandomization.Analysis.Square
noncomputable section
open Finset Complex

variable {n : ℕ} [NeZero n]

def core (k : T n) := k≠0 ∧ near k.1 ∧ near k.2
instance (k : T n) : Decidable (core k) := by unfold core; infer_instance

def sector (k : T n) : Bool := decide (|lift k.2| ≤ |lift k.1|)
def signcode (k : T n) : Bool := decide ((lift k.2 > 0) = (lift k.1 > 0))

omit [NeZero n] in
lemma lift_zero (a : ZMod n) : lift a=0 ↔ a=0 := ZMod.valMinAbs_eq_zero _

abbrev Shears := Bool × Bool

def amount (b : Bool) : ℤ := if b then 3 else -3
/-- Frequency moves -/
def move (b : Shears) : Equiv.Perm (T n) := shPerm (!b.1) (amount b.2 : ZMod n)

lemma swing_near (x y : ZMod n) (a : Bool) (h : near x) (e : near y) :
    lift (x + (amount a:ZMod n) * y) = lift x + amount a * lift y := by
  rw [lift, ZMod.valMinAbs_spec]
  constructor
  · simp [lift]
  · simp only [Set.mem_Ioc]
    unfold near at h e
    have h1:= le_abs_self (lift x); have h2:= neg_le_abs (lift x)
    have h3:= le_abs_self (lift y); have h4:= neg_le_abs (lift y)
    cases a <;> dsimp [amount] <;> omega

lemma squash (x y : ℤ) (a : Bool) (h : |y| ≤ |x|) (e : x ≠ 0) :
    |x| < |y+amount a*x| ∧ decide ((y+amount a*x > 0)=(x>0))=a := by
  obtain ⟨h0,h1⟩ := abs_le.1 h
  rcases e.lt_or_gt with w|w
  · rw [abs_of_neg w] at *
    cases a <;> simp [amount,lt_abs] <;> omega
  · rw [abs_of_pos w] at *
    cases a <;> simp [amount,lt_abs] <;> omega

lemma ping {k : T n} {b : Shears} (h : core k) (hb : sector k=b.1) :
    let v := move b k
    v≠0 ∧ (!sector v)=b.1 ∧ signcode v=b.2 := by
  rcases k with ⟨x,y⟩; obtain ⟨hk,hx,hy⟩ := h
  have he : ¬(lift x=0 ∧ lift y=0) := by
    intro h; apply hk; simp [lift_zero x |>.1 h.1,lift_zero y |>.1 h.2]
  rcases b with ⟨b,s⟩
  cases b
  · simp only [sector, decide_eq_false_iff_not] at hb
    have hv : lift y ≠ 0 := by intro hy; simp [hy] at hb
    have hg := squash (lift y) (lift x) s (by omega) hv
    change (x+_,y)≠0 ∧ _
    refine ⟨fun h=>hv ((lift_zero y).2 (congrArg Prod.snd h)),?_⟩
    simp only [move,shPerm,shear,sector,Equiv.coe_fn_mk,signcode,Bool.not_false,
       swing_near x y s hx hy]
    constructor
    · simp [le_of_lt hg.1]
    · simpa only [eq_comm (a:=(lift y > 0))] using hg.2
  · simp only [sector, decide_eq_true_eq] at hb
    have hv : lift x ≠ 0 := by
      intro h
      simp [h] at hb
      apply he ⟨h,(lift_zero y).mpr ?_⟩
      simpa only [lift_zero] using hb
    have hg := squash (lift x) (lift y) s hb hv
    change (x,y+_)≠0 ∧ _
    refine ⟨fun h=>hv ((lift_zero x).2 (congrArg Prod.fst h)),?_⟩
    simp only [move,shPerm,shear,sector,Equiv.coe_fn_mk,signcode,Bool.not_true,
        swing_near y x s hy hx]
    exact ⟨by simp [not_le.2 hg.1],hg.2⟩

lemma sqcompare (x y : ℂ) :
    2*normSq x ≤ 3*normSq y +6*normSq (y-x) := by
  simp only [normSq_apply, sub_re, sub_im]
  nlinarith [sq_nonneg (2*x.re-3*y.re), sq_nonneg (2*x.im-3*y.im)]

variable {α : Type} [Fintype α] [Nonempty α]
variable (F : α → T n → ℝ)
def atoms (k : T n) := av (fun i => mass (F i) k)
omit [Nonempty α] in
lemma ann (k) : 0 ≤ atoms F k := av_nonneg _ (fun _=> normSq_nonneg _)

def changeF (b : Shears) (u : Equiv.Perm α) (i : α) (x : T n) : ℝ :=
    F (u i) (shear b.1 (-(amount b.2 : ZMod n)) x) - F i x
def changed (b : Shears) (u : Equiv.Perm α) := atoms (changeF F b u)

omit [Nonempty α] in
lemma trial (k : T n) (b : Shears) (u : Equiv.Perm α) :
    2 * atoms F k ≤ 3 * atoms F (move b k) + 6*changed F b u k := by
  have he (i) : 2 * mass (F i) k ≤
            3 * mass (F (u i)) (move b k) +6*mass (changeF F b u i) k := by
    unfold changeF mass
    simp_rw [ofReal_sub]
    rw [hat_sub,hat_sh (fun j=>(F (u i) j:ℂ)) b.1 (-(amount b.2:ZMod n)) k,neg_neg]
    exact sqcompare _ _
  unfold changed atoms
  rw [← av_perm u (fun i=> mass (F i) (move b k))]
  rw [← av_cmul,← av_cmul,← av_cmul,← av_add]
  exact av_mono he

omit [Nonempty α] in
lemma deflect (u : Shears → Equiv.Perm α) :
    4 * ∑ k, (if core k then atoms F k else 0) ≤
       3 * ∑ k, (if k=0 then 0 else atoms F k) + 6 * ∑ b, ∑ k, changed F b (u b) k := by
  let ok (k : T n) b := core k ∧ sector k=b
  classical
  let dirsum k b := if ok k b then atoms F k else 0
  let back k b s := if (!sector k)=b ∧ signcode k=s ∧ k≠0 then atoms F k else 0
  have ev (b s : Bool) : 2 * ∑ k, dirsum k b ≤
        3 * ∑ k, back k b s + 6*∑ k, changed F (b,s) (u (b,s)) k := by
    let m : Equiv.Perm (T n) := move (b,s)
    rw [← Fintype.sum_equiv m (fun k=>back (m k) b s) (fun k=>back k b s) (fun _=>rfl),
       mul_sum,mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro k hk
    by_cases h : ok k b
    · have hg := ping (b:=(b,s)) h.1 h.2
      have hp : (!sector (m k))=b ∧ signcode (m k)=s ∧ m k≠0 :=
        ⟨hg.2.1,hg.2.2,hg.1⟩
      unfold dirsum back; rw [ite_eq_left h,ite_eq_left hp]; exact trial F k _ _
    · simp only [dirsum,h,ite_false,mul_zero]
      have ht : 0≤back (m k) b s := by unfold back; split; apply ann; rfl
      have hx : 0≤changed F (b,s) (u (b,s)) k := ann _ _
      linarith
  have ea : (∑ b : Shears, 2 * ∑ k, dirsum k b.1) ≤
      ∑ b : Shears, (3 * ∑ k, back k b.1 b.2 + 6*∑ k, changed F b (u b) k) :=
     sum_le_sum fun b _ => ev b.1 b.2
  rw [sum_add_distrib,← mul_sum,← mul_sum,← mul_sum,sum_comm, sum_comm (f:=fun (b : Shears) k=>back k b.1 b.2)] at ea
  have hd (k : T n) : ∑ b : Shears, dirsum k b.1 = 2*(if core k then atoms F k else 0) := by
    rw [Fintype.sum_prod_type]
    cases hb : sector k <;> by_cases e : core k <;> simp [dirsum, ok, hb,e]
  have he (k : T n) : ∑ b : Shears, back k b.1 b.2 = if k=0 then 0 else atoms F k := by
    rw [Fintype.sum_prod_type]
    cases hb : sector k <;> cases hs : signcode k <;> by_cases h : k=0 <;> simp [back,hb,hs,h]
  simp only [hd, he,← mul_sum] at ea
  linarith

def axial (b : Bool) : T n := if b then (1,0) else (0,1)
def shifted (b : Bool) (i : α) (x : T n) := F i (x+axial b)-F i x
private def evalC (b : Bool) (k : T n) := c (-(if b then k.1 else k.2))

omit [Nonempty α] in
lemma disp_shift (b : Bool) (k : T n) :
    atoms (shifted F b) k = normSq (evalC b k-1)*atoms F k := by
  have he (i : α) :
       mass (shifted F b i) k = normSq (evalC b k-1)*mass (F i) k := by
    unfold shifted mass
    simp_rw [ofReal_sub]
    rw [hat_sub,hat_shift (fun j=>(F i j:ℂ)) (axial b) k]
    have ht : e k (-axial b)=evalC b k := by cases b <;> simp [evalC,e,dot,axial]
    simp only [ht]
    rw [← sub_one_mul]; exact map_mul _ _ _
  simp only [atoms, he,av_cmul]

omit [Nonempty α] in
lemma wings (k : T n) :
    threshold*((if k=0 then 0 else atoms F k)-(if core k then atoms F k else 0)) ≤
       ∑ b : Bool, atoms (shifted F b) k := by
  rw [Fintype.sum_bool]
  have h0 (b) := ann (shifted F b) k
  by_cases he : k=0
  · rw [ite_eq_left he]
    rw [ite_eq_right (show ¬core k from fun h=> h.1 he)]
    linarith [h0 true,h0 false]
  rw [ite_eq_right he]; split
  · linarith [h0 true,h0 false]
  · rename_i hv
    have hh : ¬ near k.1 ∨ ¬ near k.2 := by unfold core at hv; tauto
    have hz := ann F k
    simp only [sub_zero]
    rcases hh with hl|hr
    · have hw : threshold ≤ normSq (evalC true k - 1) := far_threshold _ hl
      linarith [mul_le_mul_of_nonneg_right hw hz, disp_shift F true k, h0 false]
    · have hw : threshold ≤ normSq (evalC false k - 1) := far_threshold _ hr
      linarith [mul_le_mul_of_nonneg_right hw hz, disp_shift F false k,h0 true]

lemma gapFuel_pos : 1< 6+4/threshold := by linarith [div_pos (show 0<(4:ℝ) by norm_num) pos_threshold]

def meanSq := av fun i=> av (fun x=> F i x ^2)
omit [Nonempty α] in
lemma meanSqNN : 0 ≤ meanSq F := av_nonneg _ (fun _=> av_nonneg _ (fun _=>sq_nonneg _))

omit [Nonempty α] in
lemma packA :
    ∑ k, atoms F k = (order n:ℝ)^2 * meanSq F := by
  unfold atoms meanSq
  rw [← av_sum Finset.univ (fun k i=>mass (F i) k)]
  simp only [allmass,av_cmul]

omit [Nonempty α] in
/-- shear on chart large-first operates on first physical coordinate;
left action is simultaneous on any allowed external index. -/
lemma square_gap (u : Shears → Equiv.Perm α) :
    av (fun i=>var2 (F i)) ≤
        (6+4/threshold) * ((∑ b : Shears, meanSq (changeF F b (u b))) +
             ∑ b : Bool, meanSq (shifted F b)) := by
  have he : ∀ k:T n, (if k=0 then 0 else atoms F k) =
                        av fun i=>if k=0 then 0 else mass (F i) k := by
    intro k; split
    · next h=> simp only [av_zero]
    · rfl
  have hmain : ∑ k:T n, (if k=0 then 0 else atoms F k) =
       (order n:ℝ)^2*av (fun i=>var2 (F i)) := by
    simp only [he]
    rw [← av_sum Finset.univ (fun k i=>if k=0 then 0 else mass (F i) k)]
    simp only [vnonzero,av_cmul]
  have H:=deflect F u
  simp only [changed,hmain,packA,← mul_sum] at H
  have J := Finset.sum_le_sum (s:=(Finset.univ : Finset (T n))) fun k _ => wings F k
  rw [sum_comm (f:=fun (k:T n) b=> atoms (shifted F b) k),← mul_sum,sum_sub_distrib,hmain] at J
  simp only [packA,← mul_sum] at J
  set Tt := ∑ b:Bool, meanSq (shifted F b)
  set Ts := ∑ b:Shears, meanSq (changeF F b (u b))
  set Tl := ∑ k:T n, if core k then atoms F k else 0
  set L := av (fun i=>var2 (F i))
  let A := (order n:ℝ)^2
  have hA : 0 < A := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  have hp := pos_threshold
  have e1 : 4*Tl≤3*(A*L)+6*(A*Ts) := H
  have e2 : A*L - Tl ≤ A*Tt /threshold :=
     (le_div_iff₀ hp).2 (by rw [mul_comm]; exact J)
  have e3 : L ≤6*Ts+4/threshold*Tt := by
    apply le_of_mul_le_mul_left _ hA
    simp only [div_eq_mul_inv] at e2 ⊢; linarith
  have et : 0 ≤ Tt := Finset.sum_nonneg fun b _=> meanSqNN _
  have es : 0 ≤ Ts := Finset.sum_nonneg fun b _=> meanSqNN _
  have er : 0 ≤4/threshold := by positivity
  nlinarith

end
end ExactDerandomization.Analysis.Square

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Finset

variable {α β γ : Type}
variable [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

lemma var2_decomp (f : α → ℝ) (z : ℝ) :
    av (fun i=> (f i-z)^2) = var2 f+(av f-z)^2 := by
  rw [var2_sum]
  simp only [sub_sq,av_add,av_sub,av_mulc,av_const,av_cmul]
  ring

lemma var2_prod (f : α × β → ℝ) :
    var2 f= av (fun i=>var2 (fun j=> f (i,j))) + var2 (fun i=> av (fun j=>f (i,j))) := by
  simp only [var2_sum,av_prod,av_sub]
  ring

omit [Nonempty α] in
lemma var2_project (f : α → β → ℝ) :
    var2 (fun i=> av (f i)) ≤ av (fun j=>var2 (fun i=>f i j)) := by
  let z j:= av (fun i=>f i j)
  have h (i : α) : (av (f i)-av z)^2≤ av (fun j=> (f i j-z j)^2) := by
    rw [← av_sub]; exact av_sq_le _
  have hz : av z = av (fun i=> av (f i)) := by dsimp only [z]; rw [← av_swap f]
  have he := av_mono (f:=fun i=> (av (f i)-av z)^2) (g:=fun i=> av (fun j=> (f i j-z j)^2)) h
  rw [hz,av_swap (fun i j=>(f i j-z j)^2)] at he
  exact he

omit [Nonempty α] in
/-- Product permutations and projection onto first factor. -/
lemma energy_project (f : α × β → ℝ) (p : Equiv.Perm α) (q : Equiv.Perm β) :
    energy 2 (fun i=> av (fun j=> f (i,j))) p ≤ energy 2 f (p.prodCongr q) := by
  unfold energy
  rw [av_prod]
  apply av_mono
  intro i
  change (av _-av _)^2 ≤ av (fun j : β=> (f (p i,q j)-f (i,j))^2)
  rw [← av_perm q (fun j=> f (p i,j)),← av_sub]
  exact av_sq_le _

abbrev Punc (α : Type) [Zero α] := {a : α // a≠0}

variable [Zero α] [DecidableEq α]
variable [hp : Nonempty (Punc α)]

omit [Nonempty α] hp in
lemma punc_sum (f : α → ℝ) :
    ∑ i:Punc α, f i.val = ∑ a:α, if a=0 then 0 else f a := by
  simp_rw [show ∀ a, (if a=0 then 0 else f a) = if a≠0 then f a else 0 by intro a; grind]
  rw [← Finset.sum_filter, Finset.sum_subtype _ (p:=fun a : α=>a≠0) (by simp) f]

omit hp in
lemma card_punc :
    Fintype.card (Punc α)+1 = Fintype.card α := by
  have ht := Fintype.card_pos (α:=α)
  simp [Punc]; omega

lemma av_insert (f : α → ℝ) (h : ∀ i, 0≤f i) :
    av (fun i:Punc α=> f i.val) ≤ 2*av f := by
  set N := (Fintype.card α:ℝ)
  set M := (Fintype.card (Punc α):ℝ)
  have hM : 1≤ M := by dsimp only [M]; exact_mod_cast (show 1 ≤ Fintype.card (Punc α) from Fintype.card_pos)
  have h1 : N=M+1 := by
    dsimp only [N,M]; exact_mod_cast (card_punc (α:=α)).symm
  have e : M*av (fun i:Punc α=> f i.val) ≤ N*av f := by
    dsimp only [N,M]; rw [av_card,av_card,punc_sum]
    apply sum_le_sum; intro i _
    split; apply h; exact le_rfl
  have he := av_nonneg f h
  nlinarith

lemma var_insert (f : α → ℝ) :
    var2 (fun i:Punc α=> f i.val) ≤2*var2 f :=
  le_trans (var2_best _ (av f))
       (av_insert (fun i=>(f i-av f)^2) (fun _=>sq_nonneg _))

def rows (f : α → α → ℝ) : ℝ := av (fun i:Punc α=>var2 (f i.val))
def ctr (f : α → α → ℝ) : ℝ := av fun i:Punc α=>av fun j:Punc α=> f i.val j.val
abbrev switch (f : α → α → ℝ) : α → α → ℝ := fun i j=>f j i

lemma rows_ctrl (f : α → α → ℝ) :
    av (fun i:Punc α=>av fun j=> (f i j-ctr f)^2) ≤ 5*rows f+4*rows (switch f) := by
  let g (i:Punc α) := av fun j:Punc α=> f i j
  have hv : ctr f=av g := rfl
  have hi (i:Punc α) : av (fun j=> (f i j-ctr f)^2) ≤
        5*var2 (f i) + 2*(g i-ctr f)^2 := by
    rw [var2_decomp]
    let u : Punc α → ℝ := fun j=> av (f i)-f i j
    have hs := av_sq_le u
    have he : av (fun j:Punc α => u j^2) ≤ 2*var2 (f i) := by
      convert av_insert (fun j=> (f i j-av (f i))^2) (fun _=>sq_nonneg _) using 1
      congr 1
      ext j; dsimp [u]; ring
      rfl
    have hu : av u=av (f i)-g i := by simp [u,g,av_sub,av_const]
    rw [hu] at hs
    nlinarith [sq_nonneg (av (f i)+ctr f-2*g i)]
  have he := av_mono (f:=fun i:Punc α=>av fun j=> (f i j-ctr f)^2)
          (g:=fun i:Punc α=> 5*var2 (f i) + 2*(g i-ctr f)^2) hi
  rw [av_add,av_cmul,av_cmul,hv] at he
  have hs : var2 g ≤ 2*rows (switch f) := by
    refine le_trans (var2_project (fun (i : Punc α) (j:Punc α)=> f i j)) ?_
    unfold rows; rw [← av_cmul]
    exact av_mono fun j=>var_insert (switch f j.val)
  rw [hv]
  change _ ≤ 5 * rows f + 2 * var2 g at he
  linarith

omit [Fintype α] [Nonempty α] [DecidableEq α] in
lemma nonempty_punc : Nonempty (Punc (α×α)) := by
  obtain ⟨i,hi⟩ := hp
  exact ⟨⟨(i,i),by intro h; exact hi (congrArg Prod.fst h)⟩⟩

/-- Return normalization factors explicitly. -/
lemma punctured [Nonempty (Punc (α×α))] (f : α → α → ℝ) :
    (Fintype.card (Punc (α×α)):ℝ)*var2 (fun i : Punc (α×α)=> f i.val.1 i.val.2) ≤
      (Fintype.card (Punc α):ℝ)*Fintype.card α*(9 * (rows f + rows (switch f))) := by
  set M := (Fintype.card (Punc α):ℝ)
  set N := (Fintype.card α:ℝ)
  let z := ctr f
  have hz : ctr (switch f) = z := av_swap _
  let u x y := (f x y-z)^2
  let L := ∑ i : Punc α, ∑ j:α, u i.val j
  let R := ∑ j : Punc α, ∑ i:α, u i j.val
  have he : (Fintype.card (Punc (α×α)):ℝ)*var2 (fun i : Punc (α×α)=> f i.val.1 i.val.2) ≤ L+R := by
    refine le_trans (mul_le_mul_of_nonneg_left (var2_best _ z) (Nat.cast_nonneg _)) ?_
    rw [av_card]; dsimp only [L,R]
    change ∑ i : Punc (α × α), (fun j:α × α=>u j.1 j.2) i.val ≤ _
    rw [punc_sum (fun j : α×α=>u j.1 j.2),Fintype.sum_prod_type, punc_sum (fun i : α=>∑ j:α,u i j),
       punc_sum (fun j:α=>∑ i:α,u i j)]
    have eu (v:α → ℝ) (i : α) : (if i=0 then 0 else ∑ j,v j) =
          ∑ j, if i=0 then 0 else v j := by split <;> simp_all
    simp_rw [eu]
    nth_rw 3 [sum_comm]
    rw [←sum_add_distrib]
    apply sum_le_sum; intro i _
    rw [← sum_add_distrib]
    apply sum_le_sum; intro j _
    by_cases a:i=0 <;> by_cases b:j=0 <;> simp [a,b,u]
    positivity
  have et (p : α→α→ℝ) :
      ∑ i:Punc α,∑ j:α,(p i.val j-ctr p)^2 =
            M*N*av (fun i:Punc α=>av fun j:α=> (p i.val j-ctr p)^2) := by
    have hv (q : Punc α → α → ℝ) :
        ∑ i,∑ j,q i j=M*N*av (fun i=>av (q i)) := by
      simp_rw [← av_card, av_cmul]
      dsimp only [M,N]; ring
    exact hv _
  have hu : L ≤ M*N*(5*rows f+4*rows (switch f)) := by
    dsimp only [L,u,z]
    rw [et]; exact mul_le_mul_of_nonneg_left (rows_ctrl f) (by dsimp only [M,N]; positivity)
  have hv : R ≤ M*N*(5*rows (switch f)+4*rows f) := by
    dsimp only [R,u]; rw [← hz]
    change ∑ i:Punc α,∑ j:α, (switch f i.val j-ctr (switch f))^2 ≤ _
    rw [et]
    exact mul_le_mul_of_nonneg_left (rows_ctrl (switch f)) (by dsimp only [M,N]; positivity)
  linarith

end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Finset
open Square

namespace Affine

abbrev V (n : ℕ) := T n × T n
abbrev Cmd := (Shears ⊕ Bool) ⊕ (Bool × Bool)
abbrev Gen := Bool × Cmd
abbrev sh (b : Shears) : Cmd := Sum.inl (Sum.inl b)
abbrev tran (b : Bool) : Cmd := Sum.inl (Sum.inr b)
abbrev ov (i j : Bool) : Cmd := Sum.inr (i,j)

variable {n : ℕ} [NeZero n]

def crossTerm (y : T n) (i j : Bool) : T n :=
  let t := if j then y.1 else y.2
  if i then (t,0) else (0,t)

/-- act on lead coordinates with parameter other pair fixed. aff=true includes translations -/
def lead (k : Cmd) (aff : Bool) (d : T n) : Equiv.Perm (T n) :=
  match k with
  | Sum.inl (Sum.inl b) => shPerm b.1 (-(amount b.2 : ZMod n))
  | Sum.inl (Sum.inr b) => if aff then Equiv.addRight (axial b) else Equiv.refl _
  | Sum.inr (i,j) => Equiv.addRight (crossTerm d i j)

def face (b : Bool) : Equiv.Perm (V n) :=
    if b then Equiv.prodComm _ _ else Equiv.refl _

omit [NeZero n] in
lemma face_face (b) (x : V n) : face b (face b x)=x := by cases b <;> simp [face]

def leadPerm (aff : Bool) (k : Cmd) : Equiv.Perm (V n) :=
  ⟨fun x=> (lead k aff x.2 x.1,x.2), fun y=> ((lead k aff y.2).symm y.1,y.2),
    fun i=>by simp,fun i=>by simp⟩

def act (aff : Bool) (g : Gen) : Equiv.Perm (V n) :=
  ((face g.1).trans (leadPerm aff g.2)).trans (face g.1)

omit [NeZero n] in
lemma orient (aff b c) (x : T n) (y) :
    act aff (b,c) (face b (x,y))=face b (lead c aff y x,y) := by
  simp only [act,Equiv.trans_apply,face_face]; rfl

omit [NeZero n] in
lemma nodrift (g : Gen) : act false g (0:V n)=0 := by
  have he (b) : face b (0:V n)=0 := by cases b <;> rfl
  simp only [act,Equiv.trans_apply,he]; rw [show leadPerm false g.2 (0:V n)=0 from ?_,he]
  cases g.2 with
  | inl a =>
    cases a with
    | inl b =>
      rcases b with ⟨a,b⟩; cases a <;> simp [leadPerm,lead,shPerm,shear,Prod.ext_iff]
    | inr b => simp [leadPerm,lead]
  | inr a =>
    rcases a with ⟨i,j⟩; cases i <;> cases j <;> simp [leadPerm,lead,crossTerm,Prod.ext_iff]

def Fperm (g : Gen) : Equiv.Perm (Punc (V n)) :=
   Equiv.subtypeEquiv (act false g) (by
     intro x; constructor
     · exact fun h he=>h ((act false g).injective (he.trans (nodrift _).symm))
     · intro h e; subst x; exact h (nodrift g))

omit [NeZero n] in
lemma locked (b i) : Fperm (n:=n) (b,tran i) = Equiv.refl _ := by
  apply Equiv.ext; intro ⟨⟨j,k⟩,hx⟩; apply Subtype.ext
  cases b <;> simp [Fperm,act,face,leadPerm,lead]

abbrev gap0 := 6+4/threshold

section Torus

variable {α : Type} [Fintype α] [Nonempty α] (f : α × V n → ℝ)
    (p : Family Gen α)

def stepE (j : Gen) := energy 2 f ((p j).prodCongr (act true j))
def chart (b : Bool) := av (fun i:α=> av fun y:T n=>var2 (fun x=> f (i,face b (x,y))))

omit [Nonempty α] in
lemma chart_cost (b : Bool) (hn : ∀ i : Bool,p (b,tran i)=Equiv.refl _) :
    chart f b ≤ gap0 * ∑ c:Cmd, stepE f p (b,c) := by
  let F y i x := f (i,face b (x,y))
  let H (c:Cmd) (y x : T n) (i:α) :=
      (F y (p (b,c) i) (lead c true y x)-F y i x)^2
  let Z c (y : T n) := av fun i:α=> av fun x:T n=> H c y x i
  have he (y : T n) :
      av (fun i=>var2 (F y i)) ≤ gap0*∑ c:Cmd,Z c y := by
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    have ho := square_gap (F y) (fun s=> p (b,sh s))
    have hj : (∑ s:Shears, meanSq (changeF (F y) s (p (b, sh s)))) =
           ∑ s:Shears,Z (sh s) y := rfl
    have hk : (∑ s:Bool, meanSq (shifted (F y) s))=∑ s:Bool,Z (tran s) y := by
      apply sum_congr rfl; intro i _
      simp only [Z,H,hn,tran,lead,ite_true]
      rfl
    rw [hj,hk] at ho
    refine ho.trans (mul_le_mul_of_nonneg_left ?_ (by linarith [gapFuel_pos]))
    refine le_add_of_nonneg_right (sum_nonneg ?_)
    intro i _
    exact av_nonneg _ fun i=> av_nonneg _ (fun _=> sq_nonneg _)
  have ht (c:Cmd) : stepE f p (b,c) = av (Z c) := by
    unfold stepE energy; rw [av_prod]
    unfold Z
    rw [av_swap (f:=fun y i=>av fun x=>H c y x i)]
    congr 1
    funext i
    let L (r : V n) := (f (((p (b,c)).prodCongr (act true (b,c))) (i,r)) - f (i,r))^2
    change av L= _
    rw [← av_perm (face b) L,av_prod,av_swap (fun (x y:T n)=>L (face b (x,y)))]
    congr 1
    funext y
    congr 1
    funext x
    unfold L; simp only [Equiv.prodCongr_apply,Prod.map_apply,orient]; rfl
  unfold chart
  rw [av_swap (fun i (y:T n) =>var2 (F y i))]
  simp_rw [ht,← av_sum]
  rw [← av_cmul]
  exact av_mono he

omit [Nonempty α] in
lemma torus (hp : ∀ b i : Bool,p (b,tran i)=Equiv.refl _) :
    av (fun i : α=>var2 (fun j:V n=>f (i,j))) ≤
       gap0* ∑ j:Gen, stepE f p j := by
  have hk (i:α) : var2 (fun j:V n=>f (i,j)) ≤
          av (fun y:T n=>var2 (fun x=> f (i,face true (x,y)))) +
          av (fun y:T n=>var2 (fun x=> f (i,face false (x,y)))) := by
    rw [var2_prod]
    apply add_le_add
    · simp only [face,ite_true,Equiv.prodComm_apply]; exact le_rfl
    · simpa only [face,Bool.false_eq_true,ite_false,Equiv.refl_apply] using
         var2_project (fun (x y:T n)=>f (i,(x,y)))
  have he := av_mono (g:=fun i=>
          av (fun y:T n=>var2 (fun x=> f (i,face true (x,y)))) +
          av (fun y:T n=>var2 (fun x=> f (i,face false (x,y)))))
           (f:=fun i:α=>var2 (fun j:V n=>f (i,j))) hk
  rw [av_add] at he
  rw [Fintype.sum_prod_type,Fintype.sum_bool,mul_add]
  refine le_trans he (add_le_add ?_ ?_)
  · exact chart_cost f p _ (hp true)
  · exact chart_cost f p _ (hp false)

end Torus
end Affine
end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.Analysis.Affine
noncomputable section
open Square Finset

abbrev Frame (n : ℕ) := Punc (V n)
variable {n : ℕ} [Fact n.Prime]

instance square_punc : Nonempty (Punc (T n)) :=
    ⟨⟨(1,0),by simp [Prod.ext_iff]⟩⟩
instance frame_NE : Nonempty (Frame n) := nonempty_punc

def zoom (d : ZMod n) (e : d ≠ 0) : Equiv.Perm (T n) :=
   ⟨fun x=>(d*x.1,d*x.2),fun x=>(d⁻¹*x.1,d⁻¹*x.2),by intro x; simp [e],
      by intro x; simp [e]⟩

lemma slice_frame {y : T n} (hy : y≠0)
    (f : T n → ℝ) :
    var2 f ≤ gap0*∑ c : Cmd, energy 2 f (lead c false y) := by
  let j : Bool := decide (y.1≠0)
  let v := if j then y.1 else y.2
  have hv : v≠0 := by
    simp only [v]; split
    · next h=> simpa only [j,decide_eq_true_eq] using h
    · next h=>
      have eh : y.1=0 := by simpa [j] using h
      exact fun e=>hy (Prod.ext eh e)
  let p := zoom v hv
  have he (c:Shears) (x : T n) :
      p (shear c.1 (-(amount c.2:ZMod n)) x) = lead (sh c) false y (p x) := by
    rcases c with ⟨a,b⟩; cases a <;> simp [p,zoom,shear,lead,shPerm] <;> ring
  have ht (i) (x : T n) :
      p (x+axial i) = lead (ov i j) false y (p x) := by
    cases i <;> simp [p,zoom,lead,crossTerm,axial,v,mul_add] <;> split <;> simp_all
  let F := fun (_ : Unit) x=> f (p x)
  let u := fun (_ : Shears) => Equiv.refl Unit
  have H := square_gap F u
  have hz : av (fun i=>var2 (F i))=var2 f := by
    simp only [F,av_const,var2_sum,av_perm p f,
       av_perm p (fun i=> f i^2)]
  have ek (c) : meanSq (changeF F c (u c))=energy 2 f (lead (sh c) false y) := by
    simp only [meanSq,changeF,F,av_const,he]
    exact av_perm p (fun x=> (f (lead (sh c) false y x)-f x)^2)
  have ej (i) : meanSq (shifted F i)=energy 2 f (lead (ov i j) false y) := by
    simp only [meanSq, shifted,F,av_const,ht]
    exact av_perm p (fun x=> (f (lead (ov i j) false y x)-f x)^2)
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [hz,ek,ej] at H
  have hh (c : Cmd) : 0 ≤ energy 2 f (lead c false y) :=
     av_nonneg _ (fun _=>sq_nonneg _)
  refine H.trans (mul_le_mul_of_nonneg_left ?_ (show 0≤gap0 by linarith [gapFuel_pos]))
  have hd :
     ∑ i : Bool, energy 2 f (lead (ov i j) false y) ≤
       ∑ i : Bool × Bool, energy 2 f (lead (Sum.inr i) false y) := by
    rw [Fintype.sum_prod_type]
    apply sum_le_sum; intro i _
    apply single_le_sum (fun j _=>hh (ov i j)) (mem_univ j)
  exact add_le_add (le_add_of_nonneg_right (sum_nonneg fun i _=> hh (tran i))) hd

variable (F : Frame n → ℝ) (f : V n → ℝ)
abbrev nf := (Fintype.card (Frame n):ℝ)
abbrev nu := (Fintype.card (Punc (T n)):ℝ)

def weighingF (n : ℕ) [Fact n.Prime] : ℝ := Fintype.card (Frame n)
def weighingU (n : ℕ) [Fact n.Prime] : ℝ := (Fintype.card (Punc (T n)):ℝ)* order n

def fSlice (b : Bool) (y x : T n) := f (face b (x,y))
def fSliceE (b : Bool) (c : Cmd) (y : T n) := energy 2 (fSlice f b y) (lead c false y)

lemma fE_le (hf : ∀ i : Frame n,f i.val=F i) (b : Bool) (c) :
    weighingU n * av (fun i : Punc (T n)=> fSliceE f b c i.val) ≤
      weighingF n*energy 2 F (Fperm (b,c)) := by
  let g := fun i:V n => (f (act false (b,c) i)-f i)^2
  have he (i : Frame n) : (F (Fperm (b,c) i)-F i)^2 = g i.val := by
    rw [← hf,← hf]; rfl
  have hs (x : V n) :
      (∑ i:Frame n,g i.val)=∑ i:V n,g i := by
    rw [punc_sum]
    apply sum_congr rfl; intro i _; split
    · next h=> subst i; simp [g,nodrift]
    · rfl
  unfold energy weighingF
  rw [av_card]
  simp only [he]
  rw [hs 0,← Fintype.sum_equiv (face b) (fun i=>g (face b i)) g (fun _=>rfl),
     Fintype.sum_prod_type, sum_comm]
  have hc (y : T n) :
      (order n:ℝ)* fSliceE f b c y = ∑ x:T n,g (face b (x,y)) := by
    unfold fSliceE energy fSlice
    rw [av_card]; simp only [g,orient]
  unfold weighingU
  rw [mul_assoc,← av_cmul,av_card]
  simp only [hc]
  rw [punc_sum (fun y : T n=> ∑ x:T n,g (face b (x,y)))]
  exact sum_le_sum fun i _=> by split; apply sum_nonneg fun _ _=>sq_nonneg _; exact le_rfl

lemma slice_E (b : Bool) (hf : ∀ i : Frame n,f i.val=F i) :
    weighingU n * rows (fSlice f b) ≤
       gap0 * weighingF n * ∑ c:Cmd, energy 2 F (Fperm (b,c)) := by
  have he : rows (fSlice f b) ≤ gap0 * ∑ c:Cmd,av (fun i : Punc (T n)=> fSliceE f b c i.val) := by
    rw [← av_sum,← av_cmul]
    exact av_mono fun i=> slice_frame i.prop (fSlice f b i.val)
  have hs := sum_le_sum (s:=(univ : Finset Cmd)) fun c _ => fE_le F f hf b c
  rw [← mul_sum,← mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left he (show 0 ≤ weighingU n by unfold weighingU; positivity)
  have hu := mul_le_mul_of_nonneg_left hs (show 0≤gap0 by linarith [gapFuel_pos])
  linarith

lemma frame_gap :
    var2 F ≤ (9*gap0)*energies Fperm F := by
  let f (i : V n) := if h : i≠0 then F ⟨i,h⟩ else 0
  have hf (i : Frame n) : f i.val=F i := by simp [f,i.prop]
  have ek := punctured (fun (i j : T n)=>f (i,j))
  have he := slice_E F f true hf
  have hg := slice_E F f false hf
  change weighingF n * var2 (fun i : Frame n=> f (i.val.1,i.val.2)) ≤
          weighingU n * (9*(rows _+rows _)) at ek
  have h0 : (fun i : Frame n=> f (i.val.1,i.val.2))=F := funext hf
  have h1 : fSlice f true = fun i j=> f (i,j) := by ext; rfl
  have h2 : fSlice f false = fun i j=> f (j,i) := by ext; rfl
  rw [h0] at ek
  change weighingF n*var2 F≤ weighingU n * (9*(rows (fun i j=>f (i,j))
                                    +rows (fun i j=>f (j,i)))) at ek
  rw [← h1,← h2] at ek
  unfold energies
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  apply le_of_mul_le_mul_left (a:=weighingF n)
  · linarith
  · exact Nat.cast_pos.mpr Fintype.card_pos

lemma expands_frame : expands (α:=Frame n) Fperm (9*gap0) := fun F=>frame_gap F

variable (l : ℕ) [NeZero l]

def gens (k : Gen) : Equiv.Perm (Frame n × V l) :=
   Equiv.prodCongr (Fperm k) (act true k)

/-- Uniform spectral input needed by the conditional averaging. -/
theorem slice_gap : expands (gens (n:=n) l) (10*gap0) := by
   intro f
   rw [var2_prod]
   have h1 := torus f Fperm locked
   have hx : gap0 * ∑ j:Gen,stepE f Fperm j=gap0*energies (gens l) f := rfl
   rw [hx] at h1
   let g i := av fun j=> f (i,j)
   have h2:=frame_gap g
   have hu : energies Fperm g ≤ energies (gens l) f :=
      sum_le_sum fun j _ => energy_project f _ _
   have he := mul_le_mul_of_nonneg_left hu (show 0≤9*gap0 by linarith [gapFuel_pos])
   change _ + var2 g ≤ _
   linarith

theorem bits_gap : expands (α:=V l) (act true) gap0 := by
  intro f
  have h := torus (fun x : Unit × V l=> f x.2) (fun _=>Equiv.refl Unit) (fun _ _=>rfl)
  simp only [av_const] at h
  unfold stepE energy at h
  unfold energies energy
  simp only [Equiv.prodCongr_apply,Prod.map_snd,av_prod,av_const] at h ⊢
  exact h

end
end ExactDerandomization.Analysis.Affine

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Square _root_.OAI.ExactDerandomization.Analysis.Affine Finset

def side (n k : ℕ) := (n-1)/ (2^k)+1
instance (n k : ℕ) : NeZero (side n k) := ⟨Nat.succ_ne_zero _⟩

def rate (k : ℕ) : ℝ := (2^k)⁻¹ ^ (4:ℕ)
def pct (n k : ℕ) := ((side n k : ℝ)/n)^ (4:ℕ)
lemma rate_pos (k) : 0<rate k := by unfold rate; positivity
lemma pct_pos {n} (h : 0<n) (k) : 0<pct n k := by unfold pct; unfold side; positivity

lemma side_zero {n : ℕ} (h : 0<n) : side n 0=n := by simp [side]; omega
lemma side_antitone (n : ℕ) : Antitone (side n) := by
  intro a b e
  exact Nat.add_le_add_right (Nat.div_le_div_left
       (Nat.pow_le_pow_right (by omega) e) (pow_pos (by omega) _)) 1
lemma side_le {n} (h : 0<n) (k : ℕ) : side n k≤n :=
  le_trans (side_antitone n (Nat.zero_le k)) (le_of_eq (side_zero h))

lemma rate_ratio {n k} (hp : 0<n) :
    (2^k:ℝ)⁻¹ ≤ (side n k:ℝ)/n ∧
     (2^k≤n → (side n k:ℝ)/n ≤ 2 * (2^k:ℝ)⁻¹) := by
  have h0 : 0 < 2^k := pow_pos (show 0< (2:ℕ) by omega) _
  have e := Nat.mod_lt (n-1) h0
  have h : n-1 = (side n k-1)*2^k+(n-1)%(2^k) := by
    simp [side,Nat.div_add_mod']
  have ht : (side n k-1)*2^k+2^k=side n k*2^k := by
    rw [show (side n k -1)*2^k+2^k=(side n k-1+1)*2^k by ring]
    congr 1
  constructor
  · have hu : n≤ side n k*2^k := by omega
    have he : (n:ℝ) ≤ side n k* (2:ℝ)^k := by exact_mod_cast hu
    field_simp; linarith
  · intro hg
    have hu : side n k *2^k≤2*n := by omega
    have he : (side n k:ℝ)* (2:ℝ)^k≤2*n := by exact_mod_cast hu
    field_simp; linarith

lemma pct_bounds {n k} (h : 2^k≤n) : rate k ≤ pct n k ∧ pct n k ≤16*rate k := by
  have hn : 0<n := lt_of_lt_of_le (by positivity) h
  obtain ⟨h1,h2⟩ := rate_ratio (k:=k) hn
  refine ⟨pow_le_pow_left₀ (by positivity) h1 4,?_⟩
  have he := pow_le_pow_left₀ (by positivity) (h2 h) 4
  unfold pct rate
  calc _ ≤ _ := he
       _ = _ := by ring

def vmap {α β : Type} (f : α→ β) (a : (α × α) × (α × α)) :=
    ((f a.1.1,f a.1.2),(f a.2.1,f a.2.2))
def each {α : Type} (f : α → Prop) (a : (α × α) × (α × α)) :=
    f a.1.1 ∧ f a.1.2 ∧ f a.2.1 ∧ f a.2.2

variable {n : ℕ} [Fact n.Prime]

abbrev Channel (n : ℕ) := Frame n × V n

def restr (k : ℕ) (v : V n) : Prop := each (fun i:ZMod n=> i.val < side n k) v
def vwide (k) (v : V (side n k)) : V n := vmap (fun i=> (i.val:ZMod n)) v
def vshort (k) (v : V n) : V (side n k) := vmap (fun i=> (i.val:ZMod (side n k))) v

instance (v : V n) (k) : Decidable (restr k v) := by unfold restr each; infer_instance
lemma wrest (k) (v : V (side n k)) :
    restr k (vwide k v : V n) ∧ vshort k (vwide k v : V n) = v := by
  have h (i : ZMod (side n k)) : (↑i.val:ZMod n).val=i.val := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt i) (side_le (NeZero.pos n) k))]
  simp only [restr, each,vwide,vshort,vmap,h,ZMod.val_lt,ZMod.natCast_zmod_val]; simp
lemma restw (k) (v : V n) (h : restr k v) : vwide k (vshort k v)=v := by
  unfold restr each at h
  obtain ⟨h1,h2,h3,h4⟩ := h
  simp only [vwide,vshort,vmap,ZMod.val_natCast,Nat.mod_eq_of_lt,h1,h2,h3,h4,ZMod.natCast_zmod_val]

def vEval (s : Channel n) (y : ZMod n) : V n := s.2+y • s.1.val
def hit (k) (y : ZMod n) (s : Channel n) := restr k (vEval s y)
instance (k) (y : ZMod n) (s) : Decidable (hit k y s) := by unfold hit; infer_instance

abbrev pc (n k : ℕ) := Frame n × V (side n k)
def openP (k) (y : ZMod n) (s : pc n k) : Channel n :=
   (s.1,vwide k s.2-y • s.1.val)
def closeP (k) (y : ZMod n) (s : Channel n) : pc n k :=
   (s.1,vshort k (vEval s y))

lemma hit_open (k) (y : ZMod n) (s : pc n k) : hit k y (openP k y s) := by
  simp only [openP,hit,vEval,sub_add_cancel]
  exact (wrest k s.2).1
lemma close_open (k) (y : ZMod n) (s : pc n k) : closeP k y (openP k y s)=s := by
  simp only [openP,closeP,vEval,sub_add_cancel,(wrest k s.2).2]
lemma open_close (k) (y : ZMod n) (s : Channel n) (h : hit k y s) :
    openP k y (closeP k y s)=s := by
  simp only [openP,closeP,restw k _ h]; simp only [vEval,add_sub_cancel_right]

def atP (k : ℕ) (y : ZMod n) (f : Channel n → ℝ) : ℝ := av (fun s=> f (openP k y s))

lemma cardinalV (n : ℕ) [NeZero n] : Fintype.card (V n)=n^4 := by
  simp [V,T]; ring

lemma ratioP (n : ℕ) [Fact n.Prime] (k) :
    (Fintype.card (pc n k):ℝ)=(Fintype.card (Channel n):ℝ)*pct n k := by
  simp only [Channel,pc,pct,Fintype.card_prod,ZMod.card,Nat.cast_mul]
  field_simp
  rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))]

lemma conditionP (k) (y : ZMod n) (f : Channel n → ℝ) :
    av (fun s=>if hit k y s then f s else 0) = pct n k * atP k y f := by
  classical
  have he : ∑ s : Channel n, (if hit k y s then f s else 0)=∑ s,f (openP k y s) := by
    rw [← sum_filter]
    symm
    let e : pc n k ≃ {s:Channel n//hit k y s} :=
      ⟨fun s=>⟨openP k y s,hit_open k y s⟩,fun s=>closeP k y s,
         close_open k y,fun s=>Subtype.ext (open_close k y _ s.prop)⟩
    rw [sum_subtype _ (p:=hit k y) (by simp) f]
    exact Fintype.sum_equiv e _ (fun s=> f s.val) (fun _=>rfl)
  rw [← av_card,← av_card] at he
  rw [ratioP] at he
  unfold atP
  apply mul_left_cancel₀ (show (Fintype.card (Channel n):ℝ)≠0 by positivity)
  rw [he,mul_assoc]

lemma contained (k j : ℕ) (e : j≤k) {y : ZMod n} {s} (h : hit k y s) : hit j y s := by
  have := side_antitone n e
  simp only [hit, restr, each] at *; omega

lemma allhit (y : ZMod n) (s) : hit 0 y s := by
  simp only [hit,restr,each,side_zero (NeZero.pos n),ZMod.val_lt]; tauto

def ind (k : ℕ) (y : ZMod n) (s : Channel n) : ℝ := if hit k y s then 1 else 0

lemma marginal (k) (y : ZMod n) : av (ind k y)=pct n k := by
  unfold ind
  simpa only [ind,atP,av_const,mul_one] using conditionP k y (fun _=>1)

lemma pct_le (n : ℕ) [Fact n.Prime] (k) : pct n k ≤ 1 := by
  rw [← marginal k (0:ZMod n),← av_const (α:=Channel n) 1]
  apply av_mono; intro i; dsimp [ind]; split <;> norm_num

def ri (n : ℕ) [Fact n.Prime] (k : ℕ) (w : V n) : ℝ := if restr k w then 1 else 0

lemma marginal_box (k) : av (ri n k)=pct n k := by
  have h := marginal k (0:ZMod n)
  rw [av_prod] at h
  unfold ri
  simpa only [ri,ind,hit,vEval,zero_smul, add_zero,av_const] using h

def scale (z : ZMod n) (h : z≠0) : Equiv.Perm (Frame n) :=
   let m (z:ZMod n) (e:z≠0) (x : Frame n) : Frame n :=
           ⟨z • x.val,smul_ne_zero e x.prop⟩
   ⟨m z h,m z⁻¹ (inv_ne_zero h),
     fun _=>Subtype.ext (inv_smul_smul₀ h _),fun _=>Subtype.ext (smul_inv_smul₀ h _)⟩

/-- padding by a fixed suffix leaves joint law unchanged -/
def affineChannel (u t : ZMod n) (h : u≠0) : Equiv.Perm (Channel n) :=
   let m := scale u h
   ⟨fun s=>(m s.1,s.2+t • s.1.val),fun s=>(m.symm s.1,s.2-t • (m.symm s.1).val),
     fun x=> by simp,fun x=>by simp⟩
lemma affine_eval (u t : ZMod n) (h) (s : Channel n) (y : ZMod n) :
    vEval (affineChannel u t h s) y=vEval s (t+y*u) := by
  simp [vEval,affineChannel,scale,add_smul,mul_smul,add_assoc]

lemma average_excl (f : V n→ℝ) (w : V n) (z : ZMod n) (e:z≠0) :
    (Fintype.card (Frame n):ℝ)*av (fun t:Frame n=> f (w+z • t.val)) + f w =
        (Fintype.card (V n):ℝ)*av f := by
  have hu := av_perm (scale z e) (fun t=> f (w+t.val))
  change av (fun t : Frame n=> f (w+z • t.val))=_ at hu
  rw [hu,av_card,av_card,punc_sum (fun t:V n=>f (w+t)),← Fintype.sum_equiv (Equiv.addLeft w)
                 _ f (fun i=>rfl)]
  have he (i:V n) : (if i=0 then 0 else f (w+i))=
                             f (w+i)-(if i=0 then f w else 0) := by split <;> simp_all
  simp [he,sum_sub_distrib]

lemma pairMean {k j} {x y : ZMod n} (he : y≠x) :
    atP k x (ind j y) ≤ 2*pct n j ∧ (k=j → atP k x (ind j y) ≤ pct n j) := by
  let f (v : V (side n k)) (s : Frame n) := ind j y (openP k x (s,v))
  let value v := av (f v)
  have hk : atP k x (ind j y)=av value := by rw [atP,av_prod,av_swap]
  let M : ℝ := Fintype.card (Frame n)
  let N : ℝ := Fintype.card (V n)
  have h0 : 1 ≤ M := by
    dsimp only [M]; exact_mod_cast (show 1≤ Fintype.card (Frame n) from Fintype.card_pos)
  have hmm : M+1=N := by
    dsimp only [M,N]; exact_mod_cast card_punc (α:=V n)
  have hv (v : V (side n k)) : M*value v + ri n j (vwide k v)=N*pct n j := by
    have e := average_excl (ri n j) (vwide k v) (y-x) (sub_ne_zero.2 he)
    rw [marginal_box] at e
    have eq : f v= _ := show f v = fun s:Frame n=>ri n j (vwide k v+(y-x) • s.val) by
      ext s
      have hl : vEval (openP k x (s,v)) y=vwide k v+(y-x) • s.val := by
        simp only [vEval,openP,sub_smul]; abel
      simp only [f,ind,hit,ri,hl]
    dsimp only [value]; rw [eq]; exact e
  constructor
  · rw [hk]
    refine le_trans (av_mono (f:=value) (g:=fun _ => 2*pct n j) (fun i=>?_)) (le_of_eq (av_const _))
    have e := hv i
    have hq := pct_pos (NeZero.pos n) j
    have hr : 0 ≤ ri n j (vwide k i) := by unfold ri; split <;> norm_num
    nlinarith
  intro e; subst k
  rw [hk]
  refine le_trans (av_mono (f:=value) (g:=fun _ => pct n j) (fun i=>?_)) (le_of_eq (av_const _))
  have he := hv i
  rw [ri,ite_eq_left (wrest j i).1] at he
  have ht := pct_le n j
  nlinarith

lemma pair_avg (k j) (x y : ZMod n) :
    av (fun i=> ind k x i * ind j y i) = pct n k * atP k x (ind j y) := by
  rw [← conditionP]
  apply congrArg av
  funext i
  unfold ind; split <;> simp_all

lemma ind_nonneg (k) (x : ZMod n) (i) : 0 ≤ ind k x i := by unfold ind; split <;> norm_num
lemma ind_mul (k) (x : ZMod n) (i) : ind k x i*ind k x i=ind k x i := by unfold ind; split <;> norm_num

/-- Variance estimate for deterministic test set. -/
lemma count_var {α : Type} (s : Finset α) (g : α → ZMod n)
    (h : Set.InjOn g s) (k : ℕ) :
    let f i := ∑ j ∈ s, ind k (g j) i
    av f = s.card*pct n k ∧ var2 f ≤ s.card*pct n k := by
  let p:=pct n k
  let f (i) := ∑ j∈s, ind k (g j) i
  have he : av f=s.card*p := by simp only [f,av_sum,marginal,sum_const,nsmul_eq_mul,p]
  refine ⟨he,?_⟩
  rw [var2_sum]
  change av (fun i=> (f i)^2)-_≤_
  classical
  have hi (a) (ha : a∈s) (b) (hb : b∈s) :
      av (fun i=>ind k (g a) i*ind k (g b) i) ≤
           p*p+(if a=b then p else 0) := by
    by_cases hx:a=b
    · subst a; rw [ite_eq_left rfl]; simp only [ind_mul,marginal]; dsimp [p]; nlinarith
    · rw [ite_eq_right hx,add_zero,pair_avg]
      have eq := pairMean (k:=k) (j:=k) (x:=g a) (y:=g b) (fun w=>hx (h ha hb w.symm))
      exact mul_le_mul_of_nonneg_left (eq.2 rfl) (le_of_lt (pct_pos (NeZero.pos n) k))
  have hj : av (fun i=>(f i)^2) =
       ∑ a∈s,∑ b∈s, av (fun i=>ind k (g a) i*ind k (g b) i) := by
    have h (i) : f i^2 = ∑ a∈s,∑ b∈s,ind k (g a) i*ind k (g b) i := by
      simp_rw [←mul_sum,←sum_mul]; rw [sq]
    simp only [h,av_sum]
  have hu := sum_le_sum (s:=s) fun a ha => sum_le_sum (s:=s) (fun b hb=> hi a ha b hb)
  have hr (a) (ha : a∈s) :
      ∑ b∈s,(p*p+(if a=b then p else 0)) = s.card*(p*p)+p := by simp [sum_add_distrib,ha]
  rw [hj]
  rw [sum_congr rfl hr, sum_const,nsmul_eq_mul] at hu
  change _-(av f)^2 ≤ (s.card:ℝ)*p
  rw [he]; linarith

end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Finset
variable {α : Type}

abbrev Vals (α : Type) := α → ℝ

def rkSet (s : Finset α) (f : Vals α) (K : ℕ) :=
   insert 0 ((s.image f).filter (fun v=>
          K < (s.filter (fun i=> v ≤ f i)).card))

lemma rkSet_zero (s : Finset α) (f : Vals α) (K) : 0 ∈ rkSet s f K := by simp [rkSet]

/-- zero-based descending rank, padded by zeros -/
def rank (s : Finset α) (f : Vals α) (K : ℕ) :=
   (rkSet s f K).max' ⟨0,rkSet_zero s f K⟩

lemma rank_nn (s : Finset α) (f : Vals α) (K) : 0≤ rank s f K :=
   Finset.le_max' _ _ (rkSet_zero s f K)

lemma rank_member (s : Finset α) (f : Vals α) (K) : rank s f K ∈ rkSet s f K := Finset.max'_mem _ _

lemma rank_gt {s : Finset α} {f : Vals α} {K v} (h : 0≤v) :
     v<rank s f K ↔ K < (s.filter (fun i=> v<f i)).card := by
   classical
   let r:=rank s f K
   constructor
   · intro h1
     have he := rank_member s f K
     rw [rkSet,Finset.mem_insert] at he
     rcases he with e|e
     · linarith
     · apply lt_of_lt_of_le (Finset.mem_filter.mp e).2
       apply Finset.card_le_card
       intro i hi
       obtain ⟨e,h⟩ := Finset.mem_filter.1 hi
       exact Finset.mem_filter.mpr ⟨e,lt_of_lt_of_le h1 h⟩
   · intro he
     let u := s.filter (fun i=> v<f i)
     have e : u.Nonempty := card_pos.mp (lt_of_le_of_lt K.zero_le he)
     let m:=(u.image f).min' (e.image _)
     obtain ⟨i,hi,rfl'⟩ : ∃ i∈u, f i=m := mem_image.mp (min'_mem _ _)
     have hm (i) (h : i∈u) : m ≤ f i := min'_le _ _ (mem_image_of_mem _ h)
     obtain ⟨hi,hg⟩ := mem_filter.mp hi
     rw [rfl'] at hg
     refine lt_of_lt_of_le hg (le_max' _ _ (mem_insert_of_mem (mem_filter.mpr ?_)))
     refine ⟨mem_image.2 ⟨i,hi,rfl'⟩, lt_of_lt_of_le he (card_le_card ?_)⟩
     intro j hj; exact mem_filter.2 ⟨(mem_filter.1 hj).1,hm j hj⟩

lemma rank_ge {s : Finset α} {f : Vals α} {K v} (h : 0<v) :
     v ≤ rank s f K ↔ K < (s.filter (fun i=> v≤f i)).card := by
   classical
   constructor
   · intro e
     have he := rank_member s f K
     rw [rkSet,mem_insert] at he
     rcases he with he|he
     · linarith
     apply lt_of_lt_of_le (mem_filter.1 he).2 (card_le_card ?_)
     intro i hi
     obtain ⟨hi,hk⟩ := mem_filter.mp hi
     exact mem_filter.2 ⟨hi,e.trans hk⟩
   · intro he
     let u:=s.filter (fun i=>v≤f i)
     have e : u.Nonempty := card_pos.mp (lt_of_le_of_lt K.zero_le he)
     let m:=(u.image f).min' (e.image _)
     obtain ⟨i,hi,rfl'⟩ : ∃ i∈u, f i=m := mem_image.mp (min'_mem _ _)
     have hm (i) (h : i∈u) : m ≤ f i := min'_le _ _ (mem_image_of_mem _ h)
     obtain ⟨hi,hg⟩ := mem_filter.mp hi
     rw [rfl'] at hg
     refine hg.trans (le_max' _ _ (mem_insert_of_mem (mem_filter.mpr ?_)))
     refine ⟨mem_image.2 ⟨i,hi,rfl'⟩, lt_of_lt_of_le he (card_le_card ?_)⟩
     intro j hj; exact mem_filter.2 ⟨(mem_filter.1 hj).1,hm j hj⟩

lemma rank_le {s : Finset α} {f : Vals α} {K v} (h : 0≤v) (e : ∀ i∈s, f i≤v) :
    rank s f K ≤ v := by
  classical
  by_contra! H
  have hk := (rank_gt h).1 H
  have he : (s.filter fun i=>v<f i).Nonempty := card_pos.mp (lt_of_le_of_lt K.zero_le hk)
  obtain ⟨i,hi⟩ := he
  exact (not_lt_of_ge (e i (mem_filter.1 hi).1)) (mem_filter.1 hi).2

lemma rank_compare {s : Finset α} {f g : Vals α} {K c} (h : 0≤c)
    (e : ∀ i∈s, f i - g i≤c) : rank s f K-rank s g K≤c := by
  by_contra! hs
  have ht := rank_nn s g K
  have h0 : 0≤c+rank s g K := by linarith
  have hv := (@rank_gt _ s f K _ h0).mp (by linarith)
  apply (lt_irrefl (rank s g K))
  apply (rank_gt ht).mpr
  apply lt_of_lt_of_le hv (card_le_card ?_)
  intro i hi; obtain ⟨hi,hx⟩ := mem_filter.1 hi
  exact mem_filter.2 ⟨hi,by linarith [e i hi]⟩

lemma rank_lip {s : Finset α} {f g : Vals α} {K c} (h : 0≤c)
    (e : ∀ i∈s, |f i - g i|≤c) : |rank s f K-rank s g K|≤c := by
  rw [abs_le']; constructor
  · exact rank_compare h (fun i hi=> (abs_le'.mp (e i hi)).1)
  · rw [neg_sub]; exact rank_compare h fun i hi=> by have := (abs_le'.mp (e i hi)).2; linarith

end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Finset

/-- A convenience for the different integrated-error sums. -/
structure Meter (α : Type) where
  I : (α → ℝ) → ℝ
  mono {f g : α → ℝ} : f≤g → I f≤I g
  add (f g) : I (fun i=> f i + g i) = I f+I g
  scl (c : ℝ) (f) : I (fun i=>c*f i)=c*I f

namespace Meter
variable {α β : Type}

def Avg [Fintype α] : Meter α := ⟨av,av_mono,av_add,av_cmul⟩
def Sum (S : Finset α) : Meter α :=
   ⟨fun f=>∑ i∈S,f i,fun h=>sum_le_sum fun i _=>h i,fun _ _=>sum_add_distrib,
     fun _ _=>(mul_sum ..).symm⟩
def Scale (u : Meter α) (c : ℝ) (h:0≤c) : Meter α :=
   ⟨fun f=>c*u.I f,fun e=>mul_le_mul_of_nonneg_left (u.mono e) h,
     fun f g=>by rw [u.add,mul_add],fun a f=>by rw [u.scl]; ring⟩
def Along (u : Meter α) (v : α → Meter β) : Meter (α × β) :=
   ⟨fun f=> u.I (fun a=> (v a).I fun b=>f (a,b)), fun h=>u.mono fun a=>(v a).mono fun b=>h (a,b),
     fun f g=> by simp only [Meter.add],fun c f=>by simp only [Meter.scl]⟩

variable (u : Meter α)

lemma I0 : u.I (fun _=>0)=0 := by simpa using u.scl 0 (fun _=>0)
lemma positive {f} (h : ∀ i,0≤f i) : 0≤u.I f :=
   le_trans (le_of_eq u.I0.symm) (u.mono h)
lemma Ineg (f) : u.I (fun i=> -f i) = -u.I f := by simpa using u.scl (-1) f
lemma Isub (f g): u.I (fun i=>f i-g i)=u.I f-u.I g := by
  simp only [sub_eq_add_neg,u.add,u.Ineg]
lemma Isum {γ : Type} (s : Finset γ) (f : γ → α → ℝ) :
    u.I (fun i=>∑ j∈s,f j i)=∑ j∈s,u.I (f j) := by
  classical
  induction s using Finset.induction_on <;> simp_all [u.I0, Meter.add]

def m2 (f : α → ℝ) := u.I fun i=>f i^2
def m4 (f : α → ℝ) := u.I fun i=>f i^4
def L (f) := fourth (u.m4 f)
lemma m2nn (f) : 0≤ u.m2 f := u.positive fun _=>sq_nonneg _
lemma m4nn (f) : 0≤ u.m4 f := u.positive fun _=> by positivity
lemma Lnn (f) : 0≤u.L f := fourth_nn _
lemma L4 (f) : u.L f^4=u.m4 f := fourth_four (u.m4nn _)

lemma LP {f : α → ℝ} {c : ℝ} (hc : 0≤ c) : u.L f ≤ c ↔ u.m4 f ≤ c^4 := by
  constructor
  · intro h; rw [← L4]; exact pow_le_pow_left₀ (u.Lnn _) h _
  · intro h
    exact (fourth_mono h).trans_eq (four_fourth hc)

lemma abs4 (z : ℝ) : |z|^4=z^4 := by rcases le_total 0 z with h|h; rw [abs_of_nonneg h]; rw [abs_of_nonpos h]; ring
lemma neg4 (z : ℝ) : (-z)^4=z^4 := by ring
lemma m4mono {f g} (h : ∀ i,|f i|≤|g i|) : u.m4 f≤u.m4 g :=
   u.mono fun i=>by simpa only [abs4] using pow_le_pow_left₀ (abs_nonneg _) (h i) 4
lemma Lmono {f g} (h : ∀ i, |f i|≤|g i|) : u.L f ≤ u.L g :=
   fourth_mono (u.m4mono h)
lemma Labs (f) : u.L (fun i=>|f i|) = u.L f := by simp [L,m4,abs4]
lemma Lzero : u.L (fun _=>0)=0 := by simp [L,m4,u.I0,fourth]
lemma Lneg (f) : u.L (fun i=> -f i)=u.L f := by simp [L,m4,neg4]
lemma Lmul (f) (c : ℝ) : u.L (fun i=>c*f i)=|c| * u.L f := by
  unfold L m4
  simp only [mul_pow,u.scl,fourth_mul (show 0≤c^4 by positivity)]
  have he := four_fourth (x:=|c|) (abs_nonneg _)
  rw [abs4] at he
  rw [he]

lemma cs (f g : α → ℝ) : (u.I fun i=> f i*g i)^2 ≤ u.m2 f*u.m2 g := by
  let x:=u.I fun i=> f i*g i
  have ht (p q:ℝ) : 0 ≤ p^2*u.m2 f-2*p*q*x+q^2*u.m2 g := by
    let F i:=p*f i-q*g i
    have he (i) : (F i)^2=p^2*f i^2-2*p*q*(f i*g i)+q^2*g i^2 := by unfold F; ring
    have hq:= u.m2nn F
    rw [m2] at hq
    simp only [he,u.add,u.Isub,u.scl] at hq
    exact hq
  have hh:=u.m2nn g
  rcases hh.eq_or_lt with hh|hh
  · by_contra h
    have he:x≠0:=by
      intro e; apply h; change x^2≤_;rw [e,← hh]; norm_num
    have hu:=ht 1 ((u.m2 f +1)/x)
    rw [←hh] at hu
    have hl : (u.m2 f+1)/x*x=u.m2 f+1:= by field_simp
    nlinarith [u.m2nn f]
  · have hu:= ht (u.m2 g) x
    change x^2≤_
    by_contra! hs
    nlinarith [mul_lt_mul_of_pos_right hs hh]

lemma m2m4 (f) : u.m2 (fun i=>f i^2)=u.m4 f := by
  unfold m2 m4
  simp only [← pow_mul]

lemma Holder2 (f g : α → ℝ) :
    u.I (fun i=> f i^2*g i^2) ≤ u.L f^2*u.L g^2 := by
  have he := u.cs (fun i=>f i^2) (fun i=>g i^2)
  rw [m2m4,m2m4,←L4,← L4] at he
  set x := u.I _
  have hd : 0≤ u.L f^2*u.L g^2 := by positivity
  nlinarith

lemma Holder3 (f g : α → ℝ) :
    u.I (fun i=> f i*g i^3) ≤ u.L f * u.L g^3 := by
  have he := u.cs (fun i=>f i*g i) (fun i=>g i^2)
  have hs := u.Holder2 f g
  rw [m2m4,←L4,m2] at he
  simp only [mul_pow] at he
  have hk (i : α) : f i*g i*g i^2=f i*g i^3 := by ring
  simp_rw [hk] at he
  have hz : 0≤u.L f *u.L g^3 := by have := u.Lnn f; have := u.Lnn g; positivity
  nlinarith [mul_le_mul_of_nonneg_right hs (show 0≤ u.L g^4 by positivity)]

lemma mink (f g : α → ℝ) : u.L (fun i=> f i+g i)≤ u.L f+u.L g := by
  let z:=fun i=> f i+g i
  have he:u.L z ^4=u.I (fun i=> f i*z i^3)+u.I (fun i=>g i*z i^3) := by
    rw [← Meter.add,u.L4]; unfold m4
    congr 1; ext i; unfold z; ring
  have hu:=u.Lnn z
  change u.L z≤_
  by_contra! hv
  have hh : 0< u.L z := by linarith [u.Lnn f,u.Lnn g]
  have hx := u.Holder3 f z; have hy := u.Holder3 g z
  nlinarith [mul_lt_mul_of_pos_right hv (pow_pos hh 3)]

lemma many {γ : Type} (S : Finset γ) (f : γ → α → ℝ) :
    u.L (fun i=>∑ j∈S,f j i) ≤ ∑ j∈S, u.L (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty=>simp [Lzero]
  | @insert a S ha h=>
    simp only [sum_insert ha]
    exact le_trans (u.mink _ _) (add_le_add_right h _)

end Meter
end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.Analysis
noncomputable section
open Square _root_.OAI.ExactDerandomization.Analysis.Affine

/- formula over any ring -/
namespace Wrap
abbrev Four (α : Type) := (α × α) × (α × α)
variable {R : Type} [CommRing R]

def lower (aff : Bool) (k : Cmd) (x y : R × R) : R × R :=
 match k with
 | Sum.inl (Sum.inl k)=>
   let t : R := -(amount k.2:R)
   if k.1 then (x.1+t*x.2,x.2) else (x.1,x.2+t*x.1)
 | Sum.inl (Sum.inr b)=> if aff then if b then (x.1+1,x.2) else (x.1,x.2+1) else x
 | Sum.inr (i,j) =>
   let t := if j then y.1 else y.2
   if i then (x.1+t,x.2) else (x.1,x.2+t)

def pol (aff : Bool) (g : Gen) (x : Four R) : Four R :=
    if g.1 then (x.1,lower aff g.2 x.2 x.1) else (lower aff g.2 x.1 x.2,x.2)

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
lemma act_formula (aff : Bool) (g : Gen) (x : V m) : act aff g x=pol aff g x := by
  have hl (x y : T m) (c) : lead c aff y x=lower aff c x y := by
    cases c with
    | inl b =>
      cases b with
      | inl b => rcases b with ⟨c,d⟩; cases c <;> rfl
      | inr b => cases aff <;> cases b <;> simp [lead,lower,axial,Prod.ext_iff]
    | inr b => rcases b with ⟨c,d⟩; cases c <;> cases d <;> simp [lead,lower,crossTerm,Prod.ext_iff]
  cases g with
  | mk b c=> cases b <;> simp [face,act,pol,leadPerm,hl]

def reduceV (m : ℕ) (z : Four ℤ) : V m := vmap (fun i : ℤ=> (i:ZMod m)) z
def raiseV (z : V m) : Four ℤ := vmap (fun i=> (i.val:ℤ)) z

omit [NeZero m] in
lemma reduce_add (x y) : reduceV m (x+y)=reduceV m x+reduceV m y := by
  simp [reduceV,vmap]

omit [NeZero m] in
lemma reducePol (g) (x) : reduceV m (pol true g x)=pol true g (reduceV m x) := by
  let p (v : ℤ × ℤ) := ((v.1: ZMod m),(v.2:ZMod m))
  have he (c) (x y : ℤ × ℤ) : p (lower true c x y) = lower true c (p x) (p y) := by
    cases c with
    | inl b => cases b with
      | inl b=> rcases b with ⟨i,j⟩; cases i <;> simp [lower,p]
      | inr b=> cases b <;> simp [lower,p]
    | inr b=> rcases b with ⟨i,j⟩; cases i <;> cases j <;> simp [lower,p]
  change (p _, p _) = pol true _ (p _,p _)
  cases g with
  | mk b c=> cases b <;> simp [pol,he]

lemma reraise (x : V m) : reduceV m (raiseV x)=x := by
  simp [reduceV,vmap,raiseV]

lemma modulo (z : Four ℤ) :
    raiseV (reduceV m z)=vmap (fun i=>i%(m:ℤ)) z := by
  simp only [reduceV,raiseV,vmap,ZMod.val_intCast]

omit [NeZero m] in
lemma affine_apply (g) (x y : V m) (b : ZMod m) :
    act true g (x-b • y)=act true g x-b • act false g y := by
  simp only [act_formula]
  have he c (x y z v : T m) :
      lower true c (x-b • z) (y-b • v) = lower true c x y - b • lower false c z v := by
    cases c with
    | inl a =>
      cases a with
      | inl a=> rcases a with ⟨i,j⟩; cases i <;> ext <;> simp [lower] <;> ring
      | inr a=> cases a <;> ext <;> simp [lower] <;> ring
    | inr a=> rcases a with ⟨i,j⟩; cases i <;> cases j <;> ext <;> simp [lower] <;> ring
  cases g with
  | mk b c=> cases b <;> simp [pol,he]

abbrev W := Four (Fin 11)
def addin (m : ℕ) (w : W) : Four ℤ := vmap (fun i=> (m:ℤ)*((i.val:ℤ)-5)) w

def chooseOne (m : ℕ) (i : ℤ) : Fin 11 :=
    ⟨min 10 (5-i/(m:ℤ)).toNat,by omega⟩

def guess (m : ℕ) (x : Four ℤ) : W := vmap (chooseOne m) x

lemma rem_one (x : ℤ) (h : -(4*(m:ℤ)) ≤ x ∧ x < 4*(m:ℤ)) :
    x+(m:ℤ)*((↑(chooseOne m x).val:ℤ)-5)=x%(m:ℤ) := by
  have hm : 0<(m:ℤ) := by exact_mod_cast NeZero.pos m
  have h1 : -4 ≤ x/(m:ℤ) := (Int.le_ediv_iff_mul_le hm).2 (by linarith [h.1])
  have h2 := Int.ediv_lt_of_lt_mul hm h.2
  have he : (↑(chooseOne m x).val : ℤ)-5=-(x/(m:ℤ)) := by dsimp [chooseOne]; omega
  rw [he]
  have h := Int.emod_add_mul_ediv x (m:ℤ)
  linarith

lemma pol_bounded (x : V m) (g) :
    each (fun i : ℤ=> -(4*(m:ℤ)) ≤ i ∧ i < 4*(m:ℤ)) (pol true g (raiseV x)) := by
  let ith (p : T m) := ((p.1.val:ℤ),(p.2.val:ℤ))
  let f i := -(4*(m:ℤ)) ≤ i ∧ i < 4*(m:ℤ)
  have h1 (p : ZMod m) : 0 ≤ (p.val:ℤ) ∧ (p.val:ℤ) < m := by
    constructor; positivity; exact_mod_cast ZMod.val_lt p
  have hp (p : ZMod m) : f p.val := by have h:=h1 p; dsimp [f]; omega
  have he (c) (p q : T m) :
      f (lower true c (ith p) (ith q)).1 ∧ f (lower true c (ith p) (ith q)).2 := by
    have h := h1 p.1; have h' := h1 p.2; have e:=h1 q.1; have e' := h1 q.2
    cases c with
    | inl b => cases b with
      | inl b=> rcases b with ⟨i,j⟩; cases i <;> cases j <;> dsimp [ith,f,lower,amount] <;> omega
      | inr b=> cases b <;> dsimp [ith,f,lower] <;> omega
    | inr b=> rcases b with ⟨i,j⟩; cases i <;> cases j <;> dsimp [ith,f,lower] <;> omega
  cases g with
  | mk b c =>
   cases b
   · exact ⟨(he c x.1 x.2).1,(he c x.1 x.2).2,hp _,hp _⟩
   · exact ⟨hp _,hp _,he c x.2 x.1⟩

variable {n : ℕ} [Fact n.Prime]

def guessP (k : ℕ) (g : Gen) (s : pc n k) : W := guess (side n k) (pol true g (raiseV s.2))

lemma affine_box (k : ℕ) (g) (s : pc n k) :
    act true g (vwide k s.2:V n)+reduceV n (addin (side n k) (guessP k g s))
       = vwide k (act true g s.2) := by
  let z := pol true g (raiseV s.2)
  let l := side n k
  have hv (x:V l) : vwide k x=reduceV n (raiseV x) := by
    simp only [reduceV,vwide,raiseV,vmap,Int.cast_natCast]
  have he : act true g s.2=reduceV l z := by rw [act_formula]; dsimp [z,l]; rw [reducePol,reraise]
  rw [hv,hv,act_formula,← reducePol, ← reduce_add,he, modulo]
  apply congrArg (reduceV n)
  obtain ⟨e,h,i,t⟩ := pol_bounded s.2 g
  exact Prod.ext (Prod.ext (rem_one _ e) (rem_one _ h)) (Prod.ext (rem_one _ i) (rem_one _ t))

/-- each fixed guessed variant permutes the *full* environment and does
not involve its not-yet-known retained point y. -/
def Variant (k : ℕ) (g : Gen) (w : W) : Equiv.Perm (Channel n) :=
   Equiv.prodCongr (Fperm g) ((act true g).trans (Equiv.addRight (reduceV n (addin (side n k) w))))

lemma variant_pin (k) (g) (y : ZMod n) (s : pc n k) :
    Variant k g (guessP k g s) (openP k y s)=openP k y (gens (side n k) g s) := by
  refine Prod.ext ?_ ?_
  · rfl
  · change act true g (vwide k s.2-y • s.1.val) + _ = vwide k _ - y • act false g s.1.val
    rw [affine_apply]
    change _ = vwide k (act true g s.2)-_
    rw [← affine_box k g s]; abel

end Wrap
end
end ExactDerandomization.Analysis

end

section

set_option synthInstance.maxSize 1024

namespace ExactDerandomization.Analysis
noncomputable section
open Finset Square _root_.OAI.ExactDerandomization.Analysis.Affine

abbrev Salt (d : ℕ) := V (2^d)

namespace Salt
variable {b d : ℕ}
abbrev Reg (d : ℕ) := ZMod (2^d)

def lo (d : ℕ) (s : Reg b) : Reg d := (s.val:Reg d)
def hi (d : ℕ) (s : Reg b) : Reg (b-d) := ↑(s.val/2^d)
def join (s : Reg d × Reg (b-d)) : Reg b := ↑(s.1.val+2^d*s.2.val)

def strip (e : d≤b) : Reg b ≃ Reg d × Reg (b-d) :=
  have hp : (2:ℕ)^b=2^(b-d)*2^d := by rw [← pow_add,Nat.sub_add_cancel e]
  { toFun := fun v=>(lo d v, hi d v)
    invFun := join
    left_inv := by
      intro v
      dsimp only [lo,hi,join]
      have hg : v.val/2^d < 2^(b-d) :=
         (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [← hp]; exact v.val_lt)
      simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hg, Nat.mod_add_div,ZMod.natCast_zmod_val]
    right_inv := by
      intro v
      have hv : v.1.val < 2^d := v.1.val_lt
      have he : v.2.val<2^(b-d) := v.2.val_lt
      have hg : v.1.val+2^d*v.2.val<2^b := by rw [hp]; nlinarith
      dsimp only [lo,hi,join]
      simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hg]
      rw [Nat.add_mul_div_left _ _ (pow_pos (by omega) _),Nat.div_eq_of_lt hv,Nat.zero_add,
         ZMod.natCast_zmod_val,Nat.cast_add,Nat.cast_mul,
         show ((↑(2^d:ℕ) : Reg d))=0 from ZMod.natCast_self _,zero_mul,add_zero,
         ZMod.natCast_zmod_val] }

private def par {α β γ : Type} (e : α ≃ β × γ) :
    (α × α) ≃ (β × β) × (γ × γ) :=
  (Equiv.prodCongr e e).trans (Equiv.prodProdProdComm _ _ _ _)

def splitBits (e : d≤b) : Salt b ≃ Salt d × Salt (b-d) := par (par (strip e))

set_option synthInstance.maxSize 1024
theorem fst_split (e:d≤b) (v : Salt b) :
    (splitBits e v).1=vmap (lo d) v := rfl
theorem snd_split (e:d≤b) (v : Salt b) :
    (splitBits e v).2=vmap (hi d) v := rfl

end Salt

/-- Canonical roles: X,Y,Z, then raw (unreduced) salt bits. -/
abbrev Env (n w : ℕ) := Channel n × Channel n × Channel n × Salt w

namespace Env

variable {n w d : ℕ} [Fact n.Prime]
abbrev Slice (n k j d : ℕ) := pc n k × pc n j × Channel n × Salt d

def inward (k j : ℕ) (x y : ZMod n) (s : Env n w) : Slice n k j w :=
    (closeP k x s.1, closeP j y s.2.1,s.2.2)
def outward (k j : ℕ) (x y : ZMod n) (s : Slice n k j w) : Env n w :=
    (openP k x s.1,openP j y s.2.1,s.2.2)

abbrev mask (k j : ℕ) (x y : ZMod n) (s : Env n w) :=
    hit k x s.1 ∧ hit j y s.2.1

theorem inverse1 (k j) (x y : ZMod n) (s : Env n w) (h : mask k j x y s) :
    outward k j x y (inward k j x y s)=s := by simp [outward,inward,open_close _ _ _ h.1,open_close _ _ _ h.2]
theorem inverse2 (k j) (x y : ZMod n) (s : Slice n k j w) :
    inward k j x y (outward k j x y s)=s := by simp [outward,inward,close_open]
theorem hits (k j) (x y : ZMod n) (s : Slice n k j w) :
    mask k j x y (outward k j x y s) := ⟨hit_open ..,hit_open ..⟩

def cond (k j : ℕ) (x y : ZMod n) (f : Env n w → ℝ) :=
    av (fun s=> f (outward k j x y s))

theorem two_cond (k j : ℕ) (x y : ZMod n) (f : Env n w → ℝ) :
    av (fun s=> if mask k j x y s then f s else 0) =
        pct n k * pct n j * cond k j x y f := by
  let h (v w : Channel n) := av fun t : Channel n × Salt _ => f (v,w,t)
  have he (v : Channel n) :
      av (fun a : Channel n × Channel n × Salt w =>
        if mask k j x y (v,a) then f (v,a) else 0)
       = if hit k x v then pct n j*atP j y (h v) else 0 := by
    cases em : decide (hit k x v)
    · have h : ¬hit k x v := decide_eq_false_iff_not.mp em
      simp [mask,h,av_zero]
    have hx : hit k x v := of_decide_eq_true em
    simp only [mask, hx,true_and,ite_true]
    rw [av_prod,← conditionP j y (h v)]
    congr 1
    ext i
    by_cases e : hit j y i
    · simp [e,h]
    · simp [e,av_zero]
  rw [av_prod]
  change av (fun a=> av (fun b=> if mask k j x y (a,b) then f (a,b) else 0)) = _
  simp_rw [he]
  rw [conditionP]
  unfold atP cond
  rw [av_cmul, mul_assoc,av_prod]
  unfold outward h
  simp only [av_prod]

def subSalt {k j : ℕ} (e : d≤w) : Slice n k j w ≃ Slice n k j d × Salt (w-d) :=
    let t := Salt.splitBits e
    { toFun := fun ⟨a,b,c,v⟩=> ((a,b,c,(t v).1),(t v).2)
      invFun := fun ⟨⟨a,b,c,v⟩,u⟩=> (a,b,c,t.symm (v,u))
      left_inv := by rintro ⟨a,b,c,v⟩; simp
      right_inv := by rintro ⟨⟨a,b,c,v⟩,u⟩; simp }

def panel (k j : ℕ) (x y : ZMod n) (e : d≤w) (z : Salt (w-d)) (f : Env n w → ℝ) :
    Slice n k j d → ℝ :=
   fun s=>f (outward k j x y ((subSalt e).symm (s,z)))

lemma mean_panel (k j) (x y : ZMod n) (e : d≤w) (f : Env n w → ℝ) :
    av (fun z=> av (panel k j x y e z f))=cond k j x y f := by
  unfold panel
  rw [av_swap,← av_prod (fun p=>f (outward k j x y ((subSalt e).symm p)))]
  exact av_equiv (subSalt e).symm (fun s=>f (outward k j x y s))

end Env
end
end ExactDerandomization.Analysis

end

section

set_option synthInstance.maxSize 2048
namespace ExactDerandomization.Analysis
noncomputable section
open Square _root_.OAI.ExactDerandomization.Analysis.Affine Finset

def unionG {α β γ δ : Type} (f : Family γ α) (g : Family δ β) :
    Family (γ⊕δ) (α × β) :=
  Sum.elim (fun i=> Equiv.prodCongr (f i) (Equiv.refl β))
           (fun i=> Equiv.prodCongr (Equiv.refl α) (g i))

lemma expands_product {α β γ δ : Type}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [Fintype γ] [Fintype δ]
    {f : Family γ α} {g : Family δ β} {C : ℝ}
    (hf : expands f C) (hg : expands g C) (hC : 0≤C) :
    expands (unionG f g) C := by
  intro w
  rw [var2_prod,energies,Fintype.sum_sum_type,mul_add,add_comm]
  apply add_le_add
  · refine le_trans (hf _) (mul_le_mul_of_nonneg_left ?_ hC)
    unfold energies
    exact sum_le_sum fun i _=> energy_project w (f i) (Equiv.refl β)
  · let v (i : α) (j) := w (i,j)
    have he := av_mono (f:=fun i=>var2 (v i)) (g:=fun i=>C*energies g (v i)) (fun i=>hg _)
    simp only [energies,av_cmul,av_sum] at he
    refine he.trans (le_of_eq ?_)
    congr 1
    apply sum_congr rfl
    intro i _
    unfold energy
    rw [av_prod]
    rfl

lemma nonneg_en {α γ : Type} [Fintype α] [Fintype γ] (g : Family γ α) (f) :
    0 ≤ energies g f :=
  sum_nonneg fun _ _=>av_nonneg _ fun _=>sq_nonneg _

namespace Env
variable {n w d : ℕ} [Fact n.Prime]

abbrev Choice := Gen ⊕ Gen ⊕ Gen ⊕ Gen
abbrev Atom := Bool × Choice
abbrev Roller := Wrap.W

def mixP (k j : ℕ) : Family Choice (Slice n k j d) :=
    unionG (gens (side n k)) (unionG (gens (side n j)) (unionG
      (gens n) (act true)))

lemma full_gap (k j : ℕ) :
    expands (mixP k j : Family Choice (Slice n k j d)) (10*gap0) := by
  have hh : 0≤gap0 := by linarith [gapFuel_pos]
  refine expands_product (slice_gap _) (expands_product (slice_gap _)
       (expands_product (slice_gap _) ?_ (by positivity)) (by positivity)) (by positivity)
  intro f
  have H := bits_gap (2^d) f
  have hg : 0≤energies (act true) f := nonneg_en _ _
  exact le_trans H (mul_le_mul_of_nonneg_right (by linarith) hg)

def rolling (e : d≤w) (i : Gen) : Equiv.Perm (Salt w) :=
  let eq := Salt.splitBits e
  (eq.trans (Equiv.prodCongr (act true i) (Equiv.refl _))).trans eq.symm

def rollG (k j : ℕ) (e : d≤w) (v : Roller) : Family Choice (Env n w) :=
   unionG (fun i=> Wrap.Variant k i v) (unionG (fun i=> Wrap.Variant j i v)
      (unionG (gens n) (rolling e)))

def rol (k j : ℕ) (e : d≤w) (a : Atom) (v : Roller) :
    Equiv.Perm (Env n w) :=
    if a.1 then rollG k j e v a.2 else Equiv.refl _

def winner (k j : ℕ) (x y : ZMod n) (a : Atom) (s : Env n w) : Roller :=
   if a.1 then match a.2 with
     | Sum.inl i => Wrap.guessP k i (closeP k x s.1)
     | Sum.inr (Sum.inl i) => Wrap.guessP j i (closeP j y s.2.1)
     | _ => 0
   else 0

def fullact (k j : ℕ) (a : Atom) : Equiv.Perm (Slice n k j d) :=
    if a.1 then mixP k j a.2 else Equiv.refl _

def exportP (k j : ℕ) (x y : ZMod n) (e : d≤w) (z : Salt (w-d)) (s : Slice n k j d) :=
    outward k j x y ((subSalt e).symm (s,z))

theorem winner_roll (k j : ℕ) (x y : ZMod n) (e : d≤w) (z : Salt (w-d)) (s : Slice n k j d)
    (a : Atom) :
    let o := exportP k j x y e z
    rol k j e a (winner k j x y a (o s)) (o s) = o (fullact k j a s) := by
  rcases a with ⟨b, i|i|i|i⟩ <;> cases b <;>
    rcases s with ⟨s1,s2,s3,s4⟩ <;>
    simp [rol,rollG,winner,exportP,outward,unionG,subSalt,mixP,fullact,
        Wrap.variant_pin,close_open,rolling]

def weight := (↑(Fintype.card Atom) : ℝ)⁻¹

omit [Fact (Nat.Prime n)] in
lemma atom_mix (k j : ℕ) (f : Slice n k j d → ℝ) (s) :
    lazyK (mixP k j) f s= weight*∑ a:Atom,f (fullact k j a s) := by
   have he (f:Atom→ℝ) : weight*∑ a,f a=av f := by unfold weight av avs; simp [div_eq_mul_inv]; ring
   rw [he,av_prod,av_swap]
   unfold lazyK fullact
   congr 1
   funext i
   simp [av,avs]

abbrev Paths (α : Type) : ℕ → Type
 | 0 => Unit
 | d+1 => α × Paths α d
instance pathFin (α) [Fintype α] (d) : Fintype (Paths α d) :=
  match d with
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => letI : Fintype (Paths α k) := pathFin α k; inferInstanceAs (Fintype (α × Paths α k))

def go (k j : ℕ) (e : d≤w) :
      {l : ℕ}→Paths Atom l → Paths Roller l → Equiv.Perm (Env n w)
 | 0,_,_=> Equiv.refl _
 | _+1,(a,s),(v,t)=> (rol k j e a v).trans (go k j e s t)

def live (k j : ℕ) (x y : ZMod n) (e : d≤w) :
      {l : ℕ}→ Paths Atom l → Paths Roller l → Env n w → Bool
 | 0,_,_,_=>true
 | _+1,(a,s),(v,t),u=>
    if v=winner k j x y a u then live k j x y e s t (rol k j e a v u)
    else false

theorem ok_dest (k j : ℕ) (x y : ZMod n) (e : d≤w) {l:ℕ} (p : Paths Atom l) (r : Paths Roller l)
     {s : Env n w} (h : mask k j x y s) (hl : live k j x y e p r s=true) :
     mask k j x y (go k j e p r s) := by
   induction l generalizing s with
   | zero=> exact h
   | succ l ih=>
     rcases p with ⟨a,p⟩; rcases r with ⟨v,r⟩
     rw [live] at hl; split at hl
     · next he=>
        apply ih p r _ hl
        let o := subSalt (n:=n) (k:=k) (j:=j) e
        let v' := inward k j x y s
        have hh : exportP k j x y e (o v').2 (o v').1=s := by
          simp [o,exportP,v',inverse1 _ _ _ _ s h]
        change mask _ _ _ _ (rol k j _ a v s)
        rw [he,← hh,winner_roll]
        exact hits _ _ _ _ _
     · simp at hl

def sampling (k j : ℕ) (x y : ZMod n) (e : d ≤ w) (l : ℕ)
    (f : Env n w → ℝ) (s : Env n w) : ℝ :=
   ∑ p : Paths Atom l, ∑ r : Paths Roller l,
      if live k j x y e p r s then weight^l * f (go k j e p r s) else 0

lemma pathZero (α : Type) [Fintype α] (f : Paths α 0→ℝ) :
    ∑ a,f a = f () := by change ∑ a:Unit,f a= _; simp

lemma pathFold (α : Type) [Fintype α] (l) (f : Paths α (l+1)→ℝ) :
    ∑ a,f a = ∑ a:α,∑ b:Paths α l,f (a,b) := Fintype.sum_prod_type _

lemma sampler_identity (k j : ℕ) (x y : ZMod n) (e : d ≤ w) (z : Salt (w-d)) (l : ℕ)
    (f : Env n w → ℝ) (s : Slice n k j d) :
    sampling k j x y e l f (exportP k j x y e z s) =
       walk (mixP k j) (panel k j x y e z f) l s := by
  induction l generalizing s with
  | zero =>
    simp [sampling,walk,go,live,exportP,panel]
  | succ l ih =>
    let o := exportP k j x y e z
    unfold sampling
    rw [walk,atom_mix,mul_sum,pathFold]
    apply sum_congr rfl; intro a _
    simp_rw [pathFold Roller]
    rw [sum_comm]
    let b := winner k j x y a (o s)
    have he (p : Paths Atom l) (v : Paths Roller l) :
       (if live k j x y e (l:=l+1) (a,p) (b,v) (o s) then
          weight^(l+1) * f (go k j e (l:=l+1) (a,p) (b,v) (o s)) else 0) =
       weight * (if live k j x y e p v (o (fullact k j a s)) then
          weight^l*f (go k j e p v (o (fullact k j a s))) else 0) := by
      have hg : rol k j e a b (o s)=o (fullact k j a s) := winner_roll ..
      rw [live,ite_eq_left rfl,go,Equiv.trans_apply,hg]
      split; rw [pow_succ',mul_assoc]; rw [mul_zero]
    rw [Finset.sum_eq_single b]
    · rw [← ih]
      simp only [sampling, mul_sum]
      exact sum_congr rfl (fun p _ => sum_congr rfl (fun v _=> he p v))
    · intro v _ h
      have hv : v ≠ winner k j x y a (exportP k j x y e z s) := h
      simp [live,hv]
    · simp

/-- Kernel contraction for this sampling definition. Handles high salt
bits z held fixed; target here is the mean in that panel. -/
lemma sampler_est (k j : ℕ) (x y : ZMod n) (e : d≤w) (z : Salt (w-d)) (l : ℕ)
    (f : Env n w → ℝ) :
    let o := exportP k j x y e z
    let g := panel k j x y e z f
    mass4 (fun s=>sampling k j x y e l f (o s) - av g) ≤
        (1-loss Choice (10*gap0))^l * (16*mass4 g) := by
  simp only [sampler_identity]
  exact walk_mix (by linarith [gapFuel_pos]) (full_gap k j) _ _

end Env
end
end ExactDerandomization.Analysis

end

section

namespace ExactDerandomization.Analysis
noncomputable section
variable {α : Type}

lemma difference_L (u : Meter α) (f g : α → ℝ) :
    |u.L f-u.L g| ≤ u.L (fun i=>f i-g i) := by
  have H (f g : α→ℝ) : u.L f≤u.L g + u.L (fun i=>f i-g i) := by
    have ht:=u.mink g (fun i=>f i-g i)
    simp_all
  have ht:u.L (fun i=>g i-f i)=u.L (fun i=>f i-g i) := by
    convert u.Lneg (fun i=>f i-g i) using 2; ext i; simp
  obtain h:= H f g
  obtain h':=H g f
  rw [abs_le]
  constructor <;> linarith

lemma integralRoot (u : Meter α) (f : α → ℝ) (h : ∀ i,0≤f i) :
    fourth (u.I f)=u.L (fun i=>fourth (f i)) := by
  simp [Meter.L,Meter.m4,fourth_four (h _)]

lemma mixtures (u : Meter α) (f g : α→ℝ) (h:∀ i,0≤f i) (e:∀ i,0≤g i) :
    (fourth (u.I f)-fourth (u.I g))^4 ≤
                    u.I (fun i=>(fourth (f i)-fourth (g i))^4) := by
   rw [integralRoot u f h,integralRoot u g e]
   let f' := fun i=>fourth (f i)
   let g' := fun i=>fourth (g i)
   have he := difference_L u f' g'
   have ht := pow_le_pow_left₀ (abs_nonneg _) he 4
   rw [Meter.abs4,u.L4] at ht
   exact ht

abbrev rel (x d : ℝ) := min 1 (|x| / (1+d))

lemma four_distance {x y C : ℝ} (h:0≤x) (e:0≤y) (hx:x≤C) (hy:y≤C) :
    |x^4-y^4|≤4*C^3* |x-y| := by
  rw [show x^4-y^4=(x-y)*(x^3+x^2*y+x*y^2+y^3) by ring,abs_mul,
     abs_of_nonneg (show 0≤x^3+x^2*y+x*y^2+y^3 by positivity)]
  have hh : x^3+x^2*y+x*y^2+y^3≤4*C^3 := by
    calc _ ≤ C^3+C^2*C+C*C^2+C^3 := by gcongr; linarith
         _ = _ := by ring
  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (x-y))]
lemma ordinary {s t u : ℝ} (h : 0 ≤ s) (e : 0≤t) (hs:fourth s ≤ u) (ht:fourth t ≤ u) :
    |s-t| ≤ 4*u^3 * |fourth s-fourth t| := by
  convert four_distance (fourth_nn s) (fourth_nn t) hs ht using 2; rw [fourth_four h,fourth_four e]
lemma fidelity {s t u C : ℝ} (h : 0 ≤ s) (e : 0≤t) (g:0≤u) (he:s≤C*u) (hc:1≤C) :
    rel (s-t) u ≤32*C * |fourth s-fourth t| := by
  let v:=fourth s
  let w:=fourth t
  let x:=max 1 v
  have hx: 1≤x:=le_max_left ..
  have hv:=fourth_nn s; change 0≤v at hv
  have hw: v≤x:=le_max_right ..
  rcases le_total 1 |v-w| with h1|h1
  · exact le_trans (min_le_left ..) (show 1≤32*C * |v-w| by nlinarith)
  · have hj : w ≤ 2*x:= by rw [abs_le] at h1; linarith [h1.1]
    have hl : x^3≤C*(1+u) := by
      rcases le_total v 1 with h2|h2
      · rw [show x=1 from max_eq_left h2]
        nlinarith
      · rw [show x=v from max_eq_right h2]
        have ht : v^3 ≤ v^4:= by exact pow_le_pow_right₀ h2 (by omega)
        have hk:v^4=s:=fourth_four h
        nlinarith
    have hp : 0<1+u:=by linarith
    have he := ordinary h e (show v≤2*x by linarith) hj
    refine le_trans (min_le_right ..) ((div_le_iff₀ hp).mpr ?_)
    change |s - t|≤32*C * |v-w| * (1+u)
    nlinarith [mul_le_mul_of_nonneg_right hl (abs_nonneg (v-w))]

end
end ExactDerandomization.Analysis

end

end OAI
