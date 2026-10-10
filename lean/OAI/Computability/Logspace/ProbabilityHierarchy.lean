import OAI.Computability.Logspace.AffineSampling

namespace OAI

/-!
Strictly forward substochastic matrices and the hierarchy of probability rewards.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! The exact hierarchy. Nat IDs, ordered (strictly forward). -/
namespace ExactDerandomization
noncomputable section
open Finset Analysis
namespace Hie

abbrev Domain := Finset ℕ
abbrev Vec := ℕ → ℝ
abbrev Mat := ℕ → Vec
def mv (S : Domain) (C : Mat) (v : Vec) : Vec := fun x=> ∑ y∈S,C x y*v y
def mm (S : Domain) (C D : Mat) : Mat := fun x y=> ∑ z∈S,C x z * D z y
def wt (S : Domain) (C : Mat) x := ∑ y∈S, C x y

def nodes (S : Domain) (C : Mat) :=
  S.filter fun x=> ∃ y∈S, 0<C x y ∨ 0<C y x

/-- support restricted to active set S' -/
structure SB (S S' : Domain) (f : ℝ) (k : ℝ) (C : Mat) : Prop where
 nn : ∀ x y, 0≤ C x y
 key : ∀ x y, C x y≤k*f
 row : ∀ x, wt S C x ≤ k
 loc : ∀ x y, 0<C x y → x∈S' ∧ y∈S' ∧ x<y

abbrev Step (S) (f) (C) := SB S S f 1 C

lemma wt_mm (S : Domain) (C D : Mat) (x) :
    wt S (mm S C D) x = ∑ y∈S, C x y * wt S D y := by
  simp_rw [wt,mm,mul_sum]
  rw [sum_comm]

lemma mm_mv (S:Domain) (C D : Mat) (f : Vec) :
    mv S (mm S C D) f=mv S C (mv S D f) := by
  ext x; simp only [mv,mm,sum_mul,mul_sum,mul_assoc]; rw [sum_comm]

lemma restrict {S S' : Domain} {f k C} (h : SB S S f k C)
    (e : nodes S C ⊆ S') : SB S S' f k C :=
   ⟨h.nn,h.key,h.row,fun x y hk=>by
     obtain ⟨hx,hy,hz⟩ := h.loc x y hk
     exact ⟨e (mem_filter.2 ⟨hx,y,hy,Or.inl hk⟩),
            e (mem_filter.2 ⟨hy,x,hx,Or.inr hk⟩),hz⟩⟩

lemma relax {S S' S'' : Domain} {f k C} (h : SB S S' f k C) (e : S'⊆ S'') :
    SB S S'' f k C := by
  refine ⟨h.nn,h.key,h.row,fun x y hk=>?_⟩
  obtain ⟨hx,hy,hz⟩ := h.loc x y hk
  exact ⟨e hx,e hy,hz⟩

def zero : Mat := fun _ _=>0
lemma sb0 (S S' f) : SB S S' f 0 zero := by
  constructor <;> simp [wt,zero]

def combine (S : Domain) (C F : Mat) := C+mm S F C

lemma data_bounds {S S' f k C F} (h : SB S S' f 1 C) (e : SB S S' f k F)
    (hf:0<f) : SB S S' f (k+1) (combine S C F) := by
  have h0 (x y) : 0≤ mm S F C x y :=
    sum_nonneg (fun z _=> mul_nonneg (e.nn x z) (h.nn z y))
  constructor
  · intro x y; exact add_nonneg (h.nn x y) (h0 x y)
  · intro x y
    have hee : mm S F C x y ≤ wt S F x *f := by
       unfold wt mm; rw [sum_mul]
       exact sum_le_sum fun z _=>mul_le_mul_of_nonneg_left
                     (by simpa using h.key z y) (e.nn x z)
    have ht := e.row x
    change C x y+mm S F C x y≤_
    nlinarith [h.key x y]
  · intro x
    have hz : wt S (mm S F C) x ≤ wt S F x := by
      rw [wt_mm]; unfold wt
      apply sum_le_sum
      intro y _
      exact (mul_le_mul_of_nonneg_left (h.row y) (e.nn x y)).trans_eq (by simp)
    simp only [wt,combine,Pi.add_apply, sum_add_distrib]
    change wt S C x+wt S (mm S F C) x ≤ _
    linarith [h.row x,e.row x]
  · intro x y he
    by_cases hx: 0<C x y
    · exact h.loc x y hx
    change 0<C x y+_ at he
    have hp : 0 < mm S F C x y := by linarith
    obtain ⟨z,hz,ht⟩ : ∃ z∈S, 0<F x z*C z y := by
      by_contra! hn
      exact (not_lt_of_ge (show mm S F C x y≤0 from sum_nonpos hn)) hp
    have hs := (mul_pos_iff.mp ht).resolve_right (by have:=h.nn z y; grind)
    obtain ⟨h1,h2,h3⟩ := h.loc z y hs.2
    obtain ⟨h4,h5,h6⟩ := e.loc x z hs.1
    exact ⟨h4,h2,h6.trans h3⟩

abbrev A : ℝ := 1/4096
def Q := shoulder A A

def correct (f : ℝ) (G : Mat) (g : Vec) : Mat := fun x y=> f*Q (G x y/f)*g y

lemma Qnn (t) : 0≤Q t :=
    (le_max_left _ _).trans (shoulder_spec A A t (by norm_num [A])).1
lemma Qhi (t) : Q t ≤ max 0 (t-A) :=
    (shoulder_spec A A t (by norm_num [A])).2
lemma Qlo (t) : t-2*A≤Q t :=
    le_trans (b:=max 0 (t-A-A)) (by grind)
       (shoulder_spec A A t (by norm_num [A])).1
lemma Qic : Ic 5 Q := shoulder_ic A A (by norm_num [A])

lemma Fbounds {f G g} (hp : 0<f) (h : ∀ x, in01 (g x)) (x y) :
    0≤ correct f G g x y ∧
       correct f G g x y ≤ max 0 (G x y-A*f) := by
  unfold correct
  have hn := Qnn (G x y/f)
  have hk := h y
  refine ⟨mul_nonneg (mul_nonneg (le_of_lt hp) hn) hk.1,?_⟩
  have hu := mul_le_mul_of_nonneg_left hk.2
                        (show 0≤f*Q (G x y/f) by positivity)
  rw [mul_one] at hu
  have e := Qhi (G x y/f)
  have hs := mul_le_mul_of_nonneg_left e (le_of_lt hp)
  have hz : f*(G x y/f-A)=G x y-A*f := by field_simp
  rcases le_total 0 (G x y/f-A) with he|he
  · rw [max_eq_right he,hz] at hs
    exact (hu.trans hs).trans (le_max_right _ _)
  · rw [max_eq_left he,mul_zero] at hs
    exact (hu.trans hs).trans (le_max_left _ _)

lemma Fle {f G g} (hp : 0<f) (h : ∀ x,in01 (g x)) {x y} (e : 0≤G x y) :
    correct f G g x y ≤ G x y := by
  refine le_trans (Fbounds hp h x y).2 (max_le e ?_)
  have : 0 ≤ A*f := mul_nonneg (by norm_num [A]) (le_of_lt hp)
  linarith

lemma Fsb {f G g S S' k} (hp : 0<f) (h : ∀ x,in01 (g x)) (e : SB S S' f k G) :
    SB S S' f k (correct f G g) := by
  have he (x y) := Fle hp h (e.nn x y)
  exact ⟨fun x y=> (Fbounds hp h x y).1,fun x y=> le_trans (he x y) (e.key x y),
    fun x=> le_trans (sum_le_sum (fun i _=>he x i)) (e.row x),
    fun x y hh=>e.loc x y (lt_of_lt_of_le hh (he x y))⟩

lemma Fgrow {S S' f k C} {F F' g g'} (h : SB S S' f k C) (hp : 0<f)
    (e : ∀ x,0 ≤ g x) (hg : g ≤ g') (ht : F≤F') :
    correct f (combine S C F) g ≤ correct f (combine S C F') g' := by
  intro x y
  have hu : combine S C F x y≤ combine S C F' x y := by
    exact add_le_add_right (
    sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (ht x i) (h.nn i y)) _
  have he := (Qic _ _ (div_le_div_of_nonneg_right hu (le_of_lt hp))).1
  exact mul_le_mul (mul_le_mul_of_nonneg_left he (le_of_lt hp))
          (hg y) (e y) (mul_nonneg (le_of_lt hp) (Qnn _))

def adjust (S : Domain) (f : ℝ) (g : Vec) (C : Mat) : ℕ → Mat
 | 0=>zero
 | n+1=>correct f (combine S C (adjust S f g C n)) g

lemma csr {f C g S S'} (hp : 0<f) (h : ∀ x,in01 (g x)) (hc : SB S S' f 1 C) (t : ℕ) :
    SB S S' f t (adjust S f g C t) := by
  induction t with
  | zero=> simpa [adjust] using sb0 S S' f
  | succ t ih=>
    simpa [adjust] using Fsb hp h (data_bounds hc ih hp)

lemma mono_steps {f C g S S'} (hp : 0<f) (h : ∀ x,in01 (g x)) (hc : SB S S' f 1 C) :
    Monotone (adjust S f g C) := by
  apply monotone_nat_of_le_succ; intro t
  induction t with
  | zero=> exact (csr hp h hc 1).nn
  | succ t ih=> exact Fgrow hc hp (fun i=>(h i).1) le_rfl ih

def residual (S : Domain) (C F : Mat) :=
   combine S C F-F

lemma substochastic {f S C g S'} (hp : 0<f) (h : ∀ x,in01 (g x)) (hc : SB S S' f 1 C)
    (t : ℕ) :
    let F := adjust S f g C t
    SB S S' ((t+1:ℕ)*f) 1 (residual S C F) ∧
    (∀ x y, 0<F x y → A*f≤residual S C F x y) := by
  let F:=adjust S f g C t
  have he := csr hp h hc t; change SB S S' f t F at he
  have hv := data_bounds hc he hp
  let H:=combine S C F
  have hsub (x y) : F x y ≤ max 0 (H x y-A*f) := by
    have he := mono_steps hp h hc (show t≤t+1 by omega)
    exact le_trans (he x y) (Fbounds hp h x y).2
  let T:=residual S C F
  have hk (x y) : T x y=H x y-F x y := rfl
  have hm (x y) (hg:0<F x y) : A*f ≤ T x y := by
    rw [hk]; have he := hsub x y
    grind
  refine ⟨?_,hm⟩
  have hu (x y) : T x y ≤ H x y := by rw [hk]; exact sub_le_self _ (he.nn _ _)
  constructor
  · intro x y
    rcases le_total (F x y) 0 with h0|h0
    · change 0≤T x y
      have eh : 0≤H x y:=hv.nn x y
      rw [hk]; linarith
    · rcases eq_or_lt_of_le h0 with h'|h'
      · change 0≤T x y
        rw [hk,← h',sub_zero]; exact hv.nn x y
      · exact le_trans (mul_nonneg (by norm_num [A]) (le_of_lt hp)) (hm x y h')
  · intro x y
    simpa using le_trans (hu x y) (hv.key x y)
  · intro x
    have h1 : wt S (mm S F C) x≤ wt S F x := by
      rw [wt_mm]
      exact sum_le_sum fun i _=>by simpa using
          mul_le_mul_of_nonneg_left (hc.row i) (he.nn x i)
    have e : wt S T x=wt S C x+wt S (mm S F C) x-wt S F x := by
      simp [T,residual,wt,combine,sum_sub_distrib,sum_add_distrib]
    change wt S T x≤_
    rw [e]; linarith [hc.row x]
  · intro x y hi; exact hv.loc x y (lt_of_lt_of_le hi (hu x y))

end Hie
end
end ExactDerandomization

end

section

namespace ExactDerandomization
noncomputable section
namespace Hie
open Analysis Finset

abbrev diff (S : Domain) (f : ℝ) (g : Vec) (C : Mat) (n : ℕ) :=
    adjust S f g C (n+1) - adjust S f g C n

lemma transfer_diff {S f g C} (hc : Step S f C) (hf : 0<f) (hg : ∀ i,in01 (g i))
    (n x y : ℕ) : diff S f g C (n+1) x y ≤ 5 * mm S (diff S f g C n) C x y := by
  let v t := combine S C (adjust S f g C t) x y
  let h t := diff S f g C t x y
  have H : 0 ≤ mm S (diff S f g C n) C x y :=
     sum_nonneg fun i _=> mul_nonneg (sub_nonneg.2 (mono_steps hf hg hc n.le_succ x i)) (hc.nn i y)
  have hdiff : v (n+1)-v n = mm S (diff S f g C n) C x y := by
    simp only [v,diff,combine,Pi.add_apply,Pi.sub_apply,mm,sum_sub_distrib,sub_mul]
    ring
  have he : v n/f ≤ v (n+1)/f := div_le_div_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨h1,h2⟩ := Qic _ _ he
  have hu : h (n+1)=f*(Q (v (n+1)/f)-Q (v n/f))*g y := by
    change f*_ *_-f*_ *_=_; ring
  change h (n+1) ≤ _
  have hv : f*(v (n+1)/f - v n/f)=mm S (diff S f g C n) C x y := by rw [← hdiff]; field_simp
  rw [hu]
  have hh := mul_le_mul_of_nonneg_left (hg y).2
       (show 0≤f*(Q (v (n+1)/f)-Q (v n/f)) by exact mul_nonneg (le_of_lt hf) (sub_nonneg.2 h1))
  have ht := mul_le_mul_of_nonneg_left h2 (le_of_lt hf)
  linarith

def sub (S : Domain) (y : ℕ) := S.filter (fun x=>x<y)

lemma sub_choose (S : Domain) (y k : ℕ) :
    ∑ x∈sub S y, ((sub S x).card.choose k : ℝ) = ((sub S y).card.choose (k+1) : ℝ) := by
  induction y with
  | zero => simp [sub]
  | succ y ih =>
    by_cases he:y∈ S
    · have e : sub S (y+1)=insert y (sub S y) := by ext x; simp [sub]; grind
      have hu : y∉sub S y := by simp [sub]
      rw [e,sum_insert hu,ih,card_insert_of_notMem hu]
      push_cast [Nat.choose]
      ring
    · rw [show sub S (y+1)=sub S y by ext x; simp [sub]; grind]
      exact ih

lemma factorial {S f g C} (hc : Step S f C) (hf : 0<f) (hg : ∀ i,in01 (g i))
    (T x y : ℕ) : diff S f g C T x y ≤ f*((5/A)^T/T.factorial) := by
  let U t := adjust S f g C t
  let R := residual S C (U (T+1))
  let M := S.filter (fun y=>0<U (T+1) x y)
  obtain ⟨hsb,hmin⟩ := substochastic hf hg hc (T+1)
  have hcap : M.card*(A*f) ≤ (1:ℝ) := by
    calc
     (M.card:ℝ)*(A*f) = ∑ _y ∈ M, A*f := by simp
     _ ≤ ∑ i∈M, R x i := sum_le_sum fun i hi=>hmin x i (mem_filter.1 hi).2
     _ ≤ ∑ i∈S,R x i := sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun i _ _=>hsb.nn x i
     _ ≤ 1 := hsb.row x
  let D t := diff S f g C t
  have HD (t z) : 0≤D t x z := sub_nonneg.2 (mono_steps hf hg hc (Nat.le_add_right _ 1) x z)
  have E (t : ℕ) (h : t ≤ T) :
       ∀ y, D t x y ≤ f * (5*f)^t * ((sub M y).card.choose t) := by
    induction t with
    | zero =>
      have hp := (csr hf hg hc 1).key
      intro y
      simp
      simpa [D,diff,zero,adjust] using hp x y
    | succ t ih =>
      intro y
      refine le_trans (transfer_diff hc hf hg t x y) ?_
      have he : mm S (D t) C x y = ∑ i∈sub M y, D t x i*C i y := by
        have ht : sub M y ⊆ S:= fun z hz=> (mem_filter.1 (mem_filter.1 hz).1).1
        apply (sum_subset ht ?_).symm
        intro z hz hy
        by_cases H: 0<D t x z
        · have hk : 0<U (T+1) x z := by
            have ht : 0 ≤ U t x z:=(csr hf hg hc t).nn x z
            have hu : U (t+1) x z≤U (T+1) x z:=mono_steps hf hg hc (by omega) x z
            change 0<U (t+1) x z-U t x z at H
            linarith
          have hv : y≤z := by
            by_contra! hv
            exact hy (mem_filter.2 ⟨mem_filter.2 ⟨hz,hk⟩,hv⟩)
          have hs : C z y=0 := by
            by_contra e
            have hi := (hc.loc z y (lt_of_le_of_ne (hc.nn _ _) (Ne.symm e))).2.2
            omega
          simp [hs]
        · have h0 : D t x z=0:=le_antisymm (le_of_not_gt H) (HD t z)
          simp [h0]
      change 5*mm S (D t) C x y ≤ _
      rw [he,mul_sum]
      calc
       _ ≤ ∑ i∈sub M y, f*(5*f)^(t+1) * ((sub M i).card.choose t) := by
          apply sum_le_sum; intro i _
          have ht := ih (by omega) i
          rw [pow_succ]
          calc
            _ ≤ 5*(D t x i*f) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (by simpa using hc.key i y) (HD t i)) (by norm_num)
            _ ≤ 5*(f*(5*f)^t*((sub M i).card.choose t)*f) := by gcongr
            _ = _ := by ring
       _ = _ := by rw [← mul_sum,sub_choose]
  refine le_trans (E T le_rfl y) ?_
  let n : ℕ := (sub M y).card
  have he := Nat.choose_le_pow_div (α:=ℝ) T n
  have ht : 5*f*(n:ℝ) ≤ 5/A := by
    have hu : (n:ℝ) ≤ M.card := Nat.cast_le.mpr (card_le_card (filter_subset ..))
    unfold A at *; nlinarith
  change f*(5*f)^T*(n.choose T) ≤ _
  have hF := pow_le_pow_left₀ (show 0≤ 5*f*(n:ℝ) by positivity) ht T
  calc _ ≤ f*(5*f)^T*((n:ℝ)^T/T.factorial) := by gcongr
       _ = f*((5*f*(n:ℝ))^T/T.factorial) := by ring
       _ ≤ _ := by gcongr

def kOK (T : ℕ) := 0<T ∧ (5/A)^T/T.factorial ≤ (1/1024:ℝ)

lemma can_cut : ∃ T : ℕ, kOK T := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop (5/A)
  obtain ⟨b,hb⟩ := Filter.eventually_atTop.1
      (h.eventually_lt_const (show 0<(1/1024:ℝ) by norm_num))
  exact ⟨b+1,Nat.zero_lt_succ _,le_of_lt (hb _ (Nat.le_succ b))⟩

abbrev good : ℝ := 1/256
lemma good_col {S f g C T} (hc : Step S f C) (hf : 0<f) (hg : ∀ i,in01 (g i))
    (ht : kOK T) (x y : ℕ) (h : g y=1) :
    residual S C (adjust S f g C T) x y ≤ good*f := by
  let F:=adjust S f g C T
  let w:=combine S C F x y
  have he := le_trans (factorial hc hf hg T x y)
      (mul_le_mul_of_nonneg_left ht.2 (le_of_lt hf))
  change correct _ _ _ _ _-F x y ≤ _ at he
  change w-F x y≤_
  have hh := mul_le_mul_of_nonneg_left (Qlo (w/f)) (le_of_lt hf)
  change f*Q (w/f)*g y - F x y ≤ f*_ at he
  have hs : f*(w/f)=w := by field_simp
  rw [h] at he
  unfold good A at *
  linarith

/-- Unsigned terms of residual dominated by residual. -/
lemma cover {S f g C T} (hc : Step S f C) (hf : 0<f) (hg : ∀ i,in01 (g i)) (x y : ℕ) :
    let F:=adjust S f g C T
    C x y+ F x y+mm S F C x y ≤ (1+2*T/A)*residual S C F x y := by
  let F:=adjust S f g C T
  let D:=residual S C F
  change _ ≤ (1+2*T/A)*D x y
  have hu := (csr hf hg hc T).nn x y
  obtain ⟨ht,hs⟩ := substochastic hf hg hc T
  have h := ht.nn x y
  have HH : D x y=C x y+mm S F C x y-F x y:=rfl
  have hv := (csr hf hg hc T).key x y
  change 0≤F x y at hu
  rcases eq_or_lt_of_le hu with e|e
  · change 0≤ D x y at h; unfold A; nlinarith
  have he := hs x y e
  change A*f≤D x y at he
  change F x y≤ _ at hv
  unfold A at *; nlinarith

end Hie
end
end ExactDerandomization

end

section

namespace ExactDerandomization
noncomputable section
namespace Hie
open Analysis Finset

abbrev delta : ℝ := A/400
abbrev eta (z : ℝ) := z/1000

def gate (z : ℝ) (v : ℝ) := 1-rising (eta z) (2*eta z) v
def light (v : ℝ) := rising delta (2*delta) v

lemma gate_mem (z v) : in01 (gate z v) := by
  obtain ⟨h,e⟩ := rising_mem (eta z) (2*eta z) v
  unfold in01 gate; constructor <;> linarith
lemma gate_full {z : ℝ} (h:0<z) (v) (e:v≤eta z) : gate z v=1 := by
  unfold gate; rw [rising_bot _ e]; simp
  unfold eta; linarith
lemma gate_shut {z : ℝ} (h:0<z) (v) (e:2*eta z≤v) : gate z v=0 := by
  unfold gate; rw [rising_top _ e]; simp
  unfold eta; linarith

variable {n : ℕ} [Fact n.Prime]

def retain (l) (S : Domain) (s : Channel n) := S.filter fun i : ℕ=>hit l i s
def tally (l : ℕ) (S : Domain) (s : Channel n) : ℝ := (retain l S s).card
lemma tally_eq (l) (S : Domain) (s : Channel n) : tally l S s=∑ i∈S,ind l i s := by
  unfold tally retain ind
  rw [card_filter]; push_cast; rfl

abbrev legal (n) (S : Domain) := S⊆range n

lemma injNat (S : Domain) (h : legal n S) : Set.InjOn (fun i:ℕ=>(i:ZMod n)) ↑S := by
  intro i hi j hj e; have he:=congrArg ZMod.val e
  simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.1 (h hi)),
         Nat.mod_eq_of_lt (mem_range.1 (h hj))] using he

lemma tally_av (l) (S : Domain) :
    av (fun i : Channel n=> tally l S i)=S.card*pct n l := by
  simp only [tally_eq,av_sum,marginal,sum_const,nsmul_eq_mul]
lemma tally_var (l) (S:Domain) (h:legal n S) :
    var2 (fun i:Channel n=>tally l S i)≤S.card*pct n l := by
  simp only [tally_eq]; exact (count_var _ _ (injNat S h) _).2

lemma tally_cond {S: Domain} (h:legal n S) {j k : ℕ} (e : 2^k≤n)
    (x : ℕ) (hx:x<n) :
    atP j (x:ZMod n) (tally k S) ≤ 1+S.card*(32*rate k) := by
  have he (i) (hi : i∈S) :
      atP j (x:ZMod n) (ind k i)≤ 32*rate k+(if i=x then 1 else 0) := by
    rcases eq_or_ne i x with h'|h'
    · rw [h',ite_eq_left rfl]
      unfold atP
      have H : 1 ≤ 32*rate k+1 := by have:=rate_pos k; linarith
      refine le_trans (b:=av (fun _ : pc n j=>1)) (av_mono (fun i=>?_)) ?_
      · dsimp only [ind]; split <;> linarith
      rw [av_const]; exact H
    · rw [ite_eq_right h',add_zero]
      have hk : (i:ZMod n)≠x := fun he=> h' (injNat (range n) (subset_refl _) (h hi) (mem_range.2 hx) he)
      have hu := (pairMean (k:=j) (j:=k) hk).1
      linarith [(pct_bounds e).2]
  have hu := sum_le_sum (s:=S) he
  unfold atP
  simp only [tally_eq,av_sum]
  simp only [atP] at hu
  refine le_trans hu ?_
  by_cases hx:x∈S <;> simp [sum_add_distrib,hx] ; linarith

def panel_rank (S : Domain) (G : Mat) (l K x) (s : Channel n) :=
   rank (retain l S s) (fun y=>G x y / rate l) K
def throttle (S : Domain) (G : Mat) (l K x) (s : Channel n) (z : ℝ) :=
   gate z (panel_rank S G l K x s)
def cost (S : Domain) (G : Mat) (l K x : ℕ) (z : ℝ) (s : Channel n) : ℝ :=
   if throttle S G l K x s z=1 then 0 else 1

lemma gate_bound {z : ℝ} (hp:0<z) {l : ℕ} (hl : 2^l≤n)
    {K j : ℕ} {G S r} (hg : ∀ x y, 0≤G x y) (hr : ∀ x, wt S G x≤r)
    (h : legal n S) {x y : ℕ} (hy:y<n)
    (he : (1+32*r/eta z)*128 ≤ (K+1:ℝ)) :
    atP j (y:ZMod n) (cost S G l K x z) ≤ 1/128 := by
  let d := rate l
  have hd : 0<d := rate_pos _
  have hz : 0 < eta z := div_pos hp (by norm_num)
  let W := S.filter (fun i=> eta z*d<G x i)
  have hh : (W.card:ℝ)*(eta z*d)≤r := by
    refine le_trans (b:=∑ i∈W,G x i) ?_ (le_trans (b:=wt S G x) ?_ (hr x))
    · rw [← nsmul_eq_mul,← sum_const]
      exact sum_le_sum fun i hi=>le_of_lt (mem_filter.1 hi).2
    · exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun i _ _=>hg _ _
  have h1 (s : Channel n) : (↑K+1:ℝ)*cost S G l K x z s≤ tally l W s := by
    unfold cost
    split
    · unfold tally; simp
    · next e=>
      have he : eta z < panel_rank S G l K x s := lt_of_not_ge (fun h=>e (gate_full hp _ h))
      have ht := (rank_gt (le_of_lt hz)).1 he
      have hu : (((retain l S s).filter fun i=> eta z < G x i/rate l))=retain l W s := by
        ext i; simp only [retain,W,mem_filter,lt_div_iff₀ (rate_pos l),d]; tauto
      rw [hu] at ht; rw [mul_one]; unfold tally
      exact_mod_cast (show K+1≤ _ from ht)
  have h2 : (K+1:ℝ)*atP j (y:ZMod n) (cost S G l K x z)≤atP j (y:ZMod n) (tally l W) := by
    unfold atP; rw [← av_cmul]
    exact av_mono fun i=>h1 _
  have hs : atP j (y:ZMod n) (tally l W) ≤ 1+32*r/eta z := by
    refine le_trans (tally_cond (fun i hi=> h (mem_filter.1 hi).1) hl _ hy) ?_
    apply add_le_add_right
    rw [le_div_iff₀ hz]; dsimp only [d] at hh; linarith
  have hw : (0:ℝ)<K+1 := by positivity
  apply le_of_mul_le_mul_left _ hw
  linarith

end Hie
end
end ExactDerandomization

end

section

namespace ExactDerandomization
noncomputable section
namespace Hie
open Analysis Finset

variable {n : ℕ} [Fact n.Prime]

def mark (S G l K x y) (s : Channel n) :=
    light (G x y/rate l)*throttle S G l K x s delta

def score (S G l K J y) (s t : Channel n) :=
    rank (retain l S s) (fun i=> mark S G l K i y t) J

def U (n : ℕ) [Fact n.Prime] (S G) (l K J y : ℕ) :=
    atP l (↑y:ZMod n) (fun t=>av (fun s=> score S G l K J y s t))

lemma mark_mem (S G l K x y) (s : Channel n) : in01 (mark S G l K x y s) := by
  unfold mark light throttle
  obtain ⟨h,e⟩ := rising_mem delta (2*delta) (G x y/rate l)
  obtain ⟨w,v⟩ := gate_mem delta (panel_rank S G l K x s)
  exact ⟨mul_nonneg h w,(mul_le_mul e v w (zero_le_one)).trans_eq (by ring)⟩

lemma score_mem (S G l K J y) (s t : Channel n) :
    in01 (score S G l K J y s t) :=
  ⟨rank_nn _ _ _,rank_le (by norm_num) fun i _=>(mark_mem ..).2⟩

lemma expect_mem {α : Type} [Fintype α] [Nonempty α] {f : α → ℝ}
    (h : ∀ x, in01 (f x)) : in01 (av f) :=
  ⟨av_nonneg _ (fun x=>(h x).1),le_trans
    (av_mono (f:=f) (g:=fun _=>1) (fun i=>(h i).2)) (le_of_eq (av_const _))⟩
lemma U_mem (S G l K J y) : in01 (U n S G l K J y) :=
    expect_mem fun _=>expect_mem fun _=>score_mem ..

lemma rfull (t) (h:2*delta ≤ t) : light t=1 := rising_top (by norm_num [delta,A]) h
lemma rzero (t) (h:t≤delta) : light t=0 := rising_bot (by norm_num [delta,A]) h

def rowhi (S : Domain) (G : Mat) l y :=
    S.filter fun i=> 2*delta*rate l ≤ G i y
def rowlo (S : Domain) (G : Mat) l y :=
    S.filter fun i=> delta*rate l < G i y

lemma U_light (l K J y : ℕ) (S G) :
    (J+1:ℝ)*U n S G l K J y ≤ (rowlo S G l y).card*pct n l := by
  have he (s t : Channel n) :
      (J+1:ℝ)*score S G l K J y s t ≤ tally l (rowlo S G l y) s := by
    let f := score S G l K J y s t
    change _*f ≤ _
    obtain ⟨h1,h2⟩ := score_mem S G l K J y s t
    change _ ≤ f at h1; change f ≤ _ at h2
    rcases h1.eq_or_lt with e|e
    · rw [← e]; unfold tally; simp
    have hi := rank_gt (s:=retain l S s) (f:=fun i=>mark S G l K i y t)
                    (le_refl (0:ℝ))|>.1 e
    have ht : J<(retain l (rowlo S G l y) s).card := by
      apply lt_of_lt_of_le hi (card_le_card ?_)
      intro i he
      simp only [retain,rowlo,mem_filter] at *
      refine ⟨⟨he.1.1,?_⟩,he.1.2⟩
      by_contra! h
      have hk : light (G i y/rate l)=0 := rzero _ ((div_le_iff₀ (rate_pos l)).mpr h)
      have hh := he.2
      simp [mark,hk] at hh
    have hh : (J+1:ℝ) ≤ tally l (rowlo S G l y) s := by
      unfold tally; exact_mod_cast ht
    nlinarith
  dsimp only [U,atP]
  rw [← av_cmul]
  have hk : ∀ (t:Channel n),
       (J+1:ℝ)*av (fun s=>score S G l K J y s t) ≤ (rowlo S G l y).card*pct n l := by
    intro t; rw [← av_cmul,← tally_av]
    exact av_mono fun i=>he i t
  exact le_trans (av_mono (f:=_) (g:=fun (_:pc n l)=> (rowlo S G l y).card*pct n l)
                  (fun i=>hk _)) (le_of_eq (av_const _))

/-- A threshold usable for incoming normalization. -/
abbrev limitJ (J : ℕ) := 128 + 4*(J+1:ℝ)

lemma U_heavy {S S' G k l} (he:legal n S) (hr : SB S S' (rate l) k G) (hl : 2^l ≤ n)
    (K J y : ℕ) (hy:y∈S)
    (hK : (1+32*k / eta delta)*128≤(K+1:ℝ))
    (hJ : limitJ J ≤ (rowhi S G l y).card*rate l) :
    (9/10 : ℝ) ≤ U n S G l K J y := by
  let W:=rowhi S G l y
  let z i (t:pc n l) := cost S G l K i delta (openP l (y:ZMod n) t)
  let T (s:Channel n) := tally l W s
  let m:= (W.card:ℝ)*pct n l
  have hu : limitJ J ≤ m := le_trans hJ
           (mul_le_mul_of_nonneg_left (pct_bounds hl).1 (Nat.cast_nonneg _))
  have hm : 128 ≤ m := by unfold limitJ at hu; linarith
  have hm0 : 0 < m := by linarith
  let loss (s:Channel n) (t : pc n l) := ∑ i∈retain l W s,z i t
  let v s t := score S G l K J y s (openP l (y:ZMod n) t)
  have hh (s : Channel n) t :
      m^2*(1-v s t) ≤ 4*(T s-m)^2 + 4*m*loss s t := by
    let B:=retain l W s
    let S0 := B.filter fun i=> throttle S G l K i (openP l (y:ZMod n) t) delta=1
    have e : loss s t=T s - S0.card := by
      have he (i) : z i t=1-(if throttle S G l K i (openP l (y:ZMod n) t) delta=1 then 1 else 0) := by
        dsimp [z,cost]; split <;> norm_num
      simp only [loss,T,tally, S0,B, he,card_filter,sum_sub_distrib,sum_const,nsmul_eq_mul, mul_one]
      push_cast; rfl
    have h1 : 0 ≤ v s t := (score_mem ..).1
    have h2 : 0 ≤ loss s t := sum_nonneg fun i _=>by unfold z cost; split <;> norm_num
    by_cases ht : T s < m/2
    · nlinarith [sq_nonneg m,mul_nonneg (sq_nonneg m) h1]
    by_cases hv : m/4 < loss s t
    · nlinarith [sq_nonneg (T s-m),mul_nonneg (sq_nonneg m) h1]
    have ha : 1 ≤ v s t := by
      have hg : J<S0.card := by
        have hk : (J:ℝ)< S0.card := by unfold limitJ at hu; linarith
        exact_mod_cast hk
      apply (rank_ge (s:=retain l S s) (f:=fun i=>mark S G l K i y (openP l (y:ZMod n) t))
                (show (0:ℝ)<1 by norm_num)).2 (lt_of_lt_of_le hg (card_le_card ?_))
      intro i hi
      simp only [retain,S0,B,W,rowhi,mark,mem_filter] at *
      obtain ⟨⟨⟨h,k⟩,ha⟩,he⟩ := hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨h, ha⟩, ?_⟩
      rw [he, rfull _ ((le_div_iff₀ (rate_pos l)).2 k),mul_one]
    nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg m),sq_nonneg (T s-m)]
  have hc : U n S G l K J y=av (fun t=> av (fun s=>v s t)) := rfl
  have ht : av T=m := tally_av ..
  have hv2 : av (fun s=>(T s -m)^2) ≤ m := by
    rw [← ht]
    exact le_trans (tally_var l W (fun i e=>he (mem_filter.1 e).1)) (le_of_eq ht.symm)
  have hz : av (fun t=>av fun s=> loss s t) ≤ m/128 := by
    rw [av_swap]
    have e1 (s) : av (loss s) ≤ T s /128 := by
      have hh (i) : av (z i) ≤ 1/128 := gate_bound (by norm_num [delta,A])
         hl hr.nn hr.row he (mem_range.1 (he hy)) hK
      unfold loss
      rw [av_sum]
      refine le_trans (sum_le_sum (fun i _=>hh i)) (le_of_eq ?_)
      simp [T,tally]; ring
    rw [← ht,← av_div]
    exact av_mono (fun s=>e1 s)
  have H : av (fun t=>av fun s=>m^2*(1-v s t)) ≤
      av (fun t=>av fun s=>4*(T s-m)^2+4*m*loss s t) :=
      av_mono fun t=>av_mono fun s=>hh s t
  simp only [av_cmul,av_add,av_sub,av_const] at H
  rw [hc]
  by_contra! ht
  set V := av (fun t=> av (fun s=>v s t))
  have hg : m*m*(1-V) ≤4*m+4*m*(m/128) := by
    nlinarith [mul_le_mul_of_nonneg_left hz (show 0≤4*m by positivity)]
  nlinarith [mul_pos (show 0<(9/10-V) by linarith)
                           (show 0 < m^2 by positivity)]

end Hie
end
end ExactDerandomization

end

section

namespace ExactDerandomization
noncomputable section
namespace Hie
open Analysis Finset

structure Const where
  T : ℕ
  K : ℕ
  J : ℕ
  M : ℕ
  tOK : kOK T
  KOK : (1+32*(T+1)/eta delta)*128 ≤ (K+1:ℝ)
  mOK : 16*(T+1)<M
  jOK : 64*M*(T+1:ℝ)^2 ≤ delta*(J+1)

lemma exists_const : Nonempty Const := by
  obtain ⟨T,hT⟩ := can_cut
  let M := 16*(T+1)+1
  obtain ⟨K,hK⟩ := exists_nat_ge ((1+32*(T+1)/eta delta)*128)
  obtain ⟨J,hJ⟩ := exists_nat_ge (64*M*(T+1:ℝ)^2/delta)
  refine ⟨⟨T,K,J,M,hT,by linarith,Nat.lt_succ_self _,?_⟩⟩
  unfold delta A at *; linarith

structure Pilot where
  V : Vec
  E : Mat

variable (n : ℕ) [Fact n.Prime]

def gamma (x : ℝ) := 1-rising (1/2) (4/5) x
lemma gamma_mem (t) : in01 (gamma t) := by
  obtain ⟨e,h⟩ := rising_mem (1/2) (4/5) t
  unfold in01 gamma; constructor <;> linarith
lemma gamma_anti : Antitone gamma := by
  intro x y h; have e := (rising_ic (a:=1/2) (b:=4/5) (by norm_num)) x y h
  unfold gamma; linarith [e.1]
lemma gamma_full {x} (h:x≤1/2) : gamma x=1 := by rw [gamma,rising_bot (by norm_num) h]; simp
lemma gamma_stop {x} (h:4/5≤x) : gamma x=0 := by rw [gamma,rising_top (by norm_num) h]; simp

structure Stg where
  p : Const
  i : ℕ
  S : Domain
  C : Mat

namespace Stg
variable {n} (P : Stg)

abbrev f := rate P.i

variable (n)
def update (w : Pilot) : Pilot :=
  let G:=combine P.S P.C w.E
  let v x:= max (w.V x) (U n P.S G P.i P.p.K P.p.J x)
  ⟨v,correct P.f G (fun x=> gamma (v x))⟩

def pilots : ℕ → Pilot
 | 0 => ⟨fun _=>0,zero⟩
 | k+1 => P.update n (pilots k)

def testG (k : ℕ) := combine P.S P.C (P.pilots n k).E
def testU (k) (x) := U n P.S (P.testG n k) P.i P.p.K P.p.J x
def probed (k : ℕ) := (P.pilots n k).V
def gm (k : ℕ) := fun x => gamma (P.probed n k x)
def corr (k) := adjust P.S P.f (P.gm n P.p.T) P.C k
def nextG (k) := combine P.S P.C (P.corr n k)
def D := residual P.S P.C (P.corr n P.p.T)

theorem V_recur (k x) :
    P.probed n (k+1) x = max (P.probed n k x) (P.testU n k x) := rfl
lemma V_mem (k x) : in01 (P.probed n k x) := by
  induction k with
  | zero=> change in01 0; unfold in01; norm_num
  | succ k ih=>
    obtain ⟨e,h⟩ := ih
    have hk : in01 (P.testU n k x):=U_mem ..
    rw [V_recur]; unfold in01 at *; grind

lemma V_mono : Monotone (P.probed n) := by
  apply monotone_nat_of_le_succ; intro k x
  rw [V_recur]; exact le_max_left _ _
lemma prob_inc (k x) : P.probed n k x ≤ ∑ j∈range k, P.testU n j x := by
  induction k with
  | zero => simp [probed,pilots]
  | succ k ih =>
    rw [V_recur,sum_range_succ]
    have ht : 0 ≤ P.testU n k x := (U_mem ..).1
    have hs := (P.V_mem n k x).1
    grind

lemma pilot_bounds {S'} (h : SB P.S S' P.f 1 P.C) (k : ℕ) :
    SB P.S S' P.f k (P.pilots n k).E := by
  induction k with
  | zero=> simpa [pilots] using sb0 P.S S' P.f
  | succ k ih=>
    simpa only [probed,pilots,f,update,Nat.cast_add,Nat.cast_one] using
      Fsb (g:=fun x=> gamma (P.probed n (k+1) x)) (rate_pos _) (fun x=>gamma_mem _)
             (data_bounds h ih (rate_pos _))

lemma tbounds {S'} (h : SB P.S S' P.f 1 P.C) (k : ℕ) :
    SB P.S S' P.f (k+1:ℝ) (P.testG n k) :=
   data_bounds h (P.pilot_bounds n h k) (rate_pos _)
lemma cbounds {S'} (h : SB P.S S' P.f 1 P.C) (k : ℕ) :
    SB P.S S' P.f k (P.corr n k) :=
    csr (rate_pos _) (fun _=>gamma_mem _) h k

lemma cpilot {S'} (h : SB P.S S' P.f 1 P.C) {k : ℕ} (hk:k≤P.p.T) :
    P.corr n k≤ (P.pilots n k).E := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine Fgrow h (rate_pos _) (g:=P.gm n P.p.T) (g':=P.gm n (k+1)) (fun _=>(gamma_mem _).1)
                     ?_ (ih (by omega))
    exact fun x=>gamma_anti (P.V_mono n hk x)

lemma dbounds {S'} (h : SB P.S S' P.f 1 P.C) :
    SB P.S S' ((P.p.T+1:ℕ)*P.f) 1 (P.D n) :=
    (substochastic (rate_pos _) (fun _=> gamma_mem _) h P.p.T).1

lemma columns (he : legal n P.S) (h : Step P.S P.f P.C) (hl:2^P.i ≤ n)
    {k x : ℕ} (hk:k<P.p.T) (hx:x∈P.S) (hg:0<P.gm n (k+1) x) :
    (rowhi P.S (P.testG n k) P.i x).card*P.f ≤ limitJ P.p.J := by
  by_contra! e
  have hn : ((k:ℝ)+1)<=P.p.T := by exact_mod_cast (show k+1≤ P.p.T from hk)
  have hK := P.p.KOK
  have hs := U_heavy he (P.tbounds n h k) hl P.p.K P.p.J x hx (by unfold eta delta A at *; linarith) (le_of_lt e)
  have ht := le_max_right (P.probed n k x) (P.testU n k x)
  have hh : P.gm n (k+1) x=0 := by
    unfold gm; rw [V_recur,gamma_stop]
    unfold testU at ht ⊢; linarith
  linarith

lemma cols (he : legal n P.S) (h : Step P.S P.f P.C) (hl:2^P.i ≤ n)
    {k x : ℕ} (hk:k<P.p.T) (hx:x∈P.S) (hg:0<P.gm n P.p.T x) :
    (rowhi P.S (P.nextG n k) P.i x).card*P.f ≤ limitJ P.p.J := by
  have hp := P.columns n he h hl hk hx
                        (lt_of_lt_of_le hg (gamma_anti (P.V_mono n hk x)))
  have hu i j : P.nextG n k i j≤ P.testG n k i j := add_le_add_right
     (sum_le_sum fun z _=>mul_le_mul_of_nonneg_right (P.cpilot n h hk.le i z) (h.nn z j)) _
  refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card ?_))
              (le_of_lt (rate_pos _))) hp
  intro j hj; obtain ⟨e,hj⟩ := mem_filter.1 hj; exact mem_filter.2 ⟨e,hj.trans (hu ..)⟩

private lemma mark_sum (P : Stg) (n : ℕ) [Fact n.Prime]
    (h : Step P.S P.f P.C) (k : ℕ) :
    ∑ x∈P.S, ((rowlo P.S (P.testG n k) P.i x).card:ℝ) * (delta * P.f) ≤
      (nodes P.S P.C).card*((k:ℝ)+1) := by
  let A0:=nodes P.S P.C
  let G:=P.testG n k
  have he := P.tbounds n (restrict h (subset_refl A0)) k
  have hf:=rate_pos P.i
  have hu (x) : rowlo P.S G P.i x ⊆ A0 := by
    intro i hi; obtain ⟨e,hi⟩:=mem_filter.1 hi
    have ht : 0< G i x:=lt_trans (by unfold delta A; positivity) hi
    exact (he.loc i x ht).1
  calc _ ≤ ∑ x∈P.S,∑ y∈A0,G y x := by
         apply sum_le_sum; intro x hx
         refine le_trans (b:=∑ y∈rowlo P.S G P.i x,G y x) ?_ (sum_le_sum_of_subset_of_nonneg
              (hu x) fun y _ _=>he.nn y x)
         change ↑(rowlo P.S G P.i x).card*(delta*P.f) ≤ _
         rw [← nsmul_eq_mul,←sum_const]
         exact sum_le_sum fun i h=>le_of_lt (mem_filter.1 h).2
       _ ≤ _ := by
         rw [sum_comm,← nsmul_eq_mul,←sum_const]
         exact sum_le_sum fun i _=> he.row i

def active := P.S.filter fun i=>1/4<P.probed n P.p.T i
lemma rare (h : Step P.S P.f P.C) (hl : 2^P.i≤n) :
    (P.active n).card*P.p.M ≤ (nodes P.S P.C).card := by
  let U0:=nodes P.S P.C
  let T:=P.p.T
  let J:ℝ := ↑P.p.J+1
  let d:ℝ := delta*J/64
  have hd : 0 < d := by dsimp [d,J,delta,A]; positivity
  have H (x) (hx:x∈P.active n) : d ≤
       ∑ k ∈ range T, ((rowlo P.S (P.testG n k) P.i x).card:ℝ)*(delta*P.f) := by
    have hz := (mem_filter.mp hx).2
    have hu := P.prob_inc n T x
    have he (k : ℕ) : P.testU n k x*(4*d) ≤
          ((rowlo P.S (P.testG n k) P.i x).card:ℝ)*(delta*P.f) := by
      have e := U_light (n:=n) P.i P.p.K P.p.J x P.S (P.testG n k)
      have hk := mul_le_mul_of_nonneg_left (pct_bounds hl).2
          (show 0 ≤ ((rowlo P.S (P.testG n k) P.i x).card:ℝ) by positivity)
      change J*P.testU n k x ≤ _ at e
      dsimp only [d,delta,A,f]; linarith
    refine le_trans ?_ (sum_le_sum (fun k _=>he k))
    rw [← sum_mul]
    change 1/4<P.probed n T x at hz
    nlinarith
  have hv :
    ((P.active n).card:ℝ)*d ≤ (U0.card:ℝ)*(T+1:ℝ)^2 := by
    calc
      _ = ∑ x∈P.active n,d := by simp
      _ ≤ ∑ x∈P.active n,∑ k∈range T,((rowlo P.S (P.testG n k) P.i x).card:ℝ)*(delta*P.f) :=
          sum_le_sum H
      _ ≤ ∑ x∈P.S,∑ k∈range T,((rowlo P.S (P.testG n k) P.i x).card:ℝ)*(delta*P.f) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset ..)
          intro i _ _
          apply sum_nonneg; intro k _
          have he:0<P.f:=rate_pos _
          unfold delta A; positivity
      _ ≤ _ := by
          rw [sum_comm]
          refine le_trans (sum_le_sum (fun k (_:k∈range T)=>mark_sum P n h k)) ?_
          have hs := sum_le_sum (f:=fun k:ℕ=> (U0.card:ℝ)*((k:ℝ)+1))
                        (g:=fun _=>(U0.card:ℝ)*(T+1:ℝ))
                        (fun k (hk:k∈range T)=> by
                             have hv : (k:ℝ)≤T := Nat.cast_le.mpr (le_of_lt (mem_range.mp hk))
                             gcongr)
          simp only [sum_const,nsmul_eq_mul,card_range] at hs
          refine hs.trans ?_
          nlinarith [show (0:ℝ)≤U0.card by positivity]
  suffices ((P.active n).card:ℝ)*P.p.M ≤ (nodes P.S P.C).card by exact_mod_cast this
  have he := P.p.jOK
  have h' : P.p.M*((T:ℝ)+1)^2 ≤ d := by dsimp only [d,J,T]; unfold delta A at he ⊢; nlinarith
  have hz := mul_le_mul_of_nonneg_left h'
       (show (0:ℝ)≤ (P.active n).card by positivity)
  apply le_of_mul_le_mul_right _ (show 0<((T:ℝ)+1)^2 by positivity)
  linarith

end Stg
end Hie
end
end ExactDerandomization

end

section

namespace ExactDerandomization.Hie
noncomputable section
open Analysis Finset

abbrev radix (M x z : ℕ) := z+M*x
def copyZone (M) (S : Domain) := (S ×ˢ range M).image fun i=>radix M i.1 i.2
lemma fromrad (M x i) (h:i < M) :
    radix M x i / M=x ∧ radix M x i % M=i := by
  simp [radix,Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h,Nat.add_mul_div_left i x (show 0<M by omega)]
lemma inside {M x j : ℕ} {S : Domain} (h:x∈S) (e:j<M) : radix M x j∈copyZone M S :=
    mem_image.2 ⟨(x,j),mem_product.2 ⟨h,mem_range.2 e⟩,rfl⟩
lemma repr_copy {M x} {S:Domain} (h:x∈copyZone M S) :
    ∃ y∈S,∃ j<M, x=radix M y j := by
  obtain ⟨⟨y,j⟩,e,rfl⟩:=mem_image.1 h
  exact ⟨y,(mem_product.1 e).1,j,mem_range.1 (mem_product.1 e).2,rfl⟩
lemma member_copy {M x} {S:Domain} (h:0<M) :
    x∈copyZone M S ↔ x/M∈S := by
  constructor
  · intro h; obtain ⟨y,e,j,k,rfl⟩:=repr_copy h; rwa [(fromrad M y j k).1]
  intro he
  simpa [radix,Nat.mod_add_div] using inside he (Nat.mod_lt x h)
lemma eval_copies {M S} (f : Vec) :
    ∑ x∈copyZone M S,f x = ∑ x∈S,∑ i∈range M,f (radix M x i) := by
  rw [copyZone,sum_image]; exact sum_product ..
  intro a ha b hb e
  have h1:=fromrad M a.1 a.2 (mem_range.1 (mem_product.1 ha).2)
  have h2:=fromrad M b.1 b.2 (mem_range.1 (mem_product.1 hb).2)
  change radix M a.1 a.2 = radix M b.1 b.2 at e; rw [e] at h1; grind

abbrev bound0 : ℝ := 1/128
abbrev bound1 : ℝ := 1/64
def slice (t : ℝ) := rising bound0 bound1 t
def share (M i : ℕ) (t : ℝ) :=
    (if i=0 then 1-slice t else 0)+slice t / M

lemma share_nn (M i) (t) : 0 ≤ share M i t := by
  have he : in01 (slice t) := rising_mem _ _ _
  unfold share in01 at *
  obtain ⟨he,h⟩:=he
  split
  · exact add_nonneg (by linarith) (by positivity)
  · positivity

lemma share_sum (M) (h:0<M) (t) : ∑ j∈range M,share M j t = 1 := by
  simp only [share,sum_add_distrib,sum_const,nsmul_eq_mul,card_range]
  simp [h]
  field_simp
  linarith

lemma share_le {M i} (he:i<M) (t) : share M i t≤1 := by
  rw [← share_sum M (by omega) t]
  exact single_le_sum (fun i _=>share_nn M i t) (mem_range.2 he)

abbrev boost (x : ℝ) := rising (1/4) (1/2) x

namespace Stg
variable (P : Stg) (n : ℕ) [Fact n.Prime]

def fac (x j : ℕ) := if j=0 then 1 else boost (P.probed n P.p.T x)
def newMat (x y : ℕ) :=
   let M:=P.p.M
   let w:=P.D n (x/M) (y/M)
   P.fac n (x/M) (x%M) *w*share M (y%M) (w/P.f)
def next := Stg.mk P.p (P.i+1) (copyZone P.p.M P.S) (P.newMat n)
def project (f : Vec) (x) :=
   let M:=P.p.M
   P.fac n (x/M) (x%M)*f (x/M)

lemma mpos : 0 < P.p.M := by have := P.p.mOK; omega
lemma fac_mem (x i) : in01 (P.fac n x i) := by
  unfold fac; split; norm_num [in01]
  exact rising_mem _ _ _

lemma edge_w (x y) {i} (h:i<P.p.M) :
    P.newMat n x (radix P.p.M y i) =
       P.fac n (x/P.p.M) (x%P.p.M)*P.D n (x/P.p.M) y *
                      share P.p.M i (P.D n (x/P.p.M) y/P.f) := by
  dsimp only [newMat];  rw [(fromrad _ y _ h).1,(fromrad _ y _ h).2]

lemma edge_small (h : Step P.S P.f P.C) (x y) :
    P.newMat n x y≤rate (P.i+1) := by
  let f := P.fac n (x/P.p.M) (x%P.p.M)
  let d := P.D n (x/P.p.M) (y/P.p.M)
  let s := share P.p.M (y%P.p.M) (d/P.f)
  have hb : rate (P.i+1)=P.f/16 := by unfold Stg.f rate; rw [pow_succ]; ring
  rw [hb]; change f*d*s≤_
  have hD:=P.dbounds n h
  have hp : 0≤d:= hD.nn ..
  have hm : 0 ≤ s:=share_nn ..
  have hf : f≤1:=(P.fac_mem ..).2
  have he := mul_le_mul_of_nonneg_right (show f*d≤d by nlinarith) hm
  refine le_trans he ?_
  have hz : 0<P.f:=rate_pos _
  rcases le_total bound1 (d/P.f) with e|e
  · have hw : s=(P.p.M:ℝ)⁻¹ := by
      dsimp only [s,share,slice]
      rw [rising_top (by norm_num) e]; split <;> simp
    have hd : d ≤ (P.p.T+1:ℝ)*P.f := by
      simpa only [Nat.cast_add,Nat.cast_one,one_mul] using hD.key (x/P.p.M) (y/P.p.M)
    rw [hw,← div_eq_mul_inv]
    have h' : 16*(P.p.T+1:ℝ) < P.p.M := by exact_mod_cast P.p.mOK
    apply (div_le_iff₀ (show 0<(P.p.M:ℝ) by linarith)).2
    nlinarith
  · have hs : s≤1 := share_le (Nat.mod_lt _ P.mpos) _
    have he:= (div_le_iff₀ hz).1 e
    unfold bound1 at he; nlinarith

lemma newGood (h : Step P.S P.f P.C) :
    Step (P.next n).S (P.next n).f (P.next n).C := by
  have he := P.dbounds n (S':=P.S) h
  constructor
  · intro x y
    exact mul_nonneg (mul_nonneg (P.fac_mem ..).1 (he.nn ..)) (share_nn ..)
  · intro x y; rw [one_mul]; exact P.edge_small n h x y
  · intro x
    have H (y : ℕ) : ∑ j∈range P.p.M, P.newMat n x (radix P.p.M y j) =
        P.fac n (x/P.p.M) (x%P.p.M)*P.D n (x/P.p.M) y := by
      let a := P.fac n (x/P.p.M) (x%P.p.M)
      let t := P.D n (x/P.p.M) y
      refine Eq.trans (b:=∑ j∈range P.p.M,a*t*share P.p.M j (t/P.f)) (sum_congr rfl ?_) ?_
      · intro i hi; exact P.edge_w n _ _ (mem_range.1 hi)
      · rw [← mul_sum,share_sum _ P.mpos, mul_one]
    change ∑ y∈copyZone P.p.M P.S,P.newMat n x y≤1
    rw [eval_copies]
    simp only [H,← mul_sum]
    exact (mul_le_mul (P.fac_mem ..).2 (he.row _) (sum_nonneg (fun _ _=>he.nn ..))
            (by norm_num)).trans_eq (one_mul _)
  · intro x y hi
    let M:=P.p.M
    have ha : 0<P.D n (x/M) (y/M) := by
      have ht := he.nn (x/M) (y/M)
      by_contra! hc
      change 0 < _*P.D n (x/M) (y/M)*_ at hi
      rw [le_antisymm hc ht] at hi; simp at hi
    obtain ⟨ha,hb,hc⟩:=he.loc _ _ ha
    refine ⟨(member_copy P.mpos).2 ha, (member_copy P.mpos).2 hb,?_⟩
    by_contra! H
    exact (not_lt_of_ge (Nat.div_le_div_right H)) hc

lemma nonprimary (h : Step P.S P.f P.C) (x y j) (hj:j≠0)
    (ht : share P.p.M j (P.D n x y/P.f)≠0) :
    1/2 < P.probed n P.p.T y ∧ P.fac n y j=1 := by
  have hp : 1/2 < P.probed n P.p.T y := by
    by_contra! e
    have hu := good_col h (rate_pos _) (fun x => (show in01 (P.gm n P.p.T x) from gamma_mem _)) P.p.tOK x y (gamma_full e)
    change P.D n x y≤_ at hu
    apply ht
    dsimp [share,slice]
    rw [rising_bot (by norm_num)
          ((div_le_iff₀ (rate_pos P.i)).mpr (le_trans hu (by
             change good*rate P.i ≤ bound0*rate P.i; exact mul_le_mul_of_nonneg_right (by norm_num [good,bound0]) (le_of_lt (rate_pos _))))),ite_eq_right hj]
    simp
  refine ⟨hp,?_⟩; unfold fac boost; rw [ite_eq_right hj,rising_top (by norm_num) hp.le]

lemma commute (h : Step P.S P.f P.C) (v : Vec) (x) :
    mv (P.next n).S (P.next n).C (P.project n v) x =
        P.project n (mv P.S (P.D n) v) x := by
   let M:=P.p.M
   let a:=P.fac n (x/M) (x%M)
   have e (y) : ∑ j∈range M, P.newMat n x (radix M y j)*P.project n v (radix M y j)
                  =a*(P.D n (x/M) y * v y) := by
     let D:=P.D n (x/M) y
     let f (j) := share M j (D/P.f)
     refine Eq.trans (b:=∑ j∈range M,(a*(D*v y))*f j) (sum_congr rfl ?_) ?_
     · intro i hi
       have ht : i<P.p.M:=mem_range.1 hi
       rw [P.edge_w n _ _ ht]
       unfold project; dsimp only
       rw [(fromrad _ _ _ ht).1,(fromrad _ _ _ ht).2]
       change a*D*f i* (P.fac n y i * v y)=_
       by_cases he:f i=0
       · simp [he]
       have hp : P.fac n y i=1 := by
         by_cases hs:i=0
         · simp [fac,hs]
         exact (P.nonprimary n h (x/M) y i hs he).2
       rw [hp]; ring
     · rw [← mul_sum, show ∑ j ∈ range M,f j=1 from share_sum M P.mpos _,mul_one]
   change ∑ y∈copyZone M P.S,_=a*_
   rw [eval_copies]; change ∑ y∈P.S,_=a*∑ y∈P.S,_
   rw [mul_sum]; exact sum_congr rfl fun i _=> e i

lemma few_nodes (h : Step P.S P.f P.C) (hl: 2^P.i ≤ n) :
    (nodes (P.next n).S (P.next n).C).card ≤ 2*(nodes P.S P.C).card := by
   let M:=P.p.M
   let T:=nodes P.S P.C
   let E:=P.active n
   let A':=T.image (fun i=>radix M i 0)
   have he:= P.dbounds n (restrict h (subset_refl T))
   have hz (i j) (hi:0<P.newMat n i j) :
         0 < P.D n (i/M) (j/M) ∧
          P.fac n (i/M) (i%M)≠0 ∧ share M (j%M) (P.D n (i/M) (j/M)/P.f)≠0 := by
      let x:=P.fac n (i/M) (i%M)
      let y:=P.D n (i/M) (j/M)
      let z:=share M (j%M) (y/P.f)
      change 0<x*y*z at hi
      change 0<y ∧ x≠0 ∧ z≠0
      have hh : 0≤ y:=he.nn (i/M) (j/M)
      have : x*y*z≠0 := ne_of_gt hi
      simp only [ne_eq,mul_eq_zero,not_or] at this
      exact ⟨lt_of_le_of_ne hh (Ne.symm this.1.2), this.1.1,this.2⟩
   have hh : nodes (P.next n).S (P.next n).C ⊆ A' ∪ copyZone M E := by
     intro i hi
     obtain ⟨e,y,hy,h'⟩:= mem_filter.mp hi
     have hk := (member_copy P.mpos).1 e
     have hu : radix M (i/M) (i%M)=i := Nat.mod_add_div i M
     rcases h' with hp|hp
     · obtain ⟨h1,h2,-⟩:=hz i y hp
       by_cases hs:i%M=0
       · exact mem_union_left _ (mem_image.mpr ⟨_,(he.loc _ _ h1).1,(hs ▸ hu)⟩)
       · refine mem_union_right _ ((member_copy P.mpos).mpr (mem_filter.2 ⟨hk,?_⟩))
         by_contra! en
         exact h2 (by unfold fac boost; rw [ite_eq_right hs]; exact rising_bot (by norm_num) en)
     · obtain ⟨h1,-,h2⟩:=hz y i hp
       by_cases hs:i%M=0
       · exact mem_union_left _ (mem_image.mpr ⟨_,(he.loc _ _ h1).2.1,(hs ▸ hu)⟩)
       · have ht := (P.nonprimary n h (y/M) (i/M) (i%M) hs h2).1
         exact mem_union_right _ ((member_copy P.mpos).mpr (mem_filter.2 ⟨hk,
           lt_trans (by norm_num) ht⟩))
   have H := P.rare n h hl
   change E.card*M≤T.card at H
   calc _ ≤ _ := card_le_card hh
        _ ≤ _ := card_union_le _ _
        _ ≤ T.card + T.card := add_le_add card_image_le (le_trans card_image_le (by simpa using H))
        _ = _ := by dsimp [T]; omega

end Stg
end
end ExactDerandomization.Hie

end

section

namespace ExactDerandomization.Hie
noncomputable section
open Analysis Finset

lemma apply_add (S:Domain) (C:Mat) (f g : Vec) : mv S C (f+g)=mv S C f+mv S C g := by
  ext; simp [mv,mul_add,sum_add_distrib]
lemma add_apply (S:Domain) (C D:Mat) (f : Vec) : mv S (C+D) f=mv S C f+mv S D f := by
  ext; simp [mv,add_mul,sum_add_distrib]
lemma sub_apply (S:Domain) (C D:Mat) (f : Vec) : mv S (C-D) f=mv S C f-mv S D f := by
  ext; simp [mv,sub_mul,sum_sub_distrib]

structure Prize where
 P : Stg
 W : Vec
 /-- conceptual transported true probability -/
 v : Vec

namespace Prize

variable (n : ℕ) [Fact n.Prime]

def plus (H : Prize) :=
  {P:=H.P.next n
   W:=H.P.project n (H.W+mv H.P.S (H.P.corr n H.P.p.T) H.W)
   v:=H.P.project n H.v : Prize}

structure Correct (H : Prize) : Prop where
  step : Step H.P.S H.P.f H.P.C
  Wnn : 0≤H.W
  v01 : ∀ x,in01 (H.v x)
  eq : H.v=H.W+mv H.P.S H.P.C H.v

lemma Correct.win {H : Prize} (h: H.Correct) (x : ℕ) : in01 (H.W x) := by
  have he := congrFun h.eq x
  have hu : 0 ≤ mv H.P.S H.P.C H.v x := sum_nonneg fun i _=>
     mul_nonneg (h.step.nn _ _) (h.v01 i).1
  obtain ⟨_,hh⟩:=h.v01 x
  exact ⟨h.Wnn x,by simp only [Pi.add_apply] at he; linarith⟩

lemma Correct.raise {H : Prize} (h: H.Correct) : (plus n H).Correct := by
  let P:=H.P
  let T:=P.S
  let F:=P.corr n P.p.T
  have he:=P.cbounds n h.step P.p.T
  constructor
  · exact P.newGood n h.step
  · intro x
    have ht: 0≤ (H.W+mv T F H.W) := fun i=> add_nonneg (h.Wnn i)
       (sum_nonneg fun j _=> mul_nonneg (he.nn i j) (h.Wnn j))
    exact mul_nonneg (P.fac_mem n _ _).1 (ht _)
  · intro i
    let x:=i/P.p.M
    change in01 (_*H.v _)
    exact ⟨mul_nonneg (P.fac_mem n x _).1 (h.v01 x).1,
     le_trans (mul_le_mul (P.fac_mem n x _).2 (h.v01 x).2 (h.v01 x).1 zero_le_one)
       (le_of_eq (one_mul _))⟩
  · ext x
    let W' := H.W+mv T F H.W
    change P.project n H.v x=P.project n W' x + _
    have e := P.commute n h.step H.v x
    change _=P.project n W' x+ mv (P.next n).S (P.next n).C (P.project n H.v) x
    rw [e]; unfold Stg.project; simp only []; rw [← mul_add]
    have heq : H.v=W'+mv T (P.D n) H.v := by
      change _=_+mv T ((P.C+mm T F P.C)-F) _
      rw [sub_apply,add_apply,mm_mv]
      have hf : mv T F H.v=mv T F H.W+mv T F (mv T P.C H.v) :=
         Eq.trans (congrArg (mv T F) h.eq) (apply_add T F ..)
      rw [hf]
      calc H.v = _ := h.eq
           _ = _ := by dsimp only [W',T,P,F]; abel
    have hu := congrFun heq (x/H.P.p.M)
    rw [show W' (x/P.p.M)+_ = H.v (x/P.p.M) from hu.symm]

def iterate (H : Prize) : ℕ→Prize
 | 0=>H
 | k+1=>plus n (iterate H k)

lemma all {H : Prize} (h:H.Correct) (k) : (H.iterate n k).Correct := by
  induction k with
  | zero=>exact h
  | succ k ih=>exact ih.raise n

lemma par (H : Prize) (k) : (H.iterate n k).P.p=H.P.p := by
  induction k with
  | zero=>rfl
  | succ k ih=>exact ih

lemma index (H : Prize) (k) : (H.iterate n k).P.i=H.P.i+k := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    change _ + 1=_
    rw [ih]
    omega

def child (H : Prize) (x : ℕ) : ℕ→ℕ
 | 0=>x
 | k+1=>radix H.P.p.M (child H x k) 0

lemma unchanged (H : Prize) (k x) :
     (H.iterate n k).v (child H x k)=H.v x := by
   induction k with
   | zero=>rfl
   | succ k ih=>
     simp only [child,iterate,plus,Stg.project,par]
     have he := fromrad _ (child H x k) 0 H.P.mpos
     simp only [he.1,he.2,Stg.fac,ite_true,one_mul]; exact ih

lemma reach (H : Prize) (k) {x} (hx:x∈H.P.S) :
     child H x k ∈ (H.iterate n k).P.S := by
   induction k with
   | zero=>exact hx
   | succ k ih=>
     have he := inside ih H.P.mpos
     simp only [child,iterate,plus,Stg.next,par]; exact he

lemma density {H : Prize} (h:H.Correct) (k) (hl : 2^(H.P.i+k)≤n) :
    (nodes (H.iterate n k).P.S (H.iterate n k).P.C).card ≤ H.P.S.card*2^k := by
  induction k with
  | zero=> simpa only [iterate,nodes,pow_zero,mul_one] using card_le_card
                    (filter_subset (s:=H.P.S) _)
  | succ k ih=>
    have hk : 2^(H.P.i+k)≤n:=le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hl
    let P:=(H.iterate n k).P
    calc _ ≤ 2*(nodes P.S P.C).card :=
           P.few_nodes n ((all n h k).step) (by simp only [P,index]; exact hk)
         _ ≤ _ := by
           rw [pow_succ]
           have he : (nodes P.S P.C).card≤_:=ih hk
           rw [← mul_assoc]; omega

lemma finish {H : Prize} (h:H.Correct) (k) (hl : 2^(H.P.i+k) ≤ n) (x) :
    0 ≤ H.v x-(H.iterate n k).W (child H x k) ∧
    H.v x-(H.iterate n k).W (child H x k) ≤
       ((H.P.S.card * 2^k : ℕ) : ℝ) * rate (H.P.i+k) := by
  let P:=H.iterate n k
  let T:=P.P
  let y:=child H x k
  rw [← unchanged n H k x]
  have hs : P.Correct:=all n h k
  have he : (P.v y)-P.W y = mv T.S T.C P.v y:= by
    have h:=congrFun hs.eq y; dsimp only [Pi.add_apply] at h; rw [h]; ring
  change 0≤ P.v y-P.W y ∧ P.v y-P.W y≤_
  rw [he]
  have hu (i) := mul_nonneg (hs.step.nn y i) (hs.v01 i).1
  refine ⟨sum_nonneg fun i _=>hu i,?_⟩
  let S:=nodes T.S T.C
  have hp:S ⊆ T.S := filter_subset ..
  have hh := restrict hs.step (subset_refl S)
  unfold mv
  rw [← sum_subset hp]
  · have hf : T.f=rate (H.P.i+k) := by simp only [Stg.f,T,P,index]
    calc
     _ ≤ ∑ _i∈S,T.f := sum_le_sum fun i _=> (mul_le_mul (hh.key ..) (hs.v01 i).2
                (hs.v01 i).1 (by unfold Stg.f; have := rate_pos T.i; positivity)).trans_eq (by ring)
     _ ≤ _ := by
       simp only [sum_const,nsmul_eq_mul,hf]
       exact mul_le_mul_of_nonneg_right (by exact_mod_cast density n h k hl) (le_of_lt (rate_pos _))
  · intro i hi hk
    have hu : ¬0<T.C y i := fun h=> hk (hh.loc y i h).2.1
    rw [le_antisymm (le_of_not_gt hu) (hs.step.nn ..),zero_mul]

end Prize
end
end ExactDerandomization.Hie

end

end OAI
