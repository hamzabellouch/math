import OAI.Computability.Logspace.ProbabilityAtoms

namespace OAI

/-!
Row compression, shutdown thresholds, and accumulated approximation error.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Scalar, entry and row helpers for the full-array compression. -/
namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

/- scalar helpers -/
lemma maxnear {x a y b t : ℝ}
    (h:|x-y| ≤ t) (e:|a-b|≤t) : |max x a-max y b| ≤ t := by
  rw [abs_le] at *
  grind
lemma minnear {x a y b t : ℝ}
    (h:|x-y| ≤ t) (e:|a-b|≤t) : |min x a-min y b| ≤ t := by
  rw [abs_le] at *
  grind
lemma absnear {x y t : ℝ} (h : |x-y|≤t) : |(|x|-|y|)|≤t := by
  exact le_trans (abs_abs_sub_abs_le ..) h
lemma addnear {x x' y y' a b:ℝ} (h : |x-x'|≤a) (e : |y-y'|≤b) :
    |x+y-(x'+y')|≤a+b := by
   rw [show x+y-(x'+y')=(x-x')+(y-y') by ring]
   exact (abs_add_le ..).trans (add_le_add h e)
lemma subnear {x x' y y' a b:ℝ} (h : |x-x'|≤a) (e : |y-y'|≤b) :
    |(x-y)-(x'-y')| ≤ a+b := by
   have hi : |(-y)-(-y')| ≤ b := by rw [show -y - -y'=-(y-y') by ring,abs_neg]; exact e
   simpa only [sub_eq_add_neg] using addnear h hi
lemma sat_near {x y a b c d:ℝ} (h:|x-y|≤c) (e:|a-b|≤d) :
    |sat a x-sat b y|≤c+d := by
   have ha:=abs_nonneg (a-b); have hy:=abs_nonneg (x-y)
   have hc : 0≤c := le_trans hy h
   have hd : 0≤d := le_trans ha e
   have he := show |a-b|≤c+d by linarith
   apply minnear he
   apply maxnear _ (le_trans h (by linarith))
   rw [show -a - -b=-(a-b) by ring,abs_neg]; exact he
lemma sat_id {x u:ℝ} (h:|x|≤u) : sat u x=x := by
   obtain ⟨h,e⟩:=abs_le.1 h; simp [sat,clip,h,e]
lemma sat_eq_min {x u:ℝ} (h: -u ≤ x) : sat u x = min u x := by simp [sat,clip,h]
lemma sat_abs {x u:ℝ} (h:0≤u) : |sat u x| = min u |x| := by
   rcases le_total 0 x with h0|h0
   · have he := le_trans (neg_nonpos.2 h) h0
     rw [sat_eq_min he,abs_of_nonneg (le_min h h0),abs_of_nonneg h0]
   rw [abs_of_nonpos h0]; unfold sat clip
   rw [min_eq_right (max_le (by linarith) (by linarith))]
   rw [abs_of_nonpos (max_le (by linarith) h0)]; grind
lemma sat_between {x u:ℝ} (h : 0≤u) : min 0 x ≤ sat u x ∧ sat u x≤ max 0 x := by
   unfold sat clip; grind
lemma sat_size {u:ℝ} (h:0≤u) (x : ℝ) : |sat u x| ≤ u := by rw [sat_abs h]; exact min_le_left ..
lemma sat_add {r h d x y : ℝ} (hh:|d|+r≤h) (he : sat h x=sat h y) (hg: 0≤r) :
    sat r (x+d)=sat r (y+d) := by
   unfold sat clip at he
   have h1:=le_abs_self d; have h2:=neg_le_abs d
   unfold sat clip
   grind

/-- Compression coordinate binary vector helpers. -/
abbrev Row := ℕ → Pt
def ht (p : Pt) := max |p.1| |p.2|
lemma ht_nn (p) : 0 ≤ ht p := le_trans (abs_nonneg _) (le_max_left ..)
def near (c : ℝ) (v w : Pt) := |v.1-w.1|≤c ∧ |v.2-w.2|≤c
def clp (r : ℝ) (p : Pt) : Pt := (sat r p.1, sat r p.2)
lemma ht_clp {p r} (h:0≤r) : ht (clp r p) = min r (ht p) := by
   simp only [clp,ht,sat_abs h]; grind
lemma near_ht {v w c} (h:near c v w) : |ht v-ht w|≤c := maxnear (absnear h.1) (absnear h.2)
lemma ht_near (x : ℝ) (p : Pt) : ht p≤x ↔ near x p 0 := by simp [ht,near]
lemma near_self {c p} (h:0≤c) : near c p p := by simp [near,h]
lemma near_le {v w c d} (h:near c v w) (e:c≤d) : near d v w := ⟨h.1.trans e,h.2.trans e⟩
lemma near_add {v w p q c d} (h:near c v w) (e:near d p q) :
    near (c+d) (v+p) (w+q) := ⟨addnear h.1 e.1,addnear h.2 e.2⟩
lemma near_sub {v w p q c d} (h:near c v w) (e:near d p q) :
    near (c+d) (v-p) (w-q) := ⟨subnear h.1 e.1,subnear h.2 e.2⟩
lemma ht_add (p q) : ht (p+q)≤ ht p+ht q := by
   have e := near_add ((ht_near (ht p) p).1 le_rfl) ((ht_near (ht q) q).1 le_rfl)
   rw [add_zero] at e; exact (ht_near ..).2 e
lemma ht_sub (v w c) : ht (v-w)≤c ↔ near c v w := by simp [ht,near]

abbrev line (z : ℝ) : Pt := (z,0)
lemma ht_line {z} (h:0≤z) : ht (line z)=z := by simp [ht,h]

def suit (S : Domain) (a : ℝ) (w v : Blob) :=
   |w.base-v.base|≤a ∧ ∀ i∈S, near a (w.ts i) (v.ts i)
lemma suit_self (S B b) (h : 0≤b) : suit S b B B := ⟨by simpa,fun _ _=>near_self h⟩
lemma suit0 {S v w} (h : suit S 0 v w) :
   v.base=w.base ∧ ∀ i∈S, v.ts i=w.ts i := by
   constructor
   · have := h.1
     exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
   intro i hi
   have ⟨hx,hy⟩:=h.2 i hi
   exact Prod.ext (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hx (abs_nonneg _))))
            (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hy (abs_nonneg _))))
lemma suit_rk {S b v w} (h:suit S b v w) (K : ℕ) :
    |v.rk S K-w.rk S K|≤b :=
   maxnear (rank_lip (le_trans (abs_nonneg _) h.1) (fun i hi=>(h.2 i hi).1)) h.1
lemma suit_val {t C f S b v w} (h:TS t C f) (e:suit S b v w) (K) {i} (hi:i∈S) :
   |fourth (v.val S K f i)-fourth (w.val S K f i)|≤3*C^3*b :=
   h.comparison (e.2 i hi).1 (suit_rk e K) (e.2 i hi).2

lemma rank_min {α : Type} (S : Finset α) (f : α→ ℝ) (K u) (h:0≤ u) :
   rank S (fun i=>min u (f i)) K=min u (rank S f K) := by

  have he1:=rank_nn S f K; have he2:=rank_nn S (fun i=>min u (f i)) K
  have he3 := le_min h he1
  rcases lt_trichotomy (rank S (fun i=>min u (f i)) K) (min u (rank S f K)) with hs|hs|hs
  · let r:=rank S (fun i=>min u (f i)) K
    have ht := (rank_gt he2).mp (lt_of_lt_of_le hs (min_le_right ..))
    have hh : r < u := lt_of_lt_of_le hs (min_le_left ..)
    refine False.elim (lt_irrefl r ((rank_gt he2).mpr ?_))
    simpa only [lt_min_iff,show rank S (fun i=>min u (f i)) K < u from hh,true_and]
  · exact hs
  · apply False.elim
    let v:=min u (rank S f K)
    have he := (rank_gt he3).mp hs
    rcases le_total u (rank S f K) with h|h
    · rw [min_eq_left h] at he; simp at he
    · rw [min_eq_right h] at he
      refine lt_irrefl _ ((rank_gt he1).mpr (lt_of_lt_of_le he (card_le_card ?_)))
      intro i hi; obtain ⟨hi,hh⟩:=mem_filter.mp hi
      exact mem_filter.2 ⟨hi,lt_of_lt_of_le hh (min_le_right ..)⟩

lemma rank_sat {α : Type} (S : Finset α) (f : α→ℝ) (K u) (h:0≤u) :
   rank S (fun i=> sat u (f i)) K = min u (rank S f K) := by
  unfold sat clip; rw [rank_min S _ K u h]
  have he : rank S (fun i=>max (-u) (f i)) K=rank S f K := by
    have hl:= rank_nn S f K; have hv :=rank_nn S (fun i=>max (-u) (f i)) K
    have hk (v) (he:0≤v) (i) : (v< max (-u) (f i))=(v<f i) := by grind
    rcases lt_trichotomy (rank S (fun i=>max (-u) (f i)) K) (rank S f K) with he|he|he
    · refine False.elim (lt_irrefl _ ((rank_gt hv).mpr ?_))
      simp_rw [hk _ hv]; exact (rank_gt hv).mp he
    · exact he
    · have hu := (rank_gt hl).mp he
      simp_rw [hk _ hl] at hu
      exact False.elim (lt_irrefl _ ((rank_gt hl).mpr hu))
  rw [he]

end
end ExactDerandomization.Buf

end

section

/-! Row update with thresholds capped at 4. While the gate is below
permanent shutdown this cap has no effect on the exceptional representation;
the actual calculation can use a buffered shutdown test emptying its real
slots on detecting u > 2. Our analysis uses the full map before that emptying. -/
namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

structure Params where
    S : Domain
    K : ℕ
    n : ℕ
    rho : ℝ

namespace Params
variable (p : Params)
def U (v : Blob) := min 4 (max p.rho (max v.base (rank p.S (fun i=> ht (v.ts i)) p.n)))
def Z (v : Blob) := min 4 (max (p.U v) (min (v.rk p.S p.K) (3*p.U v)))

lemma U_nn (v : Blob) : 0 ≤ p.U v := by unfold U; have :=rank_nn p.S (fun i=> ht (v.ts i)) p.n; grind
lemma U_four (v : Blob) : p.U v ≤ 4 := min_le_left ..
lemma U_old {v : Blob} (h : v.base ≤ 4) : v.base ≤ p.U v := by unfold U; grind
lemma U_rho (v : Blob) (h : p.rho ≤ 4) : p.rho ≤ p.U v := by unfold U; grind
lemma Z_w (v : Blob) : p.U v≤p.Z v∧ p.Z v≤3*p.U v ∧ p.Z v≤4 := by
  have h:=p.U_nn v; have e:=p.U_four v
  unfold Z; grind
lemma Z_nn (v : Blob) : 0≤p.Z v := (p.U_nn v).trans (p.Z_w v).1

def push (v : Blob) : Blob :=
   let u:=p.U v
   let z:=p.Z v
   ⟨z,fun i=>
       let r:=v.ts i
       let b:=line z
       b + clp (7*max 0 (ht r-2*u)) (r-b)⟩

lemma base_push (v : Blob) : (p.push v).base=p.Z v := rfl

lemma nearbase {v : Blob} {i} (h: ht (v.ts i)≤2*p.U v) :
    (p.push v).ts i = line (p.Z v) := by
   have H x : sat 0 x=0 := by unfold sat clip; grind
   dsimp only [push]
   rw [max_eq_left (show ht (v.ts i)-2*p.U v≤0 from by linarith)]
   simp [clp,H]
lemma offbase {v : Blob} {i} (h : 3*p.U v ≤ ht (v.ts i)) :
    (p.push v).ts i=v.ts i := by
   have h1:=p.U_nn v; obtain ⟨h2,h3,-⟩:=p.Z_w v; let z:=line (p.Z v)
   let m:=ht (v.ts i)
   have hx : ht (-z)=p.Z v := by simp [ht,z,p.Z_nn]
   have e : ht (v.ts i-z)≤ m+3*p.U v := by
      rw [sub_eq_add_neg]
      apply le_trans (ht_add _ _)
      rw [hx]; linarith
   have hh : ht (v.ts i-z) ≤7*max 0 (ht (v.ts i)-2*p.U v) := by
      unfold m at e; have H:=le_max_right 0 (ht (v.ts i)-2*p.U v)
      linarith
   obtain ⟨a,b⟩:=max_le_iff.mp hh
   have ht : clp (7*max 0 (ht (v.ts i)-2*p.U v)) (v.ts i-z)=v.ts i-z :=
        Prod.ext (sat_id a) (sat_id b)
   unfold push; change z+clp _ (_-z)=_
   rw [ht]; abel

def Between (x y z : ℝ) := min x z ≤ y ∧ y ≤ max x z
lemma middle {v : Blob} {i} :
    Between (p.Z v) ((p.push v).ts i).1 (v.ts i).1 ∧
     Between 0 ((p.push v).ts i).2 (v.ts i).2 := by
   let u:=7*max 0 (ht (v.ts i)-2*p.U v)
   have h : 0 ≤ u := by dsimp [u]; positivity
   have H (x b : ℝ) : Between b (b+sat u (x-b)) x := by
      have := sat_between (x:=x-b) h; unfold Between
      grind
   exact ⟨H _ _,H _ _⟩

lemma perturb (v : Blob) (i) : near (6*p.U v) ((p.push v).ts i) (v.ts i) := by
   have h:=p.U_nn v; obtain ⟨h2,h3,h4⟩:=p.Z_w v
   rcases le_total (3*p.U v) (ht (v.ts i)) with hh|hh
   · rw [p.offbase hh]; exact near_self (by linarith)
   obtain ⟨a1,a2⟩:=max_le_iff.mp hh
   obtain ⟨a,b⟩:=p.middle (v:=v) (i:=i)
   unfold near Between at *
   rw [abs_le] at a1 a2; rw [abs_le,abs_le]
   grind

lemma U_near {v w b} (h:suit p.S b v w) :
    |p.U v-p.U w|≤b := by
   have hs : 0≤b := le_trans (abs_nonneg _) h.1
   apply minnear (by simpa)
   apply maxnear (by simpa)
   apply maxnear h.1
   exact rank_lip hs fun i hi=>near_ht (h.2 i hi)
lemma Z_near {v w b} (h:suit p.S b v w) :
    |p.Z v-p.Z w|≤ 3*b := by
   have hs : 0≤b := le_trans (abs_nonneg _) h.1
   have hu:=p.U_near h
   apply minnear (by simp; linarith)
   apply maxnear (by linarith)
   apply minnear (le_trans (suit_rk h _) (by linarith))
   rw [← mul_sub,abs_mul,abs_of_nonneg (show (0:ℝ)≤3 by norm_num)]
   linarith
lemma smooth_push {v w b} (h:suit p.S b v w) :
    suit p.S (30*b) (p.push v) (p.push w) := by
   have hu:=p.U_near h; have hz:=p.Z_near h
   have hs : 0≤ b:=le_trans (abs_nonneg _) h.1
   refine ⟨le_trans hz (by linarith),fun i hi=>?_⟩
   have he:=h.2 i hi
   have htt := near_ht he
   let r (v:Blob):=7*max 0 (ht (v.ts i)-2*p.U v)
   have hr : |r v-r w|≤21*b := by
     have h1 : |2*p.U v-2*p.U w|≤2*b := by rw [← mul_sub,abs_mul,abs_of_nonneg (by norm_num)]; linarith
     have h2 := subnear htt h1
     have h3 := maxnear (show |(0:ℝ)-0|≤b+2*b by simp; linarith) h2
     unfold r; rw [← mul_sub,abs_mul,abs_of_nonneg (by norm_num)]
     linarith
   have hh : near (3*b) (line (p.Z v)) (line (p.Z w)) := ⟨hz,show |(0:ℝ)-0|≤3*b from by simp; linarith⟩
   have hl := near_sub he hh
   have hq := near_add hh (show near (b+3*b+21*b)
                            (clp (r v) (v.ts i-line (p.Z v)))
                            (clp (r w) (w.ts i-line (p.Z w))) from
                                  ⟨sat_near hl.1 hr,sat_near hl.2 hr⟩)
   exact near_le hq (by linarith)

end Params

def struck (L : ℝ) (v : Blob) : Blob := ⟨v.base,fun i=>clp L (v.ts i)⟩

lemma strike_U (p : Params) (v : Blob) (L : ℝ) (hh:4≤L) :
    p.U (struck L v)=p.U v := by
   unfold Params.U struck; have hL : 0≤L := by linarith
   simp_rw [ht_clp hL,rank_min _ _ _ L hL]; grind

lemma strike_rk (S : Domain) (K) (v : Blob) (L) (h : v.base≤L) (hh:0≤L) :
    (struck L v).rk S K = min L (v.rk S K) := by
   unfold struck Blob.rk clp; simp_rw [rank_sat _ _ _ _ hh]; grind

lemma strike_Z (p : Params) (v : Blob) (L) (hh:12≤L) (h:v.base≤4) :
    p.Z (struck L v)=p.Z v := by
   unfold Params.Z
   rw [strike_U p v _ (by linarith),strike_rk _ _ _ _ (by linarith) (by linarith)]
   have he := p.U_four v; grind

lemma strike_push (p : Params) (v : Blob) (L) (hh:12≤L) (h:v.base≤4) :
    struck L (p.push v)= p.push (struck L v) := by
   have he:=strike_U p v L (by linarith)
   have hZ := strike_Z p v L hh h
   have hu:=p.U_four v
   have H (i) : clp L ((p.push v).ts i)=(p.push (struck L v)).ts i := by
      have h0 : 0≤L:=by linarith
      rcases le_total (3*p.U v) (ht (v.ts i)) with hv|hv
      · rw [Params.offbase p hv,Params.offbase p]
        · rfl
        rw [he]
        change 3*p.U v≤ht (clp L (v.ts i))
        rw [ht_clp h0]; exact le_min (by linarith) hv
      obtain ⟨hx,hy⟩:=max_le_iff.mp hv
      have hg1 : |(v.ts i).1|≤L := by linarith
      have hg2 : |(v.ts i).2|≤L := by linarith
      have hg : (struck L v).ts i=v.ts i := Prod.ext (sat_id hg1) (sat_id hg2)
      rw [show (p.push (struck L v)).ts i=(p.push v).ts i from ?_]
      · obtain ⟨h1,h2⟩:=Params.middle p (v:=v) (i:=i)
        obtain ⟨h1a,h1b⟩:=h1; obtain ⟨h2a,h2b⟩:=h2
        obtain ⟨hp,hp'⟩:=abs_le.1 hg1; obtain ⟨hq,hq'⟩:=abs_le.1 hg2
        obtain hh' :=p.Z_nn v; obtain hh'' := (p.Z_w v).2.2
        exact Prod.ext (sat_id (by rw [abs_le]; grind)) (sat_id (by rw [abs_le]; grind))
      dsimp only [Params.push]; rw [he,hZ,hg]
   cases H1:struck L (p.push v) with
   | mk base ts =>
     cases H2:p.push (struck L v) with
     | mk b f =>
       have h1 : base=b := calc
         _ = (struck L (p.push v)).base := by rw [H1]
         _ = (p.push (struck L v)).base := hZ.symm
         _ = b := by rw [H2]
       have h2 : ts=f := calc
         _ = (struck L (p.push v)).ts := by rw [H1]
         _ = (p.push (struck L v)).ts := funext H
         _ = _:= by rw [H2]
       rw [h1,h2]
lemma strike_val {theta C f} {v:Blob} (h:TS theta C f) (S : Domain) (K i L) (he:C≤L)
    (hh:v.base≤L) :
    (struck L v).val S K f i=v.val S K f i := by
   have hg:= h.extend he
   have hl:=h.start.one
   unfold Blob.val
   rw [strike_rk _ _ _ _ hh (by linarith)]
   have hk : sat L (v.rk S K)=min L (v.rk S K) := sat_eq_min (by
      unfold Blob.rk; have :=rank_nn S (fun i=>(v.ts i).1) K; grind)
   rw [← hk]; exact hg.flat _ _ _

/-- At gate-close baseline, any arrays represent zero row outputs. -/
lemma closed {theta C f} {v:Blob} (h:TS theta C f) (he : theta/40 ≤ v.base)
   (S : Domain) (K i) : v.val S K f i=0 := by
   unfold Blob.val Trio.eval
   rw [h.off (v.rk S K) (he.trans (le_max_right ..))]; ring

end
end ExactDerandomization.Buf

end

section

/-! Compression remaining stationary on a nearly nonnegative reference array. -/
namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

abbrev mist := 10*At.small
lemma smallp : 0<At.small := by norm_num [At.small,delta,A]
lemma mistp : 0< mist := by have :=smallp; unfold mist; linarith
lemma mist1 : mist<1 := by norm_num [mist,At.small,delta,A]
lemma mist_eta {theta} (h : delta≤theta) : mist < eta theta := by
  unfold mist At.small eta; unfold delta A at *; linarith
lemma mist_shut {theta} (h : delta≤theta) : 3*mist<theta/8 := by
  have := mist_eta h; have he:=dp; unfold eta at *; linarith

def Calm (S : Domain) (v : Blob) : Prop :=
    0 ≤ v.base ∧ v.base≤4 ∧ ∀ i∈S, -mist ≤ (v.ts i).1 ∧ |(v.ts i).2|≤ mist

namespace Params
variable (p : Params)
lemma still_calm {v} (h : Calm p.S v) : Calm p.S (p.push v) := by
   refine ⟨p.Z_nn v,(p.Z_w v).2.2,fun i hi=>?_⟩
   obtain ⟨hl,ht⟩:= h.2.2 i hi
   obtain ⟨⟨hx,hy⟩,hg,hg'⟩:=p.middle (v:=v) (i:=i)
   have he := p.Z_nn v; have hp:=mistp
   rw [abs_le] at ht ⊢
   grind

lemma toprank {q : ℝ} {v} (he:0≤q) (hh:v.rk p.S p.K≤q) (hz:p.Z v ≤ q) :
    (p.push v).rk p.S p.K≤q := by
  have hc : rank p.S (fun i=>(v.ts i).1) p.K ≤ q :=
     le_trans (le_max_left ..) hh
  unfold Blob.rk
  apply max_le _ hz
  by_contra! h
  have ht := (rank_gt he).1 h
  have he1 := (rank_gt (K:=p.K) (f:=fun i=>(v.ts i).1) (s:=p.S) he).not.mpr
  have hi : (p.S.filter fun i=>q<((p.push v).ts i).1) ⊆ p.S.filter (fun i=>q<(v.ts i).1) := by
    intro i hg; obtain ⟨hj,hk⟩:=mem_filter.mp hg
    obtain ⟨hx,hy⟩:=(p.middle (i:=i) (v:=v)).1
    exact mem_filter.mpr ⟨hj,by grind⟩
  exact not_lt_of_ge hc ((rank_gt he).mpr (lt_of_lt_of_le ht (card_le_card hi)))

lemma hold_U {q v} (h: Calm p.S v) (hq: mist≤ q) (he:v.rk p.S p.K ≤ q)
    (hs : p.rho ≤ mist) (hk : p.K≤p.n) : p.U v ≤ q := by
   have hq0 : 0 ≤ q := by linarith [mistp]
   have hb : v.base ≤ q := le_trans (le_max_right ..) he
   have hp : rank p.S (fun i=>(v.ts i).1) p.K ≤ q := le_trans (le_max_left ..) he
   have hh : rank p.S (fun i=>ht (v.ts i)) p.n ≤ q := by
     by_contra! e
     have he := lt_of_le_of_lt hk ((rank_gt hq0).1 e)
     have ht : p.S.filter (fun i=>q<ht (v.ts i)) ⊆ p.S.filter (fun i=>q<(v.ts i).1) := by
       intro i hi; obtain ⟨h1,h2⟩:=mem_filter.1 hi
       obtain ⟨hy,hz⟩:=h.2.2 i h1
       apply mem_filter.2 ⟨h1,?_⟩; unfold ht at h2; grind
     exact not_lt_of_ge hp ((rank_gt hq0).2 (lt_of_lt_of_le he (card_le_card ht)))
   unfold U; grind
lemma hold_Z {q v} (h:v.rk p.S p.K ≤ q) (he:p.U v≤q) :
    p.Z v≤q := by unfold Z; grind

lemma raising_rank {q : ℝ} {v : Blob} (h:Calm p.S v) (hz:0<q)
    (he:q≤v.rk p.S p.K) (hq:q≤4) : q≤(p.push v).rk p.S p.K := by
   rcases le_total q (p.Z v) with hb|hb
   · exact le_trans hb (le_max_right ..)
   by_contra! hc
   have hh : p.Z v < q := lt_of_le_of_lt (le_max_right ..) hc
   have hh1 : 3*p.U v < q := by unfold Z at hh; grind
   have htt : v.base < q :=
      lt_of_le_of_lt ((p.U_old h.2.1).trans (p.Z_w v).1) hh
   have he1 : q≤rank p.S (fun i=>(v.ts i).1) p.K := by unfold Blob.rk at he; grind
   have hs := (rank_ge hz).1 he1
   have hx : p.S.filter (fun i=>q≤(v.ts i).1) ⊆ p.S.filter (fun i=>q≤((p.push v).ts i).1) := by
      intro i hi; obtain ⟨h1,h2⟩:=mem_filter.mp hi
      have h3 : 3*p.U v≤ht (v.ts i) := by unfold ht; grind
      apply mem_filter.mpr ⟨h1,?_⟩; rw [p.offbase h3]; exact h2
   have hu : q ≤ (p.push v).rk p.S p.K :=
     le_trans ((rank_ge hz).mpr (lt_of_lt_of_le hs (card_le_card hx))) (le_max_left ..)
   linarith

lemma same {theta C v f r} (h : TS theta C f) (ht:0<theta)
    (he : f.row (v.rk p.S p.K)=f.row ((p.push v).rk p.S p.K))
    (hs : 3*r ≤ theta/8) (hx : p.U v≤r) (i) :
    v.val p.S p.K f i = (p.push v).val p.S p.K f i := by
  rcases le_total (3*p.U v) (Buf.ht (v.ts i)) with h1|h1
  · unfold Blob.val Trio.eval; rw [p.offbase h1,he]
  have hp := (p.Z_w v).2.1
  have h2:= (p.middle (i:=i) (v:=v)).1.2
  have h3 : (v.ts i).1 ≤ theta/8 := by unfold Buf.ht at *; grind
  have h4 : ((p.push v).ts i).1 ≤ theta/8 := by grind
  unfold Blob.val Trio.eval
  rw [h.shut _ h3,h.shut _ h4]; ring

lemma motionless {theta C f} (h : TS theta C f) (ht:delta≤theta) (hc:theta≤1)
    {v} (hv:Calm p.S v) (hz:p.rho≤ mist) (hk:p.K≤p.n) (i) :
    (p.push v).val p.S p.K f i=v.val p.S p.K f i := by
  have ht0 : 0<theta := dp.trans_le ht
  let q := v.rk p.S p.K
  rcases le_total q mist with hq|hq
  · have hu:=p.hold_U hv le_rfl hq hz hk
    have hZ := p.toprank (le_of_lt mistp) hq (p.hold_Z hq hu)
    have H := le_of_lt (mist_eta ht)
    apply Eq.symm (p.same h ht0 _ (le_of_lt (mist_shut ht)) hu i)
    rw [h.full _ (le_trans hq H),h.full _ (le_trans hZ H)]
  rcases le_total q 4 with hh|hh
  · have hu := p.hold_U hv hq le_rfl hz hk
    have h0 : 0<q := lt_of_lt_of_le mistp hq
    have h1 : (p.push v).rk p.S p.K=q := le_antisymm
      (p.toprank h0.le le_rfl (p.hold_Z le_rfl hu)) (p.raising_rank hv h0 le_rfl hh)
    have hL : f.row (v.rk p.S p.K)=f.row ((p.push v).rk p.S p.K) := by rw [h1]
    rcases le_total (theta/40) q with h2|h2
    · unfold Blob.val Trio.eval; rw [h1,h.off _ h2]; ring
    · exact Eq.symm (p.same h ht0 hL (by linarith : 3*q ≤ theta/8) hu i)
  have h1 := p.raising_rank hv (by norm_num : (0:ℝ)<4) hh le_rfl
  unfold Blob.val Trio.eval
  have h2 : theta/40 ≤ 4 := by linarith
  rw [h.off _ (h2.trans h1),h.off (v.rk p.S p.K) (h2.trans hh)]; ring

end Params

def trim (F : Domain) (v:Blob) : Blob :=
    ⟨0,fun i=>if i∈F then v.ts i else 0⟩

/-- Positions with their first entry below mist are below sensitivity.
Drop them to compare only the other positions. -/
lemma trim_safe {theta C f} (h : TS theta C f) (ht: delta ≤ theta)
    (S F : Domain) {v:Blob} (he:v.base≤ mist)
    (hh : ∀ i∈S,i∉F → (v.ts i).1≤ mist) (K) {i} (hi:i∈S) :
    v.val S K f i=(trim F v).val S K f i := by
   let w:= trim F v
   have hu (q : ℝ) (hz:mist ≤ q) :
      q<v.rk S K ↔ q<w.rk S K := by
     have hg := lt_of_lt_of_le mistp hz
     have hs : (S.filter fun i=>q<(v.ts i).1) = S.filter (fun i=>q<(w.ts i).1) := by
        ext i; unfold w trim; by_cases hi:i∈F
        · simp [hi]
        by_cases he:i∈S
        · have hx : (v.ts i).1≤q:=(hh i he hi).trans hz; simp [hi,not_lt_of_ge hx,not_lt_of_ge hg.le]
        · simp [he]
     unfold Blob.rk
     have h1 : v.base ≤ q := he.trans hz
     have h2 : w.base ≤ q := hg.le
     rw [lt_max_iff,lt_max_iff,rank_gt hg.le,rank_gt hg.le,hs]
     grind
   have ht0 := le_of_lt (mist_eta ht)
   have hw : f.row (v.rk S K)=f.row (w.rk S K) := by
      by_cases hp: mist<v.rk S K
      · have hh1 := (hu mist le_rfl).1 hp
        have hr : v.rk S K=w.rk S K := by
          rcases lt_trichotomy (v.rk S K) (w.rk S K) with hs|hs|hs
          · exact False.elim (lt_irrefl _ ((hu _ hp.le).mpr hs))
          · exact hs
          · exact False.elim (lt_irrefl _ ((hu _ hh1.le).mp hs))
        rw [hr]
      have hh1 : w.rk S K≤ mist:=le_of_not_gt (fun e=> hp ((hu mist le_rfl).2 e))
      rw [h.full _ ((le_of_not_gt hp).trans ht0),h.full _ (hh1.trans ht0)]
   by_cases hb:i∈F
   · unfold Blob.val Trio.eval; rw [hw]
     simp only [w,trim,ite_eq_left hb]
   have hp : mist≤theta/8 := by linarith [mistp,mist_shut ht]
   unfold Blob.val Trio.eval
   rw [h.shut _ (le_trans (hh i hi hb) hp),h.shut _ (show ((trim F v).ts i).1≤theta/8 from ?_)]
   · ring
   simp only [trim,hb,ite_false]; change 0≤_
   linarith [mistp]

end
end ExactDerandomization.Buf

end

section

/-! Compression run, preloss and beginning of the comparison. -/
namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

structure Run where
    L : ℕ
    S : Domain
    K : ℕ
    n : ℕ→ℕ
    rho : ℕ→ℝ
    inc : ℕ→Row
    aim : Row

namespace Run
variable (r : Run)
abbrev pm (i : ℕ) : Params := ⟨r.S,r.K,r.n i,r.rho i⟩

def pile (r:Run) : ℕ→Row
 | 0=>0
 | i+1=>r.pile i+r.inc i
def shifted (i : ℕ) (v : Blob) : Blob := ⟨v.base,v.ts+r.inc i⟩
def mid (r:Run) : ℕ→Blob
 | 0=>⟨0,0⟩
 | i+1=>(r.pm i).push (r.shifted i (r.mid i))
def enter (i) := r.shifted i (r.mid i)
lemma mid_succ (i) : r.mid (i+1)=(r.pm i).push (r.enter i) := rfl
def loss (i) := (r.mid i).ts-r.pile i
lemma total_enter (i x : ℕ) :
    (r.enter i).ts x=r.pile (i+1) x+r.loss i x := by
   simp only [enter,shifted,pile,loss,Pi.add_apply,Pi.sub_apply]
   abel
lemma iter_loss (i x) :
    r.loss (i+1) x=r.loss i x+((r.mid (i+1)).ts x-(r.enter i).ts x) := by
   rw [r.total_enter]; unfold loss; simp only [Pi.sub_apply]; abel

def epi (i x : ℕ) :=
   let p:=r.aim x
   let q:=r.pile (i+1) x
   min 1 (max (|q.1-p.1|/(1+p.1)) |q.2-p.2|)
def bad (i) := rank r.S (r.epi i) 0
lemma epi_nn (i x) : 0≤r.epi i x := le_min zero_le_one (le_trans (abs_nonneg _) (le_max_right ..))
lemma bad_epi (i) {x} (h:x∈r.S) : r.epi i x ≤ r.bad i := by
   obtain he|he:=(r.epi_nn i x).eq_or_lt
   · rw [← he]; apply rank_nn
   · apply (rank_ge he).2
     exact card_pos.mpr ⟨x,mem_filter.2 ⟨h,le_rfl⟩⟩
lemma bad_nn (i) : 0≤r.bad i := rank_nn ..

def dust (j) := ∑ i ∈ range j, 6*r.rho i
def rain (j) := ∑ i ∈ range j, 24/small*r.rho i*r.bad i
def overflow (i : ℕ) : Prop := r.rho i < (r.pm i).U (r.enter i)
def pre (i : ℕ) := ∀ j< i,¬r.overflow j

structure Good (r:Run) : Prop where
    pos : ∀ i < r.L, 0<r.rho i
    tiny : r.dust r.L≤ small
    ahead : ∀ i<r.L, r.dust i≤r.rho i/100
    cap : ∀ i<r.L, r.K ≤ r.n i
    target_nn : ∀ i∈r.S, 0≤(r.aim i).1
    target_s : ∀ i∈r.S, |(r.aim i).2|≤zeta
    target_flat : ∀ i∈r.S, (r.aim i).1≤ small → (r.aim i).2=0

lemma base_mid (i) : 0≤(r.mid i).base ∧ (r.mid i).base≤4 := by
  cases i with
  | zero=>simp [mid]
  | succ i=>exact ⟨Params.Z_nn ..,(Params.Z_w ..).2.2⟩
lemma dust_nn (h:r.Good) {i} (he:i≤r.L) : 0 ≤ r.dust i :=
   sum_nonneg fun j hj=>mul_nonneg (by norm_num) (le_of_lt (h.pos _ (lt_of_lt_of_le (mem_range.1 hj) he)))
lemma rain_nn (h:r.Good) {i} (he:i≤r.L) : 0 ≤ r.rain i :=
   sum_nonneg fun j hj=>by
      have ha:=h.pos _ (lt_of_lt_of_le (mem_range.1 hj) he)
      have he:=r.bad_nn j; have hs:=smallp
      positivity
lemma dust_le (h:r.Good) {i} (he:i≤r.L) : r.dust i≤ small := by
   apply le_trans _ h.tiny; unfold dust
   exact sum_le_sum_of_subset_of_nonneg (range_mono he) fun j hj _=>
      mul_nonneg (by norm_num) (h.pos _ (mem_range.1 hj)).le
lemma dust_next (i) : r.dust (i+1)=r.dust i+6*r.rho i := sum_range_succ ..
lemma rain_next (i) : r.rain (i+1)=r.rain i+24/small*r.rho i*r.bad i :=
   sum_range_succ ..

lemma rho_dust (h:r.Good) {i} (he:i<r.L) : 6*r.rho i≤ small := by
   have hh := r.dust_le h (i:=i+1) he
   have hl := r.dust_nn h he.le
   rw [r.dust_next] at hh; linarith
lemma rho_mist (h:r.Good) {i} (he:i<r.L) : r.rho i ≤ mist := by
  have ht:=h.pos i he; have hu := r.rho_dust h he
  unfold Buf.mist; linarith

lemma literal (h:r.Good) {i x} (he:x∈r.S) (hx:r.bad i < 1) :
   |(r.pile (i+1) x).1-(r.aim x).1|≤(1+(r.aim x).1)*r.bad i ∧
   |(r.pile (i+1) x).2-(r.aim x).2|≤r.bad i := by
   have hg:=r.bad_epi i he
   dsimp only [epi] at hg
   have hs: 0<1+(r.aim x).1 := by linarith [h.target_nn _ he]
   constructor
   · rw [mul_comm]; apply (div_le_iff₀ hs).1; grind
   · grind

/-- preloss biggest bound, until the first overflow -/
lemma pre_head (h:r.Good) {i} (hh:i≤r.L) (hp:r.pre i) :
   (r.mid i).base≤r.dust i ∧ ∀ x∈r.S, ht (r.loss i x) ≤ r.dust i := by
   induction i with
   | zero=>simp [mid,dust,ht,loss,pile]
   | succ i ih=>
     obtain ⟨hb,hx⟩:= ih (by omega) (fun j hj=>hp j (by omega))
     have he : (r.pm i).U (r.enter i)≤r.rho i :=
        le_of_not_gt (hp i (Nat.lt_add_one _))
     rw [r.dust_next]
     constructor
     · rw [r.mid_succ]; change (r.pm i).Z _≤_
       have hp : 0≤r.rho i := (h.pos _ hh).le
       have hh1:= ((r.pm i).Z_w (r.enter i)).2.1
       have hh2:=r.dust_nn h (i:=i) (by omega)
       linarith
     · intro x hi
       have hp := hx x hi
       rw [r.iter_loss]
       apply (ht_add ..).trans
       apply add_le_add hp
       rw [r.mid_succ]
       apply (ht_sub ..).2
       exact near_le (Params.perturb ..) (by linarith)

/-- At a significant position changed during preloss, the prefix made
definite relative error. -/
lemma flag (h:r.Good) {i x} (hi:i<r.L) (hp:r.pre i) (hx:x∈r.S)
    (hs:¬r.overflow i) (hh:4*small≤(r.aim x).1)
    (he : (r.mid (i+1)).ts x ≠ (r.enter i).ts x) :
    small/4 ≤ r.bad i := by
  let p:=r.enter i
  let z:=r.aim x
  let w:=r.pile (i+1) x
  have hv : ht (p.ts x) <3*r.rho i := by
    by_contra! hl
    exact he ((r.pm i).offbase (v:=p) (by
      have e : (r.pm i).U p≤r.rho i:=le_of_not_gt hs
      linarith))
  have hl:= le_trans ((r.pre_head h hi.le hp).2 x hx) (r.dust_le h hi.le)
  have hk:= r.rho_dust h hi
  have h0 := (r.total_enter i x)
  have h1 : w.1≤ 2*small := by
    have hu : |(p.ts x).1|≤ht (p.ts x):=le_max_left ..
    have htt : p.ts x=w+r.loss i x:=h0
    obtain ⟨hy,hx'⟩ :=abs_le.1 (le_trans (show |(r.loss i x).1|≤Buf.ht (r.loss i x) from le_max_left ..) hl)
    rw [htt] at hu hv; simp only [Prod.fst_add] at hu
    have hf := le_abs_self (w.1+(r.loss i x).1)
    linarith [smallp]
  refine le_trans ?_ (r.bad_epi i hx)
  apply le_min
  · have :=mist1; unfold mist at *; linarith
  apply le_trans _ (le_max_left ..)
  change small/4≤ |w.1-z.1|/(1+z.1)
  have hz1: 4*small≤z.1:= hh
  have hp : 0< z.1 := by linarith [smallp]
  have hl1 : small ≤ 1 := by linarith [show 10*small<1 from mist1]
  rw [le_div_iff₀ (by linarith)]
  unfold small delta A at *; linarith [neg_le_abs (w.1-z.1)]

lemma pre_marks (h:r.Good) {i} (hh:i≤r.L) (hp:r.pre i) {x} (hx:x∈r.S)
    (he:4*small≤(r.aim x).1) :
    ht (r.loss i x)≤r.rain i := by
   induction i with
   | zero=>simp [ht,rain,loss,mid,pile]
   | succ i ih=>
     have hz : r.pre i:=fun j hj=>hp _ (by omega)
     have he1:=ih (by omega) hz
     have hs : ¬r.overflow i:=hp _ (by omega)
     rw [r.iter_loss,r.rain_next]
     apply le_trans (ht_add ..)
     apply add_le_add he1
     have h0:= h.pos i hh
     by_cases hn : (r.mid (i+1)).ts x=(r.enter i).ts x
     · rw [hn, sub_self]
       have hb := r.bad_nn i; have hh := smallp
       simp [ht]; positivity
     have hf:=r.flag h hh hz hx hs he hn
     have h2 : (r.pm i).U (r.enter i)≤r.rho i := le_of_not_gt hs
     apply le_trans (b:=6*r.rho i)
     · rw [r.mid_succ, ht_sub]; exact near_le (Params.perturb ..) (by linarith)
     · have hp:=smallp
       rw [div_mul_eq_mul_div,div_mul_eq_mul_div, le_div_iff₀ hp]
       have :=mul_le_mul_of_nonneg_left hf h0.le; unfold small delta A at *; linarith

def origin : Blob := ⟨0,r.aim⟩
def corrected (i : ℕ) : Blob := ⟨(r.mid i).base,r.aim+r.loss i⟩
lemma start_calm (h:r.Good) {i} (he : i≤r.L) (hp:r.pre i) :
    Calm r.S (r.corrected i) := by
   refine ⟨(r.base_mid i).1,(r.base_mid i).2,fun j hj=>?_⟩
   have hh := h.target_nn j hj; have hz := h.target_s j hj
   have hl := r.pre_head h he hp |>.2 j hj
   obtain ⟨h1,h2⟩:=max_le_iff.mp (le_trans hl (r.dust_le h he))
   simp only [corrected,Pi.add_apply,Prod.fst_add,Prod.snd_add]
   have hu:= (abs_le.mp h1).1
   have hp:=smallp
   constructor
   · unfold mist; linarith
   · refine le_trans (abs_add_le ..) ?_
     unfold zeta at hz; unfold mist; unfold small delta A at *; linarith

lemma rain_effect {theta C f} (h:r.Good) (he:TS theta C f) (hz:delta≤theta)
    {i} (hi : i≤r.L) (hp:r.pre i) {x} (hx:x∈r.S) :
    |fourth ((r.corrected i).val r.S r.K f x)-fourth (r.origin.val r.S r.K f x)| ≤
         3*C^3*r.rain i := by
   let F:=r.S.filter fun x=> 4*small≤(r.aim x).1
   have hh (x) (hx:x∈r.S) (he:x∉F) : (r.aim x).1< 4*small :=
         lt_of_not_ge fun hn=> he (mem_filter.2 ⟨hx,hn⟩)
   have hk := r.pre_head h hi hp
   have hv:=r.dust_le h hi; have hs:=smallp
   have he1 (j) (he:j∈r.S) : ht (r.loss i j)≤ small := le_trans (hk.2 _ he) hv
   have HF : suit r.S (r.rain i) (trim F (r.corrected i)) (trim F r.origin) := by
      have h0 :=r.rain_nn h hi
      refine ⟨by simp [trim,h0],fun j hj=>?_⟩
      by_cases hb:j∈F
      · simp only [trim,hb,ite_true,corrected,origin]
        rw [← ht_sub]; simp only [Pi.add_apply,add_sub_cancel_left]
        exact r.pre_marks h hi hp hj (mem_filter.1 hb).2
      simp only [trim,hb,ite_false]; exact near_self h0
   rw [trim_safe he hz _ F (v:=r.corrected i) ?_ ?_ _ hx,trim_safe he hz _ F (v:=r.origin) ?_ ?_ _ hx]
   · refine suit_val he HF _ hx
   · exact show 0≤ mist from mistp.le
   · intro i hj hi
     have := hh i hj hi; change (r.aim i).1≤ mist
     unfold mist; linarith
   · change (r.mid i).base≤ mist; unfold mist; linarith [hk.1]
   · intro j hj hi
     change ((r.aim+r.loss i) j).1≤ mist
     simp only [Pi.add_apply,Prod.fst_add]
     have h2 := le_trans (le_trans (le_abs_self _) (show |(r.loss i j).1|≤ht (r.loss i j) from le_max_left ..)) (he1 j hj)
     unfold mist; linarith [hh j hj hi]

end Run
end
end ExactDerandomization.Buf

end

section

/-! Clamped row run. Since U is capped, the actual row is allowed a
shutdown test, discarding the real slots upon detecting U>1. -/
namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

lemma suit_map {S L R v w} (_ : 0≤L) (he : L≤R)
    (h:suit S 0 (struck R v) (struck R w)) :
    suit S 0 (struck L v) (struck L w) := by
  obtain ⟨hs,ht⟩:=suit0 h
  refine ⟨by change |v.base-w.base|≤0; change v.base=w.base at hs; rw [hs]; simp,fun i hi=>?_⟩
  have hc := ht _ hi
  have hz {p} : clp L (clp R p)=clp L p := by
     apply Prod.ext <;>
       exact sandwich (by linarith) he _
  change clp R (v.ts i)=clp R (w.ts i) at hc
  change near _ (clp L _) (clp L _)
  rw [← hz (p:=v.ts i),← hz (p:=w.ts i),hc]; exact near_self le_rfl

lemma suit_idem (S : Domain) (v : Blob) (L R : ℝ) (he:L≤R) :
    suit S 0 (struck L (struck R v)) (struck L v) := by
   refine ⟨by change |v.base-v.base|≤0; simp, fun i hi=>?_⟩
   have hh (p:Pt) : clp L (clp R p)=clp L p := by apply Prod.ext <;> exact sandwich (by linarith) he _
   change near _ (clp L (clp R _)) _
   rw [hh]; exact near_self le_rfl

lemma suit0_trans {S u v w} (h:suit S 0 u v) (e:suit S 0 v w) : suit S 0 u w := by
   obtain ⟨hb,ht⟩:=suit0 h; obtain ⟨he,hf⟩:=suit0 e
   refine ⟨by rw [hb,he]; simp,fun i hi=>?_⟩
   rw [ht _ hi,hf _ hi]; exact near_self le_rfl
lemma suit0_symm {S u v} (h:suit S 0 u v) : suit S 0 v u := by
   obtain ⟨hb,ht⟩:=suit0 h
   refine ⟨by rw [hb]; simp,fun i hi=>?_⟩
   rw [ht _ hi]; exact near_self le_rfl

namespace Run
variable (r : Run)
def die (v : Blob) : Blob := ⟨v.base,fun _=>line v.base⟩
def actual (r : Run) (R : ℕ→ℝ) (kap : ℕ→Bool) : ℕ→Blob
   | 0=>r.mid 0
   | i+1=>
     let w:=struck (R i) ((r.pm i).push (r.shifted i (r.actual R kap i)))
     if kap i then die w else w
abbrev taken (i : ℕ) (v : Blob) (R:ℝ) (b:Bool) :=
  let w:=struck R ((r.pm i).push (r.shifted i v))
  if b then die w else w
lemma actual_push (R kap i) : r.actual R kap (i+1)=r.taken i (r.actual R kap i) (R i) (kap i) := rfl
lemma actual_base (R kap i) :
 (r.actual R kap (i+1)).base=(r.pm i).Z (r.shifted i (r.actual R kap i)) := by
   rw [r.actual_push]; unfold taken; split <;> rfl
lemma actual_closed (R kap i) :
   0≤(r.actual R kap i).base ∧ (r.actual R kap i).base≤4 := by
   cases i with
   | zero=>exact r.base_mid _
   | succ i=>rw [r.actual_base]; exact ⟨Params.Z_nn ..,(Params.Z_w ..).2.2⟩

def bridged (L:ℝ) (v w:Blob) :=
    suit r.S 0 (struck L v) (struck L w) ∨ 1≤v.base∧ 1≤w.base

lemma cross_zero {L H i v w} (h:suit r.S 0 (struck H v) (struck H w))
    (hp : 0≤L) (he:∀ j∈r.S, ht (r.inc i j)+L ≤ H) :
    suit r.S 0 (struck L (r.shifted i v)) (struck L (r.shifted i w)) := by
   refine ⟨h.1,fun j hj=>?_⟩
   have hf := (suit0 h).2 j hj
   have hx := he j hj
   let d:=r.inc i j; change ht d+L≤H at hx
   have ha : sat H (v.ts j).1=sat H (w.ts j).1:=congrArg Prod.fst hf
   have hb : sat H (v.ts j).2=sat H (w.ts j).2:=congrArg Prod.snd hf
   have hg : clp L (v.ts j+d)=clp L (w.ts j+d) :=
      Prod.ext (sat_add (by unfold ht at hx; grind) ha hp) (sat_add (by unfold ht at hx; grind) hb hp)
   change near _ (clp L (v.ts j+d)) (clp L (w.ts j+d))
   rw [hg]; exact near_self le_rfl

lemma next_bridge {R kap i L H} (h: r.bridged H (r.mid i) (r.actual R kap i))
    (hs : 12≤L) (hh : L≤R i) (he:∀ j∈r.S,ht (r.inc i j) + L≤H)
    (hp : kap i=true → 1≤(r.pm i).U (r.shifted i (r.actual R kap i))) :
    r.bridged L (r.mid (i+1)) (r.actual R kap (i+1)) := by
    rcases h with h|⟨h,h'⟩
    · let p:=r.pm i; let v:=r.enter i; let w:=r.shifted i (r.actual R kap i)
      have hz := r.cross_zero h (by linarith) he
      change suit r.S 0 (struck L v) (struck L w) at hz
      have h1:=Params.smooth_push (r.pm i) hz
      have hv : v.base ≤4:=(r.base_mid i).2
      have hw : w.base ≤4:=(r.actual_closed R kap i).2
      rw [← strike_push p v L hs hv, ← strike_push p w L hs hw] at h1
      have hC : suit r.S 0 (struck L (r.mid (i+1))) (struck L (p.push w)) :=
              by rw [mul_zero] at h1; rw [r.mid_succ]; exact h1
      by_cases hd:kap i=true
      · right
        rw [r.actual_base]; change 1≤(r.mid (i+1)).base ∧ 1≤p.Z w
        have hs1 : 1≤p.Z w:=le_trans (hp hd) (p.Z_w w).1
        have hs2 : (r.mid (i+1)).base=p.Z w:=(suit0 hC).1
        rw [hs2]; exact ⟨hs1,hs1⟩
      left
      rw [r.actual_push]; dsimp only [taken]; rw [ite_eq_right hd]
      exact suit0_trans hC (suit0_symm (suit_idem _ _ _ _ hh))
    · right
      rw [r.actual_base,r.mid_succ]
      let p:=r.pm i
      refine ⟨le_trans ?_ (p.Z_w _).1,le_trans ?_ (p.Z_w _).1⟩
      · exact h.trans (p.U_old (v:=r.enter i) (r.base_mid i).2)
      exact h'.trans (p.U_old (v:=r.shifted i (r.actual R kap i)) (r.actual_closed R kap i).2)

theorem clamped {R kap theta C f} (h:TS theta C f) (he:theta≤1)
    (H : ℕ→ℝ) (hb : ∀ j≤r.L,C≤ H j ∧12 ≤ H j)
    (hz : ∀ i<r.L,H (i+1)≤R i)
    (hh : ∀ i<r.L,∀ j∈r.S, ht (r.inc i j) + H (i+1) ≤ H i)
    (hp : ∀ i<r.L,kap i=true → 1≤(r.pm i).U (r.shifted i (r.actual R kap i)))
    {i} (hi:i∈r.S) :
   (r.actual R kap r.L).val r.S r.K f i=(r.mid r.L).val r.S r.K f i := by
   have h1 (j) (he:j≤r.L) : r.bridged (H j) (r.mid j) (r.actual R kap j) := by
     induction j with
     | zero=> exact Or.inl (suit_self _ _ _ le_rfl)
     | succ j ih=>
       exact r.next_bridge (ih (by omega)) (hb _ he).2
           (hz j he) (hh j he) (hp j he)
   obtain ⟨h2,h3⟩:=hb r.L le_rfl
   rcases h1 r.L le_rfl with hs|⟨hs,hk⟩
   · obtain ⟨hV,ht⟩:=suit0 hs
     have hU:=suit_rk hs r.K
     let L:=H r.L
     have hv : (r.actual R kap r.L).base≤ H r.L := by linarith [(r.actual_closed R kap r.L).2]
     have hw : (r.mid r.L).base≤ H r.L := by linarith [(r.base_mid r.L).2]
     have hg := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hU (abs_nonneg _)))
     rw [← strike_val h _ _ _ L h2 hv,← strike_val h _ _ _ L h2 hw]
     unfold Blob.val; dsimp only [L]; rw [hg,ht _ hi]
   · rw [closed h (show theta/40≤ (r.actual R kap r.L).base from by linarith),
         closed h (show theta/40≤(r.mid r.L).base from by linarith)]

end Run

namespace Params
variable (p : Params)

lemma enough {B : Domain} {v : Blob} (h:p.U v<4) (hh:B⊆p.S)
    (hs : ∀ i∈B,p.U v<ht (v.ts i)) :
    B.card ≤ p.n := by
   have he : rank p.S (fun i=>ht (v.ts i)) p.n ≤ p.U v := by unfold U at *; grind
   by_contra! hn
   have hg : B⊆ p.S.filter (fun i=>p.U v<ht (v.ts i)) :=
     fun i hi => mem_filter.2 ⟨hh hi,hs i hi⟩
   exact not_lt_of_ge he ((rank_gt (p.U_nn v)).2 (lt_of_lt_of_le hn (card_le_card hg)))

lemma listed {B : Domain} {v : Blob} (L : ℝ) (hl:4≤L)
    (hh : ∀ i∈p.S,2*p.U v<ht (v.ts i) → i∈B)
    {i} (hi:i∈p.S) (hj:i∉B) :
    (struck L (p.push v)).ts i=line ((struck L (p.push v)).base) := by
   have hs : ht (v.ts i) ≤2*p.U v:=le_of_not_gt fun e=>hj (hh _ hi e)
   have hp :=(p.Z_w v).2.2; have hn :=p.Z_nn v
   change clp L ((p.push v).ts i)=line (p.Z v)
   rw [p.nearbase hs]
   exact Prod.ext (sat_id (x:=p.Z v) (by rw [abs_of_nonneg hn]; linarith)) (sat_id (x:=0) (by rw [abs_zero]; linarith))

end Params
end
end ExactDerandomization.Buf

end

section

namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

lemma Blobext {v w : Blob} (h:v.base=w.base) (g:∀ i,v.ts i=w.ts i) : v=w := by
   cases v; cases w
   simp only [Blob.mk.injEq]; exact ⟨h,funext g⟩

/-- A comparison replacing very positive first coordinates by a bounded
comparison sentinel. -/
def ears (F : Domain) (L : ℝ) (v : Blob) : Blob :=
    ⟨v.base, fun x=> if x∈F then (L,(v.ts x).2) else v.ts x⟩
def tall (F : Domain) (L : ℝ) (v : Blob) := ∀ i∈F,L≤(v.ts i).1

lemma tower_struck {F L v} (h:tall F L v) (hh:0≤L) :
    struck L (ears F L v)=struck L v := by
   refine Blobext (v:=struck L (ears F L v)) (w:=struck L v) rfl ?_
   intro i
   unfold struck ears
   by_cases hi:i∈F
   · have hv:=h i hi
     have h1 : -L ≤ (v.ts i).1 := by linarith
     have h2 : sat L (v.ts i).1=L:=by unfold sat clip; grind
     have hs : sat L L=L := sat_id (le_of_eq (abs_of_nonneg hh))
     simp [clp,h2,hi,hs]
   simp [hi]
lemma towering {F L v} (h:tall F L v) (hh : 12≤L) (p : Params)
    {i} (hi:i∈F) : (p.push v).ts i=v.ts i := by
  apply p.offbase
  have hu:=p.U_four v
  have hv := h i hi
  unfold ht; grind
lemma tower_push {F L v} (h:tall F L v) (hh:12≤L) (hv:v.base≤4) (p : Params) :
    p.push (ears F L v)=ears F L (p.push v) := by
   let u:=ears F L v
   have h0:=tower_struck h (by linarith)
   have hb : u.base ≤4:=hv
   have heZ : p.Z u=p.Z v := calc
      _ = _ := (strike_Z p u _ hh hb).symm
      _ = p.Z v := by change p.Z (struck L (ears F L v))=p.Z v; rw [h0,strike_Z p v _ hh hv]
   have heU : p.U u=p.U v := calc
      _ = _ := (strike_U p u L (by linarith)).symm
      _ = p.U v := by change p.U (struck L (ears F L v))=p.U v; rw [h0,strike_U p v L (by linarith)]
   have ht:tall F L u:= by intro i hi; simp [u,ears,hi]
   apply Blobext heZ
   intro i; change (p.push u).ts i=_
   by_cases hi:i∈F
   · rw [towering ht hh _ hi]
     simp only [u,ears,hi,ite_true,towering h hh _ hi]
   have hg : u.ts i=v.ts i:=by simp [u,ears,hi]
   change (p.push u).ts i = if _ then _ else _
   rw [ite_eq_right hi]
   dsimp only [Params.push]
   rw [heZ,heU,hg]
lemma tower_val {F L v theta C f} (h:tall F L v) (hh:12≤L)
    (hv:v.base≤4) (hs:TS theta C f) (he:C≤L) (S K i) :
    (ears F L v).val S K f i=v.val S K f i := by
   have hh1 : v.base≤L:= by linarith
   rw [← strike_val hs S K i L he (show (ears F L v).base≤L from hh1),tower_struck h (by linarith),
        strike_val hs S K i L he hh1]

namespace Run
variable (r : Run)
def wide (B : ℝ) : Domain := r.S.filter fun x=>4*B < (r.aim x).1

def steady (r : Run) (j : ℕ) : ℕ → Blob
   | 0=> r.corrected j
   | i+1=> if j≤ i then (r.pm i).push (r.steady j i) else r.corrected j
lemma steady_zero (j) : r.steady j j=r.corrected j := by cases j <;> simp [steady]
lemma steady_push {i j} (he : j≤ i) :
    r.steady j (i+1) = (r.pm i).push (r.steady j i) := by rw [steady,ite_eq_left he]

lemma still_here_c (h:r.Good) {i j} (hi : j≤ i) (hj:i≤r.L) (hp:r.pre j) :
    Calm r.S (r.steady j i) := by
   induction i,hi using Nat.le_induction with
   | base=> rw [r.steady_zero]; exact r.start_calm h hj hp
   | succ i hi ih=> rw [r.steady_push hi]; exact (r.pm i).still_calm (ih (by omega))

lemma still_here {theta C f} (h:r.Good) (ht:TS theta C f) (hs: delta≤theta)
    (hh:theta≤1) {j i} (hi:j≤ i) (he:i≤r.L) (hp:r.pre j) (x) :
    (r.steady j i).val r.S r.K f x=(r.corrected j).val r.S r.K f x := by
  induction i,hi using Nat.le_induction with
  | base=>rw [r.steady_zero]
  | succ i hi ih=>
    have ht1:=ih (by omega)
    rw [r.steady_push hi, ← ht1]
    exact (r.pm i).motionless ht hs hh (r.still_here_c h hi (by omega) hp)
             (r.rho_mist h he) (h.cap i he) x

lemma still_hi (h:r.Good) {j i B} (hi:j≤ i) (he:i≤r.L) (hp:r.pre j) (hh:12≤B) :
    tall (r.wide B) B (r.steady j i) := by
  induction i,hi using Nat.le_induction with
  | base=>
    rw [r.steady_zero]; intro i hi
    obtain ⟨ha,hb⟩:=mem_filter.1 hi
    have he1:= le_trans ((r.pre_head h he hp).2 i ha) (r.dust_le h he)
    have hp := show small ≤ 1 from by linarith [show 10*small<1 from mist1]
    have hs := (abs_le.1 (max_le_iff.mp he1).1).1
    simp only [corrected,Pi.add_apply,Prod.fst_add]
    linarith
  | succ i hi ih=>
    rw [r.steady_push hi]
    intro t ht; rw [towering (ih (by omega)) hh _ ht]
    exact ih (by omega) t ht

/-- Known large first values don't cross the capped thresholds when
relative prefix errors are small. Keep track of the discrepancy from
the raw prefix at such locations. -/
def Mild (j) := ∀ i, j≤ i → i<r.L → r.bad i≤1/4

lemma enter_tall (h:r.Good) {j i B} (hi : j≤ i) (he:i<r.L) (hp:r.pre j)
    (hh:12 ≤ B) (hm:r.Mild j) :
    tall (r.wide B) B (r.enter i) ∧ ∀ x∈r.wide B,r.loss i x=r.loss j x := by
   have up (k) (hs:j≤k) (hi:k<r.L) {x} (hx:x∈r.wide B) (ht:r.loss k x=r.loss j x) :
       B ≤ ((r.enter k).ts x).1 := by
      obtain ⟨ha,hb⟩:=mem_filter.1 hx
      have hL := le_trans ((r.pre_head h (i:=j) (by omega) hp).2 x ha) (r.dust_le h (by omega))
      have h0 := hm k hs hi
      have hl:= r.literal h (i:=k) ha (by linarith)
      have h1 := show small≤1 from by linarith [show 10*small<1 from mist1]
      have hz := (abs_le.mp hl.1).1
      rw [r.total_enter,ht]
      have hv := (abs_le.mp (max_le_iff.mp hL).1).1
      simp only [Prod.fst_add]
      nlinarith [mul_le_mul_of_nonneg_left h0 (show 0≤(1+(r.aim x).1) from by linarith)]
   induction i,hi using Nat.le_induction with
   | base=> exact ⟨fun _ hx=> up j le_rfl he hx rfl,fun _ _=>rfl⟩
   | succ i hi ih=>
     obtain ⟨ha,hb⟩:=ih (by omega)
     have hc (x) (hx:x∈r.wide B) : r.loss (i+1) x=r.loss j x := by
        rw [r.iter_loss, r.mid_succ,towering ha hh _ hx,sub_self,add_zero,hb x hx]
     exact ⟨fun x hx=>up (i+1) (by omega) he hx (hc x hx),hc⟩

end Run
end
end ExactDerandomization.Buf

end

section

/-! Comparison using the relative prefix errors, beginning at group j. -/
namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

def hood (F : Domain) (v : Row) : Row :=
   fun i=>if i∈F then (0,(v i).2) else v i
def blast (F : Domain) (i : ℕ) (t : Pt) : Pt :=
   if i∈F then (0,t.2) else t
lemma blast_apply (F v i) : hood F v i = blast F i (v i) := rfl
lemma blast_add (F i x y) : blast F i (x+y)=blast F i x+blast F i y := by
   by_cases h:i∈F <;> simp [blast,h]
lemma blast_sub (F i x y) : blast F i (x-y)=blast F i x-blast F i y := by
   by_cases h:i∈F <;> simp [blast,h]
lemma hooded {F L v w i} :
    (ears F L v).ts i - (ears F L w).ts i = blast F i (v.ts i-w.ts i) := by
   by_cases h:i∈F
   · simp [ears,h,blast]
   · simp [ears,h,blast]

namespace Run
variable (r : Run)

/-- Absolute bounds when ears are sentinels. -/
abbrev wideK (B : ℝ) := 1+4*B
lemma hood_at (h:r.Good) {j B i} (he : j≤ i) (hi : i<r.L)
    (hh:12≤B) (hm:r.Mild j) {x} (hx:x∈r.S) :
    ht (blast (r.wide B) x (r.pile (i+1) x-r.aim x)) ≤ wideK B*r.bad i := by
   have hb:= hm i he hi
   obtain ⟨hp,hq⟩:= r.literal h (i:=i) hx (by linarith)
   have hr:=r.bad_nn i
   have ht1 : r.bad i ≤ wideK B*r.bad i := by unfold wideK; nlinarith
   by_cases hz:x∈r.wide B
   · unfold blast; rw [ite_eq_left hz]; change max |(0:ℝ)| |_-_| ≤ _
     rw [max_le_iff]
     exact ⟨by rw [abs_zero]; linarith,hq.trans ht1⟩
   have hu : (r.aim x).1≤4*B := le_of_not_gt fun e=>hz (mem_filter.2 ⟨hx,e⟩)
   unfold blast; rw [ite_eq_right hz,ht_sub]
   exact ⟨hp.trans (mul_le_mul_of_nonneg_right (by unfold wideK; grind) hr),hq.trans ht1⟩

lemma hood_prev (h:r.Good) {j B i} (he : j≤ i) (hi : i+1<r.L)
    (hh:12≤B) (hm:r.Mild j) {x} (hx:x∈r.S) :
    ht (blast (r.wide B) x (r.inc (i+1) x)) ≤ wideK B*(r.bad i + r.bad (i+1)) := by
   have hd : r.inc (i+1) x=(r.pile (i+1+1) x-r.aim x)-(r.pile (i+1) x-r.aim x) := by

      rw [show r.pile (i+1+1) x=r.pile (i+1) x+r.inc (i+1) x from rfl]; abel
   have hp := r.hood_at h he (by omega) hh hm hx
   have hv := r.hood_at h (i:=i+1) (by omega) hi hh hm hx
   have hg := near_sub ((ht_near ..).1 hv) ((ht_near ..).1 hp)
   rw [hd, blast_sub,add_comm (r.bad i),mul_add]
   exact (ht_near ..).2 (by simpa only [sub_zero] using hg)

lemma hood_init (h:r.Good) {j B} (he : j<r.L) (hh:12≤B) (hm:r.Mild j) :
    suit r.S (wideK B*r.bad j)
      (ears (r.wide B) B (r.enter j))
      (ears (r.wide B) B (r.steady j j)) := by
   rw [r.steady_zero]; have hb:=r.bad_nn j
   have hK : 0<wideK B := by unfold wideK; linarith
   refine ⟨?_,fun x hx=>?_⟩
   · change |(r.mid j).base-(r.mid j).base| ≤ _
     simp; positivity
   · rw [← ht_sub,hooded,r.total_enter]
     simp only [corrected,Pi.add_apply,add_sub_add_right_eq_sub]
     exact r.hood_at h le_rfl he hh hm hx

lemma hood_link {j B v w b c i} (_:i=j)
    (h : suit r.S b (ears (r.wide B) B v) (ears (r.wide B) B w))
    (hc:0≤c) (e : ∀ x∈r.S,ht (blast (r.wide B) x (r.inc i x))≤c) :
    suit r.S (b+c) (ears (r.wide B) B (r.shifted i v))
                                  (ears (r.wide B) B w) := by
  refine ⟨le_trans h.1 (by linarith),fun x hx=>?_⟩
  have hs:= (ht_sub ..).mpr (h.2 x hx)
  rw [hooded] at hs
  rw [← ht_sub,hooded]
  simp only [shifted,Pi.add_apply]
  rw [show v.ts x+r.inc i x-w.ts x=(v.ts x-w.ts x)+r.inc i x by abel,blast_add]
  exact le_trans (ht_add ..) (add_le_add hs (e x hx))

/-- Envelope for propagation coefficient. -/
def cloud (j i) := ∑ k ∈ Ico j (i+1),(32:ℝ)^(i-k)*r.bad k
def tail (j) := ∑ k ∈ Ico j r.L,(32:ℝ)^(r.L-k)*r.bad k
lemma cloud_adj {i j} (_:j≤ i) :
   (∑ k ∈ Ico j (i+1),(32:ℝ)^(i+1-k)*r.bad k) = 32*r.cloud j i := by
  unfold cloud; rw [mul_sum]
  apply sum_congr rfl; intro k hk
  have he : i+1-k=i-k+1 := by obtain ⟨a,b⟩:=mem_Ico.mp hk; omega
  rw [he,pow_succ]; ring
lemma cloud0 (j) : r.cloud j j=r.bad j := by simp [cloud]
lemma cloud_step {j i} (h : j≤ i) : r.cloud j (i+1)=32*r.cloud j i+r.bad (i+1) := by
   rw [cloud,sum_Ico_succ_top (a:=j) (b:=i+1) (by omega),r.cloud_adj h]
   simp
lemma cloud_bad {j i} (he : j≤ i) : r.bad i≤r.cloud j i := by
   have ht : ∀ k : ℕ,0≤(32:ℝ)^(i-k)*r.bad k:=fun k=>mul_nonneg (by positivity) (r.bad_nn _)
   unfold cloud
   simpa using (single_le_sum (fun k (_ : k∈Ico j (i+1))=>ht k) (mem_Ico.mpr ⟨he,Nat.lt_succ_self i⟩))
lemma tail_bad {j i} (he:j≤ i) (hh:i<r.L) : r.bad i≤r.tail j := by
   have ht : ∀ k : ℕ,0≤(32:ℝ)^(r.L-k)*r.bad k:=fun k=>mul_nonneg (by positivity) (r.bad_nn _)
   have h0 : 1 ≤ (32:ℝ)^(r.L-i) := one_le_pow₀ (by norm_num)
   apply le_trans (b:=(32:ℝ)^(r.L-i)*r.bad i)
   · nlinarith [r.bad_nn i]
   exact single_le_sum (fun k hi=>ht k) (mem_Ico.mpr ⟨he,hh⟩)

lemma hood_cmp (h:r.Good) {i j B} (he:j≤ i) (hL:i<r.L)
    (hh:12≤B) (hp:r.pre j) (hm:r.Mild j) :
    suit r.S (wideK B*r.cloud j i) (ears (r.wide B) B (r.enter i))
          (ears (r.wide B) B (r.steady j i)) := by
   have hz : 0<wideK B:=by unfold wideK; linarith
   induction i,he using Nat.le_induction with
   | base=>rw [r.cloud0]; exact r.hood_init h hL hh hm
   | succ i hi ih=>

     have he1 : i < r.L := by omega
     have h1:=ih he1
     let p:=r.pm i; let u:=r.enter i; let v:=r.steady j i
     have h2:=Params.smooth_push p h1
     have ht0: u.base≤4 := r.base_mid i |>.2
     have ht1: v.base≤4 := r.still_here_c h hi he1.le hp |>.2.1
     rw [tower_push (r.enter_tall h hi he1 hp hh hm).1 hh ht0 p,
         tower_push (r.still_hi h hi he1.le hp hh) hh ht1 p] at h2
     rw [r.steady_push hi]; unfold enter
     rw [r.mid_succ]
     have hn := r.bad_nn i; have hn2 := r.bad_nn (i+1)
     have hb := r.hood_link (i:=i+1) rfl h2
             (show 0≤wideK B*(r.bad i+r.bad (i+1)) from by positivity)
             (fun x hx=> r.hood_prev h hi hL hh hm hx)
     have hz : 30*(wideK B*r.cloud j i)+wideK B*(r.bad i+r.bad (i+1))≤wideK B*r.cloud j (i+1) := by
        rw [r.cloud_step hi]
        nlinarith [mul_le_mul_of_nonneg_left (r.cloud_bad hi) hz.le]
     exact ⟨le_trans hb.1 hz,fun x hx=>near_le (hb.2 x hx) hz⟩

/-- Final pointwise estimate after starting before group j. -/
abbrev charge (C : ℝ) := 16*C^3 * wideK (C+12)
set_option maxHeartbeats 500000 in
lemma wave {theta C f} (h:r.Good) (ht:TS theta C f) (hz:delta≤theta)
    (hc:theta≤1) {j} (he:j<r.L) (hp:r.pre j) {x} (hx:x∈r.S) :
    |fourth ((r.mid r.L).val r.S r.K f x)-fourth (r.origin.val r.S r.K f x)| ≤
         charge C*(r.rain j+r.tail j) := by
   let B:=C+12
   have hC:= ht.start.one
   have h0 : 12≤B := by dsimp [B]; linarith
   have hC0 : C≤B := by dsimp [B]; linarith
   have hC3 : 0<C^3 := pow_pos (by linarith) _
   have hwp : 1 ≤ wideK B := by unfold wideK; linarith
   have hz0 : 4*C^3 ≤ charge C := by change 4*C^3 ≤ 16*C^3*wideK B; nlinarith
   have hRain :=r.rain_nn h he.le
   rcases le_total (r.tail j) (1/4) with hu|hu
   · have hm : r.Mild j:= fun i hi hh=>le_trans (r.tail_bad hi hh) hu
     let i:=r.L-1
     have he0 : r.L=i+1:=by unfold i; omega
     have hi0 : j≤ i:=by omega
     have hi : i<r.L:=by omega
     let p:=r.pm i
     have hh:=Params.smooth_push p (r.hood_cmp h hi0 hi h0 hp hm)
     obtain ⟨ha,_⟩:=r.enter_tall h hi0 hi hp h0 hm
     have hb:=r.still_hi h hi0 hi.le hp h0
     have hb1 := (r.still_here_c h hi0 hi.le hp).2.1
     rw [tower_push ha h0 (r.base_mid i).2 p, tower_push hb h0 hb1 p] at hh
     have Hg (v : Blob) (h:tall (r.wide B) B v) :
         (ears (r.wide B) B (p.push v)).val r.S r.K f x = (p.push v).val r.S r.K f x :=
        tower_val (fun i hi=>by rw [towering h h0 p hi]; apply h i hi)
                    h0 (p.Z_w v).2.2 ht hC0 _ _ _
     have h1:= suit_val ht hh r.K hx
     rw [Hg _ ha,Hg _ hb,show p.push (r.enter i)=r.mid (i+1) from (r.mid_succ i).symm,
           show p.push (r.steady j i)=r.steady j (i+1) from (r.steady_push hi0).symm,
           ← he0,r.still_here h ht hz hc he.le le_rfl hp] at h1
     have he2 : r.tail j=32*r.cloud j i := by
        unfold tail; conv_lhs => rw [he0]
        exact r.cloud_adj hi0
     have h2:= r.rain_effect h ht hz he.le hp hx
     have h3 := le_trans (abs_sub_le ((fourth ((r.mid r.L).val r.S r.K f x)))
                              (fourth ((r.corrected j).val r.S r.K f x))
                              (fourth (r.origin.val r.S r.K f x))) (add_le_add h1 h2)
     have hcn := le_trans (r.bad_nn i) (r.cloud_bad hi0)
     rw [he2]; apply le_trans h3
     rw [mul_add]
     change _≤16*C^3*wideK B*(r.rain j)+16*C^3*wideK B*(32*r.cloud j i)
     rw [add_comm (16*C^3*wideK B*(r.rain j))]
     apply add_le_add
     · have hx : 0≤C^3*wideK B*r.cloud j i := mul_nonneg (mul_nonneg hC3.le (by linarith)) hcn
       linarith
     · exact mul_le_mul_of_nonneg_right (by change _≤charge C; linarith) hRain
   · have hl (v : Blob) : 0≤fourth (v.val r.S r.K f x) ∧ fourth (v.val r.S r.K f x)≤C^3 :=
          ⟨fourth_nn _, ht.rootub ..⟩
     obtain ⟨hl1,hl2⟩:=hl (r.mid r.L); obtain ⟨hh1,hh2⟩:=hl r.origin
     apply le_trans (b:=C^3)
     · rw [abs_le]; constructor <;> linarith
     nlinarith

end Run
end
end ExactDerandomization.Buf

end

section

namespace ExactDerandomization.Buf
noncomputable section
open Analysis At Hie Finset

namespace Run
variable (r : Run)
def fatties (j : ℕ) := r.S.filter (fun x=> r.rho j/4<(r.aim x).1)
def binge (j : ℕ) : Prop := r.n j ≤ 2*(r.fatties j).card
def hap (j : ℕ) : Prop := r.pre j∧r.overflow j

lemma fake (h:r.Good) {j} (hi:j<r.L) (hp:r.hap j) (hh:¬r.binge j) :
    (r.n j:ℝ)/2*(r.rho j/8)^4 ≤ ∑ i∈r.S,(r.epi j i)^4 := by
   let u:=r.rho j
   have hu : 0<u := h.pos j hi
   have hu1 : u≤1 := le_trans (r.rho_mist h hi) mist1.le
   let v:=r.enter j
   obtain ⟨hp,hm⟩:=hp
   let F:=r.S.filter (fun x=>u<ht (v.ts x))
   let T:=F\r.fatties j
   obtain ⟨hs,hl⟩:=r.pre_head h hi.le hp
   have hq := h.ahead j hi
   have hx : v.base<u := by
      change (r.mid j).base<r.rho j
      change 0<r.rho j at hu; linarith
   have hk : r.n j<F.card := by
      apply (rank_gt hu.le).1
      change u<(r.pm j).U v at hm
      unfold Params.U at hm
      change u< min 4 (max u (max v.base (rank r.S (fun x=>ht (v.ts x)) (r.n j)))) at hm
      grind
   have he : F ⊆ T ∪ r.fatties j := by
      intro i hi; by_cases he:i∈r.fatties j
      · exact mem_union_right _ he
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hi,he⟩)
   have he1 : r.n j ≤ 2*T.card := by
      have hd := (card_le_card he).trans (card_union_le ..)
      unfold binge at hh; omega
   have he2 : T⊆r.S:= fun i hi =>(mem_filter.mp (mem_sdiff.mp hi).1).1
   have hf {x} (hg:x∈T) : u/8 ≤ r.epi j x := by
     obtain ⟨hz1,hz2⟩:= mem_sdiff.1 hg
     obtain ⟨hv,hv'⟩:= mem_filter.mp hz1
     let d:=r.aim x
     let w:=r.pile (j+1) x
     have hs : d.1≤u/4 := le_of_not_gt fun he=> hz2 (mem_filter.2 ⟨hv,he⟩)
     have ht0 := r.rho_dust h hi
     have hz : u/4≤ small := by change 6*u≤ small at ht0; exact le_trans (by linarith : u/4≤6*u) ht0
     have hs1 : d.2=0 := h.target_flat _ hv (le_trans hs hz)
     have hs0 : 0≤d.1 := h.target_nn _ hv
     have hx1 : ht (v.ts x) ≤ ht w + u/100 := by
       change ht ((r.enter j).ts x) ≤_
       rw [r.total_enter]
       exact le_trans (ht_add ..) (add_le_add_right (le_trans (hl _ hv) hq) _)
     change u/8≤ min 1 (max (|w.1-d.1|/(1+d.1)) |w.2-d.2|)
     apply le_min (by linarith)
     by_contra! hn
     obtain ⟨ha,hb⟩:=max_lt_iff.mp hn
     change ht (v.ts x) ≤ max |w.1| |w.2| + u/100 at hx1
     rw [hs1,sub_zero] at hb
     rw [div_lt_iff₀ (by linarith)] at ha
     have he := (abs_add_le (w.1-d.1) d.1)
     rw [sub_add_cancel,abs_of_nonneg hs0] at he
     have hg : ht (v.ts x)>u := hv'
     have he2 : u/8*(1+d.1)≤u/4 := by nlinarith
     rcases le_total |w.1| |w.2| with hz|hz
     · rw [max_eq_right hz] at hx1; linarith
     · rw [max_eq_left hz] at hx1; linarith
   have huR : (r.n j:ℝ)≤2*(T.card:ℝ) := by exact_mod_cast he1
   calc _ ≤ (T.card:ℝ)*(u/8)^4 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ∑ i∈T,(u/8)^4 := by simp
        _ ≤ ∑ i∈T,r.epi j i^4 :=
            sum_le_sum fun i hi=>pow_le_pow_left₀ (by linarith) (hf hi) 4
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg he2 (fun _ _ _=>by positivity)

lemma earliest (h:0<r.L) : ∃ j<r.L,r.pre j∧(r.L=j+1 ∨ r.overflow j) := by
   classical
   by_cases he:∃ j<r.L,r.overflow j
   · obtain ⟨ha,hb⟩:=Nat.find_spec he
     exact ⟨_,ha,fun j hj hs=>Nat.find_min he hj ⟨hj.trans ha,hs⟩,Or.inr hb⟩
   refine ⟨r.L-1,by omega,fun i hi h=>he ⟨i,by omega,h⟩,Or.inl (by omega)⟩

end Run
end
end ExactDerandomization.Buf

end

end OAI
