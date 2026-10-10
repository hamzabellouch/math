import OAI.Analysis.FourierLLogL.Assembly.Duration
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Troupe
open Run Streak

def lowI (j : ℕ) (b : Bool) := if b then mainIx j else 0
def highI (j M : ℕ) (b : Bool) := lowI j b+M+1
def playsL (j M : ℕ) (b : Bool) := Finset.Ico (lowI j b) (highI j M b)
def picks (s : Scene M) (i j : ℕ) (b : Bool) :=
    i ∈ playsL j M b ∧ hazard s false i

def priciest (s : Scene M) (j : ℕ) (b : Bool) :=
    if h : ∃ i, picks s i j b then Nat.find h else lowI j b
def mutedR (s : Scene M) (j : ℕ) (b : Bool) :=
    surcharge s false (priciest s j b)

/-- scalar edge charges pay the largest bad level, chosen locally at the pre-bit moment. -/
lemma pricey (s : Scene M) (j : ℕ) (b : Bool) (i : ℕ) (h : picks s i j b) :
    side i ≤ 128*mutedR s j b := by
  let n := priciest s j b
  have hi : ∃ i, picks s i j b := ⟨i,h⟩
  have hn : n=Nat.find hi := dite_eq_left hi
  have HE : hazard s false n := hn.symm ▸ (Nat.find_spec hi).2
  have H : side i ≤ side n := pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (hn.le.trans (Nat.find_min' hi h))
  change side n / 128 ≤ edgeW s n at HE
  change _ ≤ 128*surcharge s false n
  rw [surcharge,ite_eq_left (show hazard s false n from HE)]; linarith

def special (j : ℕ) (b : Beat M) := (rose (tagM (mainIx j +1)) (0:Grid M)).flag b.post

def token (a : Grade → ℕ) (L : Path M) (j : ℕ) (s : Bool) (b : Beat M) :=
    side M+512*mutedR b.post j s+
      (∑ i∈playsL j M s,4*side i*stripe a (tagL i) j L b) +
        (if s then 4*(special j b+stripe a (tagM (mainIx j)) j L b) else 0)

lemma token_floor (a : Grade → ℕ) (j : ℕ) (s : Bool) (L : Path M) (b : Beat M) :
    side M ≤ token a L j s b ∧ 512*mutedR b.post j s ≤ token a L j s b ∧
      (∑ i∈playsL j M s,4*side i*stripe a (tagL i) j L b) ≤ token a L j s b ∧
      (s=true → 4*(special j b+stripe a (tagM (mainIx j)) j L b) ≤ token a L j s b) := by
  let z := ∑ i∈playsL j M s,4*side i*stripe a (tagL i) j L b
  have hZ : 0 ≤ z := Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by norm_num)
    (side_pos _).le) (stripe_pos _ _ _ _ _)
  have hx : 0 ≤ mutedR b.post j s := surcharge_nonneg _ _ _
  have hi : 0 ≤ special j b := flag_nonneg _ _
  have hv := stripe_pos a (tagM (mainIx j)) j L b
  have hh := side_pos M
  unfold token
  unfold z at *
  cases s <;> simp only [↓reduceIte,Bool.false_eq_true] <;>
    refine ⟨?_,?_,?_,fun H => ?_⟩ <;> first | linarith | contradiction

lemma tokens_nonneg (a : Grade → ℕ) (L : Path M) (b : Beat M) (j : ℕ) (s : Bool) :
    0 ≤ token a L j s b := (side_pos M).le.trans (token_floor a j s L b).1

lemma amp_test {s : Scene M} (h : Climb s) (u : Grid M) :
    ‖gain s u‖ ≤ ampU s u ∧ ampU s u ≤ 4 ∧
      ∃ b : Bool, ampU s u=‖scalar (s.smaller b) u‖ := by
  have H (b) := (scalar_norm (h.child b) u).trans (h.child b).lift
  constructor
  · apply (norm_halfcomplex _ _).trans
    have h1 : ‖scalar (s.smaller false) u‖ ≤ ampU s u := le_max_left _ _
    have h2 : ‖scalar (s.smaller true) u‖ ≤ ampU s u := le_max_right _ _
    linarith
  · unfold ampU
    refine ⟨max_le (H false) (H true),?_⟩
    by_cases hh : ‖scalar (s.smaller true) u‖ ≤ ‖scalar (s.smaller false) u‖
    exact ⟨false,max_eq_left hh⟩
    exact ⟨true,max_eq_right (le_of_not_ge hh)⟩

lemma side_ant (i j : ℕ) (h : i ≤ j) : side j ≤ side i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- Each unmasked direct jump outside the main intervals can be paid by its amplitude-selected
coupons. During the recursion node n hasn't entered or is unmasked for its scalar level. -/
lemma direct_point {s : Scene M} {L : Path M} {x u : Grid M} (h : Trip x s L)
    (j : ℕ) (c : Bool) (a : Grade → ℕ) (hh : shades a u L j)
    (n : ℕ) (l r : Path M) (b : Beat M)
    (hR : c=true → stall u (tagM (mainIx j)) j L l)
    (hc : ∀ i ∈ Finset.Ico (lowI j c) n, stall u (tagL i) j L l)
    (_hn : n ∈ Set.Icc (lowI j c) (highI j M c)) (hl : L=l++r)
    (hm : b∈l) (hb : n < highI j M c → 4*side n < ampU b.post u) :
    ‖proceeds x u b‖ ≤ token a L j c b := by
  let t := lowI j c; let B := side t; let q := b.post; let s := playsL j M c
  let K := t+M
  let v := token a L j c b
  let p := ampU q u
  have ht := trip_attend h b (by rw [hl]; simp [hm])
  have H := token_floor a j c L b
  change _ ≤ v ∧ _ ≤ v ∧ _ ≤ v ∧ (c=true→_ ≤ v) at H
  obtain ⟨hP,hB,z,hz⟩ := amp_test ht.1.climb u
  change p ≤ 4 at hB
  change p=_ at hz
  rw [proceeds,norm_scaleC,ht.2.2.1,one_mul]
  apply hP.trans
  by_cases hi : 4*B < p
  · have he : c=true := by
      by_contra he
      have HE : t=0 := ite_eq_right he
      unfold B at hi; rw [HE,show side 0=1 by simp [side]] at hi; linarith
    have hI : mainIx j=t := by unfold t lowI; rw [ite_eq_left he]
    apply le_trans _ (H.2.2.2 he)
    by_cases ha : hazard q true t
    · have HF : special j b=1 :=
        ite_eq_left ⟨(show 0 < mainIx j + 1 by omega),by
          change hazard q true (mainIx j+1-1); rw [hI]; exact ha⟩
      rw [HF]
      linarith [stripe_pos a (tagM (mainIx j)) j L b]
    · have HV : snag (tagM (mainIx j)) u b := by
        rw [hI]; refine ⟨⟨z,?_⟩,ha⟩
        change B^2 ≤ energy (q.smaller z) u
        have hi' := scalar_energy (q.smaller z) (ht.1.climb.child z) u
        change p=‖scalar (q.smaller z) u‖ at hz
        rw [←hz] at hi'
        nlinarith [show 0 < B from side_pos _]
      have HW := hh _ l r hl (hR he) b hm HV
      rw [show stripe a (tagM (mainIx j)) j L b=1 from ite_eq_left HW]
      have hx : 0 ≤ special j b := flag_nonneg _ _
      linarith
  have hk : p ≤ 4*B := le_of_not_gt hi
  by_cases h : p < side K
  · apply le_trans _ H.1
    exact h.le.trans (side_ant M K (by unfold K; omega))
  have hq : side K ≤ p := le_of_not_gt h
  let goodN (i : ℕ) := t ≤ i ∧ side i ≤ p
  have HX : goodN K := ⟨by unfold K; omega,hq⟩
  have HF : ∃ i,goodN i := ⟨K,HX⟩
  let i := Nat.find HF
  have hE : goodN i := Nat.find_spec HF
  have hV : i ≤ K := Nat.find_min' HF HX
  have hS : i∈s := Finset.mem_Ico.mpr ⟨hE.1,Nat.lt_succ_of_le hV⟩
  have HI : p ≤ 4*side i := by
    by_cases HC : t=i
    · unfold B at hk; rwa [← HC]
    have HH := Nat.find_min HF (m:=i-1) (by have hi : t < i := lt_of_le_of_ne hE.1 HC; change i-1 < i; omega)
    have hx' : p < side (i-1) := lt_of_not_ge fun H =>
      HH ⟨Nat.le_sub_one_of_lt (lt_of_le_of_ne hE.1 HC), H⟩
    have H := side_succ (i-1)
    have HV : 0 < i := by have hi := hE.1; omega
    rw [Nat.sub_add_cancel HV] at H
    nlinarith [side_pos i]
  have hj : i < n := by
    by_cases hz : n < highI j M c
    · by_contra! he
      exact not_lt_of_ge (HI.trans (mul_le_mul_of_nonneg_left (side_ant n i he) (by norm_num)))
        (hb hz)
    exact (Finset.mem_Ico.mp hS).2.trans_le (le_of_not_gt hz)
  apply HI.trans
  by_cases hv : hazard q false i
  · apply le_trans _ H.2.1
    linarith [pricey b.post j c i (show picks q i j c from ⟨hS,hv⟩)]
  · let g := tagL i
    have hb : stall u g j L l := hc _ (Finset.mem_Ico.mpr ⟨hE.1,hj⟩)
    have hi : betweenS (a g) (billWait g j L) b :=
      hh g l r hl hb b hm ⟨⟨z,(show side i ≤ ‖scalar _ _‖ from le_trans hE.2 hz.le)⟩,hv⟩
    have hx' : stripe a g j L b=1 := ite_eq_left hi
    apply le_trans _ H.2.2.1
    calc
      _ = 4*side i*stripe a (tagL i) j L b := by rw [hx']; ring
      _ ≤ _ := Finset.single_le_sum (f:=fun i => 4*side i*stripe a (tagL i) j L b) (fun k _ =>
        mul_nonneg (mul_nonneg (by norm_num) (side_pos _).le) (stripe_pos _ _ _ _ _)) hS

def tokenCost (j : ℕ) (s : Bool) (L : Path M) :=
    1 + 512*subtotal (fun b => mutedR b.post j s) L+
      (∑ i∈playsL j M s,4*side i*(billWait (tagL i) j L:ℝ))+
        (if s then 4*(subtotal (special j) L+(billWait (tagM (mainIx j)) j L:ℝ)) else 0)

lemma cross_subtotal (l : Path M) (s : Finset ℕ) (f : Beat M → ℕ → ℝ) :
    subtotal (fun b => ∑ i∈s,f b i) l=∑ i∈s,subtotal (fun b => f b i) l := by
  induction l with
  | nil => simp only [subtotal_nil,Finset.sum_const_zero]
  | cons b l ih =>
    rw [subtotal_cons,ih]; simp_rw [subtotal_cons,Finset.sum_add_distrib]

lemma max_tokens {x : Grid M} (L : Path M) (h : Trip x s L)
    (a : Grade→ℕ) (j : ℕ) (p : Bool)
    (hh : L.length ≤ M) :
    subtotal (token a L j p) L ≤ tokenCost j p L := by
  let C i := 4*side i
  have h1 : subtotal (fun _ => side M) L ≤ 1 := by
    rw [subt_constant]
    have H : (L.length:ℝ) ≤ 2^M := by exact_mod_cast (hh.trans Nat.lt_two_pow_self.le)
    apply le_trans (mul_le_mul_of_nonneg_left H (side_pos _).le)
    rw [side_card]
  have h2 (T : Finset ℕ) :
      subtotal (fun b => ∑ i∈T,4*side i *stripe a (tagL i) j L b) L ≤
        ∑ i∈T,4*side i*(billWait (tagL i) j L:ℝ) := by
    rw [cross_subtotal _ _ (fun b i => _)]
    apply Finset.sum_le_sum; intro i _
    rw [subtR]; exact mul_le_mul_of_nonneg_left (stripe_bill _ _ _ _ x h)
      (mul_nonneg (by norm_num) (side_pos _).le)
  have HE (b : Bool) :
      subtotal (fun B : Beat M => 512*mutedR B.post j b) L=512*subtotal (fun B => mutedR B.post j b) L :=
    subtR _ _ _
  unfold token tokenCost
  have h3 := stripe_bill a (tagM (mainIx j)) j L x h
  cases p <;>
   simp only [Bool.false_eq_true,↓reduceIte,add_zero]
  · rw [blend _ (f:=fun _ => _) (g:=fun _ => _),blend _ (f:=fun _=>_) (g:=fun _=>_),HE]
    linarith [h2 (playsL j M false)]
  · simp_rw [blend _ (f:=fun b => _) (g:=fun b => _)]
    rw [HE,subtR _ _ 4,blend _ (f:=special j)]
    linarith [h2 (playsL j M true)]

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
