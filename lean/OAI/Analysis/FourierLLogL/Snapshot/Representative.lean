import OAI.Analysis.FourierLLogL.Snapshot.Display

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Snapshot
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

def tolerance (j i : ℕ) (main : Bool) :=
    if main then sig j else side i ^4/65536
def spotLimit (s : Scene M) (j i : ℕ) (main : Bool) :=
    tolerance j i main * s.here.invlen

lemma tolerance_pos (j i : ℕ) (b : Bool) : 0 < tolerance j i b := by
  unfold tolerance sig; have H := slow_pos j; have HH := side_pos i; split <;> positivity
lemma spotLimit_pos (s : Scene M) (j i : ℕ) (b : Bool) : 0 < spotLimit s j i b :=
    mul_pos (tolerance_pos _ _ _) s.here.invlen_pos

def adjacent (s : Scene M) (j i : ℕ) (main : Bool) (x : Grid M) :=
    if main then fnear s.fund.mood (sepRad j) (spotLimit s j i main) x else rad x ≤ spotLimit s j i main

lemma adjacent_zero (s : Scene M) (j i : ℕ) (b : Bool) :
    adjacent s j i b 0 := by
  have H := spotLimit_pos s j i b
  cases b
  · change rad _ ≤ _
    simpa [rad] using H.le
  · refine ⟨0,?_,?_⟩
    · rw [delta_zero]; unfold sepRad; positivity
    simp only [sub_self]
    simpa [rad] using H.le

lemma adjacent_neg (s : Scene M) (j i : ℕ) (b : Bool) {x : Grid M} (hx : adjacent s j i b x) :
    adjacent s j i b (-x) := by
  cases b with
  | false =>
    change rad (-_) ≤ _
    rw [rad_even]; exact hx
  | true =>
    obtain ⟨v,hv,h⟩ := (show fnear _ _ _ x from hx)
    refine ⟨-v,?_,?_⟩
    · rw [delta_even _ v]; exact hv
    rw [show -x- -v= -(x-v) by ring,rad_even]; exact h

def net_ok (s : Scene M) (j i : ℕ) (b : Bool) (d : Finset (Grid M)) :=
    (∀ x∈d, intense b s (side (i+1)) x) ∧
    (∀ x ∈ d,∀ y∈d,x≠y → ¬ adjacent s j i b (x-y)) ∧
    ∀ x, intense b s (side (i+1)) x → ∃ y∈d, adjacent s j i b (x-y)
lemma exists_net (s : Scene M) (j i : ℕ) (b : Bool) : ∃ d, net_ok s j i b d := by
  classical
  let L := intense b s (side (i+1)); let H := adjacent s j i b
  let P (d : Finset (Grid M)) := (∀ i∈d, L i) ∧ (∀ i∈d,∀ u∈d,i≠u → ¬ H (i-u))
  let F := Finset.univ.filter P
  have he : (∅:Finset (Grid M))∈F := by simp [F,P]
  obtain ⟨d,hd,hh⟩ := Finset.exists_max_image F Finset.card ⟨_,he⟩
  have hp := (Finset.mem_filter.mp hd).2
  refine ⟨d,hp.1,hp.2,?_⟩
  intro x hx
  by_contra! Hh
  have hn : x∉d := by intro he; apply Hh _ he; rw [sub_self]; exact adjacent_zero _ _ _ _
  have hh' : insert x d ∈ F := by
    apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    refine ⟨?_,?_⟩
    · intro w ht
      rcases Finset.mem_insert.mp ht with h|h; exact h ▸ hx; exact hp.1 _ h
    intro w hw q hq h'
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact Hh q ((Finset.mem_insert.mp hq).resolve_left (Ne.symm h'))
    rcases Finset.mem_insert.mp hq with he|he
    · subst q
      intro hc
      apply Hh w hw
      rw [show x-w= -(w-x) by ring]
      exact adjacent_neg _ _ _ _ hc
    exact hp.2 _ hw _ he h'
  have hi := hh _ hh'
  rw [Finset.card_insert_of_notMem hn] at hi; omega

def net (s : Scene M) (j i : ℕ) (b : Bool) := Classical.choose (exists_net s j i b)
lemma net_spec (s : Scene M) (j i : ℕ) (b : Bool) :
    net_ok s j i b (net s j i b) := Classical.choose_spec _

lemma net_len_main (s : Scene M) (j i : ℕ) (h : i+1 ≤ testIx j) (hs : s.settled j)
    (he : s.live=true) : ((net s j i true).card:ℝ) ≤ exp (kappa j (codeWeight capA) (i+1)) := by
  apply le_of_not_gt
  intro hh
  obtain ⟨H,H1,H2⟩ := net_spec s j i true
  exact hs he _ h ⟨_,hh.le,H,H1⟩

lemma share_pos' (s : Scene M) (hs : ReadyAt s) (hp : 0 ≤ s.norm) : 0 ≤ share s :=
  div_nonneg (avg_nonneg _ (fun x _ => hs.2 x)) hp
lemma share_small {s : Scene M} (hb : work s j J f) : 0 < s.norm ∧ share s ≤ 2 := by
  have hi := hb.2.2
  have hx := hb.1.2.2
  unfold enter at hi
  refine ⟨by linarith,?_⟩
  exact (div_le_iff₀ (by linarith)).mpr (le_of_not_gt hi)
lemma share_child (s : Scene M) (hp : s.here.valid) (h : s.here.lev < M)
    (hs : 0 ≤ s.wage) (hh : 0 < s.norm) (hb : share s ≤ 2) (b) :
    share (s.smaller b) ≤ 4 := by
  have H := share_split s
  have HF (i : Bool) : 0 ≤ share (s.smaller i) := share_pos' (s.smaller i)
    ⟨s.here.child_ok hp h i,hs⟩ hh.le
  cases b <;> linarith [HF false,HF true]

lemma scalar_point (s : Scene M) (i : Grid M) (hp : ReadyAt s) (hh : 0 ≤ s.norm)
    {p : Node} (ht : below s.here p) (x : Grid M) (he : x∈p.block M)
    (k : Grid M) :
    ‖scalar s i-chi (i-k) x*scalar s k‖ ≤ share s * (8 * p.len * rad (i-k)) := by
  have HF y (hy : y∈s.here.block M) :
      ‖chi i y-chi (i-k) x*chi k y‖ ≤ 8*p.len * rad (i-k) := by
    rw [show chi i y-chi (i-k) x*chi k y=(chi (i-k) y-chi (i-k) x)*chi k y by
      rw [sub_mul,← chi_add',sub_add_cancel],norm_mul,norm_chi,mul_one]
    have h := phase_distance (i-k) y x
    apply h.trans
    rw [mul_comm (rad _)]
    have hi := diam_block (block_of_below ht _ hy) he
    gcongr
    exact rad_nonneg _
  unfold scalar; rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply le_trans (norm_sum_le _ _)
  rw [← ante_total s hp.1, Finset.sum_mul]
  apply Finset.sum_le_sum; intro y hy
  unfold ante; rw [mul_left_comm,← mul_sub,norm_mul, Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (wt_nonneg s.here hp.2 hh _)]
  by_cases H : y∈s.here.block M
  · exact mul_le_mul_of_nonneg_left (HF _ H) (wt_nonneg s.here hp.2 hh _)
  rw [wt,dice_apply hp.1,ite_eq_right H,zero_mul,zero_div]
  simp

lemma scalar_compare (s : Scene M) (i k : Grid M) (hp : ReadyAt s) (hh : 0 ≤ s.norm)
    (b : ℝ) (hb : share s ≤ b) :
    |‖scalar s i‖-‖scalar s k‖| ≤ b * (8*s.here.len*rad (i-k)) := by
  have Hs := hp.1
  let x := s.here.start M
  have HH := abs_norm_sub_norm_le (scalar s i) (chi (i-k) x*scalar s k)
  rw [norm_mul,norm_chi,one_mul] at HH
  apply HH.trans ((scalar_point s i hp hh (below_refl _) x (start_mem Hs.1 Hs.2) k).trans ?_)
  exact mul_le_mul_of_nonneg_right hb (by have := s.here.len_pos; have := rad_nonneg (i-k); positivity)


lemma scalar_power (s : Scene M) (hp : ReadyAt s) (hh : 0 < s.norm) (d b : ℝ)
    (h : ∀ x, s.wage x ≤ d) (he : share s ≤ b) (hd : 0 ≤ d) :
    ∑ i, ‖scalar s i‖^2 ≤ s.here.invlen * b * d / s.norm := by
  let p := s.here
  let P := ante s
  let f (i : Grid M) : ℂ := ((P i / side M:ℝ):ℂ)
  have hb := side_pos M
  have Hχ (i : Grid M) : scalar s i = fc f (-i) := by
    unfold scalar fc expU; rw [neg_neg, Complex.real_smul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by unfold f P ante; push_cast; field_simp [(Complex.ofReal_ne_zero.mpr hb.ne')]
  have HT (i : Grid M) :
      side M*‖f i‖^2 ≤ P i * (p.invlen * d / s.norm) := by
    have hi : P i ≤ side M*p.invlen * d / s.norm := by
      unfold P ante wt; rw [dice_apply hp.1]
      split_ifs with hx
      · rw [rinv p]
        apply div_le_div_of_nonneg_right _ hh.le
        exact mul_le_mul_of_nonneg_left (h i) (by have := s.here.len_pos; positivity)
      · simp only [zero_mul,zero_div]; have := p.invlen_pos; positivity
    unfold f
    have he : 0 ≤ P i := ante_nonneg s hp.2 hh.le _
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
    calc
      _ = P i * (P i / side M) := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ he
        apply (div_le_iff₀ hb).mpr
        apply hi.trans; exact le_of_eq (by ring)
  calc
    _ = ∑ i, ‖fc f i‖^2 := by simp_rw [Hχ]; exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
    _ = _ := fc_parseval f
    _ ≤ ∑ i, P i * (p.invlen *d/s.norm) := by
      unfold expU; rw [smul_eq_mul,Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => HT i
    _ ≤ _ := by
      rw [← Finset.sum_mul,show ∑ i,P i = _ from ante_total s hp.1]
      apply (mul_le_mul_of_nonneg_right he (show 0 ≤ p.invlen*d/s.norm by
        have := p.invlen_pos; positivity)).trans
      exact le_of_eq (by unfold p; ring)

end FourierLLogL.Dyadic.Procedure.Snapshot

end OAI
