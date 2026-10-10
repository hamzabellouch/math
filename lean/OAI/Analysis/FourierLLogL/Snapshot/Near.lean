import OAI.Analysis.FourierLLogL.Snapshot.Representative

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Snapshot
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

def scLimit (s : Scene M) (i j : ℕ) :=
    1000*(height j+max (-log s.norm) 0 + i +1)

lemma net_len_scalar {s : Scene M} (j i : ℕ) (h : ReadyAt s) (hm : s.here.lev<M)
    (hx : 0<s.norm) (hq : share s ≤ 2) (he : ∀ x, s.wage x ≤ exp (height j)) :
    ((net s j i false).card:ℝ) ≤ exp (scLimit s i j) := by
  classical
  let t := net s j i false
  let b := side i
  let q := s.here
  let d := exp (height j)
  let p := s.norm
  let w := tolerance j i false
  have heq : w=b^4/65536 := rfl
  let u := w*q.invlen/4
  let U := arc M u
  have hb : 0 < b := side_pos i
  have hh : b ≤ 1 := side_le i
  have hq' : 0 < q.invlen := q.invlen_pos
  have hp : 0 < u := by unfold u; have hw := tolerance_pos j i false; positivity
  have hV : b^4 ≤ b := by simpa using pow_le_pow_of_le_one hb.le hh (show 1 ≤ 4 by omega)
  have hd : u ≤ (2:ℝ)^M := calc
    _ ≤ q.invlen := by unfold u; rw [heq]; nlinarith
    _ ≤ _ := loc_scale h.1.2
  have hD : u ≤ (U.card:ℝ) := arc_card_lo _ _ hp.le hd
  let V := t ×ˢ U
  let a (x : Grid M × Grid M) := x.1+x.2
  have HH := net_spec s j i false
  have hI : InjOn a V := by
    rintro ⟨x,k⟩ H ⟨y,l⟩ H' HE
    obtain ⟨H1,H2⟩ := Finset.mem_product.mp H
    obtain ⟨H3,H4⟩ := Finset.mem_product.mp H'
    change x+k=y+l at HE
    have hxy : x=y := by
      by_contra hxy
      apply HH.2.1 x H1 y H3 hxy
      have hx : rad (x-y) ≤ 2*u := by rw [show x-y=l-k by linear_combination HE]; exact rad_diff H4 H2
      change rad _ ≤ w*q.invlen
      unfold u at hx; linarith [rad_nonneg (x-y)]
    subst x; simp_all
  let X (z : Grid M) (i : Bool) := ‖scalar (s.smaller i) z‖
  let Y (z : Grid M) := X z false^2 + X z true^2
  have hk i : ReadyAt (s.smaller i) :=
      ⟨child_ok _ h.1.1 hm i,h.2⟩
  have hs i : share (s.smaller i)≤4 := share_child s h.1.1 hm h.2 hx hq i
  have Hnear (z : Grid M × Grid M) (hz : z∈V) : (b/4)^2 ≤ Y (a z) := by
    obtain ⟨x,k⟩ := z
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hz
    obtain ⟨i',hv⟩ := HH.1 x h₁
    have hi : 4*(8*(s.smaller i').here.len*rad ((x+k)-x)) ≤ b/4 := by
      have hg : rad k ≤ u := (mem_arc _ _).mp h₂
      rw [show x+k-x=k by ring, show (s.smaller i').here.len=q.len/2 from child_len _ _]
      have hi : q.len*u=w/4 := by unfold u; rw [rinv]; field_simp [q.len_pos.ne']
      have hp' : q.len*rad k ≤ w/4 := hi ▸ (mul_le_mul_of_nonneg_left hg q.len_pos.le)
      nlinarith
    have hB := scalar_compare _ (x+k) x (hk _) hx.le _ (hs i')
    rw [side_succ] at hv
    change b/2 ≤ X x i' at hv
    change |X (x+k) i'- X x i'| ≤ _ at hB
    change (b/4)^2 ≤ Y (x+k)
    unfold Y; cases i' <;>
      nlinarith [(abs_le.mp hB).1,sq_nonneg (X (x+k) false),sq_nonneg (X (x+k) true)]
  have HL (i':Bool) : ∑ x : Grid M, X x i'^2 ≤ 8*q.invlen*d/p := by
    have H := scalar_power (s.smaller i') (hk _) hx d 4 he (hs _) (exp_nonneg _)
    have hV : (s.smaller i').here.invlen=2*q.invlen := by
      change (s.here.child _).invlen=_
      rw [invlen,child_depth,pow_succ]; unfold q invlen; ring
    rw [hV] at H
    exact H.trans (le_of_eq (by unfold p; simp only [smaller]; ring))
  have ht : t.card*u*(b/4)^2 ≤ 16*q.invlen*d/p := by
    calc
      _ ≤ t.card*(U.card:ℝ)*(b/4)^2 := by gcongr
      _ = ∑ _x∈V, (b/4)^2 := by simp [V]
      _ ≤ ∑ x∈V, Y (a x) := Finset.sum_le_sum Hnear
      _ = ∑ x∈V.image a, Y x := by rw [Finset.sum_image]; exact fun x hx y hy H => hI hx hy H
      _ ≤ ∑ x, Y x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ 16*q.invlen*d/p := by
        unfold Y; rw [Finset.sum_add_distrib]
        rw [show 16*q.invlen*d/p=8*q.invlen*d/p+8*q.invlen*d/p by ring]
        exact add_le_add (HL false) (HL true)
  have hr : 0 < p := hx
  have hd : 0 < d := exp_pos _
  have h_u : (t.card:ℝ) ≤ ((2:ℝ)^26*d)/(p*b^6) := by
    unfold u at ht; rw [heq] at ht
    field_simp at ht ⊢
    nlinarith
  change (t.card:ℝ) ≤ _
  apply h_u.trans
  have h1 : log ((2^26*d)/(p*b^6)) ≤ scLimit s i j := by
    rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) hd.ne',
      Real.log_mul hr.ne' (by positivity), log_pow, log_pow]
    unfold d b scLimit; rw [log_exp,side_pow_two,log_inv,log_pow]
    push_cast
    have Hp' : -log p ≤ max (-log s.norm) 0 := le_max_left _ _
    have Hi : 0 ≤ max (-log s.norm) 0 := le_max_right _ _
    nlinarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),d_pos j,Nat.cast_nonneg (α:=ℝ) i]
  exact le_trans (b:=exp (log _)) (le_of_eq (exp_log (by positivity)).symm) (exp_monotone h1)


lemma magnitude_near (main : Bool) (s : Scene M) (i k : Grid M) (hp : ReadyAt s) (hh : 0 ≤ s.norm)
    (b : ℝ) (hb : share s ≤ b) :
    magnitude main s i ≤ magnitude main s k + b * (16*s.here.len*rad (i-k)) := by
  let p := s.here
  obtain ⟨g,hg,hG⟩ := (test_complete main s hp.2 hh i).2
  let z := chi (i-k) (p.start M)
  have hZ : ‖z‖=1 := norm_chi _ _
  let f (x : Grid M) := g x*z
  have hf (x) : ‖f x‖≤1 := by unfold f; rw [norm_mul,hZ,mul_one]; exact hg _
  let T := 16*p.len*rad (i-k)
  have ht : 0 ≤ T := by have he := p.len_pos; have hv := rad_nonneg (i-k); unfold T; positivity
  have HI (x : Grid M) (hx : x∈p.block M) :
      ‖chi i x-z * chi k x‖ ≤ 8*p.len*rad (i-k) := by
    have HE := phase_distance (i-k) x (p.start M)
    rw [show chi i x-z*chi k x=(chi (i-k) x-z)*chi k x by rw [sub_mul,←chi_add',sub_add_cancel],norm_mul,norm_chi,mul_one]
    have hx' := diam_block hx (start_mem hp.1.1 hp.1.2)
    apply HE.trans; rw [mul_comm (rad _)]; gcongr; exact rad_nonneg _
  let P := channel (optic s main)
  let w (p : Grid M → ℂ) (i x y : Grid M) := utility main (p y) (chi i x)
  have hhU :
      sales main s g i ≤ sales main s f k + share s*T := by
    rw [show sales main s f k=rung s P (w f k) from rfl,← rung_const s hp.1 P T,←rung_add]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    by_cases hx : x∈p.block M
    · have heq : w f k x y = utility main (g y) (z*chi k x) := by unfold w utility f; rw [mul_assoc,norm_mul,hZ,mul_one]
      have hl := utility_diff main (g y) (chi i x) (z*chi k x) (hg _)
      apply mul_le_mul_of_nonneg_left
      · change w g i x y ≤ _
        unfold w at heq ⊢; dsimp only; rw [heq]
        unfold T; linarith [(abs_le.mp hl).2,HI x hx]
      exact mul_nonneg (ante_nonneg _ hp.2 hh _) (P _ |>.nonneg _)
    · have H : ante s x=0 := by unfold ante wt; rw [dice_apply hp.1,ite_eq_right hx,zero_mul,zero_div]
      change addMass s P x y*_ ≤ addMass s P x y*_
      rw [addMass,H]; ring_nf; exact le_rfl
  have HH := (test_complete main s hp.2 hh k).1 f hf
  rw [← hG]; apply hhU.trans
  exact add_le_add HH (mul_le_mul_of_nonneg_right hb ht)

end FourierLLogL.Dyadic.Procedure.Snapshot

end OAI
