import OAI.Analysis.FourierLLogL.Procedure.Likelihood
/-! # Expected starts, entropy and attempt counts -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

namespace Road

def flatFee (t : Road j M s) (f : Event j M → ℝ) :=
    t.expHike (fun l _ => l.fee f)

lemma flat_finish (s : Scene M) (b : Bool) (f : Event j M → ℝ) :
    flatFee (.finish s b) f = 0 := by simp [flatFee,expHike,hike,fee,Ex_const]

lemma flat_push (v : Pace) (t : Road j M (s.pace v)) (f : Event j M → ℝ) :
    flatFee (.push s v t) f = f (Event.pace s v)+t.flatFee f := by
  simp_rw [flatFee,Ex_hike_push,fee_pre,expHike,Ex_add (f:=fun _ => f (Event.pace s v)),Ex_const]

lemma flat_fork (v : Turn j s) (t : ∀ b, Road j M (v.fork.dst b))
    (h : (.fork s v t : Road j M s).Trusted J f) (g : Event j M → ℝ) :
    flatFee (.fork s v t) g = v.fork.probs.Ex (fun b => g (.march s v b)+(t b).flatFee g) := by
  simp_rw [flatFee,Ex_hike_fork h,fee_pre,expHike,Ex_add,Ex_const]

lemma total_step (v : Turn j s) :
    v.fork.probs.Ex (fun b => exp (-likelihood (.march s v b))) ≤ 1 := by
  cases v with
  | ask u => simp [Event.likelihood, Ex_const]
  | move =>
    let Q := (step s).probs
    change Q.Ex (fun b => exp (-log (2*Q b))) ≤ 1
    have HH (b : Bool) : Q b * exp (-log (2*Q b)) ≤ 1/2 := by
      rcases eq_or_lt_of_le (Q.nonneg b) with H|H
      · rw [← H,zero_mul]; norm_num
      rw [Real.exp_neg,Real.exp_log (by positivity)]
      field_simp
      rfl
    unfold Ex; rw [Fintype.sum_bool]; linarith [HH true,HH false]

def beginFee : Event j M → ℝ
| .pace _ .renew => 1
| _ => 0


private def headroom (x : ℝ) := x+exp (-x)-1
private lemma headroom_nonneg (x : ℝ) : 0 ≤ headroom x := by
  unfold headroom; linarith [Real.add_one_le_exp (-x)]

private lemma headroom_up {x : ℝ} (hx : log 2 ≤ x) : 1/10 ≤ headroom x := by
  unfold headroom
  let t := log 2
  have h0 : 63/100 ≤ t := by unfold t; linarith [log_two_gt_d9]
  have h1 := Real.add_one_le_exp (t-x)
  have he : exp (-x) = exp (t-x)/2 := by
    rw [sub_eq_add_neg,exp_add]; unfold t; rw [exp_log (by norm_num)]; ring
  rw [he]
  change t ≤ x at hx; linarith

private def startup (s : Scene M) :=
    (if s.live then (1/10:ℝ) else 0)+(if s.norm=0 then (1/10:ℝ) else 0)

private lemma startup_ok (s : Scene M) : 0 ≤ startup s ∧ startup s ≤ 2/10 := by
  unfold startup
  split_ifs <;> norm_num

lemma ticket_count (t : Road j M s) (h : t.Trusted J f)
    (hm : 0 < s.mass) (x : ℝ) (hX : 0 < s.norm → log s.mass - log s.norm ≤ x) :
    t.flatFee beginFee /10 ≤ t.flatFee likelihood + t.flatFee count /10 + headroom x + startup s := by
  classical
  induction t generalizing x with
  | finish s _ =>
    simp_rw [flat_finish]; linarith [headroom_nonneg x,(startup_ok s).1]
  | push s v t ih =>
    obtain ⟨ha,hb,hc,hd⟩ := h
    simp_rw [flat_push,Event.likelihood,Event.count,zero_add]
    have hM := pace_mass s v
    cases v with
    | cross =>
      have HH := ih hd (hM.symm ▸ hm) 0 (by simp [Scene.pace,out])
      have he : startup (s.pace .cross) ≤ startup s := by
        have Hs : s.live=true := hc.1
        simp [startup,Scene.pace,out,Hs]
        split_ifs <;> norm_num
      rw [headroom,neg_zero,exp_zero] at HH
      have := headroom_nonneg x
      change (0+_)/10 ≤ _
      linarith
    | renew =>
      have he : (s.pace .renew).norm=s.mass := rfl
      have HH := ih hd (hM.symm ▸ hm) 0 (by intro h; rw [he,hM,sub_self])
      rw [headroom,neg_zero,exp_zero] at HH
      change (1+_)/10 ≤ _
      by_cases H : s.norm=0
      · have Hs : startup s = startup (s.pace .renew)+1/10 := by
          unfold startup; rw [he,ite_eq_left H,ite_eq_right hm.ne']
          simp [Scene.pace, reset]
        linarith [headroom_nonneg x]
      have Hs : startup s = startup (s.pace .renew) := by
        unfold startup; rw [he,ite_eq_right H,ite_eq_right hm.ne']; rfl
      have hp := lt_of_le_of_ne ha.norm_ok (Ne.symm H)
      have HH' := log_le_log (show 0 < 2 *s.norm from by positivity) hc.2.le
      rw [log_mul (by norm_num) hp.ne'] at HH'
      have ht := headroom_up (x:=x) (by linarith [hX hp])
      linarith
  | fork s v t ih =>
    have ha := h.1
    have hρ := branchTrusted h
    have hc := h.2.1
    have hn : 0 < s.norm := by by_contra! he; apply hc.2.2; unfold enter; linarith
    let Q := v.fork.probs
    let L (b : Bool) := likelihood (.march s v b)
    have hx (b : Bool) (hb : 0 < Q b) :
        (t b).flatFee beginFee /10 ≤ (t b).flatFee likelihood + (t b).flatFee count /10 +
          headroom (x+L b) + startup (v.fork.dst b) := by
      have hp := (true_mass hρ).mp hb
      apply ih b (h.2.2.2 b) hp (x+L b)
      have HH := price_space v b hρ hm hb
      intro hy
      have he : (v.fork.dst b).norm=s.norm := by
        cases v with
        | move => rfl
        | ask u => cases b
                   · rfl
                   · exfalso; change (0:ℝ)<0 at hy; linarith
      rw [he]
      unfold L
      have ht := fee_bounds (.march s v b)
      unfold Event.memFee at HH
      linarith [ht.1,ht.2.1,hX hn]
    have hh : Q.Ex (fun b => headroom (x+L b)) ≤ Q.Ex L + headroom x := by
      have he (b : Bool) : headroom (x+L b) = (x+L b)+(exp (-x)*exp (-L b)-1) := by
        unfold headroom; rw [←exp_add]; ring_nf
      simp_rw [he,Ex_add,Ex_sub,Ex_lmul,Ex_const]
      have H : Q.Ex (fun b => exp (-L b)) ≤ 1 := total_step v
      unfold headroom; nlinarith [exp_pos (-x)]
    have HH : Q.Ex (fun b => startup (v.fork.dst b)) ≤ startup s + Q.Ex fun b =>
        count (.march s v b)/10 := by
      conv_rhs => lhs; rw [← Ex_const Q (startup s)]
      rw [← Ex_add]
      apply Ex_mono; intro b
      cases v with
      | move => simp [startup,Turn.fork,step,smaller,count]
      | ask u =>
        cases b <;> simp [startup,Turn.fork,toss,lose,win,hn.ne',count]
    simp_rw [flat_fork _ _ h]
    have ht := Q.Ex_mono_mem hx
    simp_rw [Ex_add] at *

    have hZ : v.fork.probs.Ex (fun b => beginFee (.march s v b)) = 0 := by
      simp only [beginFee,Ex_const]
    rw [hZ]
    simp_rw [div_eq_mul_inv,Ex_mul] at *
    unfold L Q at *
    norm_num at *
    linarith

lemma final_coarse :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ t : Road j M s, t.Trusted J f → 1/H j ≤ s.mass →
        t.flatFee likelihood ≤ 2*limitC * H j ∧
        t.flatFee count ≤ capA * H j ∧
        (s.norm=0 → t.flatFee beginFee ≤ 100*limitC*H j) := by
  filter_upwards [mem_budget,cutoff_log] with j hj h M J s f t hh hM
  have hp := H_pos j; have he := H_ge j
  have hm : 0 < s.mass := lt_of_lt_of_le (by positivity : 0 < 1/H j) hM
  have Hl := (hj M J s f t hh hm).2
  have hX : t.flatFee likelihood ≤ 2*limitC*H j := by
    have hQ (x : Grid M) (hx : 0 < s.actor x) : (t.hike x).fee likelihood ≤
        30000*H j+(t.hike x).membership := by
      let l := t.hike x
      obtain ⟨h1,h2,h3,h4,h5⟩ := final_sound hh hm hx
      have H₃ : log l.done.mass ≤ 20000*H j := (log_le_log h3 h1.budget).trans h
      have hz := log_le_log (by positivity : 0 < 1/H j) hM
      rw [one_div,Real.log_inv] at hz
      change l.like ≤ _ + l.membership
      change l.like = _ at h4
      linarith [log_le_sub_one_of_pos hp]
    unfold flatFee expHike
    apply (s.actor.Ex_mono_mem hQ).trans
    rw [Ex_add,Ex_const]; unfold expHike limitC at *; nlinarith
  have hY : t.flatFee count ≤ capA*H j := by
    have hQ (x : Grid M) (hx : 0 < s.actor x) : (t.hike x).fee count ≤ capA*H j := by
      obtain ⟨h1,h2,h3,h4,h5,_⟩ := final_sound hh hm hx
      linarith [h1.capital.under,Nat.cast_nonneg (α:=ℝ) s.fund.uses]
    unfold flatFee expHike; apply le_trans (s.actor.Ex_mono_mem hQ); rw [Ex_const]
  refine ⟨hX,hY, fun hn => ?_⟩
  have HZ := ticket_count t hh hm 0 (by simp [hn])
  rw [headroom,neg_zero,exp_zero] at HZ
  have hZ := (startup_ok s).2
  unfold limitC capA at *; linarith

lemma attempt_count :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ t : Road j M s, t.Trusted J f → 1/H j ≤ s.mass →
        t.flatFee tried ≤ 12800*capA*H j^33 := by
  filter_upwards [final_coarse] with j hg M J s f t h hm
  let a := 12800*H j^32
  have H (s : Scene M) (t : Road j M s) (h : t.Trusted J f) :
      t.flatFee tried ≤ a*t.flatFee count := by
    induction t with
    | finish => simp [flat_finish]
    | push s v t ih =>
      simp only [flat_push,tried,count,zero_add]; exact ih h.2.2.2
    | fork s v t ih =>
      simp_rw [flat_fork v t h, Ex_add]
      rw [mul_add]
      apply add_le_add ?_
      · rw [← Ex_lmul]; exact Ex_mono _ (fun b => ih b (h.2.2.2 b))
      cases v with
      | move => simp [tried,count,Ex_const]
      | ask u =>
        have ht := h.2.2.1.2
        have HX : beta u.ix/2 ≤ (toss s u).probs true := by rw [success_prob]; exact ht.bias
        have hp := (main_bounds j ht.ix_ok).1
        simp [tried,count,Ex,Turn.fork]
        have hh : (toss s u).probs true + (toss s u).probs false = 1 := by simpa [Fintype.sum_bool] using (toss s u).probs.total
        rw [hh]
        calc
          1 ≤ a*(beta u.ix/2) := by have := H_pos j; unfold a; field_simp at *; nlinarith
          _ ≤ _ := by exact mul_le_mul_of_nonneg_left HX (by unfold a; positivity)
  have hx := (hg M J s f t h hm).2.1
  apply (H s t h).trans
  calc
    _ ≤ a*(capA*Thermal.H j) := by exact mul_le_mul_of_nonneg_left hx (by unfold a; positivity)
    _ = _ := by unfold a; ring

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
