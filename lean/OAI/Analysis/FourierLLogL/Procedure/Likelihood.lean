import OAI.Analysis.FourierLLogL.Procedure.Surprisal

/-! # Likelihood estimates through any terminal step -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal

variable {J M j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

lemma cutoff_log :
    ∀ᶠ j : ℕ in atTop, log (2*cutoff j) ≤ 20000*H j := by
  filter_upwards [evt_slow, eventually_ge_atTop 1] with j hj hi
  have h1 := hj.2
  have hp : (1:ℝ) ≤ j := by exact_mod_cast hi
  unfold cutoff; rw [log_mul (by norm_num) (by positivity),log_pow]
  have hZ := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have he : (j:ℝ)<2^(3000*slow j) := by exact_mod_cast h1
  have HH := log_le_log (by linarith : 0 < (j:ℝ)+1) (show (j:ℝ)+1≤ 2* (2:ℝ)^(3000*slow j) by linarith)
  rw [log_mul (by norm_num) (by positivity), log_pow] at HH
  have hg := H_ge j
  unfold Thermal.H at *; push_cast at *
  nlinarith

namespace Journal

lemma fee_neg (l : Journal j M) (f : Event j M → ℝ) :
    l.fee (fun x => - f x) = -l.fee f := by
  unfold fee
  suffices HH : ∀ l : List (Event j M), (l.map (fun x => -f x)).sum= -(l.map f).sum from HH _
  intro L; induction L with
  | nil => simp
  | cons i t ih => simp [ih,add_comm]

lemma fee_div_sub (l : Journal j M) (f g : Event j M → ℝ) (r : ℝ) :
    l.fee (fun x => f x/r-g x) = l.fee f/r-l.fee g := by
  unfold fee
  suffices H : ∀ l : List (Event j M), (l.map (fun x => f x/r-g x)).sum =
      (l.map f).sum/r - (l.map g).sum from H _
  intro a; induction a with
  | nil => simp
  | cons i t ih => simp only [List.map_cons,List.sum_cons,ih]; ring

end Journal

namespace Road

lemma minus_like_cap (t : Road j M s) (h : t.Trusted J f) (hm : 0 < s.mass) :
    t.expHike (fun l _ => exp (-l.like)) ≤ 1 := by
  have hi := capital_bound (s:=s) (fun i => -i.likelihood)
    (by intro i v; simp [Event.likelihood]) (by
      intro s v; cases v with
      | ask u =>
        simp only [likelihood,neg_zero,exp_zero,Ex_const]; exact le_rfl
      | move =>
        let Q := (step s).probs
        change Q.Ex (fun b => exp (-log (2*Q b))) ≤ _
        have H (b : Bool) : Q b * exp (-log (2*Q b)) ≤ 1/2 := by
          rcases eq_or_lt_of_le (Q.nonneg b) with hx|hx
          · rw [← hx,zero_mul]; norm_num
          rw [exp_neg,exp_log (by positivity)]
          field_simp; rfl
        simp only [Ex,Fintype.sum_bool]; linarith [H true,H false]) t h hm
  simpa only [Journal.fee_neg,like] using hi

lemma half_debit_cap (t : Road j M s) (h : t.Trusted J f) (hm : 0 < s.mass) :
    t.expHike (fun l _ => exp (l.debit/2-l.fee count)) ≤ 1 := by
  have H' := capital_bound (s:=s) (fun i => i.failFee/2-i.count)
    (by intro x v; simp [failFee,count]) (by
      intro s v; cases v with
      | move =>
        simp [Ex_const,failFee,count]
      | ask u =>
        let Q := (toss s u).probs
        have Hq : Q true+Q false=1 := by simp only [← Q.total,Fintype.sum_bool]
        have he₁ : Q true*exp (-1) ≤ Q true/2 := by
          have HP : Q true ≤ 1 := Q.le_one _
          have hx := Q.nonneg true
          rw [exp_neg]
          have he : 2 ≤ exp 1 := Real.exp_one_gt_two.le
          field_simp; nlinarith
        have he₂ : Q false*exp ((-log (Q false))/2) ≤ 1-Q true/2 := by
          rcases eq_or_lt_of_le (Q.nonneg false) with Hx|Hx
          · rw [← Hx,zero_mul]
            linarith
          have Ht := Real.exp_pos ((-log (Q false))/2)
          let q := Q false
          have hs : exp ((-log q)/2)^2 = 1/q := by
            rw [pow_two,←exp_add, add_halves,exp_neg,exp_log Hx]; ring
          have HH : (q *exp ((-log q)/2))^2=q := by rw [mul_pow,hs]; field_simp
          change _ + q = 1 at Hq
          change _*exp ((-log q)/2) ≤ _
          change 0 < q at Hx
          change q*exp ((-log q)/2) ≤ _
          nlinarith [sq_nonneg (q-1)]
        unfold Ex
        rw [Fintype.sum_bool]
        simp only [failFee,count, surprise,Turn.fork,zero_div,zero_sub,sub_zero]
        unfold Q at *; linarith) t h hm
  simpa only [debit,fee_div_sub] using H'

private lemma negative_square (x : ℝ) : max (-x) 0 ^2 ≤ 4*exp (-x) := by
  by_cases H : 0 ≤ -x
  · rw [max_eq_left H]
    have hh := Real.add_one_le_exp ((-x)/2)
    rw [show exp (-x)=exp ((-x)/2)*exp ((-x)/2) from
      Eq.symm (by rw [← exp_add,add_halves])]
    nlinarith
  rw [max_eq_right (by linarith)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  positivity

lemma neg_like_budget (t : Road j M s) (h : t.Trusted J f) (hm : 0 < s.mass) :
    t.expHike (fun l _ => (max (-l.like) 0)^2) ≤ 4 := by
  unfold expHike
  apply le_trans (Ex_mono _ fun x => negative_square ((t.hike x).like))
  rw [Ex_lmul]
  have hh := minus_like_cap t h hm; unfold expHike at hh
  linarith

private lemma spent_top :
    ∀ᶠ j : ℕ in atTop, ∀ M : ℕ, ∀ c : Fund M, ∀ p : Node, Ok c p j →
      c.spend ≤ 10^19*height j := by
  filter_upwards [Fund.fund_est,Fund.envelope_scale] with j H hi M c p h
  have h0 := ((H M).2 c p h).1
  have h1 := h.solvent
  have h2 : 1 ≤ height j := hi.2.2.1
  unfold reserve capA at h1
  norm_num at *; linarith

def limitC : ℝ := 10^30

lemma mem_budget :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ t : Road j M s, t.Trusted J f → 0 < s.mass →
        t.expHike (fun l _ => membership l ^2) ≤ (limitC*H j)^2 ∧
        t.expHike (fun l _ => membership l) ≤ limitC*H j := by
  classical
  filter_upwards [spent_top] with j hg M J s f t h hm
  let a := H j; let d := height j
  have ha : 1 ≤ a := H_ge _
  have hb : 0 ≤ a := le_trans zero_le_one ha
  have hd : 0 < d := d_pos _
  let F (x) := membership (t.hike x)
  let e (x) := debit (t.hike x)/2 - (t.hike x).fee count
  have hf : s.actor.Ex (fun x => F x ^2) ≤ (limitC*a)^2 := by
    have H (x : Grid M) (hx : 0 < s.actor x) :
        F x ^2 ≤ 10^58*a^2 + 128*exp (e x) := by
      obtain ⟨hs,hh,h1,h2,h3,h4⟩ := final_sound h hm hx
      let l := t.hike x
      have hi : l.fee count ≤ capA*a := by
        have ht := hs.capital.under
        change _ + l.fee count=_ at h3
        change ((l.done.fund.uses:ℕ):ℝ) ≤ capA*a at ht
        linarith [Nat.cast_nonneg (α:=ℝ) s.fund.uses]
      have hW : creditSum l ≤ 10^26*a := by
        have HP : l.done.fund.spend-s.fund.spend ≤ 10^19*d := by
          have hk := (rootSafe h).capital.nonneg
          exact le_trans (sub_le_self _ (hk.1.trans hk.2)) (hg M l.done.fund l.done.here hs.capital)
        apply h4.trans
        calc
          _ ≤ 2000000*a/d*(10^19*d) := mul_le_mul_of_nonneg_left HP (by positivity : 0 ≤ 2000000*a/d)
          _ ≤ _ := by field_simp; nlinarith
      have hWW : F x ≤ (10^26+2*capA)*a+ 2*max (e x) 0 := by
        change membership l ≤ _
        rw [mem_parts]
        have hh := le_max_left (e x) 0
        change debit l/2-l.fee count ≤ _ at hh
        unfold capA at *; linarith
      have hr' := negative_square (-(e x))
      rw [neg_neg] at hr'
      have hr := le_max_right (e x) 0
      have hZ : 0 ≤ F x := l.positive_mem
      apply le_trans (pow_le_pow_left₀ hZ hWW 2)
      unfold capA; nlinarith [exp_nonneg (e x),
        sq_nonneg ((10^26+2*(10:ℝ)^16)*a-2*max (e x) 0)]
    apply le_trans (Ex_mono_mem _ H)
    rw [Ex_add,Ex_const,Ex_lmul]
    have Hh : s.actor.Ex (fun x => exp (e x)) ≤ 1 := half_debit_cap t h hm
    unfold limitC; norm_num at *; nlinarith
  change s.actor.Ex (fun x => F x^2) ≤ (limitC*a)^2 ∧ s.actor.Ex F ≤ limitC*a
  exact ⟨hf,by nlinarith [sq_Ex s.actor F,show 0 ≤ limitC*a by unfold limitC; positivity]⟩

lemma log_mass_budget :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ t : Road j M s, t.Trusted J f → 1/H j ≤ s.mass →
        t.expHike (fun l _ => (max (-log l.done.mass) 0)^2) ≤ (10*limitC*H j)^2 := by
  filter_upwards [mem_budget] with j hj M J s f t h hm
  let a := H j
  have hp : 0 < a := H_pos j
  have he : 1 ≤ a := H_ge j
  have hs : 0 < s.mass := lt_of_lt_of_le (by positivity : 0 < 1/a) hm
  have Hl : -log s.mass ≤ a := by
    have HH := log_le_log (by positivity : 0 < 1/a) hm
    rw [one_div,Real.log_inv] at HH
    linarith [log_le_sub_one_of_pos hp]
  have Hx (x : Grid M) (hx : 0 < s.actor x) :
      let l := t.hike x
      (max (-log l.done.mass) 0)^2 ≤ 3*a^2 + 3*l.membership^2 + 3*max (-l.like) 0 ^2 := by
    intro l; obtain ⟨_,_,_,h1,_,_⟩ := final_sound h hs hx
    have hP := l.positive_mem
    have hi := le_max_right (-l.like) 0
    have h := le_max_left (-l.like) 0
    have heq : max (-log l.done.mass) 0 ≤ a + l.membership + max (-l.like) 0 := by
      apply max_le <;> first | (dsimp only [l] at *; linarith)
    nlinarith [show 0 ≤ max (-log l.done.mass) 0 from le_max_right _ _,
      sq_nonneg (a-l.membership),sq_nonneg (a-max (-l.like) 0),sq_nonneg (l.membership-max (-l.like) 0)]
  have HH := (hj M J s f t h hs).1
  have HE := neg_like_budget t h hs
  unfold expHike at *
  apply le_trans (Ex_mono_mem _ Hx)
  rw [Ex_add,Ex_add,Ex_lmul,Ex_const,Ex_lmul,Ex_lmul]
  unfold limitC at *; nlinarith [show H j=a from rfl]

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
