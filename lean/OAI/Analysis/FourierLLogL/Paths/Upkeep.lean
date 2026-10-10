import OAI.Analysis.FourierLLogL.Paths.Ribbon
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


/-! # Expected forward sums of marked jump quantities -/
open Beam Run Run.Streak

/-- A local bit-Fisher budget -/
def caveat (s : Scene M) (j : ℕ) :=
    share s*(deficit s (channel (dye s))+(minimumT j)⁻¹)

lemma caveat_pos (s : Scene M) (j : ℕ) (h : Fit s) : 0 ≤ caveat s j := by
  have he : 0 ≤ s.mass := avg_nonneg _ fun x _ => h.ready.2 _
  unfold caveat
  rcases eq_or_lt_of_le he with he|he
  · unfold share; rw [← he,zero_div,zero_mul]
  exact mul_nonneg (div_nonneg he.le h.pos.le)
    (add_nonneg (deficit_nonneg s h.ready.1 h.ready.2 he _)
      (inv_nonneg.mpr (minimum_pos j).le))

lemma caveat_step {s q : Scene M} {l} (h : Following j J f (ran s q l)) (hh : Ideal s q) :
    (uniform Bool).Ex (fun b => caveat (q.smaller b) j) + (1/4:ℝ)*fax q ≤ caveat s j := by
  let U := (step q).probs; let v := (keep s q).snip; let Q := v.probs
  let Z := channel (dye q); let H (x) := deficit x Z; let a := (minimumT j)⁻¹
  have hm := pre_pos h
  have HE : Q.entropy ≤ a*Q false := debt_at h
  obtain ⟨hh1,hh2,h3⟩ := hh
  obtain ⟨ha,hb,hv,hp',ht,hs⟩ := h
  have hR : q.here.lev < M := (rooted _ (hs false)).within.2
  have hS : ReadyAt s := ⟨ha.within,ha.positive⟩; have hS' : ReadyAt q := ⟨hv.within,hv.positive⟩
  have hd := hh1.pos
  have hQ := hp'.1.2.2; have hZ := hh2.fit.pos
  have hM := keep_true hb.1 hS hS' hm
  have h₂ : Q true*(H q+a) ≤ H s+a := by
    have hi (b : Bool) : levels (v.dst b)=levels s := by
      unfold levels; rw [show (v.dst b).here=s.here from keep_here hb.1 _]
    have hz : Q.Ex (fun b => H (v.dst b)) ≤ H s+Q.entropy := by
      have hh := old_entropy_cost v Z
      have hh' := conditioned_balance Z v hM
      unfold H deficit; simp_rw [hi,Ex_sub (f:=fun _ => levels s),Ex_const]
      change v.probs.Ex _+ _ = s.actor.privateH Z at hh'
      unfold Q; linarith
    have hZ : 0 ≤ Q false * H (v.dst false) := by
      rcases eq_or_lt_of_le (Q.nonneg false) with h|h
      · rw [← h,zero_mul]
      have HH := other_ok hb.1 hS
      exact mul_nonneg h.le (deficit_nonneg (v.dst false) HH.1 HH.2 ((true_mass hM).mp h) Z)
    have ht₁ : Q true + Q false = 1 := by simpa only [Fintype.sum_bool] using Q.total
    rw [Ex,Fintype.sum_bool] at hz
    rw [show v.dst true=q from rfl] at hz
    nlinarith [show a*(Q true+Q false)=a by rw [ht₁]; ring]
  have ht₁ := space_deficit q Z hv.within.1 hR hv.positive hQ hZ
  let D (b : Bool) := H (q.smaller b)+a
  have h₁ :
      (uniform Bool).Ex (fun b => caveat (q.smaller b) j) =
        share q * U.Ex D := by
    have HI (b : Bool) : caveat (q.smaller b) j =
        (q.smaller b).mass * (q.norm⁻¹ * D b) := by unfold caveat D H; simp only [smaller]; unfold share Z dye a; dsimp; ring
    simp_rw [HI]
    rw [← output_split _ hv.within.1 hR hv.positive hQ (fun b => q.norm⁻¹*D b),
      Ex_lmul]
    unfold share U; ring
  have HZ : share q * ((1/4:ℝ)*(q.norm/q.mass)*fax q)=1/4*fax q := by
    unfold share; field_simp
  have hEq : share q = share s * Q true := by
    have H := kept_mass hb.1 hS hS' hm
    unfold share
    nth_rw 1 [H,hb.1.flat]
    unfold Q v; ring
  rw [h₁,← HZ,← mul_add]
  unfold D; rw [Ex_add (g:=fun b => a),Ex_const]
  have hDC : caveat s j=share s*(H s+a) := by unfold caveat H Z dye a; rw [hb.1.fund]
  have hsq : 0 ≤ share q := div_nonneg hQ.le hZ.le
  calc
    _ ≤ share q*(H q+a) := by
      apply mul_le_mul_of_nonneg_left _ hsq
      change U.Ex (fun i => H (q.smaller i))+(1/4:ℝ)*(q.norm/q.mass)*fax q ≤ H q at ht₁
      linarith
    _ ≤ _ := by
      rw [hEq,mul_assoc,hDC]
      exact mul_le_mul_of_nonneg_left h₂ (div_nonneg hm.le hd.le)

/-- average of forward statistics under uniform output path -/
def stats {s : Scene M} (t : Thread M s) (L : Path M → ℝ) :=
    (s.here.dice M).Ex (fun x => L (t.stream x))

lemma stats_cons {s q : Scene M} {k} (h : Following j J f (ran s q k)) (F : Path M → ℝ) :
    stats (ran s q k) F =
      (uniform Bool).Ex (fun b => stats (k b) (fun l => F (⟨s,q,b⟩::l))) :=
  stream_branch k h (fun l _ => F l)

lemma stat_pay (s : Scene M) (t : Thread M s) (g : Beat M → ℝ) :
    stats t (subtotal g)=Thread.fee t g := rfl
lemma stats_nil (s : Scene M) (F : Path M → ℝ) : stats (blank s) F=F [] := by simp [stats,stream,Ex_const]
lemma stats_plus {s : Scene M} (t : Thread M s) (f g : Path M → ℝ) :
    stats t (fun l => f l+g l)=stats t f+stats t g :=
    Ex_add _ (f:=fun _ => f _) (g:=fun _ => g _)
lemma stats_fix {s : Scene M} (t : Thread M s) (r : ℝ) : stats t (fun _ => r)=r :=
    Ex_const _ _

lemma caveat_total {s : Scene M} (t : Thread M s) (h : Following j J f t) (hp : Fit s) :
    stats t fullFax ≤ 4*caveat s j := by
  change t.fee billFax ≤ _
  induction t with
  | blank s =>
    change stats (blank s) fullFax ≤ _
    rw [stats_nil, show fullFax (M:=M) [] = 0 from rfl]
    linarith [caveat_pos s j hp]
  | ran s q k ih =>
    have hx := jump_ideal h hp.lift
    have HH := caveat_step h hx
    rw [fee_ran _ h,Ex_add,show (uniform Bool).Ex (fun b : Bool => billFax ⟨s,q,b⟩) = fax q from by unfold billFax; exact Ex_const (uniform Bool) (fax q)]
    apply le_trans (b:=fax q+(uniform Bool).Ex fun b => 4*caveat (q.smaller b) j)
    · gcongr
      apply Ex_mono
      intro b
      exact ih b (h.2.2.2.2.2 b) (hx.climb.child b)
    rw [Ex_lmul]; linarith

lemma showers_total (e : Streak M)
    {s : Scene M} (t : Thread M s) (h : Following j J f t) (hp : Fit s) :
    stats t e.showers ≤ 4-energy s e.u+8*stats t fullKills := by
  let g (b : Beat M) := shower e.u b.post
  change t.fee g ≤ 4-energy s e.u+8*t.fee killed
  induction t with
  | blank s =>
    have Hh := (energy_small hp e.u).2.trans hp.lift
    simp [Thread.fee,stream,Ex_const]; linarith
  | ran s q k ih =>
    let U := uniform Bool
    have H := jump_ideal h hp.lift
    have HE (b : Bool) := ih b (h.2.2.2.2.2 b) (H.climb.child _)
    rw [fee_ran _ h,fee_ran _ h]
    simp_rw [Ex_add]
    rw [Ex_const U (shower e.u q)]
    have HH : U.Ex (fun b => energy (q.smaller b) e.u) = energy q e.u+shower e.u q := by
      rw [show U=uniform Bool from rfl,fair_av]; exact wet_average q H.climb e.u
    have HF := (energy_drain (b:=⟨s,q,false⟩) H e.u)
    let K := killed (Thread.Beat.mk s q false)
    have HR : (uniform Bool).Ex (fun b => killed ⟨s,q,b⟩) = K := Ex_const U K
    have HT := U.Ex_mono HE
    rw [Ex_add,Ex_lmul,Ex_sub (f:=fun _=> 4),Ex_const,HH] at HT
    rw [HR]
    change |energy s _-energy q _| ≤ 8*K at HF
    change shower e.u q + U.Ex _ ≤ _ +8*(K+U.Ex _)
    linarith [(abs_le.mp HF).2]

lemma flag_point (s : Scene M) (e : Streak M) :
    e.b^2* e.flag s ≤ 128*surcharge s true (e.i-1) := by
  unfold Streak.flag
  split_ifs with h
  · rw [surcharge,ite_eq_left h.2]
    apply le_trans (b:=128*gateWidth true (e.i-1))
    · change side e.i^2*1 ≤ 128*(side (e.i-1)^2 / 128)
      have hh : side e.i ≤ side (e.i-1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      nlinarith [side_pos e.i]
    · exact mul_le_mul_of_nonneg_left h.2 (by norm_num)
  rw [mul_zero]
  exact mul_nonneg (by norm_num) (surcharge_nonneg s true _)

lemma flag_total (e : Streak M) {s : Scene M} (t : Thread M s) :
    e.b^2 * stats t e.flagged ≤
      128 * Thread.fee t (fun b => surcharge b.post true (e.i-1)) := by
  change e.b^2 * t.fee _ ≤ _

  unfold Thread.fee
  rw [← Ex_lmul,← Ex_lmul]
  apply Ex_mono; intro x
  generalize t.stream x = l
  induction l with
  | nil => change _*0 ≤ _*0; exact le_of_eq (by ring)
  | cons b l ih =>
    rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons]
    linarith [flag_point b.post e]

lemma sum_budget_run :
    ∀ᶠ j : ℕ in atTop,
      ∀ M J : ℕ, ∀ f : Grid M → ℝ, ∀ s q : Scene M, ∀ k,
        Following j J f (.ran s q k) → Fit s → q.live=true →
        (∀ x, f x ≤ exp (height j)) →
        ∀ e : Streak M,
          let v := ran s q k
          stats v fullKills ≤ 4 ∧ stats v e.showers ≤ 36 ∧
            stats v fullFax ≤ 10^26*height j ∧ e.b^2 * stats v e.flagged ≤ 10^6*height j := by
  filter_upwards [segment_cost,side_deficit, hpoly 12800 32] with j h1 h2 ht
    M J f s q k h hh hx hF e v
  have hk := jump_ideal h hh.lift
  have hq := pre_pos h
  have hR : q.mass ≤ s.mass := hk.lower.mass_le hh.ready.2 hh.ready.1
  have hT := h.2.2.2.1.2.1
  let d := height j
  have hM : exp (-d) ≤ q.mass := le_of_not_gt (fun H => hT ⟨hx,Or.inr H⟩)
  have hE : -d ≤ log s.mass := by
    rw [←log_exp (-d)]
    exact log_le_log (exp_pos _) (hM.trans hR)
  have he : (minimumT j)⁻¹ ≤ height j := by unfold minimumT; rw [one_div,inv_inv]; exact ht
  have HP : stats v fullKills ≤ 4 :=
    le_trans (deaths v h hh.pos) hh.lift
  refine ⟨HP, le_trans (showers_total e v h hh)
    (by linarith [(energy_small hh e.u).1]),le_trans (caveat_total v h hh) ?_,
      le_trans (flag_total e v) ?_⟩
  · have HL := h2 M J s f (rooted _ h) hF hq
    have HJ : 0 ≤ share s ∧ share s ≤ 4 := ⟨share_pos' _ hh.ready hh.pos.le,hh.lift⟩
    have HY : 0 ≤ deficit s (channel (dye s)) := deficit_nonneg s hh.ready.1 hh.ready.2 hq _
    unfold caveat
    have h₃ : deficit s (channel (dye s)) + (minimumT j)⁻¹ ≤ 10^23*d+d+d := by
      change deficit s _ ≤ _ at HL; unfold dye d at *; linarith
    have h₄ : 0 ≤ d := (d_pos j).le
    change _ ≤ 10^26*d
    nlinarith
  · have H₁ := h1 M J s f v h hF hq hh.pos (fun _ => e.i-1) true
    have H₂ : 0 ≤ s.mass/s.norm := div_nonneg hq.le hh.pos.le
    have H₃ : s.mass/s.norm ≤ 4 := hh.lift
    have H₄ : 128*(2*height j-log s.mass) ≤ 384*d := by unfold d at *; linarith
    have h₄ : 0 ≤ d := (d_pos j).le
    nlinarith



end FourierLLogL.Dyadic.Procedure.Paths

end OAI
