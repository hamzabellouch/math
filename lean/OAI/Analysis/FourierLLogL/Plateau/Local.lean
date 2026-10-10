import OAI.Analysis.FourierLLogL.Plateau.Output

/-! # Local costs and projected edge bounds -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Thread
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse
variable {M J j : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical

lemma debt_at {s q : Scene M} {l} (h : Following j J f (ran s q l)) :
    let P := (keep s q).snip.probs
    entropy P ≤ (minimumT j)⁻¹*P false := by
  let v := keep s q
  intro P
  have hm := pre_pos h
  obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
  have hf := kept_mass hb.1 ⟨ha.within,ha.positive⟩ ⟨hc.within,hc.positive⟩ hm
  change q.mass = P true * s.mass at hf
  have Ht : P true+P false=1 := by simpa [Fintype.sum_bool] using P.total
  rcases hb.2 with hh | hh
  · have hi : P true=1 := by nlinarith
    have hj : P false=0 := by linarith
    unfold entropy Law.crossE Ex
    simp [hi,hj]
  have hi : minimumT j ≤ P false := by nlinarith
  have hj : 1 ≤ (minimumT j)⁻¹ * P false := by
    rw [← div_eq_inv_mul]; exact (one_le_div (minimum_pos _)).mpr hi
  have HH := entropy_le_log_card P
  simp only [Fintype.card_bool,Nat.cast_ofNat] at HH
  linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]

lemma debt_total (t : Thread M s) (h : Following j J f t) :
    (unfoldW t).spotDebt ≤ (minimumT j)⁻¹ := by
  let a := (minimumT j)⁻¹
  have hp := (inv_pos.mpr (minimum_pos j)).le
  induction t with
  | blank => rw [unfoldW,extraDebt]; exact hp
  | ran s q l ih =>
    let v := (keep s q).snip
    have hx := h.2.2.2.2.2
    have h0 : ∀ b, (unfoldW (l b)).spotDebt ≤ a := fun b => ih b (hx b)
    let K := Wire.link q true fun b => unfoldW (l b)
    have HE : K.spotDebt ≤ a := (Ex_mono _ h0).trans (Ex_const _ _).le
    have HM := debt_at h
    rw [unfoldW,splice,spotDebt,Ex,Fintype.sum_bool]
    change v.probs.entropy+(v.probs true*K.spotDebt+v.probs false*spotDebt (extra (other s q) _)) ≤ a
    rw [extraDebt,mul_zero,add_zero]
    have hQ : v.probs true + v.probs false = 1 := by simpa [Fintype.sum_bool] using v.probs.total
    change v.probs.entropy ≤ a * v.probs false at HM
    nlinarith [v.probs.nonneg true]

lemma segment_cost :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ t : Thread M s, Following j J f t → (∀ x, f x ≤ exp (height j)) →
        0 < s.mass → 0 < s.norm →
        ∀ (p : Policy M) (b : Bool), t.fee (fun i => surcharge i.post b (p i.post)) ≤
          s.mass/s.norm * (128*(2*height j-log s.mass)) := by
  filter_upwards [hpoly 12800 32] with j hg M J s f t h hf hm hn p b
  rw [surcharge_wire _ _ _ h hm hn]
  let T := unfoldW t
  have hu := rooted _ h
  have hk := splice_valid t h
  have H := edge_total p b T hk hm 0 (fun _ => Or.inl rfl)
  have HX := due_all T true hk hm
  have HD : T.spotDebt ≤ height j :=
    (debt_total t h).trans (by
      unfold minimumT; rw [one_div,inv_inv]; exact hg)
  have hi := local_deficit_dry s (uniform Unit) hu.within hu.positive hm (height j) (fun x => le_trans (hu.sub x) (hf x))
  rw [deficit,privateH_const] at hi
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  change T.expenditure _ ≤ _
  norm_num at *; linarith


lemma side_deficit :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      s.Safe j J f → (∀ x, f x ≤ exp (height j)) → 0 < s.mass →
      deficit s (channel s.fund.mood) ≤
        10^23*height j-log s.mass := by
  filter_upwards [Fund.fund_est, Fund.envelope_scale, hpoly (3000*capA) 1] with j hH hv h
    M J s f hs hf hm
  let p := s.here
  let c := s.fund
  let A := c.mood; let k := channel A
  let P := s.actor; let d := height j
  let v := fun _ : Grid M => uniform Unit
  let Q := channel (place c.anchor M) (c.anchor.start M)
  have hp := hs.capital
  have h1 := replace_signal P v k (fun _ => Q) (fun i t => ch_pos _ _ _)
  have hE : (P.withNext v).Ex (fun x => (k x.1).kl Q) ≤ F A-log c.anchor.invlen+300 := by
    rw [Ex_withNext]; simp_rw [Ex_const]
    rw [← Ex_const P (F A-log c.anchor.invlen+300)]
    apply Ex_mono_mem _
    intro x hx
    have he : x ∈ c.anchor.block M :=
      block_of_below hp.domain M (piece_support hs.within (actor_def hs.within hs.positive hm) _ hx)
    exact (kl_ex _ _).le.trans (side_entropy hp.effects _ he)
  have ht := local_deficit_dry s (uniform Unit) hs.within hs.positive hm d
    (fun x => (hs.sub x).trans (hf x))
  have hi := hp.solvent
  have H := hp.relative
  have HE := ((hH M).2 s.fund s.here hp).1
  have hr : 1 ≤ d := hv.2.2.1
  change c.bank ≤ (1000+ reserve capA)*d at hi
  change F A ≤ _+3000*c.uses+400*c.spend at H
  change c.spend ≤ 2*(c.bank+1) at HE
  have hT : 3000*(c.uses:ℝ) ≤ d := by
    rw [pow_one] at h
    have hx := hp.under; unfold d c; linarith
  change (P.withNext v).Ex _ ≤ F A-log c.anchor.invlen+300 at hE
  change levels s - P.privateH v ≤ _ at ht
  change levels s - P.privateH k ≤ 10^23*d-log s.mass
  apply le_trans (b:=d-log s.mass+ (F A-log c.anchor.invlen+300))
  · linarith
  unfold reserve capA at *
  change F A ≤ log c.anchor.invlen + _ + _ at H; linarith

def killed (b : Beat M) := (b.pre.mass-b.post.mass) / b.pre.norm

/-- Averaging future removals along uniform output paths, not actual input-choice paths. -/
lemma deaths (t : Thread M s) (h : Following j J f t) (hr : 0 < s.norm) :
    t.fee killed ≤ s.mass/s.norm := by
  induction t with
  | blank =>
    simp [fee,stream,Ex_const]; exact div_nonneg (Thread.rooted _ h).mass_lower hr.le
  | ran s q k ih =>
    rw [fee_ran _ h]
    obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
    let P := uniform Bool
    let F := fun b : Bool => (q.smaller b).mass
    have hi (b : Bool) : (k b).fee killed ≤ F b/q.norm := by
      apply ih b (hk b)
      change 0 < q.norm; rw [hb.1.flat]; exact hr
    rw [Ex_add,show (fun b : Bool => killed ⟨s,q,b⟩) = (fun _ => (s.mass-q.mass)/s.norm) from rfl,Ex_const]
    have hh := P.Ex_mono hi
    rw [show P.Ex (fun b => F b / q.norm)=P.Ex F / q.norm by simp_rw [div_eq_mul_inv, Ex_mul]] at hh
    have HX : P.Ex F=q.mass := by
      unfold P F mass; rw [Ex,Fintype.sum_bool, uniform_apply,uniform_apply,Fintype.card_bool,Nat.cast_ofNat]
      simp only [smaller,child]
      rw [avg_split_real q.here]; ring
    rw [HX,hb.1.flat] at hh
    change _ + P.Ex _ ≤ _
    linarith [show (s.mass-q.mass)/s.norm=s.mass/s.norm-q.mass/s.norm by ring]

end FourierLLogL.Dyadic.Procedure.Thread

end OAI
