import OAI.Analysis.FourierLLogL.Assembly.Gross
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace CastShow
open Troupe

def drought (m : ℝ) := max (-log m) 0
lemma drought_pos (m : ℝ) : 0 ≤ drought m := le_max_right _ _
def chargeStatic (j : ℕ) (m : ℝ) :=
    10^150*(Thermal.H j +1+drought m)*(height j+2+drought m)
lemma charge_pos (j : ℕ) (m : ℝ) : 0 ≤ chargeStatic j m := by
  unfold chargeStatic
  have := H_pos j
  have := d_pos j
  have := drought_pos m
  positivity

def coldLump (v : Journal j M) := if v.froze then chargeStatic j v.done.mass else 0
def coldFee {s : Scene M} (t : Road j M s) :=
    expHike t (fun l _ => coldLump l)

lemma chill_descendants :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ f : Grid M → ℝ,
    ∀ s : Scene M, ∀ t : Play j M s, Play.Follows J f t →
      s.live=false → s.norm=0 → 0 < s.mass →
        netGross t ≤ chargeStatic j s.mass := by
  filter_upwards [cutoff_log] with j h M J f s t hF he hx hm
  let x := s.mass
  let A := height j+2+drought x
  let v := Thermal.H j; let U := 20000*v
  have HV : 1 ≤ v := H_ge j
  have hA : 0 ≤ A := by unfold A; have := d_pos j; have := drought_pos x; positivity
  have HE (q : Scene M) (hh : Safe q j J f) (h : 0 < q.mass) :
      log q.mass ≤ U :=
    le_trans (log_le_log h hh.budget) (by assumption)
  let K : ℝ := 10^140*A
  have hK : 0 ≤ K := by unfold K; positivity
  have HT (s : Scene M) (hh : x ≤ s.mass) (ht : s.live=false) :
      gateTax s.reset j ≤ K := by
    unfold gateTax amount; simp only [reset,ht, Bool.false_eq_true, ↓reduceIte]
    have hi : max (-log s.mass) 0 ≤ drought x := max_le_max_right 0 (neg_le_neg (log_le_log hm hh))
    unfold K A; linarith

  have HI {q : Scene M} (t : Play j M q) (h : Play.Follows J f t) (he : q.live=false)
      (hE : x ≤ q.norm) (hL : log q.norm ≤ U) :
      netGross t ≤ 2*K*(U-log q.norm) := by
    induction t with
    | rest q =>
      rw [netGross,trace,flat_finish]; nlinarith
    | ticket q z ih =>
      obtain ⟨ha,hb,hc,hd,hf⟩ := h
      have he₁ := hb.2.2
      have he₂ : 0 < q.norm := hm.trans_le hE
      have hv : x ≤ q.mass := by unfold enter at hd; linarith
      have HE' := ih hf he hv (HE q ha he₁)
      unfold netGross
      rw [trace,flat_push]
      change gateTax _ j+netGross z ≤ _
      have he₃ : log q.norm+1/2 ≤ log q.mass := by
        have HH := log_le_log (show 0 < 2*q.norm by positivity) (le_of_lt (show 2*q.norm < q.mass from hd))
        rw [log_mul (by norm_num) he₂.ne'] at HH
        linarith [Real.log_two_gt_d9]
      change netGross z ≤ 2*K*(U-log q.mass) at HE'
      linarith [mul_le_mul_of_nonneg_left he₃ hK,HT q hv he]
    | jump q l r il ir =>
      have HG := traced _ true h
      rw [netGross,trace,flat_fork _ _ HG]
      obtain ⟨ha,hb,hc,hd,hf⟩ := h
      rw [← Ex_const (Turn.fork (Turn.move (j:=j) (s:=q))).probs (2*K*(U-log q.norm))]
      apply Ex_mono; intro b
      cases b
      · change normStamp q j+netGross l ≤ _
        rw [normStamp,ite_eq_right (by rw [he]; simp),zero_add]
        exact il hd he hE hL
      change normStamp q j+netGross r ≤ _
      rw [normStamp,ite_eq_right (by rw [he]; simp),zero_add]
      exact ir hf he hE hL
    | attempt q u l r =>
      have HH := h.2.2.1
      rw [he] at HH; cases HH
    | freeze q w ih =>
      have HH := h.2.2.1.1
      rw [he] at HH; cases HH
  cases t with
  | rest s =>
    rw [netGross,trace,flat_finish]; exact charge_pos _ _
  | freeze s w =>
    have HH := hF.2.2.1.1
    rw [he] at HH; cases HH
  | attempt s u l r =>
    have HH := hF.2.2.1
    rw [he] at HH; cases HH
  | jump s l r =>
    have HH := share_small hF.2.1
    rw [hx] at HH
    linarith [HH.1]
  | ticket s w =>
    rw [netGross,trace,flat_push]
    have HC := HI w hF.2.2.2.2 he (le_refl _) (HE s hF.1 hm)
    change netGross w ≤ 2*K*(U-log x) at HC
    change gateTax s.reset j+netGross w ≤ 10^150*(v+1+drought x)*A
    have hz := drought_pos x
    have hx' : -log x ≤ drought x := le_max_left _ _
    apply le_trans (add_le_add (HT s le_rfl he) HC)
    unfold K U; nlinarith

/-- Every coast including virtual ends of the true live processing bills only once for static
descendants. -/
lemma frostCompare :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ f : Grid M → ℝ, ∀ s : Scene M,
    ∀ t : Play j M s, Play.Follows J f t → s.live=true →

      netGross t ≤ (trace false t).flatFee billOf + coldFee (trace false t) := by
  filter_upwards [chill_descendants] with j h M J f s t hh he
  induction t with
  | rest s =>
    unfold coldFee netGross; simp only [trace,flat_finish,zero_add]
    simp [expHike,hike,Ex_const,coldLump]
  | freeze s t ih =>
    have HX := hh.2.2.2
    have H := h M J f s.out t HX rfl rfl hh.2.1.2.2
    unfold netGross coldFee
    rw [trace,ite_eq_left rfl, flat_push]
    simp only [trace,Bool.false_eq_true,ite_false,flat_finish,zero_add]
    simp only [expHike,hike,coldLump, ↓reduceIte,Ex_const]
    change 0+netGross t ≤ _
    rw [zero_add]; exact H
  | ticket s t ih =>
    have H := ih hh.2.2.2.2 he
    unfold netGross coldFee
    rw [trace,flat_push]
    simp only [trace,flat_push]
    rw [Ex_hike_push]
    apply le_trans (add_le_add_right H _)
    rw [← add_assoc]; exact le_rfl
  | jump s l r il ir =>
    have HF := traced _ true hh
    have HG := traced _ false hh
    unfold netGross coldFee
    rw [trace,flat_fork _ _ HF]
    simp only [trace,flat_fork _ _ HG]
    rw [Ex_hike_fork HG, ← Ex_add]
    apply Ex_mono; intro b
    cases b
    · apply le_trans (add_le_add_right (il hh.2.2.2.1 he) _)
      rw [←add_assoc]; exact le_rfl
    · apply le_trans (add_le_add_right (ir hh.2.2.2.2 he) _)
      rw [←add_assoc]; exact le_rfl
  | attempt s u l r il ir =>
    have HF := traced _ true hh
    have HG := traced _ false hh
    unfold netGross coldFee; rw [trace,flat_fork _ _ HF]
    simp only [trace,flat_fork _ _ HG]
    rw [Ex_hike_fork HG, ← Ex_add]
    apply Ex_mono; intro b
    cases b
    · apply le_trans (add_le_add_right (il hh.2.2.2.2.1 he) _)
      rw [← add_assoc]; exact le_rfl
    · apply le_trans (add_le_add_right (ir hh.2.2.2.2.2 he) _)
      rw [← add_assoc]; exact le_rfl

end CastShow


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
