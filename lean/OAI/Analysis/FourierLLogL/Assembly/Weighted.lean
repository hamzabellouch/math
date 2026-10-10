import OAI.Analysis.FourierLLogL.Assembly.Verdict
import OAI.Analysis.FourierLLogL.Procedure.Rare
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

lemma burn_rate :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, 1000*((2:ℝ)^J) ≤ 2^M →
      ∀ f : Grid M → ℝ, (∀ x, f x ≤ exp (height j)) →
      let s := beginPlay f true
      ∀ t : Road j M s, Trusted J f t → 1/Thermal.H j ≤ s.mass →
        coldFee t ≤ 10^220*height j := by
  filter_upwards [rare,log_mass_budget,hpoly 1 4] with j h1 h2 hd M J hm f hf s t h hh
  let a := Thermal.H j; let d := height j; let P := s.actor
  let c := 10*limitC
  have hp : 1 ≤ a := H_ge j
  have ha : 0 < a := H_pos j
  have he : a^4 ≤ d := by simpa using hd
  have hD : 1 ≤ d := one_le_pow₀ (by norm_num)
  let k (x : Grid M) := t.hike x
  let w (x : Grid M) := if (k x).froze then (1:ℝ) else 0
  let y (x : Grid M) := drought (k x).done.mass
  have HX : P.Ex w ≤ 1/a^10 := by
    apply le_trans _ (h1 M J hm f hf t h hh)
    apply Ex_mono; intro x; unfold w
    cases he : (k x).froze <;> simp_all only [k,Bool.false_eq_true,↓reduceIte,le_refl]
  have HH : P.Ex (fun i => y i^2) ≤ (c*a)^2 := h2 M J s f t h hh
  let L := fun i => w i*y i
  let K := fun i => w i*y i^2
  have hw (i) : w i ≤ 1 ∧ w i^2=w i := by unfold w; split <;> norm_num
  have H : P.Ex K ≤ (c*a)^2 := le_trans (Ex_mono _ fun i =>
    mul_le_of_le_one_left (sq_nonneg (y i)) (hw _).1) HH
  have HC : P.Ex L ≤ c := by
    have Heq := Law.sq_Ex_mul P w y
    simp_rw [(hw _).2] at Heq
    have HJ : P.Ex w * P.Ex (fun i => y i^2) ≤ (1/a^10)*(c*a)^2 :=
      mul_le_mul HX HH (Ex_nonneg _ (fun _ => sq_nonneg _)) (by positivity)
    have HF : (1/a^10)*(c*a)^2 ≤ c^2 := by
      apply le_trans (b:=(1/a^2)*(c*a)^2)
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hp (by omega))
      exact le_of_eq (by field_simp)
    change (P.Ex L)^2 ≤ _ at Heq
    have hP : 0 < c := by unfold c limitC; norm_num
    nlinarith
  have heq (x : Grid M) : coldLump (k x) =
      10^150* ((a+1)*(d+2)*w x+(a+d+3)*L x+K x) := by
    unfold coldLump chargeStatic
    unfold L K w y
    split_ifs <;> unfold d a <;> ring
  unfold coldFee expHike
  change P.Ex (fun i => coldLump (k i)) ≤ 10^220*d
  simp_rw [heq,Ex_lmul,Ex_add,Ex_lmul]
  have HR : a ≤ d := le_trans (by simpa using pow_le_pow_right₀ hp (by omega : 1≤4)) he
  have Hs : a^2 ≤ d := le_trans (pow_le_pow_right₀ hp (by omega)) he
  have HS : (a+1)*(d+2)*P.Ex w ≤ 6*d :=
    le_trans (mul_le_mul_of_nonneg_left HX (by positivity)) (by
      have H : 1/a^10 ≤ 1/a := one_div_le_one_div_of_le ha (by simpa using pow_le_pow_right₀ hp (by omega : 1≤10))
      apply (mul_le_mul_of_nonneg_left H (show 0 ≤ (a+1)*(d+2) by positivity)).trans
      rw [mul_one_div]
      apply (div_le_iff₀ ha).mpr; nlinarith)
  have HT : (a+d+3)*P.Ex L ≤ 5*d*c :=
    le_trans (mul_le_mul_of_nonneg_left HC (by positivity)) (by
      have H : 0 ≤ c := by unfold c limitC; norm_num
      nlinarith)
  unfold c limitC at *
  nlinarith

lemma grossOur :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, 1000*((2:ℝ)^J) ≤ 2^M →
      ∀ f : Grid M → ℝ, (∀ x, f x ≤ exp (height j)) →
      let s := beginPlay f true
      ∀ t : Play j M s, t.Follows J f → 1/Thermal.H j ≤ s.mass →
        yieldA t ≤ s.mass*(10^221*height j) := by
  filter_upwards [cost_overall,burn_rate,upper_total,frostCompare] with j h1 h2 h3 h4 M J hC f hf s t h hm
  have H := traced t false h
  have HP := (Play.first h).mass_lower
  let v := trace false t
  have hE := h1 M J f s t h hf
  rw [due_restart rfl,add_zero] at hE
  apply le_trans hE (mul_le_mul_of_nonneg_left ?_ HP)
  have hc := h2 M J hC f hf v H hm
  have he := h3 M J f hf v H hm
  have HH := short_trace_bound t h rfl
  apply (h4 M J f s t h rfl).trans
  change v.flatFee billOf ≤ v.flatFee upperFare at HH
  change v.flatFee billOf+coldFee v ≤ _
  linarith [d_pos j]

private lemma scale_drought (m : ℝ) (hm : 0 < m) (h : m ≤ 1) :
    m*drought m ≤ 4 ∧ m*(drought m)^2 ≤ 4 := by
  have hh' : drought m= -log m := max_eq_left (by linarith [log_nonpos hm.le h])
  let x := drought m
  have heq : m= (exp x)⁻¹ := by unfold x; rw [hh',exp_neg,inv_inv,exp_log hm]
  have H : x^2 /4 ≤ exp x := by
    have h0 : exp x=(exp (x/2))^2 := by rw [pow_two,←exp_add]; ring_nf
    have hi := add_one_le_exp (x/2)
    rw [h0]
    nlinarith [show 0 ≤ x from drought_pos m]
  have HH := mul_le_mul_of_nonneg_left H hm.le
  have Hx : m*exp x=1 := by rw [heq,inv_mul_cancel₀ (exp_pos x).ne']
  change m*x≤4 ∧ m*x^2≤4
  constructor
  · nlinarith [mul_nonneg hm.le (sq_nonneg (x-1))]
  linarith

lemma grossDry :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ f : Grid M → ℝ,
      (∀ x, f x ≤ exp (height j)) →
      let s := beginPlay f false
      ∀ t : Play j M s, t.Follows J f → s.mass ≤ 1/Thermal.H j →
        yieldA t ≤ 10^152*height j := by
  filter_upwards [cost_overall,chill_descendants,hpoly 1 1] with j h1 h2 h3 M J f hf s t h hm
  have H := h1 _ _ f s t h hf
  rw [due_restart rfl,add_zero] at H
  apply H.trans
  let m := s.mass; let d := height j; let a := Thermal.H j
  have hh : 0 ≤ m := (Play.first h).mass_lower
  have ha : 1 ≤ a := H_ge _
  have hd : 1 ≤ d := one_le_pow₀ (by norm_num)
  have hp : a ≤ d := by simpa using h3
  have hz : 0 < a := by linarith
  change m≤1/a at hm
  have hi : m*a ≤ 1 := (le_div_iff₀ hz).mp hm
  have hr : m ≤ 1 := by nlinarith
  change m*_ ≤ 10^152*d
  rcases eq_or_lt_of_le hh with hh|hh
  · rw [←hh,zero_mul]; positivity
  apply le_trans (mul_le_mul_of_nonneg_left (h2 M J f s t h rfl rfl hh) hh.le)
  let x := drought m
  change m*(10^150*(a+1+x)*(d+2+x)) ≤ _
  have he : m*x ≤ 4 ∧ m*x^2 ≤ 4 := scale_drought m hh hr
  nlinarith [mul_le_mul_of_nonneg_right hi (show 0 ≤ d by linarith),mul_le_mul_of_nonneg_right he.1
    (show 0 ≤ a by linarith),mul_le_mul_of_nonneg_right he.1 (show 0 ≤ d by linarith)]

end CastShow


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
