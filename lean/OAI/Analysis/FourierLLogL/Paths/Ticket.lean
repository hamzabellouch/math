import OAI.Analysis.FourierLLogL.Paths.Troupe
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
open Plot

def entry (s : Scene M) := s.norm=s.mass

lemma entry_share {s : Scene M} (h : Fit s) (e : entry s) : share s=1 := by
  unfold share entry at *; rw [←e,div_self h.pos.ne']

lemma old_budget :
    ∀ᶠ j : ℕ in atTop,
      (minimumT j)⁻¹ ≤ height j ∧
      ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
        s.Safe j J f → Fit s → entry s →
        (∀ x, f x ≤ exp (height j)) →
        ∀ b : Bool, deficit s (channel (optic s b))+(minimumT j)⁻¹ ≤ 10^24*amount s j := by
  filter_upwards [side_deficit,hpoly 12800 32] with j ht hh
  have H : (minimumT j)⁻¹ ≤ height j := by unfold minimumT; rw [one_div,inv_inv]; exact hh
  refine ⟨H,?_⟩
  intro M J s f h hp e hf b
  let x := height j; let y := amount s j
  have hm : 0 < s.mass := e ▸ hp.pos
  have hx := (amount_limits s j).2
  have hy : -log s.mass ≤ y := by
    unfold entry at e; rw [←e]; unfold y amount
    linarith [d_pos j,le_max_left (-log s.norm) 0]
  have hZ := ht M J s f h hf hm
  cases b
  · unfold optic; rw [ite_eq_right (by simp),funext no_label]
    have H₁ := local_deficit_dry s (uniform (Grid M)) hp.ready.1 hp.ready.2 hm x
      (fun i => (h.sub i).trans (hf i))
    unfold y x at *
    linarith [d_pos j]
  · simp only [optic,ite_true]
    unfold y at *; linarith [d_pos j]

def scaleC (i : ℕ) : ℝ := 2^i
lemma scale_one (i : ℕ) : 1 ≤ scaleC i := one_le_pow₀ (by norm_num)
lemma scale_pos (i : ℕ) : 0 < scaleC i := lt_of_lt_of_le zero_lt_one (scale_one i)
lemma scale_side (i : ℕ) : side i = (scaleC i)⁻¹ := by unfold scaleC; rw [side_pow_two]

lemma prescale (p : Plot) : (precision p.ix p.cap:ℝ) ≤ 100*(scaleC p.ix* scaleC p.cap) := by
  have H (i : ℕ) : (i:ℝ) ≤ scaleC i := by
    unfold scaleC; exact_mod_cast Nat.lt_two_pow_self.le
  have hi := scale_one p.cap; have he := scale_one p.ix
  unfold precision
  push_cast; nlinarith [H p.cap,H p.ix]

lemma marker_one (p : Plot) : p.marker ≤ 1 ∧ 1/p.marker ≤ 10^14 * (scaleC p.ix)^12 := by
  let x := side p.ix; let v := scaleC p.ix
  have hx : 0 < x := side_pos _; have hv : 0 < v := scale_pos _
  have ht : x = v⁻¹ := scale_side _
  have he₁ : x^6 ≤ 1 := pow_le_one₀ hx.le (side_le _)
  unfold marker sharp; change (x^6/32768)^2/16 ≤ 1 ∧ _ ≤ _
  constructor
  · nlinarith [pow_pos hx 6]
  · change 1/((x^6/32768)^2/16) ≤ 10^14*v^12
    rw [ht]
    field_simp
    nlinarith [pow_pos hv 12]

def broadMass (l : Path M) (g : Grade) : ℕ :=
    (goal g.i g.main (Chart.classic M) l).size

lemma prelude :
    ∀ᶠ j : ℕ in atTop,
      ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ, ∀ t : Thread M s,
        t.Following j J f → Fit s → entry s →
        (∀ x, f x ≤ exp (height j)) →
        ∀ p : Plot,
          let x := amount s j
          let g := grade p
          let B := scaleC p.ix
          let D := scaleC p.cap
          stats t (minted p (vacant M)) ≤ 10^50*B^14*x*D^4 ∧
            stats t (fun l => (broadMass l g:ℝ)) ≤ 10^31*B^6*x := by
  filter_upwards [old_budget] with j hj M J s f t h hp hh hF p x g B D
  have he : 1 ≤ x := (amount_limits s j).1
  have HD : 1 ≤ D := scale_one p.cap; have HB : 1 ≤ B := scale_one p.ix
  let c := vacant M
  have hc : c.chart.Sound := classic_sound M
  have hS : share s=1 := entry_share hp hh
  have HT := mint_small p c s t h hc
    (show soundPrev c from fun s hs => by cases hs)
    (show p.cardStep c from by simp [cardStep,c,vacant,classic,Chart.size]) hp.pos
  have HP : deficit s (channel (optic s p.main))+(minimumT j)⁻¹ ≤ 10^24*x :=
    hj.2 M J s f (Thread.rooted _ h) hp hh hF _
  have hh : (p.creditsC c)=D := by simp [creditsC,c,vacant,classic,rangeIx,D,scaleC,Chart.size]
  constructor
  · have HH : p.debtC c s j ≤ 10^24*x+100*(B*D^3) := by
      have H₁ := (sight_budget s p.main c.chart.items (precision p.ix p.cap)).2
      change deficit s (p.kObs c s) ≤ _ at H₁
      rw [show c.chart.items.card=0 by simp [c,vacant,classic],Nat.cast_zero,zero_mul,add_zero] at H₁
      unfold debtC; rw [hh]
      have hF₁ : D*p.coinC ≤ 100*(B*D^3) := by
        have H := prescale p
        have hZ : p.coinC = D*(precision p.ix p.cap) := by simp [coinC,rangeIx,D,scaleC]
        rw [hZ]
        change _ ≤ 100*(B*D) at H
        have hv := mul_le_mul_of_nonneg_left H (sq_nonneg D); linarith
      linarith
    have hh₂ : p.slotC c ≤ D+1 := by
      unfold slotC; rw [hh,ite_eq_left (show c.previous=none from rfl)]
      exact mul_le_of_le_one_left (by positivity) (marker_one p).1
    have hh₃ : p.expenses c s j ≤ 10^26* (B*x*D^4) := by
      unfold expenses; rw [hS,show p.deltaC c s=0 from rfl]
      have HX : 0 ≤ B*D^3 := by positivity
      have HL : B*D^3 ≤ B*x*D^4 := by gcongr; all_goals nlinarith
      have HT : D ≤ B*D^3 := (by calc
        D ≤ D^3 := by simpa using pow_le_pow_right₀ HD (show 1 ≤ 3 by omega)
        _ ≤ _ := by nlinarith [pow_nonneg (le_trans (by norm_num) HD) 3])
      have HZ : x ≤ B*x*D^4 := by apply le_trans (b:=B*x) (by nlinarith); exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ HD)
      nlinarith
    have HI : stats t (minted p c) ≤ (1/p.marker)*p.expenses c s j := by
      rw [one_div,← div_eq_inv_mul]
      apply (le_div_iff₀ (p.marker_pos)).mpr
      rw [mul_comm]; exact HT
    apply HI.trans
    have hz := (marker_one p).2
    calc
      _ ≤ (10^14*B^12)*(10^26*(B*x*D^4)) := by
        exact mul_le_mul hz hh₃ (expenses_nonneg p c _ j
          (show p.cardStep c from by simp [cardStep,c,vacant,classic,Chart.size]) hp.ready
          (show soundPrev c from fun s hs => by cases hs) hp.pos) (by positivity)
      _ ≤ _ := by
        have HV := pow_le_pow_right₀ HB (show 13≤14 by omega)
        nlinarith [mul_le_mul_of_nonneg_right HV (show 0 ≤ x*D^4 by positivity),
          show 0 ≤ B^14*x*D^4 by positivity]
  · have H := buildup_total s t f h p.main p.ix c.chart hc hp.pos
    let r := amp p.ix p.main; let m := stats t (fun l => (broadMass l g:ℝ))
    have hr := amp_pos p.ix p.main; change 0 < r at hr
    have Heq (x' : Grid M) :
        buildup p.ix p.main c.chart (t.stream x')=(broadMass (t.stream x') g:ℝ) := by
      unfold buildup; rw [show c.chart.size=0 by simp [c,vacant,classic,Chart.size]]
      simp only [Nat.cast_zero,sub_zero]; rfl
    simp_rw [Heq] at H
    rw [show s.mass/s.norm=_ from hS,one_mul
      ] at H
    have hh : chartDebt s j c.chart p.main ≤ 10^24*x := by
      unfold chartDebt; apply le_trans _ HP
      change flex s p.main (fun _ _ => 1)+_ ≤ _; rw [flex_one]
    change (r/2*(r^2/2048))*m ≤ _ at H
    have hi : 1/B^2 ≤ r := by
      have HE := (strength_bounds p.main (side_pos p.ix) (side_le p.ix)).2.2
      rw [scale_side] at HE
      unfold r amp; rw [scale_side]; unfold B; simpa only [one_div,inv_pow] using HE
    change m ≤ _
    have hT : 4096 * 10^24*x / r^3 ≤ 4096*10^24*x*B^6 := by
      have hB : 0 < B := by positivity
      calc
        _ ≤ 4096*10^24*x/(1/B^2)^3 := by gcongr
        _ = _ := by field_simp
    apply le_trans (le_trans ?_ hT)
    · have H : 0 ≤ x*B^6 := by positivity
      linarith
    apply (le_div_iff₀ (pow_pos hr _)).mpr; nlinarith

end Troupe


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
