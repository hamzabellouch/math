import OAI.NumberTheory.TwoPoint.Halasz.HalaszFirstDerivative
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Locate the unique possible stationary point and quantify the slope
away from it on a positive finite interval. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_log_slope_drop (u v b x y : ℝ) (hu : 0 ≤ u)
    (hx : 0 < x) (hxy : x ≤ y) (hyb : y ≤ b) :
    u*(y-x)/b^2 ≤ halaszLogSlope u v x-halaszLogSlope u v y := by
  have hy : 0 < y := hx.trans_le hxy
  have hb : 0 < b := hy.trans_le hyb
  have hprod : x*y ≤ b^2 := by nlinarith
  calc
    _ ≤ u*(y-x)/(x*y) := div_le_div_of_nonneg_left
      (mul_nonneg hu (sub_nonneg.mpr hxy)) (mul_pos hx hy) hprod
    _ = _ := by unfold halaszLogSlope; field_simp; ring

lemma halasz_log_stationary_center (u v a b : ℝ) (hu : 0 ≤ u)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ c ∈ Set.Icc a b,
      (∀ x ∈ Set.Icc a b, x < c → u*(c-x)/b^2 ≤ halaszLogSlope u v x) ∧
      (∀ x ∈ Set.Icc a b, c < x → u*(x-c)/b^2 ≤ -halaszLogSlope u v x) := by
  by_cases hb : 0 ≤ halaszLogSlope u v b
  · refine ⟨b, ⟨hab, le_rfl⟩, ?_, ?_⟩
    · intro x hx hxb
      have hh := halasz_log_slope_drop u v b x b hu (ha.trans_le hx.1) hxb.le le_rfl
      linarith
    · intro x hx hbx
      exact (not_lt_of_ge hx.2 hbx).elim
  by_cases ha' : halaszLogSlope u v a ≤ 0
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_, ?_⟩
    · intro x hx hxa
      exact (not_lt_of_ge hx.1 hxa).elim
    · intro x hx hax
      have hh := halasz_log_slope_drop u v b a x hu ha hax.le hx.2
      linarith
  have hc : ContinuousOn (halaszLogSlope u v) (Set.Icc a b) :=
    (continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')).sub
      continuousOn_const
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc' hab hc
    (show (0:ℝ) ∈ Set.Icc (halaszLogSlope u v b) (halaszLogSlope u v a) by
      exact ⟨(lt_of_not_ge hb).le, (lt_of_not_ge ha').le⟩)
  refine ⟨c, hc, ?_, ?_⟩
  · intro x hx hxc
    have hh := halasz_log_slope_drop u v b x c hu (ha.trans_le hx.1) hxc.le hc.2
    linarith
  · intro x hx hcx
    have hh := halasz_log_slope_drop u v b c x hu (ha.trans_le hc.1) hcx.le hx.2
    linarith

/-- Uniform square-root cancellation for an individual Poisson integral. -/
theorem halasz_log_stationary_integral (u v a b : ℝ) (hu : 0 < u)
    (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x in a..b, halaszLogPhase u v x‖ ≤ 10*b/Real.sqrt u := by
  have hb : 0 < b := ha.trans_le hab
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  let r := b/Real.sqrt u
  let lam := Real.sqrt u/b
  have hr : 0 < r := div_pos hb hsu
  have hlam : 0 < lam := div_pos hsu hb
  have he : u*r/b^2 = lam := by
    dsimp [r, lam]
    have hs := Real.sq_sqrt hu.le
    field_simp
    nlinarith
  have hrec : 4/lam = 4*r := by dsimp [lam, r]; field_simp
  obtain ⟨c, hc, hleft, hright⟩ := halasz_log_stationary_center u v a b hu.le ha hab
  let l := max a (c-r)
  let q := min b (c+r)
  have hal : a ≤ l := le_max_left _ _
  have hlc : l ≤ c := max_le hc.1 (by linarith)
  have hcq : c ≤ q := le_min hc.2 (by linarith)
  have hqb : q ≤ b := min_le_left _ _
  have hlq : l ≤ q := hlc.trans hcq
  have hi (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) :
      IntervalIntegrable (halaszLogPhase u v) volume x y :=
    (halasz_log_phase_continuousOn u v x y (ha.trans_le hax)).intervalIntegrable_of_Icc hxy
  have hLI : ‖∫ x in a..l, halaszLogPhase u v x‖ ≤ 4*r := by
    by_cases hla : l = a
    · simp only [hla, intervalIntegral.integral_same, norm_zero]
      positivity
    have hal' : a < l := lt_of_le_of_ne hal (Ne.symm hla)
    have hl : l = c-r := max_eq_right (by
      have hh : a < max a (c-r) := hal'
      exact (lt_max_iff.mp hh).resolve_left (lt_irrefl a) |>.le)
    have hh := halasz_log_first_derivative u v a l lam hu.le ha hal hlam (by
      intro x hx
      have hxc : x < c := by rw [hl] at hx; linarith [hx.2]
      have hd := hleft x ⟨hx.1, hx.2.trans (hlc.trans hc.2)⟩ hxc
      have hdist : r ≤ c-x := by rw [hl] at hx; linarith [hx.2]
      have hscale := mul_le_mul_of_nonneg_left hdist hu.le
      have hd' : lam ≤ halaszLogSlope u v x := by
        rw [← he]
        exact (div_le_div_of_nonneg_right hscale (sq_nonneg b)).trans hd
      exact hd'.trans (le_abs_self _))
    rwa [hrec] at hh
  have hRI : ‖∫ x in q..b, halaszLogPhase u v x‖ ≤ 4*r := by
    by_cases hqb' : q = b
    · simp only [hqb', intervalIntegral.integral_same, norm_zero]
      positivity
    have hqb'' : q < b := lt_of_le_of_ne hqb hqb'
    have hq : q = c+r := min_eq_right (by
      have hh : min b (c+r) < b := hqb''
      exact (min_lt_iff.mp hh).resolve_left (lt_irrefl b) |>.le)
    have hh := halasz_log_first_derivative u v q b lam hu.le (ha.trans_le (hc.1.trans hcq)) hqb hlam (by
      intro x hx
      have hcx : c < x := by rw [hq] at hx; linarith [hx.1]
      have hd := hright x ⟨(hc.1.trans hcq).trans hx.1, hx.2⟩ hcx
      have hdist : r ≤ x-c := by rw [hq] at hx; linarith [hx.1]
      have hscale := mul_le_mul_of_nonneg_left hdist hu.le
      have hd' : lam ≤ -halaszLogSlope u v x := by
        rw [← he]
        exact (div_le_div_of_nonneg_right hscale (sq_nonneg b)).trans hd
      exact hd'.trans (neg_le_abs _))
    rwa [hrec] at hh
  have hMI : ‖∫ x in l..q, halaszLogPhase u v x‖ ≤ 2*r := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := q) (C := (1:ℝ)) (f := halaszLogPhase u v)
      (fun x _ => (halasz_log_phase_norm u v x).le)
    rw [abs_of_nonneg (sub_nonneg.mpr hlq), one_mul] at hh
    have hll : c-r ≤ l := le_max_right _ _
    have hqq : q ≤ c+r := min_le_right _ _
    linarith
  have hsplit : (∫ x in a..b, halaszLogPhase u v x) =
      (∫ x in a..l, halaszLogPhase u v x) +
        (∫ x in l..q, halaszLogPhase u v x) +
        ∫ x in q..b, halaszLogPhase u v x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi a l le_rfl hal) (hi l q hal hlq),
      intervalIntegral.integral_add_adjacent_intervals (hi a q le_rfl (hal.trans hlq)) (hi q b (hal.trans hlq) hqb)]
  rw [hsplit]
  have hn := norm_add_le
    ((∫ x in a..l, halaszLogPhase u v x)+(∫ x in l..q, halaszLogPhase u v x))
    (∫ x in q..b, halaszLogPhase u v x)
  have hn' := norm_add_le (∫ x in a..l, halaszLogPhase u v x)
    (∫ x in l..q, halaszLogPhase u v x)
  have he10 : 10*b/Real.sqrt u = 10*r := by dsimp [r]; ring
  rw [he10]
  linarith

end TwoPointCorrelations

end OAI
