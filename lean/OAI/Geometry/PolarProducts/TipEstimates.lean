import OAI.Geometry.PolarProducts.HorizontalIntegrals

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

open MeasureTheory intervalIntegral Set
open scoped Real

namespace SymmetricPolar
noncomputable section

def endpointKernel (H y : ℝ) : ℝ := Real.sqrt (y / (H - y))

lemma endpointKernel_eq_rpow {H y : ℝ} (hy : 0 ≤ y) (hyH : y ≤ H) :
    endpointKernel H y = y ^ (1 / 2 : ℝ) * (H - y) ^ (-(1 / 2 : ℝ)) := by
  rw [endpointKernel, Real.sqrt_div hy, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.rpow_neg (sub_nonneg.mpr hyH), div_eq_mul_inv]

lemma intervalIntegrable_endpointKernel {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable (endpointKernel H) volume 0 H := by
  have hi : IntervalIntegrable (fun y : ℝ => (H - y) ^ (-(1 / 2 : ℝ))) volume 0 H := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := H)
      (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_left H).symm
  have hm := hi.continuousOn_mul Real.continuous_sqrt.continuousOn
  apply IntervalIntegrable.congr (f := fun y => Real.sqrt y * (H - y) ^ (-(1 / 2 : ℝ))) _ hm
  intro y hy
  rw [uIoc_of_le hH] at hy
  dsimp only
  rw [endpointKernel_eq_rpow hy.1.le hy.2, Real.sqrt_eq_rpow]

private lemma beta_three_halves_one_half :
    Complex.betaIntegral (3 / 2) (1 / 2) = (Real.pi : ℂ) / 2 := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
  have hG : Complex.Gamma (2 : ℂ) = 1 := by
    norm_num [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one]
  have hreflect := Complex.Gamma_mul_Gamma_one_sub (1 / 2)
  norm_num at hreflect
  rw [show (Real.pi : ℂ) * (1 / 2) = (Real.pi : ℂ) / 2 by ring,
    Complex.sin_pi_div_two, div_one] at hreflect
  rw [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num, hG, div_one,
    show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num,
    Complex.Gamma_add_one _ (by norm_num)]
  rw [mul_assoc, hreflect]
  ring

lemma integral_endpointKernel {H : ℝ} (hH : 0 < H) :
    (∫ y in 0..H, endpointKernel H y) = Real.pi * H / 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h := Complex.betaIntegral_scaled (3 / 2) (1 / 2) hH
  norm_num only at h
  rw [beta_three_halves_one_half] at h
  have hc : (∫ y in 0..H, (endpointKernel H y : ℂ)) =
      ∫ y in 0..H, (y : ℂ) ^ ((3 / 2 : ℂ) - 1) *
        ((H : ℂ) - y) ^ ((1 / 2 : ℂ) - 1) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hH.le] at hy
    dsimp only
    rw [endpointKernel_eq_rpow hy.1 hy.2, Complex.ofReal_mul,
      Complex.ofReal_cpow hy.1, Complex.ofReal_cpow (sub_nonneg.mpr hy.2),
      Complex.ofReal_sub]
    norm_num
  rw [hc]
  norm_num only
  rw [h]
  norm_num
  ring

lemma endpointKernel_le_one {H y : ℝ} (hH : 0 < H) (_hy : 0 ≤ y)
    (hyH : y ≤ H / 2) : endpointKernel H y ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  exact (div_le_one (by linarith : 0 < H - y)).mpr (by linarith)

lemma intervalIntegrable_dampedEndpointKernel {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable (fun y => Real.exp (-y) * endpointKernel H y) volume 0 H :=
  (intervalIntegrable_endpointKernel hH).continuousOn_mul (by fun_prop)

lemma integral_dampedEndpointKernel_le {H : ℝ} (hH : 0 < H) :
    (∫ y in 0..H, Real.exp (-y) * endpointKernel H y) ≤
      1 + Real.pi / Real.exp 1 := by
  have hhalf : 0 ≤ H / 2 := by positivity
  have hhalfH : H / 2 ≤ H := by linarith
  have hsfirst : uIcc 0 (H / 2) ⊆ uIcc 0 H := by
    simpa only [uIcc_of_le hhalf, uIcc_of_le hH.le] using
      Icc_subset_Icc le_rfl hhalfH
  have hslast : uIcc (H / 2) H ⊆ uIcc 0 H := by
    simpa only [uIcc_of_le hhalfH, uIcc_of_le hH.le] using
      Icc_subset_Icc hhalf le_rfl
  have hk := intervalIntegrable_endpointKernel hH.le
  have hf := intervalIntegrable_dampedEndpointKernel hH.le
  have hfirst : (∫ y in 0..H / 2, Real.exp (-y) * endpointKernel H y) ≤ 1 := by
    calc
      _ ≤ ∫ y in 0..H / 2, Real.exp (-y) := by
        apply intervalIntegral.integral_mono_on hhalf (hf.mono_set hsfirst)
          ((by fun_prop : Continuous (fun y : ℝ => Real.exp (-y))).intervalIntegrable _ _)
        intro y hy
        exact mul_le_of_le_one_right (Real.exp_pos _).le
          (endpointKernel_le_one hH hy.1 hy.2)
      _ ≤ 1 := by
        rw [intervalIntegral.integral_comp_neg, integral_exp]
        simp only [neg_zero, Real.exp_zero]
        linarith [Real.exp_pos (-(H / 2))]
  have hlast : (∫ y in H / 2..H, Real.exp (-y) * endpointKernel H y) ≤
      Real.exp (-(H / 2)) * (Real.pi * H / 2) := by
    calc
      _ ≤ ∫ y in H / 2..H, Real.exp (-(H / 2)) * endpointKernel H y := by
        apply intervalIntegral.integral_mono_on hhalfH (hf.mono_set hslast)
          ((hk.mono_set hslast).const_mul _)
        intro y hy
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hy.1))
          (Real.sqrt_nonneg _)
      _ = Real.exp (-(H / 2)) * ∫ y in H / 2..H, endpointKernel H y :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ Real.exp (-(H / 2)) * ∫ y in 0..H, endpointKernel H y := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply intervalIntegral.integral_mono_interval hhalf hhalfH le_rfl _ hk
        exact Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _)
      _ = _ := by rw [integral_endpointKernel hH]
  have hexp : (H / 2) * Real.exp (-(H / 2)) ≤ 1 / Real.exp 1 := by
    calc
      _ ≤ Real.exp (H / 2 - 1) * Real.exp (-(H / 2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (H / 2 - 1)]
      _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
      _ = _ := by rw [Real.exp_neg, one_div]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.mono_set hsfirst) (hf.mono_set hslast)]
  have hp := mul_le_mul_of_nonneg_left hexp Real.pi_pos.le
  have hp' : Real.exp (-(H / 2)) * (Real.pi * H / 2) ≤ Real.pi / Real.exp 1 := by
    calc
      _ = Real.pi * (H / 2 * Real.exp (-(H / 2))) := by ring
      _ ≤ Real.pi * (1 / Real.exp 1) := hp
      _ = _ := by ring
  exact add_le_add hfirst (hlast.trans hp')

def movingEndpointIntegral (k : ℕ) (a : ℝ) : ℝ :=
  (k : ℝ) * ∫ r in a..1,
    r ^ (2 * k - 1) * Real.sqrt ((1 - r) / (r - a))

lemma movingEndpointIntegral_eq {k : ℕ} (hk : 0 < k) (a : ℝ) :
    movingEndpointIntegral k a = ∫ y in 0..(k : ℝ) * (1 - a),
      (1 - y / k) ^ (2 * k - 1) * endpointKernel ((k : ℝ) * (1 - a)) y := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  let f : ℝ → ℝ := fun y =>
    (1 - y / k) ^ (2 * k - 1) * endpointKernel ((k : ℝ) * (1 - a)) y
  have hsub (r : ℝ) : f ((k : ℝ) - k * r) =
      r ^ (2 * k - 1) * Real.sqrt ((1 - r) / (r - a)) := by
    dsimp [f, endpointKernel]
    have hbase : 1 - ((k : ℝ) - k * r) / k = r := by field_simp; ring
    rw [hbase]
    congr 2
    rw [show (k : ℝ) - k * r = k * (1 - r) by ring,
      show (k : ℝ) * (1 - a) - k * (1 - r) = k * (r - a) by ring,
      mul_div_mul_left _ _ hk0]
  calc
    _ = (k : ℝ) • ∫ r in a..1, f ((k : ℝ) - k * r) := by
      simp only [movingEndpointIntegral, smul_eq_mul, hsub]
    _ = ∫ y in (k : ℝ) - k * 1..(k : ℝ) - k * a, f y :=
      intervalIntegral.smul_integral_comp_sub_mul f _ _
    _ = _ := by
      rw [show (k : ℝ) - k * 1 = 0 by ring,
        show (k : ℝ) - k * a = k * (1 - a) by ring]

lemma movingEndpointIntegral_le {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) :
    movingEndpointIntegral k a ≤ 1 + Real.pi / Real.exp 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hH : 0 < (k : ℝ) * (1 - a) := mul_pos hkR (sub_pos.mpr ha1)
  rw [movingEndpointIntegral_eq (by omega : 0 < k) a]
  apply le_trans _ (integral_dampedEndpointKernel_le hH)
  apply intervalIntegral.integral_mono_on hH.le
    ((intervalIntegrable_endpointKernel hH.le).continuousOn_mul (by fun_prop))
    (intervalIntegrable_dampedEndpointKernel hH.le)
  intro y hy
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hyk : y ≤ (k : ℝ) := by nlinarith [mul_nonneg hkR.le ha, hy.2]
  have hb0 : 0 ≤ 1 - y / (k : ℝ) := sub_nonneg.mpr ((div_le_one hkR).mpr hyk)
  have hb1 : 1 - y / (k : ℝ) ≤ 1 := sub_le_self _ (div_nonneg hy.1 hkR.le)
  exact (pow_le_pow_of_le_one hb0 hb1 (by omega : k ≤ 2 * k - 1)).trans
    (Real.one_sub_div_pow_le_exp_neg hyk)

lemma movingEndpointIntegral_le_linear {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) :
    movingEndpointIntegral k a ≤ Real.pi * ((k : ℝ) * (1 - a)) / 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hH : 0 < (k : ℝ) * (1 - a) := mul_pos hkR (sub_pos.mpr ha1)
  rw [movingEndpointIntegral_eq (by omega : 0 < k) a,
    ← integral_endpointKernel hH]
  apply intervalIntegral.integral_mono_on hH.le
    ((intervalIntegrable_endpointKernel hH.le).continuousOn_mul (by fun_prop))
    (intervalIntegrable_endpointKernel hH.le)
  intro y hy
  apply mul_le_of_le_one_left (Real.sqrt_nonneg _)
  have hyk : y ≤ (k : ℝ) := by nlinarith [mul_nonneg hkR.le ha, hy.2]
  have hb0 : 0 ≤ 1 - y / (k : ℝ) := sub_nonneg.mpr ((div_le_one hkR).mpr hyk)
  have hb1 : 1 - y / (k : ℝ) ≤ 1 := sub_le_self _ (div_nonneg hy.1 hkR.le)
  exact pow_le_one₀ hb0 hb1

end
end SymmetricPolar

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

def tailSlope (a : ℝ) : ℝ := 8/Real.pi^2 * Real.artanh a

theorem tailSlope_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) : 0 < tailSlope a := by
  apply mul_pos (by positivity)
  exact Real.artanh_pos ⟨ha, ha1⟩

theorem T_rho_ge_abs {t v u : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 ≤ v) (hu : u ∈ Icc 0 v) : |t| ≤ T (rho t u) := by
  have hmono := (horizontal_radius_strictMono hz hv).monotoneOn
  have h0 := horizontal_segment_mem hz hv (left_mem_Icc.mpr hv)
  have hU := horizontal_segment_mem hz hv hu
  have hle := hmono (left_mem_Icc.mpr hv) hu hu.1
  have hT := strictMonoOn_T.monotoneOn
    (show rho t 0 ∈ Icc (-1) 1 from ⟨(le_trans (by norm_num) (norm_nonneg _)), (norm_g_lt h0).le⟩)
    (show rho t u ∈ Icc (-1) 1 from ⟨le_trans (by norm_num) (norm_nonneg _), (norm_g_lt hU).le⟩) hle
  have he : T (rho t 0) = |t| := by simpa [rho] using T_norm_g_axis (axis_mem_D hz)
  rwa [he] at hT

theorem reciprocal_A_tail {w : ℂ} (hw : ‖w‖ < 1) (hwr : 0 < w.re)
    {a b : ℝ} (ha : 1/2 ≤ a) (hab : a ≤ b) (hbw : b < ‖w‖)
    (ht : |(F w).im| ≤ T b) :
    1/A w ≤ Real.pi/2 + Real.pi^3 / Real.sqrt (tailSlope a) *
      Real.sqrt ((1-‖w‖)/(‖w‖-b)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : a < 1 := hab.trans_lt (hbw.trans hw)
  have hL := tailSlope_pos ha0 ha1
  have hgap := T_tail_gap ha0 hab hbw.le hw
  have hnum : 0 ≤ 1-‖w‖ := by linarith
  have hden : 0 < tailSlope a * (‖w‖-b) := mul_pos hL (sub_pos.mpr hbw)
  have hgap' : tailSlope a * (‖w‖-b) ≤ T ‖w‖ - |(F w).im| := by
    dsimp [tailSlope] at *
    linarith
  apply (reciprocal_A_slice hw hwr (ha.trans (hab.trans hbw.le))).trans
  apply add_le_add_right
  calc
    Real.pi^3 * Real.sqrt ((1-‖w‖)/(T ‖w‖ - |(F w).im|))
        ≤ Real.pi^3 * Real.sqrt ((1-‖w‖)/(tailSlope a*(‖w‖-b))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left hnum hden hgap'
    _ = Real.pi^3 / Real.sqrt (tailSlope a) * Real.sqrt ((1-‖w‖)/(‖w‖-b)) := by
      rw [show (1-‖w‖)/(tailSlope a*(‖w‖-b)) = ((1-‖w‖)/(‖w‖-b))/(tailSlope a) by rw [div_div, mul_comm (‖w‖-b)],
        Real.sqrt_div (div_nonneg hnum (sub_nonneg.mpr hbw.le))]
      ring

theorem integrable_radialError {b : ℝ} (hb : b ≤ 1) (k : ℕ) :
    IntervalIntegrable (fun r : ℝ => r^(2*k-1)*Real.sqrt ((1-r)/(r-b))) volume b 1 := by
  have h := (SymmetricPolar.intervalIntegrable_endpointKernel (sub_nonneg.mpr hb)).comp_sub_left 1
  have he : (fun r : ℝ => SymmetricPolar.endpointKernel (1-b) (1-r)) =
      fun r : ℝ => Real.sqrt ((1-r)/(r-b)) := by
    funext r
    dsimp [SymmetricPolar.endpointKernel]
    congr 2
    ring
  rw [he] at h
  have hh : IntervalIntegrable (fun r : ℝ => Real.sqrt ((1-r)/(r-b))) volume b 1 := by
    convert h.symm using 1 <;> ring
  exact hh.continuousOn_mul (by fun_prop)

theorem integral_radialLeading {k : ℕ} (hk : 1 ≤ k) (b R : ℝ) :
    (k : ℝ) * ∫ r in b..R, r^(2*k-1)*(Real.pi/2) =
      Real.pi/4 * (R^(2*k)-b^(2*k)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => r^(2*k)/(2*k)) (r^(2*k-1)) r := by
    convert ((hasDerivAt_id r).pow (2*k)).div_const ((2:ℝ)*k) using 1 <;>
      first | rfl | (simp only [Nat.cast_mul, Nat.cast_ofNat, id_eq, mul_one]; field_simp [hk0])
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r ∈ uIcc b R) => hd r)
    (show IntervalIntegrable (fun r : ℝ => r^(2*k-1)) volume b R from (by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, hi]
  field_simp
  ring

theorem outer_integral_bound {k : ℕ} (hk : 1 ≤ k) {t v u a : ℝ}
    (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (hu : 0 ≤ u) (huv : u ≤ v)
    (ha : 1/2 ≤ a) (hau : a ≤ rho t u) :
    (k : ℝ)*∫ h in u..v, density k ((h : ℂ)+(t : ℂ)*I) ≤
      Real.pi/4*((rho t v)^(2*k)-(rho t u)^(2*k)) +
        Real.pi^3/Real.sqrt (tailSlope a)*(1+Real.pi/Real.exp 1) := by
  have hv : 0 ≤ v := hu.trans huv
  have huI : u ∈ Icc 0 v := ⟨hu, huv⟩
  have huD := horizontal_segment_mem hz hv huI
  have hb0 : 0 ≤ rho t u := norm_nonneg _
  have hb1 : rho t u < 1 := norm_g_lt huD
  have hR1 : rho t v < 1 := norm_g_lt hz
  have hrho := horizontal_radius_strictMono hz hv
  have hbR : rho t u ≤ rho t v := hrho.monotoneOn huI (right_mem_Icc.mpr hv) huv
  have ha1 : a < 1 := hau.trans_lt hb1
  have hL : 0 < tailSlope a := tailSlope_pos (by linarith) ha1
  have hc : 0 ≤ Real.pi^3/Real.sqrt (tailSlope a) := by positivity
  let P : ℝ → ℝ := fun r => r^(2*k-1)*(Real.pi/2) +
    (Real.pi^3/Real.sqrt (tailSlope a))*(r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u)))
  have hradE := integrable_radialError hb1.le k
  have hradE' : IntervalIntegrable
      (fun r : ℝ => r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))) volume (rho t u) (rho t v) :=
    hradE.mono_set (uIcc_subset_uIcc (left_mem_uIcc) (by
      rw [uIcc_of_le hb1.le]; exact ⟨hbR, hR1.le⟩))
  have hP : IntervalIntegrable P volume (rho t u) (rho t v) :=
    ((by fun_prop : Continuous (fun r : ℝ => r^(2*k-1)*(Real.pi/2))).intervalIntegrable _ _).add
      (hradE'.const_mul _)
  have hcont : ContinuousOn (rho t) (uIcc u v) := by
    rw [uIcc_of_le huv]
    exact (continuousOn_rho hz hv).mono (fun _ hx => ⟨hu.trans hx.1, hx.2⟩)
  have hder : ∀ h ∈ Ioo (min u v) (max u v), HasDerivAt (rho t) (rhoD t h) h := by
    rw [min_eq_left huv, max_eq_right huv]
    intro h hh
    exact hasDerivAt_rho (horizontal_segment_mem hz hv ⟨hu.trans hh.1.le, hh.2.le⟩)
      (hu.trans_lt hh.1)
  have hpos : ∀ h ∈ Ioo (min u v) (max u v), 0 ≤ rhoD t h := by
    rw [min_eq_left huv, max_eq_right huv]
    intro h hh
    exact (rhoD_pos (horizontal_segment_mem hz hv ⟨hu.trans hh.1.le, hh.2.le⟩)
      (hu.trans_lt hh.1)).le
  have hPc : IntervalIntegrable (fun h => P (rho t h)*rhoD t h) volume u v :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hcont hder hpos).mpr hP
  have hdens : IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_density k).comp (by fun_prop)
    intro h hh
    rw [uIcc_of_le huv] at hh
    exact horizontal_segment_mem hz hv ⟨hu.trans hh.1, hh.2⟩
  have hcmp : ∫ h in u..v, density k ((h : ℂ)+(t : ℂ)*I) ≤ ∫ r in rho t u..rho t v, P r := by
    rw [← intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hcont hder hpos (g := P)]
    apply intervalIntegral.integral_mono_ae_restrict huv hdens hPc
    change ∀ᵐ (h : ℝ) ∂volume.restrict (Icc u v), density k ((h : ℂ)+(t : ℂ)*I) ≤ P (rho t h)*rhoD t h
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [volume.ae_ne u] with h hne hh
    have hhu : u < h := lt_of_le_of_ne hh.1 (Ne.symm hne)
    have hh0 : 0 < h := hu.trans_lt hhu
    have hhz := horizontal_segment_mem hz hv ⟨hh0.le, hh.2⟩
    have hbr : rho t u < rho t h := hrho huI ⟨hh0.le, hh.2⟩ hhu
    have hA := reciprocal_A_tail (norm_g_lt hhz) (re_g_pos hhz (by simpa using hh0))
      ha hau hbr (by simpa only [F_g hhz, add_im, ofReal_im, mul_im, ofReal_re, I_im,
        I_re, mul_one, mul_zero, add_zero, zero_add] using T_rho_ge_abs hz hv huI)
    rw [density_radial hk hhz hh0]
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hA (pow_nonneg (norm_nonneg (g ((h : ℂ)+(t : ℂ)*I))) (2*k-1))) (rhoD_pos hhz hh0).le
    convert hmul using 1 <;>
      first | rfl | (dsimp only [P, rho]; ring)
  have hlead := integral_radialLeading hk (rho t u) (rho t v)
  have herr : (k : ℝ)*∫ r in rho t u..rho t v,
      r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u)) ≤ 1+Real.pi/Real.exp 1 := by
    apply le_trans _ (SymmetricPolar.movingEndpointIntegral_le hk hb0 hb1)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    apply intervalIntegral.integral_mono_interval le_rfl hbR hR1.le _ hradE
    change ∀ᵐ (r : ℝ) ∂volume.restrict (Ioc (rho t u) 1), 0 ≤ r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun r hr => mul_nonneg
      (pow_nonneg (hb0.trans hr.1.le) _) (Real.sqrt_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg k)
  dsimp [P] at hh
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun r : ℝ => r^(2*k-1)*(Real.pi/2))).intervalIntegrable _ _)
    (hradE'.const_mul _), intervalIntegral.integral_const_mul, mul_add, hlead] at hh
  apply hh.trans
  apply add_le_add_right
  calc
    _ = (Real.pi^3/Real.sqrt (tailSlope a))*((k : ℝ)*∫ r in rho t u..rho t v,
        r^(2*k-1)*Real.sqrt ((1-r)/(r-rho t u))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left herr hc

end
end PlanarLens

end LowerBoundInline

end OAI
