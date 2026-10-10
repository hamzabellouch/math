import Mathlib
import OAI.Probability.SLE.OccupationBound
import OAI.Probability.SLE.StripKernels

namespace OAI

/-! Sausage Point Bound for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def spatialSmallnessConstant : ℝ := 128 * Real.pi * Real.exp 1 + 1
noncomputable def spatialOnePointConstant (κ : ℝ) : ℝ :=
  uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ

lemma spatialSmallnessConstant_gt_one : 1 < spatialSmallnessConstant := by
  dsimp [spatialSmallnessConstant]
  have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 128) Real.pi_pos) (Real.exp_pos 1)
  linarith

lemma spatial_smallness (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hy : spatialSmallnessConstant * r < z.im) :
    0 < z.im ∧ r ≤ z.im ∧ 1 ≤ Real.log ((2 * z.im) / ((128 * Real.pi) * r)) := by
  have hA : 1 ≤ spatialSmallnessConstant := spatialSmallnessConstant_gt_one.le
  have hry : r < z.im := (le_mul_of_one_le_left hr.le hA).trans_lt hy
  refine ⟨hr.trans hry, hry.le, ?_⟩
  have hC : 0 < (128 * Real.pi) * r := mul_pos (mul_pos (by norm_num) Real.pi_pos) hr
  have hquot : 0 < (2 * z.im) / ((128 * Real.pi) * r) :=
    div_pos (mul_pos (by norm_num) (hr.trans hry)) hC
  apply (Real.le_log_iff_exp_le hquot).mpr
  apply (le_div_iff₀ hC).mpr
  dsimp [spatialSmallnessConstant] at hy
  nlinarith [Real.exp_pos 1]

lemma initialGreen_le_height (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    initialGreen κ z ≤ (2 : ℝ) ^ (-codimension κ) * z.im ^ (-codimension κ) := by
  have hs : 0 ≤ Real.sin (Complex.arg z) := by
    rw [Complex.sin_arg]; exact div_nonneg hz.le (norm_nonneg _)
  calc
    initialGreen κ z ≤ (2 * z.im) ^ (-codimension κ) * 1 :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_one hs (Real.sin_le_one _) (greenExponent_pos κ hκ hκ8).le)
        (Real.rpow_nonneg (mul_nonneg (by norm_num) hz.le) _)
    _ = (2 : ℝ) ^ (-codimension κ) * z.im ^ (-codimension κ) := by
      rw [mul_one, Real.mul_rpow (by norm_num) hz.le]

noncomputable def sausagePointConstant (κ : ℝ) : ℝ :=
  max (spatialOnePointConstant κ * (2 : ℝ) ^ (-codimension κ))
    (spatialSmallnessConstant ^ codimension κ)

lemma spatialOnePointConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < spatialOnePointConstant κ :=
  mul_pos (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num))
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _)

lemma sausagePointConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < sausagePointConstant κ :=
  (mul_pos (spatialOnePointConstant_pos κ hκ hκ8) (Real.rpow_pos_of_pos (by norm_num) _)).trans_le
    (le_max_left _ _)

lemma negative_power_scale (x r A p : ℝ) (hx : 0 < x) (hr : 0 < r)
    (hA : 0 < A) (hp : 0 ≤ p) (hxr : x ≤ A * r) :
    r ^ (-p) ≤ A ^ p * x ^ (-p) := by
  have hh := Real.rpow_le_rpow hx.le hxr hp
  rw [Real.mul_rpow hA.le hr.le] at hh
  rw [Real.rpow_neg hr.le, Real.rpow_neg hx.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hx p)).mpr
  exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hr p)).mpr (by simpa [mul_comm] using hh)

 

theorem normalized_visit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z.im ≠ 0) (r : ℝ) (hr : 0 < r) :
    r ^ (-codimension κ) * (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      sausagePointConstant κ * |z.im| ^ (-codimension κ) := by
  have hp := codimension_pos κ hκ8
  have hA : 0 < spatialSmallnessConstant := zero_lt_one.trans spatialSmallnessConstant_gt_one
  have hscale (hy : |z.im| ≤ spatialSmallnessConstant * r) :
      r ^ (-codimension κ) * (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
        sausagePointConstant κ * |z.im| ^ (-codimension κ) := by
    calc
      _ ≤ r ^ (-codimension κ) * 1 := mul_le_mul_of_nonneg_left measureReal_le_one
        (Real.rpow_nonneg hr.le _)
      _ ≤ spatialSmallnessConstant ^ codimension κ * |z.im| ^ (-codimension κ) := by
        rw [mul_one]
        exact negative_power_scale _ _ _ _ (abs_pos.mpr hz) hr hA hp.le hy
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (abs_nonneg _) _)
  by_cases hsmall : spatialSmallnessConstant * r < z.im
  · obtain ⟨hy, hry, hlog⟩ := spatial_smallness z r hr hsmall
    have hh := euclidean_approach hB κ hκ hκ8 γ G F hw z hy r hr hry hlog
    have hS := (spatialOnePointConstant_pos κ hκ hκ8).le
    change (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      spatialOnePointConstant κ * initialGreen κ z * r ^ codimension κ at hh
    have hcancel : r ^ (-codimension κ) * r ^ codimension κ = 1 := by
      rw [← Real.rpow_add hr]; simp
    calc
      _ ≤ r ^ (-codimension κ) * (spatialOnePointConstant κ * initialGreen κ z * r ^ codimension κ) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr.le _)
      _ = spatialOnePointConstant κ * initialGreen κ z := by
        calc
          _ = (spatialOnePointConstant κ * initialGreen κ z) *
              (r ^ (-codimension κ) * r ^ codimension κ) := by ring
          _ = _ := by rw [hcancel, mul_one]
      _ ≤ spatialOnePointConstant κ * ((2 : ℝ) ^ (-codimension κ) * z.im ^ (-codimension κ)) :=
        mul_le_mul_of_nonneg_left (initialGreen_le_height κ hκ hκ8 z hy) hS
      _ ≤ _ := by
        rw [abs_of_pos hy, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)
  · by_cases hy : 0 ≤ z.im
    · apply hscale
      rw [abs_of_nonneg hy]
      exact le_of_not_gt hsmall
    · by_cases hzr : -r < z.im
      · apply hscale
        rw [abs_of_neg (lt_of_not_ge hy)]
        exact (by linarith : -z.im ≤ r).trans (le_mul_of_one_le_left hr.le spatialSmallnessConstant_gt_one.le)
      · have hzero : P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r} = 0 := by
          have hn : ∀ᵐ ω ∂P, ¬ (∃ t : ℝ≥0, dist (γ ω t) z < r) := by
            filter_upwards [hw] with ω hω
            rintro ⟨t, ht⟩
            have hi := Complex.im_le_norm (γ ω t - z)
            rw [Complex.sub_im, ← dist_eq_norm] at hi
            have hnon := hω.2.2.1 t
            linarith [le_of_not_gt hzr]
          simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hn
        rw [hzero, ENNReal.toReal_zero, mul_zero]
        exact mul_nonneg (sausagePointConstant_pos κ hκ hκ8).le (Real.rpow_nonneg (abs_nonneg _) _)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsOrdinaryChordalSLE.exists_charts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P) :
    ∃ (B : ℝ≥0 → Ω → ℝ) (G F : Ω → ℝ≥0 → ℂ → ℂ),
      IsBrownianReal B P ∧ ∀ᵐ ω ∂P, IsCapacityTwoWitness
        (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω) := by
  classical
  obtain ⟨B,hB,htrace⟩ := hSLE.2
  have hchoice (ω : Ω) : ∃ G F : ℝ≥0 → ℂ → ℂ,
      IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω) →
        IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) G F := by
    by_cases h : IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω)
    · obtain ⟨G,F,hw⟩ := h
      exact ⟨G,F,fun _ => hw⟩
    · exact ⟨fun _ _ => 0,fun _ _ => 0,fun hh => False.elim (h hh)⟩
  choose G F hw using hchoice
  exact ⟨B,G,F,hB,htrace.mono fun ω hω => hw ω hω⟩

 

lemma sle_high_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : Real.sqrt r ≤ z.im) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      sausagePointConstant κ * r^(codimension κ/2) := by
  obtain ⟨B,G,F,hB,hw⟩ := hSLE.exists_charts
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hp := codimension_pos κ hκ8
  have hs := Real.sqrt_pos.mpr hr
  have hz : 0 < z.im := hs.trans_le hy
  have hb := normalized_visit_bound hB κ hκ hκ8 γ G F hw z hz.ne' r hr
  have hb' := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le (codimension κ))
  rw [← mul_assoc,← Real.rpow_add hr,add_neg_cancel,Real.rpow_zero,one_mul,abs_of_pos hz] at hb'
  have hpow : z.im^(-codimension κ) ≤ (Real.sqrt r)^(-codimension κ) :=
    Real.rpow_le_rpow_of_nonpos hs hy (neg_nonpos.mpr hp.le)
  have hid : r^codimension κ * (Real.sqrt r)^(-codimension κ) = r^(codimension κ/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hr.le,← Real.rpow_add hr]
    congr 1
    ring
  calc
    _ ≤ r^codimension κ * (sausagePointConstant κ * (Real.sqrt r)^(-codimension κ)) :=
      hb'.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (sausagePointConstant_pos κ hκ hκ8).le)
        (Real.rpow_nonneg hr.le _))
    _ = _ := by rw [← mul_assoc,mul_comm (r^codimension κ),mul_assoc,hid]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def boundaryApproachPower (κ : ℝ) : ℝ := 3*(8-κ)/(4*κ)
noncomputable def annularApproachPower (κ : ℝ) : ℝ :=
  min (boundaryApproachPower κ/2) (codimension κ/2)
noncomputable def annularApproachConstant (κ : ℝ) : ℝ :=
  (8/((8-κ)/32))^boundaryApproachPower κ + sausagePointConstant κ

lemma annularApproachPower_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < annularApproachPower κ := by
  have hp := codimension_pos κ hκ8
  unfold annularApproachPower boundaryApproachPower
  exact lt_min (by positivity) (by positivity)

lemma annularApproachConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < annularApproachConstant κ := by
  have hh := sausagePointConstant_pos κ hκ hκ8
  unfold annularApproachConstant
  exact add_pos (Real.rpow_pos_of_pos (by positivity) _) hh

 

lemma sle_low_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (hz : 0 ≤ z.im) (hn : 1/2 ≤ ‖z‖)
    (r : ℝ) (hr : 0 < r) (hr16 : r < 1/16) (hy : z.im ≤ Real.sqrt r) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      (8/((8-κ)/32))^boundaryApproachPower κ * r^(boundaryApproachPower κ/2) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < (8-κ)/32 := by positivity
  have hβ : 0 < boundaryApproachPower κ := by unfold boundaryApproachPower; positivity
  have hs := Real.sqrt_pos.mpr hr
  have hsq := Real.sq_sqrt hr.le
  have hs4 : Real.sqrt r < 1/4 := by nlinarith [Real.sqrt_nonneg r]
  have hrs : r ≤ Real.sqrt r := by nlinarith [Real.sqrt_nonneg r]
  have hx : 1/4 ≤ |z.re| := by
    have hn' := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz] at hn'
    linarith
  have hx0 : z.re ≠ 0 := by
    intro he
    rw [he,abs_zero] at hx
    norm_num at hx
  have hd : dist z (z.re:ℂ) = z.im := by
    rw [dist_eq_norm]
    have he : z-(z.re:ℂ) = (z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
  have hb := sle_real_center_approach κ hκ hκ8 γ hSLE z.re (2*Real.sqrt r) hx0 (by positivity)
  have he : P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r} ≤
      P {ω | ∃ t : ℝ≥0, dist (γ ω t) (z.re:ℂ) < 2*Real.sqrt r} := by
    apply measure_mono
    rintro ω ⟨t,ht⟩
    refine ⟨t,?_⟩
    have hh := dist_triangle (γ ω t) z (z.re:ℂ)
    rw [hd] at hh
    linarith
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he.trans hb)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)] at hb'
  have hq : (2*Real.sqrt r)/(((8-κ)/32)*|z.re|) ≤ (8/((8-κ)/32))*Real.sqrt r := by
    calc
      _ ≤ (2*Real.sqrt r)/(((8-κ)/32)*(1/4)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left hx hδ.le)
      _ = _ := by field_simp; ring
  have hsβ : (Real.sqrt r)^boundaryApproachPower κ = r^(boundaryApproachPower κ/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hr.le]
    congr 1
    ring
  calc
    _ ≤ ((8/((8-κ)/32))*Real.sqrt r)^boundaryApproachPower κ :=
      hb'.trans (Real.rpow_le_rpow (by positivity) hq hβ.le)
    _ = _ := by rw [Real.mul_rpow (by positivity) hs.le,hsβ]

 

theorem sle_annular_small_target
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (hz : 0 ≤ z.im) (hn : 1/2 ≤ ‖z‖) (_hn2 : ‖z‖ ≤ 2)
    (r : ℝ) (hr : 0 < r) (hr16 : r < 1/16) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r} ≤
      ENNReal.ofReal (annularApproachConstant κ * r^annularApproachPower κ) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hC := annularApproachConstant_pos κ hκ hκ8
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  have hr1 : r ≤ 1 := by linarith
  by_cases hy : z.im ≤ Real.sqrt r
  · have hb := sle_low_center_approach κ hκ hκ8 γ hSLE z hz hn r hr hr16 hy
    have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_left
      (boundaryApproachPower κ/2) (codimension κ/2))
    have hcoeff : (8/((8-κ)/32))^boundaryApproachPower κ ≤ annularApproachConstant κ := by
      exact le_add_of_nonneg_right (sausagePointConstant_pos κ hκ hκ8).le
    exact hb.trans (mul_le_mul hcoeff hp (Real.rpow_nonneg hr.le _) hC.le)
  · have hb := sle_high_center_approach κ hκ hκ8 γ hSLE z r hr (le_of_not_ge hy)
    have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right
      (boundaryApproachPower κ/2) (codimension κ/2))
    have hcoeff : sausagePointConstant κ ≤ annularApproachConstant κ := by
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    exact hb.trans (mul_le_mul hcoeff hp (Real.rpow_nonneg hr.le _) hC.le)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma sle_high_center_approach_scaled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hy : R*Real.sqrt r ≤ z.im) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r}).toReal ≤
      sausagePointConstant κ * r^(codimension κ/2) := by
  obtain ⟨B,G,F,hB,hw⟩ := hSLE.exists_charts
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hp := codimension_pos κ hκ8
  have hs := Real.sqrt_pos.mpr hr
  have hz : 0 < z.im := (mul_pos hR hs).trans_le hy
  have hb := normalized_visit_bound hB κ hκ hκ8 γ G F hw z hz.ne' (R*r) (mul_pos hR hr)
  have hb' := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (mul_nonneg hR.le hr.le) (codimension κ))
  rw [← mul_assoc,← Real.rpow_add (mul_pos hR hr),add_neg_cancel,Real.rpow_zero,one_mul,abs_of_pos hz] at hb'
  have hpow : z.im^(-codimension κ) ≤ (R*Real.sqrt r)^(-codimension κ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hR hs) hy (neg_nonpos.mpr hp.le)
  have hid : (R*r)^codimension κ * (R*Real.sqrt r)^(-codimension κ) = r^(codimension κ/2) := by
    rw [Real.mul_rpow hR.le hr.le,Real.mul_rpow hR.le hs.le]
    calc
      _ = (R^codimension κ*R^(-codimension κ)) *
          (r^codimension κ*(Real.sqrt r)^(-codimension κ)) := by ring
      _ = r^(codimension κ/2) := by
        rw [← Real.rpow_add hR,add_neg_cancel,Real.rpow_zero,one_mul,
          Real.sqrt_eq_rpow,← Real.rpow_mul hr.le,← Real.rpow_add hr]
        congr 1
        ring
  calc
    _ ≤ (R*r)^codimension κ * (sausagePointConstant κ * (R*Real.sqrt r)^(-codimension κ)) :=
      hb'.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (sausagePointConstant_pos κ hκ hκ8).le)
        (Real.rpow_nonneg (mul_nonneg hR.le hr.le) _))
    _ = _ := by rw [← mul_assoc,mul_comm ((R*r)^codimension κ),mul_assoc,hid]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma sle_low_center_approach_scaled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hz : 0 ≤ z.im) (hn : R/2 ≤ ‖z‖)
    (r : ℝ) (hr : 0 < r) (hr16 : r < 1/16) (hy : z.im ≤ R*Real.sqrt r) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r}).toReal ≤
      (8/((8-κ)/32))^boundaryApproachPower κ * r^(boundaryApproachPower κ/2) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < (8-κ)/32 := by positivity
  have hβ : 0 < boundaryApproachPower κ := by unfold boundaryApproachPower; positivity
  have hs := Real.sqrt_pos.mpr hr
  have hsq := Real.sq_sqrt hr.le
  have hs4 : Real.sqrt r < 1/4 := by nlinarith [Real.sqrt_nonneg r]
  have hrs : r ≤ Real.sqrt r := by nlinarith [Real.sqrt_nonneg r]
  have hx : R/4 ≤ |z.re| := by
    have hn' := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz] at hn'
    nlinarith [mul_pos hR (sub_pos.mpr hs4)]
  have hx0 : z.re ≠ 0 := by
    intro he
    rw [he,abs_zero] at hx
    linarith
  have hd : dist z (z.re:ℂ) = z.im := by
    rw [dist_eq_norm]
    have he : z-(z.re:ℂ) = (z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
  have hb := sle_real_center_approach κ hκ hκ8 γ hSLE z.re (2*R*Real.sqrt r) hx0 (by positivity)
  have he : P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r} ≤
      P {ω | ∃ t : ℝ≥0, dist (γ ω t) (z.re:ℂ) < 2*R*Real.sqrt r} := by
    apply measure_mono
    rintro ω ⟨t,ht⟩
    refine ⟨t,?_⟩
    have hh := dist_triangle (γ ω t) z (z.re:ℂ)
    rw [hd] at hh
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hrs)]
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he.trans hb)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)] at hb'
  have hq : (2*R*Real.sqrt r)/(((8-κ)/32)*|z.re|) ≤ (8/((8-κ)/32))*Real.sqrt r := by
    calc
      _ ≤ (2*R*Real.sqrt r)/(((8-κ)/32)*(R/4)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left (show R/4 ≤ |z.re| from hx) hδ.le)
      _ = _ := by field_simp; ring
  have hsβ : (Real.sqrt r)^boundaryApproachPower κ = r^(boundaryApproachPower κ/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hr.le]
    congr 1
    ring
  calc
    _ ≤ ((8/((8-κ)/32))*Real.sqrt r)^boundaryApproachPower κ :=
      hb'.trans (Real.rpow_le_rpow (by positivity) hq hβ.le)
    _ = _ := by rw [Real.mul_rpow (by positivity) hs.le,hsβ]

 

theorem sle_annular_small_target_scaled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hz : 0 ≤ z.im)
    (hn : R/2 ≤ ‖z‖) (_hn2 : ‖z‖ ≤ 2*R)
    (r : ℝ) (hr : 0 < r) (hr16 : r < 1/16) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r} ≤
      ENNReal.ofReal (annularApproachConstant κ * r^annularApproachPower κ) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hC := annularApproachConstant_pos κ hκ hκ8
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  have hr1 : r ≤ 1 := by linarith
  by_cases hy : z.im ≤ R*Real.sqrt r
  · have hb := sle_low_center_approach_scaled κ hκ hκ8 γ hSLE z R hR hz hn r hr hr16 hy
    have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_left
      (boundaryApproachPower κ/2) (codimension κ/2))
    have hcoeff : (8/((8-κ)/32))^boundaryApproachPower κ ≤ annularApproachConstant κ := by
      exact le_add_of_nonneg_right (sausagePointConstant_pos κ hκ hκ8).le
    exact hb.trans (mul_le_mul hcoeff hp (Real.rpow_nonneg hr.le _) hC.le)
  · have hb := sle_high_center_approach_scaled κ hκ hκ8 γ hSLE z R r hR hr (le_of_not_ge hy)
    have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right
      (boundaryApproachPower κ/2) (codimension κ/2))
    have hcoeff : sausagePointConstant κ ≤ annularApproachConstant κ := by
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    exact hb.trans (mul_le_mul hcoeff hp (Real.rpow_nonneg hr.le _) hC.le)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
lemma stripRectangle_norm_sub_le (a b l : ℝ) (w : ℂ)
    (hw : w ∈ stripRectangle a b l) :
    ‖w-((a:ℂ)+(b:ℂ)*Complex.I)‖ ≤ (1+Real.pi)*l := by
  rcases hw with ⟨hwr,hwr',hwi,hwi'⟩
  have hr : 0 ≤ (w-((a:ℂ)+(b:ℂ)*Complex.I)).re := by simpa using sub_nonneg.mpr hwr
  have hi : 0 ≤ (w-((a:ℂ)+(b:ℂ)*Complex.I)).im := by simpa using sub_nonneg.mpr hwi
  have hh := Complex.norm_le_abs_re_add_abs_im (w-((a:ℂ)+(b:ℂ)*Complex.I))
  rw [abs_of_nonneg hr,abs_of_nonneg hi] at hh
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im, mul_zero, mul_one,
    sub_self,add_zero,Complex.sub_im,Complex.add_im,Complex.mul_im,
    zero_add] at hh
  nlinarith

lemma stripRectangle_exp_distance (a b l : ℝ) (hl : 0 < l)
    (hs : (1+Real.pi)*l ≤ 1) (w : ℂ) (hw : w ∈ stripRectangle a b l) :
    dist (Complex.exp w) (Complex.exp ((a:ℂ)+(b:ℂ)*Complex.I)) <
      Real.exp a * (3*(1+Real.pi)*l) := by
  let c : ℂ := (a:ℂ)+(b:ℂ)*Complex.I
  have hn := stripRectangle_norm_sub_le a b l w hw
  have he : Complex.exp w - Complex.exp c =
      Complex.exp c * (Complex.exp (w-c)-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    ring
  have hc : ‖Complex.exp c‖ = Real.exp a := by simp [c,Complex.norm_exp]
  rw [dist_eq_norm,show ((a:ℂ)+(b:ℂ)*Complex.I) = c from rfl,he,norm_mul,hc]
  calc
    _ ≤ Real.exp a * (2*‖w-c‖) := mul_le_mul_of_nonneg_left
      (Complex.norm_exp_sub_one_le (hn.trans hs)) (Real.exp_pos a).le
    _ ≤ Real.exp a * (2*((1+Real.pi)*l)) := by gcongr
    _ < _ := by
      apply mul_lt_mul_of_pos_left _ (Real.exp_pos a)
      have hh : 0 < (1+Real.pi)*l := mul_pos (by linarith [Real.pi_pos]) hl
      nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def stripHittingConstant (κ : ℝ) : ℝ :=
  (annularApproachConstant κ+1) * (64*(1+Real.pi))^annularApproachPower κ

lemma stripHittingConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < stripHittingConstant κ := by
  have hC := annularApproachConstant_pos κ hκ hκ8
  have hp := Real.pi_pos
  unfold stripHittingConstant
  positivity

 

theorem sle_exp_strip_rectangle_hit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (a b l : ℝ) (hb0 : 0 ≤ b) (hbpi : b ≤ Real.pi) (hl : 0 < l) :
    P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' stripRectangle a b l} ≤
      ENNReal.ofReal (stripHittingConstant κ * l^annularApproachPower κ) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hC := annularApproachConstant_pos κ hκ hκ8
  have hα := annularApproachPower_pos κ hκ hκ8
  have hD : 0 < 1+Real.pi := by have hp := Real.pi_pos; linarith
  have h64 : 0 < 64*(1+Real.pi) := by positivity
  by_cases hs : l < 1/(64*(1+Real.pi))
  · have hs' : 64*(1+Real.pi)*l < 1 := by
      have hh := (lt_div_iff₀ h64).mp hs
      nlinarith
    let c : ℂ := Complex.exp ((a:ℂ)+(b:ℂ)*Complex.I)
    have hc : ‖c‖ = Real.exp a := by simp [c,Complex.norm_exp]
    have hci : 0 ≤ c.im := by
      simp only [c,Complex.exp_im,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        sub_self,add_zero,Complex.add_im,Complex.mul_im,zero_add]
      exact mul_nonneg (Real.exp_pos a).le (Real.sin_nonneg_of_mem_Icc ⟨hb0,hbpi⟩)
    have hb := sle_annular_small_target_scaled κ hκ hκ8 γ hSLE c (Real.exp a)
      (Real.exp_pos a) hci (by rw [hc]; linarith [Real.exp_pos a])
      (by rw [hc]; linarith [Real.exp_pos a]) (3*(1+Real.pi)*l)
      (by positivity) (by nlinarith)
    have hsub : P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' stripRectangle a b l} ≤
        P {ω | ∃ t : ℝ≥0, dist (γ ω t) c < Real.exp a * (3*(1+Real.pi)*l)} := by
      apply measure_mono
      rintro ω ⟨t,w,hw,he⟩
      refine ⟨t,?_⟩
      rw [← he]
      exact stripRectangle_exp_distance a b l hl (by nlinarith) w hw
    refine (hsub.trans hb).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.mul_rpow (by positivity : 0 ≤ 3*(1+Real.pi)) hl.le]
    unfold stripHittingConstant
    have hp : (3*(1+Real.pi))^annularApproachPower κ ≤
        (64*(1+Real.pi))^annularApproachPower κ := by
      apply Real.rpow_le_rpow (by positivity) (by nlinarith) hα.le
    have hcoeff : annularApproachConstant κ * (3*(1+Real.pi))^annularApproachPower κ ≤
        (annularApproachConstant κ+1) * (64*(1+Real.pi))^annularApproachPower κ :=
      mul_le_mul (by linarith) hp (Real.rpow_nonneg (by positivity) _) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hl.le (annularApproachPower κ))]
  · have hs' : 1 ≤ 64*(1+Real.pi)*l := by
      have hh := (div_le_iff₀ h64).mp (le_of_not_gt hs)
      nlinarith
    have hp : 1 ≤ (64*(1+Real.pi)*l)^annularApproachPower κ :=
      Real.one_le_rpow hs' hα.le
    rw [Real.mul_rpow h64.le hl.le] at hp
    have hc : 1 ≤ stripHittingConstant κ * l^annularApproachPower κ := by
      unfold stripHittingConstant
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hp)]
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hc

end SLEExactGauge
end

 
end

end OAI
