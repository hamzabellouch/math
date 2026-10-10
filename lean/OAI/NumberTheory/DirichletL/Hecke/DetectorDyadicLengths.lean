import OAI.NumberTheory.DirichletL.Hecke.DetectorSaturation

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDyadicGeometry

lemma log_scale_bounds (U x : ℝ) (hU : 8≤U) (hx : 1≤x) (hxU : x≤8*U^21) :
    0≤Real.logb U x ∧ Real.logb U x≤22 ∧ U^(Real.logb U x)=x := by
  have hUp : 0<U := by linarith
  have hU1 : 1<U := by linarith
  have hxp : 0<x := by linarith
  have he := Real.rpow_logb hUp hU1.ne' hxp
  refine ⟨Real.logb_nonneg hU1 hx,?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hU1).mp
  rw [he,show (22 : ℝ)=((22 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  calc
    x ≤ 8*U^21 := hxU
    _ ≤ U*U^21 := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = U^22 := by ring

lemma dyadic_scale_bounds (U : ℝ) (hU : 8≤U) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    0≤Real.logb U ((2 : ℝ)^j) ∧ Real.logb U ((2 : ℝ)^j)≤22 ∧
      0≤Real.logb U ((2 : ℝ)^k) ∧ Real.logb U ((2 : ℝ)^k)≤22 ∧
      U^(Real.logb U ((2 : ℝ)^j))=(2 : ℝ)^j ∧
      U^(Real.logb U ((2 : ℝ)^k))=(2 : ℝ)^k := by
  obtain ⟨hj,hk⟩ := HeckeDetectorDyadicBridge.scales_le_eight_terminal (U^21) j k hprod
  obtain ⟨hr,hr',he⟩ := log_scale_bounds U ((2 : ℝ)^j) hU (one_le_pow₀ (by norm_num)) hj
  obtain ⟨hm,hm',he'⟩ := log_scale_bounds U ((2 : ℝ)^k) hU (one_le_pow₀ (by norm_num)) hk
  exact ⟨hr,hr',hm,hm',he,he'⟩

lemma support_exponents (U t r m ε : ℝ) (hU : 1<U) (hcost : 8≤U^ε)
    (hleft : U^r<4*U^t) (hright : U^t/8<U^r*U^m) :
    r≤t+ε ∧ t-ε≤r+m := by
  have hUp : 0<U := by linarith
  constructor
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^r ≤ 4*U^t := hleft.le
      _ ≤ U^ε*U^t := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hUp.le _)
      _ = U^(t+ε) := by rw [←Real.rpow_add hUp]; congr 1; ring
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^(t-ε) = U^t/U^ε := Real.rpow_sub hUp _ _
      _ ≤ U^t/8 := div_le_div_of_nonneg_left (Real.rpow_nonneg hUp.le _) (by norm_num) hcost
      _ ≤ U^r*U^m := hright.le
      _ = U^(r+m) := (Real.rpow_add hUp _ _).symm

lemma truncation_scale (U t : ℝ) (hU : 2≤U) (ht : 1≤t) (ht' : t≤3/2) :
    2≤U^t ∧ U^t≤U^(3/2 : ℝ) := by
  have hU1 : 1≤U := by linarith
  constructor
  · apply hU.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1 ht
  · exact Real.rpow_le_rpow_of_exponent_le hU1 ht'

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
