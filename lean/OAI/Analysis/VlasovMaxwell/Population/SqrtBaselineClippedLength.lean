import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.NormalisedPartialCutoff

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma sqrt_baseline_clipped_length {I lam : ℝ} (hI : 0 < I) (hlam : 0 < lam) :
    Real.sqrt (1+I/min I (lam/2))  ≤  2*(1+Real.sqrt (I/lam)) := by
  have hlen : 0 < min I (lam/2) := lt_min hI (by positivity)
  have hq : 0 ≤ I/lam := by positivity
  have hR : 0 ≤ Real.sqrt (I/lam) := Real.sqrt_nonneg _
  have hRsq := Real.sq_sqrt hq
  have hdiv : I/min I (lam/2)  ≤  1+2*(I/lam) := by
    rcases le_total I (lam/2) with h|h
    · rw [min_eq_left h,div_self hI.ne']
      linarith
    · rw [min_eq_right h]
      have he : I/(lam/2)=2*(I/lam) := by ring
      rw [he]
      linarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith

lemma stabilityLength_pos {P C M A p w φ : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hM : 0 < M) (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) :
    0 < stabilityLength P C M A p w φ := by
  unfold stabilityLength stabilityRate
  have hm : 0 < min p w := lt_min hp hw
  have hr : 0  <  M/φ+Real.sqrt (A*Real.log (2+P)/φ) :=
    add_pos_of_pos_of_nonneg (div_pos hM hφ) (Real.sqrt_nonneg _)
  positivity

lemma direction_clipped_baseline_R_log_bound {P C M A p w φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hpP : p ≤ P) (hwP : w ≤ P) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    Real.sqrt I*Real.sqrt (1+I/min I (lam/2))*p*φ  ≤
      2*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hI : 0 < (w/P)^2 := sq_pos_of_pos (div_pos hw hP)
  have hlam := stabilityLength_pos hP hC hM hp hw hφ (A:=A)
  have hroot := sqrt_baseline_clipped_length hI hlam
  have hbound := direction_baseline_R_log_bound hP hL hC.le hM.le hA hp hw hφ hφ1 hpP hwP
  calc
    _  ≤  Real.sqrt ((w/P)^2)*(2*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ)))*p*φ := by gcongr
    _ = 2*(Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ) := by ring
    _  ≤  2*((1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma stability_massScale_identity (P C M A p w φ : ℝ) :
    (C*(P/(min p w/128))*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2 =
      stabilityLength P (128*C) M A p w φ := by
  unfold stabilityLength stabilityRate
  congr 2
  ring

lemma direction_baseline_R_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*w*(1+C*(M+Real.sqrt (A*Real.log (2+P)))) := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < min p w := lt_min hp hw
  have hwP' : w≤128*P := hwP.trans (by linarith only [hP])
  have hwp := product_le_min_scale hp.le hw.le hpP hwP'
  have hmain : w^2*p/(P*min p w)≤128*w := by
    apply (div_le_iff₀ (mul_pos hP hm)).mpr
    nlinarith
  have hfirst : w*p*φ/P≤128*w := by
    apply (div_le_iff₀ hP).mpr
    have hh : p*φ≤128*P := (mul_le_of_le_one_right hp.le hφ1).trans hpP
    nlinarith
  have hroot : φ*Real.sqrt (A*Real.log (2+P)/φ)=
      Real.sqrt (A*Real.log (2+P)*φ) := by
    calc
      _ = Real.sqrt (φ^2)*Real.sqrt (A*Real.log (2+P)/φ) := by rw [Real.sqrt_sq hφ.le]
      _ = Real.sqrt (A*Real.log (2+P)*φ) := by
        rw [←Real.sqrt_mul (sq_nonneg φ)]
        congr 1
        field_simp
  have hsqrt : Real.sqrt (A*Real.log (2+P)*φ)≤Real.sqrt (A*Real.log (2+P)) :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right (mul_nonneg hA hL) hφ1)
  rw [Real.sqrt_sq (div_nonneg hw.le hP.le),
    sqrt_div_stabilityLength hP.le hC hM hp.le hw.le hφ.le (sq_nonneg _),
    Real.sqrt_sq (div_nonneg hw.le hP.le)]
  have he : (w/P)*(1+(w/P)*stabilityRate P C M A p w φ)*p*φ=
      w*p*φ/P+C*(w^2*p/(P*min p w))*(M+φ*Real.sqrt (A*Real.log (2+P)/φ)) := by
    unfold stabilityRate
    field_simp
  rw [he,hroot]
  calc
    _ ≤ 128*w+C*(128*w)*(M+Real.sqrt (A*Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma direction_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  apply (direction_baseline_R_bound128 hP hC hM hA hp hw hφ hφ1 hpP hwP).trans
  rw [Real.sqrt_mul hA]
  have hroot : 1≤Real.sqrt (Real.log (2+P)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have h0 : 0≤1+C*M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg (show 0≤128*w by positivity) h0)]

lemma direction_clipped_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hpP : p ≤ 128*P) (hwP : w ≤ P) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    Real.sqrt I*Real.sqrt (1+I/min I (lam/2))*p*φ  ≤
      256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hI : 0 < (w/P)^2 := sq_pos_of_pos (div_pos hw hP)
  have hlam := stabilityLength_pos hP hC hM hp hw hφ (A:=A)
  have hroot := sqrt_baseline_clipped_length hI hlam
  have hbound := direction_baseline_R_log_bound128 hP hL hC.le hM.le hA hp hw hφ hφ1 hpP hwP
  calc
    _  ≤  Real.sqrt ((w/P)^2)*(2*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ)))*p*φ := by gcongr
    _ = 2*(Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ) := by ring
    _  ≤  2*(128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma direction_clipped_source_angle_bound {P C M A p w θ φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 1 ≤ p) (hw : 1 ≤ w) (hθ : 0 ≤ θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hθφ : θ ≤ φ) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    Real.sqrt (1+I/min I (lam/2))*θ ≤
      2*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hm : 1 ≤ min p w := le_min hp hw
  have hm0 : 0 < min p w := zero_lt_one.trans_le hm
  have hI : 0 < (w/P)^2 := sq_pos_of_pos (div_pos hw0 hP)
  have hlam := stabilityLength_pos hP hC hM hp0 hw0 hφ (A:=A)
  have hroot := sqrt_baseline_clipped_length hI hlam
  have hlog : 0 ≤ Real.log (2+P) := le_trans (by norm_num) hL
  have hθ1 : θ ≤ 1 := hθφ.trans hφ1
  have hquot : θ/φ ≤ 1 := (div_le_one hφ).mpr hθφ
  have hwm : w/min p w ≤ w := div_le_self hw0.le hm
  have hsqrt : θ*Real.sqrt (A*Real.log (2+P)/φ) ≤ Real.sqrt (A*Real.log (2+P)) := by
    calc
      _ ≤ φ*Real.sqrt (A*Real.log (2+P)/φ) := mul_le_mul_of_nonneg_right hθφ (Real.sqrt_nonneg _)
      _ = Real.sqrt (φ^2)*Real.sqrt (A*Real.log (2+P)/φ) := by rw [Real.sqrt_sq hφ.le]
      _ = Real.sqrt (A*Real.log (2+P)*φ) := by
        rw [←Real.sqrt_mul (sq_nonneg φ)]
        congr 1
        field_simp
      _ ≤ _ := Real.sqrt_le_sqrt (mul_le_of_le_one_right (mul_nonneg hA hlog) hφ1)
  have hr : 1 ≤ Real.sqrt (Real.log (2+P)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have he : 2*(1+(w/P)*stabilityRate P C M A p w φ)*θ=
      2*θ+2*C*(w/min p w)*(M*(θ/φ)+θ*Real.sqrt (A*Real.log (2+P)/φ)) := by
    unfold stabilityRate
    field_simp
  have hMQ : M*(θ/φ)≤M := mul_le_of_le_one_right hM.le hquot
  have hθw : θ≤w := hθ1.trans hw
  rw [sqrt_div_stabilityLength hP.le hC.le hM.le hp0.le hw0.le hφ.le hI.le,
    Real.sqrt_sq (div_nonneg hw0.le hP.le)] at hroot
  calc
    _ ≤ 2*(1+(w/P)*stabilityRate P C M A p w φ)*θ := mul_le_mul_of_nonneg_right hroot hθ
    _ = _ := he
    _ ≤ 2*w+2*C*w*(M+Real.sqrt (A*Real.log (2+P))) := by gcongr
    _ ≤ _ := by
      rw [Real.sqrt_mul hA]
      have h0 : 0≤1+C*M := by positivity
      nlinarith only [mul_le_mul_of_nonneg_left hr (mul_nonneg hw0.le h0)]

lemma direction_source_far_scale {P C M A p w θ r φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 1 ≤ p) (hw : 1 ≤ w) (hθ : 0 < θ) (hr : 0 < r) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hθφ : θ ≤ φ) (hpP : p ≤ 128*P) (hwP : w ≤ P)
    (hfar : 1/32 ≤ p*θ*Real.sqrt r) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    let R := Real.sqrt (1+I/min I (lam/2))
    Real.sqrt I*R*φ/(θ*Real.sqrt r)+2*R*θ ≤
      8196*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hB := direction_clipped_baseline_R_log_bound128 hP hL hC hM hA hp0 hw0 hφ hφ1 hpP hwP
  have hR := direction_clipped_source_angle_bound hP hL hC hM hA hp hw hθ.le hφ hφ1 hθφ
  have hfirst : Real.sqrt ((w/P)^2)*Real.sqrt (1+(w/P)^2/min ((w/P)^2)
      (stabilityLength P C M A p w φ/2))*φ/(θ*Real.sqrt r) ≤
      8192*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
    let B := (1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))
    have h0 : 0≤B := by dsimp [B]; positivity
    apply (div_le_iff₀ (mul_pos hθ (Real.sqrt_pos.mpr hr))).mpr
    have hh := mul_le_mul_of_nonneg_left hfar (show 0≤8192*B by positivity)
    have hB' : Real.sqrt ((w/P)^2)*Real.sqrt (1+(w/P)^2/min ((w/P)^2)
        (stabilityLength P C M A p w φ/2))*p*φ ≤ 256*B := by simpa only [B,mul_assoc] using hB
    apply (mul_le_mul_iff_right₀ hp0).mp
    dsimp [B] at *
    nlinarith only [hh,hB']
  nlinarith only [hfirst,hR]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma remaining_good_angular {θ φ σ κ : ℝ} (hθ : 0≤θ) (hφ : 0≤φ)
    (hσ : 0<σ) (_hκ : 0≤κ) (hφθ : φ≤κ*θ) :
    (min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)≤κ^2*(1+κ)*σ*θ^4 := by
  let ν := min θ σ
  have hν : 0≤ν := le_min hθ hσ.le
  have hnθ : ν≤θ := min_le_left _ _
  have hnσ : ν≤σ := min_le_right _ _
  have hroot : Real.sqrt (1+φ/σ)≤1+φ/σ :=
    Real.sqrt_le_self_iff.mpr (Or.inr (le_add_of_nonneg_right (div_nonneg hφ hσ.le)))
  have hc1 : ν^3≤σ*θ^2 := by
    calc
      _ = ν*ν^2 := by ring
      _ ≤ σ*θ^2 := by gcongr
  have hc2 : ν^3≤σ^2*θ := by
    calc
      _ = ν^2*ν := by ring
      _ ≤ σ^2*θ := by gcongr
  have h1 : ν^3*φ^2≤κ^2*σ*θ^4 := by
    calc
      _ ≤ (σ*θ^2)*(κ*θ)^2 := mul_le_mul hc1 (by gcongr) (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : ν^3*φ^3/σ≤κ^3*σ*θ^4 := by
    calc
      _ ≤ (σ^2*θ)*(κ*θ)^3/σ := by gcongr
      _ = _ := by field_simp
  change ν^3*φ^2*Real.sqrt (1+φ/σ)≤_
  calc
    _ ≤ ν^3*φ^2*(1+φ/σ) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = ν^3*φ^2+ν^3*φ^3/σ := by ring
    _ ≤ κ^2*σ*θ^4+κ^3*σ*θ^4 := add_le_add h1 h2
    _ = _ := by ring

lemma remaining_magnetic_angular {θ φ σ κ : ℝ} (hθ : 0≤θ) (hθ1 : θ≤1)
    (hφ : 0≤φ) (hσ : 0<σ) (hκ : 0≤κ) (hφθ : φ≤κ*θ) :
    (min θ σ)^3*Real.sqrt (1+φ/σ)≤(1+κ)*σ := by
  let ν := min θ σ
  have hν : 0≤ν := le_min hθ hσ.le
  have hnθ : ν≤θ := min_le_left _ _
  have hnσ : ν≤σ := min_le_right _ _
  have hroot : Real.sqrt (1+φ/σ)≤1+φ/σ :=
    Real.sqrt_le_self_iff.mpr (Or.inr (le_add_of_nonneg_right (div_nonneg hφ hσ.le)))
  have hc1 : ν^3≤σ*θ^2 := by
    calc
      _ = ν*ν^2 := by ring
      _ ≤ σ*θ^2 := by gcongr
  have hc2 : ν^3≤σ^2*θ := by
    calc
      _ = ν^2*ν := by ring
      _ ≤ σ^2*θ := by gcongr
  have hθ2 : θ^2≤1 := by nlinarith
  have h1 : ν^3≤σ := hc1.trans (by nlinarith)
  have h2 : ν^3*φ/σ≤κ*σ := by
    calc
      _ ≤ (σ^2*θ)*(κ*θ)/σ := by gcongr
      _ = κ*σ*θ^2 := by field_simp
      _ ≤ κ*σ := by nlinarith [mul_nonneg hκ hσ.le]
  change ν^3*Real.sqrt (1+φ/σ)≤_
  calc
    _ ≤ ν^3*(1+φ/σ) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = ν^3+ν^3*φ/σ := by ring
    _ ≤ σ+κ*σ := add_le_add h1 h2
    _ = _ := by ring

lemma remaining_transport_angular {θ φ σ κ : ℝ} (hθ : 0<θ) (hφ : 0≤φ)
    (hσ : 0<σ) (hκ : 0≤κ) (hφθ : φ≤κ*θ) :
    (min θ σ)*φ*Real.sqrt (1+φ/σ)/θ^3≤κ*(1+κ)/θ := by
  let ν := min θ σ
  have hν : 0≤ν := le_min hθ.le hσ.le
  have hnθ : ν≤θ := min_le_left _ _
  have hnσ : ν≤σ := min_le_right _ _
  have hroot : Real.sqrt (1+φ/σ)≤1+φ/σ :=
    Real.sqrt_le_self_iff.mpr (Or.inr (le_add_of_nonneg_right (div_nonneg hφ hσ.le)))
  have h1 : ν*φ≤κ*θ^2 := by
    calc
      _ ≤ θ*(κ*θ) := by gcongr
      _ = _ := by ring
  have h2 : ν*φ^2/σ≤κ^2*θ^2 := by
    calc
      _ ≤ σ*(κ*θ)^2/σ := by gcongr
      _ = _ := by field_simp
  have hh : ν*φ*Real.sqrt (1+φ/σ)≤κ*(1+κ)*θ^2 := by
    calc
      _ ≤ ν*φ*(1+φ/σ) := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = ν*φ+ν*φ^2/σ := by ring
      _ ≤ κ*θ^2+κ^2*θ^2 := add_le_add h1 h2
      _ = _ := by ring
  change ν*φ*Real.sqrt (1+φ/σ)/θ^3≤_
  calc
    _ ≤ (κ*(1+κ)*θ^2)/θ^3 := div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

lemma direction_interval_momentum_factor {P p w : ℝ}
    (hP : 0<P) (hp : 0≤p) (hw : 0≤w) (hpP : p≤128*P) (hwP : w≤P) :
    (w/P)^2*p≤128*w := by
  have hwq : w/P≤1 := (div_le_one hP).mpr hwP
  have hpq : p/P≤128 := (div_le_iff₀ hP).mpr hpP
  calc
    _ = (w/P)*w*(p/P) := by ring
    _ ≤ 1*w*128 := by gcongr
    _ = _ := by ring

lemma remaining_good_balance_coefficient {P C M A p w θ φ σ κ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hθ : 0<θ) (hφ : 0≤φ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκ : 0≤κ) (hφθ : φ≤κ*θ) (hpP : p≤128*P) (hwP : w≤P) :
    let I := (w/P)^2
    let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
    I*Real.sqrt I*R*p^2*((min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/θ^4)≤
      32768*κ^2*(1+κ)*(1+C*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P)) := by
  let I := (w/P)^2
  let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
  change I*Real.sqrt I*R*p^2*((min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/θ^4)≤_
  have hI : 0≤I := sq_nonneg _
  have hR : 0≤R := Real.sqrt_nonneg _
  have hang : (min θ σ)^3*φ^2*Real.sqrt (1+φ/σ)/θ^4≤κ^2*(1+κ)*σ := by
    apply (div_le_iff₀ (pow_pos hθ 4)).mpr
    exact remaining_good_angular hθ.le hφ hσ hκ hφθ
  have hrate := direction_clipped_baseline_R_log_bound128 hP hL hC hM hA hp hw hσ hσ1 hpP hwP
  change Real.sqrt I*R*p*σ≤_ at hrate
  have hIp := direction_interval_momentum_factor hP hp.le hw.le hpP hwP
  change I*p≤_ at hIp
  calc
    _ ≤ I*Real.sqrt I*R*p^2*(κ^2*(1+κ)*σ) := by gcongr
    _ = (κ^2*(1+κ))*(I*p)*(Real.sqrt I*R*p*σ) := by ring
    _ ≤ (κ^2*(1+κ))*(128*w)*
        (256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma remaining_magnetic_balance_coefficient {P C M A p w θ φ σ κ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hθ : 0≤θ) (hθ1 : θ≤1) (hφ : 0≤φ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκ : 0≤κ) (hφθ : φ≤κ*θ) (hpP : p≤128*P) (hwP : w≤P) :
    let I := (w/P)^2
    let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
    I*Real.sqrt I*R*p^2*((min θ σ)^3*Real.sqrt (1+φ/σ))≤
      32768*(1+κ)*(1+C*(M+Real.sqrt A))*w^2*Real.sqrt (Real.log (2+P)) := by
  let I := (w/P)^2
  let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
  change I*Real.sqrt I*R*p^2*((min θ σ)^3*Real.sqrt (1+φ/σ))≤_
  have hI : 0≤I := sq_nonneg _
  have hR : 0≤R := Real.sqrt_nonneg _
  have hang := remaining_magnetic_angular hθ hθ1 hφ hσ hκ hφθ
  have hrate := direction_clipped_baseline_R_log_bound128 hP hL hC hM hA hp hw hσ hσ1 hpP hwP
  change Real.sqrt I*R*p*σ≤_ at hrate
  have hIp := direction_interval_momentum_factor hP hp.le hw.le hpP hwP
  change I*p≤_ at hIp
  calc
    _ ≤ I*Real.sqrt I*R*p^2*((1+κ)*σ) := by gcongr
    _ = (1+κ)*(I*p)*(Real.sqrt I*R*p*σ) := by ring
    _ ≤ (1+κ)*(128*w)*
        (256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma remaining_transport_balance_coefficient {P C M A p w θ φ σ κ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0<C) (hM : 0<M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hθ : 0<θ) (hφ : 0≤φ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hκ : 0≤κ) (hφθ : φ≤κ*θ) (hpP : p≤128*P) (hwP : w≤P)
    (hpθ : 1≤p*θ) (hpσ : 1≤p*σ) :
    let I := (w/P)^2
    let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
    (Real.sqrt I*R/p)*((min θ σ)*φ*Real.sqrt (1+φ/σ)/θ^3)≤
      256*κ*(1+κ)*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  let I := (w/P)^2
  let R := Real.sqrt (1+I/min I (stabilityLength P C M A p w σ/2))
  change (Real.sqrt I*R/p)*((min θ σ)*φ*Real.sqrt (1+φ/σ)/θ^3)≤_
  have hS : 0≤Real.sqrt I*R := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hang := remaining_transport_angular hθ hφ hσ hκ hφθ
  have hrate := direction_clipped_baseline_R_log_bound128 hP hL hC hM hA hp hw hσ hσ1 hpP hwP
  change Real.sqrt I*R*p*σ≤_ at hrate
  have hden : (Real.sqrt I*R)/(p*θ)≤Real.sqrt I*R := div_le_self hS hpθ
  have hscale : Real.sqrt I*R≤Real.sqrt I*R*p*σ := by
    nlinarith [mul_le_mul_of_nonneg_left hpσ hS]
  calc
    _ ≤ (Real.sqrt I*R/p)*(κ*(1+κ)/θ) := mul_le_mul_of_nonneg_left hang (div_nonneg hS hp.le)
    _ = κ*(1+κ)*((Real.sqrt I*R)/(p*θ)) := by ring
    _ ≤ κ*(1+κ)*(Real.sqrt I*R*p*σ) := mul_le_mul_of_nonneg_left (hden.trans hscale) (by positivity)
    _ ≤ κ*(1+κ)*(256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

end RVM

end

end OAI
