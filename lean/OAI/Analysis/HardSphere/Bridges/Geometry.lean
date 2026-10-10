import Mathlib

namespace OAI

section

section
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace HardSphere.Bridge

lemma power_div_identity {D : ℝ} (hD : 0 < D) (p : ℝ) :
    D^p/D = D^(p-1) := by
  rw [Real.rpow_sub hD,Real.rpow_one]

lemma source_geometry_eventually {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧ A/D ≤ 1 ∧ (A/D)^2 ≤ t ∧
      (A/D)*D^(1/12:ℝ) ≤ 1 ∧ 2*A^2 ≤ D ∧ 8*A^2 ≤ D ∧
      26*(A/D) ≤ t ∧ (13+Real.sqrt (2*t)*D^(1/12:ℝ))*(A/D) ≤ t ∧
      (D⁻¹/t)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12 ∧
      3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ) ∧
      A/D+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ) := by
  have h1 : Tendsto (fun D : ℝ ↦ A/D) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul A
  have h2 : Tendsto (fun D : ℝ ↦ A*D^(-(11/12):ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 11/12)).const_mul A
  have h3 : Tendsto (fun D : ℝ ↦ 13*(A/D)+Real.sqrt (2*t)*(A*D^(-(11/12):ℝ))) atTop (𝓝 0) := by
    simpa using (h1.const_mul 13).add (h2.const_mul (Real.sqrt (2*t)))
  have h4 : Tendsto (fun D : ℝ ↦ D^(-(2/3):ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h5 : Tendsto (fun D : ℝ ↦ D^(1/12:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),h1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    (h1.pow 2).eventually (gt_mem_nhds (by simpa using ht)),
    h2.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    eventually_ge_atTop (8*A^2),
    (h1.const_mul 26).eventually (gt_mem_nhds (by simpa using ht)),
    h3.eventually (gt_mem_nhds ht),
    h4.eventually (gt_mem_nhds (by positivity : (0:ℝ) < b*t/(96*13))),
    h5.eventually (eventually_ge_atTop (6:ℝ)),
    h4.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 3*b/(4*A)))] with D hD hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hp : (A/D)*D^(1/12:ℝ)=A*D^(-(11/12):ℝ) := by
    calc
      _ = A*(D^(1/12:ℝ)/D) := by ring
      _ = _ := by rw [power_div_identity hDp]; norm_num
  have hq : D⁻¹ = D^(-(2/3):ℝ)*D^(-(1/3):ℝ) := by
    rw [←Real.rpow_add hDp]
    norm_num [Real.rpow_neg_one]
  refine ⟨hD,hd1.le,hd2.le,by rw [hp]; exact hd3.le,by nlinarith,hd4,hd5.le,?_,?_,by linarith,?_⟩
  · have he : (13+Real.sqrt (2*t)*D^(1/12:ℝ))*(A/D)=
        13*(A/D)+Real.sqrt (2*t)*(A*D^(-(11/12):ℝ)) := by rw [←hp]; ring
    rw [he]
    exact hd6.le
  · have hh := (lt_div_iff₀ (by norm_num : (0:ℝ) < 96*13)).mp hd7
    rw [hq]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ht).mpr
    have hmul := mul_le_mul_of_nonneg_right hh.le (by positivity : 0 ≤ D^(-(1/3):ℝ))
    nlinarith
  · have hh := (lt_div_iff₀ (by positivity : (0:ℝ) < 4*A)).mp hd9
    have hmul := mul_lt_mul_of_pos_right hh (by positivity : 0 < D^(-(1/3):ℝ))
    rw [div_eq_mul_inv,hq]
    nlinarith

lemma source_trial_geometry {A b t : ℝ} (hA : 0 < A) (hb : 0 < b) (ht : 0 < t) :
    ∀ᶠ D : ℝ in atTop, ∀α : ℝ,0 < α → α ≤ A →
      let r := α/D
      let n := ⌈t/r^2⌉₊
      1 ≤ D ∧ 0 < n ∧ r ≤ 1 ∧ r*D^(1/12:ℝ) ≤ 1 ∧
      t/(n:ℝ) ≤ r^2 ∧ (n:ℝ)*r^2 ≤ 2*t ∧
      0 ≤ D⁻¹/t ∧ D⁻¹/t ≤ 1 ∧
      2*(t/(n:ℝ)) ≤ D⁻¹ ∧ 8*t ≤ (n:ℝ)*D⁻¹ ∧
      2*13/(n:ℝ) ≤ r ∧ (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r ∧
      (D⁻¹/t)*13 ≤ (b*D^(-(1/3):ℝ)/8)/12 ∧
      3*(1+D^(1/12:ℝ)/6) ≤ D^(1/12:ℝ) ∧
      r+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ) := by
  filter_upwards [source_geometry_eventually hA hb ht,eventually_ge_atTop t⁻¹] with D h hd
  rcases h with ⟨hD,hA1,hAsq,hAR,hD2,hD8,h26,hQ,hwin,hrelax,hiso⟩
  intro α hα hαA
  dsimp only
  let r := α/D
  let n := ⌈t/r^2⌉₊
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hr : 0 < r := by dsimp [r]; positivity
  have hrA : r ≤ A/D := div_le_div_of_nonneg_right hαA hDp.le
  have hn : 0 < n := Nat.ceil_pos.mpr (by positivity : 0 < t/r^2)
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnr : t ≤ (n:ℝ)*r^2 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp (Nat.le_ceil (t/r^2))
    exact hh
  have hτ : t/(n:ℝ) ≤ r^2 := (div_le_iff₀ hnp).mpr (by nlinarith [hnr])
  have hrs : r^2 ≤ t := (pow_le_pow_left₀ hr.le hrA 2).trans hAsq
  have hup : (n:ℝ)*r^2 ≤ 2*t := by
    have hh := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity : 0 ≤ t/r^2)).le (sq_nonneg r)
    have he : (t/r^2+1)*r^2=t+r^2 := by field_simp
    rw [he] at hh
    nlinarith
  have hsq : r^2 ≤ D⁻¹/8 := by
    calc
      _ ≤ (A/D)^2 := pow_le_pow_left₀ hr.le hrA 2
      _ ≤ (1/8)/D := by
        apply (le_div_iff₀ hDp).mpr
        have he : (A/D)^2*D=A^2/D := by field_simp
        rw [he]
        exact (div_le_iff₀ hDp).mpr (by linarith)
      _ = _ := by ring
  have htime : D⁻¹/t ≤ 1 := by
    apply (div_le_iff₀ ht).mpr
    simp only [one_mul]
    rw [←one_div]
    apply (div_le_iff₀ hDp).mpr
    have hh := mul_le_mul_of_nonneg_left hd ht.le
    simpa [mul_inv_cancel₀ ht.ne'] using hh
  have hsmall : r*D^(1/12:ℝ) ≤ 1 := (mul_le_mul_of_nonneg_right hrA (by positivity)).trans hAR
  have hdr : 26/(n:ℝ) ≤ r := by
    apply (div_le_iff₀ hnp).mpr
    have hh : 26*r ≤ t := (mul_le_mul_of_nonneg_left hrA (by norm_num)).trans h26
    nlinarith
  have hdr' : (13+Real.sqrt (2*t)*D^(1/12:ℝ))/(n:ℝ) ≤ r := by
    apply (div_le_iff₀ hnp).mpr
    have hq : 0 ≤ 13+Real.sqrt (2*t)*D^(1/12:ℝ) := by positivity
    have hh := (mul_le_mul_of_nonneg_left hrA hq).trans hQ
    nlinarith
  refine ⟨hD,hn,hrA.trans hA1,hsmall,hτ,hup,by positivity,htime,?_,?_,?_,hdr',hwin,hrelax,?_⟩
  · change 2*(t/(n:ℝ)) ≤ D⁻¹
    nlinarith [inv_pos.mpr hDp]
  · change 8*t ≤ (n:ℝ)*D⁻¹
    have hh := mul_le_mul_of_nonneg_left hsq hnp.le
    nlinarith
  · change 2*13/(n:ℝ) ≤ r
    convert hdr using 1
    norm_num
  · change r+2*(b*D^(-(1/3):ℝ)/8) < b*D^(-(1/3):ℝ)
    linarith

end HardSphere.Bridge

end
end

end

end OAI
