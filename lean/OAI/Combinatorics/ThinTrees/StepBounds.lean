import OAI.Combinatorics.ThinTrees.Normalization

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace StrongThinTree

def splitEpsilon (r : ℕ) : ℝ := 6*resistanceT r
def splitTau (r : ℕ) : ℝ := 2*Real.sqrt (splitEpsilon r)+splitEpsilon r
def stepCount (r : ℕ) : ℕ := ⌊(1-4*errorU r)*r/2⌋₊

lemma tendsto_errorU : Tendsto errorU atTop (𝓝 0) := by
  change Tendsto (fun r : ℕ => errorU r) atTop (𝓝 0)
  simpa [errorU,Function.comp_def,neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/16)).comp tendsto_natCast_atTop_atTop
lemma tendsto_resistanceT : Tendsto resistanceT atTop (𝓝 0) := by
  change Tendsto (fun r : ℕ => resistanceT r) atTop (𝓝 0)
  simpa [resistanceT,Function.comp_def,neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
lemma resistanceT_sq {r : ℕ} (hr : 0 < r) : resistanceT r^2=1/(r:ℝ) := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  unfold resistanceT
  rw [pow_two,←Real.rpow_add hrR]
  norm_num [Real.rpow_neg_one]
lemma splitTau_ratio {r : ℕ} (hr : 0 < r) :
    splitTau r=(2*Real.sqrt 6*(r:ℝ)^(-3/16:ℝ)+6*(r:ℝ)^(-7/16:ℝ))*errorU r := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hs : Real.sqrt (splitEpsilon r)=Real.sqrt 6*(r:ℝ)^(-1/4:ℝ) := by
    rw [splitEpsilon,resistanceT,Real.sqrt_mul (by norm_num),Real.sqrt_eq_rpow ((r:ℝ)^(-1/2:ℝ)),←Real.rpow_mul hrR.le]
    norm_num
  rw [splitTau,hs,splitEpsilon,resistanceT,errorU,add_mul]
  have h1 : (r:ℝ)^(-3/16:ℝ)*(r:ℝ)^(-1/16:ℝ)=(r:ℝ)^(-1/4:ℝ) := by
    rw [←Real.rpow_add hrR]; norm_num
  have h2 : (r:ℝ)^(-7/16:ℝ)*(r:ℝ)^(-1/16:ℝ)=(r:ℝ)^(-1/2:ℝ) := by
    rw [←Real.rpow_add hrR]; norm_num
  calc
    _ = 2*Real.sqrt 6*((r:ℝ)^(-3/16:ℝ)*(r:ℝ)^(-1/16:ℝ))+
        6*((r:ℝ)^(-7/16:ℝ)*(r:ℝ)^(-1/16:ℝ)) := by rw [h1,h2]; ring
    _ = _ := by ring

lemma inverse_le_errorU {r : ℕ} (hr : 1 ≤ r) : 1/(r:ℝ) ≤ errorU r := by
  have hh := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ r by exact_mod_cast hr) (by norm_num : (-1:ℝ) ≤ -1/16)
  simpa only [Real.rpow_neg_one,one_div,errorU] using hh

lemma step_rounding {r : ℕ} (hr : 4 ≤ r) (hu : errorU r ≤ 1/16)
    (hτ : splitTau r ≤ errorU r/2) :
    stepCount r ≤ ⌊(1/2-splitTau r)*(extractQ r:ℝ)/(1+errorU r)⌋₊ ∧
    (5/16:ℝ)*r ≤ stepCount r ∧ (stepCount r:ℝ) ≤ (r:ℝ)/2 ∧
    (1/2+3*splitTau r)*(r:ℝ) ≤ (1+15*errorU r)*stepCount r := by
  have hrR : (4:ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (0:ℝ) < r := by linarith
  have hu0 : 0 ≤ errorU r := Real.rpow_nonneg hrp.le _
  have ht0 : 0 ≤ splitTau r := by unfold splitTau splitEpsilon resistanceT; positivity
  have hc : 0 ≤ 1/2-splitTau r := by linarith
  have hinv := inverse_le_errorU (by omega : 1 ≤ r)
  have hru : 1 ≤ errorU r*r := (div_le_iff₀ hrp).mp hinv
  obtain ⟨_,_,_,hq⟩ := extractQ_bounds hrR (by linarith)
  have hab : 0 ≤ (1-errorU r)*r-1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hq hc
  have hτm := mul_le_mul_of_nonneg_right hτ hab
  have hur2 : 0 ≤ (r:ℝ)*(errorU r)^2 := mul_nonneg hrp.le (sq_nonneg _)
  have hpack : (1-4*errorU r)*r/2 ≤ (1/2-splitTau r)*(extractQ r:ℝ)/(1+errorU r) := by
    apply (le_div_iff₀ (by linarith : 0 < 1+errorU r)).mpr
    nlinarith
  have hfloorLo := Nat.sub_one_lt_floor ((1-4*errorU r)*r/2)
  have hfloorHi := Nat.floor_le (show 0 ≤ (1-4*errorU r)*r/2 by positivity [show 0 ≤ 1-4*errorU r by linarith])
  change (1-4*errorU r)*r/2-1 < (stepCount r:ℝ) at hfloorLo
  change (stepCount r:ℝ) ≤ (1-4*errorU r)*r/2 at hfloorHi
  have hcountLo : (1/2-3*errorU r)*r ≤ (stepCount r:ℝ) := by nlinarith
  have hcountPos : 0 ≤ (stepCount r:ℝ) := Nat.cast_nonneg _
  have hul := mul_le_mul_of_nonneg_right hu hrp.le
  have hum := mul_nonneg hu0 (show 0 ≤ 3-45*errorU r by linarith)
  have humr := mul_nonneg hrp.le hum
  have hproduct := mul_le_mul_of_nonneg_left hcountLo (show 0 ≤ 1+15*errorU r by positivity)
  refine ⟨Nat.floor_le_floor hpack,by nlinarith,by nlinarith,?_⟩
  have hτr := mul_le_mul_of_nonneg_right hτ hrp.le
  nlinarith

structure StepNumeric (r : ℕ) : Prop where
  rlarge : 4 ≤ r
  usmall : errorU r ≤ 1/16
  qpos : 0 < extractQ r
  size : (1+errorU r)/(extractQ r:ℝ) ≤ 2*resistanceT r
  tausmall : splitTau r ≤ errorU r/2
  packing : stepCount r ≤ ⌊(1/2-splitTau r)*(extractQ r:ℝ)/(1+errorU r)⌋₊
  lower : (5/16:ℝ)*r ≤ stepCount r
  upper : (stepCount r:ℝ) ≤ (r:ℝ)/2
  ratio : (1/2+3*splitTau r)*(r:ℝ) ≤ (1+15*errorU r)*stepCount r

lemma eventual_step_numeric : ∃R : ℕ, ∀r : ℕ, R ≤ r → StepNumeric r := by
  have htau : Tendsto (fun r : ℕ => 2*Real.sqrt 6*(r:ℝ)^(-3/16:ℝ)+6*(r:ℝ)^(-7/16:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def,neg_div] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/16)).const_mul (2*Real.sqrt 6)).add
        ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 7/16)).const_mul 6)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ r : ℕ in atTop, 4 ≤ r ∧ errorU r ≤ 1/16 ∧ resistanceT r ≤ 1/2 ∧
      2*Real.sqrt 6*(r:ℝ)^(-3/16:ℝ)+6*(r:ℝ)^(-7/16:ℝ) ≤ 1/2 := by
    filter_upwards [eventually_ge_atTop 4,
      tendsto_errorU.eventually_lt_const (by norm_num : (0:ℝ) < 1/16),
      tendsto_resistanceT.eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
      htau.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with r hr hu ht hτ
    exact ⟨hr,hu.le,ht.le,hτ.le⟩
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  refine ⟨R,fun r hr => ?_⟩
  obtain ⟨hr4,hu,ht,hτ⟩ := hR r hr
  have hrp : 0 < r := by omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hrp
  have hu0 : 0 ≤ errorU r := Real.rpow_nonneg hrR.le _
  have hτsmall : splitTau r ≤ errorU r/2 := by
    rw [splitTau_ratio hrp]
    have hh := mul_le_mul_of_nonneg_right hτ hu0
    linarith
  obtain ⟨hpack,hlo,hhi,hratio⟩ := step_rounding hr4 hu hτsmall
  obtain ⟨hqlo,_,_,_⟩ := extractQ_bounds (by exact_mod_cast hr4) (by linarith)
  have hqp : (0:ℝ) < extractQ r := by linarith
  have htpos : 0 < resistanceT r := Real.rpow_pos_of_pos hrR _
  have hinv : 4/(r:ℝ) ≤ 2*resistanceT r := by
    have hh := resistanceT_sq hrp
    have hmul := mul_le_mul_of_nonneg_left ht htpos.le
    rw [show 4/(r:ℝ)=4*(resistanceT r)^2 by rw [hh]; ring]
    nlinarith
  have hsize : (1+errorU r)/(extractQ r:ℝ) ≤ 2*resistanceT r := by
    apply le_trans _ hinv
    apply (div_le_div_iff₀ hqp hrR).mpr
    nlinarith
  exact ⟨hr4,hu,by exact_mod_cast hqp,hsize,hτsmall,hpack,hlo,hhi,hratio⟩
end StrongThinTree

end
end

end OAI
