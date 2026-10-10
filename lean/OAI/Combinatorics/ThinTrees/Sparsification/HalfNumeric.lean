import Mathlib
import OAI.Combinatorics.ThinTrees.IterationBounds
import OAI.Combinatorics.ThinTrees.Sparsification.ShortcutExtraction

namespace OAI

/-! Half numeric. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning Filter Topology
open scoped MatrixOrder

def countError (r : ℕ) : ℚ := 1/(Nat.nthRoot 16 r:ℚ)

def nextCount (r : ℕ) : ℕ := ⌊(1-16*countError r)*(r:ℚ)/2⌋₊

noncomputable def varianceBound (r : ℕ) : ℝ := 5*(r:ℝ)^(-1/4:ℝ)
noncomputable def halfError (r : ℕ) : ℝ := 20*Real.sqrt (2*varianceBound r)

lemma countError_bounds (r : ℕ) (hr : 0 < r) :
    errorU r ≤ (countError r:ℝ) ∧ (countError r:ℝ) ≤ 2*errorU r := by
  have hroot := nthRoot_le_real_root 16 r (by norm_num)
  have hr0 : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hu1 : (1:ℝ) ≤ Nat.nthRoot 16 r := by exact_mod_cast nthRoot_pos 16 r (by norm_num) hr
  have hup := real_root_lt_nthRoot_add 16 r (by norm_num)
  have hp : 0 < (r:ℝ)^(1/16:ℝ) := Real.rpow_pos_of_pos hr0 _
  have he : errorU r=1/((r:ℝ)^(1/16:ℝ)) := by
    simp only [errorU,show (-1/16:ℝ)= -(1/16:ℝ) by ring,Real.rpow_neg hr0.le,one_div]
  simp only [Nat.cast_ofNat] at hroot hup
  rw [he]
  have hg : (countError r:ℝ)=1/(Nat.nthRoot 16 r:ℝ) := by simp [countError]
  rw [hg]
  constructor
  · exact one_div_le_one_div_of_le (by linarith only [hu1]) hroot
  · have hu0 : 0 < (Nat.nthRoot 16 r:ℝ) := by linarith only [hu1]
    apply (div_le_iff₀ hu0).mpr
    rw [show 2*(1/((r:ℝ)^(1/16:ℝ)))*(Nat.nthRoot 16 r:ℝ)=
      (2*(Nat.nthRoot 16 r:ℝ))/((r:ℝ)^(1/16:ℝ)) by ring]
    apply (le_div_iff₀ hp).mpr
    linarith only [hu1,hup]

lemma halfError_ratio (r : ℕ) (hr : 0 < r) :
    halfError r=(20*Real.sqrt 10*errorU r)*errorU r := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hmul : errorU r*errorU r=(r:ℝ)^(-1/8:ℝ) := by
    rw [errorU,←Real.rpow_add hrR]
    norm_num
  rw [mul_assoc,hmul]
  unfold halfError varianceBound
  rw [show 2*(5*(r:ℝ)^(-1/4:ℝ))=10*(r:ℝ)^(-1/4:ℝ) by ring,
    Real.sqrt_mul (by norm_num),Real.sqrt_eq_rpow ((r:ℝ)^(-1/4:ℝ)),←Real.rpow_mul hrR.le]
  norm_num only [mul_div_assoc,mul_one,div_mul_div_comm]
  ring

structure Numeric (r : ℕ) : Prop where
  rlarge : 4 ≤ r
  small : errorU r ≤ 1/128
  inverse : 4/(r:ℝ) ≤ errorU r
  loss : halfError r ≤ errorU r

lemma eventual_numeric : ∃R : ℕ, ∀r, R ≤ r → Numeric r := by
  have hinv : Tendsto (fun r : ℕ => 4*(r:ℝ)^(-15/16:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def,neg_div] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<15/16)).const_mul 4).comp
        tendsto_natCast_atTop_atTop
  have heps : Tendsto (fun r : ℕ => 20*Real.sqrt 10*errorU r) atTop (𝓝 0) := by
    simpa using tendsto_errorU.const_mul (20*Real.sqrt 10)
  have hev : ∀ᶠ r : ℕ in atTop, 4 ≤ r ∧ errorU r ≤ 1/128 ∧
      4*(r:ℝ)^(-15/16:ℝ) ≤ 1 ∧ 20*Real.sqrt 10*errorU r ≤ 1 := by
    filter_upwards [eventually_ge_atTop 4,
      tendsto_errorU.eventually_lt_const (by norm_num : (0:ℝ)<1/128),
      hinv.eventually_lt_const (by norm_num : (0:ℝ)<1),
      heps.eventually_lt_const (by norm_num : (0:ℝ)<1)] with r hr hu hi he
    exact ⟨hr,hu.le,hi.le,he.le⟩
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  refine ⟨R,fun r hr => ?_⟩
  obtain ⟨hr4,hu,hi,he⟩ := hR r hr
  have hr0 : 0 < r := by omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr0
  refine ⟨hr4,hu,?_,?_⟩
  · have hpow : (r:ℝ)^(-15/16:ℝ)*errorU r=(r:ℝ)⁻¹ := by
      rw [errorU,←Real.rpow_add hrR]
      norm_num [Real.rpow_neg_one]
    have hh := mul_le_mul_of_nonneg_right hi (errorU_nonneg r)
    rw [mul_assoc,hpow,one_mul] at hh
    simpa only [div_eq_mul_inv] using hh
  · rw [halfError_ratio r hr0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (errorU_nonneg r)

lemma rounding_bounds {r : ℕ} (hn : Numeric r) :
    ((1/2:ℝ)-17*errorU r)*r ≤ nextCount r ∧
    (nextCount r:ℝ) ≤ ((1/2:ℝ)-8*errorU r)*r := by
  have hr0 : 0 < r := by have := hn.rlarge;omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr0
  have hu := errorU_nonneg r
  obtain ⟨hv,hv2⟩ := countError_bounds r hr0
  have hsmall := hn.small
  have hnonneg : 0 ≤ (1-16*countError r)*(r:ℚ)/2 := by
    have hh : (0:ℝ) ≤ (1-16*(countError r:ℝ))*(r:ℝ)/2 := by positivity [show 0 ≤ 1-16*(countError r:ℝ) by linarith only [hv2,hsmall]]
    exact_mod_cast hh
  have hlo := Nat.sub_one_lt_floor ((1-16*countError r)*(r:ℚ)/2)
  have hhi := Nat.floor_le hnonneg
  have hloR : (1-16*(countError r:ℝ))*(r:ℝ)/2-1 < (nextCount r:ℝ) := by exact_mod_cast hlo
  have hhiR : (nextCount r:ℝ) ≤ (1-16*(countError r:ℝ))*(r:ℝ)/2 := by exact_mod_cast hhi
  have hru := rounding_absorbed r (by omega)
  change 1 ≤ errorU r*r at hru
  constructor
  · have hm := mul_le_mul_of_nonneg_right hv2 hrR.le
    nlinarith only [hloR,hm,hru]
  · have hm := mul_le_mul_of_nonneg_right hv hrR.le
    nlinarith only [hhiR,hm]

lemma nextCount_bounds {r : ℕ} (hn : Numeric r) :
    (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r := by
  obtain ⟨hlo,hhi⟩ := rounding_bounds hn
  have hu := errorU_nonneg r
  have hsmall := hn.small
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := hn.rlarge;omega)
  have hm := mul_le_mul_of_nonneg_right hsmall hr0.le
  have hz := mul_nonneg hu hr0.le
  have hpos : (0:ℝ) < nextCount r := by nlinarith only [hlo,hm,hr0]
  exact ⟨by nlinarith only [hlo,hm],by nlinarith only [hhi,hz],by exact_mod_cast hpos⟩

lemma packing_numeric {r q : ℕ} (hn : Numeric r) (hq : 0 < q)
    (hqr : (1-6*errorU r)*(r:ℝ) ≤ q) :
    (nextCount r:ℝ)*((1+4/(r:ℝ))/(q:ℝ)) ≤ 1/2-halfError r := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := hn.rlarge;omega)
  have hq0 : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hu := errorU_nonneg r
  have herror0 : 0 ≤ halfError r := by unfold halfError; positivity
  have hc : 0 ≤ 1/2-halfError r := by linarith only [hn.loss,hn.small]
  rw [←mul_div_assoc,div_le_iff₀ hq0]
  have hupper := (rounding_bounds hn).2
  have hsize := mul_le_mul_of_nonneg_left hn.inverse (Nat.cast_nonneg (nextCount r) : (0:ℝ) ≤ _)
  have htarg := mul_le_mul_of_nonneg_left hqr hc
  have hm := mul_le_mul_of_nonneg_right hupper (by linarith only [hu] : 0 ≤ 1+errorU r)
  have hp : 0 ≤ (1-6*errorU r)*(r:ℝ) := mul_nonneg (by linarith only [hn.small]) hr0.le
  have hloss := mul_le_mul_of_nonneg_right hn.loss hp
  have husq := mul_nonneg (sq_nonneg (errorU r)) hr0.le
  have huR := mul_nonneg hu hr0.le
  nlinarith only [hsize,htarg,hm,hloss,husq,huR]

lemma half_ratio {r : ℕ} (hn : Numeric r) :
    (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r := by
  have hrR := (Nat.cast_nonneg r : (0:ℝ) ≤ r)
  have hu := errorU_nonneg r
  have hlo := (rounding_bounds hn).1
  have hB : 0 ≤ 20-1360*errorU r := by linarith only [hn.small]
  have hpos := mul_nonneg (mul_nonneg hu hB) hrR
  have hm := mul_le_mul_of_nonneg_left hlo (by linarith only [hu] : 0 ≤ 1+80*errorU r)
  have he := mul_le_mul_of_nonneg_right hn.loss hrR
  nlinarith only [hm,hpos,he]

lemma normalized_size {r q : ℕ} (hn : Numeric r)
    (hqr : (1-6*errorU r)*(r:ℝ) ≤ q) :
    (1+4/(r:ℝ))/(q:ℝ) ≤ 4*(r:ℝ)^(-1/4:ℝ) := by
  have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by have := hn.rlarge;omega)
  have hqR : (r:ℝ)/2 ≤ q := by
    have hm := mul_le_mul_of_nonneg_right hn.small hr0.le
    nlinarith only [hqr,hm]
  have hq0 : (0:ℝ) < q := by linarith only [hqR,hr0]
  have hi : (1+4/(r:ℝ))/(q:ℝ) ≤ 4/(r:ℝ) := by
    have hupp : 1+4/(r:ℝ) ≤ 2 := by linarith only [hn.inverse,hn.small]
    rw [div_le_div_iff₀ hq0 hr0]
    have hm := mul_le_mul_of_nonneg_right hupp hr0.le
    nlinarith only [hm,hqR]
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1:ℝ) ≤ r by exact_mod_cast (show 1 ≤ r by have := hn.rlarge;omega))
    (by norm_num : (-1:ℝ) ≤ -1/4)
  simp only [Real.rpow_neg_one] at hpow
  apply hi.trans
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 4)

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
