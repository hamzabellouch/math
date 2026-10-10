import OAI.Geometry.TranslativeCovering.WitnessBlocks

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace RadialCost
noncomputable def weight (n : ℕ) (a r : ℝ) : ℝ := 1+(n:ℝ)*max (1-r^2/a^2) 0

lemma weight_ge_one (n : ℕ) (a r : ℝ) : 1 ≤ weight n a r := by
  unfold weight
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _))

lemma radial_deficit {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    a-r ≤ a*max (1-r^2/a^2) 0 := by
  by_cases h : r ≤ a
  · have haa : 0 < a^2 := sq_pos_of_pos ha
    have hr2 : r^2 ≤ a^2 := (sq_le_sq₀ hr ha.le).mpr h
    rw [max_eq_left (by exact sub_nonneg.mpr ((div_le_one haa).mpr hr2))]
    apply (mul_le_mul_iff_right₀ ha).mp
    field_simp
    nlinarith only [sq_nonneg (a-r),mul_nonneg hr (sub_nonneg.mpr h)]
  · have hq := mul_nonneg ha.le (le_max_right (1-r^2/a^2) 0)
    linarith only [hq,le_of_not_ge h]

lemma upper_threshold {n : ℕ} {a r η : ℝ} (ha : 1 ≤ a) (hr : a/2 ≤ r)
    (hη : 0 ≤ η) (hnη : (n:ℝ)*η ≤ 1) :
    (n:ℝ)*max ((1+3*η)/r-1/a) 0 ≤ (8/a)*weight n a r := by
  have hap : 0 < a := by linarith
  have hrp : 0 < r := by linarith
  let q := max (1-r^2/a^2) 0
  have hq : 0 ≤ q := le_max_right _ _
  have hd : a-r ≤ a*q := radial_deficit hap hrp.le
  have ht : (1+3*η)/r-1/a ≤ (2*q+6*η)/a := by
    apply (le_div_iff₀ hap).mpr
    rw [show ((1+3*η)/r-1/a)*a = ((1+3*η)*a-r)/r by field_simp]
    apply (div_le_iff₀ hrp).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hq) (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hη))
    nlinarith only [hd,hh]
  have ht0 : 0 ≤ (2*q+6*η)/a := by positivity
  have hh := mul_le_mul_of_nonneg_left (max_le ht ht0) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hw : 0 ≤ (n:ℝ)*q := mul_nonneg (Nat.cast_nonneg n) hq
  calc
    _ ≤ (n:ℝ)*((2*q+6*η)/a) := hh
    _ = (2*((n:ℝ)*q)+6*((n:ℝ)*η))/a := by ring
    _ ≤ (2*((n:ℝ)*q)+6)/a := div_le_div_of_nonneg_right (by linarith only [hnη]) hap.le
    _ ≤ (8/a)*weight n a r := by
      change (2*((n:ℝ)*q)+6)/a ≤ (8/a)*(1+(n:ℝ)*q)
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith only [hw]) hap.le

lemma lower_threshold {n : ℕ} {a r η : ℝ} (hn : 0 < n) (ha : 1 ≤ a)
    (hr : a/2 ≤ r) (hη : 0 ≤ η) (hnη : (n:ℝ)*η ≤ 1)
    (hru : r ≤ a*(1+1/(n:ℝ))+3*η) :
    (n:ℝ)*max (1/a-(1+3*η)/r) 0 ≤ 8 := by
  have hap : 0 < a := by linarith
  have hrp : 0 < r := by linarith
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hu : (n:ℝ)*(r-a) ≤ a+3 := by
    have h := mul_le_mul_of_nonneg_left hru hnp.le
    field_simp at h
    nlinarith only [h,hnη]
  have ht : (n:ℝ)*(1/a-(1+3*η)/r) ≤ 8 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hap hrp)).mp
    field_simp
    have hp := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (mul_nonneg hap.le hη)
    have har := mul_le_mul_of_nonneg_left hr hap.le
    nlinarith only [hu,hp,har,ha,sq_nonneg (a-1)]
  rw [mul_max_of_nonneg _ _ hnp.le,mul_zero]
  exact max_le ht (by norm_num)

end RadialCost

end OAI
