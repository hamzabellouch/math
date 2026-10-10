import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Smoothing

lemma inv_sqrt_eq_neg_half {x : ℝ} (hx : 0 ≤ x) :
    1/Real.sqrt x = x^(-(1/2:ℝ)) := by
  rw [Real.rpow_neg hx,← Real.sqrt_eq_rpow,one_div]

lemma intervalIntegrable_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => 1/Real.sqrt x) volume a b := by
  apply (intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) (r := -(1/2:ℝ)) (by norm_num)).congr
  intro x hx
  rw [uIoc_of_le hab] at hx
  exact (inv_sqrt_eq_neg_half (ha.trans hx.1.le)).symm

lemma integral_inv_sqrt {b : ℝ} (hb : 0 ≤ b) :
    (∫ x in (0:ℝ)..b, 1/Real.sqrt x) = 2*Real.sqrt b := by
  have he : (∫ x in (0:ℝ)..b, 1/Real.sqrt x) = ∫ x in (0:ℝ)..b, x^(-(1/2:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hb] at hx
    exact inv_sqrt_eq_neg_half hx.1
  rw [he,integral_rpow (Or.inl (by norm_num : -(1:ℝ) < -(1/2:ℝ)))]
  norm_num only [neg_add_cancel_left,show -(1/2:ℝ)+1=1/2 by norm_num,Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0),sub_zero]
  rw [← Real.sqrt_eq_rpow]
  ring

lemma intervalIntegrable_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun r => 1/Real.sqrt (r-a)) volume a b := by
  simpa only [zero_add,sub_add_cancel] using
    (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_right a

lemma intervalIntegrable_inv_sqrt_sub' {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun r => 1/Real.sqrt (b-r)) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_left b
  simpa only [sub_zero,sub_sub_cancel] using h.symm

lemma integral_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    (∫ r in a..b, 1/Real.sqrt (r-a)) = 2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1/Real.sqrt x) a,sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma integral_inv_sqrt_sub' {a b : ℝ} (hab : a ≤ b) :
    (∫ r in a..b, 1/Real.sqrt (b-r)) = 2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => 1/Real.sqrt x) b,sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma sqrt_kernel_bound {a r b : ℝ} (har : a < r) (hrb : r < b) :
    1/(Real.sqrt (r-a)*Real.sqrt (b-r)) ≤
      (2/Real.sqrt (b-a))*(1/Real.sqrt (r-a)+1/Real.sqrt (b-r)) := by
  have hp : 0 < Real.sqrt (r-a) := Real.sqrt_pos.mpr (sub_pos.mpr har)
  have hq : 0 < Real.sqrt (b-r) := Real.sqrt_pos.mpr (sub_pos.mpr hrb)
  have hh : 0 < Real.sqrt (b-a) := Real.sqrt_pos.mpr (sub_pos.mpr (har.trans hrb))
  have hps := Real.sq_sqrt (sub_pos.mpr har).le
  have hqs := Real.sq_sqrt (sub_pos.mpr hrb).le
  have hhs := Real.sq_sqrt (sub_pos.mpr (har.trans hrb)).le
  have hs : Real.sqrt (b-a) ≤ 2*(Real.sqrt (r-a)+Real.sqrt (b-r)) := by
    nlinarith [mul_nonneg hp.le hq.le]
  apply (div_le_iff₀ (mul_pos hp hq)).mpr
  have he : (2/Real.sqrt (b-a))*(1/Real.sqrt (r-a)+1/Real.sqrt (b-r)) *
      (Real.sqrt (r-a)*Real.sqrt (b-r)) =
      2*(Real.sqrt (r-a)+Real.sqrt (b-r))/Real.sqrt (b-a) := by
    field_simp
    ring
  rw [he]
  exact (le_div_iff₀ hh).mpr (by simpa using hs)

lemma intervalIntegrable_sqrt_kernel {a b : ℝ} (hab : a < b) :
    IntervalIntegrable (fun r => 1/(Real.sqrt (r-a)*Real.sqrt (b-r))) volume a b := by
  apply (((intervalIntegrable_inv_sqrt_sub hab.le).add
    (intervalIntegrable_inv_sqrt_sub' hab.le)).const_mul (2/Real.sqrt (b-a))).mono_fun'
      ((measurable_const.div ((measurable_id.sub_const a).sqrt.mul ((measurable_const.sub measurable_id).sqrt))).aestronglyMeasurable)
  rw [uIoc_of_le hab.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,show ∀ᵐ r ∂volume.restrict (Ioc a b), r ≠ b from
    (ae_restrict_of_ae (volume.ae_ne b))] with r hr hrb
  simp only [Pi.div_apply,Pi.mul_apply,Pi.sub_apply,id_eq]
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 1/(Real.sqrt (r-a)*Real.sqrt (b-r)) by positivity)]
  exact sqrt_kernel_bound hr.1 (lt_of_le_of_ne hr.2 hrb)

lemma integral_sqrt_kernel_le {a b : ℝ} (hab : a < b) :
    (∫ r in a..b, 1/(Real.sqrt (r-a)*Real.sqrt (b-r))) ≤ 8 := by
  have hL := intervalIntegrable_inv_sqrt_sub hab.le
  have hR := intervalIntegrable_inv_sqrt_sub' hab.le
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab.le
    (intervalIntegrable_sqrt_kernel hab) ((hL.add hR).const_mul (2/Real.sqrt (b-a)))
    (fun r hr => sqrt_kernel_bound hr.1 hr.2)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hL hR,
    integral_inv_sqrt_sub hab.le,integral_inv_sqrt_sub' hab.le] at h
  have hr : Real.sqrt (b-a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hab))
  have he : 2/Real.sqrt (b-a)*(2*Real.sqrt (b-a)+2*Real.sqrt (b-a)) = 8 := by field_simp; ring
  rwa [he] at h

end ZeroTemperatureSK.Smoothing

namespace ZeroTemperatureSK.Smoothing

def weightedValues (F : ℝ → ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {z | ∃ t ∈ Icc a b, ∃ x, z = Real.sqrt (b-t)*|F t x|}

def weightedSize (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ := sSup (weightedValues F a b)

lemma weightedValues_nonempty (F : ℝ → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (weightedValues F a b).Nonempty := by
  refine ⟨0,b,⟨hab,le_rfl⟩,0,?_⟩
  simp

lemma weightedValues_bddAbove {F : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) : BddAbove (weightedValues F a b) := by
  refine ⟨Real.sqrt (b-a)*max C 0,?_⟩
  rintro _ ⟨t,ht,x,rfl⟩
  apply mul_le_mul (Real.sqrt_le_sqrt (by linarith [ht.1]))
    ((hC t ht x).trans (le_max_left _ _)) (abs_nonneg _) (Real.sqrt_nonneg _)

lemma weighted_le_size {F : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    Real.sqrt (b-t)*|F t x| ≤ weightedSize F a b :=
  le_csSup (weightedValues_bddAbove hC) ⟨t,ht,x,rfl⟩

lemma weightedSize_nonneg {F : ℝ → ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) : 0 ≤ weightedSize F a b := by
  have h := weighted_le_size hC (t := b) ⟨hab,le_rfl⟩ 0
  simpa using h

lemma abs_le_weightedSize {F : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) {t : ℝ} (ht : t ∈ Ico a b) (x : ℝ) :
    |F t x| ≤ weightedSize F a b/Real.sqrt (b-t) := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (sub_pos.mpr ht.2))).mpr
  simpa only [mul_comm] using weighted_le_size hC ⟨ht.1,ht.2.le⟩ x

lemma weightedSize_le {F : ℝ → ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hK : ∀ t ∈ Icc a b, ∀ x, Real.sqrt (b-t)*|F t x| ≤ K) :
    weightedSize F a b ≤ K := by
  apply csSup_le (weightedValues_nonempty F hab)
  rintro _ ⟨t,ht,x,rfl⟩
  exact hK t ht x

lemma weighted_absorption {F : ℝ → ℝ → ℝ} {a b C K ε : ℝ} (hab : a < b)
    (hC : ∀ t ∈ Icc a b, ∀ x, |F t x| ≤ C) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hsmall : ε*Real.sqrt (b-a) ≤ 1/2)
    (hineq : ∀ t ∈ Ico a b, ∀ x,
      Real.sqrt (b-t)*|F t x| ≤ K+ε*Real.sqrt (b-t)*weightedSize F a b) :
    weightedSize F a b ≤ 2*K := by
  have hM := weightedSize_nonneg hab.le hC
  have hsup : weightedSize F a b ≤ K+ε*Real.sqrt (b-a)*weightedSize F a b := by
    apply weightedSize_le hab.le
    intro t ht x
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · apply (hineq t ⟨ht.1,htb⟩ x).trans
      gcongr
      linarith [ht.1]
    · simp only [sub_self,Real.sqrt_zero,zero_mul]
      positivity
  nlinarith [mul_le_mul_of_nonneg_right hsmall hM]

end ZeroTemperatureSK.Smoothing

end
end
end
end
end

end OAI
