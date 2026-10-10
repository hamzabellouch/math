import OAI.Analysis.RotationWeights.FourierSampling

namespace OAI

noncomputable section

namespace CircleSampling

universe uE

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

abbrev CircleX := AddCircle (1 : ℝ)

instance : IsProbabilityMeasure (volume : Measure CircleX) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num
  infer_instance

lemma volume_singleton_zero (s : CircleX) : volume ({s} : Set CircleX) = 0 := by
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

def repr (x : CircleX) : ℝ := (AddCircle.measurableEquivIco 1 0 x).val
lemma measurable_repr : Measurable repr :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
lemma repr_mem (x : CircleX) : repr x ∈ Ico 0 1 := by
  simpa only [repr, zero_add] using (AddCircle.measurableEquivIco 1 0 x).property
lemma repr_coe {s : ℝ} (hs : s ∈ Ico 0 1) : repr (s : CircleX) = s := by
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa using hs))
lemma coe_repr (x : CircleX) : (repr x : CircleX) = x :=
  AddCircle.coe_equivIco

lemma integral_repr {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ x : CircleX, f (repr x) = ∫ s in Ioc 0 1, f s := by
  rw [← AddCircle.integral_preimage (1 : ℝ) 0]
  simp only [zero_add]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ s : ℝ, s ≠ 1 from by simp [ae_iff])] with s hs hne
  rw [repr_coe ⟨le_of_lt hs.1, lt_of_le_of_ne hs.2 hne⟩]

def delta (s : ℝ) : ℝ := min s (1-s)
def weight (ℓ α s t : ℝ) : ℝ :=
  if α ≤ delta s ∧ 0 < t ∧ t < ℓ * delta s then 1 / (ℓ * delta s) else 0
def uPos (ℓ α : ℝ) (s t : CircleX) : ℝ := weight ℓ α (repr s) (repr t)
def uNeg (ℓ α : ℝ) (s t : CircleX) : ℝ := uPos ℓ α (s-t) t

lemma measurable_delta : Measurable delta := by unfold delta; fun_prop
lemma measurable_weight (ℓ α : ℝ) : Measurable (fun z : ℝ × ℝ ↦ weight ℓ α z.1 z.2) := by
  unfold weight
  exact Measurable.ite ((measurableSet_le measurable_const (measurable_delta.comp measurable_fst)).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.mul (measurable_delta.comp measurable_fst)))))
    (measurable_const.div (measurable_const.mul (measurable_delta.comp measurable_fst))) measurable_const
lemma measurable_uPos (ℓ α : ℝ) : Measurable (Function.uncurry (uPos ℓ α)) :=
  (measurable_weight ℓ α).comp ((measurable_repr.comp measurable_fst).prodMk
    (measurable_repr.comp measurable_snd))
lemma measurable_uNeg (ℓ α : ℝ) : Measurable (Function.uncurry (uNeg ℓ α)) :=
  (measurable_uPos ℓ α).comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)

lemma weight_bounds {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (s t : ℝ) :
    0 ≤ weight ℓ α s t ∧ weight ℓ α s t ≤ 1 / (ℓ * α) := by
  unfold weight
  split_ifs with h
  · have hd : 0 < ℓ * delta s := mul_pos hℓ (lt_of_lt_of_le hα h.1)
    exact ⟨le_of_lt (one_div_pos.mpr hd),
      one_div_le_one_div_of_le (mul_pos hℓ hα) (mul_le_mul_of_nonneg_left h.1 hℓ.le)⟩
  · exact ⟨le_rfl, (one_div_pos.mpr (mul_pos hℓ hα)).le⟩

lemma delta_lipschitz (s t : ℝ) : |delta s - delta t| ≤ |s-t| := by
  rw [abs_le]
  have h1 := le_abs_self (s-t)
  have h2 := neg_abs_le (s-t)
  unfold delta
  simp only [min_def]
  split_ifs <;> constructor <;> linarith
lemma delta_pos {s : ℝ} (hs : s ∈ Ioo 0 1) : 0 < delta s := by
  exact lt_min hs.1 (sub_pos.mpr hs.2)
lemma delta_le_half (s : ℝ) : delta s ≤ 1/2 := by
  unfold delta
  rcases le_total s (1/2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

lemma weight_integral_t {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α) :
    (∫ t in Ioc 0 1, weight ℓ α s t) = if α ≤ delta s then 1 else 0 := by
  by_cases h : α ≤ delta s
  · have hd : 0 < ℓ * delta s := mul_pos hℓ (lt_of_lt_of_le hα h)
    have hd1 : ℓ * delta s < 1 := by
      have := delta_le_half s
      nlinarith
    have he : (fun t ↦ weight ℓ α s t) = (Ioo 0 (ℓ * delta s)).indicator
        (fun _ ↦ 1 / (ℓ * delta s)) := by
      ext t
      simp only [weight, h, true_and, indicator, mem_Ioo]
    rw [he, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
    have hs : Ioo 0 (ℓ * delta s) ∩ Ioc 0 1 = Ioo 0 (ℓ * delta s) := by
      apply inter_eq_left.mpr
      intro t ht
      exact ⟨ht.1, le_of_lt (lt_trans ht.2 hd1)⟩
    rw [hs, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal hd.le, smul_eq_mul, ite_eq_left h]
    exact mul_one_div_cancel hd.ne'
  · simp [weight, h]

lemma uPos_integral_t {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α)
    (s : CircleX) : (∫ t, uPos ℓ α s t) = if α ≤ delta (repr s) then 1 else 0 := by
  change (∫ t : CircleX, weight ℓ α (repr s) (repr t)) = _
  rw [integral_repr]
  exact weight_integral_t hℓ hℓ1 hα

lemma integral_uPos {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, uPos ℓ α s t) = 1 - 2 * α := by
  simp_rw [uPos_integral_t hℓ hℓ1 hα]
  change (∫ s : CircleX, (fun r ↦ if α ≤ delta r then (1 : ℝ) else 0) (repr s)) = _
  rw [integral_repr (fun r : ℝ ↦ if α ≤ delta r then (1 : ℝ) else 0)]
  have he : (fun s : ℝ ↦ if α ≤ delta s then (1 : ℝ) else 0) = (Icc α (1-α)).indicator (fun _ ↦ 1) := by
    ext s
    simp [delta, indicator, mem_Icc, le_sub_comm]
  rw [he, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc α (1-α) ∩ Ioc 0 1 = Icc α (1-α) := by
    apply inter_eq_left.mpr
    intro s hs
    exact ⟨lt_of_lt_of_le hα hs.1, le_trans hs.2 (by linarith)⟩
  rw [hs, integral_const]
  simp [Measure.real, Real.volume_Icc, show 0 ≤ (1-α)-α by linarith]
  ring

lemma integrable_uPos {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) :
    Integrable (Function.uncurry (uPos ℓ α)) (volume.prod volume) := by
  apply Integrable.of_bound (measurable_uPos ℓ α).aestronglyMeasurable (1 / (ℓ * α))
  filter_upwards [] with z
  rcases weight_bounds hℓ hα (repr z.1) (repr z.2) with ⟨h0, hB⟩
  simpa only [Function.uncurry, uPos, Real.norm_eq_abs, abs_of_nonneg h0] using hB

lemma integrable_uNeg {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) :
    Integrable (Function.uncurry (uNeg ℓ α)) (volume.prod volume) := by
  apply Integrable.of_bound (measurable_uNeg ℓ α).aestronglyMeasurable (1 / (ℓ * α))
  filter_upwards [] with z
  rcases weight_bounds hℓ hα (repr (z.1-z.2)) (repr z.2) with ⟨h0, hB⟩
  simpa only [Function.uncurry, uNeg, uPos, Real.norm_eq_abs, abs_of_nonneg h0] using hB

lemma integral_uNeg {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, uNeg ℓ α s t) = 1 - 2 * α := by
  rw [integral_integral_swap (integrable_uNeg hℓ hα)]
  have he (t : CircleX) : (∫ s : CircleX, uNeg ℓ α s t) = ∫ s : CircleX, uPos ℓ α s t :=
    integral_sub_right_eq_self (fun s ↦ uPos ℓ α s t) t
  simp_rw [he]
  rw [← integral_integral_swap (integrable_uPos hℓ hα)]
  exact integral_uPos hℓ hℓ1 hα hα2

lemma weight_sq_integral_t {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α) :
    (∫ t in Ioc 0 1, (weight ℓ α s t)^2) =
      if α ≤ delta s then 1 / (ℓ * delta s) else 0 := by
  have he : (fun t ↦ (weight ℓ α s t)^2) =
      (fun t ↦ (1 / (ℓ * delta s)) * weight ℓ α s t) := by
    ext t
    unfold weight
    split_ifs <;> ring
  rw [he, integral_const_mul, weight_integral_t hℓ hℓ1 hα]
  split_ifs <;> simp

lemma integral_inv_delta {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s in Icc α (1-α), 1 / (ℓ * delta s)) =
      (2 / ℓ) * Real.log (1 / (2*α)) := by
  have hab : α ≤ 1-α := by linarith
  have hc : ContinuousOn (fun s : ℝ ↦ 1 / (ℓ * delta s)) (Icc α (1-α)) := by
    apply continuousOn_const.div (continuousOn_const.mul ((continuous_id.min (continuous_const.sub continuous_id)).continuousOn))
    intro s hs
    change ℓ * min s (1-s) ≠ 0
    exact ne_of_gt (mul_pos hℓ (lt_min (lt_of_lt_of_le hα hs.1) (by linarith [hs.2])))
  have hi : IntervalIntegrable (fun s : ℝ ↦ 1 / (ℓ * delta s)) volume α (1-α) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hc.integrableOn_Icc
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hi.mono_set (by rw [uIcc_of_le hα2, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl (by linarith)))
      (hi.mono_set (by rw [uIcc_of_le (by linarith : (1:ℝ)/2 ≤ 1-α), uIcc_of_le hab]; exact Icc_subset_Icc hα2 le_rfl))]
  have he1 : (∫ s in α..(1:ℝ)/2, 1 / (ℓ * delta s)) =
      (1/ℓ) * (∫ s in α..(1:ℝ)/2, 1/s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hα2] at hs
    simp only [delta, min_eq_left (by linarith [hs.2] : s ≤ 1-s)]
    simp [one_div, mul_inv_rev, mul_comm]
  have he2 : (∫ s in (1:ℝ)/2..1-α, 1 / (ℓ * delta s)) =
      (1/ℓ) * (∫ s in α..(1:ℝ)/2, 1/s) := by
    calc
      _ = ∫ s in (1:ℝ)/2..1-α, (1/ℓ) * (1/(1-s)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : (1:ℝ)/2 ≤ 1-α)] at hs
        simp only [delta, min_eq_right (by linarith [hs.1] : 1-s ≤ s)]
        simp [one_div, mul_inv_rev, mul_comm]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
        congr 2 <;> ring
  rw [he1, he2, integral_one_div_of_pos hα (by norm_num)]
  rw [show (1:ℝ)/2/α = 1/(2*α) by ring]
  ring

lemma integral_uPos_sq {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, (uPos ℓ α s t)^2) =
      (2 / ℓ) * Real.log (1 / (2*α)) := by
  simp_rw [uPos]
  have he (s : ℝ) : (∫ t : CircleX, (weight ℓ α s (repr t))^2) =
      if α ≤ delta s then 1/(ℓ*delta s) else 0 := by
    rw [integral_repr (fun t ↦ (weight ℓ α s t)^2), weight_sq_integral_t hℓ hℓ1 hα]
  simp_rw [he]
  rw [integral_repr (fun s : ℝ ↦ if α ≤ delta s then 1/(ℓ*delta s) else 0)]
  have hf : (fun s : ℝ ↦ if α ≤ delta s then 1/(ℓ*delta s) else 0) =
      (Icc α (1-α)).indicator (fun s ↦ 1/(ℓ*delta s)) := by
    ext s
    simp [delta, indicator, mem_Icc, le_sub_comm]
  rw [hf, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (show Icc α (1-α) ⊆ Ioc 0 1 from fun s hs ↦
      ⟨lt_of_lt_of_le hα hs.1, le_trans hs.2 (by linarith)⟩)]
  exact integral_inv_delta hℓ hα hα2

lemma integral_uNeg_sq {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, ∫ t : CircleX, (uNeg ℓ α s t)^2) =
      (2 / ℓ) * Real.log (1 / (2*α)) := by
  have hip : Integrable (fun z : CircleX × CircleX ↦ (uPos ℓ α z.1 z.2)^2) (volume.prod volume) := by
    apply Integrable.of_bound ((measurable_uPos ℓ α).pow_const 2).aestronglyMeasurable ((1/(ℓ*α))^2)
    exact ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (weight_bounds hℓ hα _ _).1 (weight_bounds hℓ hα _ _).2 2
  have hin : Integrable (fun z : CircleX × CircleX ↦ (uNeg ℓ α z.1 z.2)^2) (volume.prod volume) := by
    apply Integrable.of_bound ((measurable_uNeg ℓ α).pow_const 2).aestronglyMeasurable ((1/(ℓ*α))^2)
    exact ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (weight_bounds hℓ hα _ _).1 (weight_bounds hℓ hα _ _).2 2
  rw [integral_integral_swap hin]
  have he (t : CircleX) : (∫ s : CircleX, (uNeg ℓ α s t)^2) = ∫ s : CircleX, (uPos ℓ α s t)^2 :=
    integral_sub_right_eq_self (fun s ↦ (uPos ℓ α s t)^2) t
  simp_rw [he]
  rw [← integral_integral_swap hip]
  exact integral_uPos_sq hℓ hℓ1 hα hα2

lemma uNeg_unwrapped {ℓ α a b : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α)
    (ha : a ∈ Ico 0 1) (hb : b ∈ Ico 0 1) :
    uNeg ℓ α (a : CircleX) (b : CircleX) = weight ℓ α (a-b) b := by
  unfold uNeg uPos
  rw [repr_coe hb, ← AddCircle.coe_sub]
  by_cases hba : b ≤ a
  · rw [repr_coe ⟨sub_nonneg.mpr hba, by linarith [ha.2, hb.1]⟩]
  · have hab : a < b := lt_of_not_ge hba
    have hr : repr ((a-b : ℝ) : CircleX) = a-b+1 := by
      rw [← AddCircle.coe_add_period 1 (a-b), repr_coe ⟨by linarith [ha.1, hb.2], by linarith⟩]
    rw [hr]
    have hn1 : ¬(α ≤ delta (a-b) ∧ 0 < b ∧ b < ℓ * delta (a-b)) := by
      intro h
      have := min_le_left (a-b) (1-(a-b))
      change delta (a-b) ≤ a-b at this
      linarith [h.1]
    have hn2 : ¬(α ≤ delta (a-b+1) ∧ 0 < b ∧ b < ℓ * delta (a-b+1)) := by
      intro h
      have hd : delta (a-b+1) ≤ b-a := by
        exact (min_le_right _ _).trans_eq (by ring)
      have := mul_le_mul_of_nonneg_left hd hℓ.le
      have := mul_le_mul_of_nonneg_left (show b-a ≤ b by linarith [ha.1]) hℓ.le
      nlinarith [h.2.1, h.2.2]
    simp only [weight, ite_eq_right hn1, ite_eq_right hn2]

lemma uNeg_integral_real {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hα : 0 < α)
    (s : CircleX) : (∫ t : CircleX, uNeg ℓ α s t) =
      ∫ t in Ioc 0 1, weight ℓ α (repr s-t) t := by
  rw [← AddCircle.integral_preimage (1 : ℝ) 0]
  simp only [zero_add]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ t : ℝ, t ≠ 1 from by simp [ae_iff])] with t ht hne
  nth_rw 1 [← coe_repr s]
  exact uNeg_unwrapped hℓ hℓ1 hα (repr_mem s) ⟨le_of_lt ht.1, lt_of_le_of_ne ht.2 hne⟩

lemma negative_weight_upper {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) (t : ℝ) :
    weight ℓ α (s-t) t ≤ (Ioo 0 (ℓ * delta s / (1-ℓ))).indicator
      (fun _ ↦ (1+ℓ) / (ℓ * delta s)) t := by
  unfold weight
  split_ifs with h
  · have hd : 0 < delta (s-t) := lt_of_lt_of_le hα h.1
    have hlip := delta_lipschitz s (s-t)
    rw [show s-(s-t)=t by ring, abs_of_pos h.2.1, abs_le] at hlip
    have ht : t < ℓ * delta s / (1-ℓ) := by
      apply (lt_div_iff₀ (sub_pos.mpr hℓ1)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hlip.1 hℓ.le, h.2.2]
    rw [indicator_of_mem (show t ∈ Ioo 0 (ℓ * delta s / (1-ℓ)) from ⟨h.2.1, ht⟩)]
    apply (div_le_div_iff₀ (mul_pos hℓ hd) (mul_pos hℓ hs)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlip.2 hℓ.le,
      mul_lt_mul_of_pos_left h.2.2 hℓ]
  · apply indicator_nonneg
    intro _ _
    exact div_nonneg (by linarith) (mul_nonneg hℓ.le hs.le)

lemma negative_weight_lower {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) (hcut : (1+ℓ)*α ≤ delta s) (t : ℝ) :
    (Ioo 0 (ℓ * delta s / (1+ℓ))).indicator
      (fun _ ↦ (1-ℓ) / (ℓ * delta s)) t ≤ weight ℓ α (s-t) t := by
  by_cases ht : t ∈ Ioo 0 (ℓ * delta s / (1+ℓ))
  · rw [indicator_of_mem ht]
    have hb : t * (1+ℓ) < ℓ * delta s := (lt_div_iff₀ (by linarith : 0 < 1+ℓ)).mp ht.2
    have hlip := delta_lipschitz s (s-t)
    rw [show s-(s-t)=t by ring, abs_of_pos ht.1, abs_le] at hlip
    have hct : α ≤ delta (s-t) := by nlinarith
    have hd : 0 < delta (s-t) := lt_of_lt_of_le hα hct
    have hsup : t < ℓ * delta (s-t) := by nlinarith
    rw [weight, ite_eq_left ⟨hct, ht.1, hsup⟩]
    apply (div_le_div_iff₀ (mul_pos hℓ hs) (mul_pos hℓ hd)).mpr
    have hbound : (1-ℓ)*delta (s-t) ≤ delta s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hbound hℓ.le]
  · rw [indicator_of_notMem ht]
    exact (weight_bounds hℓ hα _ _).1

lemma integrable_negative_weight {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (s : ℝ) :
    IntegrableOn (fun t ↦ weight ℓ α (s-t) t) (Ioc 0 1) := by
  apply Integrable.of_bound ((measurable_weight ℓ α).comp
    ((measurable_const.sub measurable_id).prodMk measurable_id)).aestronglyMeasurable (1/(ℓ*α))
  exact ae_of_all _ fun t ↦ by
    change ‖weight ℓ α (s-t) t‖ ≤ 1/(ℓ*α)
    rw [Real.norm_eq_abs, abs_of_nonneg (weight_bounds hℓ hα _ _).1]
    exact (weight_bounds hℓ hα _ _).2

lemma negative_density_upper {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) :
    (∫ t in Ioc 0 1, weight ℓ α (s-t) t) ≤ (1+ℓ)/(1-ℓ) := by
  let R := ℓ * delta s / (1-ℓ)
  let C := (1+ℓ)/(ℓ*delta s)
  have hR : 0 < R := div_pos (mul_pos hℓ hs) (sub_pos.mpr hℓ1)
  have hC : 0 ≤ C := div_nonneg (by linarith) (mul_nonneg hℓ.le hs.le)
  have hi : Integrable ((Ioo 0 R).indicator (fun _ : ℝ ↦ C)) :=
    (integrableOn_const (μ := volume) (s := Ioo 0 R) (C := C) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioo
  calc
    _ ≤ ∫ t in Ioc 0 1, (Ioo 0 R).indicator (fun _ : ℝ ↦ C) t :=
      integral_mono (integrable_negative_weight hℓ hα s) hi.restrict
        (negative_weight_upper hℓ hℓ1 hα hs)
    _ ≤ ∫ t : ℝ, (Ioo 0 R).indicator (fun _ : ℝ ↦ C) t :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (indicator_nonneg fun _ _ ↦ hC)) hi
    _ = _ := by
      rw [integral_indicator measurableSet_Ioo, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        ENNReal.toReal_ofReal hR.le, smul_eq_mul]
      dsimp [R, C]
      field_simp

lemma negative_density_lower {ℓ α s : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hs : 0 < delta s) (hcut : (1+ℓ)*α ≤ delta s) :
    (1-ℓ)/(1+ℓ) ≤ ∫ t in Ioc 0 1, weight ℓ α (s-t) t := by
  let R := ℓ * delta s / (1+ℓ)
  let C := (1-ℓ)/(ℓ*delta s)
  have hR : 0 < R := div_pos (mul_pos hℓ hs) (by linarith)
  have hR1 : R ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1+ℓ)).mpr
    nlinarith [delta_le_half s]
  have hi : Integrable ((Ioo 0 R).indicator (fun _ : ℝ ↦ C)) :=
    (integrableOn_const (μ := volume) (s := Ioo 0 R) (C := C) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioo
  calc
    _ = ∫ t in Ioc 0 1, (Ioo 0 R).indicator (fun _ : ℝ ↦ C) t := by
      rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
        inter_eq_left.mpr (show Ioo 0 R ⊆ Ioc 0 1 from fun _ ht ↦ ⟨ht.1, ht.2.le.trans hR1⟩),
        integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        ENNReal.toReal_ofReal hR.le, smul_eq_mul]
      dsimp [R, C]
      field_simp
    _ ≤ _ := integral_mono hi.restrict (integrable_negative_weight hℓ hα s)
      (negative_weight_lower hℓ hℓ1 hα hs hcut)

lemma integral_delta_small {r : ℝ} (hr : 0 < r) :
    (∫ s : CircleX, if delta (repr s) < r then (1 : ℝ) else 0) ≤ 2*r := by
  have hm : Measurable (fun s : CircleX ↦ if delta (repr s) < r then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt (measurable_delta.comp measurable_repr) measurable_const)
      measurable_const measurable_const
  have hm' : Measurable (fun s : CircleX ↦ if r ≤ delta (repr s) then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_delta.comp measurable_repr))
      measurable_const measurable_const
  have hi' : Integrable (fun s : CircleX ↦ if r ≤ delta (repr s) then (1 : ℝ) else 0) := by
    apply Integrable.of_bound hm'.aestronglyMeasurable 1
    exact ae_of_all _ fun s ↦ by split_ifs <;> norm_num
  by_cases hr2 : r ≤ 1/2
  · have he := integral_uPos (ℓ := 1/2) (α := r) (by norm_num) (by norm_num) hr hr2
    simp_rw [uPos_integral_t (ℓ := 1/2) (α := r) (by norm_num) (by norm_num) hr] at he
    have hf : (fun s : CircleX ↦ if delta (repr s) < r then (1 : ℝ) else 0) =
        (fun s ↦ 1 - (if r ≤ delta (repr s) then (1 : ℝ) else 0)) := by
      funext s
      by_cases h : r ≤ delta (repr s) <;> simp [h, not_lt_of_ge, lt_of_not_ge]
    rw [hf, integral_sub (integrable_const 1) hi', he]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    linarith
  · have hi : Integrable (fun s : CircleX ↦ if delta (repr s) < r then (1 : ℝ) else 0) := by
      apply Integrable.of_bound hm.aestronglyMeasurable 1
      exact ae_of_all _ fun s ↦ by split_ifs <;> norm_num
    have hu := integral_mono hi (integrable_const (1 : ℝ)) (fun s ↦ by split_ifs <;> norm_num)
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hu
    linarith

lemma uNeg_mean_bounds {ℓ α : ℝ} (hℓ : 0 < ℓ) (hα : 0 < α) (s : CircleX) :
    0 ≤ (∫ t : CircleX, uNeg ℓ α s t) ∧
      (∫ t : CircleX, uNeg ℓ α s t) ≤ 1/(ℓ*α) := by
  have hm : Measurable (fun t ↦ uNeg ℓ α s t) :=
    (measurable_uNeg ℓ α).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun t ↦ uNeg ℓ α s t) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (1/(ℓ*α))
    exact ae_of_all _ fun t ↦ by
      change ‖weight ℓ α (repr (s-t)) (repr t)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_bounds hℓ hα _ _).1]
      exact (weight_bounds hℓ hα _ _).2
  refine ⟨integral_nonneg (fun t ↦ (weight_bounds hℓ hα _ _).1), ?_⟩
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] using
    integral_mono hi (integrable_const (1/(ℓ*α))) (fun t ↦ (weight_bounds hℓ hα _ _).2)

lemma integral_uNeg_mean_sq {ℓ α : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1)
    (hα : 0 < α) (hα2 : α ≤ 1/2) :
    (∫ s : CircleX, (∫ t : CircleX, uNeg ℓ α s t)^2) ≤
      1 + (2*ℓ/(1-ℓ))^2 + 2*(1+ℓ)*α := by
  let g : CircleX → ℝ := fun s ↦ ∫ t : CircleX, uNeg ℓ α s t
  let C : ℝ := 2*ℓ/(1-ℓ)
  let r : ℝ := (1+ℓ)*α
  let b : CircleX → ℝ := fun s ↦ if delta (repr s) < r then 1 else 0
  have hC : 0 ≤ C := div_nonneg (by positivity) (by linarith)
  have hr : 0 < r := mul_pos (by linarith) hα
  have hgi : Integrable g := (integrable_uNeg hℓ hα).integral_prod_left
  have hgb (s : CircleX) := uNeg_mean_bounds hℓ hα s
  have hgs : Integrable (fun s ↦ (g s)^2) := by
    apply Integrable.of_bound (hgi.aestronglyMeasurable.pow 2) ((1/(ℓ*α))^2)
    exact ae_of_all _ fun s ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hgb s).1 (hgb s).2 2
  have hbi : Integrable b := by
    have hm : Measurable b := Measurable.ite
      (measurableSet_lt (measurable_delta.comp measurable_repr) measurable_const)
      measurable_const measurable_const
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact ae_of_all _ fun s ↦ by dsimp [b]; split_ifs <;> norm_num
  have hv : (fun s ↦ (g s-1)^2) = (fun s ↦ (g s)^2 - 2*g s + 1) := by
    funext s; ring
  have hvi : Integrable (fun s ↦ (g s-1)^2) := by
    rw [hv]
    exact (hgs.sub (hgi.const_mul 2)).add (integrable_const 1)
  have hbound : ∀ᵐ s : CircleX, (g s-1)^2 ≤ C^2 + b s := by
    filter_upwards [show ∀ᵐ s : CircleX, s ≠ 0 from by simpa [ae_iff] using volume_singleton_zero (0 : CircleX)] with s hs
    have hsp : 0 < repr s := by
      by_contra! h
      have hz : repr s = 0 := le_antisymm h (repr_mem s).1
      have := coe_repr s
      simp only [hz, AddCircle.coe_zero] at this
      exact hs this.symm
    have hd : 0 < delta (repr s) := delta_pos ⟨hsp, (repr_mem s).2⟩
    have hu := negative_density_upper hℓ hℓ1 hα hd
    rw [← uNeg_integral_real hℓ hℓ1 hα s] at hu
    change g s ≤ _ at hu
    have heU : (1+ℓ)/(1-ℓ) = 1+C := by dsimp [C]; field_simp [ne_of_gt (sub_pos.mpr hℓ1)]; ring
    rw [heU] at hu
    by_cases hb : delta (repr s) < r
    · simp only [b, ite_eq_left hb]
      rcases le_total (g s) 1 with hl | hl
      · nlinarith [(hgb s).1, sq_nonneg C]
      · nlinarith
    · simp only [b, ite_eq_right hb, add_zero]
      have hl := negative_density_lower hℓ hℓ1 hα hd (le_of_not_gt hb)
      rw [← uNeg_integral_real hℓ hℓ1 hα s] at hl
      change _ ≤ g s at hl
      have hL : 1-C ≤ (1-ℓ)/(1+ℓ) := by
        have hc : 2*ℓ/(1+ℓ) ≤ C := by
          exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        have he : (1-ℓ)/(1+ℓ) = 1 - 2*ℓ/(1+ℓ) := by
          field_simp [ne_of_gt (show 0 < 1+ℓ by linarith)]
          ring
        rw [he]
        linarith
      have hlo := hL.trans hl
      nlinarith [sq_nonneg (g s-1-C), sq_nonneg (g s-1+C)]
  have hive := integral_mono_ae hvi ((integrable_const (C^2)).add hbi) hbound
  change (∫ s : CircleX, (g s-1)^2) ≤ ∫ s : CircleX, C^2+b s at hive
  rw [integral_add (integrable_const (C^2)) hbi,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hive
  have hbmass : ∫ s : CircleX, b s ≤ 2*r := integral_delta_small hr
  have hgm : ∫ s : CircleX, g s = 1-2*α := integral_uNeg hℓ hℓ1 hα hα2
  rw [hv] at hive
  rw [integral_add (show Integrable (fun s : CircleX ↦ (g s)^2 - 2*g s) volume from
      hgs.sub (hgi.const_mul 2)) (integrable_const 1),
    integral_sub hgs (hgi.const_mul 2), integral_const_mul, hgm,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hive
  change (∫ s : CircleX, (g s)^2) ≤ _
  dsimp [C, r] at hive hbmass
  linarith



end CircleSampling

end

end OAI
