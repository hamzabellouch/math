import Mathlib
import OAI.Geometry.BallPacking.Holder.KernelSchauder

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Filter MeasureTheory
local instance : NormedAddCommGroup (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace

structure SchauderSplit (K : ℂ → ℂ) (r A B : ℝ) where
  near : ℂ → ℂ
  far : ℂ → ℂ
  smooth_near : ContDiff ℝ ∞ near
  smooth_far : ContDiff ℝ ∞ far
  compact_near : HasCompactSupport near
  compact_far : HasCompactSupport far
  sum_eq : ∀ w, K w = near w + far w
  support_near : tsupport near ⊆ Metric.closedBall (0:ℂ) (2*r)
  support_far : ∀ w, ‖w‖ ≤ r → w ∉ tsupport far
  bound_near : ∀ w, w ≠ 0 → ‖fderiv ℝ near w‖ ≤ A / ‖w‖^2
  bound_far : ∀ w, w ≠ 0 → ‖iteratedFDeriv ℝ 2 far w‖ ≤ B / ‖w‖^3

lemma norm_second_const_sub {b : ℂ → ℝ} (w : ℂ) :
    ‖iteratedFDeriv ℝ 2 (fun z => 1-b z) w‖ = ‖iteratedFDeriv ℝ 2 b w‖ := by
  rw [norm_second_jet]
  have he : fderiv ℝ (fun z => 1-b z) = fun z => -fderiv ℝ b z := funext fun z => fderiv_const_sub 1
  rw [he, fderiv_fun_neg]
  exact (norm_neg (fderiv ℝ (fderiv ℝ b) w)).trans (norm_second_jet b w).symm

lemma first_near_bound {K : ℂ → ℂ} {b : ℂ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hb : ContDiff ℝ ∞ b) {M C₁ : ℝ} (hM : 0 ≤ M) (_hC₁ : 0 ≤ C₁)
    {w : ℂ} (hw : w ≠ 0) (hbn : ‖b w‖ ≤ 1)
    (hb1 : ‖fderiv ℝ b w‖ ≤ 2*M/‖w‖)
    (hK0 : ‖K w‖ ≤ ‖w‖⁻¹) (hK1 : ‖fderiv ℝ K w‖ ≤ C₁/‖w‖^2) :
    ‖fderiv ℝ (fun z => b z • K z) w‖ ≤ (C₁+2*M)/‖w‖^2 := by
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  calc
    _ ≤ ‖b w‖*‖fderiv ℝ K w‖ + ‖fderiv ℝ b w‖*‖K w‖ := norm_first_smul_le hb hK w
    _ ≤ 1*(C₁/‖w‖^2) + (2*M/‖w‖)*‖w‖⁻¹ := by
      exact add_le_add (mul_le_mul hbn hK1 (norm_nonneg _) zero_le_one)
        (mul_le_mul hb1 hK0 (norm_nonneg _) (by positivity))
    _ = _ := by field_simp

lemma second_far_bound {K : ℂ → ℂ} {b : ℂ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hb : ContDiff ℝ ∞ b) {M C₁ C₂ : ℝ} (hM : 0 ≤ M) (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    {w : ℂ} (hw : w ≠ 0) (hbn : ‖1-b w‖ ≤ 1)
    (hb1 : ‖fderiv ℝ b w‖ ≤ 2*M/‖w‖)
    (hb2 : ‖iteratedFDeriv ℝ 2 b w‖ ≤ 4*M/‖w‖^2)
    (hK0 : ‖K w‖ ≤ ‖w‖⁻¹) (hK1 : ‖fderiv ℝ K w‖ ≤ C₁/‖w‖^2)
    (hK2 : ‖iteratedFDeriv ℝ 2 K w‖ ≤ C₂/‖w‖^3) :
    ‖iteratedFDeriv ℝ 2 (fun z => (1-b z) • K z) w‖ ≤
      (C₂+4*M*C₁+4*M)/‖w‖^3 := by
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  calc
    _ ≤ ‖1-b w‖*‖iteratedFDeriv ℝ 2 K w‖ +
        2*‖fderiv ℝ (fun z => 1-b z) w‖*‖fderiv ℝ K w‖ +
        ‖iteratedFDeriv ℝ 2 (fun z => 1-b z) w‖*‖K w‖ :=
      norm_second_smul_le (contDiff_const.sub hb) hK w
    _ = ‖1-b w‖*‖iteratedFDeriv ℝ 2 K w‖ +
        2*‖fderiv ℝ b w‖*‖fderiv ℝ K w‖ + ‖iteratedFDeriv ℝ 2 b w‖*‖K w‖ := by
      rw [fderiv_const_sub, norm_neg, norm_second_const_sub]
    _ ≤ 1*(C₂/‖w‖^3) + 2*(2*M/‖w‖)*(C₁/‖w‖^2) + (4*M/‖w‖^2)*‖w‖⁻¹ := by
      apply add_le_add _ (mul_le_mul hb2 hK0 (norm_nonneg _) (by positivity))
      exact add_le_add (mul_le_mul hbn hK2 (norm_nonneg _) zero_le_one)
        (mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by norm_num))
          hK1 (norm_nonneg _) (by positivity))
    _ = _ := by field_simp; ring

lemma schauderSplit_exists_uniform {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ K : ℂ → ℂ,
      ContDiff ℝ ∞ K → HasCompactSupport K →
      (∀ z, z ≠ 0 → ‖K z‖ ≤ ‖z‖⁻¹ ∧ ‖fderiv ℝ K z‖ ≤ C₁/‖z‖^2 ∧
        ‖iteratedFDeriv ℝ 2 K z‖ ≤ C₂/‖z‖^3) →
      ∀ r : ℝ, 0 < r → Nonempty (SchauderSplit K r A B) := by
  obtain ⟨M,hM,hMjet⟩ := scaledSchauderBump_homogeneous_bounds
  refine ⟨C₁+2*M, C₂+4*M*C₁+4*M, by positivity, by positivity, ?_⟩
  intro K hK hcK hjet r hr
  let b : ℂ → ℝ := scaledSchauderBump r
  have hb : ContDiff ℝ ∞ b := scaledSchauderBump_smooth r
  have hb0 (w : ℂ) : 0 ≤ b w := (scaledSchauderBump_range r w).1
  have hb1 (w : ℂ) : b w ≤ 1 := (scaledSchauderBump_range r w).2
  refine ⟨{
    near := fun w => b w • K w
    far := fun w => (1-b w) • K w
    smooth_near := hb.smul hK
    smooth_far := (contDiff_const.sub hb).smul hK
    compact_near := hcK.smul_left (f := b)
    compact_far := hcK.smul_left (f := fun w => (1:ℝ)-b w)
    sum_eq := fun w => by rw [← add_smul]; simp
    support_near := (tsupport_smul_subset_left b K).trans (scaledSchauderBump_tsupport hr)
    support_far := ?_
    bound_near := ?_
    bound_far := ?_ }⟩
  · intro w hw
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [scaledSchauderBump_eventually_one hr hw] with z hz
    simp only [b, hz, sub_self, zero_smul, Pi.zero_apply]
  · intro w hw
    apply first_near_bound hK hb hM hC₁ hw
    · rw [Real.norm_of_nonneg (hb0 w)]; exact hb1 w
    · exact (hMjet r hr w hw).1
    · exact (hjet w hw).1
    · exact (hjet w hw).2.1
  · intro w hw
    apply second_far_bound hK hb hM hC₁ hC₂ hw
    · rw [Real.norm_of_nonneg (sub_nonneg.mpr (hb1 w))]; linarith [hb0 w]
    · exact (hMjet r hr w hw).1
    · exact (hMjet r hr w hw).2
    · exact (hjet w hw).1
    · exact (hjet w hw).2.1
    · exact (hjet w hw).2.2

lemma cutoff_smoothCauchyKernel_splits (b : ContDiffBump (0:ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ δ : ℝ, 0 < δ → ∀ r : ℝ, 0 < r →
      Nonempty (SchauderSplit (fun w => b w • smoothCauchyKernel δ w) r A B) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hjet⟩ := cutoff_smoothCauchyKernel_jet_bounds b
  obtain ⟨A,B,hA,hB,h⟩ := schauderSplit_exists_uniform hC₁ hC₂
  refine ⟨A,B,hA,hB,fun δ hδ r hr => h _ (b.contDiff.smul (smoothCauchyKernel_smooth hδ))
    (b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)) (hjet δ hδ) r hr⟩


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma inv_sq_mul_third {t : ℝ} (ht : 0 < t) :
    (t^2)⁻¹*t^((1:ℝ)/3) = t^(-(5:ℝ)/3) := by
  rw [← Real.rpow_two, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  norm_num

lemma inv_cube_mul_third {t : ℝ} (ht : 0 < t) :
    (t^3)⁻¹*t^((1:ℝ)/3) = t^(-(8:ℝ)/3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  norm_num

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma SchauderSplit.near_weight_bound {K : ℂ → ℂ} {r A B H : ℝ}
    (s : SchauderSplit K r A B) (hr : 0 < r) (hA : 0 ≤ A) (hH : 0 ≤ H)
    {g : ℂ → E} (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x w v : ℂ) :
    ‖fderiv ℝ s.near w v‖*‖g (x-w)-g x‖ ≤
      (A*H*scaledSchauderWeight (-(5:ℝ)/3) schauderNearWeight r w)*‖v‖ := by
  rw [scaledNearWeight_value hr]
  by_cases hw2 : w ∈ Metric.closedBall (0:ℂ) (2*r)
  · rw [indicator_of_mem hw2]
    by_cases hw : w = 0
    · subst w
      simp only [sub_zero, sub_self, norm_zero, mul_zero]
      positivity
    have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hd : ‖fderiv ℝ s.near w v‖ ≤ (A/‖w‖^2)*‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (s.bound_near w hw) (norm_nonneg _))
    have hg' : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left, norm_neg] using hg (x-w) x
    calc
      _ ≤ ((A/‖w‖^2)*‖v‖)*(H*‖w‖^((1:ℝ)/3)) :=
        mul_le_mul hd hg' (norm_nonneg _) (by positivity)
      _ = A*H*((‖w‖^2)⁻¹*‖w‖^((1:ℝ)/3))*‖v‖ := by ring
      _ = _ := by rw [inv_sq_mul_third hp]
  · have ht : w ∉ tsupport s.near := fun h => hw2 (s.support_near h)
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) ht, zero_apply, norm_zero, zero_mul,
      indicator_of_notMem hw2, mul_zero, zero_mul]

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma SchauderSplit.far_weight_bound {K : ℂ → ℂ} {r A B H : ℝ}
    (s : SchauderSplit K r A B) (hr : 0 < r) (hB : 0 ≤ B) (_hH : 0 ≤ H)
    {g : ℂ → E} (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x w v t : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ s.far y v) w t‖*‖g (x-w)-g x‖ ≤
      (B*H*scaledSchauderWeight (-(8:ℝ)/3) schauderFarWeight r w)*‖v‖*‖t‖ := by
  rw [scaledFarWeight_value hr]
  by_cases hw2 : r < ‖w‖
  · rw [indicator_of_mem (show ‖w‖ ∈ Ioi r from hw2)]
    have hp : 0 < ‖w‖ := hr.trans hw2
    have hw : w ≠ 0 := norm_pos_iff.mp hp
    have hd : ‖fderiv ℝ (fun y => fderiv ℝ s.far y v) w t‖ ≤
        (B/‖w‖^3)*‖v‖*‖t‖ :=
      (second_directional_norm_le s.smooth_far w v t).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (s.bound_far w hw)
          (norm_nonneg _)) (norm_nonneg _))
    have hg' : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left, norm_neg] using hg (x-w) x
    calc
      _ ≤ ((B/‖w‖^3)*‖v‖*‖t‖)*(H*‖w‖^((1:ℝ)/3)) :=
        mul_le_mul hd hg' (norm_nonneg _) (by positivity)
      _ = B*H*((‖w‖^3)⁻¹*‖w‖^((1:ℝ)/3))*‖v‖*‖t‖ := by ring
      _ = _ := by rw [inv_cube_mul_third hp]
  · have ht : w ∉ tsupport s.far := s.support_far w (le_of_not_gt hw2)
    have hd2 : iteratedFDeriv ℝ 2 s.far w = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (tsupport_iteratedFDeriv_subset 2 h)
    have hd := second_directional_norm_le s.smooth_far w v t
    rw [hd2, norm_zero, zero_mul, zero_mul] at hd
    rw [indicator_of_notMem (show ‖w‖ ∉ Ioi r from hw2), mul_zero, zero_mul, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg hd (norm_nonneg _)

lemma SchauderSplit.holder_bound {K : ℂ → ℂ} {r A B H : ℝ}
    (s : SchauderSplit K r A B) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    {g : ℂ → E} (hgC : Continuous g)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) {x y : ℂ} (hxy : ‖x-y‖ = r) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      (2*A*(∫ w, schauderNearWeight w)+B*(∫ w, schauderFarWeight w))*H*r^((1:ℝ)/3) := by
  let WN := fun w => A*H*scaledSchauderWeight (-(5:ℝ)/3) schauderNearWeight r w
  let WF := fun w => B*H*scaledSchauderWeight (-(8:ℝ)/3) schauderFarWeight r w
  have hN : Integrable WN := (scaledSchauderWeight_integrable schauderNearWeight_integrable _ hr).const_mul _
  have hF : Integrable WF := (scaledSchauderWeight_integrable schauderFarWeight_integrable _ hr).const_mul _
  have hF0 (w : ℂ) : 0 ≤ WF w := by
    dsimp [WF, scaledSchauderWeight]
    exact mul_nonneg (mul_nonneg hB hH) (mul_nonneg (Real.rpow_nonneg hr.le _) (schauderFarWeight_nonneg _))
  have he := compact_convolution_split_derivative_bound s.smooth_near s.compact_near
    s.smooth_far s.compact_far s.sum_eq hgC hN hF hF0
    (s.near_weight_bound hr hA hH hg) (s.far_weight_bound hr hB hH hg) x y
  apply he.trans_eq
  simp only [WN, WF, integral_const_mul, integral_scaledSchauderWeight _ _ hr, hxy]
  have hpow : r^(-(8:ℝ)/3+2)*r = r^((1:ℝ)/3) := by
    calc
      _ = r^(-(8:ℝ)/3+2)*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hr]; norm_num
  have hpowN : r^(-(5:ℝ)/3+2) = r^((1:ℝ)/3) := by norm_num
  rw [hpowN]
  calc
    _ = (2*A*(∫ w, schauderNearWeight w))*H*r^((1:ℝ)/3) +
        (B*(∫ w, schauderFarWeight w))*H*(r^(-(8:ℝ)/3+2)*r) := by ring
    _ = _ := by rw [hpow]; ring

lemma cutoff_smoothCauchyKernel_full_schauder (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, Continuous g → ∀ H : ℝ, 0 ≤ H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) → ∀ δ : ℝ, 0 < δ → ∀ x y : ℂ,
      ‖fderiv ℝ (convolution (fun w => b w • smoothCauchyKernel δ w) g
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution (fun w => b w • smoothCauchyKernel δ w) g
          (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤ C*H*‖x-y‖^((1:ℝ)/3) := by
  obtain ⟨A,B,hA,hB,h⟩ := cutoff_smoothCauchyKernel_splits b
  refine ⟨2*A*(∫ w, schauderNearWeight w)+B*(∫ w, schauderFarWeight w), ?_, ?_⟩
  · have hN : 0 ≤ ∫ w, schauderNearWeight w := integral_nonneg schauderNearWeight_nonneg
    have hF : 0 ≤ ∫ w, schauderFarWeight w := integral_nonneg schauderFarWeight_nonneg
    positivity
  · intro g hgC H hH hg δ hδ x y
    by_cases hxy : x = y
    · subst y; simp only [sub_self, norm_zero,
        Real.zero_rpow (by norm_num : (1:ℝ)/3 ≠ 0), mul_zero, le_refl]
    · obtain ⟨s⟩ := h δ hδ ‖x-y‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
      exact s.holder_bound (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) hA hB hH hgC hg rfl


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

 def cauchySchauderWeight (R : ℝ) : ℂ → ℝ :=
  (Metric.closedBall (0:ℂ) R).indicator
    (fun z => ‖z‖^(-(2:ℝ)/3)+‖z‖^(-(5:ℝ)/3))

 theorem cauchy_holder_power_locallyIntegrable {α : ℝ} (hα : α<2) :
    LocallyIntegrable (fun z : ℂ => ‖z‖^(-α)) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := α) (by simp) (by simpa using hα)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),one_mul]
  · exact (measurable_norm.pow_const (-α)).aestronglyMeasurable

 theorem cauchySchauderWeight_integrable (R : ℝ) : Integrable (cauchySchauderWeight R) := by
  apply IntegrableOn.integrable_indicator
    (s := Metric.closedBall (0:ℂ) R) _ measurableSet_closedBall
  apply LocallyIntegrable.integrableOn_isCompact _ (isCompact_closedBall _ _)
  have h := (cauchy_holder_power_locallyIntegrable (α := (2:ℝ)/3) (by norm_num)).add
    (cauchy_holder_power_locallyIntegrable (α := (5:ℝ)/3) (by norm_num))
  convert h using 1
  funext z
  simp only [Pi.add_apply, neg_div]

 theorem cutoff_smoothCauchyKernel_bound (b : ContDiffBump (0:ℂ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → ∀ z v : ℂ, z≠0 →
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z v‖ ≤
        (C*‖z‖⁻¹+3/‖z‖^2)*‖v‖ := by
  have hbs : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:ℂ) b.rOut).exists_bound_of_continuousOn
    ((hbs.fderiv_right (m := ∞) (by simp)).continuous.continuousOn)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro δ hδ z v hz
  by_cases hzb : z ∈ Metric.closedBall (0:ℂ) b.rOut
  · have hDb : ‖fderiv ℝ b z v‖ ≤ max D 0*‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
        ((hD z hzb).trans (le_max_left _ _)) (norm_nonneg _))
    have hd := (hbs.differentiable (by simp) z).hasFDerivAt.smul
      ((smoothCauchyKernel_smooth hδ).differentiable (by simp) z).hasFDerivAt
    rw [show fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z = _ from hd.fderiv]
    simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
    calc
      _ ≤ |b z| *‖fderiv ℝ (smoothCauchyKernel δ) z v‖+
        ‖fderiv ℝ b z v‖*‖smoothCauchyKernel δ z‖ := by
        simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le
          (b z • fderiv ℝ (smoothCauchyKernel δ) z v)
          (fderiv ℝ b z v • smoothCauchyKernel δ z)
      _ ≤ 1*((3/‖z‖^2)*‖v‖)+(max D 0*‖v‖)*‖z‖⁻¹ := by
        exact add_le_add (mul_le_mul (by simpa only [abs_of_nonneg b.nonneg] using b.le_one)
          (smoothCauchyKernel_fderiv_norm hδ hz v) (norm_nonneg _) zero_le_one)
          (mul_le_mul hDb (smoothCauchyKernel_norm hδ z) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  · have ht : z ∉ tsupport (fun w => b w • smoothCauchyKernel δ w) := by
      intro hh
      apply hzb
      exact (b.tsupport_eq ▸ tsupport_smul_subset_left _ _ hh)
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) ht,zero_apply,norm_zero]
    positivity

 theorem cutoff_smoothCauchyKernel_schauder_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (b : ContDiffBump (0:ℂ)) {C : ℝ} (hC : 0≤C)
    (hCbound : ∀ δ : ℝ, 0<δ → ∀ z v : ℂ, z≠0 →
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z v‖ ≤
        (C*‖z‖⁻¹+3/‖z‖^2)*‖v‖)
    {g : ℂ → E} {H : ℝ} (hH : 0≤H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    {δ : ℝ} (hδ : 0<δ) (x w v : ℂ) :
    ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) w v‖*‖g (x-w)-g x‖ ≤
      ((C+3)*H*cauchySchauderWeight b.rOut w)*‖v‖ := by
  by_cases hwb : w ∈ Metric.closedBall (0:ℂ) b.rOut
  · rw [cauchySchauderWeight,indicator_of_mem hwb]
    by_cases hw : w=0
    · subst w
      simp only [sub_zero,sub_self,norm_zero,mul_zero]
      positivity
    have hp : 0<‖w‖ := norm_pos_iff.mpr hw
    have hh : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left,norm_neg] using hg (x-w) x
    have hb := mul_le_mul (hCbound δ hδ w v hw) hh (norm_nonneg _) (by positivity)
    have he1 : ‖w‖⁻¹*‖w‖^((1:ℝ)/3)=‖w‖^(-(2:ℝ)/3) := by
      rw [←Real.rpow_neg_one,←Real.rpow_add hp]
      norm_num
    have he2 : (‖w‖^2)⁻¹*‖w‖^((1:ℝ)/3)=‖w‖^(-(5:ℝ)/3) := by
      rw [←Real.rpow_two,←Real.rpow_neg (norm_nonneg w),←Real.rpow_add hp]
      norm_num
    calc
      _ ≤ _ := hb
      _ = (C*‖w‖^(-(2:ℝ)/3)+3*‖w‖^(-(5:ℝ)/3))*H*‖v‖ := by
        rw [show (C*‖w‖⁻¹+3/‖w‖^2)*‖v‖*(H*‖w‖^((1:ℝ)/3)) =
          (C*(‖w‖⁻¹*‖w‖^((1:ℝ)/3))+3*((‖w‖^2)⁻¹*‖w‖^((1:ℝ)/3)))*H*‖v‖ from by ring,
          he1,he2]
      _ ≤ _ := by
        have h1 := Real.rpow_nonneg (norm_nonneg w) (-(2:ℝ)/3)
        have h2 := Real.rpow_nonneg (norm_nonneg w) (-(5:ℝ)/3)
        have hb0 : C*‖w‖^(-(2:ℝ)/3)+3*‖w‖^(-(5:ℝ)/3) ≤
            (C+3)*(‖w‖^(-(2:ℝ)/3)+‖w‖^(-(5:ℝ)/3)) := by nlinarith
        have hh0 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb0 hH) (norm_nonneg v)
        convert hh0 using 1; first | rfl | ring
  · have ht : w ∉ tsupport (fun z => b z • smoothCauchyKernel δ z) := by
      intro hh
      exact hwb ((b.tsupport_eq ▸ tsupport_smul_subset_left _ _ hh))
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) ht,zero_apply,norm_zero,zero_mul,
      cauchySchauderWeight,indicator_of_notMem hwb,mul_zero,zero_mul]


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 theorem locallyIntegrable_complex_inv : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact ae_of_all _ fun z => by simp only [norm_inv,Real.rpow_neg_one,one_mul,le_refl]
  · exact measurable_inv.aestronglyMeasurable

 variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 def cauchyTransform (h : ℂ → E) : ℂ → E :=
  (Real.pi : ℂ)⁻¹ • convolution (fun z : ℂ => z⁻¹) h (ContinuousLinearMap.lsmul ℝ ℂ) volume

 theorem cauchyTransform_apply (h : ℂ → E) (z : ℂ) :
    cauchyTransform h z = (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • h (z-w) := rfl

 theorem cauchyTransform_smooth {h : ℂ → E} (hc : HasCompactSupport h) (hs : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (cauchyTransform h) := by
  exact (hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_complex_inv hs).const_smul _

 theorem cauchyTransform_hasFDerivAt {h : ℂ → E} (hc : HasCompactSupport h)
    (hs : ContDiff ℝ ∞ h) (z : ℂ) :
    HasFDerivAt (cauchyTransform h)
      ((Real.pi : ℂ)⁻¹ • convolution (fun w : ℂ => w⁻¹) (fderiv ℝ h)
        ((ContinuousLinearMap.lsmul ℝ ℂ).precompR ℂ) volume z) z := by
  exact (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_complex_inv (hs.of_le (by simp)) z).const_smul _


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem cutoff_smoothCauchyKernel_convolution_tendsto
    (b : ContDiffBump (0:ℂ)) {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Tendsto (fun δ : ℝ => convolution (fun w => b w • smoothCauchyKernel δ w)
      g (ContinuousLinearMap.lsmul ℝ ℂ) volume x) (𝓝[>] 0)
      (𝓝 (convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x)) := by
  have hv : Continuous (fun w : ℂ => b w • g (x-w)) :=
    b.continuous.smul (hg.comp (continuous_const.sub continuous_id))
  have hc : HasCompactSupport (fun w : ℂ => b w • g (x-w)) := b.hasCompactSupport.smul_right
  have hi := locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport hv hc
  apply tendsto_integral_filter_of_dominated_convergence
    (fun w : ℂ => ‖w⁻¹ • (b w • g (x-w))‖)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (((b.continuous.smul (smoothCauchyKernel_smooth hδ).continuous).smul
      (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply Eventually.of_forall
    intro w
    change ‖(b w • smoothCauchyKernel δ w) • g (x-w)‖ ≤ _
    simp only [norm_smul,norm_inv,Real.norm_eq_abs]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (smoothCauchyKernel_norm hδ w) (abs_nonneg (b w))) (norm_nonneg (g (x-w)))]
  · exact hi.norm
  · apply Eventually.of_forall
    intro w
    exact (tendsto_const_nhds.smul (smoothCauchyKernel_tendsto w)).smul tendsto_const_nhds

 theorem cutoff_cauchy_holder_lipschitz (b : ContDiffBump (0:ℂ)) :
    ∃ L : ℝ, 0≤L ∧ ∀ (g : ℂ → E), Continuous g → ∀ H : ℝ, 0≤H →
      (∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) → ∀ x y : ℂ,
      ‖convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x-
        convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume y‖ ≤
          L*H*‖x-y‖ := by
  obtain ⟨C,hC,hCb⟩ := cutoff_smoothCauchyKernel_bound b
  let L : ℝ := (C+3)*(∫ w : ℂ, cauchySchauderWeight b.rOut w)
  have hw0 : ∀ w, 0≤cauchySchauderWeight b.rOut w := by
    intro w
    apply indicator_nonneg
    intro z _
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hL : 0≤L := mul_nonneg (by linarith) (integral_nonneg hw0)
  refine ⟨L,hL,?_⟩
  intro g hg H hH hHg x y
  have hb (δ : ℝ) (hδ : 0<δ) :
      ‖convolution (fun w => b w • smoothCauchyKernel δ w) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x-
        convolution (fun w => b w • smoothCauchyKernel δ w) g (ContinuousLinearMap.lsmul ℝ ℂ) volume y‖ ≤
          L*H*‖x-y‖ := by
    have hs : ContDiff ℝ ∞ (fun w => b w • smoothCauchyKernel δ w) :=
      b.contDiff.smul (smoothCauchyKernel_smooth hδ)
    have hc : HasCompactSupport (fun w => b w • smoothCauchyKernel δ w) := b.hasCompactSupport.smul_right
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (s := (univ : Set ℂ)) (fun z _ =>
        (hc.hasFDerivAt_convolution_left _ (hs.of_le (by simp)) hg.locallyIntegrable z).differentiableAt)
      (fun z _ => ?_) convex_univ (mem_univ y) (mem_univ x)
    have hh := compact_kernel_convolution_derivative_bound hs hc hg
      ((cauchySchauderWeight_integrable b.rOut).const_mul ((C+3)*H))
      (cutoff_smoothCauchyKernel_schauder_bound b hC hCb hH hHg hδ) z
    apply hh.trans_eq
    rw [integral_const_mul]
    dsimp [L]
    ring
  have ht := ((cutoff_smoothCauchyKernel_convolution_tendsto b hg x).sub
    (cutoff_smoothCauchyKernel_convolution_tendsto b hg y)).norm
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hb δ hδ


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

def regularizedCauchyJet (δ : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (‖z‖^2+δ)⁻¹ • (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap -
    (2/(‖z‖^2+δ)^2) • ((innerSL ℝ z).smulRight (star z))

lemma regularizedCauchyJet_eq {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    fderiv ℝ (smoothCauchyKernel δ) z = regularizedCauchyJet δ z := by
  ext v
  rw [smoothCauchyKernel_fderiv hδ]
  simp only [regularizedCauchyJet, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, starL'_apply, ContinuousLinearEquiv.coe_coe, smul_smul]
  congr 1
  congr 1
  ring

lemma regularizedCauchyJet_continuousAt {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun δ : ℝ => regularizedCauchyJet δ z) 0 := by
  have hq : ‖z‖^2+(0:ℝ) ≠ 0 := by simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hi : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹) 0 :=
    (continuousAt_const.add continuousAt_id).inv₀ hq
  have hcoeff : ContinuousAt (fun δ : ℝ => 2/(‖z‖^2+δ)^2) 0 :=
    continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2) (pow_ne_zero 2 hq)
  exact (hi.smul continuousAt_const).sub
    (hcoeff.smul continuousAt_const)

def cutoffCauchyJet (b : ContDiffBump (0:ℂ)) (δ : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  b z • regularizedCauchyJet δ z + (fderiv ℝ b z).smulRight (smoothCauchyKernel δ z)

lemma cutoffCauchyJet_eq (b : ContDiffBump (0:ℂ)) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z = cutoffCauchyJet b δ z := by
  rw [fderiv_fun_smul ((b.contDiff : ContDiff ℝ ∞ b).differentiable (by simp) z)
    ((smoothCauchyKernel_smooth hδ).differentiable (by simp) z), regularizedCauchyJet_eq hδ]
  rfl

lemma cutoffCauchyJet_continuousAt (b : ContDiffBump (0:ℂ)) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun δ : ℝ => cutoffCauchyJet b δ z) 0 := by
  have hq : ‖z‖^2+(0:ℝ) ≠ 0 := by simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hi : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹) 0 :=
    (continuousAt_const.add continuousAt_id).inv₀ hq
  have hv : ContinuousAt (fun δ : ℝ => smoothCauchyKernel δ z) 0 :=
    hi.smul (show ContinuousAt (fun _ : ℝ => star z) 0 from continuousAt_const)
  have hs : ContinuousAt (fun δ : ℝ => (fderiv ℝ b z).smulRight (smoothCauchyKernel δ z)) 0 :=
    (ContinuousLinearMap.smulRightL ℝ ℂ ℂ (fderiv ℝ b z)).continuous.continuousAt.comp hv
  have hb : ContinuousAt (fun δ : ℝ => b z • regularizedCauchyJet δ z) 0 :=
    (show ContinuousAt (fun _ : ℝ => b z) 0 from continuousAt_const).smul
      (regularizedCauchyJet_continuousAt hz)
  exact hb.add hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def cancellationJetIntegrand (b : ContDiffBump (0:ℂ)) (δ : ℝ) (g : ℂ → E)
    (x w : ℂ) : ℂ →L[ℝ] E :=
  ((ContinuousLinearMap.lsmul ℝ ℂ).flip (g (x-w)-g x)).comp (cutoffCauchyJet b δ w)

def cutoffCauchyDerivative (b : ContDiffBump (0:ℂ)) (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  ∫ w : ℂ, cancellationJetIntegrand b 0 g x w

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_apply (b : ContDiffBump (0:ℂ)) (δ : ℝ)
    (g : ℂ → E) (x w v : ℂ) :
    cancellationJetIntegrand b δ g x w v = cutoffCauchyJet b δ w v • (g (x-w)-g x) := rfl

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_continuous (b : ContDiffBump (0:ℂ)) {δ : ℝ} (hδ : 0 < δ)
    {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Continuous (cancellationJetIntegrand b δ g x) := by
  have hK : ContDiff ℝ ∞ (fun w => b w • smoothCauchyKernel δ w) :=
    b.contDiff.smul (smoothCauchyKernel_smooth hδ)
  have hD : Continuous (fun w => cutoffCauchyJet b δ w) := by
    simp_rw [← cutoffCauchyJet_eq b hδ]
    exact hK.continuous_fderiv (by simp)
  exact (((ContinuousLinearMap.lsmul ℝ ℂ).flip).continuous.comp
    ((hg.comp (continuous_const.sub continuous_id)).sub continuous_const)).clm_comp hD

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_bound (b : ContDiffBump (0:ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ δ : ℝ, 0 < δ → ∀ z v : ℂ, z ≠ 0 →
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z v‖ ≤
        (C*‖z‖⁻¹+3/‖z‖^2)*‖v‖)
    {g : ℂ → E} {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    {δ : ℝ} (hδ : 0 < δ) (x w : ℂ) :
    ‖cancellationJetIntegrand b δ g x w‖ ≤ (C+3)*H*cauchySchauderWeight b.rOut w := by
  have hw0 : 0 ≤ cauchySchauderWeight b.rOut w := by
    apply indicator_nonneg _ w
    intro z _
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [cancellationJetIntegrand_apply, norm_smul, ← cutoffCauchyJet_eq b hδ]
  exact cutoff_smoothCauchyKernel_schauder_bound b hC hCb hH hg hδ x w v

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_tendsto (b : ContDiffBump (0:ℂ))
    (g : ℂ → E) (x w : ℂ) :
    Tendsto (fun δ : ℝ => cancellationJetIntegrand b δ g x w) (𝓝[>] 0)
      (𝓝 (cancellationJetIntegrand b 0 g x w)) := by
  by_cases hw : w = 0
  · subst w
    simp only [cancellationJetIntegrand, sub_zero, sub_self, map_zero, ContinuousLinearMap.zero_comp]
    exact tendsto_const_nhds
  · have h : ContinuousAt (fun δ : ℝ => cancellationJetIntegrand b δ g x w) 0 :=
      (show ContinuousAt (fun _ : ℝ => (ContinuousLinearMap.lsmul ℝ ℂ).flip (g (x-w)-g x)) 0
        from continuousAt_const).clm_comp (cutoffCauchyJet_continuousAt b hw)
    exact h.tendsto.mono_left nhdsWithin_le_nhds

lemma cutoff_smoothCauchyKernel_derivative_tendsto (b : ContDiffBump (0:ℂ))
    {g : ℂ → E} (hgC : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x : ℂ) :
    Tendsto (fun δ : ℝ => fderiv ℝ
      (convolution (fun w => b w • smoothCauchyKernel δ w) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x) (𝓝[>] 0)
      (𝓝 (cutoffCauchyDerivative b g x)) := by
  obtain ⟨C,hC,hCb⟩ := cutoff_smoothCauchyKernel_bound b
  let W : ℂ → ℝ := fun w => (C+3)*H*cauchySchauderWeight b.rOut w
  have hW : Integrable W := (cauchySchauderWeight_integrable b.rOut).const_mul _
  have hi (δ : ℝ) (hδ : 0 < δ) : Integrable (cancellationJetIntegrand b δ g x) :=
    hW.mono' (cancellationJetIntegrand_continuous b hδ hgC x).aestronglyMeasurable
      (Eventually.of_forall (cancellationJetIntegrand_bound b hC hCb hH hg hδ x))
  have he (δ : ℝ) (hδ : 0 < δ) : fderiv ℝ
      (convolution (fun w => b w • smoothCauchyKernel δ w) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x =
      ∫ w : ℂ, cancellationJetIntegrand b δ g x w := by
    ext v
    rw [ContinuousLinearMap.integral_apply (hi δ hδ)]
    rw [compact_kernel_convolution_cancel (K := fun w => b w • smoothCauchyKernel δ w) (b.contDiff.smul (smoothCauchyKernel_smooth hδ))
      (b.hasCompactSupport.smul_right (f' := smoothCauchyKernel δ)) hgC]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by
      dsimp only
      rw [cancellationJetIntegrand_apply, cutoffCauchyJet_eq b hδ]
  have hEq : (fun δ : ℝ => ∫ w : ℂ, cancellationJetIntegrand b δ g x w) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ => fderiv ℝ (convolution (fun w => b w • smoothCauchyKernel δ w) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) x) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (he δ hδ).symm
  apply Tendsto.congr' hEq
  apply tendsto_integral_filter_of_dominated_convergence W
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (cancellationJetIntegrand_continuous b hδ hgC x).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall (cancellationJetIntegrand_bound b hC hCb hH hg hδ x)
  · exact hW
  · exact Eventually.of_forall (cancellationJetIntegrand_tendsto b g x)


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
