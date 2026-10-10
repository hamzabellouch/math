import OAI.Analysis.HenonEmden.RadialGradient

namespace OAI

section RadialJoint

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

@[fun_prop] lemma measurable_joint_kernelDir (n : ℕ) :
    Measurable (fun z : Space n × Space n => kernelDir z.1 (z.1-z.2)) := by
  unfold kernelDir
  exact (measurable_const.mul ((measurable_fst.sub measurable_snd).norm.pow_const _)).mul (by fun_prop)

lemma IsSolution.integrable_joint_radial_gradient {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun z : Space n × Space n =>
      eta n z.1*source u q B z.1*(kernelDir z.1 (z.1-z.2)*source v p A z.2)) (volume.prod volume) := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  have hfm := measurable_source h.continuous_u q B
  have hgm := measurable_source h.continuous_v p A
  have hηm := (continuous_eta n (E := Space n)).measurable
  have hm : Measurable (fun z : Space n × Space n =>
      eta n z.1*source u q B z.1*(kernelDir z.1 (z.1-z.2)*source v p A z.2)) := by fun_prop
  have hz : ∀ᵐ x : Space n, x ≠ 0 := ae_iff.mpr (by simp)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hz] with x hx
    exact ((h.gradient_u hn hq hx x).1.const_mul _)
  · obtain ⟨C,hC,hbound⟩ := h.radial_kernel_absolute_bounded hn hp hq
    have hi : Integrable (fun x => C*(eta n x*source u q B x)) :=
      ((h.source_f_locallyIntegrable hn).integrable_smul_left_of_hasCompactSupport
        (continuous_eta n) (compactSupport_eta n)).const_mul C
    apply hi.mono' hm.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable
    filter_upwards [hz] with x hx
    have hs := source_nonneg (fun y => (h.positive_u y).le) q B x
    have ht : 0 ≤ eta n x*source u q B x := mul_nonneg
      (pow_nonneg (baseProfile_nonneg ‖x‖) (N n) : 0 ≤ eta n x) hs
    have he (y : Space n) : ‖eta n x*source u q B x*(kernelDir x (x-y)*source v p A y)‖ =
        (eta n x*source u q B x)*|kernelDir x (x-y)*source v p A y| := by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ht,Real.norm_eq_abs]
    simp_rw [he]
    rw [integral_const_mul,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht (integral_nonneg (fun y => abs_nonneg _)))]
    by_cases hx2 : ‖x‖ ≤ 2
    · exact (mul_le_mul_of_nonneg_left (hbound x hx hx2) ht).trans_eq (mul_comm _ _)
    · rw [eta_eq_zero (le_of_not_ge hx2)]; simp

lemma IsSolution.integrable_eta_source_radialDir {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun x => eta n x*source u q B x*dir u x x) := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  have hi := (h.integrable_joint_radial_gradient hn hp hq).integral_prod_left.const_mul ((newtonDenom n)⁻¹)
  apply hi.congr
  filter_upwards [ae_iff.mpr (show volume {x : Space n | ¬x ≠ 0}=0 by simp)] with x hx
  rw [integral_const_mul]
  have hg := (h.gradient_u hn hq hx x).2
  rw [← hg]
  field_simp [ne_of_gt (newtonDenom_pos (h.dimension_ge_three hn))]

lemma IsSolution.integral_eta_source_radialDir {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (∫ x, eta n x*source u q B x*dir u x x) = (newtonDenom n)⁻¹*
      ∫ z : Space n × Space n, eta n z.1*source u q B z.1*
        (kernelDir z.1 (z.1-z.2)*source v p A z.2) ∂volume.prod volume := by
  have : Nontrivial (Space n) := (Module.finrank_pos_iff (R := ℝ)).mp (by simp; omega)
  rw [integral_prod _ (h.integrable_joint_radial_gradient hn hp hq),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (show volume {x : Space n | ¬x ≠ 0}=0 by simp)] with x hx
  rw [integral_const_mul,← (h.gradient_u hn hq hx x).2]
  field_simp [ne_of_gt (newtonDenom_pos (h.dimension_ge_three hn))]

end HenonLaneEmden
end
end RadialJoint

end OAI
