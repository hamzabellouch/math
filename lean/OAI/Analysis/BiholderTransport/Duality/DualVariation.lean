import Mathlib
import OAI.Analysis.BiholderTransport.Duality.CompactDual

namespace OAI

section

section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section DualVariation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma contact_gap_level_control {v : M → ℝ} (hv : Continuous v) {x y₀ : M}
    (huniq : ∀ y, contactGap (cTransform v) v x y=0 → y=y₀)
    (f : M →ᵇ ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ δ>0, ∀ y, contactGap (cTransform v) v x y≤δ → |f y₀-f y|≤ε := by
  let G := fun y => contactGap (cTransform v) v x y
  have hG : Continuous G := (continuous_const.add (continuous_cost_right x)).add hv
  let A := {y | ε≤|f y₀-f y|}
  have hA : IsCompact A := (isClosed_le continuous_const
    ((continuous_const.sub f.continuous).abs)).isCompact
  by_cases hne : A.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hA.exists_isMinOn hne hG.continuousOn
    have hpos : 0<G z := by
      apply lt_of_le_of_ne (cTransform_gap_nonneg hv x z)
      intro he
      have hez := huniq z he.symm
      have H : ε≤|f y₀-f z| := hz
      rw [hez,sub_self,abs_zero] at H
      exact (not_le.mpr hε) H
    refine ⟨G z/2,half_pos hpos,fun y hy => ?_⟩
    by_contra hh
    have hm := hmin (le_of_lt (lt_of_not_ge hh))
    change G z≤G y at hm
    change G y≤G z/2 at hy
    linarith
  · refine ⟨1,by norm_num,fun y _ => ?_⟩
    by_contra hh
    exact hne ⟨y,le_of_lt (lt_of_not_ge hh)⟩

lemma boundedCTransform_perturbation_bound (v f : M →ᵇ ℝ) (t : ℝ) (x : M) :
    |boundedCTransform (v+t • f) x-boundedCTransform v x|≤|t| *‖f‖ := by
  have H := boundedCTransform_nonexpansive.norm_sub_le (v+t • f) v
  have hp := BoundedContinuousFunction.norm_coe_le_norm
    (boundedCTransform (v+t • f)-boundedCTransform v) x
  simp only [BoundedContinuousFunction.sub_apply,Real.norm_eq_abs] at hp
  apply hp.trans
  simpa only [NNReal.coe_one,one_mul,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] using H

lemma boundedCTransform_perturbation_hasDerivAt (v f : M →ᵇ ℝ) {x y₀ : M}
    (hy₀ : contactGap (boundedCTransform v) v x y₀=0)
    (huniq : ∀ y, contactGap (boundedCTransform v) v x y=0 → y=y₀) :
    HasDerivAt (fun t : ℝ => boundedCTransform (v+t • f) x) (-f y₀) 0 := by
  rw [hasDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hcontrol⟩ := contact_gap_level_control v.continuous huniq f hε
  have hden : 0<2*‖f‖+1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (div_pos hδ hden)] with t ht
  have ht' : |t|<δ/(2*‖f‖+1) := by simpa only [mem_ball,Real.dist_eq,sub_zero] using ht
  have htδ : |t| *(2*‖f‖+1)<δ := (lt_div_iff₀ hden).mp ht'
  obtain ⟨y,hy⟩ := cTransform_gap_zero (v+t • f).continuous x
  have hgap := cTransform_gap_nonneg v.continuous x y
  have hbound := boundedCTransform_perturbation_bound v f t x
  have hf := BoundedContinuousFunction.norm_coe_le_norm f y
  rw [Real.norm_eq_abs] at hf
  have htf : |t*f y|≤|t| *‖f‖ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hf (abs_nonneg t)
  have hy' : boundedCTransform (v+t • f) x + cost x y+v y+t*f y=0 := by
    simpa only [contactGap,BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
      smul_eq_mul,add_assoc,boundedCTransform_apply] using hy
  have hsmall : contactGap (boundedCTransform v) v x y≤δ := by
    dsimp only [contactGap]
    nlinarith [(abs_le.mp hbound).1,(abs_le.mp htf).1,abs_nonneg t]
  have hc := hcontrol y hsmall
  have hrem := cTransform_gap_nonneg (v+t • f).continuous x y₀
  change 0≤boundedCTransform (v+t • f) x+cost x y₀+(v+t • f) y₀ at hrem
  simp only [BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,smul_eq_mul] at hrem
  dsimp only [contactGap] at hy₀ hgap
  change 0≤boundedCTransform v x+cost x y+v y at hgap
  have hab : |t*(f y₀-f y)|≤|t| *ε := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hc (abs_nonneg t)
  simp only [sub_zero,zero_smul,add_zero,smul_eq_mul,Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hε.le (abs_nonneg t)]
  · nlinarith [(abs_le.mp hab).2]

end DualVariation
end WeakMTWTransport

end

end

end

end OAI
