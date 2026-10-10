import Mathlib
import OAI.Probability.LogConcave.Sampling.QuadraticExpectation

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

theorem translation_integration_by_parts {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (v : Point d) :
    Integrable (fun z => inner ℝ (gradient H z) v * Real.exp (-H z)) ∧
      (∫ z,inner ℝ (gradient H z) v * Real.exp (-H z))=0 := by
  obtain ⟨m,hm,C,ht⟩ := ht
  let F : ℝ → Point d → ℝ := fun t z => Real.exp (-H (z+t • v))
  let F' : ℝ → Point d → ℝ := fun t z =>
    -(inner ℝ (gradient H (z+t • v)) v)*Real.exp (-H (z+t • v))
  have hgc : Continuous (gradient H) := hL.continuous
  have hd (z : Point d) (t : ℝ) : HasDerivAt (fun t => F t z) (F' t z) t := by
    have hh := (hH.differentiable (by norm_num) (z+t • v)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v).const_add z)
    have hh' : HasDerivAt (fun t => H (z+t • v)) (inner ℝ (gradient H (z+t • v)) v) t := by
      convert! hh using 1
      rw [one_smul,inner_gradient_left]
    convert! hh'.neg.exp using 1
    simp only [F',mul_comm,Pi.neg_apply]
  have hi : Integrable (F 0) := by
    simpa [F] using integrable_tilted H hH.continuous continuous_const
      ⟨m,hm,C,ht⟩ (growth_const (1:ℝ)) 0
  let A : ℝ := (‖gradient H 0‖+(K:ℝ)*‖v‖+(K:ℝ))*‖v‖*Real.exp (C+m*‖v‖^2)
  have hb (z : Point d) (t : ℝ) (ht' : t∈Set.Ioo (-1:ℝ) 1) :
      ‖F' t z‖ ≤ A*((1+‖z‖)*Real.exp (-(m/2)*‖z‖^2)) := by
    have hat : |t|≤1 := (abs_le.mpr ⟨ht'.1.le,ht'.2.le⟩)
    have hv : ‖t • v‖≤‖v‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hat (norm_nonneg v)).trans_eq (one_mul _)
    have hn : ‖z+t • v‖≤‖z‖+‖v‖ := (norm_add_le _ _).trans (add_le_add le_rfl hv)
    have hn' : ‖z‖≤‖z+t • v‖+‖v‖ := by
      calc
        ‖z‖=‖(z+t • v)-t • v‖ := by congr 1; abel
        _ ≤ ‖z+t • v‖+‖t • v‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add le_rfl hv
    have hs : ‖z‖^2≤2*‖z+t • v‖^2+2*‖v‖^2 := by
      have hh := pow_le_pow_left₀ (norm_nonneg z) hn' 2
      nlinarith [sq_nonneg (‖z+t • v‖-‖v‖)]
    have he : Real.exp (-H (z+t • v))≤
        Real.exp (C+m*‖v‖^2)*Real.exp (-(m/2)*‖z‖^2) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hs hm.le
      nlinarith [ht (z+t • v)]
    have hg : ‖gradient H (z+t • v)‖ ≤
        (‖gradient H 0‖+(K:ℝ)*‖v‖+(K:ℝ))*(1+‖z‖) := by
      have hh := hL.dist_le_mul (z+t • v) 0
      rw [dist_zero_right] at hh
      have hh' := norm_add_le (gradient H (z+t • v)-gradient H 0) (gradient H 0)
      rw [sub_add_cancel,←dist_eq_norm] at hh'
      have hk := mul_le_mul_of_nonneg_left hn K.coe_nonneg
      nlinarith [mul_nonneg (norm_nonneg (gradient H 0)) (norm_nonneg z),
        mul_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg v)) (norm_nonneg z)]
    dsimp [F']
    rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (‖gradient H (z+t • v)‖*‖v‖)*Real.exp (-H (z+t • v)) :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (by positivity)
      _ ≤ (((‖gradient H 0‖+(K:ℝ)*‖v‖+(K:ℝ))*(1+‖z‖))*‖v‖)*
          (Real.exp (C+m*‖v‖^2)*Real.exp (-(m/2)*‖z‖^2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hg (norm_nonneg v)) he (by positivity) (by positivity)
      _ = _ := by dsimp [A]; ring
  have hint : Integrable (fun z : Point d => A*((1+‖z‖)*Real.exp (-(m/2)*‖z‖^2))) := by
    have hh := ((integrable_gaussian_envelope d (b:=m/2) (by positivity)).add
      (integrable_norm_pow_gaussian d 1 (b:=m/2) (by positivity))).const_mul A
    simpa [add_mul] using hh
  have hp := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=(volume:Measure (Point d))) (F:=F) (F':=F')
    (bound:=fun z => A*((1+‖z‖)*Real.exp (-(m/2)*‖z‖^2)))
    (x₀:=(0:ℝ)) (s:=Set.Ioo (-1:ℝ) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t =>
      (Real.continuous_exp.comp (hH.continuous.comp
        (continuous_id.add continuous_const)).neg).aestronglyMeasurable)
    hi
    (by
      have hh : Continuous (fun z => -(inner ℝ (gradient H z) v)*Real.exp (-H z)) :=
        (hgc.inner continuous_const).neg.mul (Real.continuous_exp.comp hH.continuous.neg)
      simpa [F'] using hh.aestronglyMeasurable)
    (Filter.Eventually.of_forall hb) hint (Filter.Eventually.of_forall fun z t _ => hd z t)
  have he (t : ℝ) : (∫ z,F t z)=∫ z,Real.exp (-H z) := by
    exact integral_add_right_eq_self (fun z => Real.exp (-H z)) (t • v)
  have hh := hp.2.unique ((hasDerivAt_const (0:ℝ) (∫ z,Real.exp (-H z))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall he))
  refine ⟨?_,?_⟩
  · simpa [F',neg_mul] using hp.1.neg
  · simpa only [F',zero_smul,add_zero,neg_mul,integral_neg,neg_eq_zero] using hh

lemma integral_gradient_gibbs_zero {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) :
    (∫ z,gradient H z ∂gibbs H)=0 := by
  have hd : Integrable (fun z => Real.exp (-H z)) := by
    simpa using integrable_tilted H hH.continuous continuous_const ht (growth_const (1:ℝ)) 0
  have hi : Integrable (fun z => Real.exp (-H z) • gradient H z) := by
    simpa using integrable_tilted H hH.continuous hL.continuous ht (growth_of_lipschitz hL) 0
  have hz : (∫ z,Real.exp (-H z) • gradient H z)=0 := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_zero_left,real_inner_comm,←integral_inner hi]
    simpa [inner_smul_right,mul_comm,real_inner_comm] using
      (translation_integration_by_parts hH ht hL v).2
  rw [integral_gibbs_vector hH.continuous hd,hz,smul_zero]
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
