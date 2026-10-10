import OAI.Geometry.NodalSets.Waves.GaussianPairCovariance

namespace OAI

namespace Yau.Geometry
open Yau.Probability MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma pairLinearSum_real_combination (z w : ι → ℂ) (u v : ℝ) :
    pairLinearSum (fun i ↦ (u:ℂ)*z i+(v:ℂ)*w i) =
      fun a ↦ u*pairLinearSum z a+v*pairLinearSum w a := by
  classical
  funext a
  simp only [pairLinearSum,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

lemma two_point_coefficient_energy (z w : ι → ℂ) (u v : ℝ) :
    (∑ i, ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2) =
      u^2*Var[pairLinearSum z;gaussianPairs] +
        2*u*v*cov[pairLinearSum z,pairLinearSum w;gaussianPairs] +
        v^2*Var[pairLinearSum w;gaussianPairs] := by
  let : IsProbabilityMeasure (gaussianPairs (ι := ι)) := by unfold gaussianPairs; infer_instance
  rw [← variance_pairLinearSum,pairLinearSum_real_combination,
    variance_fun_add ((pairLinearSum_memLp_two z).const_mul u) ((pairLinearSum_memLp_two w).const_mul v),
    variance_const_mul,variance_const_mul,covariance_const_mul_left,covariance_const_mul_right]
  ring

lemma two_point_energy_of_gap (z w : ι → ℂ) (M C delta : ℝ)
    (hM : Var[pairLinearSum z;gaussianPairs] = M)
    (hW : Var[pairLinearSum w;gaussianPairs] = M)
    (hC : cov[pairLinearSum z,pairLinearSum w;gaussianPairs] = C)
    (hC0 : 0 ≤ C) (hgap : C ≤ M-delta) (u v : ℝ) :
    delta*(u^2+v^2) ≤ ∑ i, ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2 := by
  rw [two_point_coefficient_energy,hM,hW,hC]
  have h1 := mul_nonneg hC0 (sq_nonneg (u+v))
  have h2 := mul_nonneg (show 0 ≤ M-delta-C by linarith) (add_nonneg (sq_nonneg u) (sq_nonneg v))
  nlinarith

lemma complex_norm_add_sq_bound (z w : ℂ) : ‖z+w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have hh := norm_add_le z w
  have hs := sq_le_sq₀ (norm_nonneg (z+w)) (add_nonneg (norm_nonneg z) (norm_nonneg w))
  have hh2 := hs.mpr hh
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma two_point_energy_perturbation (z w f h : ι → ℂ) (delta e : ℝ)
    (hz : ∑ i, ‖f i-z i‖^2 ≤ e) (hw : ∑ i, ‖h i-w i‖^2 ≤ e)
    (hgap : ∀ u v : ℝ, delta*(u^2+v^2) ≤ ∑ i, ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2)
    (u v : ℝ) :
    (delta/2-2*e)*(u^2+v^2) ≤ ∑ i, ‖(u:ℂ)*f i+(v:ℂ)*h i‖^2 := by
  have hp (i : ι) : ‖(u:ℂ)*z i+(v:ℂ)*w i‖^2 ≤
      2*‖(u:ℂ)*f i+(v:ℂ)*h i‖^2 +
        4*(u^2*‖f i-z i‖^2+v^2*‖h i-w i‖^2) := by
    have h1 := complex_norm_add_sq_bound ((u:ℂ)*f i+(v:ℂ)*h i)
      (-((u:ℂ)*(f i-z i)+(v:ℂ)*(h i-w i)))
    rw [show (u:ℂ)*f i+(v:ℂ)*h i+-((u:ℂ)*(f i-z i)+(v:ℂ)*(h i-w i)) =
      (u:ℂ)*z i+(v:ℂ)*w i by ring,norm_neg] at h1
    have h2 := complex_norm_add_sq_bound ((u:ℂ)*(f i-z i)) ((v:ℂ)*(h i-w i))
    simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs] at h2
    linarith
  have heq : (∑ i, (2*‖(u:ℂ)*f i+(v:ℂ)*h i‖^2 + 4*(u^2*‖f i-z i‖^2+v^2*‖h i-w i‖^2))) =
      2*(∑ i, ‖(u:ℂ)*f i+(v:ℂ)*h i‖^2)+
        4*(u^2*(∑ i, ‖f i-z i‖^2)+v^2*(∑ i, ‖h i-w i‖^2)) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum,mul_add]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hp i)
  rw [heq] at hsum
  have hzu := mul_le_mul_of_nonneg_left hz (sq_nonneg u)
  have hwv := mul_le_mul_of_nonneg_left hw (sq_nonneg v)
  have hg := hgap u v
  nlinarith

end
end Yau.Geometry

end OAI
