import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralBase

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open MeasureTheory Filter Complex Set
open scoped SchwartzMap FourierTransform Topology

theorem dampedSquareKernel_fourier (W : 𝓢(ℝ, ℂ)) (ε a x : ℝ) :
    (∫ t : ℝ, dampedSquareKernel W ε a x t) =
      (Real.exp (-ε*x^2) : ℂ)*(𝓕 W) (a*x^2) := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq',←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [dampedSquareKernel,smul_eq_mul,RCLike.inner_apply,starRingEnd_apply,star_trivial,Complex.ofReal_exp]
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  simp only [squareGaussianParameter]
  push_cast
  ring

theorem damped_fourier_square_integral (W : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0<ε) (a : ℝ) :
    (∫ x : ℝ, (Real.exp (-ε*x^2) : ℂ)*(𝓕 W) (a*x^2)) =
      ∫ t : ℝ, ((Real.pi : ℂ)/squareGaussianParameter ε a t)^(1/2 : ℂ)*W t := by
  simpa only [dampedSquareKernel_fourier] using dampedSquareKernel_swap W hε a

theorem tendsto_damped_fourier_square_integral (W : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a≠0) :
    Tendsto (fun ε : ℝ => ∫ x : ℝ,
      (Real.exp (-ε*x^2) : ℂ)*(𝓕 W) (a*x^2)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x : ℝ, (𝓕 W) (a*x^2))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => ‖(𝓕 W) (a*x^2)‖)
  · exact Filter.Eventually.of_forall fun ε => (by fun_prop : Continuous
      (fun x : ℝ => (Real.exp (-ε*x^2) : ℂ)*(𝓕 W) (a*x^2))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards with x
    have he : Real.exp (-ε*x^2) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by simpa using (neg_nonpos.mpr (Set.mem_Ioi.mp hε).le)) (sq_nonneg x))
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) he
  · exact (integrable_squarePullback (𝓕 W) ha).norm
  · filter_upwards with x
    have h : ContinuousAt (fun ε : ℝ => (Real.exp (-ε*x^2) : ℂ)*(𝓕 W) (a*x^2)) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds

end Ostmann.QuadraticSieve

end

end OAI
