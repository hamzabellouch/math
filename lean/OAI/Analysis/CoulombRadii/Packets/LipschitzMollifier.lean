import Mathlib

namespace OAI

section
section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Topology ContDiff Convolution
noncomputable section
namespace NeutralAtom

theorem exists_smooth_lipschitz_approx
    (K : EuclideanSpace ℝ (Fin 3) → ℝ) {A R ε : ℝ} (hA : 0≤A) (hε : 0<ε)
    (y : EuclideanSpace ℝ (Fin 3))
    (hs : ∀ z, R<‖z-y‖ → K z=0)
    (hL : ∀ z v, |K z-K v|≤A*‖z-v‖) :
    ∃ χ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ ∞ χ ∧
      tsupport χ⊆Metric.closedBall y (R+ε) ∧
      (∀ z v, |χ z-χ v|≤A*‖z-v‖) ∧ (∀ z, |χ z-K z|≤A*ε) := by
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨ε/2,ε,by positivity,by linarith⟩
  have hKl : LipschitzWith ⟨A,hA⟩ K := by
    apply LipschitzWith.of_dist_le_mul
    intro z v
    change dist (K z) (K v) ≤ A*dist z v
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs] using hL z v
  have hKc := hKl.continuous
  let χ := φ.normed volume ⋆[lsmul ℝ ℝ,volume] K
  have hχ : ContDiff ℝ ∞ χ :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hKc.locallyIntegrable
  have hi (z : EuclideanSpace ℝ (Fin 3)) :
      Integrable (fun u => φ.normed volume u * K (z-u)) := by
    exact φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hKc.locallyIntegrable z
  refine ⟨χ,hχ,?_,?_,?_⟩
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    change χ z≠0 at hz
    by_contra hn
    have hd : R+ε<‖z-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hn
    apply hz
    change (∫ u, φ.normed volume u*K (z-u))=0
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    change φ.normed volume u*K (z-u)=0
    by_cases hu : φ.normed volume u=0
    · simp only [hu,zero_mul]
    have hu' : ‖u‖<ε := by
      have hh : u∈Function.support (φ.normed volume) := hu
      rw [φ.support_normed_eq] at hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
    have htri : ‖z-y‖≤‖z-u-y‖+‖u‖ := by
      calc _=‖(z-u-y)+u‖ := by congr 1; module
           _≤_ := norm_add_le _ _
    rw [hs _ (by linarith),mul_zero]
  · intro z v
    change |(∫ u, φ.normed volume u*K (z-u))-(∫ u, φ.normed volume u*K (v-u))|≤_
    rw [←integral_sub (hi z) (hi v)]
    calc
      _≤∫ u, |φ.normed volume u*K (z-u)-φ.normed volume u*K (v-u)| := abs_integral_le_integral_abs
      _≤∫ u, φ.normed volume u*(A*‖z-v‖) := by
        apply integral_mono
        · simpa only [Pi.sub_apply,Real.norm_eq_abs] using ((hi z).sub (hi v)).norm
        · exact φ.integrable_normed.mul_const _
        · intro u
          dsimp only
          rw [←mul_sub,abs_mul,abs_of_nonneg (φ.nonneg_normed u)]
          have he : z-u-(v-u)=z-v := by module
          exact mul_le_mul_of_nonneg_left (by simpa only [he] using hL (z-u) (v-u)) (φ.nonneg_normed u)
      _=A*‖z-v‖ := by rw [integral_mul_const,φ.integral_normed,one_mul]
  · intro z
    have hh := φ.dist_normed_convolution_le (μ := volume) hKc.aestronglyMeasurable
      (x₀ := z) (ε := A*ε) (fun v hv => by
        rw [Real.dist_eq]
        exact (hL v z).trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_ball,dist_eq_norm] using hv.le) hA))
    exact hh

end NeutralAtom
end

end
end

end OAI
