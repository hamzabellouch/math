import OAI.NumberTheory.JointDickman.Amplification.SchwartzFourierProfile

namespace OAI

/-! # Finite Fourier inversion for the sampled smooth endpoint kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem schwartz_phase_integrable (w : 𝓢(ℝ, ℝ)) (s : ℝ) :
    Integrable (fun ξ : ℝ => testFourierTransform w ξ*additivePhase (ξ*s)) :=
  (schwartz_testFourier_integrable w).mul_bdd
    (continuous_additivePhase.comp (continuous_id.mul_const s)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => (norm_additivePhase (ξ*s)).le))

theorem finite_fourier_kernel {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (x : ι → ℝ) (y : κ → ℝ) (w : 𝓢(ℝ, ℝ)) :
    (∫ ξ : ℝ, testFourierTransform w ξ*(∑ i ∈ s, a i*additivePhase (ξ*x i))*
      (∑ j ∈ t, b j*additivePhase (-ξ*y j))) =
      ∑ i ∈ s, ∑ j ∈ t, (a i*b j)*(w (x i-y j) : ℂ) := by
  have hi (i : ι) (j : κ) : Integrable (fun ξ : ℝ =>
      (a i*b j)*(testFourierTransform w ξ*additivePhase (ξ*(x i-y j)))) :=
    (schwartz_phase_integrable w _).const_mul _
  have he : (fun ξ : ℝ => testFourierTransform w ξ*(∑ i ∈ s, a i*additivePhase (ξ*x i))*
      (∑ j ∈ t, b j*additivePhase (-ξ*y j))) =
      fun ξ => ∑ i ∈ s, ∑ j ∈ t,
        (a i*b j)*(testFourierTransform w ξ*additivePhase (ξ*(x i-y j))) := by
    funext ξ
    simp only [mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    have hp : additivePhase (ξ*(x i-y j)) = additivePhase (ξ*x i)*additivePhase (-ξ*y j) := by
      rw [← additivePhase_add]
      congr 1
      ring
    rw [hp]
    ring
  rw [he,integral_finsetSum]
  · apply sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro j _
      rw [integral_const_mul,schwartz_testFourier_inversion]
    · exact fun j _ => hi i j
  · exact fun i _ => integrable_finsetSum _ (fun j _ => hi i j)

end JointDickman

end OAI
