import OAI.NumberTheory.JointDickman.Probability.SampledHistogram
import OAI.NumberTheory.JointDickman.Probability.FiniteFourierKernel
import OAI.NumberTheory.JointDickman.Probability.ProjectedResidueKernel

namespace OAI

/-! # Exact inversion of the sampled, residue-averaged arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

theorem projected_residue_full_integral {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)]
    (W A B : ℝ → ℂ) :
    ((μ q : ℂ)/(q.totient : ℂ))*(∑ h : ZMod (j*q), if h.val.Coprime q then
      ∫ ξ : ℝ, W ξ*((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A ξ)*
        ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B ξ) else 0) =
      (((j : ℝ)/j.totient*singularSeriesCoefficient j q : ℝ) : ℂ)*
        ∫ ξ : ℝ, W ξ*A ξ*B ξ := by
  let I : ℂ := ∫ ξ : ℝ, W ξ*A ξ*B ξ
  have hi (h : ZMod (j*q)) :
      (∫ ξ : ℝ, W ξ*((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A ξ)*
        ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B ξ)) =
        ((ramanujanSum (j*q) h/((j*q).totient : ℂ))*I)*
          ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*1) := by
    have he : (fun ξ => W ξ*((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A ξ)*
        ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B ξ)) =
        fun ξ => ((ramanujanSum (j*q) h/((j*q).totient : ℂ))*
          (ramanujanSum (j*q) (-h)/((j*q).totient : ℂ)))*(W ξ*A ξ*B ξ) := by
      funext ξ
      ring
    rw [he,integral_const_mul]
    dsimp [I]
    ring
  simp_rw [hi]
  simpa only [mul_one,I] using projected_residue_kernel (j := j) (q := q) I 1

theorem sampledProjectedValue_fourier_inversion (m B d : ℕ) [NeZero d]
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) :
    (∫ ξ : ℝ, testFourierTransform w ξ*
      sampledProjectedValue m B d J g (fun i => a i*additivePhase (ξ*x i))*
      sampledProjectedValue m B d K h (fun i => b i*additivePhase (-ξ*y i))) =
      ∑ i ∈ J, ∑ k ∈ K,
        ((channelMesh (channelFineCount m B) : ℂ)*
          (finiteResidueAverage (fun r => manuscriptChannel m B d g (i,r)) : ℂ)*a i)*
        ((channelMesh (channelFineCount m B) : ℂ)*
          (finiteResidueAverage (fun r => manuscriptChannel m B d h (k,r)) : ℂ)*b k)*
        (w (x i-y k) : ℂ) := by
  simpa only [sampledProjectedValue,mul_assoc] using finite_fourier_kernel J K
    (fun i => (channelMesh (channelFineCount m B) : ℂ)*
      (finiteResidueAverage (fun r => manuscriptChannel m B d g (i,r)) : ℂ)*a i)
    (fun k => (channelMesh (channelFineCount m B) : ℂ)*
      (finiteResidueAverage (fun r => manuscriptChannel m B d h (k,r)) : ℂ)*b k) x y w

/-- The sampled archimedean kernel and the exact singular-series coefficient.
The residue condition remains the one in the lifted major-arc partition. -/
theorem sampledProjectedFourier_kernel (m B j q : ℕ) [NeZero j] [NeZero q] [NeZero (j*q)]
    (J K : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b : Fin (channelFineCount m B) → ℂ)
    (x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) :
    ((μ q : ℂ)/(q.totient : ℂ))*(∑ r : ZMod (j*q), if r.val.Coprime q then
      ∫ ξ : ℝ, testFourierTransform w ξ*
        sampledProjectedFourier m B (j*q) J g (fun i => a i*additivePhase (ξ*x i)) r*
        sampledProjectedFourier m B (j*q) K h (fun i => b i*additivePhase (-ξ*y i)) (-r)
      else 0) =
      (((j : ℝ)/j.totient*singularSeriesCoefficient j q : ℝ) : ℂ)*
        ∑ i ∈ J, ∑ k ∈ K,
          ((channelMesh (channelFineCount m B) : ℂ)*
            (finiteResidueAverage (fun s => manuscriptChannel m B (j*q) g (i,s)) : ℂ)*a i)*
          ((channelMesh (channelFineCount m B) : ℂ)*
            (finiteResidueAverage (fun s => manuscriptChannel m B (j*q) h (k,s)) : ℂ)*b k)*
          (w (x i-y k) : ℂ) := by
  simp_rw [sampledProjectedFourier_eq]
  rw [projected_residue_full_integral,sampledProjectedValue_fourier_inversion]

end JointDickman

end OAI
