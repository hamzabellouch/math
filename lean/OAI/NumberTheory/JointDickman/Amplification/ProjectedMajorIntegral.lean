import OAI.NumberTheory.JointDickman.Probability.ProjectedResidueKernel
import OAI.NumberTheory.JointDickman.Amplification.MajorArcFiniteSum

namespace OAI

/-! # The exact main term after projecting both endpoint residues -/

namespace JointDickman
open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

theorem projected_residue_integral {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)]
    (L U : ℝ) (W A B : ℝ → ℂ) :
    ((μ q : ℂ)/(q.totient : ℂ))*(∑ h : ZMod (j*q), if h.val.Coprime q then
      ∫ ξ in L..U, W ξ*
        ((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A ξ)*
        ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B ξ) else 0) =
      (((j : ℝ)/j.totient*singularSeriesCoefficient j q : ℝ) : ℂ)*
        ∫ ξ in L..U, W ξ*A ξ*B ξ := by
  classical
  let I : ℂ := ∫ ξ in L..U, W ξ*A ξ*B ξ
  have hi (h : ZMod (j*q)) :
      (∫ ξ in L..U, W ξ*((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A ξ)*
        ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B ξ)) =
        ((ramanujanSum (j*q) h/((j*q).totient : ℂ))*I)*
          ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*1) := by
    have he : (fun ξ => W ξ*((ramanujanSum (j*q) h/((j*q).totient : ℂ))*A ξ)*
        ((ramanujanSum (j*q) (-h)/((j*q).totient : ℂ))*B ξ)) =
        fun ξ => ((ramanujanSum (j*q) h/((j*q).totient : ℂ))*
          (ramanujanSum (j*q) (-h)/((j*q).totient : ℂ)))*(W ξ*A ξ*B ξ) := by
      funext ξ
      ring
    rw [he,intervalIntegral.integral_const_mul]
    dsimp [I]
    ring
  simp_rw [hi]
  simpa only [mul_one,I] using projected_residue_kernel (j := j) (q := q) I 1

theorem projected_major_integral (j Q : ℕ) [NeZero j] (L U : ℝ) (W A B : ℝ → ℂ) :
    (∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
      (∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
        ∫ ξ in L..U, W ξ*
          ((ramanujanSum (j*(q : ℕ)) h/((j*(q : ℕ)).totient : ℂ))*A ξ)*
          ((ramanujanSum (j*(q : ℕ)) (-h)/((j*(q : ℕ)).totient : ℂ))*B ξ)
      else 0)) =
      (((j : ℝ)/j.totient*(∑ q ∈ positiveDenominators Q,
        singularSeriesCoefficient j (q : ℕ)) : ℝ) : ℂ)*
          ∫ ξ in L..U, W ξ*A ξ*B ξ := by
  simp_rw [projected_residue_integral]
  push_cast
  rw [mul_sum,sum_mul]

end JointDickman

end OAI
