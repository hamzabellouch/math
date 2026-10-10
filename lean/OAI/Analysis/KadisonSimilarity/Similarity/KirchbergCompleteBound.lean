import OAI.Analysis.KadisonSimilarity.Similarity.ExponentialSimilarity
import OAI.Analysis.KadisonSimilarity.Similarity.AmplifyExponential
import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergIntegral

namespace OAI

/-! Kirchberg's cancellation argument at all matrix sizes, with the
commutator estimate left as an explicit hypothesis. -/

noncomputable section
namespace KadisonSimilarity
open NormedSpace

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kirchberg_completeNorm_le_exp (π : BoundedUnitalHom A H)
    (t : H →L[ℂ] H) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ht : IsSelfAdjoint t)
    (hπ : ∀ a, π.1 a = exp (-t) * σ a * exp t)
    (hK : ‖exp (-t)‖ * ‖exp t‖ = completeNorm π.1)
    {D : ℝ} (hD : 0 ≤ D) (hδ : CompleteBound (fun a => commutator t (σ a)) D) :
    completeNorm π.1 ≤ Real.exp D := by
  apply le_exp_of_kirchberg_inequality hD
  intro hlarge
  let K := completeNorm π.1
  let q := (K - 1) / Real.log K
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hlarge.le) (Real.log_pos hlarge).le
  apply completeNorm_le (show 0 ≤ 1 + D * q by positivity)
  intro n X
  let a := matrixOperator (X.map σ)
  let T := amplify t n
  have hscale (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
      ‖exp (s • (-T))‖ * ‖exp (s • T)‖ ≤ K ^ s := by
    change ‖exp (s • (-amplify t n))‖ * ‖exp (s • amplify t n)‖ ≤ _
    rw [← amplify_neg, ← amplify_smul, ← amplify_smul, ← amplify_exp, ← amplify_exp]
    calc
      _ ≤ ‖exp (s • (-t))‖ * ‖exp (s • t)‖ :=
        mul_le_mul (norm_amplify_le _ n) (norm_amplify_le _ n) (norm_nonneg _) (norm_nonneg _)
      _ = K ^ s := by rw [exp_condition_real_smul t ht hs.1, hK]
  have he : matrixOperator (X.map π.1) = exp (-T) * a * exp T := by
    change _ = exp (-amplify t n) * _ * exp (amplify t n)
    rw [← amplify_neg, ← amplify_exp, ← amplify_exp]
    ext ξ i
    simp only [a, matrixOperator_apply, Matrix.map_apply, hπ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      amplify_apply, map_sum]
  have hd : ‖a * T - T * a‖ ≤ D * ‖CStarMatrix.ofMatrix X‖ := by
    rw [norm_sub_rev]
    change ‖commutator T a‖ ≤ _
    rw [show commutator T a = matrixOperator (fun i j => commutator t (σ (X i j))) from
      commutator_amplify_matrixOperator t (X.map σ)]
    exact hδ n X
  rw [he]
  calc
    _ ≤ ‖a‖ + ‖a * T - T * a‖ * q := norm_real_conjugation_le T a hlarge hscale
    _ ≤ ‖CStarMatrix.ofMatrix X‖ + (D * ‖CStarMatrix.ofMatrix X‖) * q := by
      exact add_le_add (by simpa only [one_mul] using completeBound_starHom σ n X)
        (mul_le_mul_of_nonneg_right hd hq)
    _ = (1 + D * q) * ‖CStarMatrix.ofMatrix X‖ := by ring

end KadisonSimilarity

end

end OAI
