import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBounded
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace OAI

noncomputable section
namespace KadisonSimilarity
open NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def amplifyAlgHom (n : ℕ) :
    (H →L[ℂ] H) →ₐ[ℂ] (HilbertCopies H n →L[ℂ] HilbertCopies H n) where
  toFun Y := amplify Y n
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' _ _ := by ext x i; simp
  map_mul' _ _ := by ext x i; simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  commutes' c := by ext x i; simp [Algebra.algebraMap_eq_smul_one]

theorem amplify_continuous (n : ℕ) : Continuous (fun Y : H →L[ℂ] H => amplify Y n) := by
  let L : (H →L[ℂ] H) →ₗ[ℂ] (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
    (amplifyAlgHom n).toLinearMap
  exact (L.mkContinuous 1 (fun Y => by change ‖amplify Y n‖ ≤ 1 * ‖Y‖; simpa using norm_amplify_le Y n)).continuous

omit [CompleteSpace H] in
@[simp] theorem amplify_smul (c : ℝ) (Y : H →L[ℂ] H) (n : ℕ) :
    amplify (c • Y) n = c • amplify Y n := by ext x i; simp

omit [CompleteSpace H] in
@[simp] theorem amplify_neg (Y : H →L[ℂ] H) (n : ℕ) :
    amplify (-Y) n = -amplify Y n := by ext x i; simp

@[simp] theorem amplify_exp (Y : H →L[ℂ] H) (n : ℕ) :
    amplify (exp Y) n = exp (amplify Y n) := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (amplifyAlgHom n) (amplify_continuous n) Y

end KadisonSimilarity

end

end OAI
