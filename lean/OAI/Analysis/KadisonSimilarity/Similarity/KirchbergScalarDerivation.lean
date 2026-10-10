import OAI.Analysis.KadisonSimilarity.Similarity.KirchbergConjugation
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! Kirchberg's scalar commutator bound for an exponential similarity of
a star representation. This is the estimate before equation (2), p. 61. -/

noncomputable section
namespace KadisonSimilarity

open NormedSpace

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem star_kirchbergPath_one (t : B) (ht : IsSelfAdjoint t) (a : B) :
    star (kirchbergPath t (star a) 1) = kirchbergPath t a (-1) := by
  simp [kirchbergPath, star_mul, NormedSpace.star_exp, ht.star_eq, mul_assoc]

/-- A bound for the positive endpoint also bounds the negative endpoint,
because the source representation preserves adjoints. -/
theorem kirchberg_commutator_bound (σ : A →⋆ₐ[ℂ] B) (t : B)
    (ht : IsSelfAdjoint t) {M : ℝ} (hM : 0 < M)
    (hπ : ∀ a : A, ‖kirchbergPath t (σ a) 1‖ ≤ M * ‖a‖) (a : A) :
    ‖t * σ a - σ a * t‖ ≤ (M + 1) * ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  have hMa : 0 < M * ‖a‖ := mul_pos hM (norm_pos_iff.mpr ha)
  have hleft : ‖kirchbergPath t (σ a) (-1)‖ ≤ M * ‖a‖ := by
    rw [← star_kirchbergPath_one t ht (σ a), norm_star, ← map_star]
    simpa only [norm_star] using hπ (star a)
  exact (norm_commutator_le_of_kirchberg_bound t (σ a) ht hMa hleft (hπ a)).trans
    (by nlinarith [NonUnitalStarAlgHom.norm_apply_le σ a])

end KadisonSimilarity

end

end OAI
