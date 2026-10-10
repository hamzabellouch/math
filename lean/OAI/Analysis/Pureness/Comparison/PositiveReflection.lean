import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzComparison
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem nonneg_of_injective_starHom (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    {a : A} (ha : 0 ≤ φ a) : 0 ≤ a := by
  have hsa : IsSelfAdjoint a := hφ (by rw [map_star]; exact ha.star_eq)
  have he : φ (cfcₙ (fun t : ℝ => max t 0) a) = φ a := by
    rw [φ.map_cfcₙ (fun t : ℝ => max t 0) a (hf₀ := by simp)
      (hφ := map_continuous φ) (ha := hsa) (hφa := ha.isSelfAdjoint)]
    calc
      _ = cfcₙ (fun t : ℝ => t) (φ a) := by
        apply cfcₙ_congr
        intro t ht
        exact max_eq_left (quasispectrum_nonneg_of_nonneg (φ a) ha t ht)
      _ = φ a := cfcₙ_id' ℝ (φ a)
  rw [← hφ he]
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)
end CuntzComparison

end

end OAI
