import OAI.Geometry.ProjectionVolume.GeneralProduct
import OAI.Geometry.ProjectionVolume.SimplexPolytope
import OAI.Geometry.ProjectionVolume.SimplexValue
import OAI.Geometry.ProjectionVolume.Arithmetic

namespace OAI

noncomputable section
open Set MeasureTheory

namespace Paper092

theorem standardSimplex_product_normalizedProjectionVolume {r s : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    normalizedProjectionVolume (cartesianBody (standardSimplex r) (standardSimplex s)) =
      simplexConstant r * simplexConstant s := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have h := normalizedProjectionVolume_product hr hs
    (standardSimplexPolytope r hr0) (standardSimplexPolytope s hs0)
  simpa only [standardSimplexPolytope_body,
    standardSimplex_normalizedProjectionVolume r hr0,
    standardSimplex_normalizedProjectionVolume s hs0] using h

theorem simplex_product_ratio {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    normalizedProjectionVolume (cartesianBody (standardSimplex r) (standardSimplex s)) /
      simplexConstant (r + s) =
      ((r + 1 : ℝ) * (s + 1) / (r + s + 1)) * (Nat.choose (r + s) r : ℝ) *
        ((r : ℝ)^r * (s : ℝ)^s / ((r+s : ℕ) : ℝ)^(r+s)) := by
  rw [standardSimplex_product_normalizedProjectionVolume hr hs]
  exact simplex_constant_product_ratio r s (by omega) (by omega)

theorem universal_upper_constant_ge_product {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (C : ℝ) (hC : ∀ K : Set (Euclidean (r+s)), IsCompact K → Convex ℝ K →
      (interior K).Nonempty → normalizedProjectionVolume K ≤ C) :
    simplexConstant r * simplexConstant s ≤ C := by
  rw [← standardSimplex_product_normalizedProjectionVolume hr hs]
  exact hC _ (cartesianBody_isCompact (standardSimplex_isCompact r) (standardSimplex_isCompact s))
    (cartesianBody_convex (standardSimplex_convex r) (standardSimplex_convex s))
    (cartesianBody_interior_nonempty (standardSimplex_interior_nonempty r)
      (standardSimplex_interior_nonempty s))

end Paper092

end

end OAI
